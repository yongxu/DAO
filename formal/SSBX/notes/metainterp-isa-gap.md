# MetaInterp ISA Expressivity Gap — Phase C Architecture Note

**Date**: 2026-05-08
**Status**: Open — blocks discharge of `KleeneCarrier.universalInterpExists`

## Summary

`Phase C` of the MetaInterp work aims to construct a YiInstr program
`metaInterpProg : List YiInstr` such that for every `P : List YiInstr`
and every `h : Hexagram`,

```
Halts P h ↔ HaltsWith metaInterpProg h (encProg P)
```

After completing C.0 (bounded spec), C.A (sub-dispatch trees), and C.C
(11 dispatch routing proofs), a deeper review of the per-block simulation
contract revealed an **ISA-level expressivity gap** that prevents the
construction with the current `YiInstr` instruction set.

## The gap

`YiState` carries one register cell `cur : Cell192` plus a stack
`history : List Cell192`. Every step that updates `sim.pc` requires
prepending `regDataCell regHex` to the pc-counter region of META.history;
every step that updates `sim.cur` (for hu/cuo/zong/setShi/flipYao) requires
applying the corresponding `YiInstr` op to `META.cur` while it equals
`sim.cur`.

These two requirements **collide** under any layout of `encMetaHistory`:

* If `META.cur = sim.cur` (the natural loop invariant), the pc-update
  needs `META.cur = regDataCell` — a different cell — at the moment
  `push` prepends. There is no way to obtain `regDataCell` without
  overwriting `sim.cur` from `cur`.
* If `META.cur = regDataCell` (constant), the cur-mutating ops cannot
  apply to `META.cur` (they would corrupt the loop invariant). They
  would need to reach `sim.cur` from history, which requires popping
  it into `cur` — losing `regDataCell`.
* If `sim.cur` is encoded INSIDE `encMetaHistory` (at known position),
  the pc-update still needs to insert a `regDataCell` between
  `sim.cur` and the encCounter region. Inserting at depth 1+ requires
  swapping or duplicating, which the ISA does not support.

## Why dup/swap is needed

The fundamental operation absent from YiInstr is "swap top of history
with cur" or "duplicate top of history". With a single register and
strictly destructive `pop`, every load-from-history overwrites whatever
`cur` held; every push deposits `cur` to history but cannot retain a
copy of any other value.

Concretely, to insert `regDataCell` between `sim.cur` (at history[0])
and `encCounter` (at history[1+]) without losing either:

```
-- need: history' = [sim.cur, regDataCell, encCounter[0], ...]
-- have: history = [sim.cur, encCounter[0], ...], cur = anything
-- pop sim.cur:    cur = sim.cur,          history = encCounter [...]
-- push:            cur = sim.cur,          history = [sim.cur, ...]   -- back to start
-- pop encCounter top: cur = regDataCell,   history = [encCounter[1:], ...]
-- (sim.cur is now lost; cannot be recovered)
```

Every protocol that moves `cur` between two distinct values destroys
the original. With one register, there is no way to hold both
`sim.cur` and `regDataCell` simultaneously.

## What this means for `universalInterpExists`

`UniversalInterpSpec U := ∀ P h, Halts P h ↔ HaltsWith U h (encProg P)`
quantifies over all `P : List YiInstr`, including programs that mutate
`sim.cur`. For such programs, `metaInterpProg` must track `sim.cur` AND
manipulate the pc-counter — and as shown above, both cannot be
simultaneously maintained with the current ISA.

Consequently:

> **Within the current YiInstr ISA, no `metaInterpProg` can satisfy
> `UniversalInterpSpec` for arbitrary `P`. The axiom is not just
> engineering debt — it sits on the far side of an ISA expressivity
> wall.**

## Paths forward

### Path 1 — Extend YiInstr ISA (recommended for full discharge)

Add one of:
* `dup`: pushes a copy of `cur` to history WITHOUT modifying `cur` —
  essentially a no-op that copies cur. (`push` already does this.)
  *Wait: `push` IS this. Re-examine.*
* `swap`: swaps `cur` with `history.head`. New instruction.
* `peek`: writes `history.head` to `cur` without removing it. New
  instruction.

Of these, `swap` is most expressive: combined with existing pop/push it
implements both peek and dup-effective behaviour. Adding `swap` to
`YiInstr` is a focused ISA change (~1 inductive case + execute clause +
encoding clause) and unblocks `metaInterpProg` construction.

Estimated cost: ~50 LOC ISA change + ~3500 LOC for full Phase C
(unchanged from original plan, since the architecture only blocks
specific simulation steps).

### Path 2 — Restrict `UniversalInterpSpec` to a sim.cur-free subset

Restrict to programs using only `nop`/`jump`/`halt`/`branchYaoEq`/
`branchShiEq` — even this subset has `branchYaoEq`/`branchShiEq` which
read `sim.cur`. Truly sim.cur-independent subset is just nop/jump/halt,
which is too small to preserve undecidability arguments downstream.

### Path 3 — Accept `universalInterpExists` as permanent axiom

The axiom remains as one of the four atomic axioms in `KleeneCarrier`.
The other three (`smnExists`, `kleeneFromPrimitives`,
`allDecidersAreYiComputable`) are unaffected. Net axiom count remains
4; `universalInterpExists` is documented as resting on the YiInstr ISA
expressivity wall rather than mere engineering debt.

### Path 4 — Different simulation strategy

Construct a SEPARATE simulator that does not use `metaInterpProg : List
YiInstr` at all — e.g., a deeply-embedded interpreter encoded directly
in Lean. This would not discharge `universalInterpExists` (which
requires a YiInstr witness), but might offer alternative reductions
upstream.

## Recommendation

**Path 1** is cleanest from both 理 (single ISA addition unblocks
universal interp construction) and 文 (`swap` is a small, locally
self-justifying instruction) perspectives. The ISA extension is
philosophically defensible: it captures the expressivity required by
"the machine simulating itself", which is a meta-level capability the
original 12-instruction core did not need to express.

Adopting Path 1 would:
1. Add `YiInstr.swap` with execute clause `cur ↔ history.head`
2. Update `encInstr`/`decInstr` round-trip lemmas (~50 LOC)
3. Re-enable Phase C as originally planned (E1 design works with
   `swap` available)
4. Document the addition in [BaguaTuring.lean](../Foundation/Bagua/BaguaTuring.lean) and the architecture
   notes here.

Without Path 1, Phase C cannot complete and `universalInterpExists`
remains an axiom indefinitely.

## See also

* [/Users/ren/.claude/plans/sparkling-floating-perlis.md](/Users/ren/.claude/plans/sparkling-floating-perlis.md) —
  original Phase C plan
* [Foundation/Wen/MetaInterp/Fetch.lean](../Foundation/Wen/MetaInterp/Fetch.lean) §0 — D1-D4 deferred items
* [Foundation/Wen/MetaInterp/ExecuteBlock.lean](../Foundation/Wen/MetaInterp/ExecuteBlock.lean) §A — block contract
* [Foundation/Bagua/KleeneCarrier.lean](../Foundation/Bagua/KleeneCarrier.lean) — the four atomic axioms
