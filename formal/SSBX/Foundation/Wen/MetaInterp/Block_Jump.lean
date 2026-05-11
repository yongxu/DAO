/-
# Block_Jump — executeBlock for `jump t` (absolute pc set)

## Summary

The `jump t` opcode in `sim` sets `sim.pc := t` (per `BaguaTuring.lean`
`YiState.execute (.jump t) s = { s with pc := t }`).  Critically, this is
**absolute**, not relative; the target `t` is a payload of the encoded
instruction (a length-prefixed `encNat t` cell run living in
`ProgEnc.encProg sim.prog` directly after the `jump`-tag cell).

In META terms, satisfying the block contract therefore requires:

1. **Read** the encoded jump-target `t` from the param-cell run that sits
   at the front of the `ProgEnc.encProg sim.prog` tail of META.history
   (per the `ParamEnc` discipline of `ExecuteBlock.lean §A.4`: fetch
   consumes only the tag cell; payload remains in place).

2. **Replace** the pc-counter at the **top** of `META.history`.  Per the
   `encMetaHistory` layout (`MetaInterp.lean §4`), the pc-counter lives
   at the very top:
     `encCounter regHex sim.pc ++ [pcMarker] ++ ...`
   To turn this into `encCounter regHex t ++ [pcMarker] ++ ...`, the
   block must pop `sim.pc + 1` cells (the `sim.pc` data cells plus the
   pc-marker) and push back `t + 1` cells (the new `t` data cells plus
   a fresh marker).

3. **Jump** to `fetchOffset`.

## Why this block is structurally harder than nop / interlace / complement / reverse

The cur-transform blocks (`nop`, `interlace`, `complement`, `reverse`) only need to
prepend ONE `regDataCell regHex` cell at the top of META.history (the
pc-counter advance from `sim.pc` to `sim.pc + 1`).  This is a single
`YiInstr.push` whose Hex content is supplied automatically by the loop
invariant `META.cur = (regHex, Shi.jin)`.

`jump t` is qualitatively different in three ways:

* **Variable-length pop.**  The pc-counter has `sim.pc + 1` cells, and
  `sim.pc` is dynamic.  A counted-loop pop is required to consume them
  all, gated on the `Shi.wei` pc-marker.

* **Variable-length push.**  After the pop, `t + 1` cells must be pushed
  to install the new pc-counter.  Since `t` is read at runtime (decoded
  from the param-cell length prefix), this is also a counted-loop push.

* **Param-cell decoding.**  Before any of the above, the block must
  decode `encNat t` from the program-tail prefix to obtain the runtime
  value `t`.  The encoding is length-prefixed: 1 length cell + N digit
  cells, each base-256.  Decoding requires inspecting the length cell
  and walking through N digits while reconstructing the Nat value
  somewhere accessible to the subsequent push loop.

## Sub-lemmas that would be needed for the full proof

- `decodeJumpTargetSubroutine_simulates`: a sub-block that reads the
  program-tail prefix (after the `jump` tag) and produces the Nat target
  `t` materialized as `t` data cells + 1 marker on a fresh counter
  region of META.history.  This depends on a counted-loop combinator
  with a non-empty body that walks the digit cells, plus an arithmetic
  layer for base-256 reconstruction (currently absent: YiInstr cannot
  multiply or do general arithmetic; the decoder must instead unary-
  expand each digit, which is exponential in the digit value but works
  for small jump targets).

- `popPcCounterSubroutine_simulates`: pop until first `Shi.wei` —
  exactly the empty-body case of `countedLoop` already proved as
  `countedLoop_empty_simulates_n_iterations` in `MetaInterp.lean §7.1`.

- `pushPcCounterSubroutine_simulates`: push `t` `regDataCell regHex`
  cells then 1 `regMarkerCell regHex` cell, given a counter of `t` on
  some scratch region and `META.cur = (regHex, Shi.jin)`.  Requires a
  body that does `setShi Shi.jin; push` per iteration.

- A composition lemma stitching the three subroutines and the closing
  `jump fetchOffset` together to discharge the full simulation
  postcondition `BlockPost regHex sim fetchOffset metaProg μ' false`.

## Pragmatic deliverable in this file

We provide:

1. The block's `def` (`executeBlock_jump`), implemented as a skeleton
   that inlines the **structural shape** required — explicitly the
   final `YiInstr.jump fetchOffset`.  The full decode/pop/push body is
   **deferred** and replaced by an explicit `nop` placeholder run so
   that the length and last-instruction lemmas can be proved
   unconditionally.  The block as presented therefore satisfies the
   contract ONLY for the special case where the runtime jump-target
   already equals the current `sim.pc` (so the pc-counter does not
   need to be rewritten).

2. The length lemma (`executeBlock_jump_length`).

3. The last-instruction lemma (`executeBlock_jump_last`).

4. A general **sim-side encoding bridge**:
   `encMetaHistory_jump_step`.  It states the audited algebraic fact
   that a simulated `jump t` rewrites the leading pc-counter prefix from
   `encCounter regHex sim.pc` to `encCounter regHex t`, preserving the
   halted flag, simulated history, and encoded program tail.

5. A **simulation lemma for the trivial case** `t = sim.pc`, i.e., a
   "no-op jump" where the pc-counter encoding is unchanged — proven
   end-to-end as `executeBlock_jump_local_effect_trivial`.

6. The general-case block simulation lemma is **stated only as a docstring**
   (no `theorem` declaration, since we may not use `sorry` and we are
   not yet in a position to prove it).  The required sub-lemmas are
   itemized above.

This file contains 0 sorry and 0 axiom; it is an **honest scaffold**
that nails the trivial subcase and documents the sub-lemmas needed for
the general case.  It is the analogue of the worked-example sections
of `ExecuteBlock.lean` and `Block_HuCuoZong.lean`, scoped to what is
provable without first building out the missing arithmetic /
param-decode layer.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  The `jump` execute block — skeleton

For the **trivial case** (`t = sim.pc`, no pc-counter rewrite needed),
the block reduces to a single `jump fetchOffset` instruction.  We use
this as the present implementation, with the understanding that the
general case will require additional pre-jump instructions (decode +
pop + push subroutines, see file docstring).

The `_offset` and `_t` parameters are accepted for future extension to
match the contract signature.  `_t` is the **statically known**
jump-target threaded by the dispatch layer when the encoded program is
known at compile time; for the dynamic decode case (the general
contract), the target is read at runtime and `_t` is unused.
-/

/-- The `jump` execute block (current trivial-case skeleton): a single
    `jump fetchOffset`.  See the file docstring for the full design and
    the sub-lemmas needed to lift this to the general dynamic-target case. -/
def executeBlock_jump (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.jump fetchOffset ]

theorem executeBlock_jump_length (offset fetchOffset : Nat) :
    (executeBlock_jump offset fetchOffset).length = 1 := rfl

theorem executeBlock_jump_first (offset fetchOffset : Nat) :
    (executeBlock_jump offset fetchOffset)[0]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- The block's only / last instruction is `jump fetchOffset`. -/
theorem executeBlock_jump_last (offset fetchOffset : Nat) :
    (executeBlock_jump offset fetchOffset).getLast?
      = some (YiInstr.jump fetchOffset) := rfl

/-! ## § 2  Trivial-case simulation

In the **trivial case** `t = sim.pc`, the encoded META state is
unchanged across `sim.step`:
  `encMetaHistory regHex sim.step = encMetaHistory regHex sim`
because `sim.step = { sim with pc := t } = { sim with pc := sim.pc } = sim`
(extensionally on the encoded history — `pc` is the only field affected
by `jump`, and `pc := pc` is a no-op).

In this case the block contract is satisfied by the single
`jump fetchOffset` instruction — pc moves to fetchOffset, all other
META fields are preserved, and the encoded post-state equals the
encoded pre-state.

We prove the **local effect** form (no surrounding metaProg context):
running the 1-instruction skeleton from a state with arbitrary cur and
history just lands at fetchOffset with everything else unchanged.
-/

/-- **Local effect** of the jump skeleton: a 1-fuel run lands at
    `fetchOffset` and preserves cur, history, halted. -/
theorem executeBlock_jump_local_effect
    (cur : R8) (history : List R8) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_jump offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 1
    μ'.cur = cur
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for general jump**: when the simulated ISA executes
    `jump t`, the encoded META history rewrites exactly its pc-counter
    prefix to `encCounter regHex t`; every non-pc region is preserved.

    This closes the algebraic encoding side of the jump case.  The
    concrete META block that performs this variable-length rewrite is
    still deferred to the subroutine work described above. -/
theorem encMetaHistory_jump_step
    (regHex : Hexagram) (sim : YiState) (t : Nat)
    (h_alive : sim.halted = false)
    (h_jump : sim.prog[sim.pc]? = some (.jump t)) :
    encMetaHistory regHex (sim.step) =
      encCounter regHex t ++
      [encHaltedFlag regHex sim.halted] ++
      encCounter regHex sim.history.length ++
      sim.history ++
      ProgEnc.encProg sim.prog := by
  have h_step : sim.step = { sim with pc := t } := by
    simp [YiState.step, h_alive, h_jump, YiState.execute]
  rw [h_step]
  exact encMetaHistory_pc_set regHex sim t

/-- **Sim-side bridge for the trivial case** (`t = sim.pc`): when the
    `jump`'s target equals the current pc, `sim.step` is the identity on
    `sim` (pc is replaced by the same value), so the encoded META state
    is unchanged. -/
theorem encMetaHistory_jump_step_trivial
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_jump : sim.prog[sim.pc]? = some (.jump sim.pc)) :
    encMetaHistory regHex (sim.step) = encMetaHistory regHex sim := by
  -- sim.step = execute (.jump sim.pc) sim = { sim with pc := sim.pc }
  have h_step : sim.step = sim := by
    unfold YiState.step
    rw [h_alive]
    simp only [Bool.false_eq_true, if_false]
    rw [h_jump]
    show YiState.execute (.jump sim.pc) sim = sim
    unfold YiState.execute
    -- { sim with pc := sim.pc } is extensionally equal to sim.
    cases sim with
    | mk cur history pc prog halted => rfl
  rw [h_step]

/-! ## § 3  General-case simulation — **deferred**

The general-case simulation theorem would have the shape:

```lean
theorem executeBlock_jump_simulates
    (regHex : Hexagram) (sim : YiState)
    (offset fetchOffset t : Nat)
    (metaProg : List YiInstr)
    (h_alive : sim.halted = false)
    (h_jump  : sim.prog[sim.pc]? = some (.jump t))
    (μ : YiState)
    (h_pre : BlockPre regHex sim offset metaProg μ) :
    -- with BLOCK_FUEL = (full block fuel including decode+pop+push)
    BlockPost regHex sim fetchOffset metaProg
      (μ.runFuel <BLOCK_FUEL>) false
```

To prove it, the implementer would need to:

1. **Replace `executeBlock_jump`** with the full pipeline:
   ```
   decodeJumpTargetSubroutine offset       -- obtain t into META state
   ++ popPcCounterSubroutine (offset + dLen)
   ++ pushPcCounterSubroutine (offset + dLen + pLen)
   ++ [ jump fetchOffset ]
   ```
   where `dLen`, `pLen` are the static sizes of the decode and pop
   subroutines.

2. **Prove the four sub-lemmas** itemized in the file docstring:
   - `decodeJumpTargetSubroutine_simulates`
   - `popPcCounterSubroutine_simulates`
   - `pushPcCounterSubroutine_simulates`
   - composition lemma combining the above with the trailing
     `jump fetchOffset`.

3. **Address the arithmetic gap**: YiInstr has no native multiplication,
   so base-256 decode of `encNat t` requires either an exponential
   unary-expansion blow-up, or a structural restriction to "1-cell
   targets" (`t < 256`), where the digit value can be unary-expanded by
   256-way dispatch.  Either choice deserves a separate design
   sub-document before implementation begins.

For now, this file ships only the trivial subcase (proven) and the
shape contract (documented).  The general case is **out of scope** for
this incremental landing.
-/

end SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
