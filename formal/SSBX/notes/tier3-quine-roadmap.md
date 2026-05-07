# Tier 3 Quine Roadmap

Scope: this note records what was checked for task D without changing Parser,
Kleene, `SSBX.lean`, or README files.

## Current Tier 2 Evidence

`formal/SSBX/Foundation/Wen/WenyanSelfHost.lean` proves the current M4 Tier 2
kernel source has these machine-checked properties:

- `微核源_well_formed`: standalone structural validity accepts the 64-instruction
  kernel.
- `微核源_round_trip`: `ProgEnc.decInstrs 微核源.length 微核数 = some (微核源, [])`.
- `微核源_token_round_trip`: `WenyanParserGeneral.parseProgN` parses
  `tokensOfProg 微核源` back to `微核源`, using the existing token-level general
  theorem.
- `微核源_print_parseN_round_trip`: the concrete printed source also round-trips
  through `lexN` and `parseProgN`.
- `微核自释_total`: the kernel halts within fuel 200 from every hexagram.

This direction is correct for Tier 3 because it keeps the two required
round-trip layers separate: source text/parser round-trip and Cell192 program
encoding round-trip.

## What Is Already Machine-Proveable

These can be proved with the current encoding and without touching Parser or
Kleene:

- Any concrete finite `List YiInstr` with small Nat parameters can prove
  `ProgEnc.AllEncodable`, then use `ProgEnc.decInstrs_encProg`.
- Any concrete valid program can prove String-level parser round-trip by
  `native_decide` on `lexN (printProg p)`, or token-level round-trip by
  `parseProgN_tokensOfProg`.
- Concrete execution facts under fixed `runFuel` can be proved by
  `native_decide`.
- The existing 1-cell quine in `WenyanSelfInterp.Quine` proves a real base case:
  `[push]`, started with the right `cur`, leaves its own flattened instruction
  encoding in `history`.

## What Tier 2 Does Not Yet Prove

The current `微核源` is not a full runtime quine. It proves that source and data
encodings round-trip externally, and that the program halts, but it does not
run and produce `微核数`. The theorem `微核源_not_runtime_quine_qian` records the
concrete qian run does not leave `微核数` in `history`.

This is the exact conceptual gap:

- Tier 2: external verifier proves `decode(encode(微核源)) = 微核源`.
- Tier 3: a 文 program itself constructs or emits `encode(its own source)` at
  runtime, with a theorem identifying the emitted cells with its source
  encoding.

## Blocking Items For A Complete Tier 3 Quine

1. `ProgEnc` needs an explicit program framing story if a program is consumed
   from a raw stream. `encProg` is currently flattened instruction bodies; the
   decoder requires an external instruction count. A self-interpreter needs
   either a length delimiter in the stream or a state layout that carries the
   program length as a register.

2. A runtime parser/decoder theorem is missing. `WenyanParserGeneral` gives
   token-level parse/print inversion and concrete `lexN` witnesses, but the
   machine program does not execute `lexN` or `parseProgN`. A Tier 3 theorem
   needs a YiInstr-level decoder/interpreter or a formal bridge explaining why
   the runtime representation is already decoded.

3. The meta-interpreter is still a stub. `WenyanSelfInterp.MetaInterp` currently
   handles only the `nop`/`halt` shape. Tier 3 needs fetch, decode, 12-way
   dispatch, handlers for all constructors, and writeback, plus simulation
   lemmas per handler and a combined theorem.

4. General N-cell quine construction is not present. The 1-cell quine proves
   the base case, but a full quine needs a builder for arbitrary Cell192 lists
   and a fixed-point/s-m-n style theorem tying the built list to the builder's
   own `ProgEnc.encProg`.

## Next Safe Steps

1. Add a length-framed program encoding alongside the existing `ProgEnc.encProg`
   without replacing it, then prove `decFramedProg (encFramedProg p ++ rest)`.

2. Define a stable encoded-state layout with explicit offsets for `cur`,
   `history length`, `pc`, `program length`, `program cells`, and `halted`.

3. Implement one nontrivial handler beyond `nop`/`halt`, preferably `setShi`,
   and prove its encoded-state simulation theorem.

4. After two or three handlers share the same fetch/writeback path, factor the
   dispatch theorem. Only then start the N-cell quine builder.

## Phases Shipped

### Phase C.1 — Length-framed program encoding (2026-05-07)

Closes blocker #1 (program framing). Added in `WenyanSelfInterp.lean § 4b`:

- `ProgEnc.encFramedProg p := YiInstrEnc.encNat p.length ++ encProg p` — length-prefixed
  program encoding, using the existing length-prefix Nat scheme.
- `ProgEnc.decFramedProg : List Cell192 → Option (List YiInstr × List Cell192)` —
  reads the length cell, then runs `decInstrs n` for that length.
- `ProgEnc.decFramedProg_encFramedProg` — generic round-trip theorem
  (`AllEncodable p → (NatCell.encodeNat p.length).length < 192 → ...`).
- `ProgEnc.framed_round_trip_witness` — concrete witness on `[push, halt]`.

This gives stream-friendly self-decoding: a Tier 3 interpreter can read the program
from a raw `List Cell192` stream without an externally-supplied instruction count.

### Phase C.7 partial — uniform N-cell quine (2026-05-07)

Closes the uniform-program subset of Tier 3 (the simplest non-trivial Tier 3
class). Added in `WenyanSelfInterp.lean § 7.3`:

- `Quine.quineNProg N := List.replicate N YiInstr.push` — uniform N-push program.
- `Quine.quineNInit N` — initial state with `cur := encInstr push = cellFromIdx ⟨9, _⟩`.
- `Quine.quine3_history`, `quine5_history`, `quine16_history` — all proven by `rfl`.

These are honest Tier 3 quines: running the program from the prescribed initial
state literally produces `(quineNProg N).map encInstr |>.flatten = encProg
(quineNProg N)` in `history`.  The construction generalizes to any N.

The class is restricted because:
- Programs must be `List.replicate N push` (no other instructions).
- Initial `cur` must be `encInstr push`.

This is not the full Tier 3 — for that we'd need `buildEmitProg` for arbitrary
target lists plus the Kleene diagonal step.  See plan
`/Users/ren/.claude/plans/let-s-look-in-this-dapper-island.md` § Phase C.7
for the full construction.

### Phases C.2–C.6 — pending (meta-interpreter scaffold)

State layout, 12 handlers, dispatch, simulation theorem all remain.
The uniform N-cell quine in C.7 partial does NOT depend on these phases —
it's an orthogonal axis to the meta-interpreter.
