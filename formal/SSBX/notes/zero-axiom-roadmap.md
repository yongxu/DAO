# zero-axiom roadmap for `kleene_recursion_axiom`

Scope: remove the need for `GodelLi.kleene_recursion_axiom` without editing
`GodelLi.lean`.  The active Lean staging file is
`formal/SSBX/Foundation/Bagua/KleeneInternal.lean`.

## Current Lean interface split

`KleeneInternal.lean` now separates the former single diagonal gap into these
proof obligations:

- `UniversalInterpSpec U`: `U` simulates `P` on `h` from `ProgEnc.encProg P`.
- `LenProgInput P`: a new staged input convention
  `YiInstrEnc.encNat P.length ++ ProgEnc.encProg P`, with theorem
  `decLenProgInput_self` proving the bounded-length round-trip.
- `SmnSpec subst`: `subst P input` behaves like `P` started with `input` in
  history.
- `KleeneFixedPointExists`: every one-input program `F` has a closed fixed
  point `D`.
- `BoolInverterCompilerExists`: every concrete Bool decider program can be
  compiled into a one-input program that halts exactly on false output.
- `AllDecidersAreYiComputable`: restricted to `CuoInvariantDecide`, matching
  the current `GodelLi.KleeneInverter` statement.

Already proved:

- `yi_kleene_from_fixedpoint_and_inverter`
- `yi_kleene_from_primitives`
- `kleene_inverter_via_yi_kleene`
- `path_to_zero_axiom`
- `decLenProgInput_self`
- `progEnc_append`

Thus the remaining work is no longer a monolithic Kleene theorem; it is a set
of witness constructors plus their correctness proofs.

## Interface audit, 2026-05-07

This audit checks the current route against the actual `YiInstr` machine,
`ProgEnc` encoding, and `HaltsWith` input convention.

### `UniversalInterpSpec U`

- Direction: correct as a halting-only universal interpreter target:
  `Halts P h ↔ HaltsWith U h (ProgEnc.encProg P)`.
- Currently provable? Not from the existing scaffold. It remains a real witness
  obligation.
- Fit issues:
  - `ProgEnc.encProg` is a raw concatenation of instruction encodings; despite
    older comments, it has no leading program-length cell.
  - `ProgEnc.decInstrs` round-trips only when supplied `P.length` and
    `ProgEnc.AllEncodable P`.
  - `YiInstr.pop` on empty history halts instead of branching, so a real `U`
    cannot simply probe for end-of-stream and continue.
- Current implementation: kept as an explicit premise. A local sanity lemma
  `progEnc_decodes_self` records the actual round-trip shape, and
  `universalInterpSpec_empty_input` proves the required empty-program behavior
  for any witness.
- Remaining gap: either build a raw-history interpreter that avoids needing a
  length delimiter, or change/prove a length-delimited input convention and
  align the spec with it.

### Task E feasibility judgment: length-delimited `ProgEnc` vs raw-history interpreter

Two routes were audited against `KleeneInternal.lean`,
`WenyanSelfInterp.lean`, and `义理/M_证明报告_192_理之不完备.md`.

**More tractable route: length-delimited `ProgEnc` with an explicit bound.**

This route is better because it reuses what is already proved:

- `YiInstrEnc.decNat_encNat` decodes a Nat length prefix, provided
  `(NatCell.encodeNat n).length < 192`.
- `ProgEnc.decInstrs_encProg` decodes exactly `P.length` instructions from
  `ProgEnc.encProg P`, provided `ProgEnc.AllEncodable P`.
- The new `KleeneInternal.decLenProgInput_self` composes those facts for
  `LenProgInput P`.

It still does not prove `UniversalInterpExists`: a YiInstr-level interpreter
must read and use the prefix.  But the parser boundary is now a small theorem
rather than a vague convention.  The cost is honest: every universal-interpreter
statement should either assume/prove `ProgLenBounded P`, or move to a stronger
multi-cell length encoding whose decoder does not saturate at one header cell.

**Less tractable route: raw-history interpreter over `ProgEnc.encProg P`.**

This route keeps the old `UniversalInterpSpec`, but it must solve a harder
boundary problem.  `ProgEnc.encProg` is raw concatenation; the new
`progEnc_append` theorem records that it composes by append.  Since
`ProgEnc.decInstrs` needs an external instruction count, a raw-history
interpreter must either:

- decode until history exhaustion without a safe object-level empty-stream
  branch, or
- infer program boundaries from parse failure/end-of-list behavior, where
  `YiInstr.pop` on empty history halts rather than exposing a branchable test,
  or
- carry another delimiter convention implicitly, which is the length-delimited
  route in disguise.

Therefore raw-history interpretation is not impossible, but it is the riskier
engineering path.  It also makes correctness statements more brittle because
the same byte stream can be a prefix of a longer program stream.

### Critical read of `M_证明报告_192_理之不完备.md`

The report is useful as a high-level inventory of `GodelLi.lean`, but it
overstates and/or dates several claims relative to the current code:

- It describes `KleeneInverter` as quantifying over all Lean Bool functions.
  Current `GodelLi.lean` has the necessary
  `CuoInvariantDecide decide → ...` restriction.  This is not cosmetic:
  unrestricted inversion conflicts with the proved cuo-invariance of halting
  profiles.
- It calls `kleene_recursion_axiom` "Church-Turing on BaguaTuring" too broadly.
  The current formal assumption is a cuo-restricted Church-Turing boundary plus
  missing witness/compiler work, not a theorem about all Lean-definable Bool
  functions.
- It says the zero-axiom work is essentially a 500-1000 line universal
  interpreter/quine implementation.  That estimate ignores the exact input
  convention: `ProgEnc.encProg` has no length cell, and `decInstrs` needs an
  external count.
- It presents `SmnSpec` as a relatively small helper in places.  Current
  `YiInstr` lacks arbitrary `Cell192` literals and a safe empty-stack test, so
  generic specialization is a real language-expressivity problem, not merely a
  short push-list routine.
- The finite-fuel theorem, cuo-invariant conditional halting theorem, four Rice
  instances, uniform ∅/univ-profile theorem, and `daoJudge_not_universal`
  results are real Lean-level consequences.  The "unconditional" versions,
  however, remain conditional on the single axiom until the interfaces in this
  roadmap are discharged.

### `SmnSpec subst`

- Direction: semantically right for s-m-n:
  `HaltsWith P h input ↔ Halts (subst P input) h`.
- Currently provable? No, not over arbitrary `List Cell192` with the current
  core instruction set.
- Fit issues:
  - The tempting construction `pushList input ++ P` requires materializing
    arbitrary `Cell192` constants.
  - Current `YiInstr` has relative hex operations (`flipYao`, `hu`, `cuo`,
    `zong`) and `setShi`, but no `hexLit`, absolute yao setter/test, or
    safe empty-stack test.
  - Therefore the old "50 line cell-setting helper" estimate was too weak.
- Current implementation: kept as a strong explicit premise. The new
  `smnSpec_empty_input` sanity lemma proves that any valid witness must reduce
  to ordinary halting when `input = []`.
- Remaining gap: add/prove a literal-materialization layer, or replace generic
  s-m-n with a narrower self-encoding/quining construction that is actually
  expressible by `YiInstr`.

### `KleeneFixedPointExists`

- Direction: correct payload for the recursion theorem. It asks only for
  halting equivalence, not final-state equality:
  `Halts D h ↔ HaltsWith F h (ProgEnc.encProg D)`.
- Currently provable? Not yet. It is provable only after a real specialization
  or quine/self-application construction exists.
- Fit issues:
  - Depends on the same program-as-data materialization problem as `SmnSpec`.
  - It is intentionally weaker than full behavioral equality, which is good.
- Current implementation: explicit premise, assembled by
  `yi_kleene_from_fixedpoint_and_inverter`.
- Remaining gap: derive it from a strengthened, actually implementable
  universal/s-m-n route, or prove it directly by a Bagua-specific quine.

### `BoolInverterCompilerExists`

- Direction: correct interface for the diagonal step: given a concrete decider
  program, compile a one-input program that halts exactly when the decider's
  Bool output is false.
- Currently provable? Not from `UniversalInterpSpec` alone.
- Fit issues:
  - The halting-only universal spec does not expose the decider's final `Shi`,
    so it is too weak to justify a "run then inspect final Bool" compiler.
  - A real proof needs a universal evaluator/readout spec, or a separate
    hand-built wrapper with its own correctness theorem.
- Current implementation: kept as an explicit compiler premise. `YiDecides`
  has been tightened so a decider must halt with defined output
  (`Shi.ji`/`Shi.wei`, not `Shi.jin`).
- Remaining gap: introduce/prove an evaluator spec that returns or preserves
  final `Shi`, then derive this compiler from it.

### `AllDecidersAreYiComputable` (cuo-restricted)

- Direction: correct relative to `GodelLi.KleeneInverter`, which already
  quantifies only over `CuoInvariantDecide`.
- Currently provable? No. It is the Church-Turing boundary, not a Lean theorem
  about all definable Bool functions.
- Fit issues:
  - The unrestricted version is known inconsistent with cuo symmetry.
  - The cuo-restricted version is still a meta-level completeness assumption
    unless the project defines a smaller syntactic class of deciders and
    compiles that class.
- Current implementation: explicit premise. `all_deciders_from_all_lean_deciders`
  records that the old unrestricted claim would imply the restricted one, but
  the route uses only the restricted form.
- Remaining gap: either leave it as the stated meta-interface, or replace it
  with a concrete source-language compiler theorem for a specific decider
  syntax.

### `path_to_zero_axiom`

- Direction: correct as an assembly theorem.
- Currently provable? Yes, conditionally. It is a theorem with no `sorry` or
  local axiom, but its hypotheses are still the witness/compiler/meta
  interfaces above.
- Fit issues: none in the assembly itself; the risk is only in over-reading the
  premises as already constructible.
- Current implementation: proved by composing
  `yi_kleene_from_primitives` and `kleene_inverter_via_yi_kleene`.
- Remaining gap: discharge or consciously keep the four premises:
  `UniversalInterpExists`, `SmnExists`, `KleeneFromPrimitives`, and
  `AllDecidersAreYiComputable`.

## Execution plan

1. Universal interpreter witness, likely more than the previous 700-1000 line
   estimate unless the input convention is changed.
   Build a concrete `U : List YiInstr` in or near `WenyanSelfInterp.lean`, then
   prove `UniversalInterpSpec U`.  The proof should factor through fetch,
   decode, execute, and writeback lemmas for the existing `ProgEnc` encoding.
   First decide whether `U` receives raw `ProgEnc.encProg P` or a new
   length-delimited encoding.

2. Specialization compiler.
   Do not assume an arbitrary-cell `pushList` helper exists.  Either extend the
   object language with a literal/materialization macro and prove it, or replace
   the generic `SmnSpec` obligation with a directly provable quine/fixed-point
   construction.

3. Fixed-point compiler, estimated 150-250 Lean lines after steps 1-2.
   Prove `KleeneFixedPointFromPrimitives` by using `U` and `subst` to build the
   usual self-application program.  The target theorem is only
   `Halts D h ↔ HaltsWith F h (ProgEnc.encProg D)`, so final-state equality is
   unnecessary.

4. Bool inverter compiler, after a universal evaluator/readout spec.
   Build a wrapper that runs a concrete decider, inspects final `Shi`, halts on
   `Shi.wei`, and loops on `Shi.ji`.  `Shi.jin` is now excluded by
   `YiDecides`; a halted decider must output `Shi.ji` or `Shi.wei`.

5. Cuo-restricted Church-Turing interface, meta-level boundary.
   The formal assumption is now the narrower
   `∀ decide, CuoInvariantDecide decide → YiComputable decide`.  This avoids
   the inconsistent unrestricted claim and matches the actual quantifier in
   `GodelLi.KleeneInverter`.

## Integration checkpoint

Once steps 1-4 produce the two package terms
`KleeneFixedPointFromPrimitives` and `BoolInverterCompilerFromUniversal`,
`KleeneInternal.path_to_zero_axiom` can assemble:

```lean
UniversalInterpExists →
SmnExists →
KleeneFromPrimitives →
AllDecidersAreYiComputable →
KleeneInverter
```

At that point `GodelLi.lean` can replace `kleene_recursion_axiom` with the
assembled theorem in a separate edit.
