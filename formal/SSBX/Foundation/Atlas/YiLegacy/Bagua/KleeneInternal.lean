/-
# KleeneInternal — 内部 Kleene 递归 · 去公理化路径

This file formalizes the path to remove `kleene_recursion_axiom` from `GodelLi.lean`.

## Strategy

The original `KleeneInverter` quantifies over ALL Lean Bool functions `decide :
List YiInstr → Hexagram → Bool`.  Since Lean (with Classical) admits noncomputable
Bool functions, this version is **fundamentally unprovable** as a Lean theorem:
some Lean-definable Bool functions correspond to no YiInstr program.

**Honest path forward**:
1.  Define `YiComputable decide` — a precise computability witness via YiInstr.
2.  State `YiKleeneInverter` for `YiComputable` deciders (provable conditional
    on universal interpreter + s-m-n; foundation in `WenyanSelfInterp.lean`).
3.  Show the current complement-invariant `KleeneInverter` ⟸
    `YiKleeneInverter` ∧ complement-restricted `Church-Turing`.

This file delivers parts (1) and (3) rigorously, plus the formal statement of
the remaining engineering (2) as a `Prop` so its dependency is explicit.

## What's done (this file, 0 sorry / 0 axiom)

- `RunWith`: explicit YiState constructor with custom initial history (the
  input convention for any universal interpreter).
- `LenProgInput`: a length-delimited program input convention, plus a proved
  decode round-trip for bounded program lengths.
- `BoolFromShi`: a Bool readout from a YiState's final `Shi` component.
- `BoolOutputDefined`: deciders must halt with `Shi.ji` or `Shi.wei`, not
  the mid-computation marker `Shi.jin`.
- `YiDecides`, `YiComputable`: precise computability via YiInstr.
- `UniversalInterpSpec`, `SmnSpec`: concrete witness-level specifications for
  the missing primitives.
- `KleeneFixedPointExists`, `BoolInverterCompilerExists`: the two Lean-level
  interfaces that remain between the primitives and `YiKleeneInverter`.
- `yi_kleene_from_fixedpoint_and_inverter`: proved assembly of those interfaces.
- `kleene_inverter_via_yi_kleene`: structural reduction from
  `YiKleeneInverter ∧ complement-restricted Church-Turing ⇒ KleeneInverter`.
- `path_to_zero_axiom`: the full chain — given primitives + diagonal
  construction + Church-Turing, the original axiom is a theorem.

## What's NOT done (and why)

- `UniversalInterpExists`, `SmnExists`, `KleeneFixedPointFromPrimitives`, and
  `BoolInverterCompilerFromUniversal` are stated as `Prop`, not proven.
  Witnesses require building the ~700-1000 line universal interpreter
  (12-way dispatch + execute blocks + fetch/writeback in YiInstr).  See
  `WenyanSelfInterp.lean § 6b` for the existing partial scaffold.

- The current `SmnSpec` is intentionally an explicit strong assumption.  The
  existing `YiInstr` core has no `R8` literal instruction or safe
  empty-stack test, so a generic "push arbitrary cells, then continue" prefix
  is not currently justified by the instruction set alone.

- The full `kleene_recursion_axiom` remains in `GodelLi.lean`.  Its removal
  requires the primitive/compiler `Prop`s below to be proven as theorems.

This file is the **formal scaffolding** that, once the primitives are proven
(future work), makes the axiom removal mechanical.
-/
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Atlas.YiLegacy.Bagua.GodelLi

namespace SSBX.Foundation.Bagua.KleeneInternal

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Bagua.GodelLi

/-! ## § 1 Input convention: running a YiInstr program with custom history -/

/-- Initial YiState with custom history (the "input tape").  Standard
    `YiState.init` sets history := [].  For meta-interpretation, we need the
    input encoding to be present at startup. -/
def RunWith (h : Hexagram) (prog : List YiInstr) (input : List R8) : YiState :=
  { cur := (h, Shi.jin), history := input, pc := 0, prog := prog, halted := false }

/-- `RunWith` agrees with `YiState.init` when input is empty. -/
theorem runWith_empty (h : Hexagram) (prog : List YiInstr) :
    RunWith h prog [] = YiState.init h prog := rfl

/-- Halting predicate for a state with custom input. -/
def HaltsWith (prog : List YiInstr) (h : Hexagram) (input : List R8) : Prop :=
  ∃ n : Nat, ((RunWith h prog input).runFuel n).halted = true

/-- For empty input, `HaltsWith` reduces to `Halts`. -/
theorem haltsWith_empty (P : List YiInstr) (h : Hexagram) :
    HaltsWith P h [] ↔ Halts P h := by
  unfold HaltsWith Halts
  rw [runWith_empty]

/-- The empty YiInstr program halts immediately because pc 0 is out of range. -/
theorem halts_empty_prog (h : Hexagram) : Halts ([] : List YiInstr) h := by
  exact ⟨1, rfl⟩

/-- Local wrapper around the existing program encoding round-trip.  Note that
    decoding still requires the external instruction count `P.length`. -/
theorem progEnc_decodes_self (P : List YiInstr) (h_enc : ProgEnc.AllEncodable P) :
    ProgEnc.decInstrs P.length (ProgEnc.encProg P) = some (P, []) := by
  simpa using ProgEnc.decInstrs_encProg P h_enc []

/-! ### § 1.1 Length-delimited program input

  `ProgEnc.encProg` is intentionally raw concatenation of instruction encodings:
  it does not carry the number of instructions.  A universal interpreter can
  therefore either parse a raw finite history directly, or consume an explicit
  length prefix.  The latter route is easier to state and prove against the
  existing decoder because `ProgEnc.decInstrs` already requires the instruction
  count as an argument. -/

/-- Program lengths whose `YiInstrEnc.encNat` prefix is represented without
    saturation.  This is the explicit finite-bound side condition behind the
    "length-delimited ProgEnc" route. -/
def ProgLenBounded (P : List YiInstr) : Prop :=
  (NatCell.encodeNat P.length).length < 256

/-- A length-delimited program input: first encode `P.length`, then the raw
    program body. -/
def LenProgInput (P : List YiInstr) : List R8 :=
  YiInstrEnc.encNat P.length ++ ProgEnc.encProg P

/-- Lean-side decoder for `LenProgInput`: read the instruction count, then
    decode exactly that many instructions. -/
def decLenProgInput (input : List R8) : Option (List YiInstr × List R8) :=
  match YiInstrEnc.decNat input with
  | some (n, rest) => ProgEnc.decInstrs n rest
  | none => none

/-- Length-delimited program inputs round-trip under the existing decoder
    assumptions: bounded length prefix plus per-instruction encodability. -/
theorem decLenProgInput_self (P : List YiInstr)
    (h_len : ProgLenBounded P) (h_enc : ProgEnc.AllEncodable P) :
    decLenProgInput (LenProgInput P) = some (P, []) := by
  unfold decLenProgInput LenProgInput ProgLenBounded at *
  rw [YiInstrEnc.decNat_encNat P.length (ProgEnc.encProg P) h_len]
  simpa using ProgEnc.decInstrs_encProg P h_enc []

/-- Raw `ProgEnc` is concatenative.  This is useful, but it also records why
    raw-history interpretation needs an independent end-of-program convention
    rather than relying on `encProg` to delimit itself. -/
theorem progEnc_append (P Q : List YiInstr) :
    ProgEnc.encProg (P ++ Q) = ProgEnc.encProg P ++ ProgEnc.encProg Q := by
  simp [ProgEnc.encProg, List.map_append]

/-! ### § 1.2 Boundedness for jump targets

  YiInstr's three control-flow ops (`branchYaoEq`, `branchShiEq`, `jump`) carry a
  `Nat` target field.  A YiInstr-implemented universal interpreter cannot read an
  arbitrary multi-cell base-256 encoding of such targets at runtime, because the
  ISA has no multiplication primitive.  Per-(opcode × parameter-value) Option-F
  dispatch handles only single-cell targets, i.e. `target < 256`.

  This restriction is the structural counterpart to `ProgLenBounded`: together
  they delimit the class of programs for which a bounded universal interpreter
  is realisable in pure YiInstr without ISA extension. -/

/-- A single instruction's jump-target field, if any, is below 256. -/
def JumpTargetsBoundedInstr : YiInstr → Prop
  | YiInstr.branchYaoEq _ _ t => t < 256
  | YiInstr.branchShiEq _   t => t < 256
  | YiInstr.jump            t => t < 256
  | _ => True

/-- Every instruction in `P` has its jump-target field below 256. -/
def JumpTargetsBounded (P : List YiInstr) : Prop :=
  ∀ i ∈ P, JumpTargetsBoundedInstr i

/-- The class of programs for which a YiInstr universal interpreter is
    realisable: program length's `encodeNat` prefix fits in one cell, AND
    every jump target fits in one cell.  Lean-side any `P : List YiInstr`
    we actually construct in this codebase satisfies this bound. -/
def ProgBounded (P : List YiInstr) : Prop :=
  ProgLenBounded P ∧ JumpTargetsBounded P

/-- The empty program is trivially bounded. -/
theorem progBounded_nil : ProgBounded ([] : List YiInstr) := by
  refine ⟨?_, ?_⟩
  · -- ProgLenBounded []: the encoding of length 0 is `[]`.
    show (NatCell.encodeNat ([] : List YiInstr).length).length < 256
    simp [NatCell.encodeNat, List.length_nil]
  · intro i hi
    cases hi

/-! ## § 2 Bool readout convention

  A YiInstr program "decides" a Prop by halting and outputting a Bool via its
  final `Shi` component:
  - `Shi.ji`  (已 settled / past) ↔ Bool true
  - `Shi.wei` (未 unsettled / future) ↔ Bool false
  - `Shi.jin` (今 present)        ↔ undefined / mid-computation

  The convention matches `daoJudge`'s `Shi.ji ↔ isTian` interpretation. -/

/-- Bool readout from a final state's Shi component.

    Post-V₄ migration: `Shi.dao` is also a "non-output" marker (the V₄ identity,
    used as a "永真 anchor" / timeless element, not a Boolean verdict).
    Both `.jin` and `.dao` map to `false` for the readout, but
    `BoolOutputDefined` excludes both from the "halted-with-real-answer" set. -/
def BoolFromShi (s : YiState) : Bool :=
  match s.cur.2 with
  | Shi.ji  => true
  | Shi.wei => false
  | Shi.jin => false  -- treated as false; mid-computation indicates an error
  | Shi.dao => false  -- V₄ identity; treated as false, not a valid answer

/-- A halted decider must have committed to a real Bool output.  Neither
    `Shi.jin` (mid-computation marker) nor `Shi.dao` (V₄ identity / timeless
    anchor) is a valid final Boolean result. -/
def BoolOutputDefined (s : YiState) : Prop :=
  s.cur.2 ≠ Shi.jin ∧ s.cur.2 ≠ Shi.dao

theorem boolFromShi_true_iff_ji (s : YiState) :
    BoolFromShi s = true ↔ s.cur.2 = Shi.ji := by
  rcases h : s.cur.2 with ⟨y, g⟩
  cases y <;> cases g <;> simp [BoolFromShi, h, Shi.ji]

theorem boolFromShi_false_iff_wei_of_defined (s : YiState)
    (hdef : BoolOutputDefined s) :
    BoolFromShi s = false ↔ s.cur.2 = Shi.wei := by
  rcases h : s.cur.2 with ⟨y, g⟩
  cases y <;> cases g <;>
    simp [BoolFromShi, BoolOutputDefined, h, Shi.dao, Shi.jin, Shi.wei] at hdef ⊢

/-! ## § 3 YiComputable: precise computability witness -/

/-- A YiInstr program `D_decide` **decides** a Lean predicate `decide` iff
    for every program `P` and hexagram `h`, running `D_decide` with `encProg P`
    as initial input and `h` as initial cur-hexagram halts in finite fuel and
    outputs a defined Bool matching `decide P h`. -/
def YiDecides (D_decide : List YiInstr) (decide : List YiInstr → Hexagram → Bool) : Prop :=
  ∀ (P : List YiInstr) (h : Hexagram),
    ∃ (N : Nat),
      let s := (RunWith h D_decide (ProgEnc.encProg P)).runFuel N
      s.halted = true ∧ BoolOutputDefined s ∧ BoolFromShi s = decide P h

/-- A Lean predicate is `YiComputable` iff some YiInstr program decides it. -/
def YiComputable (decide : List YiInstr → Hexagram → Bool) : Prop :=
  ∃ D_decide : List YiInstr, YiDecides D_decide decide

/-- The YiComputable-restricted version of KleeneInverter: for any YiComputable
    Lean predicate, a counter-example program exists. -/
def YiKleeneInverter : Prop :=
  ∀ (decide : List YiInstr → Hexagram → Bool),
    YiComputable decide →
    ∃ D : List YiInstr, ∀ h : Hexagram, Halts D h ↔ decide D h = false

/-! ## § 4 Universal interpreter, s-m-n, and diagonal compiler interfaces

  The primitive gaps are now split at witness level:
  - `UniversalInterpSpec U`: one concrete universal interpreter program.
  - `SmnSpec subst`: one concrete specialization compiler.
  - `KleeneFixedPointExists`: a program-level fixed-point interface.
  - `BoolInverterCompilerExists`: a compiler from Bool deciders to halting
    inversions.

  The last two are the exact Lean interfaces needed to prove
  `YiKleeneInverter`; the theorem below proves that assembly without adding
  any axiom. -/

/-- **Universal interpreter** spec: a YiInstr program `U` that, when run
    with input `(encProg P)` on history and initial hexagram `h`, halts iff
    `P` halts on `h`.

    This is the FUNDAMENTAL primitive needed for Church-Turing in BaguaTuring.
    The current `ProgEnc.encProg` is a raw concatenation, while
    `ProgEnc.decInstrs` needs an external instruction count.  Therefore this
    spec is stronger than the existing round-trip theorem: a witness must
    either interpret the raw finite history directly, or introduce/prove a
    compatible length-delimited input convention. -/
def UniversalInterpSpec (U : List YiInstr) : Prop :=
  ∀ (P : List YiInstr) (h : Hexagram),
    Halts P h ↔ HaltsWith U h (ProgEnc.encProg P)

/-- Existence form for a universal interpreter witness. -/
def UniversalInterpExists : Prop :=
  ∃ U : List YiInstr, UniversalInterpSpec U

/-- Any universal interpreter satisfying the current spec must halt on empty
    program input, because the empty object program itself halts. -/
theorem universalInterpSpec_empty_input {U : List YiInstr}
    (hU : UniversalInterpSpec U) (h : Hexagram) :
    HaltsWith U h (ProgEnc.encProg ([] : List YiInstr)) := by
  exact (hU [] h).mp (halts_empty_prog h)

/-! ### § 4.1 Bounded universal interpreter spec

  The realisable variant: `U` correctly simulates `P` on `h` for every
  bounded `P` (length-prefix and jump targets within one R8).  Pure
  YiInstr cannot realise the unbounded variant because the ISA lacks
  multiplication, but the Lean-side universe of programs we ever construct
  in this codebase satisfies the bound. -/

/-- **Bounded universal interpreter** spec: same correctness as
    `UniversalInterpSpec` but only required for `ProgBounded P`.  A
    metaInterpProg constructed in pure YiInstr satisfies this restricted
    form. -/
def UniversalInterpSpecBounded (U : List YiInstr) : Prop :=
  ∀ (P : List YiInstr) (h : Hexagram),
    ProgBounded P → (Halts P h ↔ HaltsWith U h (ProgEnc.encProg P))

/-- Existence form for a bounded universal interpreter witness. -/
def UniversalInterpExistsBounded : Prop :=
  ∃ U : List YiInstr, UniversalInterpSpecBounded U

/-- Trivially, the unbounded spec implies the bounded one (the bounded
    requirement is weaker). -/
theorem universalInterpSpec_to_bounded {U : List YiInstr}
    (hU : UniversalInterpSpec U) : UniversalInterpSpecBounded U := by
  intro P h _
  exact hU P h

theorem universalInterpExists_to_bounded :
    UniversalInterpExists → UniversalInterpExistsBounded := by
  intro ⟨U, hU⟩
  exact ⟨U, universalInterpSpec_to_bounded hU⟩

/-- **s-m-n parameterization** spec: a Lean function `subst` such that
    `subst P input_cells` is a YiInstr program that, when run, behaves as
    `P` would when run with `input_cells` already on its history.

    A tempting implementation is `subst P input = pushList input ++ P`, but
    this is not currently available for arbitrary `R8`: `YiInstr` has
    relative hex transformations and `setShi`, not hex literals or absolute
    yao tests.  Proving this spec therefore needs either a new literal/macro
    layer, or a different self-encoding construction.

    Together with `UniversalInterpExists`, this gives Kleene's recursion. -/
def SmnSpec (subst : List YiInstr → List R8 → List YiInstr) : Prop :=
  ∀ (P : List YiInstr) (input : List R8) (h : Hexagram),
    HaltsWith P h input ↔ Halts (subst P input) h

/-- Existence form for an s-m-n specialization compiler witness. -/
def SmnExists : Prop :=
  ∃ subst : List YiInstr → List R8 → List YiInstr, SmnSpec subst

/-- Immediate sanity check for any s-m-n witness: specializing empty input
    cannot change halting behavior. -/
theorem smnSpec_empty_input {subst : List YiInstr → List R8 → List YiInstr}
    (hsubst : SmnSpec subst) (P : List YiInstr) (h : Hexagram) :
    Halts (subst P []) h ↔ Halts P h :=
  (hsubst P [] h).symm.trans (haltsWith_empty P h)

/-- **Program-level fixed point interface**: every one-input program `F` has a
    closed program `D` whose halting behavior is `F` run with `encProg D` as
    its initial history.  This is the quine/recursion-theorem payload. -/
def KleeneFixedPointExists : Prop :=
  ∀ F : List YiInstr,
    ∃ D : List YiInstr, ∀ h : Hexagram,
      Halts D h ↔ HaltsWith F h (ProgEnc.encProg D)

/-- **Bool inverter compiler interface**: from any concrete decider program
    `D_decide`, build a one-input program `invert` that consumes `encProg P`,
    runs the decider on `(P, h)`, and halts exactly when the decider's defined
    final Bool readout is false.

    The quantification over `decide` keeps the compiler independent from the
    Lean-level predicate; it only relies on the concrete witness
    `YiDecides D_decide decide`. -/
def BoolInverterCompilerExists : Prop :=
  ∀ D_decide : List YiInstr,
    ∃ invert : List YiInstr,
      ∀ (decide : List YiInstr → Hexagram → Bool),
        YiDecides D_decide decide →
        ∀ (P : List YiInstr) (h : Hexagram),
          HaltsWith invert h (ProgEnc.encProg P) ↔ decide P h = false

/-- The fixed-point compiler is expected to be derived from the universal
    interpreter plus s-m-n.  This separates the recursion-theorem payload from
    the Bool-output inversion compiler. -/
def KleeneFixedPointFromPrimitives : Prop :=
  UniversalInterpExists → SmnExists → KleeneFixedPointExists

/-- The Bool inverter compiler is expected to use a universal evaluator, not
    merely the halting-only `UniversalInterpSpec`, plus a small "if final
    Shi is false then halt, else loop" suffix.  Kept as an explicit compiler
    premise until such an evaluator spec exists. -/
def BoolInverterCompilerFromUniversal : Prop :=
  UniversalInterpExists → BoolInverterCompilerExists

/-- **Diagonal construction package**: the remaining compiler obligations after
    `UniversalInterpExists` and `SmnExists` are available. -/
def KleeneFromPrimitives : Prop :=
  KleeneFixedPointFromPrimitives ∧ BoolInverterCompilerFromUniversal

/-- Once the fixed-point and Bool-inverter interfaces exist, the
    YiComputable-restricted Kleene inverter is a direct Lean theorem. -/
theorem yi_kleene_from_fixedpoint_and_inverter
    (h_fixed : KleeneFixedPointExists)
    (h_invert : BoolInverterCompilerExists) :
    YiKleeneInverter := by
  intro decide h_comp
  obtain ⟨D_decide, h_decides⟩ := h_comp
  obtain ⟨invert, h_invert_spec⟩ := h_invert D_decide
  obtain ⟨D, h_fixed_spec⟩ := h_fixed invert
  refine ⟨D, ?_⟩
  intro h
  exact Iff.trans (h_fixed_spec h) (h_invert_spec decide h_decides D h)

/-- The primitive package yields `YiKleeneInverter` by instantiating the two
    compiler interfaces. -/
theorem yi_kleene_from_primitives
    (h_univ : UniversalInterpExists)
    (h_smn : SmnExists)
    (h_diag : KleeneFromPrimitives) :
    YiKleeneInverter :=
  yi_kleene_from_fixedpoint_and_inverter
    (h_diag.1 h_univ h_smn)
    (h_diag.2 h_univ)

/-! ## § 5 Church-Turing reformulation -/

/-- The unrestricted Church-Turing statement for all Lean Bool functions.
    This is kept only as a named stronger interface; the axiom-removal chain
    below deliberately uses the complement-restricted version. -/
def AllLeanDecidersAreYiComputable : Prop :=
  ∀ (decide : List YiInstr → Hexagram → Bool), YiComputable decide

/-- Historical public name for the Church-Turing interface used here:
    every complement-invariant Lean Bool decider is YiComputable.  This is the
    version compatible with `GodelLi.KleeneInverter`, whose quantifier is also
    restricted by `CuoInvariantDecide`. -/
def AllDecidersAreYiComputable : Prop :=
  ∀ (decide : List YiInstr → Hexagram → Bool),
    CuoInvariantDecide decide → YiComputable decide

/-- The old unrestricted Church-Turing statement implies the complement-restricted
    interface, but the path theorem below only requires the latter. -/
theorem all_deciders_from_all_lean_deciders :
    AllLeanDecidersAreYiComputable → AllDecidersAreYiComputable := by
  intro h_all decide _h_cuo
  exact h_all decide

/-- **Structural reduction**: the (now complement-invariant restricted)
    `KleeneInverter` follows from `YiKleeneInverter` plus Church-Turing.
    The complement-invariance precondition is now consumed exactly where the
    Church-Turing interface needs it. -/
theorem kleene_inverter_via_yi_kleene :
    YiKleeneInverter → AllDecidersAreYiComputable → KleeneInverter := by
  intro h_yi h_ct decide h_cuo
  exact h_yi decide (h_ct decide h_cuo)

/-! ## § 6 Path to 0-axiom

  The full chain.  Given:
  - `UniversalInterpExists`     (~ 700 lines mechanical engineering)
  - `SmnExists`                 (~ 50 lines)
  - `KleeneFromPrimitives`      (fixed-point + Bool-inverter compilers)
  - `AllDecidersAreYiComputable` (complement-restricted Church-Turing meta-interface)

  We deduce `KleeneInverter` as a Lean theorem, removing
  `kleene_recursion_axiom` from `GodelLi.lean`. -/

/-- **Path theorem**: assemble the four ingredients into the original
    `KleeneInverter` as a theorem.  Each hypothesis corresponds to a precise
    bullet of remaining work; this theorem is the structural blueprint. -/
theorem path_to_zero_axiom :
    UniversalInterpExists →
    SmnExists →
    KleeneFromPrimitives →
    AllDecidersAreYiComputable →
    KleeneInverter := by
  intro h_univ h_smn h_diag h_ct
  exact kleene_inverter_via_yi_kleene
    (yi_kleene_from_primitives h_univ h_smn h_diag) h_ct

/-! ## § 7 Public summary -/

/-- Bundle of the path's structural pieces. -/
theorem kleene_internal_summary :
    -- (1) RunWith / HaltsWith input convention is well-defined
    (∀ h prog, RunWith h prog [] = YiState.init h prog)
    ∧ -- (2) Empty-input HaltsWith reduces to Halts
    (∀ P h, HaltsWith P h [] ↔ Halts P h)
    ∧ -- (3) Fixed-point + Bool-inverter ⇒ YiKleeneInverter
    (KleeneFixedPointExists → BoolInverterCompilerExists → YiKleeneInverter)
    ∧ -- (4) Primitives package ⇒ YiKleeneInverter
    (UniversalInterpExists → SmnExists → KleeneFromPrimitives → YiKleeneInverter)
    ∧ -- (5) Structural: YiKleene + Church-Turing ⇒ KleeneInverter
    (YiKleeneInverter → AllDecidersAreYiComputable → KleeneInverter)
    ∧ -- (6) Path: primitives + complement CT ⇒ axiom-free Kleene
    (UniversalInterpExists → SmnExists →
       KleeneFromPrimitives → AllDecidersAreYiComputable → KleeneInverter) :=
  ⟨runWith_empty, haltsWith_empty,
   yi_kleene_from_fixedpoint_and_inverter,
   yi_kleene_from_primitives,
   kleene_inverter_via_yi_kleene, path_to_zero_axiom⟩

end SSBX.Foundation.Bagua.KleeneInternal
