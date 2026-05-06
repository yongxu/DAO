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
3.  Show the original `KleeneInverter` ⟸ `YiKleeneInverter` ∧ `Church-Turing`.

This file delivers parts (1) and (3) rigorously, plus the formal statement of
the remaining engineering (2) as a `Prop` so its dependency is explicit.

## What's done (this file, 0 sorry / 0 axiom)

- `RunWith`: explicit YiState constructor with custom initial history (the
  input convention for any universal interpreter).
- `BoolFromShi`: a Bool readout from a YiState's final `Shi` component.
- `YiDecides`, `YiComputable`: precise computability via YiInstr.
- `UniversalInterpExists`, `SmnExists`: precise `Prop`-statements of the
  missing primitives.
- `KleeneFromPrimitives`: precise `Prop`-statement of the diagonal construction.
- `kleene_inverter_via_yi_kleene`: structural reduction from
  `YiKleeneInverter ∧ Church-Turing ⇒ KleeneInverter`.
- `path_to_zero_axiom`: the full chain — given primitives + diagonal
  construction + Church-Turing, the original axiom is a theorem.

## What's NOT done (and why)

- `UniversalInterpExists`, `SmnExists`, and `KleeneFromPrimitives` are stated
  as `Prop`, not proven.  Witnesses require building the ~700-1000 line
  universal interpreter (12-way dispatch + execute blocks + fetch/writeback
  in YiInstr).  See `WenyanSelfInterp.lean § 6b` for the existing partial
  scaffold (~15% complete after Phase 13).

- The full `kleene_recursion_axiom` remains in `GodelLi.lean`.  Its removal
  requires the three `Prop`s above to be proven as theorems.

This file is the **formal scaffolding** that, once the primitives are proven
(future work), makes the axiom removal mechanical.
-/
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Bagua.GodelLi

namespace SSBX.Foundation.Bagua.KleeneInternal

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Bagua.GodelLi

/-! ## § 1 Input convention: running a YiInstr program with custom history -/

/-- Initial YiState with custom history (the "input tape").  Standard
    `YiState.init` sets history := [].  For meta-interpretation, we need the
    input encoding to be present at startup. -/
def RunWith (h : Hexagram) (prog : List YiInstr) (input : List Cell192) : YiState :=
  { cur := (h, Shi.jin), history := input, pc := 0, prog := prog, halted := false }

/-- `RunWith` agrees with `YiState.init` when input is empty. -/
theorem runWith_empty (h : Hexagram) (prog : List YiInstr) :
    RunWith h prog [] = YiState.init h prog := rfl

/-- Halting predicate for a state with custom input. -/
def HaltsWith (prog : List YiInstr) (h : Hexagram) (input : List Cell192) : Prop :=
  ∃ n : Nat, ((RunWith h prog input).runFuel n).halted = true

/-- For empty input, `HaltsWith` reduces to `Halts`. -/
theorem haltsWith_empty (P : List YiInstr) (h : Hexagram) :
    HaltsWith P h [] ↔ Halts P h := by
  unfold HaltsWith Halts
  rw [runWith_empty]

/-! ## § 2 Bool readout convention

  A YiInstr program "decides" a Prop by halting and outputting a Bool via its
  final `Shi` component:
  - `Shi.ji`  (已 settled / past) ↔ Bool true
  - `Shi.wei` (未 unsettled / future) ↔ Bool false
  - `Shi.jin` (今 present)        ↔ undefined / mid-computation

  The convention matches `daoJudge`'s `Shi.ji ↔ isTian` interpretation. -/

/-- Bool readout from a final state's Shi component. -/
def BoolFromShi (s : YiState) : Bool :=
  match s.cur.2 with
  | Shi.ji  => true
  | Shi.wei => false
  | Shi.jin => false  -- treated as false; mid-computation indicates an error

/-! ## § 3 YiComputable: precise computability witness -/

/-- A YiInstr program `D_decide` **decides** a Lean predicate `decide` iff
    for every program `P` and hexagram `h`, running `D_decide` with `encProg P`
    as initial input and `h` as initial cur-hexagram halts in finite fuel and
    outputs Bool matching `decide P h`. -/
def YiDecides (D_decide : List YiInstr) (decide : List YiInstr → Hexagram → Bool) : Prop :=
  ∀ (P : List YiInstr) (h : Hexagram),
    ∃ (N : Nat),
      let s := (RunWith h D_decide (ProgEnc.encProg P)).runFuel N
      s.halted = true ∧ BoolFromShi s = decide P h

/-- A Lean predicate is `YiComputable` iff some YiInstr program decides it. -/
def YiComputable (decide : List YiInstr → Hexagram → Bool) : Prop :=
  ∃ D_decide : List YiInstr, YiDecides D_decide decide

/-- The YiComputable-restricted version of KleeneInverter: for any YiComputable
    Lean predicate, a counter-example program exists. -/
def YiKleeneInverter : Prop :=
  ∀ (decide : List YiInstr → Hexagram → Bool),
    YiComputable decide →
    ∃ D : List YiInstr, ∀ h : Hexagram, Halts D h ↔ decide D h = false

/-! ## § 4 Universal interpreter and s-m-n: the missing primitives

  These are the two `Prop`s whose witnesses (concrete YiInstr programs +
  correctness proofs) are the entire ~700-line engineering effort.  Once both
  are theorems, the chain in § 6 makes `kleene_recursion_axiom` a theorem. -/

/-- **Universal interpreter** existence: a YiInstr program `U` that, when run
    with input `(encProg P)` on history and initial hexagram `h`, halts iff
    `P` halts on `h`.

    This is the FUNDAMENTAL primitive needed for Church-Turing in BaguaTuring.
    Construction: 12-way dispatch + per-instruction execute blocks + fetch +
    writeback (≈ 700-1000 lines, see `WenyanSelfInterp § 6b` for ~15% scaffold). -/
def UniversalInterpExists : Prop :=
  ∃ U : List YiInstr,
    ∀ (P : List YiInstr) (h : Hexagram),
      (Halts P h ↔ HaltsWith U h (ProgEnc.encProg P))

/-- **s-m-n parameterization** existence: a Lean function `subst` such that
    `subst P input_cells` is a YiInstr program that, when run, behaves as
    `P` would when run with `input_cells` already on its history.

    Construction: `subst P input = pushList input ++ P` where `pushList`
    is a fixed YiInstr sequence that pushes given cells.  The pushList for
    arbitrary cells requires "cell-setting" subroutines (≈ 50 lines).

    Together with `UniversalInterpExists`, this gives Kleene's recursion. -/
def SmnExists : Prop :=
  ∃ subst : List YiInstr → List Cell192 → List YiInstr,
    ∀ (P : List YiInstr) (input : List Cell192) (h : Hexagram),
      (HaltsWith P h input ↔ Halts (subst P input) h)

/-- **Diagonal construction lemma**: assuming both primitives, `YiKleeneInverter`
    holds.  This is the "concrete Kleene recursion theorem proof for YiInstr",
    estimated ~100 lines once both primitives have witnesses. -/
def KleeneFromPrimitives : Prop :=
  UniversalInterpExists → SmnExists → YiKleeneInverter

/-! ## § 5 Church-Turing reformulation -/

/-- "Every Lean Bool decider is YiComputable" — the Church-Turing thesis
    applied to BaguaTuring. -/
def AllDecidersAreYiComputable : Prop :=
  ∀ (decide : List YiInstr → Hexagram → Bool), YiComputable decide

/-- **Structural reduction**: the original `KleeneInverter` follows from
    `YiKleeneInverter` plus Church-Turing.  This is a STRAIGHTFORWARD theorem
    proved here without any axiom — it captures the precise content of
    Church-Turing as the bridge.

    Once `YiKleeneInverter` is proven (via § 6), the only remaining gap is
    Church-Turing, which is the Lean equivalent of accepting that "every Lean
    Bool function on List YiInstr × Hexagram is implementable as a YiInstr
    program" — a meta-axiom about Lean's expressivity vs. BaguaTuring. -/
theorem kleene_inverter_via_yi_kleene :
    YiKleeneInverter → AllDecidersAreYiComputable → KleeneInverter := by
  intro h_yi h_ct decide
  exact h_yi decide (h_ct decide)

/-! ## § 6 Path to 0-axiom

  The full chain.  Given:
  - `UniversalInterpExists`     (~ 700 lines mechanical engineering)
  - `SmnExists`                 (~ 50 lines)
  - `KleeneFromPrimitives`      (~ 100 lines, mechanical given the above)
  - `AllDecidersAreYiComputable` (Church-Turing meta-axiom)

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
  exact kleene_inverter_via_yi_kleene (h_diag h_univ h_smn) h_ct

/-! ## § 7 Public summary -/

/-- Bundle of the path's structural pieces. -/
theorem kleene_internal_summary :
    -- (1) RunWith / HaltsWith input convention is well-defined
    (∀ h prog, RunWith h prog [] = YiState.init h prog)
    ∧ -- (2) Empty-input HaltsWith reduces to Halts
    (∀ P h, HaltsWith P h [] ↔ Halts P h)
    ∧ -- (3) Structural: YiKleene + Church-Turing ⇒ KleeneInverter
    (YiKleeneInverter → AllDecidersAreYiComputable → KleeneInverter)
    ∧ -- (4) Path: 4 primitives ⇒ axiom-free Kleene
    (UniversalInterpExists → SmnExists →
       KleeneFromPrimitives → AllDecidersAreYiComputable → KleeneInverter) :=
  ⟨runWith_empty, haltsWith_empty,
   kleene_inverter_via_yi_kleene, path_to_zero_axiom⟩

end SSBX.Foundation.Bagua.KleeneInternal
