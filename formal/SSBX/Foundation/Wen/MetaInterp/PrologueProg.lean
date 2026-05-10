/-
# PrologueProg — concrete materialization of the META prologue as `List YiInstr`

This file re-exports, at base-256, the META prologue program for the universal
meta-interpreter under a name and interface that matches the F.1-era
assembly pipeline (`prologue ++ outerLoop ++ fetch ++ dispatch ++ blocks ++ halt`).

The architecture file `MetaInterp.lean` already defines `prologueProg`
(5 instructions) along with full correctness proofs `afterPrologue_cur`,
`afterPrologue_history`, `afterPrologue_pc`, `afterPrologue_halted`,
`afterPrologue_prog`, and the headline
`afterPrologue_history_eq_encMetaHistory`.  Since the prologue is *itself*
a `List YiInstr`, the concrete `prologueProg` exposed here is a thin alias —
but having it under its own namespace keeps `metaInterpProg` assembly
self-documenting and matches the `DispatchProg` mirror pattern.

## Contents

* `prologueProg : List YiInstr` — alias of `MetaInterp.prologueProg`
* `prologueProg_length` — length = 5
* `outerLoopOffset` — the natural fall-through offset (= `prologueProg.length`)
* `postPrologueContract` — bundled invariants the assembly agent will rely on

## Notes for assembly

The existing prologue ends with `pc = 5` by **fall-through** (no explicit
`jump`); the trailing `YiInstr.setShi Shi.jin` simply finishes and pc
advances to 5.  Therefore the assembly agent should place the outer loop
entry at exactly `outerLoopOffset = prologueProg.length = 5` when this
program is the head of `metaInterpProg`.

The full proof that META.history after the prologue equals
`encMetaHistory h (YiState.init h P)` is already discharged upstream by
`MetaInterp.afterPrologue_history_eq_encMetaHistory`; we re-export it here.
-/
import SSBX.Foundation.Wen.MetaInterp

namespace SSBX.Foundation.Wen.MetaInterp.PrologueProg

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  Tier A — concrete `prologueProg` -/

/-- The concrete META prologue program.  Materializes the 5-instruction
    state-initialization sequence as a `List YiInstr`.

    This is a definitional alias for `MetaInterp.prologueProg`; it exists
    so that `metaInterpProg` assembly can refer to a dedicated name without
    leaking the parent `MetaInterp` namespace's other definitions. -/
def prologueProg : List YiInstr := MetaInterp.prologueProg

@[simp] theorem prologueProg_eq_metaPrologue :
    prologueProg = MetaInterp.prologueProg := rfl

/-! ## § 2  Tier B — length lemma -/

@[simp] theorem prologueProg_length : prologueProg.length = 5 :=
  MetaInterp.prologueProg_length

/-- The canonical outer-loop entry offset assuming `prologueProg` is the
    head of `metaInterpProg`.  Equal to `prologueProg.length = 5`.

    The assembly agent should place `outerLoopEntry` at exactly this offset. -/
def outerLoopOffset : Nat := prologueProg.length

@[simp] theorem outerLoopOffset_eq_five : outerLoopOffset = 5 := rfl

/-! ## § 3  Tier C — post-prologue contract

After running `prologueProg` for exactly `prologueProg.length = 5` fuel
steps starting from the fresh `RunWith h prologueProg (encProg P)` state,
the META state satisfies:

* `cur     = (h, Shi.jin)        = (YiState.init h P).cur`
* `history = encMetaHistory h (YiState.init h P)`
* `pc      = outerLoopOffset = 5`
* `halted  = false`
* `prog    = prologueProg`

All five invariants are direct corollaries of the upstream
`afterPrologue_*` theorems.
-/

/-- Cur after the prologue equals the cur of the initial sim-state. -/
theorem afterPrologue_cur (h : Hexagram) (P : List YiInstr) :
    ((RunWith h prologueProg (ProgEnc.encProg P)).runFuel prologueProg.length).cur
      = (YiState.init h P).cur :=
  MetaInterp.afterPrologue_cur h P

/-- History after the prologue equals the encoded META-history of the
    initial sim-state. -/
theorem afterPrologue_history (h : Hexagram) (P : List YiInstr) :
    ((RunWith h prologueProg (ProgEnc.encProg P)).runFuel prologueProg.length).history
      = encMetaHistory h (YiState.init h P) :=
  MetaInterp.afterPrologue_history_eq_encMetaHistory h P

/-- PC after the prologue equals `outerLoopOffset`. -/
theorem afterPrologue_pc (h : Hexagram) (P : List YiInstr) :
    ((RunWith h prologueProg (ProgEnc.encProg P)).runFuel prologueProg.length).pc
      = outerLoopOffset :=
  MetaInterp.afterPrologue_pc h P

/-- Halted-flag after the prologue is false (META still running). -/
theorem afterPrologue_halted (h : Hexagram) (P : List YiInstr) :
    ((RunWith h prologueProg (ProgEnc.encProg P)).runFuel prologueProg.length).halted
      = false :=
  MetaInterp.afterPrologue_halted h P

/-- Program after the prologue is unchanged (still `prologueProg`).  When
    the prologue is embedded as the head of a larger `metaInterpProg`,
    `RunWith` is invoked with the full program, and this lemma's analogue
    in that context follows by the standard "program field is invariant
    under `step`" argument the assembly agent will discharge.  -/
theorem afterPrologue_prog (h : Hexagram) (P : List YiInstr) :
    ((RunWith h prologueProg (ProgEnc.encProg P)).runFuel prologueProg.length).prog
      = prologueProg :=
  MetaInterp.afterPrologue_prog h P

/-- **Post-prologue contract (bundled).**  Starting from the fresh
    `RunWith h prologueProg (encProg P)` state, after `prologueProg.length`
    fuel ticks the META state matches the canonical
    `metaStateOf h (YiState.init h P) prologueProg outerLoopOffset`. -/
theorem postPrologueContract (h : Hexagram) (P : List YiInstr) :
    (RunWith h prologueProg (ProgEnc.encProg P)).runFuel prologueProg.length
      = metaStateOf h (YiState.init h P) prologueProg outerLoopOffset := by
  -- Two `YiState`s are equal iff all five fields agree.  We close each
  -- field using the upstream `afterPrologue_*` lemmas.
  have hc := afterPrologue_cur h P
  have hh := afterPrologue_history h P
  have hp := afterPrologue_pc h P
  have hg := afterPrologue_prog h P
  have hd := afterPrologue_halted h P
  -- Destructure the LHS YiState; metaStateOf is a mk-literal, so the
  -- equality reduces to field-by-field.
  rcases hlhs :
    (RunWith h prologueProg (ProgEnc.encProg P)).runFuel prologueProg.length
    with ⟨c, hist, pc, prog, halt⟩
  rw [hlhs] at hc hh hp hg hd
  simp only at hc hh hp hg hd
  subst hc; subst hh; subst hp; subst hg; subst hd
  rfl

end SSBX.Foundation.Wen.MetaInterp.PrologueProg
