/-
# R4CarryUniversalPlan -- strong loop surface for R4-squared carry

The R4-squared carry path can honestly reach the public restored universal
surface only after the executable fetch, restore-row embedding, and exact block
witnesses produce a full per-iteration META state.  This sidecar records that
strong target and proves that it is sufficient for the existing restored
semantic loop obligations.

The file does not claim that the concrete walker or exact blocks are complete.
It factors the final obligation so later phases can fill a single, auditable
state-equality contract instead of duplicating loop induction at every layer.
-/
import SSBX.Foundation.Wen.MetaInterp.R4CarryAssemblyPlan
import SSBX.Foundation.Wen.MetaInterp.R4CarryFetchFactor
import SSBX.Foundation.Wen.MetaInterp.UniversalRestorePlan

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryUniversalPlan

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.R4Carry
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
open SSBX.Foundation.Wen.MetaInterp.R4CarryAssemblyPlan
open SSBX.Foundation.Wen.MetaInterp.R4CarryFetchFactor
open SSBX.Foundation.Wen.MetaInterp.UniversalRestorePlan

/-! ## Strong loop state -/

/-- The exact state expected after one restored semantic iteration.

Unlike `metaStateOf`, this record mirrors `sim.halted` into META.halted.  That
is the state shape needed for induction after a simulated halt: further fuel
must leave the META machine fixed, just as the object machine is fixed. -/
def restoredLoopStateOf
    (regHex : Hexagram) (sim : YiState) : YiState :=
  { cur := sim.cur
    history := encMetaHistory regHex sim
    pc := fetchOffset
    prog := restoredMetaInterpProg
    halted := sim.halted }

private theorem runFuel_halted_fixed (s : YiState) (h : s.halted = true) :
    ∀ n, s.runFuel n = s := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      unfold YiState.runFuel
      simp [h]

/-! ## R4-carry exact step obligations -/

/-- Final exact-step target for the R4-squared carry architecture.

Later executable phases should prove these fields by composing:
decoded carry fetch, generated carry-row restore, exact block witnesses, and
fetch-level halt detection.  The structure deliberately avoids R5+ word names;
it speaks only in R4/R8 carry, dispatch, and META state terms. -/
structure R4CarryExactStepObligations : Prop where
  firstState :
    ∀ regHex sim,
      sim.halted = false →
        (metaStateOf regHex sim restoredMetaInterpProg outerLoopOffset).runFuel
          restoredLoopFuelPerIter =
        restoredLoopStateOf regHex sim.step
  steadyState :
    ∀ regHex sim,
      sim.halted = false →
        (restoredLoopStateOf regHex sim).runFuel restoredLoopFuelPerIter =
        restoredLoopStateOf regHex sim.step
  haltedPadding :
    ∀ regHex sim extraFuel,
      sim.halted = true →
        let μ := metaStateOf regHex sim restoredMetaInterpProg outerLoopOffset
        let μ' := μ.runFuel (restoredLoopFuelPerIter + extraFuel)
        μ'.history = encMetaHistory regHex sim ∧ μ'.halted = true

/-! ## Loop induction from the strong state contract -/

theorem restoredLoopState_runFuel_chunks
    (O : R4CarryExactStepObligations)
    (regHex : Hexagram) :
    ∀ sim k,
      (restoredLoopStateOf regHex sim).runFuel
          (restoredLoopFuelPerIter * k) =
        restoredLoopStateOf regHex (sim.runFuel k) := by
  intro sim k
  induction k generalizing sim with
  | zero =>
      rfl
  | succ k ih =>
      have hmul :
          restoredLoopFuelPerIter * (k + 1) =
            restoredLoopFuelPerIter + restoredLoopFuelPerIter * k := by
        rw [Nat.mul_succ, Nat.add_comm]
      rw [hmul, runFuel_add]
      by_cases hhalt : sim.halted = true
      · have h_loop_halted :
            (restoredLoopStateOf regHex sim).halted = true := by
          simp [restoredLoopStateOf, hhalt]
        rw [runFuel_halted_fixed
          (restoredLoopStateOf regHex sim) h_loop_halted restoredLoopFuelPerIter]
        rw [runFuel_halted_fixed
          (restoredLoopStateOf regHex sim) h_loop_halted
          (restoredLoopFuelPerIter * k)]
        rw [runFuel_halted_fixed sim hhalt (k + 1)]
      · have hfalse : sim.halted = false := by
          cases hs : sim.halted <;> simp [hs] at hhalt ⊢
        have hstep :
            sim.runFuel (k + 1) = sim.step.runFuel k := by
          rw [show sim.runFuel (k + 1) =
            (if sim.halted = true then sim else sim.step.runFuel k) from rfl]
          simp [hfalse]
        rw [O.steadyState regHex sim hfalse]
        rw [hstep]
        exact ih sim.step

theorem exactLoop_of_r4CarryExactStep
    (O : R4CarryExactStepObligations) :
    ∀ regHex P n,
      let simResult := (YiState.init regHex P).runFuel n
      let metaResult :=
        (restoredMetaPostPrologue regHex P).runFuel
          (restoredLoopFuelPerIter * n)
      metaResult.history = encMetaHistory regHex simResult ∧
        metaResult.halted = simResult.halted := by
  intro regHex P n
  cases n with
  | zero =>
      dsimp [restoredMetaPostPrologue, metaStateOf, YiState.init]
      exact ⟨rfl, rfl⟩
  | succ k =>
      let sim0 := YiState.init regHex P
      have hmul :
          restoredLoopFuelPerIter * (k + 1) =
            restoredLoopFuelPerIter + restoredLoopFuelPerIter * k := by
        rw [Nat.mul_succ, Nat.add_comm]
      have hfirst :
          (restoredMetaPostPrologue regHex P).runFuel restoredLoopFuelPerIter =
            restoredLoopStateOf regHex sim0.step := by
        exact O.firstState regHex sim0 rfl
      have hchunks :
          (restoredLoopStateOf regHex sim0.step).runFuel
              (restoredLoopFuelPerIter * k) =
            restoredLoopStateOf regHex (sim0.step.runFuel k) :=
        restoredLoopState_runFuel_chunks O regHex sim0.step k
      have hsim :
          sim0.runFuel (k + 1) = sim0.step.runFuel k := by
        rw [show sim0.runFuel (k + 1) =
          (if sim0.halted = true then sim0 else sim0.step.runFuel k) from rfl]
        simp [sim0, YiState.init]
      dsimp [sim0]
      rw [hmul, runFuel_add, hfirst, hchunks, hsim]
      simp [restoredLoopStateOf]

/-! ## Projection to the existing restored universal surface -/

def R4CarryExactStepObligations.toLoop
    (O : R4CarryExactStepObligations) :
    RestoredSemanticLoopObligations where
  firstIteration := by
    intro regHex sim _ h_alive
    dsimp
    rw [O.firstState regHex sim h_alive]
    simp [restoredLoopStateOf]
  steadyIteration := by
    intro regHex sim _ h_alive
    dsimp
    have hstart :
        restoredMetaFetchState regHex sim = restoredLoopStateOf regHex sim := by
      simp [restoredMetaFetchState, restoredLoopStateOf, metaStateOf, h_alive]
    rw [hstart, O.steadyState regHex sim h_alive]
    simp [restoredLoopStateOf]
  kIterations := exactLoop_of_r4CarryExactStep O
  haltedPadding := O.haltedPadding

def R4CarryExactStepObligations.toCompose
    (O : R4CarryExactStepObligations) :
    RestoredSemanticComposeObligations :=
  RestoredSemanticComposeObligations.ofLoop O.toLoop

theorem r4_carry_universal_plan_summary :
    (R4CarryExactStepObligations → RestoredSemanticLoopObligations)
    ∧ (R4CarryExactStepObligations → RestoredSemanticComposeObligations)
    ∧ (R4CarryExactStepObligations →
      ∀ regHex P n,
        let simResult := (YiState.init regHex P).runFuel n
        let metaResult :=
          (restoredMetaStart regHex P).runFuel (restoredExactMetaFuel n)
        metaResult.history = encMetaHistory regHex simResult ∧
          metaResult.halted = simResult.halted) := by
  exact
    ⟨ R4CarryExactStepObligations.toLoop
    , R4CarryExactStepObligations.toCompose
    , fun O => restoredMetaInterpProg_simulates_from_loop O.toLoop
    ⟩

end SSBX.Foundation.Wen.MetaInterp.R4CarryUniversalPlan
