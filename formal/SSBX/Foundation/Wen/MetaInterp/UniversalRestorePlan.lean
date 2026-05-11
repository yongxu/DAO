/-
# UniversalRestorePlan -- universal-compose interface for restored assembly

This sidecar mirrors `Universal.lean` for `AssemblyRestorePlan.restoredMetaInterpProg`.
It does not replace the current Strategy-B public theorem.  Its job is to give
the restored 100-instruction layout a clean semantic-obligation target before
the concrete fetch walker and block witnesses are complete.
-/

import SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

namespace SSBX.Foundation.Wen.MetaInterp.UniversalRestorePlan

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

/-! ## Restored universal-compose surface -/

def restoredMetaFuelBound (n : Nat) : Nat :=
  restoredMetaInterpProg.length * (n + 5)

def restoredMetaStart (h : Hexagram) (P : List YiInstr) : YiState :=
  RunWith h restoredMetaInterpProg (ProgEnc.encProg P)

def restoredMetaPostPrologue (h : Hexagram) (P : List YiInstr) : YiState :=
  metaStateOf h (YiState.init h P) restoredMetaInterpProg outerLoopOffset

def restoredMetaFetchState (h : Hexagram) (sim : YiState) : YiState :=
  metaStateOf h sim restoredMetaInterpProg fetchOffset

theorem restoredMetaStart_runFuel_five_eq_postPrologue
    (h : Hexagram) (P : List YiInstr) :
    (restoredMetaStart h P).runFuel 5 = restoredMetaPostPrologue h P := by
  rfl

def restoredLoopFuelPerIter : Nat := restoredMetaInterpProg.length

def restoredExactMetaFuel (n : Nat) : Nat :=
  5 + restoredLoopFuelPerIter * n

theorem restoredExactMetaFuel_zero :
    restoredExactMetaFuel 0 = 5 := by
  simp [restoredExactMetaFuel]

theorem restoredMetaInterpProg_simulates_zero_steps
    (h : Hexagram) (P : List YiInstr) :
    let simResult := (YiState.init h P).runFuel 0
    let metaResult := (restoredMetaStart h P).runFuel (restoredExactMetaFuel 0)
    metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted := by
  rw [restoredExactMetaFuel_zero, restoredMetaStart_runFuel_five_eq_postPrologue h P]
  simp [restoredMetaPostPrologue, metaStateOf, YiState.runFuel, YiState.init]

/-! ## Restored loop obligations -/

structure RestoredSemanticLoopObligations : Prop where
  firstIteration :
    ∀ h sim,
      (sim.prog ≠ [] → True) →
      sim.halted = false →
        let μ := metaStateOf h sim restoredMetaInterpProg outerLoopOffset
        let μ' := μ.runFuel restoredLoopFuelPerIter
        μ'.history = encMetaHistory h sim.step ∧
        μ'.halted = sim.step.halted ∧
        μ'.pc = fetchOffset
  steadyIteration :
    ∀ h sim,
      (sim.prog ≠ [] → True) →
      sim.halted = false →
        let μ := restoredMetaFetchState h sim
        let μ' := μ.runFuel restoredLoopFuelPerIter
        μ'.history = encMetaHistory h sim.step ∧
        μ'.halted = sim.step.halted ∧
        μ'.pc = fetchOffset
  kIterations :
    ∀ h P k,
      let μ₀ := restoredMetaPostPrologue h P
      let μ_k := μ₀.runFuel (restoredLoopFuelPerIter * k)
      let sim_k := (YiState.init h P).runFuel k
      μ_k.history = encMetaHistory h sim_k ∧
      μ_k.halted = sim_k.halted
  haltedPadding :
    ∀ h sim extraFuel,
      sim.halted = true →
        let μ := metaStateOf h sim restoredMetaInterpProg outerLoopOffset
        let μ' := μ.runFuel (restoredLoopFuelPerIter + extraFuel)
        μ'.history = encMetaHistory h sim ∧
        μ'.halted = true

theorem runFuel_add (s : YiState) (m n : Nat) :
    s.runFuel (m + n) = (s.runFuel m).runFuel n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have h1 : s.runFuel (m + (k + 1)) = (s.runFuel (m + k)).step := by
        have : m + (k + 1) = (m + k) + 1 := by omega
        rw [this, SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right]
      have h2 :
          (s.runFuel m).runFuel (k + 1) =
            ((s.runFuel m).runFuel k).step :=
        SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right _ _
      rw [h1, h2, ih]

theorem restoredMetaInterpProg_fuel_bound (n : Nat) :
    restoredExactMetaFuel n ≤ restoredMetaFuelBound n := by
  unfold restoredExactMetaFuel restoredLoopFuelPerIter restoredMetaFuelBound
  rw [restoredMetaInterpProg_length]
  have h1 : 100 * (n + 5) = 100 * n + 100 * 5 := Nat.mul_add 100 n 5
  omega

/-! ## Restored U.0 from obligations -/

structure RestoredSemanticComposeObligations : Prop where
  exactLoop :
    ∀ h P n,
      let simResult := (YiState.init h P).runFuel n
      let metaResult :=
        (restoredMetaPostPrologue h P).runFuel (restoredLoopFuelPerIter * n)
      metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted
  haltedPadding :
    ∀ h sim extraFuel,
      sim.halted = true →
        let μ := metaStateOf h sim restoredMetaInterpProg outerLoopOffset
        let μ' := μ.runFuel (restoredLoopFuelPerIter + extraFuel)
        μ'.history = encMetaHistory h sim ∧ μ'.halted = true

namespace RestoredSemanticComposeObligations

def ofLoop (O : RestoredSemanticLoopObligations) :
    RestoredSemanticComposeObligations where
  exactLoop := O.kIterations
  haltedPadding := O.haltedPadding

end RestoredSemanticComposeObligations

theorem restoredMetaInterpProg_simulates
    (O : RestoredSemanticComposeObligations)
    (h : Hexagram) (P : List YiInstr) (n : Nat) :
    let simResult := (YiState.init h P).runFuel n
    let metaResult := (restoredMetaStart h P).runFuel (restoredExactMetaFuel n)
    metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted := by
  unfold restoredExactMetaFuel
  rw [runFuel_add, restoredMetaStart_runFuel_five_eq_postPrologue h P]
  exact O.exactLoop h P n

theorem restoredMetaInterpProg_simulates_from_loop
    (O : RestoredSemanticLoopObligations)
    (h : Hexagram) (P : List YiInstr) (n : Nat) :
    let simResult := (YiState.init h P).runFuel n
    let metaResult := (restoredMetaStart h P).runFuel (restoredExactMetaFuel n)
    metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted :=
  restoredMetaInterpProg_simulates
    (RestoredSemanticComposeObligations.ofLoop O) h P n

theorem restored_universal_compose_frontier_summary :
    (RestoredSemanticLoopObligations → RestoredSemanticComposeObligations)
    ∧ (RestoredSemanticLoopObligations →
      ∀ h P n,
        let simResult := (YiState.init h P).runFuel n
        let metaResult := (restoredMetaStart h P).runFuel (restoredExactMetaFuel n)
        metaResult.history = encMetaHistory h simResult ∧
          metaResult.halted = simResult.halted)
    ∧ (∀ n, restoredExactMetaFuel n ≤ restoredMetaFuelBound n) := by
  exact
    ⟨ RestoredSemanticComposeObligations.ofLoop
    , restoredMetaInterpProg_simulates_from_loop
    , restoredMetaInterpProg_fuel_bound
    ⟩

end SSBX.Foundation.Wen.MetaInterp.UniversalRestorePlan
