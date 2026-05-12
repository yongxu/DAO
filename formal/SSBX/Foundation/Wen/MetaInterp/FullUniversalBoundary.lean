/-
# FullUniversalBoundary -- current `metaInterpProg` is not parameter-complete

`Universal.lean` already proves the public composition theorem from explicit
semantic obligations.  This sidecar makes the parameterized-program boundary
harder to misread: the current `metaInterpProg` is still Strategy-B, so it does
not cover arbitrary instruction parameters.

The positive route is the R4-squared carry frontier in
`R4CarrySemanticFrontier`; the old `metaInterpProg` remains a checked boundary,
not the final arbitrary-program interpreter.
-/
import SSBX.Foundation.Wen.MetaInterp.Universal
import SSBX.Foundation.Wen.MetaInterp.R4CarrySemanticFrontier

namespace SSBX.Foundation.Wen.MetaInterp.FullUniversalBoundary

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Universal
open SSBX.Foundation.Wen.MetaInterp.R4CarrySemanticFrontier

/-! ## Current `metaInterpProg` boundary -/

/-- A parameter-complete `metaInterpProg` would have to cover every source
program, not only the Strategy-B default-parameter subset. -/
def ParameterCompleteCurrentMetaInterp : Prop :=
  ∀ P : List YiInstr, StrategyBCompatibleProgram P

theorem current_metaInterpProg_not_parameter_complete :
    ¬ ParameterCompleteCurrentMetaInterp := by
  exact strategyB_not_full_program_space

theorem current_metaInterpProg_has_parameter_counterexample :
    ∃ P : List YiInstr, ¬ StrategyBCompatibleProgram P :=
  strategyB_has_noncompatible_program

/-- The existing `metaInterpProg` still has the unconditional zero-step/prologue
compose theorem, but it is not the full parameterized interpreter. -/
theorem current_metaInterpProg_full_universal_boundary :
    (∀ h P,
      let simResult := (YiState.init h P).runFuel 0
      let metaResult := (metaStart h P).runFuel (exactMetaFuel 0)
      metaResult.history = encMetaHistory h simResult ∧
        metaResult.halted = simResult.halted)
    ∧ ¬ ParameterCompleteCurrentMetaInterp
    ∧ (∃ P : List YiInstr, ¬ StrategyBCompatibleProgram P) := by
  exact
    ⟨ (fun h P => metaInterpProg_simulates_zero_steps h P)
    , current_metaInterpProg_not_parameter_complete
    , current_metaInterpProg_has_parameter_counterexample
    ⟩

/-- Readiness for promoting the current, old `metaInterpProg` to a full
arbitrary-program theorem.  It needs both the semantic loop evidence and
coverage of every parameterized source program. -/
structure CurrentMetaInterpFullUniversalReadiness : Prop where
  parameterComplete :
    ParameterCompleteCurrentMetaInterp
  compose :
    SemanticComposeObligations

theorem current_metaInterpProg_not_full_universal_ready :
    ¬ CurrentMetaInterpFullUniversalReadiness := by
  intro h
  exact current_metaInterpProg_not_parameter_complete h.parameterComplete

/-! ## Positive theorem shape -/

/-- The current public theorem remains valid once its semantic compose
obligations are supplied.  This is a theorem schema, not a claim that the
Strategy-B program is parameter-complete. -/
theorem current_metaInterpProg_simulates_from_compose_obligations
    (O : SemanticComposeObligations)
    (h : Hexagram) (P : List YiInstr) (n : Nat) :
    let simResult := (YiState.init h P).runFuel n
    let metaResult := (metaStart h P).runFuel (exactMetaFuel n)
    metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted :=
  metaInterpProg_simulates O h P n

/-- The R4-squared carry frontier is the positive path for arbitrary parameters:
when its concrete contracts are supplied, the restored public theorem follows. -/
theorem restored_r4_carry_frontier_is_positive_path :
    ∀ restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf carryBodyOffsetOf
      paramDecodeFuelOf bodyFuelOf carryBodyFuelOf,
      R4CarrySemanticFrontierContracts restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf
        carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf carryBodyFuelOf →
        ∀ h P n,
          let simResult := (YiState.init h P).runFuel n
          let metaResult :=
            (UniversalRestorePlan.restoredMetaStart h P).runFuel
              (UniversalRestorePlan.restoredExactMetaFuel n)
          metaResult.history = encMetaHistory h simResult ∧
            metaResult.halted = simResult.halted := by
  intro restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf carryBodyOffsetOf
    paramDecodeFuelOf bodyFuelOf carryBodyFuelOf F h P n
  exact
    (r4_carry_semantic_frontier_summary
      restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf carryBodyOffsetOf
      paramDecodeFuelOf bodyFuelOf carryBodyFuelOf F).2.2 h P n

/-- Readiness for the restored R4-carry path.  This is intentionally a direct
alias of the semantic frontier contracts: no extra doctrine or R5+ word choices
are introduced at the public theorem surface. -/
def RestoredR4CarryFullUniversalReadiness
    (restoreOffsetOf : R4CarryAssemblyPlan.RestoreOffsetOf)
    (paramDecodeOffsetOf : R4CarryParamDecodeObligations.ParamDecodeOffsetOf)
    (bodyOffsetOf : R4CarryAssemblyPlan.BodyOffsetOf)
    (carryBodyOffsetOf : R4CarryBlockPrePost.CarryBodyOffsetOf)
    (paramDecodeFuelOf : R4CarryParamDecodeObligations.ParamDecodeFuelOf)
    (bodyFuelOf : R4CarryBlockContracts.BodyFuelOf)
    (carryBodyFuelOf : R4CarryBlockPrePost.CarryBodyFuelOf) : Prop :=
  R4CarrySemanticFrontierContracts restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf
    carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf carryBodyFuelOf

theorem restored_r4_carry_full_arbitrary_program_compose
    (restoreOffsetOf : R4CarryAssemblyPlan.RestoreOffsetOf)
    (paramDecodeOffsetOf : R4CarryParamDecodeObligations.ParamDecodeOffsetOf)
    (bodyOffsetOf : R4CarryAssemblyPlan.BodyOffsetOf)
    (carryBodyOffsetOf : R4CarryBlockPrePost.CarryBodyOffsetOf)
    (paramDecodeFuelOf : R4CarryParamDecodeObligations.ParamDecodeFuelOf)
    (bodyFuelOf : R4CarryBlockContracts.BodyFuelOf)
    (carryBodyFuelOf : R4CarryBlockPrePost.CarryBodyFuelOf)
    (F :
      RestoredR4CarryFullUniversalReadiness restoreOffsetOf paramDecodeOffsetOf
        bodyOffsetOf carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf
        carryBodyFuelOf)
    (h : Hexagram) (P : List YiInstr) (n : Nat) :
    let simResult := (YiState.init h P).runFuel n
    let metaResult :=
      (UniversalRestorePlan.restoredMetaStart h P).runFuel
        (UniversalRestorePlan.restoredExactMetaFuel n)
    metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted :=
  restored_r4_carry_frontier_is_positive_path
    restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf carryBodyOffsetOf
    paramDecodeFuelOf bodyFuelOf carryBodyFuelOf F h P n

theorem full_arbitrary_program_parameterized_status_summary :
    ¬ CurrentMetaInterpFullUniversalReadiness
    ∧ (∀ restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf carryBodyOffsetOf
        paramDecodeFuelOf bodyFuelOf carryBodyFuelOf,
        RestoredR4CarryFullUniversalReadiness restoreOffsetOf paramDecodeOffsetOf
          bodyOffsetOf carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf
          carryBodyFuelOf →
        ∀ h P n,
          let simResult := (YiState.init h P).runFuel n
          let metaResult :=
            (UniversalRestorePlan.restoredMetaStart h P).runFuel
              (UniversalRestorePlan.restoredExactMetaFuel n)
          metaResult.history = encMetaHistory h simResult ∧
            metaResult.halted = simResult.halted) := by
  exact
    ⟨ current_metaInterpProg_not_full_universal_ready
    , restored_r4_carry_full_arbitrary_program_compose
    ⟩

end SSBX.Foundation.Wen.MetaInterp.FullUniversalBoundary
