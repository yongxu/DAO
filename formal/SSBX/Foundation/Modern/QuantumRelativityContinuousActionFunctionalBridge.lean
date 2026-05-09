/-
# QuantumRelativityContinuousActionFunctionalBridge -- S24 continuous action functional

Companion:
`义理/连续作用量泛函候选 · Markov桥S24.md`

S24 closes the deliberately narrow continuous-action-functional gap left by
the finite action layers:

1. define a displayed real-valued action functional on a real action
   coordinate;
2. prove this displayed functional is continuous;
3. sample it at the two branch times `0` and `1`;
4. prove those samples match the existing S22/S23 action indices and phase
   amplitudes;
5. reuse S23 to preserve the computational-basis Born weights.

This is a displayed continuous action-coordinate functional.  It is not a
general path-space action functional, not an Euler-Lagrange theorem, not a
Hamiltonian generator theorem, not a continuous unitary group, not a path
integral, and not empirical closure.
-/
import Mathlib.Tactic.NormNum
import SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge

namespace SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge

noncomputable section

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
open SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Displayed continuous action functional -/

/-- A real-valued action functional on the displayed real action coordinate. -/
structure ContinuousActionFunctionalCandidate where
  action : ℝ -> ℝ
  continuous_action : Continuous action

/-- The displayed action functional used by S24: `S(t) = t`. -/
def displayedContinuousActionFunctional :
    ContinuousActionFunctionalCandidate where
  action := fun t => t
  continuous_action := by
    simpa using continuous_id

theorem displayed_continuous_action_functional_continuous :
    Continuous displayedContinuousActionFunctional.action :=
  displayedContinuousActionFunctional.continuous_action

/-! ## § 2 Sampling the continuous action at branch times -/

/-- The displayed branch times used to sample the continuous action functional. -/
def branchActionTime : ActionMeasurementBranch -> ℝ
  | .upper => 0
  | .lower => 1

/-- The continuous action value sampled at a displayed branch time. -/
def branchContinuousActionValue (b : ActionMeasurementBranch) : ℝ :=
  displayedContinuousActionFunctional.action (branchActionTime b)

theorem upper_continuous_action_value :
    branchContinuousActionValue .upper = 0 :=
  rfl

theorem lower_continuous_action_value :
    branchContinuousActionValue .lower = 1 :=
  rfl

/-- The sampled continuous action values recover the existing finite indices. -/
theorem branch_continuous_action_value_matches_index
    (b : ActionMeasurementBranch) :
    branchContinuousActionValue b =
      (ActionMeasurementBranch.actionIndex b : ℝ) := by
  cases b <;> norm_num [branchContinuousActionValue, branchActionTime,
    displayedContinuousActionFunctional, ActionMeasurementBranch.actionIndex]

/-! ## § 3 From sampled action to phase amplitude -/

/-- The amplitude induced by sampling the continuous action at a branch. -/
def continuousActionSampledAmplitude
    (b : ActionMeasurementBranch) : ℂ :=
  actionIndexAmplitude (ActionMeasurementBranch.actionIndex b)

theorem continuous_action_sampled_amplitude_eq_branch_amplitude
    (b : ActionMeasurementBranch) :
    continuousActionSampledAmplitude b =
      ActionMeasurementBranch.amplitude b := by
  cases b <;> rfl

/-- Phase evolution induced by the sampled continuous action. -/
def continuousActionPhaseEvolveBranch
    (b : ActionMeasurementBranch) (ψ : Qubit) : Qubit :=
  fun i => continuousActionSampledAmplitude b * ψ i

theorem continuous_action_phase_evolve_eq_finite_phase_evolve
    (b : ActionMeasurementBranch) (ψ : Qubit) :
    continuousActionPhaseEvolveBranch b ψ =
      phaseEvolveBranch b ψ := by
  ext i
  simp [continuousActionPhaseEvolveBranch, phaseEvolveBranch,
    continuous_action_sampled_amplitude_eq_branch_amplitude]

theorem continuous_action_phase_evolution_reaches_action_branch_qubits :
    continuousActionPhaseEvolveBranch .upper ket0 =
        actionBranchQubit .upper
      ∧ continuousActionPhaseEvolveBranch .lower ket1 =
        actionBranchQubit .lower := by
  exact
    ⟨ by
        rw [continuous_action_phase_evolve_eq_finite_phase_evolve]
        exact phase_evolve_upper_ket0
    , by
        rw [continuous_action_phase_evolve_eq_finite_phase_evolve]
        exact phase_evolve_lower_ket1
    ⟩

/-! ## § 4 Born-weight preservation through the continuous-action sample -/

theorem continuous_action_phase_evolve_bornProb0_preserved
    (b : ActionMeasurementBranch) (ψ : Qubit) :
    bornProb0 (continuousActionPhaseEvolveBranch b ψ) =
      bornProb0 ψ := by
  rw [continuous_action_phase_evolve_eq_finite_phase_evolve]
  exact phase_evolve_branch_bornProb0_preserved b ψ

theorem continuous_action_phase_evolve_bornProb1_preserved
    (b : ActionMeasurementBranch) (ψ : Qubit) :
    bornProb1 (continuousActionPhaseEvolveBranch b ψ) =
      bornProb1 ψ := by
  rw [continuous_action_phase_evolve_eq_finite_phase_evolve]
  exact phase_evolve_branch_bornProb1_preserved b ψ

theorem continuous_action_phase_evolve_normalization_preserved
    (b : ActionMeasurementBranch) (ψ : Qubit)
    (hψ : computationalBasisNormalized ψ) :
    computationalBasisNormalized
      (continuousActionPhaseEvolveBranch b ψ) := by
  rw [continuous_action_phase_evolve_eq_finite_phase_evolve]
  exact phase_evolve_branch_normalization_preserved b ψ hψ

theorem continuous_action_phase_evolve_measurement_weights_normalized
    (b : ActionMeasurementBranch) (ψ : Qubit)
    (hψ : computationalBasisNormalized ψ) :
    MeasurementWeightsNormalized
      (computationalBasisMeasurementWeights
        (continuousActionPhaseEvolveBranch b ψ)) := by
  rw [continuous_action_phase_evolve_eq_finite_phase_evolve]
  exact phase_evolve_branch_measurement_weights_normalized b ψ hψ

/-! ## § 5 Closed S24 boundary -/

/-- Closed displayed continuous-action-functional facts used by S24. -/
def ContinuousActionFunctionalClosed : Prop :=
  Continuous displayedContinuousActionFunctional.action
    ∧ branchContinuousActionValue .upper = 0
    ∧ branchContinuousActionValue .lower = 1
    ∧ (∀ b : ActionMeasurementBranch,
        branchContinuousActionValue b =
          (ActionMeasurementBranch.actionIndex b : ℝ))
    ∧ (∀ b : ActionMeasurementBranch,
        continuousActionSampledAmplitude b =
          ActionMeasurementBranch.amplitude b)
    ∧ continuousActionPhaseEvolveBranch .upper ket0 =
        actionBranchQubit .upper
    ∧ continuousActionPhaseEvolveBranch .lower ket1 =
        actionBranchQubit .lower
    ∧ (∀ b : ActionMeasurementBranch, ∀ ψ : Qubit,
        bornProb0 (continuousActionPhaseEvolveBranch b ψ) =
          bornProb0 ψ)
    ∧ (∀ b : ActionMeasurementBranch, ∀ ψ : Qubit,
        bornProb1 (continuousActionPhaseEvolveBranch b ψ) =
          bornProb1 ψ)
    ∧ (∀ b : ActionMeasurementBranch, ∀ ψ : Qubit,
        computationalBasisNormalized ψ ->
          MeasurementWeightsNormalized
            (computationalBasisMeasurementWeights
              (continuousActionPhaseEvolveBranch b ψ)))

theorem continuous_action_functional_closed :
    ContinuousActionFunctionalClosed := by
  rcases continuous_action_phase_evolution_reaches_action_branch_qubits with
    ⟨hUpperReach, hLowerReach⟩
  exact
    ⟨ displayed_continuous_action_functional_continuous
    , upper_continuous_action_value
    , lower_continuous_action_value
    , branch_continuous_action_value_matches_index
    , continuous_action_sampled_amplitude_eq_branch_amplitude
    , hUpperReach
    , hLowerReach
    , continuous_action_phase_evolve_bornProb0_preserved
    , continuous_action_phase_evolve_bornProb1_preserved
    , continuous_action_phase_evolve_measurement_weights_normalized
    ⟩

/-! ## § 6 Remaining physical ledger -/

inductive PendingBeyondS24 where
  | generalPathSpaceActionFunctional
  | eulerLagrangeEquations
  | hamiltonianGenerator
  | continuousTimeUnitaryGroup
  | selfAdjointOperatorSemantics
  | generalSchrodingerDynamics
  | generalPathIntegral
  | generalHilbertMeasurement
  | projectionValuedMeasures
  | povmSemantics
  | decoherenceDynamics
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS24 (_b : PendingBeyondS24) : Bool :=
  false

theorem pending_boundary_not_closed_by_s24
    (b : PendingBeyondS24) :
    ClosedByStepwiseS24 b = false := by
  cases b <;> rfl

/-! ## § 7 Public summary -/

theorem continuous_action_functional_bridge_summary :
    ContinuousActionFunctionalClosed
    ∧ FinitePhaseEvolutionClosed
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS24, ClosedByStepwiseS24 b = false)
    ∧ WenConstructiveCoverage := by
  rcases finite_phase_evolution_bridge_summary with
    ⟨hFinitePhase, hActionToBorn, hBornMeasurement,
      _hPendingS23, hCoverage⟩
  exact
    ⟨ continuous_action_functional_closed
    , hFinitePhase
    , hActionToBorn
    , hBornMeasurement
    , pending_boundary_not_closed_by_s24
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge
