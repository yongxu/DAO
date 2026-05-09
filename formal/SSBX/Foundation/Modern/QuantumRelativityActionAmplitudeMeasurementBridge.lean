/-
# QuantumRelativityActionAmplitudeMeasurementBridge -- S22 action to measurement chain

Companion:
`义理/作用相位到测量权重链 · Markov桥S22.md`

S22 closes a deliberately finite chain:

1. a displayed action branch selects a finite action index;
2. the action index induces a phase amplitude;
3. that amplitude is inserted into a one-qubit computational-basis state;
4. S21 then gives normalized measurement weights.

This is still a finite typed skeleton.  It is not Hamiltonian dynamics, not
unitary time evolution, not a path integral, not general Hilbert measurement,
not POVM/PVM semantics, and not empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
import SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge

namespace SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
open SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
open SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite action branches as qubit amplitudes -/

/-- The two displayed finite action branches used by the current chain. -/
inductive ActionMeasurementBranch where
  | upper
  | lower
  deriving DecidableEq, Repr

namespace ActionMeasurementBranch

/-- The finite action index carried by a displayed branch. -/
def actionIndex : ActionMeasurementBranch -> Nat
  | .upper => 0
  | .lower => 1

/-- The phase label induced by the branch action index. -/
def phase (b : ActionMeasurementBranch) : DiscretePhase :=
  actionIndexPhase (actionIndex b)

/-- The complex amplitude induced by the branch action index. -/
def amplitude (b : ActionMeasurementBranch) : ℂ :=
  actionIndexAmplitude (actionIndex b)

theorem upper_action_index :
    actionIndex .upper = 0 :=
  rfl

theorem lower_action_index :
    actionIndex .lower = 1 :=
  rfl

theorem upper_amplitude :
    amplitude .upper = 1 :=
  rfl

theorem lower_amplitude :
    amplitude .lower = -1 :=
  rfl

end ActionMeasurementBranch

/-- A one-qubit state with amplitude `-1` on the `|1⟩` branch. -/
def negKet1 : Qubit :=
  fun i => if i = 0 then 0 else -1

/--
The finite action branch inserted into a computational-basis qubit.

The upper branch carries amplitude `1` on `|0⟩`; the lower branch carries
amplitude `-1` on `|1⟩`.
-/
def actionBranchQubit : ActionMeasurementBranch -> Qubit
  | .upper => ket0
  | .lower => negKet1

theorem action_branch_upper_qubit_amplitude0 :
    actionBranchQubit .upper 0 =
      ActionMeasurementBranch.amplitude .upper := by
  rw [ActionMeasurementBranch.upper_amplitude]
  simp [actionBranchQubit, ket0]

theorem action_branch_lower_qubit_amplitude1 :
    actionBranchQubit .lower 1 =
      ActionMeasurementBranch.amplitude .lower := by
  rw [ActionMeasurementBranch.lower_amplitude]
  simp [actionBranchQubit, negKet1]

theorem negKet1_computational_basis_normalized :
    computationalBasisNormalized negKet1 := by
  norm_num [computationalBasisNormalized, bornTotal, bornProb0, bornProb1,
    negKet1, ampProb]

theorem action_branch_qubit_normalized
    (b : ActionMeasurementBranch) :
    computationalBasisNormalized (actionBranchQubit b) := by
  cases b with
  | upper =>
      exact born_ket0.2.2
  | lower =>
      exact negKet1_computational_basis_normalized

/-! ## § 2 Born measurement weights from action-induced amplitudes -/

theorem action_branch_born_measurement_weights
    (b : ActionMeasurementBranch) :
    MeasurementWeightsNormalized
      (computationalBasisMeasurementWeights (actionBranchQubit b)) :=
  computational_basis_measurement_weights_normalized
    (actionBranchQubit b)
    (action_branch_qubit_normalized b)

/-- The two measurement events in the displayed computational-basis readout. -/
inductive ActionMeasurementOutcome where
  | zero
  | one
  deriving DecidableEq, Repr

/-- Measurement-event weights induced by a finite action branch. -/
def actionBranchOutcomeWeight
    (b : ActionMeasurementBranch) : ActionMeasurementOutcome -> ℝ
  | .zero => bornProb0 (actionBranchQubit b)
  | .one => bornProb1 (actionBranchQubit b)

theorem action_branch_outcome_weights_normalized
    (b : ActionMeasurementBranch) :
    0 ≤ actionBranchOutcomeWeight b .zero
      ∧ 0 ≤ actionBranchOutcomeWeight b .one
      ∧ actionBranchOutcomeWeight b .zero
        + actionBranchOutcomeWeight b .one = 1 := by
  simpa [actionBranchOutcomeWeight, computationalBasisMeasurementWeights,
    MeasurementWeightsNormalized]
    using action_branch_born_measurement_weights b

/-! ## § 3 Connection back to the two-route action-phase law -/

theorem two_route_action_indices_match_measurement_branches :
    twoRouteQuotientActionPhaseLaw.actionIndex
        (twoStepPathQuotientClass twoRouteUpperPath) =
          ActionMeasurementBranch.actionIndex .upper
      ∧ twoRouteQuotientActionPhaseLaw.actionIndex
        (twoStepPathQuotientClass twoRouteLowerPath) =
          ActionMeasurementBranch.actionIndex .lower := by
  exact
    ⟨ by
        simpa [ActionMeasurementBranch.actionIndex]
          using two_route_upper_quotient_action_index
    , by
        simpa [ActionMeasurementBranch.actionIndex]
          using two_route_lower_quotient_action_index
    ⟩

/-- Closed finite action-amplitude facts used by S22. -/
def ActionDrivenAmplitudeDynamicsClosed : Prop :=
  ActionMeasurementBranch.amplitude .upper = 1
    ∧ ActionMeasurementBranch.amplitude .lower = -1
    ∧ actionBranchQubit .upper 0 =
        ActionMeasurementBranch.amplitude .upper
    ∧ actionBranchQubit .lower 1 =
        ActionMeasurementBranch.amplitude .lower
    ∧ (∀ b : ActionMeasurementBranch,
        computationalBasisNormalized (actionBranchQubit b))

theorem action_driven_amplitude_dynamics_closed :
    ActionDrivenAmplitudeDynamicsClosed := by
  exact
    ⟨ ActionMeasurementBranch.upper_amplitude
    , ActionMeasurementBranch.lower_amplitude
    , action_branch_upper_qubit_amplitude0
    , action_branch_lower_qubit_amplitude1
    , action_branch_qubit_normalized
    ⟩

/-- Closed finite action-to-measurement chain used by S22. -/
def ActionToBornMeasurementChainClosed : Prop :=
  ActionDrivenAmplitudeDynamicsClosed
    ∧ (∀ b : ActionMeasurementBranch,
        MeasurementWeightsNormalized
          (computationalBasisMeasurementWeights (actionBranchQubit b)))
    ∧ (∀ b : ActionMeasurementBranch,
        0 ≤ actionBranchOutcomeWeight b .zero
          ∧ 0 ≤ actionBranchOutcomeWeight b .one
          ∧ actionBranchOutcomeWeight b .zero
            + actionBranchOutcomeWeight b .one = 1)
    ∧ twoRouteQuotientActionPhaseLaw.actionIndex
        (twoStepPathQuotientClass twoRouteUpperPath) =
          ActionMeasurementBranch.actionIndex .upper
    ∧ twoRouteQuotientActionPhaseLaw.actionIndex
        (twoStepPathQuotientClass twoRouteLowerPath) =
          ActionMeasurementBranch.actionIndex .lower

theorem action_to_born_measurement_chain_closed :
    ActionToBornMeasurementChainClosed := by
  rcases two_route_action_indices_match_measurement_branches with
    ⟨hUpper, hLower⟩
  exact
    ⟨ action_driven_amplitude_dynamics_closed
    , action_branch_born_measurement_weights
    , action_branch_outcome_weights_normalized
    , hUpper
    , hLower
    ⟩

/-! ## § 4 Remaining physical ledger -/

inductive PendingBeyondS22 where
  | continuousActionFunctional
  | hamiltonianDynamics
  | unitaryTimeEvolution
  | generalPathIntegral
  | generalHilbertMeasurement
  | projectionValuedMeasures
  | povmSemantics
  | decoherenceDynamics
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS22 (_b : PendingBeyondS22) : Bool :=
  false

theorem pending_boundary_not_closed_by_s22
    (b : PendingBeyondS22) :
    ClosedByStepwiseS22 b = false := by
  cases b <;> rfl

/-! ## § 5 Public summary -/

theorem action_amplitude_measurement_bridge_summary :
    TwoRouteActionPhaseLawBoundaryComplete
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS22, ClosedByStepwiseS22 b = false)
    ∧ WenConstructiveCoverage := by
  rcases action_phase_law_bridge_summary with
    ⟨hActionPhase, _hKeyCancel, _hKeyBorn, _hLedger, hCoverageAction⟩
  rcases born_measurement_bridge_summary with
    ⟨hBornMeasurement, _hBornDerivation, _hChannel,
      _hPendingBorn, _hCoverageBorn⟩
  exact
    ⟨ hActionPhase
    , action_to_born_measurement_chain_closed
    , hBornMeasurement
    , pending_boundary_not_closed_by_s22
    , hCoverageAction
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
