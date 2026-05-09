/-
# QuantumRelativityFinitePhaseEvolutionBridge -- S23 finite phase evolution

Companion:
`义理/有限相位演化候选 · Markov桥S23.md`

S23 upgrades the S22 displayed amplitudes into a deliberately finite
phase-evolution candidate:

1. an action branch selects the period-two amplitude `1` or `-1`;
2. this amplitude acts as a global phase on a one-qubit state;
3. the displayed `ket0 / ket1` inputs evolve to the S22 action-induced qubits;
4. the computational-basis Born weights are preserved by the finite phase.

This is still a typed skeleton.  It is not a Hamiltonian generator theorem, not
a continuous unitary group, not a general Schrödinger dynamics result, not a
path integral, not general Hilbert measurement, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Branch-indexed finite phase evolution -/

/-- Branch-indexed global phase evolution on a one-qubit state. -/
def phaseEvolveBranch (b : ActionMeasurementBranch) (ψ : Qubit) : Qubit :=
  fun i => ActionMeasurementBranch.amplitude b * ψ i

/-- The upper branch has identity finite phase. -/
theorem phase_evolve_upper_is_identity
    (ψ : Qubit) :
    phaseEvolveBranch .upper ψ = ψ := by
  ext i
  simp [phaseEvolveBranch, ActionMeasurementBranch.upper_amplitude]

/-- The lower branch is a period-two finite phase. -/
theorem phase_evolve_lower_period_two
    (ψ : Qubit) :
    phaseEvolveBranch .lower (phaseEvolveBranch .lower ψ) = ψ := by
  ext i
  simp [phaseEvolveBranch, ActionMeasurementBranch.lower_amplitude]

/-! ## § 2 Generation of the S22 action-induced qubits -/

/-- The upper finite phase sends the displayed `|0⟩` input to the S22 upper qubit. -/
theorem phase_evolve_upper_ket0 :
    phaseEvolveBranch .upper ket0 = actionBranchQubit .upper := by
  ext i
  fin_cases i <;> simp [phaseEvolveBranch, actionBranchQubit, ket0,
    ActionMeasurementBranch.upper_amplitude]

/-- The lower finite phase sends the displayed `|1⟩` input to the S22 lower qubit. -/
theorem phase_evolve_lower_ket1 :
    phaseEvolveBranch .lower ket1 = actionBranchQubit .lower := by
  ext i
  fin_cases i <;> simp [phaseEvolveBranch, actionBranchQubit, ket1, negKet1,
    ActionMeasurementBranch.lower_amplitude]

/-- The S22 action-induced qubits are reached by the finite phase evolution. -/
theorem phase_evolution_reaches_action_branch_qubits :
    phaseEvolveBranch .upper ket0 = actionBranchQubit .upper
      ∧ phaseEvolveBranch .lower ket1 = actionBranchQubit .lower :=
  ⟨phase_evolve_upper_ket0, phase_evolve_lower_ket1⟩

/-! ## § 3 Born-weight preservation -/

/-- The finite phase preserves the displayed `|0⟩` Born weight. -/
theorem phase_evolve_branch_bornProb0_preserved
    (b : ActionMeasurementBranch) (ψ : Qubit) :
    bornProb0 (phaseEvolveBranch b ψ) = bornProb0 ψ := by
  cases b <;> simp [phaseEvolveBranch, bornProb0, ampProb,
    ActionMeasurementBranch.upper_amplitude,
    ActionMeasurementBranch.lower_amplitude]

/-- The finite phase preserves the displayed `|1⟩` Born weight. -/
theorem phase_evolve_branch_bornProb1_preserved
    (b : ActionMeasurementBranch) (ψ : Qubit) :
    bornProb1 (phaseEvolveBranch b ψ) = bornProb1 ψ := by
  cases b <;> simp [phaseEvolveBranch, bornProb1, ampProb,
    ActionMeasurementBranch.upper_amplitude,
    ActionMeasurementBranch.lower_amplitude]

/-- The finite phase preserves computational-basis normalization. -/
theorem phase_evolve_branch_normalization_preserved
    (b : ActionMeasurementBranch) (ψ : Qubit)
    (hψ : computationalBasisNormalized ψ) :
    computationalBasisNormalized (phaseEvolveBranch b ψ) := by
  simpa [computationalBasisNormalized, bornTotal,
    phase_evolve_branch_bornProb0_preserved,
    phase_evolve_branch_bornProb1_preserved] using hψ

/-- The finite phase preserves the S21 normalized measurement-weight interface. -/
theorem phase_evolve_branch_measurement_weights_normalized
    (b : ActionMeasurementBranch) (ψ : Qubit)
    (hψ : computationalBasisNormalized ψ) :
    MeasurementWeightsNormalized
      (computationalBasisMeasurementWeights (phaseEvolveBranch b ψ)) :=
  computational_basis_measurement_weights_normalized
    (phaseEvolveBranch b ψ)
    (phase_evolve_branch_normalization_preserved b ψ hψ)

/-! ## § 4 Closed finite phase-evolution boundary -/

/-- Closed finite phase-evolution facts used by S23. -/
def FinitePhaseEvolutionClosed : Prop :=
  (∀ ψ : Qubit, phaseEvolveBranch .upper ψ = ψ)
    ∧ (∀ ψ : Qubit,
        phaseEvolveBranch .lower (phaseEvolveBranch .lower ψ) = ψ)
    ∧ phaseEvolveBranch .upper ket0 = actionBranchQubit .upper
    ∧ phaseEvolveBranch .lower ket1 = actionBranchQubit .lower
    ∧ (∀ b : ActionMeasurementBranch, ∀ ψ : Qubit,
        bornProb0 (phaseEvolveBranch b ψ) = bornProb0 ψ)
    ∧ (∀ b : ActionMeasurementBranch, ∀ ψ : Qubit,
        bornProb1 (phaseEvolveBranch b ψ) = bornProb1 ψ)
    ∧ (∀ b : ActionMeasurementBranch, ∀ ψ : Qubit,
        computationalBasisNormalized ψ ->
          MeasurementWeightsNormalized
            (computationalBasisMeasurementWeights (phaseEvolveBranch b ψ)))

theorem finite_phase_evolution_closed :
    FinitePhaseEvolutionClosed := by
  exact
    ⟨ phase_evolve_upper_is_identity
    , phase_evolve_lower_period_two
    , phase_evolve_upper_ket0
    , phase_evolve_lower_ket1
    , phase_evolve_branch_bornProb0_preserved
    , phase_evolve_branch_bornProb1_preserved
    , phase_evolve_branch_measurement_weights_normalized
    ⟩

/-! ## § 5 Remaining physical ledger -/

inductive PendingBeyondS23 where
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

def ClosedByStepwiseS23 (_b : PendingBeyondS23) : Bool :=
  false

theorem pending_boundary_not_closed_by_s23
    (b : PendingBeyondS23) :
    ClosedByStepwiseS23 b = false := by
  cases b <;> rfl

/-! ## § 6 Public summary -/

theorem finite_phase_evolution_bridge_summary :
    FinitePhaseEvolutionClosed
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS23, ClosedByStepwiseS23 b = false)
    ∧ WenConstructiveCoverage := by
  rcases action_amplitude_measurement_bridge_summary with
    ⟨_hActionPhase, hActionToBorn, hBornMeasurement,
      _hPendingS22, hCoverage⟩
  exact
    ⟨ finite_phase_evolution_closed
    , hActionToBorn
    , hBornMeasurement
    , pending_boundary_not_closed_by_s23
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge
