/-
# QuantumRelativityBornMeasurementBridge -- S21 Born weights as measurement weights

Companion:
`义理/概率幅到测量权重 · Markov桥S21.md`

S21 closes a deliberately narrow measurement-facing Born-rule boundary:

1. a one-qubit state is read in the computational basis;
2. the two displayed measurement weights are `ampProb (ψ 0)` and
   `ampProb (ψ 1)`;
3. if the qubit is computational-basis normalized, these two weights are
   nonnegative and sum to `1`.

This is not a general Hilbert-space measurement theorem, not POVM/PVM
semantics, not decoherence, and not a solution to the measurement problem.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge

namespace SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
open SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 One-qubit computational-basis measurement weights -/

/-- The two displayed measurement weights for a computational-basis qubit readout. -/
structure ComputationalBasisMeasurementWeights where
  weight0 : ℝ
  weight1 : ℝ

/-- The measurement weights obtained from the two computational-basis amplitudes. -/
def computationalBasisMeasurementWeights
    (ψ : Qubit) : ComputationalBasisMeasurementWeights where
  weight0 := bornProb0 ψ
  weight1 := bornProb1 ψ

/-- A binary measurement-weight interface is normalized when both weights are
nonnegative and their finite sum is `1`. -/
def MeasurementWeightsNormalized
    (w : ComputationalBasisMeasurementWeights) : Prop :=
  0 ≤ w.weight0 ∧ 0 ≤ w.weight1 ∧ w.weight0 + w.weight1 = 1

/-- The `|0⟩` measurement weight is exactly the Born weight of amplitude `ψ 0`. -/
theorem computational_basis_weight0_eq_ampProb (ψ : Qubit) :
    (computationalBasisMeasurementWeights ψ).weight0 = ampProb (ψ 0) :=
  rfl

/-- The `|1⟩` measurement weight is exactly the Born weight of amplitude `ψ 1`. -/
theorem computational_basis_weight1_eq_ampProb (ψ : Qubit) :
    (computationalBasisMeasurementWeights ψ).weight1 = ampProb (ψ 1) :=
  rfl

/-! ## § 2 Born rule as normalized measurement weights -/

/--
One-qubit computational-basis Born rule, read as measurement weights:
for a computational-basis normalized qubit, both displayed weights are
nonnegative and their sum is `1`.
-/
theorem born_rule_gives_normalized_measurement_weights
    (ψ : Qubit) (hψ : computationalBasisNormalized ψ) :
    0 ≤ bornProb0 ψ ∧ 0 ≤ bornProb1 ψ
      ∧ bornProb0 ψ + bornProb1 ψ = 1 :=
  computational_basis_born_rule ψ hψ

/-- The same theorem packaged through the explicit measurement-weight record. -/
theorem computational_basis_measurement_weights_normalized
    (ψ : Qubit) (hψ : computationalBasisNormalized ψ) :
    MeasurementWeightsNormalized (computationalBasisMeasurementWeights ψ) :=
  born_rule_gives_normalized_measurement_weights ψ hψ

/-- Closed S21 one-qubit computational-basis Born measurement boundary. -/
def ComputationalBasisBornMeasurementClosed : Prop :=
  ∀ ψ : Qubit, computationalBasisNormalized ψ ->
    0 ≤ bornProb0 ψ ∧ 0 ≤ bornProb1 ψ
      ∧ bornProb0 ψ + bornProb1 ψ = 1

theorem computational_basis_born_measurement_closed :
    ComputationalBasisBornMeasurementClosed :=
  born_rule_gives_normalized_measurement_weights

/-! ## § 3 Remaining physical ledger -/

inductive PendingBeyondS21 where
  | generalHilbertSpaceMeasurement
  | projectionValuedMeasures
  | povmSemantics
  | spectralOperatorSemantics
  | decoherenceDynamics
  | measurementProblem
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS21 (_b : PendingBeyondS21) : Bool :=
  false

theorem pending_boundary_not_closed_by_s21
    (b : PendingBeyondS21) :
    ClosedByStepwiseS21 b = false := by
  cases b <;> rfl

/-! ## § 4 Public summary -/

theorem born_measurement_bridge_summary :
    ComputationalBasisBornMeasurementClosed
    ∧ MarkovAmplitudeBornRuleDerivationClosed
    ∧ NontrivialQuantumChannelLawClosed
    ∧ (∀ b : PendingBeyondS21, ClosedByStepwiseS21 b = false)
    ∧ WenConstructiveCoverage := by
  rcases born_rule_derivation_bridge_summary with
    ⟨_hBornDistribution, _hSumOverMiddleBorn, hBornDerivation,
      _hConcreteBorn, _hPendingBorn, _hCoverageBorn⟩
  rcases nontrivial_quantum_channel_law_bridge_summary with
    ⟨hNontrivialChannel, _hBornDistributionS20, _hSumOverMiddleBornS20,
      _hPathWeight, _hPendingS20, hCoverage⟩
  exact
    ⟨ computational_basis_born_measurement_closed
    , hBornDerivation
    , hNontrivialChannel
    , pending_boundary_not_closed_by_s21
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
