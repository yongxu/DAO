/-
# QuantumRelativityNormalizedMassBridge -- normalized finite mass sum

Companion:
`义理/归一化质量求和候选 · Markov桥S10.md`

S10 advances S9 from row-total normalization to the displayed finite
probability mass law:

1. it sums `normalizedMass` over the explicit finite row support;
2. it proves this sum is the S9 normalized-row-total candidate;
3. it closes the concrete and `96000` grid non-terminal row mass sums as `1`;
4. it keeps Born-rule derivation, quantum channel laws, metric recovery, and
   empirical closure as later boundaries.

This is a rational finite probability law for already supplied Markov row
weights.  It is not a Born-rule derivation, not unitary/CPTP dynamics, not a
path integral, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge.Core

namespace SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
open SSBX.Text.OperatorCellMap

/-! ## § 1 Normalized mass over finite row support -/

/--
Finite sum of rational entry masses over an explicitly displayed row support.
-/
def normalizedMassSum {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P)
    (rowSupport : P.State -> List P.State)
    (a : P.State) : Rat :=
  ((rowSupport a).map fun b => normalizedMass K a b).sum

/--
Summing per-entry normalized masses over a finite row support is the same
candidate as first summing the natural weights and then dividing by the row
denominator.
-/
theorem normalizedMassSum_eq_normalizedRowTotalCandidate
    {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P)
    (rowSupport : P.State -> List P.State)
    (a : P.State) :
    normalizedMassSum K rowSupport a =
      normalizedRowTotalCandidate K rowSupport a := by
  unfold normalizedMassSum normalizedRowTotalCandidate rowWeightSum
    normalizedMass
  induction rowSupport a with
  | nil =>
      simp
  | cons _ _ ih =>
      simp [ih, add_div]

/--
If the displayed finite row support sums to the row denominator, then the sum
of normalized masses over that support is `1` on every normalizable row.
-/
theorem normalizedMass_sum_one
    {P : FiniteProcess}
    {K : FiniteProbabilityKernelSkeleton P}
    (R : FiniteRowSupportNormalization K)
    (a : P.State)
    (h : RowNormalizable K a) :
    normalizedMassSum K R.rowSupport a = 1 := by
  rw [normalizedMassSum_eq_normalizedRowTotalCandidate]
  exact normalized_row_total_candidate_eq_one_of_complete R a h

/-! ## § 2 Concrete and grid instances -/

theorem concrete_normalizedMass_sum_one
    (a : ConcreteState) :
    ¬ concreteProcess.terminal a ->
      normalizedMassSum concreteFiniteProbabilityKernel
        concreteRowSupport a = 1 := by
  intro h
  rw [normalizedMassSum_eq_normalizedRowTotalCandidate]
  exact concrete_normalized_row_total_candidate_eq_one a h

theorem operatorCellGrid_normalizedMass_sum_one
    (a : OperatorCellGridState) :
    ¬ operatorCellGridProcess.terminal a ->
      normalizedMassSum operatorCellGridFiniteProbabilityKernel
        operatorCellGridRowSupport a = 1 := by
  intro h
  rw [normalizedMassSum_eq_normalizedRowTotalCandidate]
  exact operatorCellGrid_normalized_row_total_candidate_eq_one a h

/-! ## § 3 Pending boundary after S10 -/

/--
Larger physical boundaries still not closed by finite normalized mass sums.

S10 closes the classical rational row-probability law for the concrete and
operator-cell grid kernels.  Amplitude-derived Born weights and channel
composition remain separate next steps.
-/
inductive PendingBeyondS10 where
  | bornRuleDerivation
  | amplitudeBornNormalizedSupport
  | continuousActionLaw
  | generalPathIntegral
  | measurablePredictionData
  | unitaryCPTPChannelLaw
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

/-- S10 does not close the larger physical boundaries. -/
def ClosedByStepwiseS10 (_b : PendingBeyondS10) : Bool :=
  false

theorem pending_boundary_not_closed_by_s10
    (b : PendingBeyondS10) :
    ClosedByStepwiseS10 b = false := by
  cases b <;> rfl

/-- Closed finite facts carried by S10 normalized mass sums. -/
def FiniteNormalizedMassBoundaryClosed : Prop :=
  (∀ a : ConcreteState,
      ¬ concreteProcess.terminal a ->
        normalizedMassSum concreteFiniteProbabilityKernel
          concreteRowSupport a = 1)
    ∧ (∀ a : OperatorCellGridState,
        ¬ operatorCellGridProcess.terminal a ->
          normalizedMassSum operatorCellGridFiniteProbabilityKernel
            operatorCellGridRowSupport a = 1)

theorem finite_normalized_mass_boundary_closed :
    FiniteNormalizedMassBoundaryClosed := by
  exact
    ⟨ concrete_normalizedMass_sum_one
    , operatorCellGrid_normalizedMass_sum_one
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
