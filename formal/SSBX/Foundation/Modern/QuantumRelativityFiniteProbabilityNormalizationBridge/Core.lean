/-
# QuantumRelativityFiniteProbabilityNormalizationBridge -- finite row normalization

Companion:
`义理/有限概率归一化候选 · Markov桥S9.md`

This module advances S8 by closing the smallest finite sum-one probability
boundary available in the current bridge:

1. it adds explicit finite row-support lists for probability kernels;
2. it defines row-weight sums and a rational normalized-row-total candidate;
3. it proves that concrete and `96000` grid non-terminal rows normalize to `1`;
4. it moves the pending ledger beyond S9 by removing the finite sum-one row
   boundary while keeping the larger physical tasks explicit.

This is finite row normalization for the existing Markov kernels.  It is not a
Born-rule derivation, not a quantum measurement law, not unitary/CPTP dynamics,
not metric recovery, and not empirical closure.
-/
import Mathlib.Tactic.NormNum
import SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Text.OperatorCellMap

/-! ## § 1 Finite row-support normalization interface -/

/-- Sum of natural-number weights over an explicitly supplied finite row support. -/
def rowWeightSum {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P)
    (rowSupport : P.State -> List P.State)
    (a : P.State) : Nat :=
  ((rowSupport a).map fun b => K.weight a b).sum

/-- Rational mass candidate for one kernel entry. -/
def normalizedMass {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P)
    (a b : P.State) : Rat :=
  (K.weight a b : Rat) / (K.rowTotal a : Rat)

/--
The finite row-total candidate: sum the displayed row weights first, then divide
by the row denominator.  This is the sum-one boundary used in S9.
-/
def normalizedRowTotalCandidate {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P)
    (rowSupport : P.State -> List P.State)
    (a : P.State) : Rat :=
  (rowWeightSum K rowSupport a : Rat) / (K.rowTotal a : Rat)

/--
Explicit finite row support for a probability kernel.

The support list is sound and complete for positive weights, and its finite
weight sum is exactly the row denominator.
-/
structure FiniteRowSupportNormalization {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P) where
  rowSupport : P.State -> List P.State
  rowSupport_sound :
    ∀ a b : P.State, b ∈ rowSupport a -> K.weight a b ≠ 0
  rowSupport_complete :
    ∀ a b : P.State, K.weight a b ≠ 0 -> b ∈ rowSupport a
  row_weight_sum_eq_rowTotal :
    ∀ a : P.State, rowWeightSum K rowSupport a = K.rowTotal a

/-- Named projection for the row-weight sum law carried by a finite support. -/
theorem rowWeightSum_eq_rowTotal
    {P : FiniteProcess}
    {K : FiniteProbabilityKernelSkeleton P}
    (R : FiniteRowSupportNormalization K)
    (a : P.State) :
    rowWeightSum K R.rowSupport a = K.rowTotal a :=
  R.row_weight_sum_eq_rowTotal a

/-- A process has finite row-support normalization when one of its kernels does. -/
def HasFiniteRowSupportNormalization (P : FiniteProcess) : Prop :=
  ∃ K : FiniteProbabilityKernelSkeleton P,
    Nonempty (FiniteRowSupportNormalization K)

/--
If a displayed row support sums to the row denominator, then every normalizable
row has normalized-row-total candidate `1`.
-/
theorem normalized_row_total_candidate_eq_one_of_complete
    {P : FiniteProcess}
    {K : FiniteProbabilityKernelSkeleton P}
    (R : FiniteRowSupportNormalization K)
    (a : P.State)
    (h : RowNormalizable K a) :
    normalizedRowTotalCandidate K R.rowSupport a = 1 := by
  unfold normalizedRowTotalCandidate
  rw [R.row_weight_sum_eq_rowTotal a]
  exact div_self (by exact_mod_cast h)

/-! ## § 2 Concrete three-state row support -/

/-- Explicit row supports for the concrete three-state probability kernel. -/
def concreteRowSupport : ConcreteState -> List ConcreteState
  | .prepared => [.evolved]
  | .evolved => [.measured]
  | .measured => []

theorem concrete_row_support_sound
    (a b : ConcreteState) :
    b ∈ concreteRowSupport a ->
      concreteFiniteProbabilityKernel.weight a b ≠ 0 := by
  cases a <;> cases b <;>
    simp [concreteRowSupport, concreteFiniteProbabilityKernel,
      ConcreteState.weight]

theorem concrete_row_support_complete
    (a b : ConcreteState) :
    concreteFiniteProbabilityKernel.weight a b ≠ 0 ->
      b ∈ concreteRowSupport a := by
  cases a <;> cases b <;>
    simp [concreteRowSupport, concreteFiniteProbabilityKernel,
      ConcreteState.weight]

theorem concrete_row_weight_sum_eq_rowTotal
    (a : ConcreteState) :
    rowWeightSum concreteFiniteProbabilityKernel concreteRowSupport a =
      concreteFiniteProbabilityKernel.rowTotal a := by
  cases a <;> native_decide

/-- The concrete kernel has explicit finite row-support normalization. -/
def concreteFiniteRowSupportNormalization :
    FiniteRowSupportNormalization concreteFiniteProbabilityKernel where
  rowSupport := concreteRowSupport
  rowSupport_sound := concrete_row_support_sound
  rowSupport_complete := concrete_row_support_complete
  row_weight_sum_eq_rowTotal := concrete_row_weight_sum_eq_rowTotal

theorem concrete_normalized_row_total_candidate_eq_one
    (a : ConcreteState) :
    ¬ concreteProcess.terminal a ->
      normalizedRowTotalCandidate
        concreteFiniteProbabilityKernel concreteRowSupport a = 1 := by
  intro h
  exact normalized_row_total_candidate_eq_one_of_complete
    concreteFiniteRowSupportNormalization a
    (nonterminal_row_normalizable concreteFiniteProbabilityKernel a h)

/-! ## § 3 Operator-cell grid row support -/

/-- Explicit successor row support for the `96000` operator-cell grid kernel. -/
def operatorCellGridRowSupport
    (a : OperatorCellGridState) : List OperatorCellGridState :=
  if h : a.val + 1 = allOperatorCells.length then
    []
  else
    [⟨a.val + 1, by
      have hle : a.val + 1 ≤ allOperatorCells.length :=
        Nat.succ_le_of_lt a.isLt
      exact Nat.lt_of_le_of_ne hle h⟩]

theorem operatorCellGrid_row_support_sound
    (a b : OperatorCellGridState) :
    b ∈ operatorCellGridRowSupport a ->
      operatorCellGridFiniteProbabilityKernel.weight a b ≠ 0 := by
  intro hb
  by_cases h : a.val + 1 = allOperatorCells.length
  · simp [operatorCellGridRowSupport, h] at hb
  · simp [operatorCellGridRowSupport, h] at hb
    rcases hb with rfl
    simp [operatorCellGridFiniteProbabilityKernel, operatorCellGridWeight]

theorem operatorCellGrid_row_support_complete
    (a b : OperatorCellGridState) :
    operatorCellGridFiniteProbabilityKernel.weight a b ≠ 0 ->
      b ∈ operatorCellGridRowSupport a := by
  unfold operatorCellGridFiniteProbabilityKernel operatorCellGridWeight
  intro hWeight
  by_cases hStep : b.val = a.val + 1
  · unfold operatorCellGridRowSupport
    by_cases hTerminal : a.val + 1 = allOperatorCells.length
    · have hb : b.val = allOperatorCells.length := hStep.trans hTerminal
      exact False.elim (Nat.ne_of_lt b.isLt hb)
    · simp [hTerminal, hStep, Fin.ext_iff]
  · simp [hStep] at hWeight

theorem operatorCellGrid_row_weight_sum_eq_rowTotal
    (a : OperatorCellGridState) :
    rowWeightSum operatorCellGridFiniteProbabilityKernel
        operatorCellGridRowSupport a =
      operatorCellGridFiniteProbabilityKernel.rowTotal a := by
  by_cases h : a.val + 1 = allOperatorCells.length
  · simp [rowWeightSum, operatorCellGridRowSupport,
      operatorCellGridFiniteProbabilityKernel, operatorCellGridRowTotal,
      operatorCellGridWeight, h]
    change 0 = 0
    rfl
  · simp [rowWeightSum, operatorCellGridRowSupport,
      operatorCellGridFiniteProbabilityKernel, operatorCellGridRowTotal,
      operatorCellGridWeight, h]
    change (if a.val + 1 = a.val + 1 then 1 else 0) = 1
    simp

/-- The operator-cell grid kernel has explicit finite row-support normalization. -/
def operatorCellGridFiniteRowSupportNormalization :
    FiniteRowSupportNormalization operatorCellGridFiniteProbabilityKernel where
  rowSupport := operatorCellGridRowSupport
  rowSupport_sound := operatorCellGrid_row_support_sound
  rowSupport_complete := operatorCellGrid_row_support_complete
  row_weight_sum_eq_rowTotal := operatorCellGrid_row_weight_sum_eq_rowTotal

theorem operatorCellGrid_normalized_row_total_candidate_eq_one
    (a : OperatorCellGridState) :
    ¬ operatorCellGridProcess.terminal a ->
      normalizedRowTotalCandidate
        operatorCellGridFiniteProbabilityKernel
        operatorCellGridRowSupport a = 1 := by
  intro h
  have hRowTotal :
      operatorCellGridFiniteProbabilityKernel.rowTotal a = 1 := by
    have hNotTerminalVal : ¬ a.val + 1 = allOperatorCells.length := by
      intro hTerminalVal
      exact h (by
        unfold operatorCellGridProcess operatorCellGridTerminal
        exact hTerminalVal)
    simp [operatorCellGridFiniteProbabilityKernel, operatorCellGridRowTotal,
      hNotTerminalVal]
  unfold normalizedRowTotalCandidate
  rw [operatorCellGrid_row_weight_sum_eq_rowTotal, hRowTotal]
  norm_num

/-! ## § 4 Pending boundary after S9 -/

/--
Larger physical boundaries still not closed by finite row normalization.

The finite sum-one row boundary is no longer listed here; S9 closes it for the
concrete and grid Markov kernels above.  The Born-rule derivation and later
physical boundaries remain separate.
-/
inductive PendingBeyondS9 where
  | bornRuleDerivation
  | continuousActionLaw
  | generalPathIntegral
  | measurablePredictionData
  | unitaryCPTPChannelLaw
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

/-- S9 does not close the larger physical boundaries. -/
def ClosedByStepwiseS9 (_b : PendingBeyondS9) : Bool :=
  false

theorem pending_boundary_not_closed_by_s9
    (b : PendingBeyondS9) :
    ClosedByStepwiseS9 b = false := by
  cases b <;> rfl

/-- Closed finite facts carried by S9 row normalization. -/
def FiniteSumOneProbabilityBoundaryClosed : Prop :=
  HasFiniteRowSupportNormalization concreteProcess
    ∧ HasFiniteRowSupportNormalization operatorCellGridProcess
    ∧ (∀ a : ConcreteState,
        ¬ concreteProcess.terminal a ->
          normalizedRowTotalCandidate
            concreteFiniteProbabilityKernel concreteRowSupport a = 1)
    ∧ (∀ a : OperatorCellGridState,
        ¬ operatorCellGridProcess.terminal a ->
          normalizedRowTotalCandidate
            operatorCellGridFiniteProbabilityKernel
            operatorCellGridRowSupport a = 1)

theorem finite_sum_one_probability_boundary_closed :
    FiniteSumOneProbabilityBoundaryClosed := by
  exact
    ⟨ ⟨concreteFiniteProbabilityKernel,
        ⟨concreteFiniteRowSupportNormalization⟩⟩
    , ⟨operatorCellGridFiniteProbabilityKernel,
        ⟨operatorCellGridFiniteRowSupportNormalization⟩⟩
    , concrete_normalized_row_total_candidate_eq_one
    , operatorCellGrid_normalized_row_total_candidate_eq_one
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
