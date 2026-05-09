/-
# QuantumRelativityFiniteProbabilityBridge — finite normalization interface

Companion:
`义理/有限概率核接口 · Markov桥S2.md`

This module upgrades the Markov/causal bridge by one conservative step:

1. a Markov kernel skeleton may carry a finite row denominator;
2. every non-terminal row has a nonzero denominator;
3. every one-step weight is bounded by that denominator;
4. terminal rows may stop, so this is not yet a Born rule or quantum channel.
-/
import SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
import SSBX.Foundation.Modern.OperatorCellGridMarkovBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge

open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Text.OperatorCellMap
open SSBX.Text.WenyanOperators

/-! ## § 1 Finite probability-kernel interface -/

/--
A finite probability-kernel interface over the existing Markov skeleton.

The `rowTotal` is a natural-number denominator for a finite row.  We only
require nonzero denominators on non-terminal rows; terminal rows are allowed to
stop rather than silently adding an absorbing physical transition.
-/
structure FiniteProbabilityKernelSkeleton (P : FiniteProcess)
    extends MarkovKernelSkeleton P where
  rowTotal : P.State → Nat
  rowTotal_positive_if_not_terminal :
    ∀ a : P.State, ¬ P.terminal a → rowTotal a ≠ 0
  weight_le_rowTotal :
    ∀ a b : P.State, weight a b ≤ rowTotal a

/-- A process has a finite probability projection when such a kernel exists. -/
def HasFiniteProbabilityProjection (P : FiniteProcess) : Prop :=
  Nonempty (FiniteProbabilityKernelSkeleton P)

/-- A row is normalizable when its denominator is nonzero. -/
def RowNormalizable {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P) (a : P.State) : Prop :=
  K.rowTotal a ≠ 0

/-- Non-terminal rows are normalizable by construction. -/
theorem nonterminal_row_normalizable {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P) (a : P.State) :
    ¬ P.terminal a → RowNormalizable K a :=
  K.rowTotal_positive_if_not_terminal a

/-- A rational-mass placeholder: numerator over a finite row denominator. -/
structure FiniteMassCandidate where
  numerator : Nat
  denominator : Nat
  deriving Repr, DecidableEq

/-- The finite mass candidate attached to one row/column entry. -/
def finiteMassCandidate {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P) (a b : P.State) :
    FiniteMassCandidate :=
  { numerator := K.weight a b
    denominator := K.rowTotal a }

/-- For non-terminal rows, the finite mass candidate has a positive denominator. -/
theorem finiteMassCandidate_denominator_positive_if_not_terminal
    {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P) (a b : P.State) :
    ¬ P.terminal a → (finiteMassCandidate K a b).denominator ≠ 0 := by
  intro h
  exact K.rowTotal_positive_if_not_terminal a h

/-! ## § 2 Concrete three-state instance -/

/-- Row denominators for the three-state concrete process. -/
def concreteRowTotal : ConcreteState → Nat
  | .prepared => 1
  | .evolved => 1
  | .measured => 0

/-- Non-terminal concrete rows have nonzero denominators. -/
theorem concreteRowTotal_positive_if_not_terminal
    (a : ConcreteState) :
    ¬ concreteProcess.terminal a → concreteRowTotal a ≠ 0 := by
  cases a <;> simp [concreteProcess, ConcreteState.terminal, concreteRowTotal]

/-- Concrete weights are bounded by their row denominators. -/
theorem concreteWeight_le_rowTotal
    (a b : ConcreteState) :
    ConcreteState.weight a b ≤ concreteRowTotal a := by
  cases a <;> cases b <;> decide

/-- Finite probability interface for the three-state concrete bridge. -/
def concreteFiniteProbabilityKernel :
    FiniteProbabilityKernelSkeleton concreteProcess where
  support := ConcreteState.step
  weight := ConcreteState.weight
  support_iff_positive := ConcreteState.step_iff_positive_weight
  support_implies_step := by
    intro a b h
    exact h
  rowTotal := concreteRowTotal
  rowTotal_positive_if_not_terminal :=
    concreteRowTotal_positive_if_not_terminal
  weight_le_rowTotal := concreteWeight_le_rowTotal

/-- The concrete prepared row is normalizable. -/
theorem concrete_prepared_row_normalizable :
    RowNormalizable concreteFiniteProbabilityKernel ConcreteState.prepared :=
  by simp [RowNormalizable, concreteFiniteProbabilityKernel, concreteRowTotal]

/-- The concrete evolved row is normalizable. -/
theorem concrete_evolved_row_normalizable :
    RowNormalizable concreteFiniteProbabilityKernel ConcreteState.evolved :=
  by simp [RowNormalizable, concreteFiniteProbabilityKernel, concreteRowTotal]

/-- The concrete terminal measured row is allowed to stop. -/
theorem concrete_measured_row_terminal :
    concreteProcess.terminal ConcreteState.measured :=
  True.intro

/-! ## § 3 Operator-cell grid instance -/

/-- Row denominators for the operator-cell grid successor kernel. -/
def operatorCellGridRowTotal (a : OperatorCellGridState) : Nat :=
  if a.val + 1 = allOperatorCells.length then 0 else 1

/-- Non-terminal grid rows have nonzero denominators. -/
theorem operatorCellGridRowTotal_positive_if_not_terminal
    (a : OperatorCellGridState) :
    ¬ operatorCellGridProcess.terminal a →
      operatorCellGridRowTotal a ≠ 0 := by
  intro h
  have hval : ¬ a.val + 1 = allOperatorCells.length := by
    intro ht
    exact h (by
      unfold operatorCellGridProcess operatorCellGridTerminal
      exact ht)
  simp [operatorCellGridRowTotal, hval]

/-- Grid successor weights are bounded by their row denominators. -/
theorem operatorCellGridWeight_le_rowTotal
    (a b : OperatorCellGridState) :
    operatorCellGridWeight a b ≤ operatorCellGridRowTotal a := by
  unfold operatorCellGridWeight operatorCellGridRowTotal
  by_cases hstep : b.val = a.val + 1
  · have hnotTerminal :
        ¬ operatorCellGridProcess.terminal a := by
      intro hterminal
      have hb_eq : b.val = allOperatorCells.length := by
        unfold operatorCellGridProcess operatorCellGridTerminal at hterminal
        exact hstep.trans hterminal
      exact Nat.lt_irrefl allOperatorCells.length (by
        simpa [hb_eq] using b.isLt)
    have hnotTerminalVal : ¬ a.val + 1 = allOperatorCells.length := by
      intro ht
      exact hnotTerminal (by
        unfold operatorCellGridProcess operatorCellGridTerminal
        exact ht)
    simp [hstep, hnotTerminalVal]
  · simp [hstep]

/-- Finite probability interface for the full operator-cell grid bridge. -/
def operatorCellGridFiniteProbabilityKernel :
    FiniteProbabilityKernelSkeleton operatorCellGridProcess where
  support := operatorCellGridStep
  weight := operatorCellGridWeight
  support_iff_positive := operatorCellGrid_step_iff_positive_weight
  support_implies_step := by
    intro a b h
    exact h
  rowTotal := operatorCellGridRowTotal
  rowTotal_positive_if_not_terminal :=
    operatorCellGridRowTotal_positive_if_not_terminal
  weight_le_rowTotal := operatorCellGridWeight_le_rowTotal

/-- Any non-terminal grid row is normalizable. -/
theorem operatorCellGrid_nonterminal_row_normalizable
    (a : OperatorCellGridState) :
    ¬ operatorCellGridProcess.terminal a →
      RowNormalizable operatorCellGridFiniteProbabilityKernel a :=
  nonterminal_row_normalizable operatorCellGridFiniteProbabilityKernel a

/-! ## § 4 Public summary -/

/-- Public summary for S2:
    both the toy concrete bridge and the full `371 × 192` operator-cell grid
    bridge have finite probability-kernel interfaces.  This only closes finite
    denominators and bounded weights; it does not prove Born rule, quantum
    channels, interference, metric recovery, or empirical closure. -/
theorem finite_probability_bridge_summary :
    HasFiniteProbabilityProjection concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ (∀ a : ConcreteState,
        ¬ concreteProcess.terminal a →
          RowNormalizable concreteFiniteProbabilityKernel a)
    ∧ (∀ a : OperatorCellGridState,
        ¬ operatorCellGridProcess.terminal a →
          RowNormalizable operatorCellGridFiniteProbabilityKernel a)
    ∧ (∀ a b : ConcreteState,
        concreteFiniteProbabilityKernel.weight a b
          ≤ concreteFiniteProbabilityKernel.rowTotal a)
    ∧ (∀ a b : OperatorCellGridState,
        operatorCellGridFiniteProbabilityKernel.weight a b
          ≤ operatorCellGridFiniteProbabilityKernel.rowTotal a)
    ∧ allOperatorIds.length = 371
    ∧ Cell192.all.length = 192
    ∧ allOperatorCells.length = 71232
    ∧ WenConstructiveCoverage := by
  exact
    ⟨ ⟨concreteFiniteProbabilityKernel⟩
    , ⟨operatorCellGridFiniteProbabilityKernel⟩
    , fun a h => nonterminal_row_normalizable
        concreteFiniteProbabilityKernel a h
    , fun a h => nonterminal_row_normalizable
        operatorCellGridFiniteProbabilityKernel a h
    , concreteFiniteProbabilityKernel.weight_le_rowTotal
    , operatorCellGridFiniteProbabilityKernel.weight_le_rowTotal
    , allOperatorIds_length
    , Cell192.all_length
    , allOperatorCells_length
    , wen_constructive_coverage_192_371
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
