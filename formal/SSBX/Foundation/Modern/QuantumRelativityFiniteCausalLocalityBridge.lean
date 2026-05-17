/-
# QuantumRelativityFiniteCausalLocalityBridge -- S27 finite causal locality

Companion:
`义理/有限因果局部性候选 · Markov桥S27.md`

S27 advances the causal side of the bridge by adding a finite local-neighborhood
interface:

1. define a finite local-future list for each state;
2. prove local-future membership is equivalent to one-step transition support;
3. prove nonlocal targets cannot be one-step successors;
4. prove positive Markov kernel weight respects the local-future list;
5. instantiate the interface for the concrete three-state process and the
   `375 × 256` operator-cell grid process.

This is only a finite one-step causal locality candidate.  It is not a full
causal set, not a light-cone theorem, not Lorentzian locality, not metric
recovery, not relativistic field locality, and not empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge
import SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge

noncomputable section

open SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
open SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge
open SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Text.OperatorCellMap
open SSBX.Text.WenyanOperators

/-! ## § 1 Finite local-future interface -/

/-- A finite one-step local-future list for each state of a finite process. -/
structure FiniteCausalLocalFutureCandidate (P : FiniteProcess) where
  localFuture : P.State -> List P.State
  localFuture_sound :
    ∀ {a b : P.State}, b ∈ localFuture a -> P.step a b
  localFuture_complete :
    ∀ {a b : P.State}, P.step a b -> b ∈ localFuture a

theorem local_future_iff_step {P : FiniteProcess}
    (N : FiniteCausalLocalFutureCandidate P)
    (a b : P.State) :
    b ∈ N.localFuture a ↔ P.step a b :=
  ⟨N.localFuture_sound, N.localFuture_complete⟩

theorem step_depends_on_local_future {P : FiniteProcess}
    (N : FiniteCausalLocalFutureCandidate P)
    {a b : P.State} :
    P.step a b -> b ∈ N.localFuture a :=
  N.localFuture_complete

theorem local_future_implies_causal_before {P : FiniteProcess}
    (N : FiniteCausalLocalFutureCandidate P)
    {a b : P.State} :
    b ∈ N.localFuture a -> causalBefore (P := P) ⟨a⟩ ⟨b⟩ := by
  intro hlocal
  exact step_implies_causal_before (N.localFuture_sound hlocal)

theorem nonlocal_not_one_step {P : FiniteProcess}
    (N : FiniteCausalLocalFutureCandidate P)
    {a b : P.State} :
    b ∉ N.localFuture a -> ¬ P.step a b := by
  intro hnot hstep
  exact hnot (N.localFuture_complete hstep)

/-- A Markov kernel respects finite causal locality when every positive
one-step weight targets the displayed local future. -/
def KernelRespectsLocalFuture {P : FiniteProcess}
    (K : MarkovKernelSkeleton P)
    (N : FiniteCausalLocalFutureCandidate P) : Prop :=
  ∀ {a b : P.State}, K.weight a b ≠ 0 -> b ∈ N.localFuture a

theorem kernel_positive_weight_implies_local_future {P : FiniteProcess}
    (K : MarkovKernelSkeleton P)
    (N : FiniteCausalLocalFutureCandidate P) :
    KernelRespectsLocalFuture K N := by
  intro a b hweight
  exact N.localFuture_complete (positive_weight_implies_step K hweight)

/-! ## § 2 Concrete local future -/

def concreteLocalFuture : ConcreteState -> List ConcreteState
  | .prepared => [.evolved]
  | .evolved => [.measured]
  | .measured => []

theorem concrete_local_future_sound
    {a b : ConcreteState} :
    b ∈ concreteLocalFuture a -> concreteProcess.step a b := by
  intro h
  cases a <;> cases b <;>
    simp [concreteLocalFuture, concreteProcess, ConcreteState.step] at h ⊢

theorem concrete_local_future_complete
    {a b : ConcreteState} :
    concreteProcess.step a b -> b ∈ concreteLocalFuture a := by
  intro h
  cases a <;> cases b <;>
    simp [concreteLocalFuture, concreteProcess, ConcreteState.step] at h ⊢

def concreteCausalLocalFuture :
    FiniteCausalLocalFutureCandidate concreteProcess where
  localFuture := concreteLocalFuture
  localFuture_sound := concrete_local_future_sound
  localFuture_complete := concrete_local_future_complete

theorem concrete_local_future_iff_step
    (a b : ConcreteState) :
    b ∈ concreteCausalLocalFuture.localFuture a ↔
      concreteProcess.step a b :=
  local_future_iff_step concreteCausalLocalFuture a b

theorem concrete_kernel_respects_local_future :
    KernelRespectsLocalFuture concreteKernel concreteCausalLocalFuture :=
  kernel_positive_weight_implies_local_future
    concreteKernel concreteCausalLocalFuture

theorem concrete_prepared_local_future :
    concreteCausalLocalFuture.localFuture ConcreteState.prepared =
      [ConcreteState.evolved] :=
  rfl

theorem concrete_evolved_local_future :
    concreteCausalLocalFuture.localFuture ConcreteState.evolved =
      [ConcreteState.measured] :=
  rfl

theorem concrete_measured_local_future :
    concreteCausalLocalFuture.localFuture ConcreteState.measured = [] :=
  rfl

theorem concrete_nonlocal_measured_not_step_to_prepared :
    ¬ concreteProcess.step ConcreteState.measured ConcreteState.prepared := by
  have hnot :
      ConcreteState.prepared ∉
        concreteCausalLocalFuture.localFuture ConcreteState.measured := by
    change ConcreteState.prepared ∉ ([] : List ConcreteState)
    simp
  exact nonlocal_not_one_step concreteCausalLocalFuture hnot

/-! ## § 3 Operator-cell grid local future -/

def operatorCellGridLocalFuture
    (a : OperatorCellGridState) : List OperatorCellGridState :=
  if h : a.val + 1 < allOperatorCells.length then
    [⟨a.val + 1, h⟩]
  else
    []

theorem operatorCellGrid_local_future_sound
    {a b : OperatorCellGridState} :
    b ∈ operatorCellGridLocalFuture a ->
      operatorCellGridProcess.step a b := by
  intro hmem
  unfold operatorCellGridLocalFuture at hmem
  unfold operatorCellGridProcess operatorCellGridStep
  by_cases h : a.val + 1 < allOperatorCells.length
  · simp [h] at hmem
    rw [hmem]
  · simp [h] at hmem

theorem operatorCellGrid_local_future_complete
    {a b : OperatorCellGridState} :
    operatorCellGridProcess.step a b ->
      b ∈ operatorCellGridLocalFuture a := by
  intro hstep
  unfold operatorCellGridProcess operatorCellGridStep at hstep
  have hnext : a.val + 1 < allOperatorCells.length := by
    rw [← hstep]
    exact b.isLt
  have hb : b = ⟨a.val + 1, hnext⟩ := by
    exact Fin.ext hstep
  simp [operatorCellGridLocalFuture, hnext, hb]

def operatorCellGridCausalLocalFuture :
    FiniteCausalLocalFutureCandidate operatorCellGridProcess where
  localFuture := operatorCellGridLocalFuture
  localFuture_sound := operatorCellGrid_local_future_sound
  localFuture_complete := operatorCellGrid_local_future_complete

theorem operatorCellGrid_local_future_iff_step
    (a b : OperatorCellGridState) :
    b ∈ operatorCellGridCausalLocalFuture.localFuture a ↔
      operatorCellGridProcess.step a b :=
  local_future_iff_step operatorCellGridCausalLocalFuture a b

theorem operatorCellGrid_kernel_respects_local_future :
    KernelRespectsLocalFuture
      operatorCellGridKernel operatorCellGridCausalLocalFuture :=
  kernel_positive_weight_implies_local_future
    operatorCellGridKernel operatorCellGridCausalLocalFuture

theorem operatorCellGrid_initial_local_future_length :
    (operatorCellGridCausalLocalFuture.localFuture
        operatorCellGridInitial).length = 1 := by
  unfold operatorCellGridCausalLocalFuture operatorCellGridLocalFuture
    operatorCellGridInitial
  simp [allOperatorCells_length]
  rfl

/-! ## § 4 Closed S27 boundary -/

def FiniteCausalLocalityClosed : Prop :=
  (∀ {P : FiniteProcess}
      (N : FiniteCausalLocalFutureCandidate P)
      (a b : P.State), b ∈ N.localFuture a ↔ P.step a b)
    ∧ (∀ {P : FiniteProcess}
        (N : FiniteCausalLocalFutureCandidate P)
        {a b : P.State},
        b ∈ N.localFuture a -> causalBefore (P := P) ⟨a⟩ ⟨b⟩)
    ∧ (∀ {P : FiniteProcess}
        (N : FiniteCausalLocalFutureCandidate P)
        {a b : P.State},
        b ∉ N.localFuture a -> ¬ P.step a b)
    ∧ KernelRespectsLocalFuture concreteKernel concreteCausalLocalFuture
    ∧ KernelRespectsLocalFuture
      operatorCellGridKernel operatorCellGridCausalLocalFuture
    ∧ concreteCausalLocalFuture.localFuture ConcreteState.prepared =
      [ConcreteState.evolved]
    ∧ concreteCausalLocalFuture.localFuture ConcreteState.evolved =
      [ConcreteState.measured]
    ∧ concreteCausalLocalFuture.localFuture ConcreteState.measured = []
    ∧ (operatorCellGridCausalLocalFuture.localFuture
        operatorCellGridInitial).length = 1

theorem finite_causal_locality_closed :
    FiniteCausalLocalityClosed := by
  exact
    ⟨ local_future_iff_step
    , local_future_implies_causal_before
    , nonlocal_not_one_step
    , concrete_kernel_respects_local_future
    , operatorCellGrid_kernel_respects_local_future
    , concrete_prepared_local_future
    , concrete_evolved_local_future
    , concrete_measured_local_future
    , operatorCellGrid_initial_local_future_length
    ⟩

/-! ## § 5 Remaining physical ledger -/

inductive PendingBeyondS27 where
  | fullCausalSetAxioms
  | localFinitenessCausalSet
  | lightConeGeometry
  | lorentzianManifoldLocality
  | metricRecovery
  | relativisticFieldLocality
  | smoothOrInfinitePathSpaceActionFunctional
  | continuousVariationSpace
  | stationaryActionPrinciple
  | eulerLagrangeEquations
  | hamiltonianGenerator
  | continuousTimeUnitaryGroup
  | generalPathIntegral
  | generalHilbertMeasurement
  | decoherenceDynamics
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS27 (_b : PendingBeyondS27) : Bool :=
  false

theorem pending_boundary_not_closed_by_s27
    (b : PendingBeyondS27) :
    ClosedByStepwiseS27 b = false := by
  cases b <;> rfl

/-! ## § 6 Public summary -/

theorem finite_causal_locality_bridge_summary :
    FiniteCausalLocalityClosed
    ∧ TwoRouteFiniteActionExtremumClosed
    ∧ FinitePathSpaceActionFunctionalClosed
    ∧ (∀ {P : FiniteProcess} (c : ComposableProcessPaths P),
        causalBefore (P := P) ⟨c.left.start⟩ ⟨c.right.stop⟩)
    ∧ CodeSuccessorStep concreteProcess
    ∧ CodeSuccessorStep operatorCellGridProcess
    ∧ (∀ b : PendingBeyondS27, ClosedByStepwiseS27 b = false)
    ∧ WenConstructiveCoverage := by
  rcases finite_action_extremum_bridge_summary with
    ⟨hActionExtremum, hPathAction, _hContinuousAction, _hActionPhase,
      _hFinitePhase, _hActionToBorn, _hBorn, _hPendingS26, hCoverage⟩
  rcases path_causal_bridge_summary with
    ⟨_hReachable, hCausal, hConcreteSuccessor, _hConcreteMonotone,
      _hConcreteNoSelf, hGridSuccessor, _hGridMonotone, _hGridNoSelf,
      _hConcreteProb, _hGridProb, _hGridLength, _hCoverageS3⟩
  exact
    ⟨ finite_causal_locality_closed
    , hActionExtremum
    , hPathAction
    , hCausal
    , hConcreteSuccessor
    , hGridSuccessor
    , pending_boundary_not_closed_by_s27
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge
