/-
# QuantumRelativityFiniteCausalIntervalBridge -- S28 finite causal interval

Companion:
`义理/有限因果区间候选 · Markov桥S28.md`

S28 advances S27 by one local-finiteness step:

1. define a finite two-step causal interval as an explicit list of center
   states between fixed endpoints;
2. prove the list is sound and complete for genuine `step a m ∧ step m c`
   witnesses;
3. prove such center states respect the S27 finite local-future interface;
4. instantiate the interval for the concrete prepared/evolved/measured chain
   and the two-route source/target toy process.

This is only a finite two-step interval candidate.  It is not a full causal set
axiomatization, not arbitrary-length causal interval finiteness, not a
Lorentzian light-cone theorem, not metric recovery, and not empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge
import SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge

noncomputable section

open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite two-step causal interval interface -/

/--
A finite two-step causal interval candidate displays all center states `m`
between fixed endpoints `a` and `c` for the local relation
`P.step a m ∧ P.step m c`.
-/
structure FiniteTwoStepCausalIntervalCandidate
    (P : FiniteProcess) (a c : P.State) where
  center : List P.State
  middle_sound :
    ∀ {m : P.State}, m ∈ center -> P.step a m ∧ P.step m c
  middle_complete :
    ∀ {m : P.State}, P.step a m -> P.step m c -> m ∈ center

/-- The displayed closed interval points: left endpoint, displayed middles,
and right endpoint. -/
def closedTwoStepIntervalPoints {P : FiniteProcess} {a c : P.State}
    (I : FiniteTwoStepCausalIntervalCandidate P a c) :
    List P.State :=
  a :: (I.center ++ [c])

theorem left_endpoint_mem_closed_interval {P : FiniteProcess}
    {a c : P.State} (I : FiniteTwoStepCausalIntervalCandidate P a c) :
    a ∈ closedTwoStepIntervalPoints I := by
  simp [closedTwoStepIntervalPoints]

theorem right_endpoint_mem_closed_interval {P : FiniteProcess}
    {a c : P.State} (I : FiniteTwoStepCausalIntervalCandidate P a c) :
    c ∈ closedTwoStepIntervalPoints I := by
  simp [closedTwoStepIntervalPoints]

theorem middle_mem_closed_interval {P : FiniteProcess}
    {a c m : P.State} (I : FiniteTwoStepCausalIntervalCandidate P a c) :
    m ∈ I.center -> m ∈ closedTwoStepIntervalPoints I := by
  intro hm
  simp [closedTwoStepIntervalPoints, hm]

theorem interval_middle_step_law {P : FiniteProcess}
    {a c m : P.State} (I : FiniteTwoStepCausalIntervalCandidate P a c) :
    m ∈ I.center -> P.step a m ∧ P.step m c :=
  I.middle_sound

theorem interval_middle_causal_law {P : FiniteProcess}
    {a c m : P.State} (I : FiniteTwoStepCausalIntervalCandidate P a c) :
    m ∈ I.center ->
      causalBefore (P := P) ⟨a⟩ ⟨m⟩ ∧
        causalBefore (P := P) ⟨m⟩ ⟨c⟩ := by
  intro hm
  rcases I.middle_sound hm with ⟨hleft, hright⟩
  exact ⟨step_implies_causal_before hleft, step_implies_causal_before hright⟩

/-- A displayed two-step interval respects a local-future interface when every
center lies in the local future of the left endpoint and the right endpoint lies
in the local future of that center. -/
def LocalTwoStepIntervalRespectsLocalFuture {P : FiniteProcess}
    {a c : P.State}
    (N : FiniteCausalLocalFutureCandidate P)
    (I : FiniteTwoStepCausalIntervalCandidate P a c) : Prop :=
  ∀ {m : P.State}, m ∈ I.center ->
    m ∈ N.localFuture a ∧ c ∈ N.localFuture m

theorem interval_respects_local_future {P : FiniteProcess}
    {a c : P.State}
    (N : FiniteCausalLocalFutureCandidate P)
    (I : FiniteTwoStepCausalIntervalCandidate P a c) :
    LocalTwoStepIntervalRespectsLocalFuture N I := by
  intro m hm
  rcases I.middle_sound hm with ⟨hleft, hright⟩
  exact ⟨N.localFuture_complete hleft, N.localFuture_complete hright⟩

/-! ## § 2 Concrete prepared-to-measured interval -/

def concretePreparedMeasuredInterval :
    FiniteTwoStepCausalIntervalCandidate concreteProcess
      ConcreteState.prepared ConcreteState.measured where
  center := [ConcreteState.evolved]
  middle_sound := by
    intro m hm
    have hm_eq : m = ConcreteState.evolved := by
      simpa using hm
    subst m
    exact
      ⟨ by simp [concreteProcess, ConcreteState.step]
      , by simp [concreteProcess, ConcreteState.step]
      ⟩
  middle_complete := by
    intro m hleft hright
    cases m
    · simp [concreteProcess, ConcreteState.step] at hleft
    · exact List.mem_singleton_self ConcreteState.evolved
    · simp [concreteProcess, ConcreteState.step] at hright

theorem concrete_prepared_measured_interval_middle :
    concretePreparedMeasuredInterval.center = [ConcreteState.evolved] :=
  rfl

theorem concrete_prepared_measured_closed_interval_points :
    closedTwoStepIntervalPoints concretePreparedMeasuredInterval =
      [ConcreteState.prepared, ConcreteState.evolved, ConcreteState.measured] :=
  rfl

theorem concrete_evolved_between_prepared_measured :
    ConcreteState.evolved ∈ concretePreparedMeasuredInterval.center := by
  exact List.mem_singleton_self ConcreteState.evolved

theorem concrete_prepared_measured_interval_respects_local_future :
    LocalTwoStepIntervalRespectsLocalFuture
      concreteCausalLocalFuture concretePreparedMeasuredInterval :=
  interval_respects_local_future
    concreteCausalLocalFuture concretePreparedMeasuredInterval

theorem concrete_prepared_measured_middle_causal_law :
    causalBefore (P := concreteProcess)
      ⟨ConcreteState.prepared⟩ ⟨ConcreteState.evolved⟩
      ∧ causalBefore (P := concreteProcess)
        ⟨ConcreteState.evolved⟩ ⟨ConcreteState.measured⟩ :=
  interval_middle_causal_law concretePreparedMeasuredInterval
    concrete_evolved_between_prepared_measured

/-! ## § 3 Two-route source-to-target interval -/

def twoRouteLocalFuture : TwoRouteState -> List TwoRouteState
  | .source => [.upper, .lower]
  | .upper => [.target]
  | .lower => [.target]
  | .target => []

theorem twoRoute_local_future_sound
    {a b : TwoRouteState} :
    b ∈ twoRouteLocalFuture a -> twoRouteProcess.step a b := by
  intro h
  cases a <;> cases b <;>
    simp [twoRouteLocalFuture, twoRouteProcess, TwoRouteState.step] at h ⊢

theorem twoRoute_local_future_complete
    {a b : TwoRouteState} :
    twoRouteProcess.step a b -> b ∈ twoRouteLocalFuture a := by
  intro h
  cases a <;> cases b <;>
    simp [twoRouteLocalFuture, twoRouteProcess, TwoRouteState.step] at h ⊢

def twoRouteCausalLocalFuture :
    FiniteCausalLocalFutureCandidate twoRouteProcess where
  localFuture := twoRouteLocalFuture
  localFuture_sound := twoRoute_local_future_sound
  localFuture_complete := twoRoute_local_future_complete

theorem twoRoute_local_future_iff_step
    (a b : TwoRouteState) :
    b ∈ twoRouteCausalLocalFuture.localFuture a ↔
      twoRouteProcess.step a b :=
  local_future_iff_step twoRouteCausalLocalFuture a b

theorem twoRoute_kernel_respects_local_future :
    KernelRespectsLocalFuture
      twoRouteFiniteProbabilityKernel.toMarkovKernelSkeleton
      twoRouteCausalLocalFuture :=
  kernel_positive_weight_implies_local_future
    twoRouteFiniteProbabilityKernel.toMarkovKernelSkeleton
    twoRouteCausalLocalFuture

def twoRouteSourceTargetInterval :
    FiniteTwoStepCausalIntervalCandidate twoRouteProcess
      TwoRouteState.source TwoRouteState.target where
  center := [TwoRouteState.upper, TwoRouteState.lower]
  middle_sound := by
    intro m hm
    have hm_cases :
        m = TwoRouteState.upper ∨ m = TwoRouteState.lower := by
      simpa using hm
    rcases hm_cases with rfl | rfl
    · exact
        ⟨ by simp [twoRouteProcess, TwoRouteState.step]
        , by simp [twoRouteProcess, TwoRouteState.step]
        ⟩
    · exact
        ⟨ by simp [twoRouteProcess, TwoRouteState.step]
        , by simp [twoRouteProcess, TwoRouteState.step]
        ⟩
  middle_complete := by
    intro m hleft hright
    cases m
    · simp [twoRouteProcess, TwoRouteState.step] at hleft
    · exact List.mem_cons_self
    · exact
        List.mem_cons_of_mem _
          (List.mem_singleton_self TwoRouteState.lower)
    · simp [twoRouteProcess, TwoRouteState.step] at hleft

theorem two_route_source_target_interval_middle :
    twoRouteSourceTargetInterval.center =
      [TwoRouteState.upper, TwoRouteState.lower] :=
  rfl

theorem two_route_source_target_closed_interval_points :
    closedTwoStepIntervalPoints twoRouteSourceTargetInterval =
      [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.lower,
        TwoRouteState.target] :=
  rfl

theorem two_route_upper_between_source_target :
    TwoRouteState.upper ∈ twoRouteSourceTargetInterval.center := by
  exact List.mem_cons_self

theorem two_route_lower_between_source_target :
    TwoRouteState.lower ∈ twoRouteSourceTargetInterval.center := by
  exact
    List.mem_cons_of_mem _
      (List.mem_singleton_self TwoRouteState.lower)

theorem two_route_source_target_interval_respects_local_future :
    LocalTwoStepIntervalRespectsLocalFuture
      twoRouteCausalLocalFuture twoRouteSourceTargetInterval :=
  interval_respects_local_future
    twoRouteCausalLocalFuture twoRouteSourceTargetInterval

theorem two_route_interval_has_two_distinct_middles :
    TwoRouteState.upper ∈ twoRouteSourceTargetInterval.center
      ∧ TwoRouteState.lower ∈ twoRouteSourceTargetInterval.center
      ∧ TwoRouteState.upper ≠ TwoRouteState.lower := by
  exact
    ⟨ two_route_upper_between_source_target
    , two_route_lower_between_source_target
    , by decide
    ⟩

theorem two_route_source_target_middle_complete
    (m : TwoRouteState) :
    twoRouteProcess.step TwoRouteState.source m ->
      twoRouteProcess.step m TwoRouteState.target ->
      m = TwoRouteState.upper ∨ m = TwoRouteState.lower := by
  intro hleft hright
  cases m
  · simp [twoRouteProcess, TwoRouteState.step] at hleft
  · exact Or.inl rfl
  · exact Or.inr rfl
  · simp [twoRouteProcess, TwoRouteState.step] at hleft

theorem two_route_source_target_middle_causal_law :
    (causalBefore (P := twoRouteProcess)
        ⟨TwoRouteState.source⟩ ⟨TwoRouteState.upper⟩
      ∧ causalBefore (P := twoRouteProcess)
        ⟨TwoRouteState.upper⟩ ⟨TwoRouteState.target⟩)
      ∧ (causalBefore (P := twoRouteProcess)
          ⟨TwoRouteState.source⟩ ⟨TwoRouteState.lower⟩
        ∧ causalBefore (P := twoRouteProcess)
          ⟨TwoRouteState.lower⟩ ⟨TwoRouteState.target⟩) := by
  exact
    ⟨ interval_middle_causal_law twoRouteSourceTargetInterval
        two_route_upper_between_source_target
    , interval_middle_causal_law twoRouteSourceTargetInterval
        two_route_lower_between_source_target
    ⟩

/-! ## § 4 Closed S28 boundary -/

def FiniteCausalIntervalClosed : Prop :=
  (∀ {P : FiniteProcess} {a c m : P.State}
      (I : FiniteTwoStepCausalIntervalCandidate P a c),
      m ∈ I.center -> P.step a m ∧ P.step m c)
    ∧ (∀ {P : FiniteProcess} {a c m : P.State}
        (I : FiniteTwoStepCausalIntervalCandidate P a c),
        m ∈ I.center ->
          causalBefore (P := P) ⟨a⟩ ⟨m⟩ ∧
            causalBefore (P := P) ⟨m⟩ ⟨c⟩)
    ∧ (∀ {P : FiniteProcess} {a c : P.State}
        (N : FiniteCausalLocalFutureCandidate P)
        (I : FiniteTwoStepCausalIntervalCandidate P a c),
        LocalTwoStepIntervalRespectsLocalFuture N I)
    ∧ closedTwoStepIntervalPoints concretePreparedMeasuredInterval =
      [ConcreteState.prepared, ConcreteState.evolved, ConcreteState.measured]
    ∧ LocalTwoStepIntervalRespectsLocalFuture
      concreteCausalLocalFuture concretePreparedMeasuredInterval
    ∧ closedTwoStepIntervalPoints twoRouteSourceTargetInterval =
      [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.lower,
        TwoRouteState.target]
    ∧ LocalTwoStepIntervalRespectsLocalFuture
      twoRouteCausalLocalFuture twoRouteSourceTargetInterval
    ∧ KernelRespectsLocalFuture
      twoRouteFiniteProbabilityKernel.toMarkovKernelSkeleton
      twoRouteCausalLocalFuture
    ∧ (TwoRouteState.upper ∈ twoRouteSourceTargetInterval.center
      ∧ TwoRouteState.lower ∈ twoRouteSourceTargetInterval.center
      ∧ TwoRouteState.upper ≠ TwoRouteState.lower)

theorem finite_causal_interval_closed :
    FiniteCausalIntervalClosed := by
  exact
    ⟨ interval_middle_step_law
    , interval_middle_causal_law
    , interval_respects_local_future
    , concrete_prepared_measured_closed_interval_points
    , concrete_prepared_measured_interval_respects_local_future
    , two_route_source_target_closed_interval_points
    , two_route_source_target_interval_respects_local_future
    , twoRoute_kernel_respects_local_future
    , two_route_interval_has_two_distinct_middles
    ⟩

/-! ## § 5 Remaining physical ledger -/

inductive PendingBeyondS28 where
  | fullCausalSetAxioms
  | arbitraryLengthCausalIntervals
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

def ClosedByStepwiseS28 (_b : PendingBeyondS28) : Bool :=
  false

theorem pending_boundary_not_closed_by_s28
    (b : PendingBeyondS28) :
    ClosedByStepwiseS28 b = false := by
  cases b <;> rfl

/-! ## § 6 Public summary -/

theorem finite_causal_interval_bridge_summary :
    FiniteCausalIntervalClosed
    ∧ FiniteCausalLocalityClosed
    ∧ TwoRouteFiniteActionExtremumClosed
    ∧ FinitePathSpaceActionFunctionalClosed
    ∧ HasSameEndpointTwoStepPair twoRouteProcess
    ∧ (∀ b : PendingBeyondS28, ClosedByStepwiseS28 b = false)
    ∧ WenConstructiveCoverage := by
  rcases finite_causal_locality_bridge_summary with
    ⟨hLocality, hActionExtremum, hPathAction, _hCausal, _hConcreteSuccessor,
      _hGridSuccessor, _hPendingS27, hCoverage⟩
  exact
    ⟨ finite_causal_interval_closed
    , hLocality
    , hActionExtremum
    , hPathAction
    , ⟨twoRouteUpperLowerPair⟩
    , pending_boundary_not_closed_by_s28
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge
