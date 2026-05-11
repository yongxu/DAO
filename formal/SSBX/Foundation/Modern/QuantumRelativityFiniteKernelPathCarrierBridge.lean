/-
# QuantumRelativityFiniteKernelPathCarrierBridge -- S29 finite kernel path carrier

Companion:
`义理/有限核路径载体候选 · Markov桥S29.md`

S29 links S19 finite kernel paths with S28 displayed causal intervals:

1. define a displayed finite carrier list attached to a finite `KernelPath`;
2. prove the attached kernel path reads back as `Reachable` and `causalBefore`;
3. prove the displayed carrier preserves the kernel path weight;
4. instantiate the carrier for the concrete prepared-to-measured path and the
   two-route upper/lower paths.

This is only a finite displayed carrier interface.  It is not a global path
enumeration theorem, not arbitrary causal interval finiteness, not a path
integral, not Lorentzian geometry, and not empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge
import SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge

noncomputable section

open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Displayed finite carrier for kernel paths -/

/--
A displayed finite carrier list attached to a finite kernel path.

The carrier is intentionally displayed data.  S29 does not claim that this list
is the global set of all states between the endpoints under `causalBefore`.
-/
structure DisplayedKernelPathCarrier {P : FiniteProcess}
    (K : MarkovKernelSkeleton P) (a b : P.State) where
  path : KernelPath K a b
  carrier : List P.State
  start_mem : a ∈ carrier
  stop_mem : b ∈ carrier

namespace DisplayedKernelPathCarrier

def weight {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State} (C : DisplayedKernelPathCarrier K a b) : Nat :=
  KernelPath.weight C.path

theorem weight_eq_path_weight {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (C : DisplayedKernelPathCarrier K a b) :
    C.weight = KernelPath.weight C.path :=
  rfl

theorem reachable {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (C : DisplayedKernelPathCarrier K a b) :
    Reachable P a b :=
  path_implies_reachable (KernelPath.toProcessPath C.path) True.intro

theorem causal_before {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (C : DisplayedKernelPathCarrier K a b) :
    causalBefore (P := P) ⟨a⟩ ⟨b⟩ :=
  C.reachable

end DisplayedKernelPathCarrier

def FiniteKernelPathCarrierClosed : Prop :=
  (∀ {P : FiniteProcess}
      {K : MarkovKernelSkeleton P} {a b : P.State}
      (_C : DisplayedKernelPathCarrier K a b),
      Reachable P a b)
    ∧ (∀ {P : FiniteProcess}
        {K : MarkovKernelSkeleton P} {a b : P.State}
        (_C : DisplayedKernelPathCarrier K a b),
        causalBefore (P := P) ⟨a⟩ ⟨b⟩)
    ∧ (∀ {P : FiniteProcess}
        {K : MarkovKernelSkeleton P} {a b : P.State}
        (C : DisplayedKernelPathCarrier K a b),
        C.weight = KernelPath.weight C.path)

theorem finite_kernel_path_carrier_closed :
    FiniteKernelPathCarrierClosed := by
  exact
    ⟨ DisplayedKernelPathCarrier.reachable
    , DisplayedKernelPathCarrier.causal_before
    , DisplayedKernelPathCarrier.weight_eq_path_weight
    ⟩

/-! ## § 2 Sound two-step path-local intervals -/

/--
A sound path-local interval for a single two-step kernel path.

Unlike S28 `FiniteTwoStepCausalIntervalCandidate`, this does not claim
completeness for all middles between the endpoints.  It only says that the
displayed center is supported by two positive-weight kernel edges.
-/
structure SoundKernelTwoStepPathLocalIntervalCandidate
    {P : FiniteProcess}
    (K : MarkovKernelSkeleton P) (a m c : P.State) where
  leftEdge : KernelEdge K a m
  rightEdge : KernelEdge K m c
  carrier : List P.State
  carrier_eq : carrier = [a, m, c]

namespace SoundKernelTwoStepPathLocalIntervalCandidate

def toKernelPath {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a m c : P.State}
    (I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c) :
    KernelPath K a c :=
  KernelPath.append
    (KernelPath.snoc (KernelPath.refl (K := K) a) I.leftEdge)
    (KernelPath.snoc (KernelPath.refl (K := K) m) I.rightEdge)

theorem start_mem {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a m c : P.State}
    (I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c) :
    a ∈ I.carrier := by
  rw [I.carrier_eq]
  exact List.mem_cons_self

theorem middle_mem {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a m c : P.State}
    (I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c) :
    m ∈ I.carrier := by
  rw [I.carrier_eq]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem stop_mem {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a m c : P.State}
    (I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c) :
    c ∈ I.carrier := by
  rw [I.carrier_eq]
  exact
    List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self c))

def toDisplayedCarrier {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a m c : P.State}
    (I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c) :
    DisplayedKernelPathCarrier K a c where
  path := I.toKernelPath
  carrier := I.carrier
  start_mem := I.start_mem
  stop_mem := I.stop_mem

theorem step_law {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a m c : P.State}
    (I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c) :
    P.step a m ∧ P.step m c :=
  ⟨KernelEdge.step I.leftEdge, KernelEdge.step I.rightEdge⟩

theorem causal_law {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a m c : P.State}
    (I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c) :
    causalBefore (P := P) ⟨a⟩ ⟨m⟩
      ∧ causalBefore (P := P) ⟨m⟩ ⟨c⟩ := by
  rcases I.step_law with ⟨hleft, hright⟩
  exact ⟨step_implies_causal_before hleft, step_implies_causal_before hright⟩

theorem displayed_carrier_causal_before {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a m c : P.State}
    (I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c) :
    causalBefore (P := P) ⟨a⟩ ⟨c⟩ :=
  I.toDisplayedCarrier.causal_before

end SoundKernelTwoStepPathLocalIntervalCandidate

def KernelPathLocalIntervalSoundClosed : Prop :=
  (∀ {P : FiniteProcess}
      {K : MarkovKernelSkeleton P} {a m c : P.State}
      (_I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c),
      P.step a m ∧ P.step m c)
    ∧ (∀ {P : FiniteProcess}
        {K : MarkovKernelSkeleton P} {a m c : P.State}
        (_I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c),
        causalBefore (P := P) ⟨a⟩ ⟨m⟩
          ∧ causalBefore (P := P) ⟨m⟩ ⟨c⟩)
    ∧ (∀ {P : FiniteProcess}
        {K : MarkovKernelSkeleton P} {a m c : P.State}
        (_I : SoundKernelTwoStepPathLocalIntervalCandidate K a m c),
        causalBefore (P := P) ⟨a⟩ ⟨c⟩)

theorem kernel_path_local_interval_sound_closed :
    KernelPathLocalIntervalSoundClosed := by
  exact
    ⟨ SoundKernelTwoStepPathLocalIntervalCandidate.step_law
    , SoundKernelTwoStepPathLocalIntervalCandidate.causal_law
    , SoundKernelTwoStepPathLocalIntervalCandidate.displayed_carrier_causal_before
    ⟩

/-! ## § 3 Concrete carrier linked to S28 interval -/

def concretePreparedMeasuredKernelCarrier :
    DisplayedKernelPathCarrier concreteKernel
      ConcreteState.prepared ConcreteState.measured where
  path := concretePreparedMeasuredKernelPath
  carrier := closedTwoStepIntervalPoints concretePreparedMeasuredInterval
  start_mem := left_endpoint_mem_closed_interval
    concretePreparedMeasuredInterval
  stop_mem := right_endpoint_mem_closed_interval
    concretePreparedMeasuredInterval

theorem concrete_kernel_carrier_points :
    concretePreparedMeasuredKernelCarrier.carrier =
      [ConcreteState.prepared, ConcreteState.evolved, ConcreteState.measured] :=
  rfl

theorem concrete_kernel_carrier_matches_s28_interval :
    concretePreparedMeasuredKernelCarrier.carrier =
      closedTwoStepIntervalPoints concretePreparedMeasuredInterval :=
  rfl

theorem concrete_kernel_carrier_weight :
    concretePreparedMeasuredKernelCarrier.weight = 1 := by
  exact concrete_prepared_measured_kernel_path_weight

theorem concrete_kernel_carrier_causal_before :
    causalBefore (P := concreteProcess)
      ⟨ConcreteState.prepared⟩ ⟨ConcreteState.measured⟩ :=
  concretePreparedMeasuredKernelCarrier.causal_before

theorem concrete_kernel_carrier_interval_respects_local_future :
    LocalTwoStepIntervalRespectsLocalFuture
      concreteCausalLocalFuture concretePreparedMeasuredInterval :=
  concrete_prepared_measured_interval_respects_local_future

def concreteKernelPathLocalInterval :
    SoundKernelTwoStepPathLocalIntervalCandidate concreteKernel
      ConcreteState.prepared ConcreteState.evolved ConcreteState.measured where
  leftEdge := concretePreparedEvolvedEdge
  rightEdge := concreteEvolvedMeasuredEdge
  carrier := closedTwoStepIntervalPoints concretePreparedMeasuredInterval
  carrier_eq := rfl

theorem concrete_kernel_path_local_interval_step_law :
    concreteProcess.step ConcreteState.prepared ConcreteState.evolved
      ∧ concreteProcess.step ConcreteState.evolved ConcreteState.measured :=
  concreteKernelPathLocalInterval.step_law

theorem concrete_kernel_path_local_interval_causal_law :
    causalBefore (P := concreteProcess)
      ⟨ConcreteState.prepared⟩ ⟨ConcreteState.evolved⟩
      ∧ causalBefore (P := concreteProcess)
        ⟨ConcreteState.evolved⟩ ⟨ConcreteState.measured⟩ :=
  concreteKernelPathLocalInterval.causal_law

/-! ## § 4 Two-route carriers linked to S28 interval -/

def twoRouteKernel : MarkovKernelSkeleton twoRouteProcess :=
  twoRouteFiniteProbabilityKernel.toMarkovKernelSkeleton

def twoRouteSourceUpperEdge :
    KernelEdge twoRouteKernel TwoRouteState.source TwoRouteState.upper where
  positive_weight := by decide

def twoRouteUpperTargetEdge :
    KernelEdge twoRouteKernel TwoRouteState.upper TwoRouteState.target where
  positive_weight := by decide

def twoRouteSourceLowerEdge :
    KernelEdge twoRouteKernel TwoRouteState.source TwoRouteState.lower where
  positive_weight := by decide

def twoRouteLowerTargetEdge :
    KernelEdge twoRouteKernel TwoRouteState.lower TwoRouteState.target where
  positive_weight := by decide

def twoRouteSourceUpperKernelPath :
    KernelPath twoRouteKernel TwoRouteState.source TwoRouteState.upper :=
  KernelPath.snoc (KernelPath.refl (K := twoRouteKernel) TwoRouteState.source)
    twoRouteSourceUpperEdge

def twoRouteUpperTargetKernelPath :
    KernelPath twoRouteKernel TwoRouteState.upper TwoRouteState.target :=
  KernelPath.snoc (KernelPath.refl (K := twoRouteKernel) TwoRouteState.upper)
    twoRouteUpperTargetEdge

def twoRouteSourceLowerKernelPath :
    KernelPath twoRouteKernel TwoRouteState.source TwoRouteState.lower :=
  KernelPath.snoc (KernelPath.refl (K := twoRouteKernel) TwoRouteState.source)
    twoRouteSourceLowerEdge

def twoRouteLowerTargetKernelPath :
    KernelPath twoRouteKernel TwoRouteState.lower TwoRouteState.target :=
  KernelPath.snoc (KernelPath.refl (K := twoRouteKernel) TwoRouteState.lower)
    twoRouteLowerTargetEdge

def twoRouteUpperKernelPath :
    KernelPath twoRouteKernel TwoRouteState.source TwoRouteState.target :=
  KernelPath.append twoRouteSourceUpperKernelPath twoRouteUpperTargetKernelPath

def twoRouteLowerKernelPath :
    KernelPath twoRouteKernel TwoRouteState.source TwoRouteState.target :=
  KernelPath.append twoRouteSourceLowerKernelPath twoRouteLowerTargetKernelPath

def twoRouteUpperKernelCarrier :
    DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target where
  path := twoRouteUpperKernelPath
  carrier := [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
  start_mem := by exact List.mem_cons_self
  stop_mem := by
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_singleton_self TwoRouteState.target))

def twoRouteLowerKernelCarrier :
    DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target where
  path := twoRouteLowerKernelPath
  carrier := [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
  start_mem := by exact List.mem_cons_self
  stop_mem := by
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_singleton_self TwoRouteState.target))

theorem two_route_upper_kernel_carrier_weight :
    twoRouteUpperKernelCarrier.weight = 1 := by
  simp [DisplayedKernelPathCarrier.weight, twoRouteUpperKernelCarrier,
    twoRouteUpperKernelPath, twoRouteSourceUpperKernelPath,
    twoRouteUpperTargetKernelPath, KernelPath.append, KernelPath.weight,
    KernelEdge.weight, twoRouteKernel, twoRouteFiniteProbabilityKernel,
    TwoRouteState.weight]

theorem two_route_lower_kernel_carrier_weight :
    twoRouteLowerKernelCarrier.weight = 1 := by
  simp [DisplayedKernelPathCarrier.weight, twoRouteLowerKernelCarrier,
    twoRouteLowerKernelPath, twoRouteSourceLowerKernelPath,
    twoRouteLowerTargetKernelPath, KernelPath.append, KernelPath.weight,
    KernelEdge.weight, twoRouteKernel, twoRouteFiniteProbabilityKernel,
    TwoRouteState.weight]

theorem two_route_upper_kernel_carrier_causal_before :
    causalBefore (P := twoRouteProcess)
      ⟨TwoRouteState.source⟩ ⟨TwoRouteState.target⟩ :=
  twoRouteUpperKernelCarrier.causal_before

theorem two_route_lower_kernel_carrier_causal_before :
    causalBefore (P := twoRouteProcess)
      ⟨TwoRouteState.source⟩ ⟨TwoRouteState.target⟩ :=
  twoRouteLowerKernelCarrier.causal_before

theorem two_route_upper_kernel_carrier_middle_in_s28_interval :
    TwoRouteState.upper ∈ twoRouteSourceTargetInterval.center :=
  two_route_upper_between_source_target

theorem two_route_lower_kernel_carrier_middle_in_s28_interval :
    TwoRouteState.lower ∈ twoRouteSourceTargetInterval.center :=
  two_route_lower_between_source_target

def twoRouteUpperKernelPathLocalInterval :
    SoundKernelTwoStepPathLocalIntervalCandidate twoRouteKernel
      TwoRouteState.source TwoRouteState.upper TwoRouteState.target where
  leftEdge := twoRouteSourceUpperEdge
  rightEdge := twoRouteUpperTargetEdge
  carrier := twoRouteUpperKernelCarrier.carrier
  carrier_eq := rfl

def twoRouteLowerKernelPathLocalInterval :
    SoundKernelTwoStepPathLocalIntervalCandidate twoRouteKernel
      TwoRouteState.source TwoRouteState.lower TwoRouteState.target where
  leftEdge := twoRouteSourceLowerEdge
  rightEdge := twoRouteLowerTargetEdge
  carrier := twoRouteLowerKernelCarrier.carrier
  carrier_eq := rfl

theorem two_route_upper_kernel_path_local_interval_step_law :
    twoRouteProcess.step TwoRouteState.source TwoRouteState.upper
      ∧ twoRouteProcess.step TwoRouteState.upper TwoRouteState.target :=
  twoRouteUpperKernelPathLocalInterval.step_law

theorem two_route_lower_kernel_path_local_interval_step_law :
    twoRouteProcess.step TwoRouteState.source TwoRouteState.lower
      ∧ twoRouteProcess.step TwoRouteState.lower TwoRouteState.target :=
  twoRouteLowerKernelPathLocalInterval.step_law

theorem two_route_upper_kernel_path_local_interval_causal_law :
    causalBefore (P := twoRouteProcess)
      ⟨TwoRouteState.source⟩ ⟨TwoRouteState.upper⟩
      ∧ causalBefore (P := twoRouteProcess)
        ⟨TwoRouteState.upper⟩ ⟨TwoRouteState.target⟩ :=
  twoRouteUpperKernelPathLocalInterval.causal_law

theorem two_route_lower_kernel_path_local_interval_causal_law :
    causalBefore (P := twoRouteProcess)
      ⟨TwoRouteState.source⟩ ⟨TwoRouteState.lower⟩
      ∧ causalBefore (P := twoRouteProcess)
        ⟨TwoRouteState.lower⟩ ⟨TwoRouteState.target⟩ :=
  twoRouteLowerKernelPathLocalInterval.causal_law

/-! ## § 5 Remaining physical ledger -/

inductive PendingBeyondS29 where
  | globalPathEnumeration
  | arbitraryLengthCausalIntervals
  | fullCausalSetAxioms
  | globalLocalFiniteness
  | generalPathIntegral
  | hamiltonianGenerator
  | continuousTimeUnitaryGroup
  | lorentzianGeometry
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS29 (_b : PendingBeyondS29) : Bool :=
  false

theorem pending_boundary_not_closed_by_s29
    (b : PendingBeyondS29) :
    ClosedByStepwiseS29 b = false := by
  cases b <;> rfl

/-! ## § 6 Public summary -/

theorem finite_kernel_path_carrier_bridge_summary :
    FiniteKernelPathCarrierClosed
    ∧ KernelPathLocalIntervalSoundClosed
    ∧ FiniteCausalIntervalClosed
    ∧ PathWeightMultiplicationBoundaryClosed
    ∧ concretePreparedMeasuredKernelCarrier.carrier =
      closedTwoStepIntervalPoints concretePreparedMeasuredInterval
    ∧ concretePreparedMeasuredKernelCarrier.weight = 1
    ∧ twoRouteUpperKernelCarrier.weight = 1
    ∧ twoRouteLowerKernelCarrier.weight = 1
    ∧ causalBefore (P := concreteProcess)
      ⟨ConcreteState.prepared⟩ ⟨ConcreteState.measured⟩
    ∧ causalBefore (P := twoRouteProcess)
      ⟨TwoRouteState.source⟩ ⟨TwoRouteState.target⟩
    ∧ (∀ b : PendingBeyondS29, ClosedByStepwiseS29 b = false)
    ∧ WenConstructiveCoverage := by
  rcases finite_causal_interval_bridge_summary with
    ⟨hInterval, _hLocality, _hActionExtremum, _hPathAction,
      _hTwoRoutePair, _hPendingS28, hCoverage⟩
  rcases path_weight_multiplication_bridge_summary with
    ⟨hPathWeight, _hConcreteWeight, _hConcreteReachable,
      _hConcreteCausal, _hPendingS19, _hCoverageS19⟩
  exact
    ⟨ finite_kernel_path_carrier_closed
    , kernel_path_local_interval_sound_closed
    , hInterval
    , hPathWeight
    , concrete_kernel_carrier_matches_s28_interval
    , concrete_kernel_carrier_weight
    , two_route_upper_kernel_carrier_weight
    , two_route_lower_kernel_carrier_weight
    , concrete_kernel_carrier_causal_before
    , two_route_upper_kernel_carrier_causal_before
    , pending_boundary_not_closed_by_s29
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge
