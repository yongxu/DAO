/-
# QuantumRelativityKernelPathRecursiveCarrierBridge -- S30 recursive kernel carrier

Companion:
`义理/递归核路径载体候选 · Markov桥S30.md`

S30 advances S29 by making the displayed carrier canonical for a finite
`KernelPath`: its carrier is now computed recursively from the path
constructors.  This closes a finite constructor-level carrier law, plus an
append readback law and a two-route finite carrier-family witness.

This is still a finite typed-skeleton boundary.  It does not enumerate all
paths between arbitrary endpoints, does not prove arbitrary-length causal
interval completeness, and does not construct a path integral, Lorentzian
geometry, metric recovery, or empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge

namespace SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge

noncomputable section

open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Recursive points for finite kernel paths -/

/--
The edge targets displayed by a finite `KernelPath`.

For a reflexive path there are no edge targets.  A `snoc` appends the new
endpoint to the target list.
-/
def kernelPathTargets {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State} : KernelPath K a b -> List P.State
  | .refl _ => []
  | .snoc (c := c) p _e => kernelPathTargets p ++ [c]

/-- The full recursive point carrier: start point plus all displayed edge targets. -/
def kernelPathPoints {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State} (p : KernelPath K a b) : List P.State :=
  a :: kernelPathTargets p

theorem kernelPathTargets_refl {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} (a : P.State) :
    kernelPathTargets (KernelPath.refl (K := K) a) = [] :=
  rfl

theorem kernelPathTargets_snoc {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (e : KernelEdge K b c) :
    kernelPathTargets (KernelPath.snoc p e) = kernelPathTargets p ++ [c] :=
  rfl

theorem kernelPathPoints_refl {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} (a : P.State) :
    kernelPathPoints (KernelPath.refl (K := K) a) = [a] :=
  rfl

theorem kernelPathPoints_snoc {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (e : KernelEdge K b c) :
    kernelPathPoints (KernelPath.snoc p e)
      = a :: (kernelPathTargets p ++ [c]) :=
  rfl

theorem kernelPath_start_mem {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (p : KernelPath K a b) :
    a ∈ kernelPathPoints p := by
  simp [kernelPathPoints]

theorem kernelPath_stop_mem {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (p : KernelPath K a b) :
    b ∈ kernelPathPoints p := by
  induction p with
  | refl =>
      simp [kernelPathPoints, kernelPathTargets]
  | snoc p e ih =>
      simp [kernelPathPoints, kernelPathTargets]

/-! ## § 2 Append readback for recursive carriers -/

theorem kernelPathTargets_append {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (q : KernelPath K b c) :
    kernelPathTargets (KernelPath.append p q)
      = kernelPathTargets p ++ kernelPathTargets q := by
  induction q with
  | refl =>
      simp [KernelPath.append, kernelPathTargets]
  | snoc q e ih =>
      simp [KernelPath.append, kernelPathTargets, ih, List.append_assoc]

theorem kernelPathPoints_append {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (q : KernelPath K b c) :
    kernelPathPoints (KernelPath.append p q)
      = kernelPathPoints p ++ kernelPathTargets q := by
  simp [kernelPathPoints, kernelPathTargets_append]

/-- The canonical displayed carrier computed directly from a finite `KernelPath`. -/
def recursiveKernelPathCarrier {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (p : KernelPath K a b) :
    DisplayedKernelPathCarrier K a b where
  path := p
  carrier := kernelPathPoints p
  start_mem := kernelPath_start_mem p
  stop_mem := kernelPath_stop_mem p

theorem recursive_kernel_path_carrier_points {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (p : KernelPath K a b) :
    (recursiveKernelPathCarrier p).carrier = kernelPathPoints p :=
  rfl

theorem recursive_kernel_path_carrier_weight {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (p : KernelPath K a b) :
    (recursiveKernelPathCarrier p).weight = KernelPath.weight p :=
  rfl

theorem recursive_kernel_path_carrier_reachable {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (p : KernelPath K a b) :
    Reachable P a b :=
  (recursiveKernelPathCarrier p).reachable

theorem recursive_kernel_path_carrier_causal_before {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (p : KernelPath K a b) :
    causalBefore (P := P) ⟨a⟩ ⟨b⟩ :=
  (recursiveKernelPathCarrier p).causal_before

theorem recursive_kernel_path_carrier_append_points {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (q : KernelPath K b c) :
    (recursiveKernelPathCarrier (KernelPath.append p q)).carrier =
      (recursiveKernelPathCarrier p).carrier ++ kernelPathTargets q := by
  simpa [recursiveKernelPathCarrier] using kernelPathPoints_append p q

def RecursiveKernelPathCarrierClosed : Prop :=
  (∀ {P : FiniteProcess}
      {K : MarkovKernelSkeleton P} {a b : P.State}
      (p : KernelPath K a b),
      (recursiveKernelPathCarrier p).carrier = kernelPathPoints p)
    ∧ (∀ {P : FiniteProcess}
        {K : MarkovKernelSkeleton P} {a b : P.State}
        (p : KernelPath K a b),
        a ∈ (recursiveKernelPathCarrier p).carrier
          ∧ b ∈ (recursiveKernelPathCarrier p).carrier)
    ∧ (∀ {P : FiniteProcess}
        {K : MarkovKernelSkeleton P} {a b : P.State}
        (p : KernelPath K a b),
        (recursiveKernelPathCarrier p).weight = KernelPath.weight p)
    ∧ (∀ {P : FiniteProcess}
        {K : MarkovKernelSkeleton P} {a b : P.State}
        (_p : KernelPath K a b),
        causalBefore (P := P) ⟨a⟩ ⟨b⟩)

theorem recursive_kernel_path_carrier_closed :
    RecursiveKernelPathCarrierClosed := by
  exact
    ⟨ recursive_kernel_path_carrier_points
    , fun p =>
        ⟨ (recursiveKernelPathCarrier p).start_mem
        , (recursiveKernelPathCarrier p).stop_mem
        ⟩
    , recursive_kernel_path_carrier_weight
    , recursive_kernel_path_carrier_causal_before
    ⟩

def KernelPathAppendCarrierClosed : Prop :=
  ∀ {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (q : KernelPath K b c),
    (recursiveKernelPathCarrier (KernelPath.append p q)).carrier =
      (recursiveKernelPathCarrier p).carrier ++ kernelPathTargets q

theorem kernel_path_append_carrier_closed :
    KernelPathAppendCarrierClosed :=
  recursive_kernel_path_carrier_append_points

/-! ## § 3 Concrete and two-route recursive witnesses -/

def concreteRecursiveKernelCarrier :
    DisplayedKernelPathCarrier concreteKernel
      ConcreteState.prepared ConcreteState.measured :=
  recursiveKernelPathCarrier concretePreparedMeasuredKernelPath

theorem concrete_recursive_kernel_carrier_points :
    concreteRecursiveKernelCarrier.carrier =
      [ConcreteState.prepared, ConcreteState.evolved, ConcreteState.measured] := by
  simp [concreteRecursiveKernelCarrier, recursiveKernelPathCarrier,
    kernelPathPoints, kernelPathTargets, concretePreparedMeasuredKernelPath,
    concretePreparedEvolvedKernelPath, concreteEvolvedMeasuredKernelPath,
    KernelPath.append]
  rfl

theorem concrete_recursive_kernel_carrier_matches_s29 :
    concreteRecursiveKernelCarrier.carrier =
      concretePreparedMeasuredKernelCarrier.carrier := by
  simp [concrete_recursive_kernel_carrier_points,
    concrete_kernel_carrier_points]

theorem concrete_recursive_kernel_carrier_weight :
    concreteRecursiveKernelCarrier.weight = 1 := by
  simpa [concreteRecursiveKernelCarrier, recursiveKernelPathCarrier,
    DisplayedKernelPathCarrier.weight]
    using concrete_prepared_measured_kernel_path_weight

def twoRouteUpperRecursiveKernelCarrier :
    DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target :=
  recursiveKernelPathCarrier twoRouteUpperKernelPath

def twoRouteLowerRecursiveKernelCarrier :
    DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target :=
  recursiveKernelPathCarrier twoRouteLowerKernelPath

theorem two_route_upper_recursive_kernel_carrier_points :
    twoRouteUpperRecursiveKernelCarrier.carrier =
      [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target] := by
  simp [twoRouteUpperRecursiveKernelCarrier, recursiveKernelPathCarrier,
    kernelPathPoints, kernelPathTargets, twoRouteUpperKernelPath,
    twoRouteSourceUpperKernelPath, twoRouteUpperTargetKernelPath,
    KernelPath.append]
  rfl

theorem two_route_lower_recursive_kernel_carrier_points :
    twoRouteLowerRecursiveKernelCarrier.carrier =
      [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target] := by
  simp [twoRouteLowerRecursiveKernelCarrier, recursiveKernelPathCarrier,
    kernelPathPoints, kernelPathTargets, twoRouteLowerKernelPath,
    twoRouteSourceLowerKernelPath, twoRouteLowerTargetKernelPath,
    KernelPath.append]
  rfl

theorem two_route_upper_recursive_kernel_carrier_matches_s29 :
    twoRouteUpperRecursiveKernelCarrier.carrier =
      twoRouteUpperKernelCarrier.carrier := by
  simp [two_route_upper_recursive_kernel_carrier_points, twoRouteUpperKernelCarrier]
  rfl

theorem two_route_lower_recursive_kernel_carrier_matches_s29 :
    twoRouteLowerRecursiveKernelCarrier.carrier =
      twoRouteLowerKernelCarrier.carrier := by
  simp [two_route_lower_recursive_kernel_carrier_points, twoRouteLowerKernelCarrier]
  rfl

theorem two_route_upper_recursive_kernel_carrier_weight :
    twoRouteUpperRecursiveKernelCarrier.weight = 1 := by
  simpa [twoRouteUpperRecursiveKernelCarrier, recursiveKernelPathCarrier,
    DisplayedKernelPathCarrier.weight, twoRouteUpperKernelCarrier]
    using two_route_upper_kernel_carrier_weight

theorem two_route_lower_recursive_kernel_carrier_weight :
    twoRouteLowerRecursiveKernelCarrier.weight = 1 := by
  simpa [twoRouteLowerRecursiveKernelCarrier, recursiveKernelPathCarrier,
    DisplayedKernelPathCarrier.weight, twoRouteLowerKernelCarrier]
    using two_route_lower_kernel_carrier_weight

/-- The finite two-route family of recursive carriers for the shared endpoints. -/
def twoRouteRecursiveKernelCarrierFamily :
    List (DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target) :=
  [twoRouteUpperRecursiveKernelCarrier, twoRouteLowerRecursiveKernelCarrier]

theorem two_route_recursive_kernel_carrier_family_length :
    twoRouteRecursiveKernelCarrierFamily.length = 2 :=
  rfl

theorem two_route_recursive_kernel_carrier_family_carriers :
    twoRouteRecursiveKernelCarrierFamily.map (fun C => C.carrier) =
      [ [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      , [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
      ] := by
  simp [twoRouteRecursiveKernelCarrierFamily,
    two_route_upper_recursive_kernel_carrier_points,
    two_route_lower_recursive_kernel_carrier_points]
  rfl

theorem two_route_recursive_kernel_carrier_family_weights :
    twoRouteRecursiveKernelCarrierFamily.map
      (fun C => DisplayedKernelPathCarrier.weight C) = [1, 1] := by
  simp [twoRouteRecursiveKernelCarrierFamily,
    two_route_upper_recursive_kernel_carrier_weight,
    two_route_lower_recursive_kernel_carrier_weight]

def FiniteRecursiveKernelCarrierFamilyClosed : Prop :=
  twoRouteRecursiveKernelCarrierFamily.length = 2
    ∧ twoRouteRecursiveKernelCarrierFamily.map (fun C => C.carrier) =
      [ [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      , [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
      ]
    ∧ twoRouteRecursiveKernelCarrierFamily.map
      (fun C => DisplayedKernelPathCarrier.weight C) = [1, 1]

theorem finite_recursive_kernel_carrier_family_closed :
    FiniteRecursiveKernelCarrierFamilyClosed :=
  ⟨ two_route_recursive_kernel_carrier_family_length
  , two_route_recursive_kernel_carrier_family_carriers
  , two_route_recursive_kernel_carrier_family_weights
  ⟩

/-! ## § 4 Remaining physical ledger -/

inductive PendingBeyondS30 where
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

def ClosedByStepwiseS30 (_b : PendingBeyondS30) : Bool :=
  false

theorem pending_boundary_not_closed_by_s30
    (b : PendingBeyondS30) :
    ClosedByStepwiseS30 b = false := by
  cases b <;> rfl

/-! ## § 5 Public summary -/

theorem kernel_path_recursive_carrier_bridge_summary :
    RecursiveKernelPathCarrierClosed
    ∧ KernelPathAppendCarrierClosed
    ∧ FiniteRecursiveKernelCarrierFamilyClosed
    ∧ FiniteKernelPathCarrierClosed
    ∧ KernelPathLocalIntervalSoundClosed
    ∧ concreteRecursiveKernelCarrier.carrier =
      [ConcreteState.prepared, ConcreteState.evolved, ConcreteState.measured]
    ∧ concreteRecursiveKernelCarrier.weight = 1
    ∧ twoRouteRecursiveKernelCarrierFamily.map (fun C => C.carrier) =
      [ [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      , [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
      ]
    ∧ twoRouteRecursiveKernelCarrierFamily.map
      (fun C => DisplayedKernelPathCarrier.weight C) = [1, 1]
    ∧ (∀ b : PendingBeyondS30, ClosedByStepwiseS30 b = false)
    ∧ WenConstructiveCoverage := by
  rcases finite_kernel_path_carrier_bridge_summary with
    ⟨hCarrier, hLocalInterval, _hInterval, _hPathWeight,
      _hConcreteCarrier, _hConcreteWeight, _hUpperWeight, _hLowerWeight,
      _hConcreteCausal, _hTwoRouteCausal, _hPendingS29, hCoverage⟩
  exact
    ⟨ recursive_kernel_path_carrier_closed
    , kernel_path_append_carrier_closed
    , finite_recursive_kernel_carrier_family_closed
    , hCarrier
    , hLocalInterval
    , concrete_recursive_kernel_carrier_points
    , concrete_recursive_kernel_carrier_weight
    , two_route_recursive_kernel_carrier_family_carriers
    , two_route_recursive_kernel_carrier_family_weights
    , pending_boundary_not_closed_by_s30
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge
