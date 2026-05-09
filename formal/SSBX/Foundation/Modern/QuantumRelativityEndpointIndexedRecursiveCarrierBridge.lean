/-
# QuantumRelativityEndpointIndexedRecursiveCarrierBridge -- S31 endpoint-indexed recursive carriers

Companion:
`义理/端点索引递归载体族候选 · Markov桥S31.md`

S31 packages S30 recursive kernel carriers into an endpoint-indexed finite
family.  The endpoint index is carried by the type of every displayed carrier,
so member readback gives shared endpoints and causal-before for the same
source/target pair.  The two-route toy family is kept finite and explicit:
its carrier lists are the upper/lower recursive point lists and its displayed
weights are `[1, 1]`, with total weight `2`.

This is not all-path completeness.  It does not prove that the displayed
family contains every kernel path between the endpoints, and it does not
construct a path integral, causal set local finiteness, Lorentzian geometry,
metric recovery, or empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge

namespace SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedRecursiveCarrierBridge

noncomputable section

open SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Endpoint-indexed recursive carrier families -/

/--
A finite family of recursive kernel carriers indexed by shared endpoints.

The type of each member fixes the same `a` and `b`; S31 only packages and reads
back that finite family.  It does not assert that the family enumerates all
possible paths between `a` and `b`.
-/
structure EndpointIndexedRecursiveKernelCarrierFamily
    {P : FiniteProcess}
    (K : MarkovKernelSkeleton P) (a b : P.State) where
  carriers : List (DisplayedKernelPathCarrier K a b)

namespace EndpointIndexedRecursiveKernelCarrierFamily

def carrierLists {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State}
    (F : EndpointIndexedRecursiveKernelCarrierFamily K a b) :
    List (List P.State) :=
  F.carriers.map (fun C => C.carrier)

def weights {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State}
    (F : EndpointIndexedRecursiveKernelCarrierFamily K a b) : List Nat :=
  F.carriers.map (fun C => DisplayedKernelPathCarrier.weight C)

def weightSum {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State}
    (F : EndpointIndexedRecursiveKernelCarrierFamily K a b) : Nat :=
  F.weights.sum

theorem member_start_mem {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (F : EndpointIndexedRecursiveKernelCarrierFamily K a b)
    (C : DisplayedKernelPathCarrier K a b)
    (_h : C ∈ F.carriers) :
    a ∈ C.carrier :=
  C.start_mem

theorem member_stop_mem {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (F : EndpointIndexedRecursiveKernelCarrierFamily K a b)
    (C : DisplayedKernelPathCarrier K a b)
    (_h : C ∈ F.carriers) :
    b ∈ C.carrier :=
  C.stop_mem

theorem member_causal_before {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (F : EndpointIndexedRecursiveKernelCarrierFamily K a b)
    (C : DisplayedKernelPathCarrier K a b)
    (_h : C ∈ F.carriers) :
    causalBefore (P := P) ⟨a⟩ ⟨b⟩ :=
  C.causal_before

theorem member_weight_readback {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (F : EndpointIndexedRecursiveKernelCarrierFamily K a b)
    (C : DisplayedKernelPathCarrier K a b)
    (_h : C ∈ F.carriers) :
    C.weight = KernelPath.weight C.path :=
  C.weight_eq_path_weight

end EndpointIndexedRecursiveKernelCarrierFamily

def EndpointIndexedRecursiveCarrierFamilyClosed : Prop :=
  ∀ {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b : P.State}
    (F : EndpointIndexedRecursiveKernelCarrierFamily K a b)
    (C : DisplayedKernelPathCarrier K a b),
    C ∈ F.carriers ->
      a ∈ C.carrier
        ∧ b ∈ C.carrier
        ∧ causalBefore (P := P) ⟨a⟩ ⟨b⟩
        ∧ C.weight = KernelPath.weight C.path

theorem endpoint_indexed_recursive_carrier_family_closed :
    EndpointIndexedRecursiveCarrierFamilyClosed := by
  intro P K a b F C h
  exact
    ⟨ F.member_start_mem C h
    , F.member_stop_mem C h
    , F.member_causal_before C h
    , F.member_weight_readback C h
    ⟩

/-! ## § 2 Two-route endpoint-indexed family -/

def twoRouteEndpointIndexedRecursiveCarrierFamily :
    EndpointIndexedRecursiveKernelCarrierFamily twoRouteKernel
      TwoRouteState.source TwoRouteState.target where
  carriers := twoRouteRecursiveKernelCarrierFamily

theorem two_route_endpoint_indexed_recursive_family_length :
    twoRouteEndpointIndexedRecursiveCarrierFamily.carriers.length = 2 := by
  simpa [twoRouteEndpointIndexedRecursiveCarrierFamily]
    using two_route_recursive_kernel_carrier_family_length

theorem two_route_endpoint_indexed_recursive_family_carriers :
    twoRouteEndpointIndexedRecursiveCarrierFamily.carrierLists =
      [ [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      , [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
      ] := by
  simpa [EndpointIndexedRecursiveKernelCarrierFamily.carrierLists,
    twoRouteEndpointIndexedRecursiveCarrierFamily]
    using two_route_recursive_kernel_carrier_family_carriers

theorem two_route_endpoint_indexed_recursive_family_weights :
    twoRouteEndpointIndexedRecursiveCarrierFamily.weights = [1, 1] := by
  simpa [EndpointIndexedRecursiveKernelCarrierFamily.weights,
    twoRouteEndpointIndexedRecursiveCarrierFamily]
    using two_route_recursive_kernel_carrier_family_weights

theorem two_route_endpoint_indexed_recursive_family_weight_sum :
    twoRouteEndpointIndexedRecursiveCarrierFamily.weightSum = 2 := by
  simp [EndpointIndexedRecursiveKernelCarrierFamily.weightSum,
    two_route_endpoint_indexed_recursive_family_weights]

theorem two_route_endpoint_indexed_recursive_family_member_causal
    (C : DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target)
    (h : C ∈ twoRouteEndpointIndexedRecursiveCarrierFamily.carriers) :
    causalBefore (P := twoRouteProcess)
      ⟨TwoRouteState.source⟩ ⟨TwoRouteState.target⟩ :=
  twoRouteEndpointIndexedRecursiveCarrierFamily.member_causal_before C h

def TwoRouteEndpointIndexedRecursiveFamilyClosed : Prop :=
  twoRouteEndpointIndexedRecursiveCarrierFamily.carriers.length = 2
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.carrierLists =
      [ [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      , [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
      ]
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.weights = [1, 1]
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.weightSum = 2
    ∧ (∀ C : DisplayedKernelPathCarrier twoRouteKernel
          TwoRouteState.source TwoRouteState.target,
        C ∈ twoRouteEndpointIndexedRecursiveCarrierFamily.carriers ->
          causalBefore (P := twoRouteProcess)
            ⟨TwoRouteState.source⟩ ⟨TwoRouteState.target⟩)

theorem two_route_endpoint_indexed_recursive_family_closed :
    TwoRouteEndpointIndexedRecursiveFamilyClosed :=
  ⟨ two_route_endpoint_indexed_recursive_family_length
  , two_route_endpoint_indexed_recursive_family_carriers
  , two_route_endpoint_indexed_recursive_family_weights
  , two_route_endpoint_indexed_recursive_family_weight_sum
  , two_route_endpoint_indexed_recursive_family_member_causal
  ⟩

/-! ## § 3 Remaining physical ledger -/

inductive PendingBeyondS31 where
  | allPathCompleteness
  | globalPathEnumeration
  | arbitraryLengthCausalIntervals
  | fullCausalSetAxioms
  | globalLocalFiniteness
  | generalPathIntegral
  | lorentzianGeometry
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS31 (_b : PendingBeyondS31) : Bool :=
  false

theorem pending_boundary_not_closed_by_s31
    (b : PendingBeyondS31) :
    ClosedByStepwiseS31 b = false := by
  cases b <;> rfl

/-! ## § 4 Public summary -/

theorem endpoint_indexed_recursive_carrier_bridge_summary :
    EndpointIndexedRecursiveCarrierFamilyClosed
    ∧ TwoRouteEndpointIndexedRecursiveFamilyClosed
    ∧ RecursiveKernelPathCarrierClosed
    ∧ KernelPathAppendCarrierClosed
    ∧ FiniteRecursiveKernelCarrierFamilyClosed
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.carrierLists =
      [ [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      , [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
      ]
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.weights = [1, 1]
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.weightSum = 2
    ∧ (∀ b : PendingBeyondS31, ClosedByStepwiseS31 b = false)
    ∧ WenConstructiveCoverage := by
  rcases kernel_path_recursive_carrier_bridge_summary with
    ⟨hRecursive, hAppend, hFamily, _hS29Carrier, _hLocalInterval,
      _hConcreteCarrier, _hConcreteWeight, _hFamilyCarriers, _hFamilyWeights,
      _hPendingS30, hCoverage⟩
  exact
    ⟨ endpoint_indexed_recursive_carrier_family_closed
    , two_route_endpoint_indexed_recursive_family_closed
    , hRecursive
    , hAppend
    , hFamily
    , two_route_endpoint_indexed_recursive_family_carriers
    , two_route_endpoint_indexed_recursive_family_weights
    , two_route_endpoint_indexed_recursive_family_weight_sum
    , pending_boundary_not_closed_by_s31
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedRecursiveCarrierBridge
