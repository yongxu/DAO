/-
# QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge -- S32 two-route displayed carrier completeness

Companion:
`义理/双路径递归载体族完备候选 · Markov桥S32.md`

S32 closes only a toy displayed-family completeness boundary: the endpoint-
indexed recursive carrier family for the two-route source/target pair contains
the displayed upper and lower recursive carriers, and every displayed member of
that finite family is one of those two carriers.

This does not enumerate all possible `KernelPath` inhabitants between arbitrary
endpoints.  It also does not prove a path integral, full causal set local
finiteness, Lorentzian geometry, metric recovery, or empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedRecursiveCarrierBridge

namespace SSBX.Foundation.Modern.QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge

noncomputable section

open SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedRecursiveCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Two-route displayed family completeness -/

def twoRouteDisplayedRecursiveCarrierFamily :
    List (DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target) :=
  twoRouteEndpointIndexedRecursiveCarrierFamily.carriers

theorem two_route_displayed_recursive_family_eq :
    twoRouteDisplayedRecursiveCarrierFamily =
      [twoRouteUpperRecursiveKernelCarrier,
        twoRouteLowerRecursiveKernelCarrier] :=
  rfl

theorem two_route_upper_recursive_carrier_mem_family :
    twoRouteUpperRecursiveKernelCarrier
      ∈ twoRouteDisplayedRecursiveCarrierFamily := by
  simp [twoRouteDisplayedRecursiveCarrierFamily,
    twoRouteEndpointIndexedRecursiveCarrierFamily,
    twoRouteRecursiveKernelCarrierFamily]

theorem two_route_lower_recursive_carrier_mem_family :
    twoRouteLowerRecursiveKernelCarrier
      ∈ twoRouteDisplayedRecursiveCarrierFamily := by
  simp [twoRouteDisplayedRecursiveCarrierFamily,
    twoRouteEndpointIndexedRecursiveCarrierFamily,
    twoRouteRecursiveKernelCarrierFamily]

theorem two_route_displayed_recursive_family_member_cases
    (C : DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target)
    (h : C ∈ twoRouteDisplayedRecursiveCarrierFamily) :
    C = twoRouteUpperRecursiveKernelCarrier
      ∨ C = twoRouteLowerRecursiveKernelCarrier := by
  simpa [twoRouteDisplayedRecursiveCarrierFamily,
    twoRouteEndpointIndexedRecursiveCarrierFamily,
    twoRouteRecursiveKernelCarrierFamily] using h

theorem two_route_displayed_recursive_family_member_carrier_cases
    (C : DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target)
    (h : C ∈ twoRouteDisplayedRecursiveCarrierFamily) :
    C.carrier =
        [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      ∨ C.carrier =
        [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target] := by
  rcases two_route_displayed_recursive_family_member_cases C h with hupper | hlower
  · left
    rw [hupper]
    exact two_route_upper_recursive_kernel_carrier_points
  · right
    rw [hlower]
    exact two_route_lower_recursive_kernel_carrier_points

theorem two_route_displayed_recursive_family_member_weight_one
    (C : DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target)
    (h : C ∈ twoRouteDisplayedRecursiveCarrierFamily) :
    C.weight = 1 := by
  rcases two_route_displayed_recursive_family_member_cases C h with hupper | hlower
  · rw [hupper]
    exact two_route_upper_recursive_kernel_carrier_weight
  · rw [hlower]
    exact two_route_lower_recursive_kernel_carrier_weight

theorem two_route_displayed_recursive_family_member_causal
    (C : DisplayedKernelPathCarrier twoRouteKernel
      TwoRouteState.source TwoRouteState.target)
    (h : C ∈ twoRouteDisplayedRecursiveCarrierFamily) :
    causalBefore (P := twoRouteProcess)
      ⟨TwoRouteState.source⟩ ⟨TwoRouteState.target⟩ :=
  twoRouteEndpointIndexedRecursiveCarrierFamily.member_causal_before C h

def TwoRouteDisplayedRecursiveCarrierFamilyComplete : Prop :=
  twoRouteUpperRecursiveKernelCarrier ∈ twoRouteDisplayedRecursiveCarrierFamily
    ∧ twoRouteLowerRecursiveKernelCarrier ∈ twoRouteDisplayedRecursiveCarrierFamily
    ∧ (∀ C : DisplayedKernelPathCarrier twoRouteKernel
          TwoRouteState.source TwoRouteState.target,
        C ∈ twoRouteDisplayedRecursiveCarrierFamily ->
          C = twoRouteUpperRecursiveKernelCarrier
            ∨ C = twoRouteLowerRecursiveKernelCarrier)
    ∧ (∀ C : DisplayedKernelPathCarrier twoRouteKernel
          TwoRouteState.source TwoRouteState.target,
        C ∈ twoRouteDisplayedRecursiveCarrierFamily ->
          C.weight = 1)

theorem two_route_displayed_recursive_carrier_family_complete :
    TwoRouteDisplayedRecursiveCarrierFamilyComplete :=
  ⟨ two_route_upper_recursive_carrier_mem_family
  , two_route_lower_recursive_carrier_mem_family
  , two_route_displayed_recursive_family_member_cases
  , two_route_displayed_recursive_family_member_weight_one
  ⟩

/-! ## § 2 Remaining physical ledger -/

inductive PendingBeyondS32 where
  | arbitraryEndpointCompleteness
  | allKernelPathEnumeration
  | globalPathEnumeration
  | arbitraryLengthCausalIntervals
  | fullCausalSetAxioms
  | globalLocalFiniteness
  | generalPathIntegral
  | lorentzianGeometry
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS32 (_b : PendingBeyondS32) : Bool :=
  false

theorem pending_boundary_not_closed_by_s32
    (b : PendingBeyondS32) :
    ClosedByStepwiseS32 b = false := by
  cases b <;> rfl

/-! ## § 3 Public summary -/

theorem two_route_displayed_carrier_completeness_bridge_summary :
    TwoRouteDisplayedRecursiveCarrierFamilyComplete
    ∧ EndpointIndexedRecursiveCarrierFamilyClosed
    ∧ TwoRouteEndpointIndexedRecursiveFamilyClosed
    ∧ twoRouteDisplayedRecursiveCarrierFamily =
      [twoRouteUpperRecursiveKernelCarrier,
        twoRouteLowerRecursiveKernelCarrier]
    ∧ (∀ C : DisplayedKernelPathCarrier twoRouteKernel
          TwoRouteState.source TwoRouteState.target,
        C ∈ twoRouteDisplayedRecursiveCarrierFamily ->
          C.weight = 1)
    ∧ (∀ b : PendingBeyondS32, ClosedByStepwiseS32 b = false)
    ∧ WenConstructiveCoverage := by
  rcases endpoint_indexed_recursive_carrier_bridge_summary with
    ⟨hEndpoint, hTwoRoute, _hRecursive, _hAppend, _hFamily,
      _hCarriers, _hWeights, _hWeightSum, _hPendingS31, hCoverage⟩
  exact
    ⟨ two_route_displayed_recursive_carrier_family_complete
    , hEndpoint
    , hTwoRoute
    , two_route_displayed_recursive_family_eq
    , two_route_displayed_recursive_family_member_weight_one
    , pending_boundary_not_closed_by_s32
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge
