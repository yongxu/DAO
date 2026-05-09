/-
# QuantumRelativityTwoRouteKernelPathEnumerationBridge -- S33 two-route KernelPath enumeration

Companion:
`义理/双路径KernelPath枚举候选 · Markov桥S33.md`

S33 closes the first all-`KernelPath` enumeration boundary for the two-route toy
process.  The result is deliberately carrier-level: every recursive
`KernelPath` from `source` to `target` has points equal to the upper route or
the lower route.  We do not identify paths by proof-field equality.

This does not prove arbitrary finite-process path enumeration, a general path
integral, Lorentzian geometry, metric recovery, or empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge

namespace SSBX.Foundation.Modern.QuantumRelativityTwoRouteKernelPathEnumerationBridge

noncomputable section

open SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedRecursiveCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Positive-edge classification for the two-route kernel -/

theorem two_route_positive_edge_cases
    {a b : TwoRouteState} (e : KernelEdge twoRouteKernel a b) :
    (a = TwoRouteState.source ∧ b = TwoRouteState.upper)
      ∨ (a = TwoRouteState.source ∧ b = TwoRouteState.lower)
      ∨ (a = TwoRouteState.upper ∧ b = TwoRouteState.target)
      ∨ (a = TwoRouteState.lower ∧ b = TwoRouteState.target) := by
  have h := e.positive_weight
  cases a <;> cases b <;>
    simp [twoRouteKernel, twoRouteFiniteProbabilityKernel,
      TwoRouteState.weight] at h ⊢

theorem two_route_edge_to_target_from_middle
    {a : TwoRouteState} (e : KernelEdge twoRouteKernel a TwoRouteState.target) :
    a = TwoRouteState.upper ∨ a = TwoRouteState.lower := by
  rcases two_route_positive_edge_cases e with h | h | h | h
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · exact Or.inl h.left
  · exact Or.inr h.left

theorem two_route_edge_to_upper_from_source
    {a : TwoRouteState} (e : KernelEdge twoRouteKernel a TwoRouteState.upper) :
    a = TwoRouteState.source := by
  rcases two_route_positive_edge_cases e with h | h | h | h
  · exact h.left
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · rcases h with ⟨_ha, hb⟩
    cases hb

theorem two_route_edge_to_lower_from_source
    {a : TwoRouteState} (e : KernelEdge twoRouteKernel a TwoRouteState.lower) :
    a = TwoRouteState.source := by
  rcases two_route_positive_edge_cases e with h | h | h | h
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · exact h.left
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · rcases h with ⟨_ha, hb⟩
    cases hb

theorem two_route_no_positive_edge_to_source
    {a : TwoRouteState} :
    ¬ KernelEdge twoRouteKernel a TwoRouteState.source := by
  intro e
  rcases two_route_positive_edge_cases e with h | h | h | h
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · rcases h with ⟨_ha, hb⟩
    cases hb
  · rcases h with ⟨_ha, hb⟩
    cases hb

theorem two_route_no_positive_edge_from_target
    {b : TwoRouteState} :
    ¬ KernelEdge twoRouteKernel TwoRouteState.target b := by
  intro e
  rcases two_route_positive_edge_cases e with h | h | h | h
  · rcases h with ⟨ha, _hb⟩
    cases ha
  · rcases h with ⟨ha, _hb⟩
    cases ha
  · rcases h with ⟨ha, _hb⟩
    cases ha
  · rcases h with ⟨ha, _hb⟩
    cases ha

theorem two_route_kernel_edge_weight_one
    {a b : TwoRouteState} (e : KernelEdge twoRouteKernel a b) :
    KernelEdge.weight e = 1 := by
  have h := e.positive_weight
  cases a <;> cases b <;>
    simp [KernelEdge.weight, twoRouteKernel, twoRouteFiniteProbabilityKernel,
      TwoRouteState.weight] at h ⊢

/-! ## § 2 Source-started recursive carrier normal forms -/

theorem two_route_kernel_path_source_targets
    : (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.source) ->
    kernelPathTargets p = []
  | KernelPath.refl _ => by
      rfl
  | KernelPath.snoc _p e => by
      exact False.elim (two_route_no_positive_edge_to_source e)

theorem two_route_kernel_path_source_upper_targets
    : (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.upper) ->
    kernelPathTargets p = [TwoRouteState.upper]
  | KernelPath.snoc p e => by
      have hprev := two_route_edge_to_upper_from_source e
      cases hprev
      have hp := two_route_kernel_path_source_targets p
      rw [kernelPathTargets_snoc p e, hp]
      rfl

theorem two_route_kernel_path_source_lower_targets
    : (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.lower) ->
    kernelPathTargets p = [TwoRouteState.lower]
  | KernelPath.snoc p e => by
      have hprev := two_route_edge_to_lower_from_source e
      cases hprev
      have hp := two_route_kernel_path_source_targets p
      rw [kernelPathTargets_snoc p e, hp]
      rfl

theorem two_route_kernel_path_source_target_targets_cases
    : (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.target) ->
    kernelPathTargets p = [TwoRouteState.upper, TwoRouteState.target]
      ∨ kernelPathTargets p = [TwoRouteState.lower, TwoRouteState.target]
  | KernelPath.snoc p e => by
      rcases two_route_edge_to_target_from_middle e with hprev | hprev
      · cases hprev
        have hp := two_route_kernel_path_source_upper_targets p
        left
        rw [kernelPathTargets_snoc p e, hp]
        rfl
      · cases hprev
        have hp := two_route_kernel_path_source_lower_targets p
        right
        rw [kernelPathTargets_snoc p e, hp]
        rfl

theorem two_route_kernel_path_source_points
    (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.source) :
    kernelPathPoints p = [TwoRouteState.source] := by
  have hp := two_route_kernel_path_source_targets p
  change TwoRouteState.source :: kernelPathTargets p =
    [TwoRouteState.source]
  rw [hp]
  rfl

theorem two_route_kernel_path_source_upper_points
    (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.upper) :
    kernelPathPoints p =
      [TwoRouteState.source, TwoRouteState.upper] := by
  have hp := two_route_kernel_path_source_upper_targets p
  change TwoRouteState.source :: kernelPathTargets p =
    [TwoRouteState.source, TwoRouteState.upper]
  rw [hp]

theorem two_route_kernel_path_source_lower_points
    (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.lower) :
    kernelPathPoints p =
      [TwoRouteState.source, TwoRouteState.lower] := by
  have hp := two_route_kernel_path_source_lower_targets p
  change TwoRouteState.source :: kernelPathTargets p =
    [TwoRouteState.source, TwoRouteState.lower]
  rw [hp]

theorem two_route_kernel_path_source_target_points_cases
    (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.target) :
    kernelPathPoints p =
        [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      ∨ kernelPathPoints p =
        [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target] := by
  rcases two_route_kernel_path_source_target_targets_cases p with hp | hp
  · left
    change TwoRouteState.source :: kernelPathTargets p =
      [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
    rw [hp]
  · right
    change TwoRouteState.source :: kernelPathTargets p =
      [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
    rw [hp]

/-! ## § 3 Weight and displayed-family readback -/

theorem two_route_source_started_kernel_path_weight_one
    {b : TwoRouteState} :
    (p : KernelPath twoRouteKernel TwoRouteState.source b) ->
    KernelPath.weight p = 1
  | KernelPath.refl _ => by
      rfl
  | KernelPath.snoc p e => by
      have hp := two_route_source_started_kernel_path_weight_one p
      simp [KernelPath.weight, hp, two_route_kernel_edge_weight_one e]
termination_by p => sizeOf p
decreasing_by
  all_goals
    simp_wf

theorem two_route_kernel_path_source_target_weight_one
    (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.target) :
    KernelPath.weight p = 1 :=
  two_route_source_started_kernel_path_weight_one p

theorem two_route_kernel_path_source_target_matches_displayed_family
    (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.target) :
    (recursiveKernelPathCarrier p).carrier ∈
      twoRouteDisplayedRecursiveCarrierFamily.map
        (fun C => DisplayedKernelPathCarrier.carrier C) := by
  rcases two_route_kernel_path_source_target_points_cases p with hupper | hlower
  · simp [twoRouteDisplayedRecursiveCarrierFamily,
      twoRouteEndpointIndexedRecursiveCarrierFamily,
      twoRouteRecursiveKernelCarrierFamily,
      recursiveKernelPathCarrier, hupper,
      two_route_upper_recursive_kernel_carrier_points,
      two_route_lower_recursive_kernel_carrier_points]
  · simp [twoRouteDisplayedRecursiveCarrierFamily,
      twoRouteEndpointIndexedRecursiveCarrierFamily,
      twoRouteRecursiveKernelCarrierFamily,
      recursiveKernelPathCarrier, hlower,
      two_route_upper_recursive_kernel_carrier_points,
      two_route_lower_recursive_kernel_carrier_points]

def TwoRouteKernelPathEnumerationComplete : Prop :=
  (∀ p : KernelPath twoRouteKernel
        TwoRouteState.source TwoRouteState.target,
      kernelPathPoints p =
          [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
        ∨ kernelPathPoints p =
          [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target])
    ∧ (∀ p : KernelPath twoRouteKernel
        TwoRouteState.source TwoRouteState.target,
      KernelPath.weight p = 1)
    ∧ (∀ p : KernelPath twoRouteKernel
        TwoRouteState.source TwoRouteState.target,
      (recursiveKernelPathCarrier p).carrier ∈
        twoRouteDisplayedRecursiveCarrierFamily.map
          (fun C => DisplayedKernelPathCarrier.carrier C))

theorem two_route_kernel_path_enumeration_complete :
    TwoRouteKernelPathEnumerationComplete :=
  ⟨ two_route_kernel_path_source_target_points_cases
  , two_route_kernel_path_source_target_weight_one
  , two_route_kernel_path_source_target_matches_displayed_family
  ⟩

/-! ## § 4 Remaining physical ledger -/

inductive PendingBeyondS33 where
  | arbitraryEndpointCompleteness
  | arbitraryFiniteProcessEnumeration
  | globalPathEnumeration
  | arbitraryLengthCausalIntervals
  | fullCausalSetAxioms
  | globalLocalFiniteness
  | generalPathIntegral
  | lorentzianGeometry
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS33 (_b : PendingBeyondS33) : Bool :=
  false

theorem pending_boundary_not_closed_by_s33
    (b : PendingBeyondS33) :
    ClosedByStepwiseS33 b = false := by
  cases b <;> rfl

/-! ## § 5 Public summary -/

theorem two_route_kernel_path_enumeration_bridge_summary :
    TwoRouteKernelPathEnumerationComplete
    ∧ TwoRouteDisplayedRecursiveCarrierFamilyComplete
    ∧ EndpointIndexedRecursiveCarrierFamilyClosed
    ∧ TwoRouteEndpointIndexedRecursiveFamilyClosed
    ∧ (∀ p : KernelPath twoRouteKernel
          TwoRouteState.source TwoRouteState.target,
        KernelPath.weight p = 1)
    ∧ (∀ b : PendingBeyondS33, ClosedByStepwiseS33 b = false)
    ∧ WenConstructiveCoverage := by
  rcases two_route_displayed_carrier_completeness_bridge_summary with
    ⟨hDisplayed, hEndpoint, hTwoRoute, _hFamilyEq, _hWeight,
      _hPendingS32, hCoverage⟩
  exact
    ⟨ two_route_kernel_path_enumeration_complete
    , hDisplayed
    , hEndpoint
    , hTwoRoute
    , two_route_kernel_path_source_target_weight_one
    , pending_boundary_not_closed_by_s33
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityTwoRouteKernelPathEnumerationBridge
