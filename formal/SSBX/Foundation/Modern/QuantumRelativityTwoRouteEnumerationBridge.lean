/-
# QuantumRelativityTwoRouteEnumerationBridge -- two-route source/target enumeration

Companion:
`义理/双路径枚举候选 · Markov桥S5j.md`

This module advances S5i by proving a deliberately small enumeration theorem
for the toy two-route process:

1. the endpoint-indexed two-route family has center list `[upper, lower]`;
2. any two-step witness from `source` to `target` in `twoRouteProcess` has
   center state `upper` or `lower`;
3. therefore every source/target two-step witness has its center listed by the
   endpoint-indexed family.

This is only a finite enumeration theorem for the toy two-step process.  It is
not an all-process path enumeration, not a general path integral, not a
continuous action law, not a Born-rule derivation, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge

namespace SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
open SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge
open SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge
open SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Endpoint-indexed center lists -/

/-- Extract the center-state list from an endpoint-indexed two-step family. -/
def endpointIndexedMiddleList {P : FiniteProcess}
    (E : EndpointIndexedTwoStepPathFamily P) : List P.State :=
  E.paths.map fun p => p.path.center

/-- The displayed source/target middles in the two-route toy process. -/
def twoRouteSourceTargetMiddleEnumeration : List TwoRouteState :=
  [TwoRouteState.upper, TwoRouteState.lower]

/-- The S5h endpoint-indexed two-route family has center list `[upper, lower]`. -/
theorem two_route_endpoint_indexed_middle_list_eq :
    endpointIndexedMiddleList twoRouteEndpointIndexedFamily =
      twoRouteSourceTargetMiddleEnumeration := by
  simp [endpointIndexedMiddleList, twoRouteEndpointIndexedFamily,
    endpointIndexedFamilyOfFinitePathFamily, twoRouteUpperLowerFamily,
    twoRouteUpperPath, twoRouteLowerPath,
    twoRouteSourceTargetMiddleEnumeration]
  rfl

/-! ## § 2 Toy source/target two-step enumeration -/

/--
Any two-step path in the toy two-route process from `source` to `target` has
center state `upper` or `lower`.
-/
theorem two_route_source_target_middle_upper_or_lower
    (p : TwoStepPathWitness twoRouteProcess)
    (hStart : p.start = TwoRouteState.source)
    (hStop : p.stop = TwoRouteState.target) :
    p.center = TwoRouteState.upper
      ∨ p.center = TwoRouteState.lower := by
  have hLeft : TwoRouteState.step TwoRouteState.source p.center := by
    simpa [twoRouteProcess, hStart] using p.leftStep
  have hRight : TwoRouteState.step p.center TwoRouteState.target := by
    simpa [twoRouteProcess, hStop] using p.rightStep
  cases hMiddle : p.center
  · exfalso
    simp [TwoRouteState.step, hMiddle] at hLeft
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    simp [TwoRouteState.step, hMiddle] at hLeft

/-- The center of any source/target two-step path appears in the displayed list. -/
theorem two_route_source_target_middle_mem_enumeration
    (p : TwoStepPathWitness twoRouteProcess)
    (hStart : p.start = TwoRouteState.source)
    (hStop : p.stop = TwoRouteState.target) :
    p.center ∈ twoRouteSourceTargetMiddleEnumeration := by
  rcases two_route_source_target_middle_upper_or_lower p hStart hStop with
    hUpper | hLower
  · rw [hUpper]
    decide
  · rw [hLower]
    decide

/--
The S5h endpoint-indexed two-route family is center-complete for source/target
two-step witnesses in the toy process.
-/
theorem two_route_source_target_middle_mem_endpoint_family
    (p : TwoStepPathWitness twoRouteProcess)
    (hStart : p.start = TwoRouteState.source)
    (hStop : p.stop = TwoRouteState.target) :
    p.center ∈ endpointIndexedMiddleList twoRouteEndpointIndexedFamily := by
  rw [two_route_endpoint_indexed_middle_list_eq]
  exact two_route_source_target_middle_mem_enumeration p hStart hStop

/-- The toy source/target two-step enumeration is complete at center-state level. -/
def TwoRouteSourceTargetMiddleComplete : Prop :=
  ∀ p : TwoStepPathWitness twoRouteProcess,
    p.start = TwoRouteState.source ->
      p.stop = TwoRouteState.target ->
        p.center ∈ endpointIndexedMiddleList twoRouteEndpointIndexedFamily

theorem two_route_source_target_middle_complete :
    TwoRouteSourceTargetMiddleComplete := by
  intro p hStart hStop
  exact two_route_source_target_middle_mem_endpoint_family p hStart hStop

/-! ## § 3 Public summary -/

/-- Public summary for S5j:
    in the toy two-route process, the endpoint-indexed source/target family
    lists exactly the two possible center states, and every source/target
    two-step witness has one of those middles.  This proves only toy finite
    two-step enumeration, not all-path enumeration for arbitrary processes, a
    path integral, continuous action law, Born-rule derivation, or empirical
    closure. -/
theorem two_route_enumeration_bridge_summary :
    endpointIndexedMiddleList twoRouteEndpointIndexedFamily =
      twoRouteSourceTargetMiddleEnumeration
    ∧ (∀ p : TwoStepPathWitness twoRouteProcess,
        p.start = TwoRouteState.source ->
          p.stop = TwoRouteState.target ->
            p.center = TwoRouteState.upper
              ∨ p.center = TwoRouteState.lower)
    ∧ TwoRouteSourceTargetMiddleComplete
    ∧ endpointIndexedFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteFilteredEndpointFamily = 0
    ∧ endpointIndexedFamilyBornWeight
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteDuplicatedEndpointFamily = 0
    ∧ WenConstructiveCoverage := by
  rcases endpoint_support_normalization_bridge_summary with
    ⟨_hFilterSum, _hFilterBorn, hFilteredCancel, _hFilteredBorn,
      _hDuplicateSum, _hDuplicatedCancel, hDuplicatedBorn, hCoverage⟩
  exact
    ⟨ two_route_endpoint_indexed_middle_list_eq
    , two_route_source_target_middle_upper_or_lower
    , two_route_source_target_middle_complete
    , hFilteredCancel
    , hDuplicatedBorn
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge
