/-
# QuantumRelativityCanonicalRepresentativeBridge -- toy canonical representatives

Companion:
`义理/规范代表元候选 · Markov桥S5n.md`

This module advances S5m by adding the smallest canonical representative
boundary for the two-route toy quotient classes:

1. it defines what it means for a witness to represent a quotient class;
2. it proves the displayed upper/lower paths represent their own classes;
3. it proves every toy source/target two-step path has one of those displayed
   representatives at quotient-class level.

This is only a toy finite representative boundary.  It is not a general
choice function, not proof-field path equality, not general all-path
enumeration, not a path integral, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge

namespace SSBX.Foundation.Modern.QuantumRelativityCanonicalRepresentativeBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge
open SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Canonical representative predicate -/

/-- A witness represents a quotient class when its class is that quotient. -/
def CanonicalRepresentativeFor {P : FiniteProcess}
    (q : TwoStepPathKeyQuotient P)
    (r : TwoStepPathWitness P) : Prop :=
  twoStepPathQuotientClass r = q

/-- The displayed upper path represents its own quotient class. -/
theorem two_route_upper_canonical_represents :
    CanonicalRepresentativeFor
      (twoStepPathQuotientClass twoRouteUpperPath)
      twoRouteUpperPath := by
  rfl

/-- The displayed lower path represents its own quotient class. -/
theorem two_route_lower_canonical_represents :
    CanonicalRepresentativeFor
      (twoStepPathQuotientClass twoRouteLowerPath)
      twoRouteLowerPath := by
  rfl

/-! ## § 2 Two-route representative completeness -/

/--
Every toy source/target two-step path has either the displayed upper or lower
path as a canonical representative of its quotient class.
-/
theorem two_route_source_target_has_canonical_representative
    (p : TwoStepPathWitness twoRouteProcess)
    (hStart : p.start = TwoRouteState.source)
    (hStop : p.stop = TwoRouteState.target) :
    ∃ r : TwoStepPathWitness twoRouteProcess,
      (r = twoRouteUpperPath ∨ r = twoRouteLowerPath)
        ∧ CanonicalRepresentativeFor (twoStepPathQuotientClass p) r := by
  rcases two_route_source_target_middle_upper_or_lower p hStart hStop with
    hUpper | hLower
  · refine ⟨twoRouteUpperPath, Or.inl rfl, ?_⟩
    exact (two_route_source_target_upper_middle_quotient_class
      p hStart hUpper hStop).symm
  · refine ⟨twoRouteLowerPath, Or.inr rfl, ?_⟩
    exact (two_route_source_target_lower_middle_quotient_class
      p hStart hLower hStop).symm

/-- Public predicate for source/target representative completeness. -/
def TwoRouteSourceTargetCanonicalRepresentativeComplete : Prop :=
  ∀ p : TwoStepPathWitness twoRouteProcess,
    p.start = TwoRouteState.source ->
      p.stop = TwoRouteState.target ->
        ∃ r : TwoStepPathWitness twoRouteProcess,
          (r = twoRouteUpperPath ∨ r = twoRouteLowerPath)
            ∧ CanonicalRepresentativeFor (twoStepPathQuotientClass p) r

theorem two_route_source_target_canonical_representative_complete :
    TwoRouteSourceTargetCanonicalRepresentativeComplete := by
  intro p hStart hStop
  exact two_route_source_target_has_canonical_representative p hStart hStop

/-! ## § 3 Public summary -/

/-- Public summary for S5n:
    the two-route toy quotient classes have displayed canonical
    representatives, and every toy source/target two-step path is represented
    by either the displayed upper or lower path at quotient-class level.  This
    proves only a finite toy representative boundary, not a general choice
    function, proof-field path equality, general all-path enumeration, path
    integral, or empirical closure. -/
theorem canonical_representative_bridge_summary :
    CanonicalRepresentativeFor
      (twoStepPathQuotientClass twoRouteUpperPath)
      twoRouteUpperPath
    ∧ CanonicalRepresentativeFor
      (twoStepPathQuotientClass twoRouteLowerPath)
      twoRouteLowerPath
    ∧ TwoRouteSourceTargetCanonicalRepresentativeComplete
    ∧ TwoRouteSourceTargetQuotientComplete
    ∧ WenConstructiveCoverage := by
  rcases path_quotient_bridge_summary with
    ⟨_hClass, _hKey, _hAmp, _hDistinct, hQuotientComplete,
      _hBorn, hCoverage⟩
  exact
    ⟨ two_route_upper_canonical_represents
    , two_route_lower_canonical_represents
    , two_route_source_target_canonical_representative_complete
    , hQuotientComplete
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityCanonicalRepresentativeBridge
