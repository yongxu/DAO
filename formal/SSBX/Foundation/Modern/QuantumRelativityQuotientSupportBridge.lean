/-
# QuantumRelativityQuotientSupportBridge -- finite quotient support

Companion:
`义理/商支撑枚举候选 · Markov桥S5o.md`

This module advances S5n by treating the displayed two-route quotient classes
as a finite quotient-support list:

1. it defines finite sums over quotient classes;
2. it proves the displayed support covers every toy source/target quotient
   class;
3. it proves quotient support can be read back to visible keys;
4. it proves the two-route quotient-support amplitude sum cancels with a
   Born-shaped zero boundary.

This is only a toy finite quotient-support boundary.  It is not a general
choice function, not all-path enumeration, not a path integral, not a Born-rule
derivation, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityCanonicalRepresentativeBridge

namespace SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityCanonicalRepresentativeBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite quotient-support sums -/

/-- Finite amplitude sum over quotient classes. -/
def quotientSupportAmplitudeSum {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (qs : List (TwoStepPathKeyQuotient P)) : ℂ :=
  (qs.map fun q => quotientKeyAmplitude K q).sum

/-- Born-shaped candidate weight for a finite quotient-support sum. -/
def quotientSupportBornWeight {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (qs : List (TwoStepPathKeyQuotient P)) : ℝ :=
  ampProb (quotientSupportAmplitudeSum K qs)

/-- Read the visible keys carried by a finite quotient-support list. -/
def quotientSupportVisibleKeys {P : FiniteProcess}
    (qs : List (TwoStepPathKeyQuotient P)) : List (TwoStepPathKey P) :=
  qs.map quotientVisibleKey

theorem quotient_support_sum_eq_visible_key_sum {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (qs : List (TwoStepPathKeyQuotient P)) :
    quotientSupportAmplitudeSum K qs =
      twoStepKeyAmplitudeSum K (quotientSupportVisibleKeys qs) := by
  simp [quotientSupportAmplitudeSum, twoStepKeyAmplitudeSum,
    quotientSupportVisibleKeys, quotientKeyAmplitude, Function.comp_def]

/-! ## § 2 Two-route quotient support -/

/-- The displayed upper/lower paths used as support representatives. -/
def twoRouteQuotientSupportRepresentatives :
    List (TwoStepPathWitness twoRouteProcess) :=
  [twoRouteUpperPath, twoRouteLowerPath]

theorem two_route_quotient_support_representative_classes :
    (twoRouteQuotientSupportRepresentatives.map
      fun p => twoStepPathQuotientClass p) =
      twoRouteSourceTargetQuotientEnumeration := by
  rfl

/-- The displayed support is complete for toy source/target quotient classes. -/
def TwoRouteSourceTargetQuotientSupportComplete : Prop :=
  ∀ p : TwoStepPathWitness twoRouteProcess,
    p.start = TwoRouteState.source ->
      p.stop = TwoRouteState.target ->
        twoStepPathQuotientClass p ∈
          twoRouteSourceTargetQuotientEnumeration

theorem two_route_source_target_quotient_support_complete :
    TwoRouteSourceTargetQuotientSupportComplete := by
  exact two_route_source_target_quotient_complete

/-- The displayed quotient support reads back to the displayed visible-key list. -/
theorem two_route_quotient_support_visible_keys_eq :
    quotientSupportVisibleKeys twoRouteSourceTargetQuotientEnumeration =
      twoRouteSourceTargetKeyEnumeration := by
  rfl

theorem two_route_quotient_support_sum_eq_key_sum :
    quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration =
        twoStepKeyAmplitudeSum twoRouteKeyAmplitudeCandidate
          twoRouteSourceTargetKeyEnumeration := by
  rw [quotient_support_sum_eq_visible_key_sum,
    two_route_quotient_support_visible_keys_eq]

/-- The displayed quotient-support amplitude sum cancels. -/
theorem two_route_quotient_support_amplitude_sum_cancels :
    quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0 := by
  rw [two_route_quotient_support_sum_eq_key_sum]
  exact two_route_key_amplitude_sum_cancels

/-- The displayed cancelling quotient-support sum has Born-shaped weight zero. -/
theorem two_route_quotient_support_born_weight_zero :
    quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0 := by
  rw [quotientSupportBornWeight,
    two_route_quotient_support_amplitude_sum_cancels]
  simp [ampProb]

/-! ## § 3 Public summary -/

/-- Public summary for S5o:
    the two-route quotient classes are now a finite quotient-support list; the
    support covers every toy source/target quotient class, can be read back to
    the visible-key list, and carries the same cancelling finite sum with
    Born-shaped zero weight.  This proves only a finite toy support boundary,
    not a general choice function, all-path enumeration, path integral,
    Born-rule derivation, or empirical closure. -/
theorem quotient_support_bridge_summary :
    (twoRouteQuotientSupportRepresentatives.map
      fun p => twoStepPathQuotientClass p) =
        twoRouteSourceTargetQuotientEnumeration
    ∧ TwoRouteSourceTargetQuotientSupportComplete
    ∧ quotientSupportVisibleKeys twoRouteSourceTargetQuotientEnumeration =
      twoRouteSourceTargetKeyEnumeration
    ∧ quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ TwoRouteSourceTargetCanonicalRepresentativeComplete
    ∧ WenConstructiveCoverage := by
  rcases canonical_representative_bridge_summary with
    ⟨_hUpperRep, _hLowerRep, hRepresentativeComplete,
      _hQuotientComplete, hCoverage⟩
  exact
    ⟨ two_route_quotient_support_representative_classes
    , two_route_source_target_quotient_support_complete
    , two_route_quotient_support_visible_keys_eq
    , two_route_quotient_support_amplitude_sum_cancels
    , two_route_quotient_support_born_weight_zero
    , hRepresentativeComplete
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
