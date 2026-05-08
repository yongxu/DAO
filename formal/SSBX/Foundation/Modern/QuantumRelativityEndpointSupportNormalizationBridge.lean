/-
# QuantumRelativityEndpointSupportNormalizationBridge -- finite support normalization boundary

Companion:
`义理/端点支撑规范化候选 · Markov桥S5i.md`

This module advances S5h by adding a conservative finite support boundary for
endpoint-indexed path families:

1. it filters an endpoint-indexed finite family by a Boolean selector;
2. it proves that filtering preserves the candidate amplitude sum when every
   removed path has zero candidate amplitude;
3. it states the matching Born-shaped boundary;
4. it makes duplicate handling explicit: duplicating a finite family doubles
   the finite amplitude sum, and duplicated zero-sum families still cancel.

This is only finite list normalization over an already given endpoint-indexed
family.  It does not enumerate all paths, quotient paths by identity, construct
a path integral, derive the Born rule, close unitary/CPTP dynamics, or provide
empirical validation.
-/
import SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge

namespace SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
open SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite support filtering -/

/-- Filter an endpoint-indexed finite family while preserving its endpoint. -/
def filterEndpointIndexedTwoStepPathFamily {P : FiniteProcess}
    (E : EndpointIndexedTwoStepPathFamily P)
    (keep : EndpointTwoStepPath P E.endpoint -> Bool) :
    EndpointIndexedTwoStepPathFamily P where
  endpoint := E.endpoint
  paths := E.paths.filter keep

/--
A filter is amplitude-complete when every path it removes has zero candidate
amplitude.  This is a finite support condition, not an all-path enumeration.
-/
def EndpointFamilyFilterComplete {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P)
    (keep : EndpointTwoStepPath P E.endpoint -> Bool) : Prop :=
  ∀ p : EndpointTwoStepPath P E.endpoint,
    p ∈ E.paths -> keep p = false -> A.twoStepAmplitude p.path = 0

/-- List-level support lemma for endpoint-indexed path sums. -/
theorem endpoint_path_sum_filter_eq_of_removed_zero {P : FiniteProcess}
    {e : EndpointPair P}
    (A : TwoStepPathAmplitudeCandidate P)
    (xs : List (EndpointTwoStepPath P e))
    (keep : EndpointTwoStepPath P e -> Bool)
    (h :
      ∀ p : EndpointTwoStepPath P e,
        p ∈ xs -> keep p = false -> A.twoStepAmplitude p.path = 0) :
    ((xs.filter keep).map fun p => A.twoStepAmplitude p.path).sum =
      (xs.map fun p => A.twoStepAmplitude p.path).sum := by
  induction xs with
  | nil =>
      simp
  | cons p ps ih =>
      have htail :
          ∀ q : EndpointTwoStepPath P e,
            q ∈ ps -> keep q = false -> A.twoStepAmplitude q.path = 0 := by
        intro q hq hk
        exact h q (by simp [hq]) hk
      cases hkp : keep p
      · have hpzero : A.twoStepAmplitude p.path = 0 :=
          h p (by simp) hkp
        simp [List.filter, hkp, hpzero, ih htail]
      · simp [List.filter, hkp, ih htail]

/--
Filtering preserves the endpoint-indexed finite-family amplitude sum when the
removed paths have zero candidate amplitude.
-/
theorem endpoint_indexed_family_filter_sum_eq_of_removed_zero
    {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P)
    (keep : EndpointTwoStepPath P E.endpoint -> Bool)
    (h : EndpointFamilyFilterComplete A E keep) :
    endpointIndexedFamilyAmplitudeSum A
      (filterEndpointIndexedTwoStepPathFamily E keep) =
        endpointIndexedFamilyAmplitudeSum A E := by
  exact endpoint_path_sum_filter_eq_of_removed_zero A E.paths keep h

/--
Born-shaped weights are preserved by amplitude-complete finite support filters.
-/
theorem endpoint_indexed_family_filter_born_weight_eq_of_removed_zero
    {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P)
    (keep : EndpointTwoStepPath P E.endpoint -> Bool)
    (h : EndpointFamilyFilterComplete A E keep) :
    endpointIndexedFamilyBornWeight A
      (filterEndpointIndexedTwoStepPathFamily E keep) =
        endpointIndexedFamilyBornWeight A E := by
  rw [endpointIndexedFamilyBornWeight, endpointIndexedFamilyBornWeight,
    endpoint_indexed_family_filter_sum_eq_of_removed_zero A E keep h]

/-! ## § 2 Duplicate handling -/

/-- Duplicate a finite endpoint-indexed family by appending its path list to itself. -/
def duplicateEndpointIndexedTwoStepPathFamily {P : FiniteProcess}
    (E : EndpointIndexedTwoStepPathFamily P) :
    EndpointIndexedTwoStepPathFamily P where
  endpoint := E.endpoint
  paths := E.paths ++ E.paths

/-- Duplicating a finite endpoint-indexed family doubles its amplitude sum. -/
theorem endpoint_indexed_family_duplicate_sum
    {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P) :
    endpointIndexedFamilyAmplitudeSum A
      (duplicateEndpointIndexedTwoStepPathFamily E) =
        endpointIndexedFamilyAmplitudeSum A E
          + endpointIndexedFamilyAmplitudeSum A E := by
  simp [endpointIndexedFamilyAmplitudeSum,
    duplicateEndpointIndexedTwoStepPathFamily, List.map_append,
    List.sum_append]

/-- Duplicating a zero-sum endpoint-indexed family preserves cancellation. -/
theorem endpoint_indexed_family_duplicate_cancels_of_canceling
    {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P)
    (h : endpointIndexedFamilyAmplitudeSum A E = 0) :
    endpointIndexedFamilyAmplitudeSum A
      (duplicateEndpointIndexedTwoStepPathFamily E) = 0 := by
  rw [endpoint_indexed_family_duplicate_sum A E, h]
  simp

/-- Duplicating a zero-sum endpoint-indexed family has Born-shaped weight zero. -/
theorem endpoint_indexed_family_duplicate_born_weight_zero_of_canceling
    {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P)
    (h : endpointIndexedFamilyAmplitudeSum A E = 0) :
    endpointIndexedFamilyBornWeight A
      (duplicateEndpointIndexedTwoStepPathFamily E) = 0 := by
  rw [endpointIndexedFamilyBornWeight,
    endpoint_indexed_family_duplicate_cancels_of_canceling A E h]
  simp [ampProb]

/-! ## § 3 Two-route support-normalization witness -/

/-- The two-route finite filter keeps both displayed paths. -/
def twoRouteKeepDisplayedEndpointPath
    (_p : EndpointTwoStepPath twoRouteProcess
      twoRouteEndpointIndexedFamily.endpoint) : Bool :=
  true

/-- The two-route endpoint-indexed family after the displayed-path filter. -/
def twoRouteFilteredEndpointFamily :
    EndpointIndexedTwoStepPathFamily twoRouteProcess :=
  filterEndpointIndexedTwoStepPathFamily twoRouteEndpointIndexedFamily
    twoRouteKeepDisplayedEndpointPath

/-- The displayed-path filter is amplitude-complete for the two-route witness. -/
theorem two_route_displayed_filter_complete :
    EndpointFamilyFilterComplete
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteEndpointIndexedFamily
      twoRouteKeepDisplayedEndpointPath := by
  intro p _hp hkeep
  simp [twoRouteKeepDisplayedEndpointPath] at hkeep

/-- Filtering the displayed two-route paths preserves their cancellation. -/
theorem two_route_filtered_endpoint_family_amplitude_cancels :
    endpointIndexedFamilyAmplitudeSum
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteFilteredEndpointFamily = 0 := by
  rw [twoRouteFilteredEndpointFamily,
    endpoint_indexed_family_filter_sum_eq_of_removed_zero]
  · exact two_route_endpoint_indexed_family_amplitude_cancels
  · exact two_route_displayed_filter_complete

/-- The filtered two-route family has Born-shaped weight zero. -/
theorem two_route_filtered_endpoint_family_born_weight_zero :
    endpointIndexedFamilyBornWeight
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteFilteredEndpointFamily = 0 := by
  rw [endpointIndexedFamilyBornWeight,
    two_route_filtered_endpoint_family_amplitude_cancels]
  simp [ampProb]

/-- The duplicated two-route endpoint-indexed family. -/
def twoRouteDuplicatedEndpointFamily :
    EndpointIndexedTwoStepPathFamily twoRouteProcess :=
  duplicateEndpointIndexedTwoStepPathFamily twoRouteEndpointIndexedFamily

/-- Duplicating the cancelling two-route endpoint family still cancels. -/
theorem two_route_duplicated_endpoint_family_amplitude_cancels :
    endpointIndexedFamilyAmplitudeSum
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteDuplicatedEndpointFamily = 0 := by
  exact endpoint_indexed_family_duplicate_cancels_of_canceling
    (edgePhaseInducedTwoStepAmplitudeCandidate
      twoRouteDiscreteActionCandidate)
    twoRouteEndpointIndexedFamily
    two_route_endpoint_indexed_family_amplitude_cancels

/-- The duplicated cancelling two-route endpoint family has Born-shaped weight zero. -/
theorem two_route_duplicated_endpoint_family_born_weight_zero :
    endpointIndexedFamilyBornWeight
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteDuplicatedEndpointFamily = 0 := by
  exact endpoint_indexed_family_duplicate_born_weight_zero_of_canceling
    (edgePhaseInducedTwoStepAmplitudeCandidate
      twoRouteDiscreteActionCandidate)
    twoRouteEndpointIndexedFamily
    two_route_endpoint_indexed_family_amplitude_cancels

/-! ## § 4 Public summary -/

/-- Public summary for S5i:
    endpoint-indexed finite path families now admit an explicit finite support
    filter boundary and an explicit duplicate-handling boundary.  Filters
    preserve sums and Born-shaped weights when removed paths have zero
    candidate amplitude.  Duplicate expansion doubles sums, so duplicated
    zero-sum families still cancel.  This proves only finite normalization over
    given lists, not all-path enumeration, quotienting, a path integral,
    Born-rule derivation, unitary/CPTP dynamics, decoherence, or empirical
    closure. -/
theorem endpoint_support_normalization_bridge_summary :
    (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (E : EndpointIndexedTwoStepPathFamily P)
        (keep : EndpointTwoStepPath P E.endpoint -> Bool)
        (_h : EndpointFamilyFilterComplete A E keep),
        endpointIndexedFamilyAmplitudeSum A
          (filterEndpointIndexedTwoStepPathFamily E keep) =
            endpointIndexedFamilyAmplitudeSum A E)
    ∧ (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (E : EndpointIndexedTwoStepPathFamily P)
        (keep : EndpointTwoStepPath P E.endpoint -> Bool)
        (_h : EndpointFamilyFilterComplete A E keep),
        endpointIndexedFamilyBornWeight A
          (filterEndpointIndexedTwoStepPathFamily E keep) =
            endpointIndexedFamilyBornWeight A E)
    ∧ endpointIndexedFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteFilteredEndpointFamily = 0
    ∧ endpointIndexedFamilyBornWeight
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteFilteredEndpointFamily = 0
    ∧ (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (E : EndpointIndexedTwoStepPathFamily P),
        endpointIndexedFamilyAmplitudeSum A
          (duplicateEndpointIndexedTwoStepPathFamily E) =
            endpointIndexedFamilyAmplitudeSum A E
              + endpointIndexedFamilyAmplitudeSum A E)
    ∧ endpointIndexedFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteDuplicatedEndpointFamily = 0
    ∧ endpointIndexedFamilyBornWeight
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteDuplicatedEndpointFamily = 0
    ∧ WenConstructiveCoverage := by
  rcases endpoint_indexed_path_family_bridge_summary with
    ⟨_hExist, _hSum, _hBorn, _hStart, _hStop, _hCancel, _hBornZero,
      hCoverage⟩
  exact
    ⟨ endpoint_indexed_family_filter_sum_eq_of_removed_zero
    , endpoint_indexed_family_filter_born_weight_eq_of_removed_zero
    , two_route_filtered_endpoint_family_amplitude_cancels
    , two_route_filtered_endpoint_family_born_weight_zero
    , endpoint_indexed_family_duplicate_sum
    , two_route_duplicated_endpoint_family_amplitude_cancels
    , two_route_duplicated_endpoint_family_born_weight_zero
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge
