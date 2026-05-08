/-
# QuantumRelativityFiniteKeyQuotientBridge -- finite visible-key quotient candidate

Companion:
`义理/有限键商候选 · Markov桥S5l.md`

This module advances S5k by adding a conservative finite quotient candidate:

1. it treats equality of visible two-step path keys as the candidate quotient
   relation;
2. it records the compatibility condition needed for amplitudes to descend to
   visible keys;
3. it proves finite key-list sum and duplicate compensation boundaries;
4. it proves the two-route displayed key sum still cancels with Born-shaped
   zero boundary.

This is only a finite visible-key quotient candidate.  It is not a quotient
type construction, not proof-field path equality, not a general all-path
enumeration, not a path integral, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
open SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge
open SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge
open SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge
open SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Visible-key equivalence -/

/--
Candidate quotient relation for two-step witnesses: two witnesses are
equivalent when their visible `(start, middle, stop)` keys agree.
-/
def TwoStepPathKeyEquivalent {P : FiniteProcess}
    (p q : TwoStepPathWitness P) : Prop :=
  twoStepPathKey p = twoStepPathKey q

theorem two_step_path_key_equiv_refl {P : FiniteProcess}
    (p : TwoStepPathWitness P) :
    TwoStepPathKeyEquivalent p p := by
  rfl

theorem two_step_path_key_equiv_symm {P : FiniteProcess}
    {p q : TwoStepPathWitness P} :
    TwoStepPathKeyEquivalent p q ->
      TwoStepPathKeyEquivalent q p := by
  intro h
  exact h.symm

theorem two_step_path_key_equiv_trans {P : FiniteProcess}
    {p q r : TwoStepPathWitness P} :
    TwoStepPathKeyEquivalent p q ->
      TwoStepPathKeyEquivalent q r ->
        TwoStepPathKeyEquivalent p r := by
  intro hpq hqr
  exact hpq.trans hqr

/-! ## § 2 Key-level amplitude candidates -/

/-- A candidate amplitude assigned directly to visible two-step path keys. -/
structure TwoStepKeyAmplitudeCandidate (P : FiniteProcess) where
  channel : QuantumChannelSkeleton P
  keyAmplitude : TwoStepPathKey P -> ℂ
  candidateWeight : TwoStepPathKey P -> ℝ
  born_boundary :
    ∀ k : TwoStepPathKey P, candidateWeight k = ampProb (keyAmplitude k)

/--
A path amplitude factors through visible keys when it is equal to a
key-amplitude after applying `twoStepPathKey`.
-/
def PathAmplitudeFactorsThroughKey {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (K : TwoStepKeyAmplitudeCandidate P) : Prop :=
  ∀ p : TwoStepPathWitness P,
    A.twoStepAmplitude p = K.keyAmplitude (twoStepPathKey p)

/-- Key-compatible amplitudes are constant on visible-key equivalence classes. -/
theorem key_equivalent_paths_amplitude_eq {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (K : TwoStepKeyAmplitudeCandidate P)
    (hFactor : PathAmplitudeFactorsThroughKey A K)
    {p q : TwoStepPathWitness P}
    (hKey : TwoStepPathKeyEquivalent p q) :
    A.twoStepAmplitude p = A.twoStepAmplitude q := by
  rw [hFactor p, hFactor q, hKey]

/-! ## § 3 Finite key-list sums -/

/-- Extract the visible-key list from an endpoint-indexed finite path family. -/
def endpointIndexedKeyList {P : FiniteProcess}
    (E : EndpointIndexedTwoStepPathFamily P) : List (TwoStepPathKey P) :=
  E.paths.map fun p => twoStepPathKey p.path

/-- Finite amplitude sum over visible keys. -/
def twoStepKeyAmplitudeSum {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (keys : List (TwoStepPathKey P)) : ℂ :=
  (keys.map fun k => K.keyAmplitude k).sum

/-- Born-shaped candidate weight for a finite visible-key sum. -/
def twoStepKeyBornWeight {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (keys : List (TwoStepPathKey P)) : ℝ :=
  ampProb (twoStepKeyAmplitudeSum K keys)

/-- Duplicate a finite visible-key list. -/
def duplicateTwoStepPathKeyList {P : FiniteProcess}
    (keys : List (TwoStepPathKey P)) : List (TwoStepPathKey P) :=
  keys ++ keys

/-- List-level helper for key-factorized endpoint path sums. -/
theorem endpoint_key_sum_eq_path_sum_of_factor_list
    {P : FiniteProcess}
    {e : EndpointPair P}
    (A : TwoStepPathAmplitudeCandidate P)
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs : List (EndpointTwoStepPath P e))
    (hFactor : PathAmplitudeFactorsThroughKey A K) :
    (xs.map fun p => K.keyAmplitude (twoStepPathKey p.path)).sum =
      (xs.map fun p => A.twoStepAmplitude p.path).sum := by
  induction xs with
  | nil =>
      simp
  | cons p ps ih =>
      simp [hFactor p.path, ih]

/--
If a path amplitude factors through visible keys, the endpoint-indexed path sum
matches the corresponding key-list sum.
-/
theorem endpoint_indexed_key_sum_eq_path_sum_of_factor
    {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (K : TwoStepKeyAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P)
    (hFactor : PathAmplitudeFactorsThroughKey A K) :
    twoStepKeyAmplitudeSum K (endpointIndexedKeyList E) =
      endpointIndexedFamilyAmplitudeSum A E := by
  simpa [twoStepKeyAmplitudeSum, endpointIndexedKeyList,
    endpointIndexedFamilyAmplitudeSum] using
      endpoint_key_sum_eq_path_sum_of_factor_list A K E.paths hFactor

/-- Finite key sums distribute over append. -/
theorem two_step_key_amplitude_sum_append {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs ys : List (TwoStepPathKey P)) :
    twoStepKeyAmplitudeSum K (xs ++ ys) =
      twoStepKeyAmplitudeSum K xs + twoStepKeyAmplitudeSum K ys := by
  simp [twoStepKeyAmplitudeSum, List.map_append, List.sum_append]

/-- Duplicating a key list doubles its key-amplitude sum. -/
theorem two_step_key_amplitude_sum_duplicate {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (keys : List (TwoStepPathKey P)) :
    twoStepKeyAmplitudeSum K (duplicateTwoStepPathKeyList keys) =
      twoStepKeyAmplitudeSum K keys + twoStepKeyAmplitudeSum K keys := by
  exact two_step_key_amplitude_sum_append K keys keys

/-- Duplicating a zero-sum key list preserves cancellation. -/
theorem two_step_key_duplicate_cancels_of_canceling
    {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (keys : List (TwoStepPathKey P))
    (h : twoStepKeyAmplitudeSum K keys = 0) :
    twoStepKeyAmplitudeSum K (duplicateTwoStepPathKeyList keys) = 0 := by
  rw [two_step_key_amplitude_sum_duplicate K keys, h]
  simp

/-- Duplicating a zero-sum key list has Born-shaped weight zero. -/
theorem two_step_key_duplicate_born_weight_zero_of_canceling
    {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (keys : List (TwoStepPathKey P))
    (h : twoStepKeyAmplitudeSum K keys = 0) :
    twoStepKeyBornWeight K (duplicateTwoStepPathKeyList keys) = 0 := by
  rw [twoStepKeyBornWeight,
    two_step_key_duplicate_cancels_of_canceling K keys h]
  simp [ampProb]

/-! ## § 4 Two-route visible-key quotient candidate -/

/-- Displayed two-route key amplitude: upper key has `1`, lower key has `-1`. -/
def twoRouteDisplayedKeyAmplitude
    (k : TwoStepPathKey twoRouteProcess) : ℂ :=
  match k.start, k.middle, k.stop with
  | TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target => 1
  | TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target => -1
  | _, _, _ => 0

/-- The displayed two-route key-amplitude candidate. -/
def twoRouteKeyAmplitudeCandidate :
    TwoStepKeyAmplitudeCandidate twoRouteProcess where
  channel := twoRouteQuantumChannelSkeleton
  keyAmplitude := twoRouteDisplayedKeyAmplitude
  candidateWeight := fun k => ampProb (twoRouteDisplayedKeyAmplitude k)
  born_boundary := by
    intro k
    rfl

/-- The upper displayed route key has candidate amplitude `1`. -/
theorem two_route_upper_key_amplitude :
    twoRouteKeyAmplitudeCandidate.keyAmplitude
      (twoStepPathKey twoRouteUpperPath) = 1 := by
  rfl

/-- The lower displayed route key has candidate amplitude `-1`. -/
theorem two_route_lower_key_amplitude :
    twoRouteKeyAmplitudeCandidate.keyAmplitude
      (twoStepPathKey twoRouteLowerPath) = -1 := by
  rfl

/-- The endpoint-indexed two-route family has exactly the displayed key list. -/
theorem two_route_endpoint_indexed_key_list_eq :
    endpointIndexedKeyList twoRouteEndpointIndexedFamily =
      twoRouteSourceTargetKeyEnumeration := by
  simp [endpointIndexedKeyList, twoRouteEndpointIndexedFamily,
    endpointIndexedFamilyOfFinitePathFamily, twoRouteUpperLowerFamily,
    twoRouteSourceTargetKeyEnumeration]

/-- The displayed two-route key-amplitude sum cancels. -/
theorem two_route_key_amplitude_sum_cancels :
    twoStepKeyAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetKeyEnumeration = 0 := by
  simp [twoStepKeyAmplitudeSum, twoRouteSourceTargetKeyEnumeration,
    two_route_upper_key_amplitude, two_route_lower_key_amplitude]

/-- The displayed cancelling key sum has Born-shaped weight zero. -/
theorem two_route_key_born_weight_zero :
    twoStepKeyBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetKeyEnumeration = 0 := by
  rw [twoStepKeyBornWeight, two_route_key_amplitude_sum_cancels]
  simp [ampProb]

/-- Duplicating the displayed cancelling key list still has zero key sum. -/
theorem two_route_duplicated_key_amplitude_sum_cancels :
    twoStepKeyAmplitudeSum twoRouteKeyAmplitudeCandidate
      (duplicateTwoStepPathKeyList twoRouteSourceTargetKeyEnumeration) = 0 := by
  exact two_step_key_duplicate_cancels_of_canceling
    twoRouteKeyAmplitudeCandidate
    twoRouteSourceTargetKeyEnumeration
    two_route_key_amplitude_sum_cancels

/-- Duplicating the displayed cancelling key list has Born-shaped weight zero. -/
theorem two_route_duplicated_key_born_weight_zero :
    twoStepKeyBornWeight twoRouteKeyAmplitudeCandidate
      (duplicateTwoStepPathKeyList twoRouteSourceTargetKeyEnumeration) = 0 := by
  exact two_step_key_duplicate_born_weight_zero_of_canceling
    twoRouteKeyAmplitudeCandidate
    twoRouteSourceTargetKeyEnumeration
    two_route_key_amplitude_sum_cancels

/-! ## § 5 Public summary -/

/-- Public summary for S5l:
    visible-key equality is an equivalence candidate; key-compatible amplitudes
    are constant on that relation; finite key sums have duplicate compensation;
    and the two-route displayed key sum cancels with Born-shaped zero boundary.
    This proves only a finite visible-key quotient candidate, not a quotient
    type construction, proof-field path equality, general all-path enumeration,
    path integral, or empirical closure. -/
theorem finite_key_quotient_bridge_summary :
    (∀ {P : FiniteProcess} (p : TwoStepPathWitness P),
      TwoStepPathKeyEquivalent p p)
    ∧ (∀ {P : FiniteProcess} {p q : TwoStepPathWitness P},
      TwoStepPathKeyEquivalent p q -> TwoStepPathKeyEquivalent q p)
    ∧ (∀ {P : FiniteProcess} {p q r : TwoStepPathWitness P},
      TwoStepPathKeyEquivalent p q ->
        TwoStepPathKeyEquivalent q r ->
          TwoStepPathKeyEquivalent p r)
    ∧ (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (K : TwoStepKeyAmplitudeCandidate P)
        (_hFactor : PathAmplitudeFactorsThroughKey A K)
        {p q : TwoStepPathWitness P},
        TwoStepPathKeyEquivalent p q ->
          A.twoStepAmplitude p = A.twoStepAmplitude q)
    ∧ (∀ {P : FiniteProcess}
        (K : TwoStepKeyAmplitudeCandidate P)
        (keys : List (TwoStepPathKey P)),
        twoStepKeyAmplitudeSum K (duplicateTwoStepPathKeyList keys) =
          twoStepKeyAmplitudeSum K keys + twoStepKeyAmplitudeSum K keys)
    ∧ endpointIndexedKeyList twoRouteEndpointIndexedFamily =
      twoRouteSourceTargetKeyEnumeration
    ∧ twoStepKeyAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetKeyEnumeration = 0
    ∧ twoStepKeyBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetKeyEnumeration = 0
    ∧ twoStepKeyBornWeight twoRouteKeyAmplitudeCandidate
      (duplicateTwoStepPathKeyList twoRouteSourceTargetKeyEnumeration) = 0
    ∧ TwoRouteSourceTargetKeyComplete
    ∧ WenConstructiveCoverage := by
  rcases path_identity_bridge_summary with
    ⟨_hStart, _hMiddle, _hStop, _hKeysDistinct, hKeyComplete,
      _hMiddleComplete, hCoverage⟩
  exact
    ⟨ two_step_path_key_equiv_refl
    , fun h => two_step_path_key_equiv_symm h
    , fun hpq hqr => two_step_path_key_equiv_trans hpq hqr
    , key_equivalent_paths_amplitude_eq
    , two_step_key_amplitude_sum_duplicate
    , two_route_endpoint_indexed_key_list_eq
    , two_route_key_amplitude_sum_cancels
    , two_route_key_born_weight_zero
    , two_route_duplicated_key_born_weight_zero
    , hKeyComplete
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
