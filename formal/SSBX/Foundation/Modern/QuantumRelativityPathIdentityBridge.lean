/-
# QuantumRelativityPathIdentityBridge -- finite two-step path identity keys

Companion:
`义理/路径身份键候选 · Markov桥S5k.md`

This module advances S5j by adding a conservative identity-key boundary for
two-step path witnesses:

1. it defines the finite two-step path key `(start, middle, stop)`;
2. it proves that key equality implies equality of the visible endpoints and
   middle state;
3. it proves that the two-route upper and lower displayed paths have distinct
   keys;
4. it proves that every toy source/target two-step witness has a key in the
   displayed two-route key enumeration.

This is only a finite identity-key boundary.  It is not a quotient
construction, not proof-field path equality, not a general path enumeration,
not a path integral, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge

namespace SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
open SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge
open SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Two-step path keys -/

/-- The visible identity key of a two-step path witness. -/
structure TwoStepPathKey (P : FiniteProcess) where
  start : P.State
  middle : P.State
  stop : P.State

/-- Forget proof fields and keep only visible two-step path identity data. -/
def twoStepPathKey {P : FiniteProcess}
    (p : TwoStepPathWitness P) : TwoStepPathKey P where
  start := p.start
  middle := p.middle
  stop := p.stop

/-- Key equality preserves the visible start state. -/
theorem two_step_path_key_eq_start {P : FiniteProcess}
    {p q : TwoStepPathWitness P}
    (h : twoStepPathKey p = twoStepPathKey q) :
    p.start = q.start := by
  have hs := congrArg TwoStepPathKey.start h
  simpa [twoStepPathKey] using hs

/-- Key equality preserves the visible middle state. -/
theorem two_step_path_key_eq_middle {P : FiniteProcess}
    {p q : TwoStepPathWitness P}
    (h : twoStepPathKey p = twoStepPathKey q) :
    p.middle = q.middle := by
  have hm := congrArg TwoStepPathKey.middle h
  simpa [twoStepPathKey] using hm

/-- Key equality preserves the visible stop state. -/
theorem two_step_path_key_eq_stop {P : FiniteProcess}
    {p q : TwoStepPathWitness P}
    (h : twoStepPathKey p = twoStepPathKey q) :
    p.stop = q.stop := by
  have ht := congrArg TwoStepPathKey.stop h
  simpa [twoStepPathKey] using ht

/-! ## § 2 Two-route key enumeration -/

/-- The displayed source/target route keys in the two-route toy process. -/
def twoRouteSourceTargetKeyEnumeration :
    List (TwoStepPathKey twoRouteProcess) :=
  [twoStepPathKey twoRouteUpperPath, twoStepPathKey twoRouteLowerPath]

/-- The upper and lower route keys are distinct. -/
theorem two_route_upper_lower_keys_distinct :
    twoStepPathKey twoRouteUpperPath ≠
      twoStepPathKey twoRouteLowerPath := by
  intro h
  have hm := two_step_path_key_eq_middle h
  exact two_route_paths_distinct_middle hm

/-- A source/target two-step path with upper middle has the upper displayed key. -/
theorem two_route_source_target_upper_middle_key
    (p : TwoStepPathWitness twoRouteProcess)
    (hStart : p.start = TwoRouteState.source)
    (hMiddle : p.middle = TwoRouteState.upper)
    (hStop : p.stop = TwoRouteState.target) :
    twoStepPathKey p = twoStepPathKey twoRouteUpperPath := by
  cases p
  simp [twoStepPathKey, twoRouteUpperPath] at hStart hMiddle hStop ⊢
  exact ⟨hStart, hMiddle, hStop⟩

/-- A source/target two-step path with lower middle has the lower displayed key. -/
theorem two_route_source_target_lower_middle_key
    (p : TwoStepPathWitness twoRouteProcess)
    (hStart : p.start = TwoRouteState.source)
    (hMiddle : p.middle = TwoRouteState.lower)
    (hStop : p.stop = TwoRouteState.target) :
    twoStepPathKey p = twoStepPathKey twoRouteLowerPath := by
  cases p
  simp [twoStepPathKey, twoRouteLowerPath] at hStart hMiddle hStop ⊢
  exact ⟨hStart, hMiddle, hStop⟩

/--
Every toy source/target two-step witness has a key in the displayed two-route
key enumeration.
-/
theorem two_route_source_target_key_mem_enumeration
    (p : TwoStepPathWitness twoRouteProcess)
    (hStart : p.start = TwoRouteState.source)
    (hStop : p.stop = TwoRouteState.target) :
    twoStepPathKey p ∈ twoRouteSourceTargetKeyEnumeration := by
  rcases two_route_source_target_middle_upper_or_lower p hStart hStop with
    hUpper | hLower
  · rw [two_route_source_target_upper_middle_key p hStart hUpper hStop]
    simp [twoRouteSourceTargetKeyEnumeration]
  · rw [two_route_source_target_lower_middle_key p hStart hLower hStop]
    simp [twoRouteSourceTargetKeyEnumeration]

/-- The two-route key enumeration is complete for toy source/target paths. -/
def TwoRouteSourceTargetKeyComplete : Prop :=
  ∀ p : TwoStepPathWitness twoRouteProcess,
    p.start = TwoRouteState.source ->
      p.stop = TwoRouteState.target ->
        twoStepPathKey p ∈ twoRouteSourceTargetKeyEnumeration

theorem two_route_source_target_key_complete :
    TwoRouteSourceTargetKeyComplete := by
  intro p hStart hStop
  exact two_route_source_target_key_mem_enumeration p hStart hStop

/-! ## § 3 Public summary -/

/-- Public summary for S5k:
    two-step path witnesses now have a visible `(start, middle, stop)` key.
    In the toy two-route process, upper and lower displayed route keys are
    distinct, and every source/target two-step witness has a key in the
    displayed key enumeration.  This proves only a finite identity-key
    boundary, not quotient construction, proof-field path equality, general
    all-path enumeration, path integral, or empirical closure. -/
theorem path_identity_bridge_summary :
    (∀ {P : FiniteProcess} {p q : TwoStepPathWitness P},
      twoStepPathKey p = twoStepPathKey q -> p.start = q.start)
    ∧ (∀ {P : FiniteProcess} {p q : TwoStepPathWitness P},
      twoStepPathKey p = twoStepPathKey q -> p.middle = q.middle)
    ∧ (∀ {P : FiniteProcess} {p q : TwoStepPathWitness P},
      twoStepPathKey p = twoStepPathKey q -> p.stop = q.stop)
    ∧ twoStepPathKey twoRouteUpperPath ≠
      twoStepPathKey twoRouteLowerPath
    ∧ TwoRouteSourceTargetKeyComplete
    ∧ TwoRouteSourceTargetMiddleComplete
    ∧ WenConstructiveCoverage := by
  rcases two_route_enumeration_bridge_summary with
    ⟨_hMiddleList, _hMiddleExhaustive, hMiddleComplete,
      _hFilteredCancel, _hDuplicatedBorn, hCoverage⟩
  exact
    ⟨ two_step_path_key_eq_start
    , two_step_path_key_eq_middle
    , two_step_path_key_eq_stop
    , two_route_upper_lower_keys_distinct
    , two_route_source_target_key_complete
    , hMiddleComplete
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
