/-
# QuantumRelativityFinitePathSumBridge -- finite path-family sum candidate

Companion:
`义理/有限路径族求和候选 · Markov桥S5f.md`

This module advances S5e by one conservative step:

1. it defines a finite same-endpoint family of two-step path witnesses;
2. it defines a finite amplitude sum over that family;
3. it shows that the two-route upper/lower pair is an instance of this finite
   family interface;
4. it proves that the finite-family sum agrees with the S5c/S5e two-path sum
   and still cancels with Born-shaped zero weight.

This is only a finite path-family sum candidate.  It is not a general path
integral, not a measure over paths, not a continuous action principle, not a
Born-rule derivation, not a unitary/CPTP law, not decoherence, and not empirical
closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite same-endpoint path families -/

/--
A finite family of two-step path witnesses with a shared endpoint pair.

The carrier is a plain list, so this is only a finite-sum interface.  It is not
an all-paths space, a measure, or a path integral.
-/
structure FiniteTwoStepPathFamily (P : FiniteProcess) where
  paths : List (TwoStepPathWitness P)
  endpointStart : P.State
  endpointStop : P.State
  same_start :
    ∀ p : TwoStepPathWitness P, p ∈ paths -> p.start = endpointStart
  same_stop :
    ∀ p : TwoStepPathWitness P, p ∈ paths -> p.stop = endpointStop

/-- A process has a finite same-endpoint path family when one is given. -/
def HasFiniteTwoStepPathFamily (P : FiniteProcess) : Prop :=
  Nonempty (FiniteTwoStepPathFamily P)

/-- Finite amplitude sum over a same-endpoint path family. -/
def finitePathFamilyAmplitudeSum {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F : FiniteTwoStepPathFamily P) : ℂ :=
  (F.paths.map fun p => A.twoStepAmplitude p).sum

/-- Born-shaped candidate weight attached to a finite path-family sum. -/
def finitePathFamilyBornWeight {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F : FiniteTwoStepPathFamily P) : ℝ :=
  ampProb (finitePathFamilyAmplitudeSum A F)

theorem finite_path_family_born_boundary {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F : FiniteTwoStepPathFamily P) :
    finitePathFamilyBornWeight A F =
      ampProb (finitePathFamilyAmplitudeSum A F) := by
  rfl

/-! ## § 2 Two-route finite-family witness -/

/-- The S5c/S5e upper/lower pair as a finite same-endpoint family. -/
def twoRouteUpperLowerFamily :
    FiniteTwoStepPathFamily twoRouteProcess where
  paths := [twoRouteUpperPath, twoRouteLowerPath]
  endpointStart := TwoRouteState.source
  endpointStop := TwoRouteState.target
  same_start := by
    intro p hp
    simp at hp
    rcases hp with hp | hp
    · cases hp
      rfl
    · cases hp
      rfl
  same_stop := by
    intro p hp
    simp at hp
    rcases hp with hp | hp
    · cases hp
      rfl
    · cases hp
      rfl

/-- The two-route finite family has the expected endpoints. -/
theorem two_route_family_endpoints :
    twoRouteUpperLowerFamily.endpointStart = TwoRouteState.source
      ∧ twoRouteUpperLowerFamily.endpointStop = TwoRouteState.target :=
  ⟨rfl, rfl⟩

/-- Every path in the two-route finite family has the shared endpoints. -/
theorem two_route_family_paths_share_endpoints :
    (∀ p : TwoStepPathWitness twoRouteProcess,
        p ∈ twoRouteUpperLowerFamily.paths ->
          p.start = TwoRouteState.source)
    ∧ (∀ p : TwoStepPathWitness twoRouteProcess,
        p ∈ twoRouteUpperLowerFamily.paths ->
          p.stop = TwoRouteState.target) :=
  ⟨twoRouteUpperLowerFamily.same_start,
   twoRouteUpperLowerFamily.same_stop⟩

/--
The two-route finite-family amplitude sum is exactly the earlier two-path pair
sum for the edge-action-induced amplitude candidate.
-/
theorem two_route_family_sum_eq_pair_sum :
    finitePathFamilyAmplitudeSum
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteUpperLowerFamily =
        twoStepPairAmplitudeSum
          (edgePhaseInducedTwoStepAmplitudeCandidate
            twoRouteDiscreteActionCandidate)
          twoRouteUpperLowerPair := by
  simp [finitePathFamilyAmplitudeSum, twoStepPairAmplitudeSum,
    twoRouteUpperLowerFamily, twoRouteUpperLowerPair]

/-- The two-route finite-family amplitude sum cancels. -/
theorem two_route_finite_family_amplitude_cancels :
    finitePathFamilyAmplitudeSum
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteUpperLowerFamily = 0 := by
  rw [two_route_family_sum_eq_pair_sum]
  exact two_route_edge_action_pair_amplitude_cancels

/-- The cancelled finite-family sum has Born-shaped weight zero. -/
theorem two_route_finite_family_born_weight_zero :
    finitePathFamilyBornWeight
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteUpperLowerFamily = 0 := by
  rw [finitePathFamilyBornWeight,
    two_route_finite_family_amplitude_cancels]
  simp [ampProb]

/-! ## § 3 Public summary -/

/-- Public summary for S5f:
    the upper/lower two-route witness is now a finite same-endpoint path family;
    its finite amplitude sum agrees with the earlier two-path pair sum and
    cancels with Born-shaped zero weight.  This proves only a finite
    path-family sum candidate, not a path integral, measure over paths,
    continuous action law, Born-rule derivation, unitary/CPTP dynamics,
    decoherence, or empirical closure. -/
theorem finite_path_sum_bridge_summary :
    HasFiniteTwoStepPathFamily twoRouteProcess
    ∧ HasTwoStepEdgePhaseCandidate twoRouteProcess
    ∧ twoRouteUpperLowerFamily.endpointStart = TwoRouteState.source
    ∧ twoRouteUpperLowerFamily.endpointStop = TwoRouteState.target
    ∧ (∀ p : TwoStepPathWitness twoRouteProcess,
        p ∈ twoRouteUpperLowerFamily.paths ->
          p.start = TwoRouteState.source)
    ∧ (∀ p : TwoStepPathWitness twoRouteProcess,
        p ∈ twoRouteUpperLowerFamily.paths ->
          p.stop = TwoRouteState.target)
    ∧ finitePathFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteUpperLowerFamily =
          twoStepPairAmplitudeSum
            (edgePhaseInducedTwoStepAmplitudeCandidate
              twoRouteDiscreteActionCandidate)
            twoRouteUpperLowerPair
    ∧ finitePathFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteUpperLowerFamily = 0
    ∧ finitePathFamilyBornWeight
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteUpperLowerFamily = 0
    ∧ HasInterferenceCandidate
    ∧ (∀ z : ℂ, (bornRuleCandidate z).candidateWeight = ampProb z)
    ∧ WenConstructiveCoverage := by
  rcases discrete_action_phase_bridge_summary with
    ⟨_hEdge, _hPhase, _hTwoStepAmp, _hUpperPhase, _hLowerPhase,
      _hRelative, _hUpperAmp, _hLowerAmp, _hPairCancel, _hBornZero,
      _hPair, hInterference, hBornBoundary, hCoverage⟩
  rcases two_route_family_endpoints with ⟨hStart, hStop⟩
  rcases two_route_family_paths_share_endpoints with
    ⟨hPathsStart, hPathsStop⟩
  exact
    ⟨ ⟨twoRouteUpperLowerFamily⟩
    , ⟨twoRouteDiscreteActionCandidate⟩
    , hStart
    , hStop
    , hPathsStart
    , hPathsStop
    , two_route_family_sum_eq_pair_sum
    , two_route_finite_family_amplitude_cancels
    , two_route_finite_family_born_weight_zero
    , hInterference
    , hBornBoundary
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge
