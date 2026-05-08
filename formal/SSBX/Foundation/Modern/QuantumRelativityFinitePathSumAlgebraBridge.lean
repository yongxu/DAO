/-
# QuantumRelativityFinitePathSumAlgebraBridge -- finite path-sum algebra candidate

Companion:
`义理/有限路径族求和代数候选 · Markov桥S5g.md`

This module advances S5f by one conservative algebraic step:

1. it appends finite same-endpoint two-step path families;
2. it reverses finite path families without changing their amplitude sum;
3. it proves permutation stability for finite path-family sums;
4. it shows that the two-route cancellation remains stable under reversal and
   under appending two already-cancelled finite families.

This is only finite list algebra over candidate path amplitudes.  It is not an
all-path enumeration, not a path integral, not a continuous action principle,
not a Born-rule derivation, not a unitary/CPTP law, not decoherence, and not
empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFinitePathSumAlgebraBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
open SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite family algebra -/

/--
Append two finite path families with the same endpoint ledger.

The endpoint equalities are explicit so that this operation remains a finite
same-endpoint operation, not an unconstrained union of unrelated paths.
-/
def appendFiniteTwoStepPathFamilies {P : FiniteProcess}
    (F G : FiniteTwoStepPathFamily P)
    (hStart : G.endpointStart = F.endpointStart)
    (hStop : G.endpointStop = F.endpointStop) :
    FiniteTwoStepPathFamily P where
  paths := F.paths ++ G.paths
  endpointStart := F.endpointStart
  endpointStop := F.endpointStop
  same_start := by
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact F.same_start p hp
    · rw [G.same_start p hp, hStart]
  same_stop := by
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact F.same_stop p hp
    · rw [G.same_stop p hp, hStop]

/-- Reverse a finite path family while preserving its endpoint ledger. -/
def reverseFiniteTwoStepPathFamily {P : FiniteProcess}
    (F : FiniteTwoStepPathFamily P) :
    FiniteTwoStepPathFamily P where
  paths := F.paths.reverse
  endpointStart := F.endpointStart
  endpointStop := F.endpointStop
  same_start := by
    intro p hp
    apply F.same_start
    simpa using hp
  same_stop := by
    intro p hp
    apply F.same_stop
    simpa using hp

/-! ## § 2 Algebraic laws for finite path-family sums -/

/-- Finite path-family sums distribute over endpoint-compatible append. -/
theorem finite_path_family_amplitude_sum_append {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F G : FiniteTwoStepPathFamily P)
    (hStart : G.endpointStart = F.endpointStart)
    (hStop : G.endpointStop = F.endpointStop) :
    finitePathFamilyAmplitudeSum A
      (appendFiniteTwoStepPathFamilies F G hStart hStop) =
        finitePathFamilyAmplitudeSum A F
          + finitePathFamilyAmplitudeSum A G := by
  simp [finitePathFamilyAmplitudeSum, appendFiniteTwoStepPathFamilies,
    List.map_append, List.sum_append]

/-- Born-shaped append boundary for finite path-family sums. -/
theorem finite_path_family_born_weight_append_boundary {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F G : FiniteTwoStepPathFamily P)
    (hStart : G.endpointStart = F.endpointStart)
    (hStop : G.endpointStop = F.endpointStop) :
    finitePathFamilyBornWeight A
      (appendFiniteTwoStepPathFamilies F G hStart hStop) =
        ampProb
          (finitePathFamilyAmplitudeSum A F
            + finitePathFamilyAmplitudeSum A G) := by
  rw [finitePathFamilyBornWeight,
    finite_path_family_amplitude_sum_append]

/-- Finite path-family sums are invariant under list permutation. -/
theorem finite_path_family_amplitude_sum_perm {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F G : FiniteTwoStepPathFamily P)
    (h : F.paths.Perm G.paths) :
    finitePathFamilyAmplitudeSum A F =
      finitePathFamilyAmplitudeSum A G := by
  unfold finitePathFamilyAmplitudeSum
  exact (h.map fun p => A.twoStepAmplitude p).sum_eq

/-- Born-shaped finite-family weights are invariant under list permutation. -/
theorem finite_path_family_born_weight_perm {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F G : FiniteTwoStepPathFamily P)
    (h : F.paths.Perm G.paths) :
    finitePathFamilyBornWeight A F =
      finitePathFamilyBornWeight A G := by
  rw [finitePathFamilyBornWeight, finitePathFamilyBornWeight,
    finite_path_family_amplitude_sum_perm A F G h]

/-- Reversing a finite path family preserves its amplitude sum. -/
theorem finite_path_family_amplitude_sum_reverse {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F : FiniteTwoStepPathFamily P) :
    finitePathFamilyAmplitudeSum A (reverseFiniteTwoStepPathFamily F) =
      finitePathFamilyAmplitudeSum A F := by
  exact finite_path_family_amplitude_sum_perm A
    (reverseFiniteTwoStepPathFamily F) F (List.reverse_perm F.paths)

/-- Reversing a finite path family preserves its Born-shaped weight. -/
theorem finite_path_family_born_weight_reverse {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F : FiniteTwoStepPathFamily P) :
    finitePathFamilyBornWeight A (reverseFiniteTwoStepPathFamily F) =
      finitePathFamilyBornWeight A F := by
  rw [finitePathFamilyBornWeight, finitePathFamilyBornWeight,
    finite_path_family_amplitude_sum_reverse A F]

/-- If two endpoint-compatible finite families both cancel, their append cancels. -/
theorem finite_path_family_append_cancels_of_canceling_summands
    {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F G : FiniteTwoStepPathFamily P)
    (hStart : G.endpointStart = F.endpointStart)
    (hStop : G.endpointStop = F.endpointStop)
    (hF : finitePathFamilyAmplitudeSum A F = 0)
    (hG : finitePathFamilyAmplitudeSum A G = 0) :
    finitePathFamilyAmplitudeSum A
      (appendFiniteTwoStepPathFamilies F G hStart hStop) = 0 := by
  rw [finite_path_family_amplitude_sum_append A F G hStart hStop,
    hF, hG]
  simp

/-! ## § 3 Two-route algebra witnesses -/

/-- The two-route upper/lower finite family in reversed order. -/
def twoRouteLowerUpperFamily :
    FiniteTwoStepPathFamily twoRouteProcess :=
  reverseFiniteTwoStepPathFamily twoRouteUpperLowerFamily

/-- The two-route family and its reversed family are list permutations. -/
theorem two_route_reversed_family_paths_perm :
    twoRouteUpperLowerFamily.paths.Perm
      twoRouteLowerUpperFamily.paths := by
  exact (List.reverse_perm twoRouteUpperLowerFamily.paths).symm

/-- Reversing the two-route family preserves cancellation. -/
theorem two_route_reversed_family_amplitude_cancels :
    finitePathFamilyAmplitudeSum
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteLowerUpperFamily = 0 := by
  simpa [twoRouteLowerUpperFamily] using
    (finite_path_family_amplitude_sum_reverse
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteUpperLowerFamily).trans
        two_route_finite_family_amplitude_cancels

/-- The reversed cancelled family has Born-shaped weight zero. -/
theorem two_route_reversed_family_born_weight_zero :
    finitePathFamilyBornWeight
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteLowerUpperFamily = 0 := by
  rw [finitePathFamilyBornWeight,
    two_route_reversed_family_amplitude_cancels]
  simp [ampProb]

/-- Append two already-cancelled two-route finite families. -/
def twoRouteDoubleCancelingFamily :
    FiniteTwoStepPathFamily twoRouteProcess :=
  appendFiniteTwoStepPathFamilies
    twoRouteUpperLowerFamily twoRouteLowerUpperFamily rfl rfl

/-- Appending the two cancelled two-route families still cancels. -/
theorem two_route_double_family_amplitude_cancels :
    finitePathFamilyAmplitudeSum
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteDoubleCancelingFamily = 0 := by
  exact finite_path_family_append_cancels_of_canceling_summands
    (edgePhaseInducedTwoStepAmplitudeCandidate
      twoRouteDiscreteActionCandidate)
    twoRouteUpperLowerFamily twoRouteLowerUpperFamily rfl rfl
    two_route_finite_family_amplitude_cancels
    two_route_reversed_family_amplitude_cancels

/-- The appended cancelled two-route family has Born-shaped weight zero. -/
theorem two_route_double_family_born_weight_zero :
    finitePathFamilyBornWeight
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteDoubleCancelingFamily = 0 := by
  rw [finitePathFamilyBornWeight,
    two_route_double_family_amplitude_cancels]
  simp [ampProb]

/-! ## § 4 Public summary -/

/-- Public summary for S5g:
    finite path-family sums now have append, reverse, and permutation stability,
    and the two-route cancellation remains stable under reversing and appending
    cancelled finite families.  This proves only finite list algebra for
    candidate amplitudes, not all-path enumeration, path integral, continuous
    action law, Born-rule derivation, unitary/CPTP dynamics, decoherence, or
    empirical closure. -/
theorem finite_path_sum_algebra_bridge_summary :
    (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (F G : FiniteTwoStepPathFamily P)
        (hStart : G.endpointStart = F.endpointStart)
        (hStop : G.endpointStop = F.endpointStop),
        finitePathFamilyAmplitudeSum A
          (appendFiniteTwoStepPathFamilies F G hStart hStop) =
            finitePathFamilyAmplitudeSum A F
              + finitePathFamilyAmplitudeSum A G)
    ∧ (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (F G : FiniteTwoStepPathFamily P)
        (_h : F.paths.Perm G.paths),
        finitePathFamilyAmplitudeSum A F =
          finitePathFamilyAmplitudeSum A G)
    ∧ (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (F : FiniteTwoStepPathFamily P),
        finitePathFamilyAmplitudeSum A (reverseFiniteTwoStepPathFamily F) =
          finitePathFamilyAmplitudeSum A F)
    ∧ twoRouteUpperLowerFamily.paths.Perm
        twoRouteLowerUpperFamily.paths
    ∧ finitePathFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteLowerUpperFamily = 0
    ∧ finitePathFamilyBornWeight
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteLowerUpperFamily = 0
    ∧ finitePathFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteDoubleCancelingFamily = 0
    ∧ finitePathFamilyBornWeight
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteDoubleCancelingFamily = 0
    ∧ WenConstructiveCoverage := by
  rcases finite_path_sum_bridge_summary with
    ⟨_hFamily, _hEdge, _hStart, _hStop, _hPathsStart, _hPathsStop,
      _hPairEq, _hCancel, _hBornZero, _hInterference, _hBornBoundary,
      hCoverage⟩
  exact
    ⟨ finite_path_family_amplitude_sum_append
    , finite_path_family_amplitude_sum_perm
    , finite_path_family_amplitude_sum_reverse
    , two_route_reversed_family_paths_perm
    , two_route_reversed_family_amplitude_cancels
    , two_route_reversed_family_born_weight_zero
    , two_route_double_family_amplitude_cancels
    , two_route_double_family_born_weight_zero
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityFinitePathSumAlgebraBridge
