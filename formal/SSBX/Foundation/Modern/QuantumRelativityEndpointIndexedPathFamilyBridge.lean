/-
# QuantumRelativityEndpointIndexedPathFamilyBridge -- endpoint-indexed finite path families

Companion:
`义理/端点索引路径族候选 · Markov桥S5h.md`

This module advances S5g by moving the same-endpoint ledger into an
endpoint-indexed finite path family:

1. it defines an endpoint pair for a finite process;
2. it defines two-step paths whose endpoints are part of their type-level
   family index;
3. it converts every S5f finite same-endpoint path family into an
   endpoint-indexed finite family;
4. it proves that this conversion preserves finite amplitude sums and
   Born-shaped weights;
5. it applies the conversion to the two-route cancellation witness.

This is only a finite endpoint-indexed enumeration boundary.  It does not
enumerate all paths, does not construct a path integral, does not provide a
continuous action principle, does not derive the Born rule, and does not close
unitary/CPTP dynamics, decoherence, or empirical validation.
-/
import SSBX.Foundation.Modern.QuantumRelativityFinitePathSumAlgebraBridge

namespace SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
open SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge
open SSBX.Foundation.Modern.QuantumRelativityFinitePathSumAlgebraBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Endpoint-indexed path families -/

/-- A pair of endpoints in a finite process. -/
structure EndpointPair (P : FiniteProcess) where
  start : P.State
  stop : P.State

/-- A two-step path whose outer endpoints are indexed by `e`. -/
structure EndpointTwoStepPath
    (P : FiniteProcess) (e : EndpointPair P) where
  path : TwoStepPathWitness P
  start_eq : path.start = e.start
  stop_eq : path.stop = e.stop

/-- A finite two-step path family indexed by a single endpoint pair. -/
structure EndpointIndexedTwoStepPathFamily
    (P : FiniteProcess) where
  endpoint : EndpointPair P
  paths : List (EndpointTwoStepPath P endpoint)

/-- A process has an endpoint-indexed finite family when one is given. -/
def HasEndpointIndexedTwoStepPathFamily (P : FiniteProcess) : Prop :=
  Nonempty (EndpointIndexedTwoStepPathFamily P)

/-- The endpoint pair carried by an S5f finite path family. -/
def endpointPairOfFinitePathFamily {P : FiniteProcess}
    (F : FiniteTwoStepPathFamily P) : EndpointPair P where
  start := F.endpointStart
  stop := F.endpointStop

/-- Convert an S5f finite family into an endpoint-indexed finite family. -/
def endpointIndexedFamilyOfFinitePathFamily {P : FiniteProcess}
    (F : FiniteTwoStepPathFamily P) :
    EndpointIndexedTwoStepPathFamily P where
  endpoint := endpointPairOfFinitePathFamily F
  paths := F.paths.attach.map fun p =>
    { path := p.val
      start_eq := F.same_start p.val p.property
      stop_eq := F.same_stop p.val p.property }

/-- Every S5f finite family gives an endpoint-indexed finite family. -/
theorem finite_family_has_endpoint_indexed_family {P : FiniteProcess}
    (F : FiniteTwoStepPathFamily P) :
    HasEndpointIndexedTwoStepPathFamily P :=
  ⟨endpointIndexedFamilyOfFinitePathFamily F⟩

/-! ## § 2 Endpoint-indexed finite sums -/

/-- Finite amplitude sum over an endpoint-indexed path family. -/
def endpointIndexedFamilyAmplitudeSum {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P) : ℂ :=
  (E.paths.map fun p => A.twoStepAmplitude p.path).sum

/-- Born-shaped candidate weight for an endpoint-indexed finite family. -/
def endpointIndexedFamilyBornWeight {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (E : EndpointIndexedTwoStepPathFamily P) : ℝ :=
  ampProb (endpointIndexedFamilyAmplitudeSum A E)

/--
Converting an S5f finite path family to an endpoint-indexed finite path family
preserves its finite amplitude sum.
-/
theorem endpoint_indexed_family_sum_of_finite_family {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F : FiniteTwoStepPathFamily P) :
    endpointIndexedFamilyAmplitudeSum A
      (endpointIndexedFamilyOfFinitePathFamily F) =
        finitePathFamilyAmplitudeSum A F := by
  simp [endpointIndexedFamilyAmplitudeSum,
    endpointIndexedFamilyOfFinitePathFamily,
    finitePathFamilyAmplitudeSum]

/--
Converting an S5f finite path family to an endpoint-indexed finite path family
preserves its Born-shaped candidate weight.
-/
theorem endpoint_indexed_family_born_weight_of_finite_family
    {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (F : FiniteTwoStepPathFamily P) :
    endpointIndexedFamilyBornWeight A
      (endpointIndexedFamilyOfFinitePathFamily F) =
        finitePathFamilyBornWeight A F := by
  rw [endpointIndexedFamilyBornWeight, finitePathFamilyBornWeight,
    endpoint_indexed_family_sum_of_finite_family]

/-! ## § 3 Two-route endpoint-indexed witness -/

/-- The two-route upper/lower finite family as endpoint-indexed data. -/
def twoRouteEndpointIndexedFamily :
    EndpointIndexedTwoStepPathFamily twoRouteProcess :=
  endpointIndexedFamilyOfFinitePathFamily twoRouteUpperLowerFamily

/-- The two-route endpoint index is the expected source/target pair. -/
theorem two_route_endpoint_index :
    twoRouteEndpointIndexedFamily.endpoint.start = TwoRouteState.source
      ∧ twoRouteEndpointIndexedFamily.endpoint.stop = TwoRouteState.target :=
  ⟨rfl, rfl⟩

/-- Endpoint-indexing preserves the two-route finite-family cancellation. -/
theorem two_route_endpoint_indexed_family_amplitude_cancels :
    endpointIndexedFamilyAmplitudeSum
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteEndpointIndexedFamily = 0 := by
  rw [twoRouteEndpointIndexedFamily,
    endpoint_indexed_family_sum_of_finite_family]
  exact two_route_finite_family_amplitude_cancels

/-- The endpoint-indexed two-route family has Born-shaped weight zero. -/
theorem two_route_endpoint_indexed_family_born_weight_zero :
    endpointIndexedFamilyBornWeight
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteEndpointIndexedFamily = 0 := by
  rw [endpointIndexedFamilyBornWeight,
    two_route_endpoint_indexed_family_amplitude_cancels]
  simp [ampProb]

/-! ## § 4 Public summary -/

/-- Public summary for S5h:
    same-endpoint finite path families can be converted into endpoint-indexed
    finite families without changing their candidate amplitude sum or
    Born-shaped weight.  The two-route cancellation survives this conversion.
    This proves only a finite endpoint-indexed enumeration boundary, not
    all-path enumeration, a path integral, continuous action law, Born-rule
    derivation, unitary/CPTP dynamics, decoherence, or empirical closure. -/
theorem endpoint_indexed_path_family_bridge_summary :
    (∀ {P : FiniteProcess} (_F : FiniteTwoStepPathFamily P),
      HasEndpointIndexedTwoStepPathFamily P)
    ∧ (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (F : FiniteTwoStepPathFamily P),
        endpointIndexedFamilyAmplitudeSum A
          (endpointIndexedFamilyOfFinitePathFamily F) =
            finitePathFamilyAmplitudeSum A F)
    ∧ (∀ {P : FiniteProcess}
        (A : TwoStepPathAmplitudeCandidate P)
        (F : FiniteTwoStepPathFamily P),
        endpointIndexedFamilyBornWeight A
          (endpointIndexedFamilyOfFinitePathFamily F) =
            finitePathFamilyBornWeight A F)
    ∧ twoRouteEndpointIndexedFamily.endpoint.start = TwoRouteState.source
    ∧ twoRouteEndpointIndexedFamily.endpoint.stop = TwoRouteState.target
    ∧ endpointIndexedFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteEndpointIndexedFamily = 0
    ∧ endpointIndexedFamilyBornWeight
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteEndpointIndexedFamily = 0
    ∧ WenConstructiveCoverage := by
  rcases finite_path_sum_algebra_bridge_summary with
    ⟨_hAppend, _hPerm, _hReverse, _hPathsPerm, _hRevCancel,
      _hRevBornZero, _hDoubleCancel, _hDoubleBornZero, hCoverage⟩
  rcases two_route_endpoint_index with ⟨hStart, hStop⟩
  exact
    ⟨ fun F => finite_family_has_endpoint_indexed_family F
    , endpoint_indexed_family_sum_of_finite_family
    , endpoint_indexed_family_born_weight_of_finite_family
    , hStart
    , hStop
    , two_route_endpoint_indexed_family_amplitude_cancels
    , two_route_endpoint_indexed_family_born_weight_zero
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge
