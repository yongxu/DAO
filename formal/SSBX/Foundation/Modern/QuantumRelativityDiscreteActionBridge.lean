/-
# QuantumRelativityDiscreteActionBridge -- discrete edge-action phase candidate

Companion:
`义理/离散作用量相位候选 · Markov桥S5e.md`

This module advances S5d by one conservative step:

1. it adds a finite phase-composition operation on the existing `zero/pi`
   labels;
2. it assigns phase increments to individual supported edges;
3. it accumulates a two-step path phase from its two edge phases;
4. it proves that the two-route upper/lower paths acquire relative phase `pi`
   and still induce finite two-path cancellation.

This is only a discrete edge-action phase candidate.  It is not a continuous
phase group, action functional, Hamiltonian law, unitary/CPTP channel law, path
integral, Born-rule derivation, decoherence model, or empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge

namespace SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite phase composition -/

/--
Composition for the two finite phase labels.

This is the minimal `Z₂`-shaped table needed by the two-route toy witness.  It
is not a continuous phase group or a physical action law.
-/
def discretePhaseAdd : DiscretePhase -> DiscretePhase -> DiscretePhase
  | .zero, .zero => .zero
  | .zero, .pi => .pi
  | .pi, .zero => .pi
  | .pi, .pi => .zero

theorem discrete_phase_add_zero_zero :
    discretePhaseAdd DiscretePhase.zero DiscretePhase.zero =
      DiscretePhase.zero := rfl

theorem discrete_phase_add_zero_pi :
    discretePhaseAdd DiscretePhase.zero DiscretePhase.pi =
      DiscretePhase.pi := rfl

theorem discrete_phase_add_pi_zero :
    discretePhaseAdd DiscretePhase.pi DiscretePhase.zero =
      DiscretePhase.pi := rfl

theorem discrete_phase_add_pi_pi :
    discretePhaseAdd DiscretePhase.pi DiscretePhase.pi =
      DiscretePhase.zero := rfl

/-- In the two-label setting, relative phase is phase composition. -/
def discretePhaseRelative
    (base observed : DiscretePhase) : DiscretePhase :=
  discretePhaseAdd base observed

/-! ## § 2 Edge-action phase candidates -/

/--
A two-step edge-action candidate assigns a finite phase increment to each
supported edge.  The two-step path phase is then accumulated from the two edge
increments.
-/
structure TwoStepEdgePhaseCandidate (P : FiniteProcess) where
  channel : QuantumChannelSkeleton P
  edgePhase :
    (a b : P.State) -> P.step a b -> DiscretePhase

namespace TwoStepEdgePhaseCandidate

/-- Accumulate a two-step path phase from its left and right edge phases. -/
def pathPhase {P : FiniteProcess}
    (C : TwoStepEdgePhaseCandidate P)
    (p : TwoStepPathWitness P) : DiscretePhase :=
  discretePhaseAdd
    (C.edgePhase p.start p.middle p.leftStep)
    (C.edgePhase p.middle p.stop p.rightStep)

end TwoStepEdgePhaseCandidate

/-- A process has a two-step edge-action phase candidate when one is given. -/
def HasTwoStepEdgePhaseCandidate (P : FiniteProcess) : Prop :=
  Nonempty (TwoStepEdgePhaseCandidate P)

/-- Turn accumulated edge phases into the S5d two-step phase interface. -/
def edgePhaseInducedTwoStepPhaseCandidate {P : FiniteProcess}
    (C : TwoStepEdgePhaseCandidate P) :
    TwoStepPhaseCandidate P where
  channel := C.channel
  phaseOf := C.pathPhase

/-- Turn accumulated edge phases into the S5c two-step amplitude interface. -/
def edgePhaseInducedTwoStepAmplitudeCandidate {P : FiniteProcess}
    (C : TwoStepEdgePhaseCandidate P) :
    TwoStepPathAmplitudeCandidate P :=
  phaseInducedTwoStepAmplitudeCandidate
    (edgePhaseInducedTwoStepPhaseCandidate C)

/-! ## § 3 Two-route edge-action witness -/

/--
Edge phase increments for the two-route toy process.

The upper route has `zero + zero`; the lower route has `zero + pi`.
-/
def twoRouteEdgePhase
    (a b : twoRouteProcess.State)
    (_h : twoRouteProcess.step a b) : DiscretePhase :=
  match a, b with
  | TwoRouteState.source, TwoRouteState.upper => DiscretePhase.zero
  | TwoRouteState.upper, TwoRouteState.target => DiscretePhase.zero
  | TwoRouteState.source, TwoRouteState.lower => DiscretePhase.zero
  | TwoRouteState.lower, TwoRouteState.target => DiscretePhase.pi
  | _, _ => DiscretePhase.zero

/-- Discrete edge-action phase candidate for the two-route toy process. -/
def twoRouteDiscreteActionCandidate :
    TwoStepEdgePhaseCandidate twoRouteProcess where
  channel := twoRouteQuantumChannelSkeleton
  edgePhase := twoRouteEdgePhase

theorem two_route_upper_left_edge_phase :
    twoRouteDiscreteActionCandidate.edgePhase
      TwoRouteState.source TwoRouteState.upper True.intro =
        DiscretePhase.zero := by
  rfl

theorem two_route_upper_right_edge_phase :
    twoRouteDiscreteActionCandidate.edgePhase
      TwoRouteState.upper TwoRouteState.target True.intro =
        DiscretePhase.zero := by
  rfl

theorem two_route_lower_left_edge_phase :
    twoRouteDiscreteActionCandidate.edgePhase
      TwoRouteState.source TwoRouteState.lower True.intro =
        DiscretePhase.zero := by
  rfl

theorem two_route_lower_right_edge_phase :
    twoRouteDiscreteActionCandidate.edgePhase
      TwoRouteState.lower TwoRouteState.target True.intro =
        DiscretePhase.pi := by
  rfl

/-- The upper route accumulates phase `zero`. -/
theorem two_route_upper_accumulated_phase :
    twoRouteDiscreteActionCandidate.pathPhase twoRouteUpperPath =
      DiscretePhase.zero := by
  rfl

/-- The lower route accumulates phase `pi`. -/
theorem two_route_lower_accumulated_phase :
    twoRouteDiscreteActionCandidate.pathPhase twoRouteLowerPath =
      DiscretePhase.pi := by
  rfl

/-- The lower path has relative phase `pi` against the upper path. -/
theorem two_route_edge_action_phase_difference :
    discretePhaseRelative
      (twoRouteDiscreteActionCandidate.pathPhase twoRouteUpperPath)
      (twoRouteDiscreteActionCandidate.pathPhase twoRouteLowerPath) =
        DiscretePhase.pi := by
  rfl

/-- Edge-action accumulation induces the S5d upper phase label. -/
theorem two_route_edge_action_upper_phase :
    (edgePhaseInducedTwoStepPhaseCandidate
      twoRouteDiscreteActionCandidate).phaseOf twoRouteUpperPath =
        DiscretePhase.zero :=
  two_route_upper_accumulated_phase

/-- Edge-action accumulation induces the S5d lower phase label. -/
theorem two_route_edge_action_lower_phase :
    (edgePhaseInducedTwoStepPhaseCandidate
      twoRouteDiscreteActionCandidate).phaseOf twoRouteLowerPath =
        DiscretePhase.pi :=
  two_route_lower_accumulated_phase

/-- The accumulated upper phase induces candidate amplitude `1`. -/
theorem two_route_edge_action_upper_amplitude :
    (edgePhaseInducedTwoStepPhaseCandidate
      twoRouteDiscreteActionCandidate).amplitude twoRouteUpperPath = 1 := by
  simp [TwoStepPhaseCandidate.amplitude, discretePhaseAmplitude,
    two_route_edge_action_upper_phase]

/-- The accumulated lower phase induces candidate amplitude `-1`. -/
theorem two_route_edge_action_lower_amplitude :
    (edgePhaseInducedTwoStepPhaseCandidate
      twoRouteDiscreteActionCandidate).amplitude twoRouteLowerPath = -1 := by
  simp [TwoStepPhaseCandidate.amplitude, discretePhaseAmplitude,
    two_route_edge_action_lower_phase]

/-- The edge-action-induced finite two-path amplitude cancels. -/
theorem two_route_edge_action_pair_amplitude_cancels :
    twoStepPairAmplitudeSum
      (edgePhaseInducedTwoStepAmplitudeCandidate
        twoRouteDiscreteActionCandidate)
      twoRouteUpperLowerPair = 0 := by
  simp [edgePhaseInducedTwoStepAmplitudeCandidate,
    phaseInducedTwoStepAmplitudeCandidate,
    twoStepPairAmplitudeSum, twoRouteUpperLowerPair,
    two_route_edge_action_upper_amplitude,
    two_route_edge_action_lower_amplitude]

/-- The edge-action-induced cancelled amplitude has Born-shaped weight zero. -/
theorem two_route_edge_action_cancelled_born_weight_zero :
    (bornRuleCandidate
      (twoStepPairAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteUpperLowerPair)).candidateWeight = 0 := by
  rw [two_route_edge_action_pair_amplitude_cancels]
  simp [bornRuleCandidate, ampProb]

/-! ## § 4 Public summary -/

/-- Public summary for S5e:
    the two-route phase labels can be accumulated from edge-action phase
    increments.  The upper path has accumulated phase `zero`, the lower path
    has accumulated phase `pi`, their relative phase is `pi`, and the induced
    finite two-path amplitude still cancels with Born-shaped zero weight.
    This proves only a discrete edge-action phase candidate, not a continuous
    action principle, Hamiltonian law, path integral, Born-rule derivation,
    unitary/CPTP dynamics, decoherence, or empirical closure. -/
theorem discrete_action_phase_bridge_summary :
    HasTwoStepEdgePhaseCandidate twoRouteProcess
    ∧ HasTwoStepPhaseCandidate twoRouteProcess
    ∧ HasTwoStepPathAmplitudeCandidate twoRouteProcess
    ∧ twoRouteDiscreteActionCandidate.pathPhase twoRouteUpperPath =
        DiscretePhase.zero
    ∧ twoRouteDiscreteActionCandidate.pathPhase twoRouteLowerPath =
        DiscretePhase.pi
    ∧ discretePhaseRelative
        (twoRouteDiscreteActionCandidate.pathPhase twoRouteUpperPath)
        (twoRouteDiscreteActionCandidate.pathPhase twoRouteLowerPath) =
          DiscretePhase.pi
    ∧ (edgePhaseInducedTwoStepPhaseCandidate
        twoRouteDiscreteActionCandidate).amplitude twoRouteUpperPath = 1
    ∧ (edgePhaseInducedTwoStepPhaseCandidate
        twoRouteDiscreteActionCandidate).amplitude twoRouteLowerPath = -1
    ∧ twoStepPairAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteUpperLowerPair = 0
    ∧ (bornRuleCandidate
        (twoStepPairAmplitudeSum
          (edgePhaseInducedTwoStepAmplitudeCandidate
            twoRouteDiscreteActionCandidate)
          twoRouteUpperLowerPair)).candidateWeight = 0
    ∧ HasSameEndpointTwoStepPair twoRouteProcess
    ∧ HasInterferenceCandidate
    ∧ (∀ z : ℂ, (bornRuleCandidate z).candidateWeight = ampProb z)
    ∧ WenConstructiveCoverage := by
  rcases discrete_phase_bridge_summary with
    ⟨_hPhase, _hPrimitiveCancel, _hUpperPhase, _hLowerPhase,
      _hUpperAmp, _hLowerAmp, _hPhaseCancel, _hPhaseBornZero,
      hPair, _hTwoStepAmp, hInterference, hBornBoundary, hCoverage⟩
  exact
    ⟨ ⟨twoRouteDiscreteActionCandidate⟩
    , ⟨edgePhaseInducedTwoStepPhaseCandidate twoRouteDiscreteActionCandidate⟩
    , ⟨edgePhaseInducedTwoStepAmplitudeCandidate twoRouteDiscreteActionCandidate⟩
    , two_route_upper_accumulated_phase
    , two_route_lower_accumulated_phase
    , two_route_edge_action_phase_difference
    , two_route_edge_action_upper_amplitude
    , two_route_edge_action_lower_amplitude
    , two_route_edge_action_pair_amplitude_cancels
    , two_route_edge_action_cancelled_born_weight_zero
    , hPair
    , hInterference
    , hBornBoundary
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
