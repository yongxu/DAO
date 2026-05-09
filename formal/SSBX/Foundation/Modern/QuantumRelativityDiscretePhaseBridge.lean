/-
# QuantumRelativityDiscretePhaseBridge -- discrete phase-label candidate

Companion:
`义理/离散相位标记候选 · Markov桥S5d.md`

This module advances S5c by one conservative step:

1. it adds a finite phase-label interface with two labels, `zero` and `pi`;
2. it maps those labels to candidate amplitudes `1` and `-1`;
3. it labels the two-route upper/lower paths with opposite phase labels;
4. it proves that the phase-induced finite two-path amplitude cancels.

This is only a discrete phase-label candidate.  It is not a Hamiltonian,
action functional, unitary evolution law, path integral, Born-rule derivation,
decoherence model, or empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge

namespace SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Discrete phase labels -/

/--
A minimal finite phase label.

`zero` and `pi` are only labels for the candidate amplitudes `1` and `-1`.
They are not a continuous phase group, an action functional, or a Hamiltonian
evolution law.
-/
inductive DiscretePhase : Type
  | zero
  | pi
  deriving Repr, DecidableEq

/-- Convert the two discrete phase labels into candidate complex amplitudes. -/
def discretePhaseAmplitude : DiscretePhase -> ℂ
  | .zero => 1
  | .pi => -1

/-- The two primitive phase labels induce opposite candidate amplitudes. -/
theorem discrete_phase_amplitudes_cancel :
    discretePhaseAmplitude DiscretePhase.zero
      + discretePhaseAmplitude DiscretePhase.pi = 0 := by
  norm_num [discretePhaseAmplitude]

/-- A two-step phase candidate assigns a discrete phase label to each witness. -/
structure TwoStepPhaseCandidate (P : FiniteProcess) where
  channel : QuantumChannelSkeleton P
  phaseOf : TwoStepPathWitness P -> DiscretePhase

namespace TwoStepPhaseCandidate

/-- The candidate amplitude induced by a discrete phase label. -/
def amplitude {P : FiniteProcess}
    (C : TwoStepPhaseCandidate P) (p : TwoStepPathWitness P) : ℂ :=
  discretePhaseAmplitude (C.phaseOf p)

end TwoStepPhaseCandidate

/-- A process has a two-step phase candidate when one is explicitly given. -/
def HasTwoStepPhaseCandidate (P : FiniteProcess) : Prop :=
  Nonempty (TwoStepPhaseCandidate P)

/-- Turn a phase-labeled two-step candidate into the S5c amplitude interface. -/
def phaseInducedTwoStepAmplitudeCandidate {P : FiniteProcess}
    (C : TwoStepPhaseCandidate P) :
    TwoStepPathAmplitudeCandidate P where
  channel := C.channel
  twoStepAmplitude := C.amplitude
  candidateWeight := fun p => ampProb (C.amplitude p)
  born_boundary := by
    intro p
    rfl

/-! ## § 2 Two-route phase labels -/

/-- The two-route phase label: upper has `zero`, lower has `pi`. -/
def twoRoutePhaseOf
    (p : TwoStepPathWitness twoRouteProcess) : DiscretePhase :=
  if p.middle = TwoRouteState.upper then DiscretePhase.zero
  else if p.middle = TwoRouteState.lower then DiscretePhase.pi
  else DiscretePhase.zero

/-- Discrete phase candidate for the two-route toy process. -/
def twoRoutePhaseCandidate :
    TwoStepPhaseCandidate twoRouteProcess where
  channel := twoRouteQuantumChannelSkeleton
  phaseOf := twoRoutePhaseOf

/-- The upper path carries the `zero` phase label. -/
theorem two_route_upper_phase :
    twoRoutePhaseCandidate.phaseOf twoRouteUpperPath = DiscretePhase.zero := by
  simp [twoRoutePhaseCandidate, twoRoutePhaseOf, twoRouteUpperPath]

/-- The lower path carries the `pi` phase label. -/
theorem two_route_lower_phase :
    twoRoutePhaseCandidate.phaseOf twoRouteLowerPath = DiscretePhase.pi := by
  simp [twoRoutePhaseCandidate, twoRoutePhaseOf, twoRouteLowerPath]

/-- The upper phase label induces candidate amplitude `1`. -/
theorem two_route_upper_phase_amplitude :
    twoRoutePhaseCandidate.amplitude twoRouteUpperPath = 1 := by
  simp [TwoStepPhaseCandidate.amplitude, discretePhaseAmplitude,
    two_route_upper_phase]

/-- The lower phase label induces candidate amplitude `-1`. -/
theorem two_route_lower_phase_amplitude :
    twoRoutePhaseCandidate.amplitude twoRouteLowerPath = -1 := by
  simp [TwoStepPhaseCandidate.amplitude, discretePhaseAmplitude,
    two_route_lower_phase]

/-- The phase-induced S5c amplitude candidate still gives upper amplitude `1`. -/
theorem two_route_phase_induced_upper_amplitude :
    (phaseInducedTwoStepAmplitudeCandidate
      twoRoutePhaseCandidate).twoStepAmplitude twoRouteUpperPath = 1 :=
  two_route_upper_phase_amplitude

/-- The phase-induced S5c amplitude candidate still gives lower amplitude `-1`. -/
theorem two_route_phase_induced_lower_amplitude :
    (phaseInducedTwoStepAmplitudeCandidate
      twoRoutePhaseCandidate).twoStepAmplitude twoRouteLowerPath = -1 :=
  two_route_lower_phase_amplitude

/-- The phase-induced finite two-path amplitude cancels. -/
theorem two_route_phase_pair_amplitude_cancels :
    twoStepPairAmplitudeSum
      (phaseInducedTwoStepAmplitudeCandidate twoRoutePhaseCandidate)
      twoRouteUpperLowerPair = 0 := by
  simp [twoStepPairAmplitudeSum, twoRouteUpperLowerPair,
    two_route_phase_induced_upper_amplitude,
    two_route_phase_induced_lower_amplitude]

/-- The phase-induced cancelled amplitude has Born-shaped weight zero. -/
theorem two_route_phase_cancelled_born_weight_zero :
    (bornRuleCandidate
      (twoStepPairAmplitudeSum
        (phaseInducedTwoStepAmplitudeCandidate twoRoutePhaseCandidate)
        twoRouteUpperLowerPair)).candidateWeight = 0 := by
  rw [two_route_phase_pair_amplitude_cancels]
  simp [bornRuleCandidate, ampProb]

/-! ## § 3 Public summary -/

/-- Public summary for S5d:
    the two-route cancellation can be generated from finite phase labels:
    upper carries `zero`, lower carries `pi`, the labels map to `1` and `-1`,
    and their finite two-path sum cancels with Born-shaped zero weight.  This
    proves only a discrete phase-label candidate, not a physical phase law,
    action principle, unitary/CPTP dynamics, path integral, decoherence, or
    empirical closure. -/
theorem discrete_phase_bridge_summary :
    HasTwoStepPhaseCandidate twoRouteProcess
    ∧ (discretePhaseAmplitude DiscretePhase.zero
        + discretePhaseAmplitude DiscretePhase.pi = 0)
    ∧ twoRoutePhaseCandidate.phaseOf twoRouteUpperPath = DiscretePhase.zero
    ∧ twoRoutePhaseCandidate.phaseOf twoRouteLowerPath = DiscretePhase.pi
    ∧ twoRoutePhaseCandidate.amplitude twoRouteUpperPath = 1
    ∧ twoRoutePhaseCandidate.amplitude twoRouteLowerPath = -1
    ∧ twoStepPairAmplitudeSum
        (phaseInducedTwoStepAmplitudeCandidate twoRoutePhaseCandidate)
        twoRouteUpperLowerPair = 0
    ∧ (bornRuleCandidate
        (twoStepPairAmplitudeSum
          (phaseInducedTwoStepAmplitudeCandidate twoRoutePhaseCandidate)
          twoRouteUpperLowerPair)).candidateWeight = 0
    ∧ HasSameEndpointTwoStepPair twoRouteProcess
    ∧ HasTwoStepPathAmplitudeCandidate twoRouteProcess
    ∧ HasInterferenceCandidate
    ∧ (∀ z : ℂ, (bornRuleCandidate z).candidateWeight = ampProb z)
    ∧ WenConstructiveCoverage := by
  rcases two_path_interference_bridge_summary with
    ⟨_hFiniteProb, _hChannel, _hPathAmp, hTwoStepAmp, hPair,
      _hEndpoints, _hMiddle, _hUpper, _hLower, _hCancel, _hBornZero,
      hInterference, hBornBoundary, hCoverage⟩
  exact
    ⟨ ⟨twoRoutePhaseCandidate⟩
    , discrete_phase_amplitudes_cancel
    , two_route_upper_phase
    , two_route_lower_phase
    , two_route_upper_phase_amplitude
    , two_route_lower_phase_amplitude
    , two_route_phase_pair_amplitude_cancels
    , two_route_phase_cancelled_born_weight_zero
    , hPair
    , hTwoStepAmp
    , hInterference
    , hBornBoundary
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
