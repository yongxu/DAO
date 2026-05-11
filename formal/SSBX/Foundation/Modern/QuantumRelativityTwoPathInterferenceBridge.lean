/-
# QuantumRelativityTwoPathInterferenceBridge -- two-path cancellation candidate

Companion:
`义理/双路径相消候选 · Markov桥S5c.md`

This module advances S5b by one conservative step:

1. it adds a two-step path witness that keeps the center state visible;
2. it gives a four-state toy process with two alternative center states;
3. it assigns candidate two-step amplitudes `1` and `-1`;
4. it proves that their finite two-path sum cancels and that the cancelled
   amplitude has Born-shaped candidate weight zero.

This is only a two-path cancellation candidate.  It is not a path integral,
not a phase/action law, not a Born-rule derivation, not a unitary/CPTP channel
law, not decoherence, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge

namespace SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Two-step path witnesses -/

/--
A two-step path witness keeps the intermediate state.

The older `ProcessPath` only stores outer endpoints and a validity proposition,
so it cannot distinguish same-endpoint alternatives by their center state.
-/
structure TwoStepPathWitness (P : FiniteProcess) where
  start : P.State
  center : P.State
  stop : P.State
  leftStep : P.step start center
  rightStep : P.step center stop

namespace TwoStepPathWitness

/-- Forget the center state and return to the older endpoint-only path shape. -/
def toProcessPath {P : FiniteProcess} (p : TwoStepPathWitness P) :
    ProcessPath P where
  start := p.start
  stop := p.stop
  valid := P.step p.start p.center ∧ P.step p.center p.stop

/-- The forgotten endpoint-only path is valid. -/
theorem toProcessPath_valid {P : FiniteProcess}
    (p : TwoStepPathWitness P) :
    p.toProcessPath.valid :=
  ⟨p.leftStep, p.rightStep⟩

end TwoStepPathWitness

/-- Two two-step paths have the same outer endpoints but different middles. -/
structure SameEndpointTwoStepPair (P : FiniteProcess) where
  left : TwoStepPathWitness P
  right : TwoStepPathWitness P
  same_start : left.start = right.start
  same_stop : left.stop = right.stop
  distinct_middle : left.center ≠ right.center

/-- A process has a same-endpoint two-step pair when one is explicitly given. -/
def HasSameEndpointTwoStepPair (P : FiniteProcess) : Prop :=
  Nonempty (SameEndpointTwoStepPair P)

/-! ## § 2 Two-route toy process -/

/-- Four states for the minimal two-route toy process. -/
inductive TwoRouteState : Type
  | source
  | upper
  | lower
  | target
  deriving DecidableEq, Repr

namespace TwoRouteState

/-- Finite code for the four states. -/
def code : TwoRouteState -> Nat
  | .source => 0
  | .upper => 1
  | .lower => 2
  | .target => 3

theorem code_lt_four (s : TwoRouteState) : code s < 4 := by
  cases s <;> decide

theorem code_injective {a b : TwoRouteState} :
    code a = code b -> a = b := by
  cases a <;> cases b <;> simp [code]

/-- The process terminates at the target. -/
def terminal : TwoRouteState -> Prop
  | .target => True
  | .source => False
  | .upper => False
  | .lower => False

/--
The two-route step relation:
`source -> upper -> target` and `source -> lower -> target`.
-/
def step : TwoRouteState -> TwoRouteState -> Prop
  | .source, .upper => True
  | .source, .lower => True
  | .upper, .target => True
  | .lower, .target => True
  | _, _ => False

/-- Natural-number kernel weights for the supported transitions. -/
def weight : TwoRouteState -> TwoRouteState -> Nat
  | .source, .upper => 1
  | .source, .lower => 1
  | .upper, .target => 1
  | .lower, .target => 1
  | _, _ => 0

theorem step_iff_positive_weight (a b : TwoRouteState) :
    step a b ↔ weight a b ≠ 0 := by
  cases a <;> cases b <;> simp [step, weight]

end TwoRouteState

/-- The four-state toy process with two alternative center states. -/
def twoRouteProcess : FiniteProcess where
  State := TwoRouteState
  stateCode := TwoRouteState.code
  stateBound := 4
  stateCode_lt_bound := TwoRouteState.code_lt_four
  stateCode_injective := by
    intro a b h
    exact TwoRouteState.code_injective h
  initial := .source
  terminal := TwoRouteState.terminal
  step := TwoRouteState.step

instance twoRouteProcessStateDecidableEq : DecidableEq twoRouteProcess.State :=
  inferInstanceAs (DecidableEq TwoRouteState)

/-! ## § 3 Probability, channel, and path-amplitude candidates -/

/-- Row denominators for the two-route toy process. -/
def twoRouteRowTotal : TwoRouteState -> Nat
  | .source => 2
  | .upper => 1
  | .lower => 1
  | .target => 0

theorem twoRouteRowTotal_positive_if_not_terminal
    (a : TwoRouteState) :
    ¬ twoRouteProcess.terminal a -> twoRouteRowTotal a ≠ 0 := by
  cases a <;> simp [twoRouteProcess, TwoRouteState.terminal, twoRouteRowTotal]

theorem twoRouteWeight_le_rowTotal
    (a b : TwoRouteState) :
    TwoRouteState.weight a b ≤ twoRouteRowTotal a := by
  cases a <;> cases b <;> decide

/-- Finite probability-kernel interface for the two-route toy process. -/
def twoRouteFiniteProbabilityKernel :
    FiniteProbabilityKernelSkeleton twoRouteProcess where
  support := TwoRouteState.step
  weight := TwoRouteState.weight
  support_iff_positive := TwoRouteState.step_iff_positive_weight
  support_implies_step := by
    intro a b h
    exact h
  rowTotal := twoRouteRowTotal
  rowTotal_positive_if_not_terminal :=
    twoRouteRowTotal_positive_if_not_terminal
  weight_le_rowTotal := twoRouteWeight_le_rowTotal

/--
Toy edge amplitudes.

The lower branch carries the opposite sign on its second edge, so its two-step
candidate amplitude can cancel the upper branch.
-/
def twoRouteQuantumAmplitude :
    TwoRouteState -> TwoRouteState -> ℂ
  | .source, .upper => 1
  | .upper, .target => 1
  | .source, .lower => 1
  | .lower, .target => -1
  | _, _ => 0

theorem twoRouteQuantumAmplitude_support_implies_step
    (a b : twoRouteProcess.State) :
    QuantumAmplitudeSupport (P := twoRouteProcess)
      twoRouteQuantumAmplitude a b ->
      twoRouteProcess.step a b := by
  intro h
  cases a <;> cases b <;>
    simp [QuantumAmplitudeSupport, twoRouteQuantumAmplitude, twoRouteProcess,
      TwoRouteState.step] at h ⊢

/-- Quantum-amplitude candidate for the two-route toy process. -/
def twoRouteQuantumAmplitudeSkeleton :
    QuantumAmplitudeSkeleton twoRouteProcess where
  amplitude := twoRouteQuantumAmplitude
  amplitude_support_implies_step :=
    twoRouteQuantumAmplitude_support_implies_step

/-- Quantum-channel candidate for the two-route toy process. -/
def twoRouteQuantumChannelSkeleton :
    QuantumChannelSkeleton twoRouteProcess where
  amplitudeLayer := twoRouteQuantumAmplitudeSkeleton
  classicalBoundary := twoRouteFiniteProbabilityKernel
  amplitude_support_refines_classical := by
    intro a b h
    exact twoRouteQuantumAmplitude_support_implies_step a b h

/--
The standard S5/S5b path-amplitude projection for the two-route process.

This endpoint-only skeleton is intentionally separate from the two-step
amplitude candidate below; the latter is what preserves route identity.
-/
noncomputable def twoRoutePathAmplitudeSkeleton :
    PathAmplitudeSkeleton twoRouteProcess :=
  validPathIndicatorPathAmplitudeSkeleton
    twoRouteProcess
    twoRouteQuantumChannelSkeleton

/-- A two-step path amplitude candidate over center-preserving witnesses. -/
structure TwoStepPathAmplitudeCandidate (P : FiniteProcess) where
  channel : QuantumChannelSkeleton P
  twoStepAmplitude : TwoStepPathWitness P -> ℂ
  candidateWeight : TwoStepPathWitness P -> ℝ
  born_boundary :
    ∀ p : TwoStepPathWitness P,
      candidateWeight p = ampProb (twoStepAmplitude p)

/-- A process has a center-preserving two-step amplitude candidate. -/
def HasTwoStepPathAmplitudeCandidate (P : FiniteProcess) : Prop :=
  Nonempty (TwoStepPathAmplitudeCandidate P)

/-- The candidate finite two-path sum for a same-endpoint pair. -/
def twoStepPairAmplitudeSum {P : FiniteProcess}
    (A : TwoStepPathAmplitudeCandidate P)
    (pair : SameEndpointTwoStepPair P) : ℂ :=
  A.twoStepAmplitude pair.left + A.twoStepAmplitude pair.right

/-! ## § 4 Concrete upper/lower route witnesses -/

/-- The upper route: `source -> upper -> target`. -/
def twoRouteUpperPath : TwoStepPathWitness twoRouteProcess where
  start := TwoRouteState.source
  center := TwoRouteState.upper
  stop := TwoRouteState.target
  leftStep := True.intro
  rightStep := True.intro

/-- The lower route: `source -> lower -> target`. -/
def twoRouteLowerPath : TwoStepPathWitness twoRouteProcess where
  start := TwoRouteState.source
  center := TwoRouteState.lower
  stop := TwoRouteState.target
  leftStep := True.intro
  rightStep := True.intro

/-- The upper/lower pair has the same endpoints and different center states. -/
def twoRouteUpperLowerPair :
    SameEndpointTwoStepPair twoRouteProcess where
  left := twoRouteUpperPath
  right := twoRouteLowerPath
  same_start := rfl
  same_stop := rfl
  distinct_middle := by
    decide

theorem two_route_paths_same_endpoints :
    twoRouteUpperPath.start = twoRouteLowerPath.start
      ∧ twoRouteUpperPath.stop = twoRouteLowerPath.stop :=
  ⟨rfl, rfl⟩

theorem two_route_paths_distinct_middle :
    twoRouteUpperPath.center ≠ twoRouteLowerPath.center := by
  decide

/-- Candidate two-step route amplitude: upper `1`, lower `-1`. -/
def twoRouteTwoStepAmplitude
    (p : TwoStepPathWitness twoRouteProcess) : ℂ :=
  if p.center = TwoRouteState.upper then 1
  else if p.center = TwoRouteState.lower then -1
  else 0

/-- Middle-preserving two-step amplitude candidate for the two-route process. -/
def twoRouteTwoStepAmplitudeCandidate :
    TwoStepPathAmplitudeCandidate twoRouteProcess where
  channel := twoRouteQuantumChannelSkeleton
  twoStepAmplitude := twoRouteTwoStepAmplitude
  candidateWeight := fun p => ampProb (twoRouteTwoStepAmplitude p)
  born_boundary := by
    intro p
    rfl

theorem two_route_upper_amplitude :
    twoRouteTwoStepAmplitudeCandidate.twoStepAmplitude
      twoRouteUpperPath = 1 := by
  simp [twoRouteTwoStepAmplitudeCandidate, twoRouteTwoStepAmplitude,
    twoRouteUpperPath]

theorem two_route_lower_amplitude :
    twoRouteTwoStepAmplitudeCandidate.twoStepAmplitude
      twoRouteLowerPath = -1 := by
  simp [twoRouteTwoStepAmplitudeCandidate, twoRouteTwoStepAmplitude,
    twoRouteLowerPath]

theorem two_route_pair_amplitude_cancels :
    twoStepPairAmplitudeSum
      twoRouteTwoStepAmplitudeCandidate
      twoRouteUpperLowerPair = 0 := by
  simp [twoStepPairAmplitudeSum, two_route_upper_amplitude,
    two_route_lower_amplitude, twoRouteUpperLowerPair]

/-- The cancelled finite two-path amplitude has Born-shaped weight zero. -/
theorem two_route_cancelled_born_weight_zero :
    (bornRuleCandidate
      (twoStepPairAmplitudeSum
        twoRouteTwoStepAmplitudeCandidate
        twoRouteUpperLowerPair)).candidateWeight = 0 := by
  rw [two_route_pair_amplitude_cancels]
  simp [bornRuleCandidate, ampProb]

/-! ## § 5 Public summary -/

/-- Public summary for S5c:
    the two-route toy process has finite probability, channel, endpoint-only
    path-amplitude, and center-preserving two-step amplitude candidates.  The
    upper and lower same-endpoint paths have different center states, carry
    candidate amplitudes `1` and `-1`, and their finite two-path sum cancels.
    This proves only a two-path cancellation candidate, not a physical
    interference law, path integral, Born-rule derivation, unitary/CPTP law,
    decoherence, or empirical closure. -/
theorem two_path_interference_bridge_summary :
    HasFiniteProbabilityProjection twoRouteProcess
    ∧ HasQuantumChannelCandidate twoRouteProcess
    ∧ HasPathAmplitudeProjection twoRouteProcess
    ∧ HasTwoStepPathAmplitudeCandidate twoRouteProcess
    ∧ HasSameEndpointTwoStepPair twoRouteProcess
    ∧ (twoRouteUpperPath.start = twoRouteLowerPath.start
        ∧ twoRouteUpperPath.stop = twoRouteLowerPath.stop)
    ∧ twoRouteUpperPath.center ≠ twoRouteLowerPath.center
    ∧ twoRouteTwoStepAmplitudeCandidate.twoStepAmplitude
        twoRouteUpperPath = 1
    ∧ twoRouteTwoStepAmplitudeCandidate.twoStepAmplitude
        twoRouteLowerPath = -1
    ∧ twoStepPairAmplitudeSum
        twoRouteTwoStepAmplitudeCandidate
        twoRouteUpperLowerPair = 0
    ∧ (bornRuleCandidate
        (twoStepPairAmplitudeSum
          twoRouteTwoStepAmplitudeCandidate
          twoRouteUpperLowerPair)).candidateWeight = 0
    ∧ HasInterferenceCandidate
    ∧ (∀ z : ℂ, (bornRuleCandidate z).candidateWeight = ampProb z)
    ∧ WenConstructiveCoverage := by
  rcases nonzero_path_amplitude_bridge_summary with
    ⟨_hNonzeroValid, _hNonzeroReachable, _hNonzeroCausal,
      _hConcreteProjection, _hConcreteNonzero, _hConcreteReachable,
      _hConcreteCausal, hInterference, hBornBoundary, hCoverage⟩
  exact
    ⟨ ⟨twoRouteFiniteProbabilityKernel⟩
    , ⟨twoRouteQuantumChannelSkeleton⟩
    , ⟨twoRoutePathAmplitudeSkeleton⟩
    , ⟨twoRouteTwoStepAmplitudeCandidate⟩
    , ⟨twoRouteUpperLowerPair⟩
    , two_route_paths_same_endpoints
    , two_route_paths_distinct_middle
    , two_route_upper_amplitude
    , two_route_lower_amplitude
    , two_route_pair_amplitude_cancels
    , two_route_cancelled_born_weight_zero
    , hInterference
    , hBornBoundary
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
