/-
# QuantumRelativityActionPhaseLawBridge -- finite action-to-phase law candidate

Companion:
`义理/作用量相位律候选 · Markov桥S5r.md`

This module advances S5q by moving the two-route cancellation from a displayed
quotient-support sum to a finite action-to-phase law candidate:

1. it defines a period-two action index and its induced discrete phase;
2. it defines quotient-support sums induced by an action-phase law;
3. it gives the two-route quotient support a finite action law: upper has
   action index `0`, lower has action index `1`;
4. it proves the induced quotient-support amplitude sum cancels and can be
   registered as a pending observable ledger entry.

This is only a finite period-two action-phase law candidate.  It is not a
continuous action functional, not Hamiltonian/unitary dynamics, not a path
integral, not a Born-rule derivation, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge

namespace SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
open SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
open SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge
open SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite action-to-phase law -/

/-- Period-two action index interpreted as a discrete phase. -/
def actionIndexPhase (n : Nat) : DiscretePhase :=
  match n % 2 with
  | 0 => DiscretePhase.zero
  | _ => DiscretePhase.pi

/-- Candidate amplitude induced by a period-two action index. -/
def actionIndexAmplitude (n : Nat) : ℂ :=
  discretePhaseAmplitude (actionIndexPhase n)

theorem action_index_zero_phase :
    actionIndexPhase 0 = DiscretePhase.zero := by
  rfl

theorem action_index_one_phase :
    actionIndexPhase 1 = DiscretePhase.pi := by
  rfl

theorem action_index_zero_amplitude :
    actionIndexAmplitude 0 = 1 := by
  rfl

theorem action_index_one_amplitude :
    actionIndexAmplitude 1 = -1 := by
  rfl

theorem action_index_zero_one_amplitudes_cancel :
    actionIndexAmplitude 0 + actionIndexAmplitude 1 = 0 := by
  rw [action_index_zero_amplitude, action_index_one_amplitude]
  norm_num

/-- A finite action-to-phase law on quotient classes. -/
structure QuotientActionPhaseLawCandidate (P : FiniteProcess) where
  actionIndex : TwoStepPathKeyQuotient P -> Nat

/-- Quotient-class amplitude induced by a finite action-to-phase law. -/
def quotientActionPhaseAmplitude {P : FiniteProcess}
    (L : QuotientActionPhaseLawCandidate P)
    (q : TwoStepPathKeyQuotient P) : ℂ :=
  actionIndexAmplitude (L.actionIndex q)

/-- Finite quotient-support sum induced by a finite action-to-phase law. -/
def quotientSupportActionPhaseAmplitudeSum {P : FiniteProcess}
    (L : QuotientActionPhaseLawCandidate P)
    (qs : List (TwoStepPathKeyQuotient P)) : ℂ :=
  (qs.map fun q => quotientActionPhaseAmplitude L q).sum

/-- Born-shaped candidate weight for an action-phase quotient-support sum. -/
def quotientSupportActionPhaseBornWeight {P : FiniteProcess}
    (L : QuotientActionPhaseLawCandidate P)
    (qs : List (TwoStepPathKeyQuotient P)) : ℝ :=
  ampProb (quotientSupportActionPhaseAmplitudeSum L qs)

/-! ## § 2 Two-route action law -/

/-- Two-route quotient action law: upper has index 0, lower has index 1. -/
def twoRouteQuotientActionPhaseLaw :
    QuotientActionPhaseLawCandidate twoRouteProcess where
  actionIndex q :=
    match (quotientVisibleKey q).middle with
    | TwoRouteState.upper => 0
    | TwoRouteState.lower => 1
    | TwoRouteState.source => 0
    | TwoRouteState.target => 0

theorem two_route_upper_quotient_action_index :
    twoRouteQuotientActionPhaseLaw.actionIndex
      (twoStepPathQuotientClass twoRouteUpperPath) = 0 := by
  rfl

theorem two_route_lower_quotient_action_index :
    twoRouteQuotientActionPhaseLaw.actionIndex
      (twoStepPathQuotientClass twoRouteLowerPath) = 1 := by
  rfl

theorem two_route_upper_action_phase_amplitude :
    quotientActionPhaseAmplitude twoRouteQuotientActionPhaseLaw
      (twoStepPathQuotientClass twoRouteUpperPath) = 1 := by
  rfl

theorem two_route_lower_action_phase_amplitude :
    quotientActionPhaseAmplitude twoRouteQuotientActionPhaseLaw
      (twoStepPathQuotientClass twoRouteLowerPath) = -1 := by
  rfl

/-- The two-route quotient support cancels under the finite action-phase law. -/
theorem two_route_action_phase_support_amplitude_cancels :
    quotientSupportActionPhaseAmplitudeSum twoRouteQuotientActionPhaseLaw
      twoRouteSourceTargetQuotientEnumeration = 0 := by
  norm_num [quotientSupportActionPhaseAmplitudeSum,
    twoRouteSourceTargetQuotientEnumeration, quotientActionPhaseAmplitude,
    twoRouteQuotientActionPhaseLaw, twoStepPathKey,
    twoRouteUpperPath, twoRouteLowerPath, actionIndexAmplitude,
    actionIndexPhase, discretePhaseAmplitude]

theorem two_route_action_phase_support_born_weight_zero :
    quotientSupportActionPhaseBornWeight twoRouteQuotientActionPhaseLaw
      twoRouteSourceTargetQuotientEnumeration = 0 := by
  rw [quotientSupportActionPhaseBornWeight,
    two_route_action_phase_support_amplitude_cancels]
  simp [ampProb]

/-! ## § 3 Ledger-compatible key amplitude -/

/-- Key-level version of the two-route action-phase law. -/
def twoRouteActionPhaseKeyAmplitudeCandidate :
    TwoStepKeyAmplitudeCandidate twoRouteProcess where
  channel := twoRouteQuantumChannelSkeleton
  keyAmplitude k :=
    actionIndexAmplitude
      (match k.middle with
      | TwoRouteState.upper => 0
      | TwoRouteState.lower => 1
      | TwoRouteState.source => 0
      | TwoRouteState.target => 0)
  candidateWeight k :=
    ampProb
      (actionIndexAmplitude
        (match k.middle with
        | TwoRouteState.upper => 0
        | TwoRouteState.lower => 1
        | TwoRouteState.source => 0
        | TwoRouteState.target => 0))
  born_boundary := by
    intro k
    rfl

theorem two_route_action_phase_key_support_amplitude_cancels :
    quotientSupportAmplitudeSum twoRouteActionPhaseKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0 := by
  norm_num [quotientSupportAmplitudeSum, twoRouteSourceTargetQuotientEnumeration,
    quotientKeyAmplitude, twoRouteActionPhaseKeyAmplitudeCandidate,
    twoStepPathKey, twoRouteUpperPath, twoRouteLowerPath,
    actionIndexAmplitude, actionIndexPhase, discretePhaseAmplitude]

theorem two_route_action_phase_key_support_born_weight_zero :
    quotientSupportBornWeight twoRouteActionPhaseKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0 := by
  rw [quotientSupportBornWeight,
    two_route_action_phase_key_support_amplitude_cancels]
  simp [ampProb]

/-- The action-phase law registered as a pending observable ledger entry. -/
def twoRouteActionPhaseObservableLedgerEntry :
    ObservableLedgerEntry twoRouteProcess where
  keyAmplitude := twoRouteActionPhaseKeyAmplitudeCandidate
  support := twoRouteSourceTargetQuotientEnumeration
  amplitudeSum := 0
  candidateWeight := 0
  status := EmpiricalClosureStatus.pendingData
  amplitude_boundary := by
    rw [two_route_action_phase_key_support_amplitude_cancels]
  born_boundary := by
    rw [two_route_action_phase_key_support_born_weight_zero]

theorem two_route_action_phase_observable_ledger_pending :
    ObservableLedgerPending twoRouteActionPhaseObservableLedgerEntry := by
  rfl

theorem two_route_action_phase_observable_ledger_not_empirically_closed :
    ¬ EmpiricallyClosed twoRouteActionPhaseObservableLedgerEntry := by
  exact pending_not_empirically_closed
    twoRouteActionPhaseObservableLedgerEntry
    two_route_action_phase_observable_ledger_pending

/-- The closed finite facts carried by the two-route action-phase law. -/
def TwoRouteActionPhaseLawBoundaryComplete : Prop :=
  twoRouteQuotientActionPhaseLaw.actionIndex
      (twoStepPathQuotientClass twoRouteUpperPath) = 0
    ∧ twoRouteQuotientActionPhaseLaw.actionIndex
      (twoStepPathQuotientClass twoRouteLowerPath) = 1
    ∧ quotientSupportActionPhaseAmplitudeSum twoRouteQuotientActionPhaseLaw
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ quotientSupportActionPhaseBornWeight twoRouteQuotientActionPhaseLaw
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ ObservableLedgerPending twoRouteActionPhaseObservableLedgerEntry
    ∧ ¬ EmpiricallyClosed twoRouteActionPhaseObservableLedgerEntry

theorem two_route_action_phase_law_boundary_complete :
    TwoRouteActionPhaseLawBoundaryComplete := by
  exact
    ⟨ two_route_upper_quotient_action_index
    , two_route_lower_quotient_action_index
    , two_route_action_phase_support_amplitude_cancels
    , two_route_action_phase_support_born_weight_zero
    , two_route_action_phase_observable_ledger_pending
    , two_route_action_phase_observable_ledger_not_empirically_closed
    ⟩

/-! ## § 4 Public summary -/

/-- Public summary for S5r:
    a finite period-two action index can induce the two-route opposite
    amplitudes, cancel over the quotient support, and be registered in a
    pending observable ledger entry.  This proves only a finite action-phase law
    candidate, not continuous action dynamics, a path integral, Born-rule
    derivation, or empirical closure. -/
theorem action_phase_law_bridge_summary :
    TwoRouteActionPhaseLawBoundaryComplete
    ∧ quotientSupportAmplitudeSum twoRouteActionPhaseKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ quotientSupportBornWeight twoRouteActionPhaseKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ TwoRouteObservableLedgerBoundaryComplete
    ∧ WenConstructiveCoverage := by
  rcases observable_ledger_bridge_summary with
    ⟨hLedgerBoundary, _hLedgerSum, _hLedgerWeight,
      _hDoubleCancel, _hDoubleBorn, hCoverage⟩
  exact
    ⟨ two_route_action_phase_law_boundary_complete
    , two_route_action_phase_key_support_amplitude_cancels
    , two_route_action_phase_key_support_born_weight_zero
    , hLedgerBoundary
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
