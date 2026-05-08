/-
# QuantumRelativityObservableLedgerBridge -- observable ledger candidate boundary

Companion:
`义理/观测账本候选 · Markov桥S5q.md`

This module advances S5p by registering the two-route quotient-support
cancellation as a candidate observable ledger entry:

1. it defines a minimal empirical-closure status with `pendingData`;
2. it packages a finite quotient-support amplitude sum and Born-shaped weight
   as an observable ledger entry;
3. it proves that a pending entry is not an empirically closed entry;
4. it records the two-route cancellation entry as pending while keeping its
   amplitude sum and Born-shaped weight at zero.

This is only a finite observable-ledger candidate boundary.  It does not prove
experimental closure, data calibration, a measurable prediction theorem, the
Born rule, a path integral, unitary/CPTP dynamics, or a continuous phase/action
law.
-/
import SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge

namespace SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
open SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Observable ledger entries -/

/-- Minimal status boundary for a candidate observable ledger entry. -/
inductive EmpiricalClosureStatus where
  /-- The candidate has been registered, but external data/calibration is open. -/
  | pendingData
  /-- External empirical closure has been supplied outside the finite skeleton. -/
  | externallyClosed
  deriving DecidableEq, Repr

/--
A finite observable-ledger entry for quotient-support candidates.

The entry records the chosen key-amplitude candidate, the finite quotient
support, the displayed amplitude sum, the displayed Born-shaped candidate
weight, and an empirical-closure status.  The two boundary fields require the
displayed numbers to agree with the finite quotient-support formulas.
-/
structure ObservableLedgerEntry (P : FiniteProcess) where
  keyAmplitude : TwoStepKeyAmplitudeCandidate P
  support : List (TwoStepPathKeyQuotient P)
  amplitudeSum : ℂ
  candidateWeight : ℝ
  status : EmpiricalClosureStatus
  amplitude_boundary :
    amplitudeSum = quotientSupportAmplitudeSum keyAmplitude support
  born_boundary :
    candidateWeight = quotientSupportBornWeight keyAmplitude support

/-- The entry is registered as a pending empirical candidate. -/
def ObservableLedgerPending {P : FiniteProcess}
    (E : ObservableLedgerEntry P) : Prop :=
  E.status = EmpiricalClosureStatus.pendingData

/-- The entry is marked as externally empirically closed. -/
def EmpiricallyClosed {P : FiniteProcess}
    (E : ObservableLedgerEntry P) : Prop :=
  E.status = EmpiricalClosureStatus.externallyClosed

/-- Pending data and empirical closure are disjoint statuses. -/
theorem pending_not_empirically_closed {P : FiniteProcess}
    (E : ObservableLedgerEntry P) :
    ObservableLedgerPending E -> ¬ EmpiricallyClosed E := by
  intro hPending hClosed
  unfold ObservableLedgerPending at hPending
  unfold EmpiricallyClosed at hClosed
  rw [hPending] at hClosed
  cases hClosed

/-! ## § 2 Two-route cancellation ledger entry -/

/--
The two-route quotient-support cancellation registered as a pending observable
candidate.  The displayed amplitude sum and displayed Born-shaped candidate
weight are both zero, but the status remains `pendingData`.
-/
def twoRouteCancellationObservableLedgerEntry :
    ObservableLedgerEntry twoRouteProcess where
  keyAmplitude := twoRouteKeyAmplitudeCandidate
  support := twoRouteSourceTargetQuotientEnumeration
  amplitudeSum := 0
  candidateWeight := 0
  status := EmpiricalClosureStatus.pendingData
  amplitude_boundary := by
    rw [two_route_quotient_support_amplitude_sum_cancels]
  born_boundary := by
    rw [two_route_quotient_support_born_weight_zero]

theorem two_route_observable_ledger_amplitude_zero :
    twoRouteCancellationObservableLedgerEntry.amplitudeSum = 0 := by
  rfl

theorem two_route_observable_ledger_weight_zero :
    twoRouteCancellationObservableLedgerEntry.candidateWeight = 0 := by
  rfl

theorem two_route_observable_ledger_pending :
    ObservableLedgerPending twoRouteCancellationObservableLedgerEntry := by
  rfl

theorem two_route_observable_ledger_not_empirically_closed :
    ¬ EmpiricallyClosed twoRouteCancellationObservableLedgerEntry := by
  exact pending_not_empirically_closed
    twoRouteCancellationObservableLedgerEntry
    two_route_observable_ledger_pending

theorem two_route_observable_ledger_matches_support_sum :
    twoRouteCancellationObservableLedgerEntry.amplitudeSum =
      quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
        twoRouteSourceTargetQuotientEnumeration := by
  exact twoRouteCancellationObservableLedgerEntry.amplitude_boundary

theorem two_route_observable_ledger_matches_born_weight :
    twoRouteCancellationObservableLedgerEntry.candidateWeight =
      quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
        twoRouteSourceTargetQuotientEnumeration := by
  exact twoRouteCancellationObservableLedgerEntry.born_boundary

/-- The closed finite facts carried by the two-route observable ledger entry. -/
def TwoRouteObservableLedgerBoundaryComplete : Prop :=
  ObservableLedgerPending twoRouteCancellationObservableLedgerEntry
    ∧ twoRouteCancellationObservableLedgerEntry.amplitudeSum = 0
    ∧ twoRouteCancellationObservableLedgerEntry.candidateWeight = 0
    ∧ ¬ EmpiricallyClosed twoRouteCancellationObservableLedgerEntry

theorem two_route_observable_ledger_boundary_complete :
    TwoRouteObservableLedgerBoundaryComplete := by
  exact
    ⟨ two_route_observable_ledger_pending
    , two_route_observable_ledger_amplitude_zero
    , two_route_observable_ledger_weight_zero
    , two_route_observable_ledger_not_empirically_closed
    ⟩

/-! ## § 3 Public summary -/

/-- Public summary for S5q:
    quotient-support cancellation can be registered as a candidate observable
    ledger entry with zero displayed amplitude sum and zero Born-shaped
    candidate weight, while the entry remains pending rather than empirically
    closed.  This proves only a finite ledger boundary, not experimental
    closure, data calibration, or a physical prediction theorem. -/
theorem observable_ledger_bridge_summary :
    TwoRouteObservableLedgerBoundaryComplete
    ∧ twoRouteCancellationObservableLedgerEntry.amplitudeSum =
      quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
        twoRouteSourceTargetQuotientEnumeration
    ∧ twoRouteCancellationObservableLedgerEntry.candidateWeight =
      quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
        twoRouteSourceTargetQuotientEnumeration
    ∧ quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0
    ∧ quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0
    ∧ WenConstructiveCoverage := by
  rcases quotient_support_algebra_bridge_summary with
    ⟨_hAppend, _hPerm, _hReverse, _hReversedCancel, _hReversedBorn,
      hDoubleCancel, hDoubleBorn, hCoverage⟩
  exact
    ⟨ two_route_observable_ledger_boundary_complete
    , two_route_observable_ledger_matches_support_sum
    , two_route_observable_ledger_matches_born_weight
    , hDoubleCancel
    , hDoubleBorn
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge
