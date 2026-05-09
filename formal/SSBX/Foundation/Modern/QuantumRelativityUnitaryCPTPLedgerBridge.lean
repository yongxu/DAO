/-
# QuantumRelativityUnitaryCPTPLedgerBridge -- S17 physical channel law ledger

Companion:
`义理/unitary-CPTP账本边界 · Markov桥S17.md`

S17 records the channel-law boundary after S13-S16:

1. the current typed skeleton has closed finite channel/probability interfaces:
   pointwise composition, associativity, sum-over-middle two-step support, and
   conditional composed Born distribution boundary;
2. the physical quantum-channel law still requires extra structure: Hilbert
   carriers, linear operators, unitary evolution, density matrices, complete
   positivity, trace preservation, Kraus semantics, and empirical calibration;
3. these physical requirements are explicitly marked required-but-not-closed by
   the current skeleton.

This ledger is a positive boundary statement: it preserves what S13-S16 have
closed and names the additional structures needed for a full unitary/CPTP
channel theorem.
-/
import SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge

namespace SSBX.Foundation.Modern.QuantumRelativityUnitaryCPTPLedgerBridge

open SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
open SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
open SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Current closed channel/probability skeleton items -/

/-- Current channel/probability boundary items closed by S13-S16. -/
inductive CurrentChannelBoundaryItem where
  | finiteClassicalBoundary
  | supportRespectingAmplitude
  | pointwiseComposition
  | pointwiseAssociativity
  | sumOverMiddleTwoStepBoundary
  | conditionalComposedBornBoundary
  deriving DecidableEq, Repr

/-- S17 records these current skeleton boundary items as closed. -/
def ClosedByStepwiseS17Boundary (_item : CurrentChannelBoundaryItem) : Bool :=
  true

theorem current_channel_boundary_closed_by_s17
    (item : CurrentChannelBoundaryItem) :
    ClosedByStepwiseS17Boundary item = true := by
  cases item <;> rfl

/-! ## § 2 Required-but-not-closed physical channel law ledger -/

/-- Ledger items required for a physical unitary/CPTP channel law. -/
inductive UnitaryCPTPLedgerItem where
  | hilbertSpaceCarrier
  | linearOperatorSemantics
  | innerProductPreservation
  | densityMatrixSemantics
  | completePositivity
  | tracePreservation
  | krausRepresentation
  | unitaryEvolutionLaw
  | empiricalCalibration
  deriving DecidableEq, Repr

/-- Each ledger item is required for a physical channel-law reading. -/
def RequiredForPhysicalChannelLaw (_item : UnitaryCPTPLedgerItem) : Bool :=
  true

/-- None of these physical channel-law items is closed by the current skeleton. -/
def ClosedByStepwiseS17 (_item : UnitaryCPTPLedgerItem) : Bool :=
  false

/--
Every physical channel-law ledger item is required for the stronger reading
and remains unclosed by S17.
-/
theorem unitary_cptp_ledger_required_but_not_closed_by_s17
    (item : UnitaryCPTPLedgerItem) :
    RequiredForPhysicalChannelLaw item = true
      ∧ ClosedByStepwiseS17 item = false := by
  cases item <;> exact ⟨rfl, rfl⟩

/-! ## § 3 Public summary -/

/--
Public summary for S17:
S13-S16 channel/probability skeleton boundaries remain closed, while the
physical unitary/CPTP channel-law ledger remains required-but-not-closed.
-/
theorem unitary_cptp_ledger_bridge_summary :
    BornDistributionBoundaryClosed
    ∧ SumOverMiddleChannelBoundaryClosed
    ∧ SumOverMiddleBornDistributionBoundaryClosed
    ∧ (∀ item : CurrentChannelBoundaryItem,
        ClosedByStepwiseS17Boundary item = true)
    ∧ (∀ item : UnitaryCPTPLedgerItem,
        RequiredForPhysicalChannelLaw item = true
          ∧ ClosedByStepwiseS17 item = false)
    ∧ WenConstructiveCoverage := by
  rcases sum_over_middle_born_distribution_bridge_summary with
    ⟨hSumOverMiddle, hBorn, hComposedBorn, _hConcreteSupport,
      _hConcreteNormalized, hCoverage⟩
  exact
    ⟨ hBorn
    , hSumOverMiddle
    , hComposedBorn
    , current_channel_boundary_closed_by_s17
    , unitary_cptp_ledger_required_but_not_closed_by_s17
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityUnitaryCPTPLedgerBridge
