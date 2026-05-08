/-
# QuantumRelativityChannelComposeBridge -- channel composition candidate

Companion:
`义理/channelCompose候选 · Markov桥S13.md`

S13 adds the minimal composition operation for the existing S4
`QuantumChannelSkeleton`:

1. `channelCompose left right` multiplies the two amplitude layers pointwise;
2. it keeps the left channel's finite classical boundary;
3. a nonzero composed amplitude still implies a process step;
4. it is recorded together with the S12 finite Born distribution boundary.

This is a candidate composition interface for the current skeleton.  It is not
a theorem that physical quantum channels are unitary, CPTP, Kraus-composable,
or empirically closed.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge

namespace SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Text.OperatorCellMap

/-! ## § 1 Channel composition candidate -/

/--
Compose two channel candidates by multiplying amplitude entries pointwise and
retaining the left channel's classical finite probability boundary.
-/
def channelCompose {P : FiniteProcess}
    (left right : QuantumChannelSkeleton P) : QuantumChannelSkeleton P where
  amplitudeLayer :=
    { amplitude := fun a b =>
        left.amplitudeLayer.amplitude a b
          * right.amplitudeLayer.amplitude a b
      amplitude_support_implies_step := by
        intro a b h
        have hleft : left.amplitudeLayer.amplitude a b ≠ 0 := by
          intro hzero
          exact h (by simp [hzero])
        exact left.amplitudeLayer.amplitude_support_implies_step a b hleft }
  classicalBoundary := left.classicalBoundary
  amplitude_support_refines_classical := by
    intro a b h
    have hleft : left.amplitudeLayer.amplitude a b ≠ 0 := by
      intro hzero
      exact h (by simp [hzero])
    exact left.amplitude_support_refines_classical a b hleft

/-- The composed amplitude is pointwise multiplication. -/
theorem channelCompose_amplitude
    {P : FiniteProcess}
    (left right : QuantumChannelSkeleton P)
    (a b : P.State) :
    (channelCompose left right).amplitudeLayer.amplitude a b =
      left.amplitudeLayer.amplitude a b
        * right.amplitudeLayer.amplitude a b :=
  rfl

/-- Composition keeps the left classical finite probability boundary. -/
theorem channelCompose_keeps_left_classical_boundary
    {P : FiniteProcess}
    (left right : QuantumChannelSkeleton P) :
    (channelCompose left right).classicalBoundary = left.classicalBoundary :=
  rfl

/-- Nonzero composed amplitudes still imply process steps. -/
theorem channelCompose_support_implies_step
    {P : FiniteProcess}
    (left right : QuantumChannelSkeleton P) {a b : P.State} :
    QuantumAmplitudeSupport
        (channelCompose left right).amplitudeLayer.amplitude a b ->
      P.step a b := by
  exact (channelCompose left right).amplitudeLayer.amplitude_support_implies_step a b

/-! ## § 2 Closed composition boundary -/

/-- Closed facts for the minimal channel composition interface. -/
def ChannelCompositionBoundaryClosed : Prop :=
  ∀ {P : FiniteProcess} (left right : QuantumChannelSkeleton P),
    (∀ a b : P.State,
      (channelCompose left right).amplitudeLayer.amplitude a b =
        left.amplitudeLayer.amplitude a b
          * right.amplitudeLayer.amplitude a b)
      ∧ (channelCompose left right).classicalBoundary = left.classicalBoundary
      ∧ (∀ a b : P.State,
          QuantumAmplitudeSupport
            (channelCompose left right).amplitudeLayer.amplitude a b ->
              P.step a b)

theorem channel_composition_boundary_closed :
    ChannelCompositionBoundaryClosed := by
  intro P left right
  exact
    ⟨ channelCompose_amplitude left right
    , channelCompose_keeps_left_classical_boundary left right
    , fun a b => channelCompose_support_implies_step left right
    ⟩

/-- Concrete channel self-composition keeps the concrete finite boundary. -/
theorem concrete_channelCompose_self_keeps_boundary :
    (channelCompose concreteQuantumChannelSkeleton
      concreteQuantumChannelSkeleton).classicalBoundary =
        concreteFiniteProbabilityKernel :=
  rfl

/-- Grid channel self-composition keeps the grid finite boundary. -/
theorem operatorCellGrid_channelCompose_self_keeps_boundary :
    (channelCompose operatorCellGridQuantumChannelSkeleton
      operatorCellGridQuantumChannelSkeleton).classicalBoundary =
        operatorCellGridFiniteProbabilityKernel :=
  rfl

/-! ## § 3 Pending boundary after S13 -/

/-- Larger physical boundaries still not closed by candidate channel composition. -/
inductive PendingBeyondS13 where
  | bornRuleDerivation
  | physicalChannelLaw
  | continuousActionLaw
  | generalPathIntegral
  | measurablePredictionData
  | unitaryCPTPChannelLaw
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

/-- S13 does not close the larger physical boundaries. -/
def ClosedByStepwiseS13 (_b : PendingBeyondS13) : Bool :=
  false

theorem pending_boundary_not_closed_by_s13
    (b : PendingBeyondS13) :
    ClosedByStepwiseS13 b = false := by
  cases b <;> rfl

/-! ## § 4 Public summary -/

/-- Public summary for S13:
    S12 finite Born distribution boundary is retained, and current channel
    skeletons now have a compositional candidate operation.  The operation
    multiplies amplitude entries, keeps the left finite classical boundary,
    and preserves support-to-step soundness.  This is not a unitary/CPTP or
    empirical quantum-channel law. -/
theorem channel_compose_bridge_summary :
    BornDistributionBoundaryClosed
    ∧ ChannelCompositionBoundaryClosed
    ∧ HasQuantumChannelCandidate concreteProcess
    ∧ HasQuantumChannelCandidate operatorCellGridProcess
    ∧ (channelCompose concreteQuantumChannelSkeleton
        concreteQuantumChannelSkeleton).classicalBoundary =
          concreteFiniteProbabilityKernel
    ∧ (channelCompose operatorCellGridQuantumChannelSkeleton
        operatorCellGridQuantumChannelSkeleton).classicalBoundary =
          operatorCellGridFiniteProbabilityKernel
    ∧ (∀ b : PendingBeyondS13, ClosedByStepwiseS13 b = false)
    ∧ WenConstructiveCoverage := by
  rcases born_distribution_bridge_summary with
    ⟨_hFiniteSumOne, _hFiniteMass, _hConditionalBorn,
      hDistribution, _hPending, hCoverage⟩
  rcases amplitude_channel_bridge_summary with
    ⟨_hConcreteProbability, _hConcreteAmplitude, hConcreteChannel,
      _hGridProbability, _hGridAmplitude, hGridChannel,
      _hLayerSep, _hChannelSep, _hConcreteProjection, _hGridProjection,
      _hConcreteStep, _hGridStep, _hBorn, _hGridLength, _hCoverageOld⟩
  exact
    ⟨ hDistribution
    , channel_composition_boundary_closed
    , hConcreteChannel
    , hGridChannel
    , concrete_channelCompose_self_keeps_boundary
    , operatorCellGrid_channelCompose_self_keeps_boundary
    , pending_boundary_not_closed_by_s13
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge
