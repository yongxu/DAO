import SSBX.Foundation.Modern.QuantumRelativityChannelComposeAssociativityBridge
import SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge.Core

namespace SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge
open SSBX.Foundation.Modern.QuantumRelativityChannelComposeAssociativityBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## Public summary -/

/--
Public summary for S15:
pointwise channel composition and its associativity remain available, while
sum-over-center composition is closed as a finite two-step boundary.  The
concrete process shows why this cannot simply be identified with the current
one-step `QuantumChannelSkeleton`: the prepared-to-measured composed amplitude
is nonzero, but prepared-to-measured is not a one-step edge.
-/
theorem sum_over_middle_channel_bridge_summary :
    ChannelCompositionBoundaryClosed
    ∧ ChannelComposeAssociativityBoundaryClosed
    ∧ SumOverMiddleChannelBoundaryClosed
    ∧ sumOverMiddleChannelAmplitude [ConcreteState.evolved]
        concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
        ConcreteState.prepared ConcreteState.measured = 1
    ∧ ¬ concreteProcess.step ConcreteState.prepared ConcreteState.measured
    ∧ TwoStepReachableViaList (P := concreteProcess) [ConcreteState.evolved]
        ConcreteState.prepared ConcreteState.measured
    ∧ WenConstructiveCoverage := by
  rcases channel_compose_associativity_bridge_summary with
    ⟨hComposition, hAssociativity, _hConcreteIdentity, _hGridIdentity, hCoverage⟩
  exact
    ⟨ hComposition
    , hAssociativity
    , sum_over_middle_channel_boundary_closed
    , concrete_sumOverMiddle_prepared_measured_amplitude
    , concrete_prepared_measured_not_one_step
    , concrete_sumOverMiddle_prepared_measured_two_step
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
