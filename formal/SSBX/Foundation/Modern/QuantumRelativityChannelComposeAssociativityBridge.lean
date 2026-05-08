/-
# QuantumRelativityChannelComposeAssociativityBridge -- S14 channel algebra boundary

Companion:
`义理/channelCompose结合律候选 · Markov桥S14.md`

S14 closes the algebraic part of the S13 pointwise `channelCompose`:

1. pointwise channel composition is associative at the amplitude boundary;
2. the left-biased classical boundary is stable under reassociation;
3. a diagonal identity amplitude would force one-step self loops, so it is
   blocked for no-self-step processes such as the concrete and operator-cell
   grid bridges.

This is not a unitary/CPTP identity theorem.  It records why the current
support-respecting skeleton cannot accept the usual diagonal identity channel
without additional structure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge

namespace SSBX.Foundation.Modern.QuantumRelativityChannelComposeAssociativityBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Text.OperatorCellMap

/-! ## § 1 Associativity boundary -/

/-- Reassociating pointwise channel composition keeps the same amplitude. -/
theorem channelCompose_associative_amplitude
    {P : FiniteProcess}
    (left middle right : QuantumChannelSkeleton P)
    (a b : P.State) :
    (channelCompose (channelCompose left middle) right).amplitudeLayer.amplitude a b =
      (channelCompose left (channelCompose middle right)).amplitudeLayer.amplitude a b := by
  simp [channelCompose, mul_assoc]

/-- Reassociating pointwise channel composition keeps the same left boundary. -/
theorem channelCompose_associative_classical_boundary
    {P : FiniteProcess}
    (left middle right : QuantumChannelSkeleton P) :
    (channelCompose (channelCompose left middle) right).classicalBoundary =
      (channelCompose left (channelCompose middle right)).classicalBoundary :=
  rfl

/-- Closed facts for pointwise associativity of the current channel skeleton. -/
def ChannelComposeAssociativityBoundaryClosed : Prop :=
  ∀ {P : FiniteProcess} (left middle right : QuantumChannelSkeleton P),
    (∀ a b : P.State,
      (channelCompose (channelCompose left middle) right).amplitudeLayer.amplitude a b =
        (channelCompose left (channelCompose middle right)).amplitudeLayer.amplitude a b)
      ∧ (channelCompose (channelCompose left middle) right).classicalBoundary =
        (channelCompose left (channelCompose middle right)).classicalBoundary

theorem channel_compose_associativity_boundary_closed :
    ChannelComposeAssociativityBoundaryClosed := by
  intro P left middle right
  exact
    ⟨ channelCompose_associative_amplitude left middle right
    , channelCompose_associative_classical_boundary left middle right
    ⟩

/-! ## § 2 Identity obstruction boundary -/

/--
A diagonal identity candidate would require every diagonal amplitude entry to
be `1`.
-/
def ChannelDiagonalIdentityCandidate
    {P : FiniteProcess} (C : QuantumChannelSkeleton P) : Prop :=
  ∀ a : P.State, C.amplitudeLayer.amplitude a a = 1

/-- A process has no one-step self loops. -/
def NoSelfStepProcess (P : FiniteProcess) : Prop :=
  ∀ a : P.State, ¬ P.step a a

/--
Any support-respecting channel whose diagonal entries are `1` forces each
state to have a one-step self loop.
-/
theorem channel_diagonal_identity_forces_self_step
    {P : FiniteProcess}
    (C : QuantumChannelSkeleton P)
    (hdiag : ChannelDiagonalIdentityCandidate C)
    (a : P.State) :
    P.step a a := by
  exact C.amplitudeLayer.amplitude_support_implies_step a a (by
    unfold QuantumAmplitudeSupport
    rw [hdiag a]
    norm_num)

/--
Therefore no-self-step processes cannot carry a diagonal identity candidate in
the current support-respecting channel skeleton.
-/
theorem no_self_step_blocks_channel_diagonal_identity
    {P : FiniteProcess}
    (C : QuantumChannelSkeleton P)
    (hNoSelf : NoSelfStepProcess P) :
    ¬ ChannelDiagonalIdentityCandidate C := by
  intro hdiag
  exact hNoSelf P.initial
    (channel_diagonal_identity_forces_self_step C hdiag P.initial)

/-- The concrete process blocks diagonal identity candidates. -/
theorem concrete_no_channel_diagonal_identity
    (C : QuantumChannelSkeleton concreteProcess) :
    ¬ ChannelDiagonalIdentityCandidate C :=
  no_self_step_blocks_channel_diagonal_identity C concrete_no_self_step

/-- The operator-cell grid process blocks diagonal identity candidates. -/
theorem operatorCellGrid_no_channel_diagonal_identity
    (C : QuantumChannelSkeleton operatorCellGridProcess) :
    ¬ ChannelDiagonalIdentityCandidate C :=
  no_self_step_blocks_channel_diagonal_identity C operatorCellGrid_no_self_step

/-! ## § 3 Public summary -/

/--
Public summary for S14:
S13 pointwise `channelCompose` is associative at the amplitude and classical
boundary interface.  The ordinary diagonal identity channel is not available in
this skeleton for no-self-step processes, because nonzero diagonal amplitudes
would force one-step self loops.
-/
theorem channel_compose_associativity_bridge_summary :
    ChannelCompositionBoundaryClosed
    ∧ ChannelComposeAssociativityBoundaryClosed
    ∧ (∀ C : QuantumChannelSkeleton concreteProcess,
        ¬ ChannelDiagonalIdentityCandidate C)
    ∧ (∀ C : QuantumChannelSkeleton operatorCellGridProcess,
        ¬ ChannelDiagonalIdentityCandidate C)
    ∧ WenConstructiveCoverage := by
  rcases channel_compose_bridge_summary with
    ⟨_hBornDistribution, hComposition, _hConcreteChannel, _hGridChannel,
      _hConcreteBoundary, _hGridBoundary, _hPending, hCoverage⟩
  exact
    ⟨ hComposition
    , channel_compose_associativity_boundary_closed
    , concrete_no_channel_diagonal_identity
    , operatorCellGrid_no_channel_diagonal_identity
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityChannelComposeAssociativityBridge
