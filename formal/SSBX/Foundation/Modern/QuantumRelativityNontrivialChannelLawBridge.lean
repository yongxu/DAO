/-
# QuantumRelativityNontrivialChannelLawBridge -- S20 nontrivial finite channel law

Companion:
`义理/非平凡量子通道律候选 · Markov桥S20.md`

S20 closes the finite, nontrivial channel-law boundary that remained implicit
after S15-S17:

1. a nonzero channel amplitude gives a process step and refines the carried
   classical finite-probability support;
2. the concrete channel from S15 is genuinely nonzero on both displayed
   one-step edges;
3. its sum-over-middle composition gives a nonzero prepared-to-measured
   two-step amplitude and connects to the S16 Born distribution boundary.

This is a finite support-respecting typed skeleton.  It is not a Hilbert-space
unitary theorem, not a CPTP/Kraus/density-matrix theorem, not a dynamics law,
and not empirical closure.
-/
import Mathlib.Tactic.NormNum
import SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge

namespace SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
open SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
open SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge
open SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
open SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Nontrivial channel amplitude witness -/

/-- A displayed nonzero amplitude of a channel candidate. -/
structure NontrivialChannelAmplitudeWitness {P : FiniteProcess}
    (C : QuantumChannelSkeleton P) where
  source : P.State
  target : P.State
  amplitude_nonzero : C.amplitudeLayer.amplitude source target ≠ 0

namespace NontrivialChannelAmplitudeWitness

/-- The complex amplitude displayed by a nontrivial channel witness. -/
def amplitude {P : FiniteProcess} {C : QuantumChannelSkeleton P}
    (w : NontrivialChannelAmplitudeWitness C) : ℂ :=
  C.amplitudeLayer.amplitude w.source w.target

/-- Nonzero channel amplitude gives a process step. -/
theorem step {P : FiniteProcess} {C : QuantumChannelSkeleton P}
    (w : NontrivialChannelAmplitudeWitness C) :
    P.step w.source w.target :=
  C.amplitudeLayer.amplitude_support_implies_step w.source w.target
    w.amplitude_nonzero

/-- Nonzero channel amplitude refines the carried classical support. -/
theorem classical_support {P : FiniteProcess} {C : QuantumChannelSkeleton P}
    (w : NontrivialChannelAmplitudeWitness C) :
    C.classicalBoundary.support w.source w.target :=
  C.amplitude_support_refines_classical w.source w.target
    w.amplitude_nonzero

/-- The displayed amplitude has the ordinary Born-shaped boundary. -/
theorem born_weight_boundary {P : FiniteProcess}
    {C : QuantumChannelSkeleton P}
    (w : NontrivialChannelAmplitudeWitness C) :
    (bornRuleCandidate w.amplitude).candidateWeight = ampProb w.amplitude :=
  rfl

end NontrivialChannelAmplitudeWitness

/--
The finite nontrivial channel law available in the current skeleton:
a displayed nonzero channel amplitude gives a process step, refines the
classical finite support, and has the Born-shaped `ampProb` boundary.
-/
theorem nontrivial_channel_amplitude_law
    {P : FiniteProcess} {C : QuantumChannelSkeleton P}
    (w : NontrivialChannelAmplitudeWitness C) :
    P.step w.source w.target
      ∧ C.classicalBoundary.support w.source w.target
      ∧ (bornRuleCandidate w.amplitude).candidateWeight = ampProb w.amplitude := by
  exact
    ⟨ NontrivialChannelAmplitudeWitness.step w
    , NontrivialChannelAmplitudeWitness.classical_support w
    , NontrivialChannelAmplitudeWitness.born_weight_boundary w
    ⟩

/-! ## § 2 Concrete nonzero channel witness -/

theorem concrete_prepared_evolved_channel_amplitude :
    concreteStepQuantumChannelSkeleton.amplitudeLayer.amplitude
      ConcreteState.prepared ConcreteState.evolved = 1 := by
  norm_num [concreteStepQuantumChannelSkeleton, concreteStepAmplitudeSkeleton,
    concreteStepAmplitude]

theorem concrete_evolved_measured_channel_amplitude :
    concreteStepQuantumChannelSkeleton.amplitudeLayer.amplitude
      ConcreteState.evolved ConcreteState.measured = 1 := by
  norm_num [concreteStepQuantumChannelSkeleton, concreteStepAmplitudeSkeleton,
    concreteStepAmplitude]

theorem concrete_prepared_evolved_channel_amplitude_nonzero :
    concreteStepQuantumChannelSkeleton.amplitudeLayer.amplitude
      ConcreteState.prepared ConcreteState.evolved ≠ 0 := by
  rw [concrete_prepared_evolved_channel_amplitude]
  norm_num

theorem concrete_evolved_measured_channel_amplitude_nonzero :
    concreteStepQuantumChannelSkeleton.amplitudeLayer.amplitude
      ConcreteState.evolved ConcreteState.measured ≠ 0 := by
  rw [concrete_evolved_measured_channel_amplitude]
  norm_num

def concretePreparedEvolvedChannelWitness :
    NontrivialChannelAmplitudeWitness concreteStepQuantumChannelSkeleton where
  source := ConcreteState.prepared
  target := ConcreteState.evolved
  amplitude_nonzero := concrete_prepared_evolved_channel_amplitude_nonzero

def concreteEvolvedMeasuredChannelWitness :
    NontrivialChannelAmplitudeWitness concreteStepQuantumChannelSkeleton where
  source := ConcreteState.evolved
  target := ConcreteState.measured
  amplitude_nonzero := concrete_evolved_measured_channel_amplitude_nonzero

theorem concrete_prepared_evolved_nontrivial_channel_law :
    concreteProcess.step ConcreteState.prepared ConcreteState.evolved
      ∧ concreteStepQuantumChannelSkeleton.classicalBoundary.support
          ConcreteState.prepared ConcreteState.evolved
      ∧ (bornRuleCandidate
          (concreteStepQuantumChannelSkeleton.amplitudeLayer.amplitude
            ConcreteState.prepared ConcreteState.evolved)).candidateWeight = 1 := by
  rcases nontrivial_channel_amplitude_law
      concretePreparedEvolvedChannelWitness with ⟨hStep, hSupport, _hBorn⟩
  exact
    ⟨ hStep
    , hSupport
    , by
        rw [concrete_prepared_evolved_channel_amplitude]
        norm_num [bornRuleCandidate, ampProb]
    ⟩

theorem concrete_evolved_measured_nontrivial_channel_law :
    concreteProcess.step ConcreteState.evolved ConcreteState.measured
      ∧ concreteStepQuantumChannelSkeleton.classicalBoundary.support
          ConcreteState.evolved ConcreteState.measured
      ∧ (bornRuleCandidate
          (concreteStepQuantumChannelSkeleton.amplitudeLayer.amplitude
            ConcreteState.evolved ConcreteState.measured)).candidateWeight = 1 := by
  rcases nontrivial_channel_amplitude_law
      concreteEvolvedMeasuredChannelWitness with ⟨hStep, hSupport, _hBorn⟩
  exact
    ⟨ hStep
    , hSupport
    , by
        rw [concrete_evolved_measured_channel_amplitude]
        norm_num [bornRuleCandidate, ampProb]
    ⟩

/-! ## § 3 Concrete two-step and Born boundary -/

theorem concrete_nontrivial_sum_over_middle_channel_law :
    sumOverMiddleChannelAmplitude [ConcreteState.evolved]
        concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
        ConcreteState.prepared ConcreteState.measured = 1
      ∧ TwoStepReachableViaList (P := concreteProcess) [ConcreteState.evolved]
          ConcreteState.prepared ConcreteState.measured
      ∧ sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
          concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
          concreteComposedEndpointSupport = [1]
      ∧ AmplitudeSupportNormalized
          (sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
            concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
            concreteComposedEndpointSupport) := by
  exact
    ⟨ concrete_sumOverMiddle_prepared_measured_amplitude
    , concrete_sumOverMiddle_prepared_measured_two_step
    , concrete_sumOverMiddle_endpoint_amplitude_support
    , concrete_composed_endpoint_amplitude_support_normalized
    ⟩

/-! ## § 4 Closed boundary and remaining ledger -/

def NontrivialQuantumChannelLawClosed : Prop :=
  (∀ {P : FiniteProcess} {C : QuantumChannelSkeleton P}
      (w : NontrivialChannelAmplitudeWitness C),
      P.step w.source w.target
        ∧ C.classicalBoundary.support w.source w.target
        ∧ (bornRuleCandidate w.amplitude).candidateWeight = ampProb w.amplitude)
    ∧ concreteStepQuantumChannelSkeleton.amplitudeLayer.amplitude
        ConcreteState.prepared ConcreteState.evolved = 1
    ∧ concreteStepQuantumChannelSkeleton.amplitudeLayer.amplitude
        ConcreteState.evolved ConcreteState.measured = 1
    ∧ concreteProcess.step ConcreteState.prepared ConcreteState.evolved
    ∧ concreteProcess.step ConcreteState.evolved ConcreteState.measured
    ∧ sumOverMiddleChannelAmplitude [ConcreteState.evolved]
        concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
        ConcreteState.prepared ConcreteState.measured = 1
    ∧ TwoStepReachableViaList (P := concreteProcess) [ConcreteState.evolved]
        ConcreteState.prepared ConcreteState.measured
    ∧ sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
        concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
        concreteComposedEndpointSupport = [1]
    ∧ AmplitudeSupportNormalized
        (sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
          concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
          concreteComposedEndpointSupport)

theorem nontrivial_quantum_channel_law_closed :
    NontrivialQuantumChannelLawClosed := by
  rcases concrete_prepared_evolved_nontrivial_channel_law with
    ⟨hPreparedEvolvedStep, _hPreparedEvolvedSupport, _hPreparedEvolvedBorn⟩
  rcases concrete_evolved_measured_nontrivial_channel_law with
    ⟨hEvolvedMeasuredStep, _hEvolvedMeasuredSupport, _hEvolvedMeasuredBorn⟩
  rcases concrete_nontrivial_sum_over_middle_channel_law with
    ⟨hComposedAmp, hTwoStep, hEndpointSupport, hNormalized⟩
  exact
    ⟨ fun w => nontrivial_channel_amplitude_law w
    , concrete_prepared_evolved_channel_amplitude
    , concrete_evolved_measured_channel_amplitude
    , hPreparedEvolvedStep
    , hEvolvedMeasuredStep
    , hComposedAmp
    , hTwoStep
    , hEndpointSupport
    , hNormalized
    ⟩

inductive PendingBeyondS20 where
  | hilbertSpaceCarrier
  | linearOperatorSemantics
  | innerProductPreservation
  | densityMatrixSemantics
  | completePositivity
  | tracePreservation
  | krausRepresentation
  | unitaryEvolutionLaw
  | amplitudeDynamics
  | measurementPostulateSemantics
  | decoherenceBoundary
  | generalPathIntegral
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS20 (_b : PendingBeyondS20) : Bool :=
  false

theorem pending_boundary_not_closed_by_s20
    (b : PendingBeyondS20) :
    ClosedByStepwiseS20 b = false := by
  cases b <;> rfl

/-! ## § 5 Public summary -/

theorem nontrivial_quantum_channel_law_bridge_summary :
    NontrivialQuantumChannelLawClosed
    ∧ BornDistributionBoundaryClosed
    ∧ SumOverMiddleBornDistributionBoundaryClosed
    ∧ PathWeightMultiplicationBoundaryClosed
    ∧ (∀ b : PendingBeyondS20, ClosedByStepwiseS20 b = false)
    ∧ WenConstructiveCoverage := by
  rcases born_rule_derivation_bridge_summary with
    ⟨hBorn, hSumOverMiddleBorn, _hDerivation, _hConcrete,
      _hPendingBorn, _hCoverageBorn⟩
  rcases path_weight_multiplication_bridge_summary with
    ⟨hPathWeight, _hConcreteWeight, _hReachable, _hCausal,
      _hPendingPath, hCoverage⟩
  exact
    ⟨ nontrivial_quantum_channel_law_closed
    , hBorn
    , hSumOverMiddleBorn
    , hPathWeight
    , pending_boundary_not_closed_by_s20
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge
