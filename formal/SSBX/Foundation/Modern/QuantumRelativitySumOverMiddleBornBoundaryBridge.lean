/-
# QuantumRelativitySumOverMiddleBornBoundaryBridge -- S16 composed Born boundary

Companion:
`义理/sum-over-middle Born边界候选 · Markov桥S16.md`

S16 connects S15 sum-over-middle channel composition to the S12 finite Born
distribution boundary:

1. a finite endpoint-pair list is mapped to composed amplitudes;
2. if that composed amplitude support is already `ampProb`-normalized, it
   induces a `BornDistributionBoundary`;
3. the concrete `prepared -> evolved -> measured` endpoint support maps to
   `[1]`, hence to the existing unit normalized amplitude support.

This remains a conditional finite boundary.  It does not derive the Born rule,
unitary/CPTP channel law, path integral, or empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge

namespace SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
open SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Composed endpoint amplitude support -/

/--
Map a finite endpoint-pair support to the sum-over-middle amplitudes attached
to those endpoints.
-/
def sumOverMiddleEndpointAmplitudeSupport {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P)
    (endpoints : List (P.State × P.State)) : List ℂ :=
  endpoints.map fun endpoint =>
    sumOverMiddleChannelAmplitude middle left right endpoint.1 endpoint.2

/-! ## § 2 Conditional Born distribution boundary -/

/--
Boundary object tying a finite endpoint support to its composed amplitude
support and the S12 finite Born distribution boundary.
-/
structure SumOverMiddleBornDistributionBoundary {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P) where
  endpointSupport : List (P.State × P.State)
  amplitudeSupport : List ℂ
  bornBoundary : BornDistributionBoundary
  amplitude_support_boundary :
    amplitudeSupport =
      sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport
  born_boundary_amplitude_support :
    bornBoundary.amplitudeSupport = amplitudeSupport
  born_boundary_sum_one :
    (bornBoundary.distribution.support.map bornBoundary.distribution.weight).sum = 1

/--
Build the composed Born boundary from an already normalized composed amplitude
support.
-/
def sumOverMiddleBornDistributionBoundary {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P)
    (endpointSupport : List (P.State × P.State))
    (h : AmplitudeSupportNormalized
      (sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport)) :
    SumOverMiddleBornDistributionBoundary middle left right where
  endpointSupport := endpointSupport
  amplitudeSupport := sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport
  bornBoundary := bornDistributionBoundary
    (sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport) h
  amplitude_support_boundary := rfl
  born_boundary_amplitude_support := rfl
  born_boundary_sum_one := by
    exact (bornFiniteProbabilityDistribution
      (sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport) h).weight_sum_one

/--
Every normalized composed endpoint amplitude support induces the S12 finite
Born distribution boundary.
-/
theorem sum_over_middle_born_distribution_boundary
    {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P)
    (endpointSupport : List (P.State × P.State))
    (h : AmplitudeSupportNormalized
      (sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport)) :
    ∃ B : SumOverMiddleBornDistributionBoundary middle left right,
      B.endpointSupport = endpointSupport
        ∧ B.amplitudeSupport =
          sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport
        ∧ B.bornBoundary.amplitudeSupport = B.amplitudeSupport
        ∧ (B.bornBoundary.distribution.support.map
            B.bornBoundary.distribution.weight).sum = 1 := by
  refine ⟨sumOverMiddleBornDistributionBoundary middle left right endpointSupport h,
    rfl, rfl, rfl, ?_⟩
  exact (sumOverMiddleBornDistributionBoundary middle left right endpointSupport h).born_boundary_sum_one

/-- Closed conditional boundary for composed endpoint supports. -/
def SumOverMiddleBornDistributionBoundaryClosed : Prop :=
  ∀ {P : FiniteProcess}
      (middle : List P.State) (left right : QuantumChannelSkeleton P)
      (endpointSupport : List (P.State × P.State)),
    AmplitudeSupportNormalized
      (sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport) ->
      ∃ B : SumOverMiddleBornDistributionBoundary middle left right,
        B.endpointSupport = endpointSupport
          ∧ B.amplitudeSupport =
            sumOverMiddleEndpointAmplitudeSupport middle left right endpointSupport
          ∧ B.bornBoundary.amplitudeSupport = B.amplitudeSupport
          ∧ (B.bornBoundary.distribution.support.map
              B.bornBoundary.distribution.weight).sum = 1

theorem sum_over_middle_born_distribution_boundary_closed :
    SumOverMiddleBornDistributionBoundaryClosed := by
  intro _P middle left right endpointSupport h
  exact sum_over_middle_born_distribution_boundary middle left right endpointSupport h

/-! ## § 3 Concrete normalized composed support -/

/-- Concrete endpoint support for the composed prepared-to-measured amplitude. -/
def concreteComposedEndpointSupport : List (ConcreteState × ConcreteState) :=
  [(ConcreteState.prepared, ConcreteState.measured)]

/-- The concrete composed endpoint support has amplitude support `[1]`. -/
theorem concrete_sumOverMiddle_endpoint_amplitude_support :
    sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
      concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
      concreteComposedEndpointSupport = [1] := by
  change [sumOverMiddleChannelAmplitude [ConcreteState.evolved]
      concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
      ConcreteState.prepared ConcreteState.measured] = [1]
  rw [concrete_sumOverMiddle_prepared_measured_amplitude]

/-- Therefore the concrete composed endpoint support is already normalized. -/
theorem concrete_composed_endpoint_amplitude_support_normalized :
    AmplitudeSupportNormalized
      (sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
        concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
        concreteComposedEndpointSupport) := by
  rw [concrete_sumOverMiddle_endpoint_amplitude_support]
  simpa [unitAmplitudeSupport] using unit_amplitude_support_normalized

/-! ## § 4 Public summary -/

/--
Public summary for S16:
S15 sum-over-middle composition can be connected to the S12 finite Born
distribution boundary whenever the displayed composed endpoint amplitude
support is already normalized.  The concrete composed endpoint support maps to
`[1]`, so it satisfies that conditional boundary.
-/
theorem sum_over_middle_born_distribution_bridge_summary :
    SumOverMiddleChannelBoundaryClosed
    ∧ BornDistributionBoundaryClosed
    ∧ SumOverMiddleBornDistributionBoundaryClosed
    ∧ sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
        concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
        concreteComposedEndpointSupport = [1]
    ∧ AmplitudeSupportNormalized
        (sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
          concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
          concreteComposedEndpointSupport)
    ∧ WenConstructiveCoverage := by
  rcases sum_over_middle_channel_bridge_summary with
    ⟨_hComposition, _hAssociativity, hSumOverMiddle, _hConcreteAmp,
      _hNotOneStep, _hTwoStep, hCoverage⟩
  exact
    ⟨ hSumOverMiddle
    , born_distribution_boundary_closed
    , sum_over_middle_born_distribution_boundary_closed
    , concrete_sumOverMiddle_endpoint_amplitude_support
    , concrete_composed_endpoint_amplitude_support_normalized
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge
