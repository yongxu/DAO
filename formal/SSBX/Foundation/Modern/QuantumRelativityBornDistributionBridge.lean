/-
# QuantumRelativityBornDistributionBridge -- finite Born distribution boundary

Companion:
`义理/Born分布边界候选 · Markov桥S12.md`

S12 advances S11 by packaging the conditional Born-weight law into a finite
probability distribution interface:

1. it defines a small finite probability distribution interface over a listed
   support and a real-valued weight function;
2. it records the amplitude support sum, candidate support, and candidate
   weights in one boundary object;
3. it proves `born_distribution_boundary`: every normalized finite amplitude
   support induces such a boundary;
4. it keeps channel composition, Born-rule derivation, dynamics, geometry, and
   empirical closure separate.

This is a finite distribution boundary for already normalized amplitude
supports.  It does not derive the Born rule and does not assert that the
support came from physical dynamics.
-/
import SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge

namespace SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
open SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite probability distribution interface -/

/--
A finite probability distribution interface over an explicitly displayed
support list.
-/
structure FiniteProbabilityDistributionInterface (α : Type u) where
  support : List α
  weight : α -> ℝ
  weight_nonnegative_on_support :
    ∀ x : α, x ∈ support -> 0 ≤ weight x
  weight_sum_one : (support.map weight).sum = 1

/-! ## § 2 Born distribution boundary -/

/-- Sum of amplitudes over a finite amplitude support. -/
def amplitudeSupportAmplitudeSum (support : List ℂ) : ℂ :=
  support.sum

/-- The finite probability distribution induced by a normalized amplitude support. -/
def bornFiniteProbabilityDistribution
    (support : List ℂ)
    (h : AmplitudeSupportNormalized support) :
    FiniteProbabilityDistributionInterface BornRuleCandidateBoundary where
  support := bornCandidateBoundarySupport support
  weight := fun c => c.candidateWeight
  weight_nonnegative_on_support :=
    (born_weight_nonnegative_and_sum_one_if_normalized support h).1
  weight_sum_one := by
    simpa [bornCandidateWeightSum] using
      (born_weight_nonnegative_and_sum_one_if_normalized support h).2

/--
Boundary object tying together:

* finite amplitude support;
* its finite amplitude sum;
* the Born-shaped candidate support;
* the finite probability distribution over candidate weights.
-/
structure BornDistributionBoundary where
  amplitudeSupport : List ℂ
  amplitudeSum : ℂ
  candidateSupport : List BornRuleCandidateBoundary
  distribution : FiniteProbabilityDistributionInterface BornRuleCandidateBoundary
  amplitude_sum_boundary :
    amplitudeSum = amplitudeSupportAmplitudeSum amplitudeSupport
  support_boundary :
    candidateSupport = bornCandidateBoundarySupport amplitudeSupport
  distribution_support_boundary :
    distribution.support = candidateSupport
  candidate_weight_boundary :
    ∀ c : BornRuleCandidateBoundary,
      c ∈ distribution.support -> distribution.weight c = c.candidateWeight

/-- Build the boundary object from a normalized amplitude support. -/
def bornDistributionBoundary
    (support : List ℂ)
    (h : AmplitudeSupportNormalized support) : BornDistributionBoundary where
  amplitudeSupport := support
  amplitudeSum := amplitudeSupportAmplitudeSum support
  candidateSupport := bornCandidateBoundarySupport support
  distribution := bornFiniteProbabilityDistribution support h
  amplitude_sum_boundary := rfl
  support_boundary := rfl
  distribution_support_boundary := rfl
  candidate_weight_boundary := by
    intro _c _hc
    rfl

/--
Every normalized finite amplitude support induces a Born-shaped finite
probability distribution boundary over its candidate weights.
-/
theorem born_distribution_boundary
    (support : List ℂ)
    (h : AmplitudeSupportNormalized support) :
    ∃ B : BornDistributionBoundary,
      B.amplitudeSupport = support
        ∧ B.amplitudeSum = amplitudeSupportAmplitudeSum support
        ∧ B.candidateSupport = bornCandidateBoundarySupport support
        ∧ B.distribution.support = B.candidateSupport
        ∧ (∀ c : BornRuleCandidateBoundary,
            c ∈ B.distribution.support ->
              B.distribution.weight c = c.candidateWeight)
        ∧ (B.distribution.support.map B.distribution.weight).sum = 1 := by
  refine ⟨bornDistributionBoundary support h, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro _c _hc
    rfl
  · exact (bornFiniteProbabilityDistribution support h).weight_sum_one

/-- Closed finite Born distribution boundary. -/
def BornDistributionBoundaryClosed : Prop :=
  ∀ support : List ℂ,
    AmplitudeSupportNormalized support ->
      ∃ B : BornDistributionBoundary,
        B.amplitudeSupport = support
          ∧ B.amplitudeSum = amplitudeSupportAmplitudeSum support
          ∧ B.candidateSupport = bornCandidateBoundarySupport support
          ∧ B.distribution.support = B.candidateSupport
          ∧ (∀ c : BornRuleCandidateBoundary,
              c ∈ B.distribution.support ->
                B.distribution.weight c = c.candidateWeight)
          ∧ (B.distribution.support.map B.distribution.weight).sum = 1

theorem born_distribution_boundary_closed :
    BornDistributionBoundaryClosed :=
  born_distribution_boundary

/-! ## § 3 Pending boundary after S12 -/

/--
Larger physical boundaries still not closed by finite Born distribution
packaging.
-/
inductive PendingBeyondS12 where
  | bornRuleDerivation
  | channelComposition
  | continuousActionLaw
  | generalPathIntegral
  | measurablePredictionData
  | unitaryCPTPChannelLaw
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

/-- S12 does not close the larger physical boundaries. -/
def ClosedByStepwiseS12 (_b : PendingBeyondS12) : Bool :=
  false

theorem pending_boundary_not_closed_by_s12
    (b : PendingBeyondS12) :
    ClosedByStepwiseS12 b = false := by
  cases b <;> rfl

/-! ## § 4 Public summary -/

/-- Public summary for S12:
    S11 conditional Born weights are packaged as a finite probability
    distribution interface that remembers the amplitude support, amplitude
    sum, candidate support, and `candidateWeight` projection.  This is still
    conditional on normalized finite amplitude support and does not prove
    Born-rule derivation, channel composition, dynamics, geometry, or
    empirical closure. -/
theorem born_distribution_bridge_summary :
    FiniteSumOneProbabilityBoundaryClosed
    ∧ FiniteNormalizedMassBoundaryClosed
    ∧ ConditionalBornWeightNormalizationBoundaryClosed
    ∧ BornDistributionBoundaryClosed
    ∧ (∀ b : PendingBeyondS12, ClosedByStepwiseS12 b = false)
    ∧ WenConstructiveCoverage := by
  rcases born_weight_normalization_bridge_summary with
    ⟨hFiniteSumOne, hFiniteMass, hConditionalBorn, _hUnit,
      _hPending, hCoverage⟩
  exact
    ⟨ hFiniteSumOne
    , hFiniteMass
    , hConditionalBorn
    , born_distribution_boundary_closed
    , pending_boundary_not_closed_by_s12
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
