/-
# QuantumRelativityBornWeightNormalizationBridge -- conditional Born weights

Companion:
`义理/Born权重条件归一候选 · Markov桥S11.md`

S11 advances S10 from classical finite Markov masses toward an amplitude-side
probability interface:

1. it treats a finite list of complex amplitudes as an amplitude support;
2. it maps that support through the existing Born-shaped `bornRuleCandidate`;
3. it proves every displayed candidate weight is nonnegative;
4. it proves the candidate weights sum to `1` if the support is already
   normalized by `ampProb`.

This is only a conditional finite probability law for an already normalized
amplitude support.  It does not derive the Born rule, does not construct a
measurement postulate, and does not prove unitary/CPTP dynamics, path
integrals, decoherence, metric recovery, or empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge

namespace SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge

/-! ## § 1 Finite amplitude support weights -/

/-- Sum of Born-shaped weights over a finite displayed amplitude support. -/
def amplitudeSupportWeightSum (support : List ℂ) : ℝ :=
  (support.map ampProb).sum

/--
A finite amplitude support is normalized when its displayed `ampProb` weights
sum to `1`.
-/
def AmplitudeSupportNormalized (support : List ℂ) : Prop :=
  amplitudeSupportWeightSum support = 1

/-- Born-shaped candidate boundaries attached to a finite amplitude support. -/
def bornCandidateBoundarySupport
    (support : List ℂ) : List BornRuleCandidateBoundary :=
  support.map bornRuleCandidate

/-- Sum of displayed `candidateWeight` fields over a Born candidate support. -/
def bornCandidateWeightSum (support : List ℂ) : ℝ :=
  ((bornCandidateBoundarySupport support).map fun c => c.candidateWeight).sum

/--
The `candidateWeight` sum attached to the candidate boundary is exactly the
finite support's `ampProb` sum.
-/
theorem bornCandidateWeightSum_eq_amplitudeSupportWeightSum
    (support : List ℂ) :
    bornCandidateWeightSum support = amplitudeSupportWeightSum support := by
  induction support with
  | nil =>
      simp [bornCandidateWeightSum, bornCandidateBoundarySupport,
        amplitudeSupportWeightSum]
  | cons z zs ih =>
      change (bornRuleCandidate z).candidateWeight
          + bornCandidateWeightSum zs =
        ampProb z + amplitudeSupportWeightSum zs
      rw [born_rule_candidate_boundary, ih]

/-! ## § 2 Conditional finite Born probability law -/

/--
If a finite amplitude support is already normalized by `ampProb`, then its
Born-shaped candidate weights are nonnegative and sum to `1`.
-/
theorem born_weight_nonnegative_and_sum_one_if_normalized
    (support : List ℂ)
    (h : AmplitudeSupportNormalized support) :
    (∀ c : BornRuleCandidateBoundary,
        c ∈ bornCandidateBoundarySupport support -> 0 ≤ c.candidateWeight)
      ∧ bornCandidateWeightSum support = 1 := by
  constructor
  · intro c hc
    rcases List.mem_map.mp hc with ⟨z, _hz, rfl⟩
    exact born_rule_candidate_nonnegative z
  · rw [bornCandidateWeightSum_eq_amplitudeSupportWeightSum]
    exact h

/-- Closed conditional finite Born-weight boundary. -/
def ConditionalBornWeightNormalizationBoundaryClosed : Prop :=
  ∀ support : List ℂ,
    AmplitudeSupportNormalized support ->
      (∀ c : BornRuleCandidateBoundary,
          c ∈ bornCandidateBoundarySupport support -> 0 ≤ c.candidateWeight)
        ∧ bornCandidateWeightSum support = 1

theorem conditional_born_weight_normalization_boundary_closed :
    ConditionalBornWeightNormalizationBoundaryClosed :=
  born_weight_nonnegative_and_sum_one_if_normalized

/-! ## § 3 Minimal normalized support witness -/

/-- A one-amplitude normalized support witness. -/
def unitAmplitudeSupport : List ℂ :=
  [1]

theorem unit_amplitude_support_normalized :
    AmplitudeSupportNormalized unitAmplitudeSupport := by
  simp [AmplitudeSupportNormalized, amplitudeSupportWeightSum, unitAmplitudeSupport,
    ampProb]

theorem unit_amplitude_support_born_weight_law :
    (∀ c : BornRuleCandidateBoundary,
        c ∈ bornCandidateBoundarySupport unitAmplitudeSupport ->
          0 ≤ c.candidateWeight)
      ∧ bornCandidateWeightSum unitAmplitudeSupport = 1 :=
  born_weight_nonnegative_and_sum_one_if_normalized
    unitAmplitudeSupport unit_amplitude_support_normalized

/-! ## § 4 Pending boundary after S11 -/

/--
Larger physical boundaries still not closed by conditional finite Born weights.

S11 closes only the conditional list-level statement: if a finite amplitude
support is already normalized, then its Born-shaped candidate weights form a
finite probability law.
-/
inductive PendingBeyondS11 where
  | bornRuleDerivation
  | bornDistributionBoundary
  | continuousActionLaw
  | generalPathIntegral
  | measurablePredictionData
  | unitaryCPTPChannelLaw
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

/-- S11 does not close the larger physical boundaries. -/
def ClosedByStepwiseS11 (_b : PendingBeyondS11) : Bool :=
  false

theorem pending_boundary_not_closed_by_s11
    (b : PendingBeyondS11) :
    ClosedByStepwiseS11 b = false := by
  cases b <;> rfl

end SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
