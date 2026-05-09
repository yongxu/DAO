/-
# QuantumRelativityBornRuleDerivationBridge -- S18 Born rule from Markov/amplitude bridge

Companion:
`义理/Born rule推导候选 · Markov桥S18.md`

S18 closes the finite typed-skeleton derivation that was pending after S12:

1. start with an explicitly normalized finite Markov row;
2. add an amplitude assignment over the same row support;
3. require the bridge equation `ampProb amplitude = normalizedMass`;
4. derive normalized amplitude support and therefore the S12 finite Born
   distribution boundary.

This proves the bridge-level Born-rule derivation under an explicit
Markov/amplitude compatibility hypothesis.  It does not prove that physical
dynamics must generate such amplitudes, nor measurement semantics, decoherence,
unitary/CPTP laws, or empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityUnitaryCPTPLedgerBridge

namespace SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
open SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
open SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge
open SSBX.Foundation.Modern.QuantumRelativityUnitaryCPTPLedgerBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 List and Markov-row real-sum lemmas -/

/-- Pointwise equality on a displayed list gives equality of finite sums. -/
theorem list_map_sum_eq_of_mem {α : Type u}
    (xs : List α) (f g : α -> ℝ)
    (h : ∀ x : α, x ∈ xs -> f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [h x (by simp), ih (by
        intro y hy
        exact h y (by simp [hy]))]

/-- Casting a finite rational sum to real is the sum of the cast entries. -/
theorem list_map_rat_sum_cast {α : Type u}
    (xs : List α) (f : α -> Rat) :
    (((xs.map f).sum : Rat) : ℝ) =
      ((xs.map fun x => (f x : ℝ)).sum) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

/-- Real-valued sum of Markov normalized masses over an explicit row support. -/
def realNormalizedMassSum {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P)
    (rowSupport : P.State -> List P.State)
    (a : P.State) : ℝ :=
  ((rowSupport a).map fun b => (normalizedMass K a b : ℝ)).sum

/--
S10's rational normalized-mass row law, read as a real-valued probability sum.
-/
theorem realNormalizedMassSum_eq_one
    {P : FiniteProcess}
    {K : FiniteProbabilityKernelSkeleton P}
    (R : FiniteRowSupportNormalization K)
    (a : P.State)
    (h : RowNormalizable K a) :
    realNormalizedMassSum K R.rowSupport a = 1 := by
  unfold realNormalizedMassSum
  have hRat : normalizedMassSum K R.rowSupport a = 1 :=
    normalizedMass_sum_one R a h
  unfold normalizedMassSum at hRat
  have hReal :
      (((R.rowSupport a).map fun b => normalizedMass K a b).sum : ℝ) = 1 := by
    exact_mod_cast hRat
  rw [list_map_rat_sum_cast] at hReal
  exact hReal

/-! ## § 2 Markov/amplitude compatibility -/

/--
Compatibility between a finite Markov row and a displayed amplitude support.

The support identity says the amplitude list is not an independent list: it is
the Markov row support read through an amplitude assignment.  The weight
identity is the bridge equation that turns Markov normalized masses into Born
weights.
-/
structure MarkovAmplitudeCompatibility {P : FiniteProcess}
    (K : FiniteProbabilityKernelSkeleton P)
    (R : FiniteRowSupportNormalization K)
    (a : P.State) where
  amplitudeOf : P.State -> ℂ
  amplitudeSupport : List ℂ
  amplitudeSupport_eq_rowSupport_map :
    amplitudeSupport = (R.rowSupport a).map amplitudeOf
  born_weight_eq_markov_mass :
    ∀ b : P.State, b ∈ R.rowSupport a ->
      ampProb (amplitudeOf b) = (normalizedMass K a b : ℝ)

/--
The Markov/amplitude bridge equation plus Markov row normalization derives
normalized finite amplitude support.
-/
theorem markov_amplitude_support_normalized
    {P : FiniteProcess}
    {K : FiniteProbabilityKernelSkeleton P}
    {R : FiniteRowSupportNormalization K}
    {a : P.State}
    (B : MarkovAmplitudeCompatibility K R a)
    (h : RowNormalizable K a) :
    AmplitudeSupportNormalized B.amplitudeSupport := by
  unfold AmplitudeSupportNormalized amplitudeSupportWeightSum
  rw [B.amplitudeSupport_eq_rowSupport_map]
  simp only [List.map_map]
  have hWeights :
      ((R.rowSupport a).map (ampProb ∘ B.amplitudeOf)).sum =
        ((R.rowSupport a).map fun b => (normalizedMass K a b : ℝ)).sum :=
    list_map_sum_eq_of_mem (R.rowSupport a)
      (ampProb ∘ B.amplitudeOf)
      (fun b => (normalizedMass K a b : ℝ))
      (by
        intro b hb
        exact B.born_weight_eq_markov_mass b hb)
  rw [hWeights]
  exact realNormalizedMassSum_eq_one R a h

/--
Every Born candidate displayed by the amplitude support is backed by a Markov
row entry with the same weight.
-/
theorem born_candidate_weights_match_markov_masses
    {P : FiniteProcess}
    {K : FiniteProbabilityKernelSkeleton P}
    {R : FiniteRowSupportNormalization K}
    {a : P.State}
    (B : MarkovAmplitudeCompatibility K R a) :
    ∀ c : BornRuleCandidateBoundary,
      c ∈ bornCandidateBoundarySupport B.amplitudeSupport ->
        ∃ b : P.State,
          b ∈ R.rowSupport a
            ∧ c.amplitude = B.amplitudeOf b
            ∧ c.candidateWeight = (normalizedMass K a b : ℝ) := by
  intro c hc
  unfold bornCandidateBoundarySupport at hc
  rcases List.mem_map.mp hc with ⟨z, hz, rfl⟩
  rw [B.amplitudeSupport_eq_rowSupport_map] at hz
  rcases List.mem_map.mp hz with ⟨b, hb, rfl⟩
  refine ⟨b, hb, rfl, ?_⟩
  calc
    (bornRuleCandidate (B.amplitudeOf b)).candidateWeight
        = ampProb (B.amplitudeOf b) := born_rule_candidate_boundary _
    _ = (normalizedMass K a b : ℝ) := B.born_weight_eq_markov_mass b hb

/--
The bridge-level Born-rule derivation: compatible amplitudes over a normalized
Markov row induce the S12 Born finite-probability boundary, and every displayed
Born candidate weight is the corresponding Markov normalized mass.
-/
theorem markov_amplitude_born_rule_derivation
    {P : FiniteProcess}
    {K : FiniteProbabilityKernelSkeleton P}
    {R : FiniteRowSupportNormalization K}
    {a : P.State}
    (B : MarkovAmplitudeCompatibility K R a)
    (h : RowNormalizable K a) :
    AmplitudeSupportNormalized B.amplitudeSupport
      ∧ (∃ D : BornDistributionBoundary,
          D.amplitudeSupport = B.amplitudeSupport
            ∧ D.candidateSupport =
                bornCandidateBoundarySupport B.amplitudeSupport
            ∧ D.distribution.support = D.candidateSupport
            ∧ (D.distribution.support.map D.distribution.weight).sum = 1)
      ∧ (∀ c : BornRuleCandidateBoundary,
          c ∈ bornCandidateBoundarySupport B.amplitudeSupport ->
            ∃ b : P.State,
              b ∈ R.rowSupport a
                ∧ c.amplitude = B.amplitudeOf b
                ∧ c.candidateWeight = (normalizedMass K a b : ℝ)) := by
  have hNorm := markov_amplitude_support_normalized B h
  rcases born_distribution_boundary B.amplitudeSupport hNorm with
    ⟨D, hAmp, _hAmpSum, hCandidates, hDistSupport, _hWeight, hSumOne⟩
  exact
    ⟨ hNorm
    , ⟨D, hAmp, hCandidates, hDistSupport, hSumOne⟩
    , born_candidate_weights_match_markov_masses B
    ⟩

/-! ## § 3 Concrete one-step witness -/

/-- Concrete prepared-row amplitude: the sole displayed Markov successor gets amplitude `1`. -/
def concretePreparedAmplitudeOf : ConcreteState -> ℂ
  | .evolved => 1
  | _ => 0

/-- The concrete prepared row satisfies the Markov/amplitude compatibility equation. -/
def concretePreparedMarkovAmplitudeCompatibility :
    MarkovAmplitudeCompatibility
      concreteFiniteProbabilityKernel
      concreteFiniteRowSupportNormalization
      ConcreteState.prepared where
  amplitudeOf := concretePreparedAmplitudeOf
  amplitudeSupport := [1]
  amplitudeSupport_eq_rowSupport_map := by
    rfl
  born_weight_eq_markov_mass := by
    intro b hb
    cases b <;>
      simp [concreteFiniteRowSupportNormalization, concreteRowSupport,
        concretePreparedAmplitudeOf, normalizedMass,
        concreteFiniteProbabilityKernel, concreteRowTotal,
        ConcreteState.weight, ampProb] at hb ⊢

theorem concrete_prepared_markov_amplitude_support_normalized :
    AmplitudeSupportNormalized
      concretePreparedMarkovAmplitudeCompatibility.amplitudeSupport :=
  markov_amplitude_support_normalized
    concretePreparedMarkovAmplitudeCompatibility
    concrete_prepared_row_normalizable

theorem concrete_prepared_born_rule_from_markov_amplitude_bridge :
    AmplitudeSupportNormalized
        concretePreparedMarkovAmplitudeCompatibility.amplitudeSupport
      ∧ (∃ D : BornDistributionBoundary,
          D.amplitudeSupport =
              concretePreparedMarkovAmplitudeCompatibility.amplitudeSupport
            ∧ D.candidateSupport =
                bornCandidateBoundarySupport
                  concretePreparedMarkovAmplitudeCompatibility.amplitudeSupport
            ∧ D.distribution.support = D.candidateSupport
            ∧ (D.distribution.support.map D.distribution.weight).sum = 1)
      ∧ (∀ c : BornRuleCandidateBoundary,
          c ∈ bornCandidateBoundarySupport
              concretePreparedMarkovAmplitudeCompatibility.amplitudeSupport ->
            ∃ b : ConcreteState,
              b ∈ concreteRowSupport ConcreteState.prepared
                ∧ c.amplitude =
                    concretePreparedMarkovAmplitudeCompatibility.amplitudeOf b
                ∧ c.candidateWeight =
                    (normalizedMass concreteFiniteProbabilityKernel
                      ConcreteState.prepared b : ℝ)) :=
  markov_amplitude_born_rule_derivation
    concretePreparedMarkovAmplitudeCompatibility
    concrete_prepared_row_normalizable

/-! ## § 4 Remaining physical ledger -/

inductive PendingBeyondS18 where
  | amplitudeConstructionFromDynamics
  | measurementPostulateSemantics
  | decoherenceBoundary
  | unitaryCPTPChannelLaw
  | generalPathIntegral
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS18 (_b : PendingBeyondS18) : Bool :=
  false

theorem pending_boundary_not_closed_by_s18
    (b : PendingBeyondS18) :
    ClosedByStepwiseS18 b = false := by
  cases b <;> rfl

/-- Closed S18 bridge-level Born-rule derivation. -/
def MarkovAmplitudeBornRuleDerivationClosed : Prop :=
  ∀ {P : FiniteProcess}
    {K : FiniteProbabilityKernelSkeleton P}
    {R : FiniteRowSupportNormalization K}
    {a : P.State}
    (B : MarkovAmplitudeCompatibility K R a)
    (_h : RowNormalizable K a),
      AmplitudeSupportNormalized B.amplitudeSupport
        ∧ (∃ D : BornDistributionBoundary,
            D.amplitudeSupport = B.amplitudeSupport
              ∧ D.candidateSupport =
                  bornCandidateBoundarySupport B.amplitudeSupport
              ∧ D.distribution.support = D.candidateSupport
              ∧ (D.distribution.support.map D.distribution.weight).sum = 1)
        ∧ (∀ c : BornRuleCandidateBoundary,
            c ∈ bornCandidateBoundarySupport B.amplitudeSupport ->
              ∃ b : P.State,
                b ∈ R.rowSupport a
                  ∧ c.amplitude = B.amplitudeOf b
                  ∧ c.candidateWeight = (normalizedMass K a b : ℝ))

theorem markov_amplitude_born_rule_derivation_closed :
    MarkovAmplitudeBornRuleDerivationClosed := by
  intro P K R a B h
  exact markov_amplitude_born_rule_derivation B h

/-! ## § 5 Public summary -/

theorem born_rule_derivation_bridge_summary :
    BornDistributionBoundaryClosed
    ∧ SumOverMiddleBornDistributionBoundaryClosed
    ∧ MarkovAmplitudeBornRuleDerivationClosed
    ∧ AmplitudeSupportNormalized
        concretePreparedMarkovAmplitudeCompatibility.amplitudeSupport
    ∧ (∀ b : PendingBeyondS18, ClosedByStepwiseS18 b = false)
    ∧ WenConstructiveCoverage := by
  rcases unitary_cptp_ledger_bridge_summary with
    ⟨hBorn, _hSumOverMiddleChannel, hSumOverMiddleBorn,
      _hCurrent, _hLedger, hCoverage⟩
  exact
    ⟨ hBorn
    , hSumOverMiddleBorn
    , markov_amplitude_born_rule_derivation_closed
    , concrete_prepared_markov_amplitude_support_normalized
    , pending_boundary_not_closed_by_s18
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
