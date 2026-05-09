import SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
import SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge.Core

namespace SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge

open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## Public summary -/

/-- Public summary for S11:
    S10 finite normalized Markov mass law is retained, and finite amplitude
    supports now have a conditional Born-shaped probability law: if their
    displayed `ampProb` weights already sum to `1`, then all displayed
    `candidateWeight`s are nonnegative and their sum is `1`.  This remains a
    conditional boundary, not a Born-rule derivation or empirical closure. -/
theorem born_weight_normalization_bridge_summary :
    FiniteSumOneProbabilityBoundaryClosed
    ∧ FiniteNormalizedMassBoundaryClosed
    ∧ ConditionalBornWeightNormalizationBoundaryClosed
    ∧ ((∀ c : BornRuleCandidateBoundary,
          c ∈ bornCandidateBoundarySupport unitAmplitudeSupport ->
            0 ≤ c.candidateWeight)
        ∧ bornCandidateWeightSum unitAmplitudeSupport = 1)
    ∧ (∀ b : PendingBeyondS11, ClosedByStepwiseS11 b = false)
    ∧ WenConstructiveCoverage := by
  rcases normalized_mass_bridge_summary with
    ⟨hFiniteSumOne, hFiniteMass, _hConcreteProbability, _hGridProbability,
      _hGridLength, _hPending, hCoverage⟩
  exact
    ⟨ hFiniteSumOne
    , hFiniteMass
    , conditional_born_weight_normalization_boundary_closed
    , unit_amplitude_support_born_weight_law
    , pending_boundary_not_closed_by_s11
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
