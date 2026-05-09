import SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge
import SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge.Core

namespace SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge

open SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
open SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## Public summary -/

theorem born_measurement_bridge_summary :
    ComputationalBasisBornMeasurementClosed
    ∧ MarkovAmplitudeBornRuleDerivationClosed
    ∧ NontrivialQuantumChannelLawClosed
    ∧ (∀ b : PendingBeyondS21, ClosedByStepwiseS21 b = false)
    ∧ WenConstructiveCoverage := by
  rcases born_rule_derivation_bridge_summary with
    ⟨_hBornDistribution, _hSumOverMiddleBorn, hBornDerivation,
      _hConcreteBorn, _hPendingBorn, _hCoverageBorn⟩
  rcases nontrivial_quantum_channel_law_bridge_summary with
    ⟨hNontrivialChannel, _hBornDistributionS20, _hSumOverMiddleBornS20,
      _hPathWeight, _hPendingS20, hCoverage⟩
  exact
    ⟨ computational_basis_born_measurement_closed
    , hBornDerivation
    , hNontrivialChannel
    , pending_boundary_not_closed_by_s21
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
