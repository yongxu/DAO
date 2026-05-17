import SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
import SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge.Core

namespace SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge

open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Text.OperatorCellMap

/-! ## Public summary -/

/-- Public summary for S10:
    S9 row-support normalization is retained, and the concrete plus `96000`
    grid kernels now also have finite normalized mass sums equal to `1` on
    every non-terminal row.  This closes the classical finite probability law
    for these displayed rows, while Born-weight normalization, channel laws,
    metric recovery, and empirical closure remain separate boundaries. -/
theorem normalized_mass_bridge_summary :
    FiniteSumOneProbabilityBoundaryClosed
    ∧ FiniteNormalizedMassBoundaryClosed
    ∧ HasFiniteProbabilityProjection concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ allOperatorCells.length = 96000
    ∧ (∀ b : PendingBeyondS10, ClosedByStepwiseS10 b = false)
    ∧ WenConstructiveCoverage := by
  rcases finite_probability_normalization_bridge_summary with
    ⟨hFiniteSumOne, hConcreteProbability, hGridProbability, hGridLength,
      _hPending, hCoverage⟩
  exact
    ⟨ hFiniteSumOne
    , finite_normalized_mass_boundary_closed
    , hConcreteProbability
    , hGridProbability
    , hGridLength
    , pending_boundary_not_closed_by_s10
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
