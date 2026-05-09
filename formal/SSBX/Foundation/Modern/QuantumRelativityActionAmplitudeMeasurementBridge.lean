import SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
import SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
import SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge.Core

namespace SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge

open SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
open SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## Public summary -/

theorem action_amplitude_measurement_bridge_summary :
    TwoRouteActionPhaseLawBoundaryComplete
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS22, ClosedByStepwiseS22 b = false)
    ∧ WenConstructiveCoverage := by
  rcases action_phase_law_bridge_summary with
    ⟨hActionPhase, _hKeyCancel, _hKeyBorn, _hLedger, hCoverageAction⟩
  rcases born_measurement_bridge_summary with
    ⟨hBornMeasurement, _hBornDerivation, _hChannel,
      _hPendingBorn, _hCoverageBorn⟩
  exact
    ⟨ hActionPhase
    , action_to_born_measurement_chain_closed
    , hBornMeasurement
    , pending_boundary_not_closed_by_s22
    , hCoverageAction
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
