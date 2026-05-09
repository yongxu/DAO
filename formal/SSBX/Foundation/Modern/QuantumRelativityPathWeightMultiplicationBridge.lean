import SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
import SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge.Core

namespace SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## Public summary -/

theorem path_weight_multiplication_bridge_summary :
    PathWeightMultiplicationBoundaryClosed
    ∧ KernelPath.weight concretePreparedMeasuredKernelPath = 1
    ∧ Reachable concreteProcess ConcreteState.prepared ConcreteState.measured
    ∧ causalBefore (P := concreteProcess)
        ⟨ConcreteState.prepared⟩ ⟨ConcreteState.measured⟩
    ∧ (∀ b : PendingBeyondS19, ClosedByStepwiseS19 b = false)
    ∧ WenConstructiveCoverage := by
  rcases born_rule_derivation_bridge_summary with
    ⟨_hBorn, _hSumOverMiddleBorn, _hDerivation, _hConcrete,
      _hPending, hCoverage⟩
  exact
    ⟨ path_weight_multiplication_boundary_closed
    , concrete_prepared_measured_kernel_path_weight
    , KernelPath.append_reachable concretePreparedEvolvedKernelPath
        concreteEvolvedMeasuredKernelPath
    , KernelPath.append_causal_before concretePreparedEvolvedKernelPath
        concreteEvolvedMeasuredKernelPath
    , pending_boundary_not_closed_by_s19
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
