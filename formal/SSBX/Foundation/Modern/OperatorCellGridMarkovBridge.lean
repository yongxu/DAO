/-
# OperatorCellGridMarkovBridge — 94976 operator-cell grid as a bridge process

Companion:
`formal/SSBX/notes/unification-stepwise-plan.md`

This module connects the checked `371 × 256 = 94976` operator-cell coverage
grid to the abstract Markov/causal bridge interface.

It remains a finite typed skeleton:

1. the state space is the finite index `Fin allOperatorCells.length`;
2. each state reads back to one row of the Wen operator-cell grid;
3. a successor relation supplies a minimal Markov support skeleton;
4. the last grid state supplies a terminal measurement/event bridge;
5. the theorem records compatibility with `WenConstructiveCoverage`.
-/
import SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
import SSBX.Foundation.Modern.QuantumRelativityWenBoundary

namespace SSBX.Foundation.Modern.OperatorCellGridMarkovBridge

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Modern.QuantumSpacetime
open SSBX.Foundation.Modern.QuantumRelativityNoGo
open SSBX.Foundation.Modern.QuantumRelativityIntegration
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Text.OperatorCellMap
open SSBX.Text.WenyanOperators

/-! ## § 1 Grid-indexed process states -/

/-- The 371 × 256 Wen operator-cell grid, used as a finite process state space. -/
abbrev OperatorCellGridState : Type :=
  Fin allOperatorCells.length

/-- Read a finite grid state back to its operator-cell row. -/
def operatorCellAtState (s : OperatorCellGridState) : OperatorCell :=
  allOperatorCells.get s

/-- Every grid state reads back to a row of the checked operator-cell coverage grid. -/
theorem operatorCellAtState_mem_allOperatorCells
    (s : OperatorCellGridState) :
    operatorCellAtState s ∈ allOperatorCells := by
  unfold operatorCellAtState
  exact List.get_mem allOperatorCells s

/-- Initial grid state. -/
def operatorCellGridInitial : OperatorCellGridState :=
  ⟨0, by
    rw [allOperatorCells_length]
    decide⟩

/-- Terminal grid state: the final row of the checked coverage grid. -/
def operatorCellGridTerminalState : OperatorCellGridState :=
  ⟨allOperatorCells.length - 1, by
    rw [allOperatorCells_length]
    decide⟩

/-- Successor relation on the finite grid index. -/
def operatorCellGridStep (a b : OperatorCellGridState) : Prop :=
  b.val = a.val + 1

/-- The terminal predicate for the last grid state. -/
def operatorCellGridTerminal (s : OperatorCellGridState) : Prop :=
  s.val + 1 = allOperatorCells.length

/-- Natural-number support weights for the successor relation. -/
def operatorCellGridWeight (a b : OperatorCellGridState) : Nat :=
  if b.val = a.val + 1 then 1 else 0

/-- The grid weight is positive exactly on successor steps. -/
theorem operatorCellGrid_step_iff_positive_weight
    (a b : OperatorCellGridState) :
    operatorCellGridStep a b ↔ operatorCellGridWeight a b ≠ 0 := by
  unfold operatorCellGridStep operatorCellGridWeight
  by_cases h : b.val = a.val + 1 <;> simp [h]

/-! ## § 2 Concrete grid bridge -/

/-- The full operator-cell grid as a finite process. -/
def operatorCellGridProcess : FiniteProcess where
  State := OperatorCellGridState
  stateCode := fun s => s.val
  stateBound := allOperatorCells.length
  stateCode_lt_bound := fun s => s.isLt
  stateCode_injective := by
    intro a b h
    exact Fin.ext h
  initial := operatorCellGridInitial
  terminal := operatorCellGridTerminal
  step := operatorCellGridStep

/-- Markov kernel skeleton over the operator-cell grid successor relation. -/
def operatorCellGridKernel : MarkovKernelSkeleton operatorCellGridProcess where
  support := operatorCellGridStep
  weight := operatorCellGridWeight
  support_iff_positive := operatorCellGrid_step_iff_positive_weight
  support_implies_step := by
    intro a b h
    exact h

/-- The last grid state satisfies the process terminal predicate. -/
theorem operatorCellGridTerminalState_is_terminal :
    operatorCellGridProcess.terminal operatorCellGridTerminalState := by
  unfold operatorCellGridProcess operatorCellGridTerminal operatorCellGridTerminalState
  change (allOperatorCells.length - 1) + 1 = allOperatorCells.length
  rw [allOperatorCells_length]

/-- The terminal grid row as a measurement/event bridge. -/
def operatorCellGridTerminalBridge :
    MeasurementEventBridge operatorCellGridProcess where
  terminalState := operatorCellGridTerminalState
  isTerminal := operatorCellGridTerminalState_is_terminal

/-- A minimal valid path witness from the first grid state to the terminal grid state. -/
def operatorCellGridPath : ProcessPath operatorCellGridProcess where
  start := operatorCellGridInitial
  stop := operatorCellGridTerminalState
  valid := True

/-- The path witness gives reachability in the abstract bridge interface. -/
theorem operatorCellGridPath_reachable :
    Reachable operatorCellGridProcess
      operatorCellGridInitial
      operatorCellGridTerminalState :=
  path_implies_reachable operatorCellGridPath True.intro

/-! ## § 3 Public summary -/

/-- Public summary:
    the checked `371 × 256` Wen operator-cell grid itself can be used as a
    finite Markov/causal bridge process.  This closes only the grid-indexed
    finite skeleton; it still does not prove probability normalization, Born
    rule, quantum channels, metric recovery, or empirical closure. -/
theorem operator_cell_grid_markov_causal_bridge_summary :
    allOperatorIds.length = 371
    ∧ R8.all.length = 256
    ∧ allOperatorCells.length = 94976
    ∧ WenConstructiveCoverage
    ∧ (∀ s : OperatorCellGridState,
        operatorCellAtState s ∈ allOperatorCells)
    ∧ HasMarkovProjection operatorCellGridProcess
    ∧ HasCausalProjection operatorCellGridProcess
    ∧ MeasurementEventsAlign operatorCellGridTerminalBridge
    ∧ keepsQuantumFace MarkovCausalRoute = true
    ∧ keepsRelativityFace MarkovCausalRoute = true
    ∧ sameOne .quantumSpace .relativisticSpacetime
    ∧ ¬ CurrentPhysicalUnity .quantumSpace .relativisticSpacetime
    ∧ ¬ DirectUnificationByAddition := by
  rcases markov_causal_bridge_summary
    operatorCellGridProcess
    operatorCellGridKernel
    operatorCellGridTerminalBridge with
    ⟨hMarkov, hCausal, hAlign, hQuantum, hRelativity,
     hSameOne, hNotIdentity, hNotDirect⟩
  exact
    ⟨ allOperatorIds_length
    , R8.all_length
    , allOperatorCells_length
    , wen_constructive_coverage_192_371
    , operatorCellAtState_mem_allOperatorCells
    , hMarkov
    , hCausal
    , hAlign
    , hQuantum
    , hRelativity
    , hSameOne
    , hNotIdentity
    , hNotDirect
    ⟩

end SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
