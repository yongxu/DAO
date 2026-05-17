/-
# QuantumRelativityPathCausalBridge — path composition and local causal constraints

Companion:
`义理/路径组合与因果约束 · Markov桥S3.md`

This module advances the Markov/causal bridge by one conservative S3 step:

1. two valid path witnesses with a shared center state compose into a valid
   path witness;
2. the composed witness gives both reachability and `causalBefore`;
3. the concrete and operator-cell grid instances have code-successor steps,
   hence one-step self loops are excluded;
4. this is still not a full causal set theory, spacetime metric, light cone,
   or Lorentzian geometry recovery theorem.
-/
import SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge

namespace SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Text.OperatorCellMap
open SSBX.Text.WenyanOperators

/-! ## § 1 Path composition -/

/-- Two valid path witnesses are composable when the first stops where the second starts. -/
structure ComposableProcessPaths (P : FiniteProcess) where
  left : ProcessPath P
  right : ProcessPath P
  middle_eq : left.stop = right.start
  left_valid : left.valid
  right_valid : right.valid

/-- Compose two path witnesses by retaining the outer endpoints. -/
def composeProcessPaths {P : FiniteProcess}
    (c : ComposableProcessPaths P) : ProcessPath P :=
  { start := c.left.start
    stop := c.right.stop
    valid := c.left.valid ∧ c.right.valid ∧ c.left.stop = c.right.start }

/-- The composed path witness is valid. -/
theorem composed_path_valid {P : FiniteProcess}
    (c : ComposableProcessPaths P) :
    (composeProcessPaths c).valid :=
  ⟨c.left_valid, c.right_valid, c.middle_eq⟩

/-- A composed path witness gives reachability from the outer start to the outer stop. -/
theorem composed_path_reachable {P : FiniteProcess}
    (c : ComposableProcessPaths P) :
    Reachable P c.left.start c.right.stop :=
  path_implies_reachable (composeProcessPaths c) (composed_path_valid c)

/-- A composed path witness also gives the causal-before reading. -/
theorem composed_path_causal_before {P : FiniteProcess}
    (c : ComposableProcessPaths P) :
    causalBefore (P := P) ⟨c.left.start⟩ ⟨c.right.stop⟩ :=
  composed_path_reachable c

/-! ## § 2 Local code-successor constraints -/

/-- A process has code-successor steps when each one-step transition advances the state code by one. -/
def CodeSuccessorStep (P : FiniteProcess) : Prop :=
  ∀ a b : P.State, P.step a b → P.stateCode b = P.stateCode a + 1

/-- A process has code-monotone steps when each one-step transition strictly increases the state code. -/
def CodeMonotoneStep (P : FiniteProcess) : Prop :=
  ∀ a b : P.State, P.step a b → P.stateCode a < P.stateCode b

/-- Code-successor steps are code-monotone. -/
theorem code_successor_step_monotone {P : FiniteProcess} :
    CodeSuccessorStep P → CodeMonotoneStep P := by
  intro hsucc a b hstep
  rw [hsucc a b hstep]
  exact Nat.lt_succ_self (P.stateCode a)

/-- Code-monotone one-step transitions have no self loops. -/
theorem code_monotone_step_no_self_loop {P : FiniteProcess}
    (hmono : CodeMonotoneStep P) (a : P.State) :
    ¬ P.step a a := by
  intro hstep
  exact Nat.lt_irrefl (P.stateCode a) (hmono a a hstep)

/-! ## § 3 Concrete and grid witnesses -/

/-- The concrete bridge steps advance the finite state code by one. -/
theorem concrete_code_successor_step :
    CodeSuccessorStep concreteProcess := by
  intro a b h
  cases a <;> cases b <;>
    simp [concreteProcess, ConcreteState.step, ConcreteState.code] at h ⊢

/-- The concrete bridge has code-monotone one-step transitions. -/
theorem concrete_code_monotone_step :
    CodeMonotoneStep concreteProcess :=
  code_successor_step_monotone concrete_code_successor_step

/-- The concrete bridge has no one-step self loops. -/
theorem concrete_no_self_step (a : ConcreteState) :
    ¬ concreteProcess.step a a :=
  code_monotone_step_no_self_loop concrete_code_monotone_step a

/-- The operator-cell grid bridge successor relation advances the finite index by one. -/
theorem operatorCellGrid_code_successor_step :
    CodeSuccessorStep operatorCellGridProcess := by
  intro a b h
  unfold operatorCellGridProcess operatorCellGridStep at h ⊢
  exact h

/-- The operator-cell grid bridge has code-monotone one-step transitions. -/
theorem operatorCellGrid_code_monotone_step :
    CodeMonotoneStep operatorCellGridProcess :=
  code_successor_step_monotone operatorCellGrid_code_successor_step

/-- The operator-cell grid bridge has no one-step self loops. -/
theorem operatorCellGrid_no_self_step (a : OperatorCellGridState) :
    ¬ operatorCellGridProcess.step a a :=
  code_monotone_step_no_self_loop operatorCellGrid_code_monotone_step a

/-! ## § 4 Public summary -/

/-- Public summary for S3:
    path composition gives reachability and causal-before at the typed skeleton
    level, while the concrete and `375 × 256` grid instances satisfy a local
    code-successor constraint that excludes one-step self loops.  This does not
    prove a full causal set, spacetime geometry, light-cone structure, or metric
    recovery. -/
theorem path_causal_bridge_summary :
    (∀ {P : FiniteProcess} (c : ComposableProcessPaths P),
      Reachable P c.left.start c.right.stop)
    ∧ (∀ {P : FiniteProcess} (c : ComposableProcessPaths P),
      causalBefore (P := P) ⟨c.left.start⟩ ⟨c.right.stop⟩)
    ∧ CodeSuccessorStep concreteProcess
    ∧ CodeMonotoneStep concreteProcess
    ∧ (∀ a : ConcreteState, ¬ concreteProcess.step a a)
    ∧ CodeSuccessorStep operatorCellGridProcess
    ∧ CodeMonotoneStep operatorCellGridProcess
    ∧ (∀ a : OperatorCellGridState, ¬ operatorCellGridProcess.step a a)
    ∧ HasFiniteProbabilityProjection concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ allOperatorCells.length = 96000
    ∧ WenConstructiveCoverage := by
  rcases finite_probability_bridge_summary with
    ⟨hConcreteProb, hGridProb, _hConcreteRows, _hGridRows, _hConcreteBound,
      _hGridBound, _hOperators, _hCells, hGridLength, hCoverage⟩
  exact
    ⟨ fun c => composed_path_reachable c
    , fun c => composed_path_causal_before c
    , concrete_code_successor_step
    , concrete_code_monotone_step
    , concrete_no_self_step
    , operatorCellGrid_code_successor_step
    , operatorCellGrid_code_monotone_step
    , operatorCellGrid_no_self_step
    , hConcreteProb
    , hGridProb
    , hGridLength
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
