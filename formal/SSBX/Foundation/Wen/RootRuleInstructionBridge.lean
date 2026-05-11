/-
# RootRuleInstructionBridge -- thin readback from YiInstr classes to root rules

This module is intentionally a sidecar bridge. It does not make the VM import
the root-language kernel, and it does not claim that a `RootRule` evaluation is
the same thing as executing a `YiInstr`. It records the conservative root-rule
reading of each parameter-erased opcode class and proves that the reading has an
R8-visible projection.
-/

import SSBX.Foundation.Wen.RootRuleKernel
import SSBX.Text.OperatorInstructionSemantics

namespace SSBX.Foundation.Wen.RootRuleInstructionBridge

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Hierarchy.RootLanguageTree
open SSBX.Foundation.Wen.R8ProjectionCalculus
open SSBX.Foundation.Wen.RootRuleKernel
open SSBX.Text.OperatorInstructionSemantics

/-! ## Root-rule readback for opcode classes -/

/-- Primary root-rule reading of a parameter-erased VM instruction class.

This is a semantic ledger, not a state-transition equality. For example, branch
instructions are read through `ite` with an `equal` support rule, while exact
program-counter behaviour remains in `BaguaTuring` and the meta-interpreter. -/
def rootRuleOfL0Clause : L0InstructionClauseKind -> RootRule
  | .nop => .returnDao
  | .setShi => .lift
  | .flipYao => .xor
  | .interlace => .compose
  | .complement => .xor
  | .reverse => .compose
  | .branchYaoEq => .ite
  | .branchShiEq => .ite
  | .jump => .recurse
  | .push => .quote
  | .pop => .lookup
  | .halt => .returnDao

/-- Additional root rules needed to read an instruction class conservatively. -/
def rootRuleSupportOfL0Clause : L0InstructionClauseKind -> List RootRule
  | .nop => []
  | .setShi => [.project]
  | .flipYao => [.apply]
  | .interlace => [.project]
  | .complement => [.apply]
  | .reverse => [.project]
  | .branchYaoEq => [.equal]
  | .branchShiEq => [.equal]
  | .jump => []
  | .push => []
  | .pop => []
  | .halt => []

/-- All root rules referenced by the opcode-class readback. -/
def rootRulesOfL0Clause (k : L0InstructionClauseKind) : List RootRule :=
  rootRuleOfL0Clause k :: rootRuleSupportOfL0Clause k

/-- Conservative CoreForm readback of an opcode class. -/
def rootCoreOfL0Clause (k : L0InstructionClauseKind) : CoreForm :=
  (rootRuleSupportOfL0Clause k).foldr
    (fun r acc => CoreForm.compose (.primitive r) acc)
    (.primitive (rootRuleOfL0Clause k))

/-- Primary root-rule reading of a concrete instruction. -/
def rootRuleOfInstr (instr : YiInstr) : RootRule :=
  rootRuleOfL0Clause (L0InstructionClauseKind.ofInstr instr)

/-- Support rules for a concrete instruction's parameter-erased class. -/
def rootRuleSupportOfInstr (instr : YiInstr) : List RootRule :=
  rootRuleSupportOfL0Clause (L0InstructionClauseKind.ofInstr instr)

/-- Conservative CoreForm readback of a concrete instruction's class. -/
def rootCoreOfInstr (instr : YiInstr) : CoreForm :=
  rootCoreOfL0Clause (L0InstructionClauseKind.ofInstr instr)

theorem rootRuleOfL0Clause_mem_all (k : L0InstructionClauseKind) :
    rootRuleOfL0Clause k ∈ RootRule.all := by
  cases k <;> simp [rootRuleOfL0Clause, RootRule.all]

theorem rootRuleSupportOfL0Clause_mem_all (k : L0InstructionClauseKind) :
    ∀ r ∈ rootRuleSupportOfL0Clause k, r ∈ RootRule.all := by
  cases k <;> simp [rootRuleSupportOfL0Clause, RootRule.all]

theorem rootRuleOfInstr_mem_all (instr : YiInstr) :
    rootRuleOfInstr instr ∈ RootRule.all := by
  exact rootRuleOfL0Clause_mem_all (L0InstructionClauseKind.ofInstr instr)

theorem rootRuleSupportOfInstr_mem_all (instr : YiInstr) :
    ∀ r ∈ rootRuleSupportOfInstr instr, r ∈ RootRule.all := by
  exact rootRuleSupportOfL0Clause_mem_all (L0InstructionClauseKind.ofInstr instr)

theorem rootRuleOfL0Clause_has_visible_projection (k : L0InstructionClauseKind) :
    ∃ c : R8, visibleR8 (primitiveSemantics (rootRuleOfL0Clause k)) = c :=
  primitive_has_visible_projection (rootRuleOfL0Clause k)

theorem rootRuleOfInstr_has_visible_projection (instr : YiInstr) :
    ∃ c : R8, visibleR8 (primitiveSemantics (rootRuleOfInstr instr)) = c :=
  primitive_has_visible_projection (rootRuleOfInstr instr)

theorem rootCoreOfL0Clause_has_visible_projection (k : L0InstructionClauseKind) :
    ∃ c : R8, CoreForm.visible emptyEnv (rootCoreOfL0Clause k) = c :=
  CoreForm.every_form_has_visible_projection emptyEnv (rootCoreOfL0Clause k)

theorem rootCoreOfL0Clause_has_loss_ledger (k : L0InstructionClauseKind) :
    ∃ loss : ProjectionLoss, CoreForm.loss emptyEnv (rootCoreOfL0Clause k) = loss :=
  CoreForm.every_form_has_loss_ledger emptyEnv (rootCoreOfL0Clause k)

theorem rootCoreOfInstr_has_visible_projection (instr : YiInstr) :
    ∃ c : R8, CoreForm.visible emptyEnv (rootCoreOfInstr instr) = c :=
  CoreForm.every_form_has_visible_projection emptyEnv (rootCoreOfInstr instr)

theorem rootCoreOfInstr_has_loss_ledger (instr : YiInstr) :
    ∃ loss : ProjectionLoss, CoreForm.loss emptyEnv (rootCoreOfInstr instr) = loss :=
  CoreForm.every_form_has_loss_ledger emptyEnv (rootCoreOfInstr instr)

/-! ## Public summary -/

theorem root_rule_instruction_bridge_summary :
    l0InstructionClauseKinds.length = 12
    ∧ l0InstructionClauseKinds.Nodup
    ∧ (∀ k : L0InstructionClauseKind, rootRuleOfL0Clause k ∈ RootRule.all)
    ∧ (∀ k : L0InstructionClauseKind,
        ∀ r ∈ rootRuleSupportOfL0Clause k, r ∈ RootRule.all)
    ∧ (∀ k : L0InstructionClauseKind,
        ∃ c : R8, visibleR8 (primitiveSemantics (rootRuleOfL0Clause k)) = c)
    ∧ (∀ k : L0InstructionClauseKind,
        ∃ c : R8, CoreForm.visible emptyEnv (rootCoreOfL0Clause k) = c)
    ∧ (∀ k : L0InstructionClauseKind,
        ∃ loss : ProjectionLoss, CoreForm.loss emptyEnv (rootCoreOfL0Clause k) = loss)
    ∧ (∀ instr : YiInstr, rootRuleOfInstr instr ∈ RootRule.all)
    ∧ (∀ instr : YiInstr,
        ∃ c : R8, visibleR8 (primitiveSemantics (rootRuleOfInstr instr)) = c)
    ∧ (∀ instr : YiInstr,
        ∃ loss : ProjectionLoss, CoreForm.loss emptyEnv (rootCoreOfInstr instr) = loss) := by
  exact
    ⟨ l0InstructionClauseKinds_length
    , l0InstructionClauseKinds_nodup
    , rootRuleOfL0Clause_mem_all
    , rootRuleSupportOfL0Clause_mem_all
    , rootRuleOfL0Clause_has_visible_projection
    , rootCoreOfL0Clause_has_visible_projection
    , rootCoreOfL0Clause_has_loss_ledger
    , rootRuleOfInstr_mem_all
    , rootRuleOfInstr_has_visible_projection
    , rootCoreOfInstr_has_loss_ledger
    ⟩

end SSBX.Foundation.Wen.RootRuleInstructionBridge
