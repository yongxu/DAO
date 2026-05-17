/-
# R4CarryBlockContracts -- exact block frontier for R4-squared carry

The R4-squared carry bridge restores `META.cur` and reaches `BlockPre`.
Universal compose still needs exact `BlockPre -> BlockPost` witnesses for every
opcode family.  This module names that frontier without changing the VM,
without deciding R5+ word names, and without pretending the current placeholder
blocks already mutate the encoded history correctly.
-/
import SSBX.Foundation.Wen.MetaInterp.Block_Branches
import SSBX.Foundation.Wen.MetaInterp.Block_HuCuoZong
import SSBX.Foundation.Wen.MetaInterp.Block_Jump
import SSBX.Foundation.Wen.MetaInterp.Block_PushPop
import SSBX.Foundation.Wen.MetaInterp.Block_SetShi_FlipYao
import SSBX.Foundation.Wen.MetaInterp.R4CarryAssemblyPlan

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryBlockContracts

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
open SSBX.Foundation.Wen.MetaInterp.R4CarryAssemblyPlan

/-! ## Encoded-history mutation targets -/

/-- Pc-increment opcodes must prepend one register cell to the encoded pc
counter.  Current-only local blocks do not satisfy exact `BlockPost` until this
mutation is executable. -/
def PcAdvanceOneMutation
    (regHex : Hexagram) (sim : YiState) (history' : List R8) : Prop :=
  history' = regDataCell regHex :: encMetaHistory regHex sim

/-- Jump and taken-branch opcodes rewrite the leading pc-counter prefix to a
decoded target. -/
def PcRewriteMutation
    (regHex : Hexagram) (sim : YiState) (target : Nat)
    (history' : List R8) : Prop :=
  history' = encMetaHistory regHex { sim with pc := target }

/-- Halt rewrites the encoded halted flag and then stops META. -/
def HaltFlagMutation
    (regHex : Hexagram) (sim : YiState) (history' : List R8) : Prop :=
  history' = encMetaHistory regHex { sim with halted := true }

/-- Simulated push updates both the sim-history length region and the sim-history
payload region inside `encMetaHistory`. -/
def PushHistoryMutation
    (regHex : Hexagram) (sim : YiState) (history' : List R8) : Prop :=
  history' = encMetaHistory regHex
    { sim with history := sim.cur :: sim.history, pc := sim.pc + 1 }

/-- Simulated pop either removes a history head and restores it into `cur`, or
halts the object machine when the simulated history is empty. -/
def PopHistoryMutation
    (regHex : Hexagram) (sim : YiState) (history' : List R8) : Prop :=
  history' = encMetaHistory regHex sim.step

/-! ## Exact block contracts -/

abbrev BodyFuelOf : Type :=
  YiInstr → Nat

/-- Exact executable block witness for one instruction shape.

The `instr` may include concrete operands.  Operand decoding and subdispatch
must route to the matching block before this contract is used. -/
def ExactBlockAt
    (bodyOffsetOf : BodyOffsetOf) (bodyFuelOf : BodyFuelOf)
    (instr : YiInstr) : Prop :=
  ∀ regHex sim μ,
    sim.halted = false →
    sim.prog[sim.pc]? = some instr →
    BlockPre regHex sim (bodyOffsetOf instr) restoredMetaInterpProg μ →
      BlockPost regHex sim fetchOffset restoredMetaInterpProg
        (μ.runFuel (bodyFuelOf instr)) sim.step.halted

structure CurrentOnlyBlockContracts
    (bodyOffsetOf : BodyOffsetOf) (bodyFuelOf : BodyFuelOf) : Prop where
  nop :
    ExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.nop
  setShi :
    ∀ sh, ExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.setShi sh)
  flipYao :
    ∀ i, ExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.flipYao i)
  interlace :
    ExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.interlace
  complement :
    ExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.complement
  reverse :
    ExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.reverse

structure ControlBlockContracts
    (bodyOffsetOf : BodyOffsetOf) (bodyFuelOf : BodyFuelOf) : Prop where
  jump :
    ∀ target, ExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.jump target)
  branchYaoEq :
    ∀ i j target,
      ExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.branchYaoEq i j target)
  branchShiEq :
    ∀ sh target,
      ExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.branchShiEq sh target)

structure StackBlockContracts
    (bodyOffsetOf : BodyOffsetOf) (bodyFuelOf : BodyFuelOf) : Prop where
  push :
    ExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.push
  pop :
    ExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.pop

structure HaltBlockContract
    (bodyOffsetOf : BodyOffsetOf) (bodyFuelOf : BodyFuelOf) : Prop where
  halt :
    ExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.halt
  /-- v2 (2026-05-17): obligation for `branchYaoYang` instruction.
      MetaInterp 暂将其与 halt 同 route. -/
  branchYaoYang :
    ∀ i target,
      ExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.branchYaoYang i target)

/-- Family-complete exact block surface for the R4-squared carry route. -/
structure R4CarryExactBlockContracts
    (bodyOffsetOf : BodyOffsetOf) (bodyFuelOf : BodyFuelOf) : Prop where
  currentOnly :
    CurrentOnlyBlockContracts bodyOffsetOf bodyFuelOf
  control :
    ControlBlockContracts bodyOffsetOf bodyFuelOf
  stack :
    StackBlockContracts bodyOffsetOf bodyFuelOf
  halt :
    HaltBlockContract bodyOffsetOf bodyFuelOf

theorem exactBlockAt_of_contracts
    (bodyOffsetOf : BodyOffsetOf) (bodyFuelOf : BodyFuelOf)
    (O : R4CarryExactBlockContracts bodyOffsetOf bodyFuelOf) :
    ∀ instr, ExactBlockAt bodyOffsetOf bodyFuelOf instr := by
  intro instr
  cases instr with
  | nop =>
      exact O.currentOnly.nop
  | setShi sh =>
      exact O.currentOnly.setShi sh
  | flipYao i =>
      exact O.currentOnly.flipYao i
  | interlace =>
      exact O.currentOnly.interlace
  | complement =>
      exact O.currentOnly.complement
  | reverse =>
      exact O.currentOnly.reverse
  | branchYaoEq i j target =>
      exact O.control.branchYaoEq i j target
  | branchShiEq sh target =>
      exact O.control.branchShiEq sh target
  | jump target =>
      exact O.control.jump target
  | push =>
      exact O.stack.push
  | pop =>
      exact O.stack.pop
  | halt =>
      exact O.halt.halt
  | branchYaoYang i target =>
      exact O.halt.branchYaoYang i target

theorem r4_carry_block_contracts_cover_all_opcodes :
    ∀ bodyOffsetOf bodyFuelOf,
      R4CarryExactBlockContracts bodyOffsetOf bodyFuelOf →
        ∀ instr, ExactBlockAt bodyOffsetOf bodyFuelOf instr := by
  intro bodyOffsetOf bodyFuelOf O instr
  exact exactBlockAt_of_contracts bodyOffsetOf bodyFuelOf O instr

end SSBX.Foundation.Wen.MetaInterp.R4CarryBlockContracts
