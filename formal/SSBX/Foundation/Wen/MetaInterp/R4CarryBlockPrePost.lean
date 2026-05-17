/-
# R4CarryBlockPrePost -- arbitrary-current block layer

`BlockPre` is the compatibility target for the transitional restored path:
`META.cur = sim.cur`.  That shape is useful for reusing existing proofs, but it
is not the clean arbitrary-current block invariant.  Exact pc-counter mutation
needs a register data cell in `META.cur`; the simulated current should be
available as the R4-squared carry.

This module introduces that next layer without changing the VM or deleting the
older `BlockPre` path.
-/
import SSBX.Foundation.Wen.MetaInterp.R4CarryBlockContracts

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryBlockPrePost

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
open SSBX.Foundation.Wen.MetaInterp.R4Carry
open SSBX.Foundation.Wen.MetaInterp.R4CarryBlockContracts

/-! ## Carry-native block state -/

/-- Carry-native block precondition for arbitrary-current execution.

Runtime `META.cur` is the register data cell needed for encoded-history
mutation.  The simulated current is preserved as `R4 x R4` proof/control data,
recoverable by `cellOfCarry`. -/
structure CarryBlockPre
    (regHex : Hexagram) (sim : YiState) (carry : SavedCurrentCarry)
    (offset : Nat) (metaProg : List YiInstr) (μ : YiState) : Prop where
  cur :
    μ.cur = regDataCell regHex
  carry_eq :
    carry = carryOfCell sim.cur
  history :
    μ.history = encMetaHistory regHex sim
  pc :
    μ.pc = offset
  prog :
    μ.prog = metaProg
  halted :
    μ.halted = false

/-- Carry-native block postcondition.  It intentionally agrees with
`BlockPost`; the difference is the stronger precondition, not a new object-level
semantics. -/
structure CarryBlockPost
    (regHex : Hexagram) (sim : YiState) (fetchOffset : Nat)
    (metaProg : List YiInstr) (μ' : YiState) (endHalted : Bool) : Prop where
  cur :
    μ'.cur = sim.step.cur
  history :
    μ'.history = encMetaHistory regHex sim.step
  pc :
    μ'.pc = fetchOffset
  prog :
    μ'.prog = metaProg
  halted :
    μ'.halted = endHalted

theorem carryBlockPost_to_BlockPost
    (regHex : Hexagram) (sim : YiState) (fetchOffset : Nat)
    (metaProg : List YiInstr) (μ' : YiState) (endHalted : Bool)
    (h : CarryBlockPost regHex sim fetchOffset metaProg μ' endHalted) :
    BlockPost regHex sim fetchOffset metaProg μ' endHalted := by
  exact ⟨h.cur, h.history, h.pc, h.prog, h.halted⟩

theorem aligned_BlockPre_to_CarryBlockPre
    (regHex : Hexagram) (sim : YiState) (offset : Nat)
    (metaProg : List YiInstr) (μ : YiState)
    (h_aligned : sim.cur = regDataCell regHex)
    (h : BlockPre regHex sim offset metaProg μ) :
    CarryBlockPre regHex sim (carryOfCell sim.cur) offset metaProg μ := by
  exact
    ⟨ h.cur.trans h_aligned
    , rfl
    , h.history
    , h.pc
    , h.prog
    , h.halted
    ⟩

/-! ## Carry-indexed exact block contracts -/

abbrev CarryBodyOffsetOf : Type :=
  SavedCurrentCarry → YiInstr → Nat

abbrev CarryBodyFuelOf : Type :=
  SavedCurrentCarry → YiInstr → Nat

/-- Exact block witness indexed by the carried source current.  This is the
right surface for blocks that must first mutate encoded history using a register
data cell, then restore `sim.step.cur` from the carried source identity. -/
def CarryExactBlockAt
    (bodyOffsetOf : CarryBodyOffsetOf) (bodyFuelOf : CarryBodyFuelOf)
    (instr : YiInstr) : Prop :=
  ∀ regHex sim carry μ,
    sim.halted = false →
    sim.prog[sim.pc]? = some instr →
    CarryBlockPre regHex sim carry (bodyOffsetOf carry instr)
      restoredMetaInterpProg μ →
      CarryBlockPost regHex sim fetchOffset restoredMetaInterpProg
        (μ.runFuel (bodyFuelOf carry instr)) sim.step.halted

structure R4CarryIndexedBlockContracts
    (bodyOffsetOf : CarryBodyOffsetOf) (bodyFuelOf : CarryBodyFuelOf) : Prop where
  nop :
    CarryExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.nop
  setShi :
    ∀ sh, CarryExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.setShi sh)
  flipYao :
    ∀ i, CarryExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.flipYao i)
  interlace :
    CarryExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.interlace
  complement :
    CarryExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.complement
  reverse :
    CarryExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.reverse
  jump :
    ∀ target, CarryExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.jump target)
  branchYaoEq :
    ∀ i j target,
      CarryExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.branchYaoEq i j target)
  branchShiEq :
    ∀ sh target,
      CarryExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.branchShiEq sh target)
  push :
    CarryExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.push
  pop :
    CarryExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.pop
  halt :
    CarryExactBlockAt bodyOffsetOf bodyFuelOf YiInstr.halt
  /-- v2 (2026-05-17): obligation for `branchYaoYang` instruction.
      MetaInterp 暂将其与 halt 同 route (见 Dispatch.lean v2 注). -/
  branchYaoYang :
    ∀ i target,
      CarryExactBlockAt bodyOffsetOf bodyFuelOf (YiInstr.branchYaoYang i target)

theorem carryExactBlockAt_of_indexed_contracts
    (bodyOffsetOf : CarryBodyOffsetOf) (bodyFuelOf : CarryBodyFuelOf)
    (O : R4CarryIndexedBlockContracts bodyOffsetOf bodyFuelOf) :
    ∀ instr, CarryExactBlockAt bodyOffsetOf bodyFuelOf instr := by
  intro instr
  cases instr with
  | nop =>
      exact O.nop
  | setShi sh =>
      exact O.setShi sh
  | flipYao i =>
      exact O.flipYao i
  | interlace =>
      exact O.interlace
  | complement =>
      exact O.complement
  | reverse =>
      exact O.reverse
  | branchYaoEq i j target =>
      exact O.branchYaoEq i j target
  | branchShiEq sh target =>
      exact O.branchShiEq sh target
  | jump target =>
      exact O.jump target
  | push =>
      exact O.push
  | pop =>
      exact O.pop
  | halt =>
      exact O.halt
  | branchYaoYang i target =>
      exact O.branchYaoYang i target

theorem r4_carry_indexed_blocks_cover_all_opcodes :
    ∀ bodyOffsetOf bodyFuelOf,
      R4CarryIndexedBlockContracts bodyOffsetOf bodyFuelOf →
        ∀ instr, CarryExactBlockAt bodyOffsetOf bodyFuelOf instr := by
  intro bodyOffsetOf bodyFuelOf O instr
  exact carryExactBlockAt_of_indexed_contracts bodyOffsetOf bodyFuelOf O instr

end SSBX.Foundation.Wen.MetaInterp.R4CarryBlockPrePost
