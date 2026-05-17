/-
# R4CarryParamDecodeObligations -- operand route frontier

R4-squared carry restores the current R8 cell after opcode-tag dispatch.  The
next executable frontier is operand routing: parameterized instructions must
route from their opcode-family entry to the concrete block indexed by the
decoded operands.  This file records that contract without building a concrete
dynamic target decoder and without introducing R5+ word names.
-/
import SSBX.Foundation.Wen.MetaInterp.R4CarryBlockContracts

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryParamDecodeObligations

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanSelfInterp.YiInstrEnc
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
open SSBX.Foundation.Wen.MetaInterp.R4CarryAssemblyPlan
open SSBX.Foundation.Wen.MetaInterp.R4CarryBlockContracts

/-! ## Pure operand cells -/

/-- The encoded payload cells after the opcode dispatch tag. -/
def operandCells : YiInstr → List R8
  | .nop => []
  | .setShi sh => [encShi sh]
  | .flipYao i => [encFin6 i]
  | .interlace => []
  | .complement => []
  | .reverse => []
  | .branchYaoEq i j target => [encFin6 i, encFin6 j] ++ encNat target
  | .branchShiEq sh target => [encShi sh] ++ encNat target
  | .jump target => encNat target
  | .push => []
  | .pop => []
  | .halt => []

theorem encInstr_eq_dispatchTag_cons_operands (instr : YiInstr) :
    encInstr instr = dispatchTagOfInstr instr :: operandCells instr := by
  cases instr <;> rfl

theorem encInstr_tail_eq_operandCells (instr : YiInstr) :
    (encInstr instr).tail = operandCells instr := by
  rw [encInstr_eq_dispatchTag_cons_operands]
  rfl

theorem decInstr_dispatchTag_cons_operands
    (instr : YiInstr) (h_enc : Encodable instr) (rest : List R8) :
    decInstr ((dispatchTagOfInstr instr :: operandCells instr) ++ rest) =
      some (instr, rest) := by
  have h := decInstr_encInstr instr h_enc rest
  rw [encInstr_eq_dispatchTag_cons_operands instr] at h
  exact h

/-! ## Decode-route contracts -/

abbrev ParamDecodeOffsetOf : Type :=
  YiInstr → Nat

abbrev ParamDecodeFuelOf : Type :=
  YiInstr → Nat

/-- Route from an opcode-family entry to the concrete operand-indexed block. -/
def ParamDecodeAt
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf)
    (instr : YiInstr) : Prop :=
  ∀ regHex sim μ,
    sim.halted = false →
    sim.prog[sim.pc]? = some instr →
    BlockPre regHex sim (paramDecodeOffsetOf instr) restoredMetaInterpProg μ →
      BlockPre regHex sim (bodyOffsetOf instr) restoredMetaInterpProg
        (μ.runFuel (paramDecodeFuelOf instr))

structure ParameterFreeDecodeContracts
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf) : Prop where
  nop :
    ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf YiInstr.nop
  interlace :
    ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf YiInstr.interlace
  complement :
    ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf YiInstr.complement
  reverse :
    ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf YiInstr.reverse
  push :
    ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf YiInstr.push
  pop :
    ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf YiInstr.pop
  halt :
    ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf YiInstr.halt

structure FiniteOperandDecodeContracts
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf) : Prop where
  setShi :
    ∀ sh, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
      (YiInstr.setShi sh)
  flipYao :
    ∀ i, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
      (YiInstr.flipYao i)
  branchShiOuter :
    ∀ sh target, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
      (YiInstr.branchShiEq sh target)
  branchYaoOuter :
    ∀ i j target, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
      (YiInstr.branchYaoEq i j target)

structure DynamicTargetDecodeContracts
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf) : Prop where
  jumpTarget :
    ∀ target, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
      (YiInstr.jump target)
  branchShiTarget :
    ∀ sh target, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
      (YiInstr.branchShiEq sh target)
  branchYaoTarget :
    ∀ i j target, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
      (YiInstr.branchYaoEq i j target)
  /-- v2 (2026-05-17): obligation for `branchYaoYang` instruction. -/
  branchYaoYangTarget :
    ∀ i target, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
      (YiInstr.branchYaoYang i target)

/-- Operand routing surface.  Finite operand dispatch and dynamic target decode
are separated because the latter is the real Nat-decoder frontier. -/
structure R4CarryParamDecodeContracts
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf) : Prop where
  parameterFree :
    ParameterFreeDecodeContracts paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
  finite :
    FiniteOperandDecodeContracts paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf
  dynamicTarget :
    DynamicTargetDecodeContracts paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf

theorem paramDecodeAt_of_contracts
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf)
    (O :
      R4CarryParamDecodeContracts
        paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf) :
    ∀ instr, ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf instr := by
  intro instr
  cases instr with
  | nop =>
      exact O.parameterFree.nop
  | setShi sh =>
      exact O.finite.setShi sh
  | flipYao i =>
      exact O.finite.flipYao i
  | interlace =>
      exact O.parameterFree.interlace
  | complement =>
      exact O.parameterFree.complement
  | reverse =>
      exact O.parameterFree.reverse
  | branchYaoEq i j target =>
      exact O.dynamicTarget.branchYaoTarget i j target
  | branchShiEq sh target =>
      exact O.dynamicTarget.branchShiTarget sh target
  | jump target =>
      exact O.dynamicTarget.jumpTarget target
  | push =>
      exact O.parameterFree.push
  | pop =>
      exact O.parameterFree.pop
  | halt =>
      exact O.parameterFree.halt
  | branchYaoYang i target =>
      exact O.dynamicTarget.branchYaoYangTarget i target

theorem r4_carry_param_decode_contracts_cover_all_opcodes :
    ∀ paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf,
      R4CarryParamDecodeContracts
        paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf →
        ∀ instr,
          ParamDecodeAt paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf instr := by
  intro paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf O instr
  exact paramDecodeAt_of_contracts
    paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf O instr

/-! ## Decode-to-block composition -/

theorem exactBlockAfterParamDecode
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf)
    (bodyFuelOf : BodyFuelOf)
    (P : R4CarryParamDecodeContracts
      paramDecodeOffsetOf bodyOffsetOf paramDecodeFuelOf)
    (B : R4CarryExactBlockContracts bodyOffsetOf bodyFuelOf)
    (instr : YiInstr) :
    ∀ regHex sim μ,
      sim.halted = false →
      sim.prog[sim.pc]? = some instr →
      BlockPre regHex sim (paramDecodeOffsetOf instr) restoredMetaInterpProg μ →
        BlockPost regHex sim fetchOffset restoredMetaInterpProg
          ((μ.runFuel (paramDecodeFuelOf instr)).runFuel (bodyFuelOf instr))
          sim.step.halted := by
  intro regHex sim μ h_alive h_get h_pre
  have h_param :
      BlockPre regHex sim (bodyOffsetOf instr) restoredMetaInterpProg
        (μ.runFuel (paramDecodeFuelOf instr)) :=
    paramDecodeAt_of_contracts paramDecodeOffsetOf bodyOffsetOf
      paramDecodeFuelOf P instr regHex sim μ h_alive h_get h_pre
  exact
    exactBlockAt_of_contracts bodyOffsetOf bodyFuelOf B instr
      regHex sim (μ.runFuel (paramDecodeFuelOf instr)) h_alive h_get h_param

end SSBX.Foundation.Wen.MetaInterp.R4CarryParamDecodeObligations
