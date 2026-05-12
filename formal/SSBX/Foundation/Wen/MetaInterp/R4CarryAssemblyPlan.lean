/-
# R4CarryAssemblyPlan -- generated carry-row restore skeleton

This sidecar records the future executable shape for R4-squared saved-current
restore rows.  It is generated from

  SavedCurrentCarry x dispatch opcode representative

not from a flat current-cell table.  The module does not splice the rows into
`restoredMetaInterpProg`; it only proves the row-level restore contract that a
later embedded layout can use.
-/
import SSBX.Foundation.Wen.MetaInterp.R4CarryBridge

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryAssemblyPlan

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
open SSBX.Foundation.Wen.MetaInterp.R4Carry
open SSBX.Foundation.Wen.MetaInterp.R4CarryRestore

private def yao0 : Fin 6 := ⟨0, by omega⟩

/-! ## Carry rows -/

/-- One representative per dispatch opcode tag.  Parameter values are placeholders
only for selecting the opcode family; operand decoding remains a later phase. -/
def dispatchOpcodeReps : List YiInstr :=
  [ YiInstr.nop
  , YiInstr.setShi Shi.dao
  , YiInstr.flipYao yao0
  , YiInstr.interlace
  , YiInstr.complement
  , YiInstr.reverse
  , YiInstr.branchYaoEq yao0 yao0 0
  , YiInstr.branchShiEq Shi.dao 0
  , YiInstr.jump 0
  , YiInstr.push
  , YiInstr.pop
  , YiInstr.halt
  ]

theorem dispatchOpcodeReps_length :
    dispatchOpcodeReps.length = 12 := rfl

abbrev CarryRow : Type :=
  SavedCurrentCarry × YiInstr

/-- Generated carry rows: R4-squared carry dimension times the 12 opcode tags. -/
def carryRows : List CarryRow :=
  savedCurrentCarries.flatMap
    (fun carry => dispatchOpcodeReps.map (fun instr => (carry, instr)))

theorem carryRows_length :
    carryRows.length = 256 * 12 := by
  native_decide

abbrev RestoreOffsetOf : Type :=
  SavedCurrentCarry → YiInstr → Nat

abbrev BodyOffsetOf : Type :=
  YiInstr → Nat

/-! ## Row programs -/

def carryRowProgram (bodyOffsetOf : BodyOffsetOf) (row : CarryRow) : List YiInstr :=
  restoreCarryProg8 (dispatchTagOfInstr row.2) row.1 (bodyOffsetOf row.2)

theorem carryRowProgram_eq_restore
    (bodyOffsetOf : BodyOffsetOf) (row : CarryRow) :
    carryRowProgram bodyOffsetOf row =
      restoreCarryProg8 (dispatchTagOfInstr row.2) row.1 (bodyOffsetOf row.2) := rfl

theorem carryRowProgram_length
    (bodyOffsetOf : BodyOffsetOf) (row : CarryRow) :
    (carryRowProgram bodyOffsetOf row).length = 8 := by
  cases row with
  | mk carry instr =>
      exact restoreCarryProg8_length (dispatchTagOfInstr instr) carry (bodyOffsetOf instr)

/-- A generated restore-region skeleton.  It is not spliced into the global
interpreter program in this phase. -/
def carryRestoreRegion (bodyOffsetOf : BodyOffsetOf) : List YiInstr :=
  carryRows.flatMap (carryRowProgram bodyOffsetOf)

private theorem length_flatMap_const {α β : Type}
    (xs : List α) (f : α → List β) (n : Nat)
    (h : ∀ x, (f x).length = n) :
    (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [h x, ih, Nat.succ_mul]
      omega

theorem carryRestoreRegion_length
    (bodyOffsetOf : BodyOffsetOf) :
    (carryRestoreRegion bodyOffsetOf).length = (256 * 12) * 8 := by
  unfold carryRestoreRegion
  rw [length_flatMap_const carryRows (carryRowProgram bodyOffsetOf) 8
    (carryRowProgram_length bodyOffsetOf)]
  rw [carryRows_length]

/-! ## Row-level restore contract -/

structure R4CarryRowSegmentContract
    (restoreOffsetOf : RestoreOffsetOf) (bodyOffsetOf : BodyOffsetOf) : Prop where
  rowLength :
    ∀ row, (carryRowProgram bodyOffsetOf row).length = 8
  restores :
    ∀ regHex sim row,
      row.1 = carryOfCell sim.cur →
        BlockPre regHex sim (bodyOffsetOf row.2)
          (carryRowProgram bodyOffsetOf row)
          (({ cur := dispatchTagOfInstr row.2
            , history := encMetaHistory regHex sim
            , pc := 0
            , prog := carryRowProgram bodyOffsetOf row
            , halted := false } : YiState).runFuel
              (carryRowProgram bodyOffsetOf row).length)

theorem carryRowProgram_yields_BlockPre
    (bodyOffsetOf : BodyOffsetOf)
    (regHex : Hexagram) (sim : YiState) (row : CarryRow)
    (hcarry : row.1 = carryOfCell sim.cur) :
    BlockPre regHex sim (bodyOffsetOf row.2)
      (carryRowProgram bodyOffsetOf row)
      (({ cur := dispatchTagOfInstr row.2
        , history := encMetaHistory regHex sim
        , pc := 0
        , prog := carryRowProgram bodyOffsetOf row
        , halted := false } : YiState).runFuel
          (carryRowProgram bodyOffsetOf row).length) := by
  cases row with
  | mk carry instr =>
      exact
        restoreCarryProg8_yields_BlockPre
          regHex sim (dispatchTagOfInstr instr) carry (bodyOffsetOf instr) hcarry

theorem r4_carry_row_segment_contract
    (restoreOffsetOf : RestoreOffsetOf) (bodyOffsetOf : BodyOffsetOf) :
    R4CarryRowSegmentContract restoreOffsetOf bodyOffsetOf where
  rowLength := carryRowProgram_length bodyOffsetOf
  restores := carryRowProgram_yields_BlockPre bodyOffsetOf

/-! ## Public summary -/

theorem r4_carry_assembly_plan_summary :
    dispatchOpcodeReps.length = 12
    ∧ carryRows.length = 256 * 12
    ∧ (∀ bodyOffsetOf : BodyOffsetOf, (carryRestoreRegion bodyOffsetOf).length = (256 * 12) * 8)
    ∧ (∀ restoreOffsetOf bodyOffsetOf,
        R4CarryRowSegmentContract restoreOffsetOf bodyOffsetOf) := by
  exact
    ⟨ dispatchOpcodeReps_length
    , carryRows_length
    , carryRestoreRegion_length
    , r4_carry_row_segment_contract
    ⟩

end SSBX.Foundation.Wen.MetaInterp.R4CarryAssemblyPlan
