/-
# Wen.Native.Examples.Confucian -- native Wen probes for Confucian cells

This file is an executable example layer, not part of the native kernel spine.
It checks that the rank-polymorphic Wen evaluator can witness the R7 五常
placement and reject two common collapse/misreading claims.
-/

import SSBX.Foundation.Lang.Wuchang
import SSBX.Foundation.Wen.Native.Program

namespace SSBX.Foundation.Wen.Native.Examples.Confucian

open SSBX.Foundation.Wen.Layered
open SSBX.Foundation.Wen.Native

abbrev Rank : Nat := 7
abbrev C : Type := Cell Rank

def s0 : Slot Rank := ⟨0, by decide⟩
def s1 : Slot Rank := ⟨1, by decide⟩
def s2 : Slot Rank := ⟨2, by decide⟩
def s3 : Slot Rank := ⟨3, by decide⟩

/-! ## Native 五常 cells

The first four constants are the same single-line flips as
`Lang.Wuchang`; 信 is the balancing synthesis of the first four.
-/

def ren : C := Reader.cellOfBits [true, false, false, false, false, false, false]
def yi : C := Reader.cellOfBits [false, true, false, false, false, false, false]
def li : C := Reader.cellOfBits [false, false, true, false, false, false, false]
def zhi : C := Reader.cellOfBits [false, false, false, true, false, false, false]
def xin : C := Reader.cellOfBits [true, true, true, true, false, false, false]

theorem native_cells_are_single_flips :
    ren = BitSpace.single s0
    ∧ yi = BitSpace.single s1
    ∧ li = BitSpace.single s2
    ∧ zhi = BitSpace.single s3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    funext i
    fin_cases i <;> rfl

def xorExpr (left right : Expr Rank) : Expr Rank :=
  .app (.prim .xor) (Expr.list [left, right])

def eqExpr (left right : Expr Rank) : Expr Rank :=
  .app (.prim .eq) (Expr.list [left, right])

def xorCellsValue : List C → C
  | [] => originCell
  | c :: rest => BitSpace.xor c (xorCellsValue rest)

def xorCellsExpr : List C → Expr Rank
  | [] => .cell originCell
  | c :: rest => xorExpr (.cell c) (xorCellsExpr rest)

def firstFourExpr : Expr Rank :=
  xorCellsExpr [ren, yi, li, zhi]

def fiveConstantsExpr : Expr Rank :=
  xorCellsExpr [ren, yi, li, zhi, xin]

theorem firstFourValue_eq_xin :
    xorCellsValue [ren, yi, li, zhi] = xin := by
  funext i
  fin_cases i <;> rfl

theorem fiveConstantsValue_eq_origin :
    xorCellsValue [ren, yi, li, zhi, xin] = (originCell : C) := by
  funext i
  fin_cases i <;> rfl

def fiveConstantsLeftValue : C :=
  BitSpace.xor (BitSpace.xor (BitSpace.xor (BitSpace.xor ren yi) li) zhi) xin

theorem fiveConstantsLeftValue_eq_origin :
    fiveConstantsLeftValue = (originCell : C) := by
  funext i
  fin_cases i <;> rfl

theorem native_integrity_is_synthesis :
    evalFuel 40 [] firstFourExpr = some (.cell xin) := by
  change some (Value.cell (xorCellsValue [ren, yi, li, zhi])) = some (Value.cell xin)
  rw [firstFourValue_eq_xin]

theorem native_fiveConstants_return_dao :
    evalFuel 60 [] fiveConstantsExpr = some (.cell (originCell : C)) := by
  change
    some (Value.cell (xorCellsValue [ren, yi, li, zhi, xin])) =
      some (Value.cell (originCell : C))
  rw [fiveConstantsValue_eq_origin]

theorem native_fourWithoutXin_not_dao :
    evalFuel 60 [] (eqExpr firstFourExpr (.cell (originCell : C))) =
      some (.bool false) := by
  rfl

/-! ## Surface program

This is the same test through the Wen native reader/program runner.  Bare
seven-bit tokens are names; `#...` tokens are cell literals.
-/

def wuchangSurfaceProgram : List String :=
  [ "(define xoooooo #xoooooo)"
  , "(define oxooooo #oxooooo)"
  , "(define ooxoooo #ooxoooo)"
  , "(define oooxooo #oooxooo)"
  , "(define xxxxooo #xxxxooo)"
  , "(xor (xor (xor (xor xoooooo oxooooo) ooxoooo) oooxooo) xxxxooo)"
  ]

def finalCell? {n : Nat} : Option (GlobalEnv n × Value n) → Option (Cell n)
  | some (_, .cell value) => some value
  | _ => none

def wuchangSurfaceCell : Option C :=
  finalCell? (Program.readEvalProgramFinal (n := Rank) 80 [] wuchangSurfaceProgram)

theorem native_surface_wuchang_returns_dao :
    wuchangSurfaceCell = some (originCell : C) := by
  native_decide

theorem old_wuchang_reader_still_agrees :
    SSBX.Foundation.Lang.DaoJudge.judge
        SSBX.Foundation.Lang.Wuchang.fiveConstants_program = true :=
  SSBX.Foundation.Lang.Wuchang.fiveConstants_program_is_dao

/-! ## Refutations

The rejected claims are deliberately concrete:

* 仁 and 义 do not collapse to one cell.
* The traditional 五行-to-hexagram placement cannot be read as a direct
  `(Z/2)^7` balancing program; in this carrier it leaves 礼 as residue.
-/

def renEqualsYiClaim : Prop :=
  evalFuel 20 [] (eqExpr (.cell ren) (.cell yi)) = some (.bool true)

theorem refute_ren_equals_yi : ¬ renEqualsYiClaim := by
  intro h
  change some (Value.bool false : Value Rank) = some (.bool true) at h
  cases h

def tradRen : C := Reader.cellOfBits [false, true, true, false, true, true, false]
def tradYi : C := Reader.cellOfBits [false, false, true, false, false, true, false]
def tradLi : C := Reader.cellOfBits [false, true, false, false, true, false, false]
def tradZhi : C := Reader.cellOfBits [true, false, true, true, false, true, false]
def tradXin : C := Reader.cellOfBits [true, true, true, true, true, true, false]

def traditionalFivePhaseExpr : Expr Rank :=
  xorCellsExpr [tradRen, tradYi, tradLi, tradZhi, tradXin]

theorem traditionalFivePhaseValue_eq_li :
    xorCellsValue [tradRen, tradYi, tradLi, tradZhi, tradXin] = tradLi := by
  funext i
  fin_cases i <;> rfl

theorem refute_traditional_direct_map_returns_dao :
    evalFuel 60 [] (eqExpr traditionalFivePhaseExpr (.cell (originCell : C))) =
      some (.bool false) := by
  rfl

theorem traditional_direct_map_leaves_li :
    evalFuel 60 [] traditionalFivePhaseExpr = some (.cell tradLi) := by
  change
    some (Value.cell (xorCellsValue [tradRen, tradYi, tradLi, tradZhi, tradXin])) =
      some (Value.cell tradLi)
  rw [traditionalFivePhaseValue_eq_li]

theorem native_confucian_probe_summary :
    evalFuel 40 [] firstFourExpr = some (.cell xin)
    ∧ evalFuel 60 [] fiveConstantsExpr = some (.cell (originCell : C))
    ∧ wuchangSurfaceCell = some (originCell : C)
    ∧ ¬ renEqualsYiClaim
    ∧ evalFuel 60 [] traditionalFivePhaseExpr = some (.cell tradLi) :=
  ⟨native_integrity_is_synthesis,
   native_fiveConstants_return_dao,
   native_surface_wuchang_returns_dao,
   refute_ren_equals_yi,
   traditional_direct_map_leaves_li⟩

end SSBX.Foundation.Wen.Native.Examples.Confucian
