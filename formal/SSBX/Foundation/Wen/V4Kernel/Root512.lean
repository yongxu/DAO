/-
# Wen.V4Kernel.Root512 -- R8 readings as V4^4 with cell/operator role

This module is the small root layer behind controlled WenScript.

* `Word64 = V4^3` remains the 64-word surface carrier.
* `RootCell256 = Word64 x V4` is the R8 cell read as four V4 axes.
* `RootReading = RootCell256 x {cell, operator}` is the 512-entry R8
  interface reading space.

The extra factor from 256 to 512 is a reading role, not a ninth ontology bit
and not another V4 factor.
-/

import SSBX.Foundation.Wen.V4Kernel.WenAction

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

namespace Root512

/-! ## Root cell carrier -/

/-- R8 read as a V4-native 256-cell carrier: `Word64 x V4 = V4^4`. -/
abbrev RootCell256 : Type := Mode16.R8View

def originCell : RootCell256 :=
  ⟨Word64.origin, .dao⟩

def ofV4Quad (a b c d : V4) : RootCell256 :=
  ⟨⟨a, b, c⟩, d⟩

def toV4Quad (cell : RootCell256) : V4 × V4 × V4 × V4 :=
  (cell.word.first, cell.word.second, cell.word.third, cell.temporal)

@[simp] theorem ofV4Quad_toV4Quad (cell : RootCell256) :
    ofV4Quad cell.word.first cell.word.second cell.word.third cell.temporal = cell := by
  cases cell with
  | mk word temporal =>
      cases word
      rfl

@[simp] theorem toV4Quad_ofV4Quad (a b c d : V4) :
    toV4Quad (ofV4Quad a b c d) = (a, b, c, d) := rfl

/-- R8 as two sixteen-mode blocks: `(V4 x V4) x (V4 x V4)`. -/
def toMode16Pair (cell : RootCell256) : Mode16 × Mode16 :=
  (⟨cell.word.first, cell.word.second⟩, ⟨cell.word.third, cell.temporal⟩)

def ofMode16Pair (pair : Mode16 × Mode16) : RootCell256 :=
  ⟨⟨pair.1.word, pair.1.temporal, pair.2.word⟩, pair.2.temporal⟩

@[simp] theorem ofMode16Pair_toMode16Pair (cell : RootCell256) :
    ofMode16Pair (toMode16Pair cell) = cell := by
  cases cell with
  | mk word temporal =>
      cases word
      rfl

@[simp] theorem toMode16Pair_ofMode16Pair (pair : Mode16 × Mode16) :
    toMode16Pair (ofMode16Pair pair) = pair := by
  rcases pair with ⟨left, right⟩
  cases left
  cases right
  rfl

def cellsForTemporal (temporal : V4) : List RootCell256 :=
  Word64.all.map fun word => ⟨word, temporal⟩

def allCells : List RootCell256 :=
  V4.all.flatMap cellsForTemporal

theorem allCells_length : allCells.length = 256 := by
  native_decide

/-- The R6/Word64 fiber embedded at temporal origin. -/
def word64Cell (word : Word64) : RootCell256 :=
  ⟨word, .dao⟩

def word64CellsAtOrigin : List RootCell256 :=
  Word64.all.map word64Cell

theorem word64CellsAtOrigin_length :
    word64CellsAtOrigin.length = 64 := by
  native_decide

/-! ## Cell/operator readings -/

/-- The two interface readings of the same R8 cell. -/
inductive ReadingKind where
  | cell
  | operator
  deriving DecidableEq, Repr

namespace ReadingKind

def all : List ReadingKind := [.cell, .operator]

theorem all_length : all.length = 2 := rfl

def label : ReadingKind → String
  | .cell => "cell"
  | .operator => "operator"

end ReadingKind

/-- One R8 cell read either as a carrier element or as an operator. -/
structure RootReading where
  cell : RootCell256
  kind : ReadingKind
  deriving DecidableEq, Repr

namespace RootReading

def label (r : RootReading) : String :=
  s!"{r.kind.label}"

end RootReading

def cellReading (cell : RootCell256) : RootReading :=
  ⟨cell, .cell⟩

def operatorReading (cell : RootCell256) : RootReading :=
  ⟨cell, .operator⟩

def readingsForCell (cell : RootCell256) : List RootReading :=
  [cellReading cell, operatorReading cell]

def allReadings : List RootReading :=
  allCells.flatMap readingsForCell

theorem allReadings_length : allReadings.length = 512 := by
  native_decide

def word64Reading (word : Word64) (kind : ReadingKind) : RootReading :=
  ⟨word64Cell word, kind⟩

def word64CellReadings : List RootReading :=
  Word64.all.map (fun word => word64Reading word .cell)

def word64OperatorReadings : List RootReading :=
  Word64.all.map (fun word => word64Reading word .operator)

theorem word64CellReadings_length :
    word64CellReadings.length = 64 := by
  native_decide

theorem word64OperatorReadings_length :
    word64OperatorReadings.length = 64 := by
  native_decide

/-- The 64-word cell surface is one eighth of the 512-entry R8 reading space. -/
theorem word64_cell_readings_one_eighth :
    word64CellReadings.length * 8 = allReadings.length := by
  native_decide

/-! ## Root-operator application -/

/-- R8 XOR/composition in the V4^4 reading. -/
def composeCell (a b : RootCell256) : RootCell256 :=
  ⟨Word64.compose a.word b.word, V4.compose a.temporal b.temporal⟩

@[simp] theorem composeCell_origin_left (cell : RootCell256) :
    composeCell originCell cell = cell := by
  cases cell with
  | mk word temporal =>
      change
        (⟨Word64.compose Word64.origin word,
          V4.compose V4.dao temporal⟩ : RootCell256) = ⟨word, temporal⟩
      rw [show Word64.compose Word64.origin word = word from Word64.compose_origin_left word,
        show V4.compose V4.dao temporal = temporal from V4.compose_dao_left temporal]

@[simp] theorem composeCell_origin_right (cell : RootCell256) :
    composeCell cell originCell = cell := by
  cases cell with
  | mk word temporal =>
      change
        (⟨Word64.compose word Word64.origin,
          V4.compose temporal V4.dao⟩ : RootCell256) = ⟨word, temporal⟩
      rw [show Word64.compose word Word64.origin = word from Word64.compose_origin_right word,
        show V4.compose temporal V4.dao = temporal from V4.compose_dao_right temporal]

@[simp] theorem composeCell_self (cell : RootCell256) :
    composeCell cell cell = originCell := by
  cases cell with
  | mk word temporal =>
      simp [composeCell, originCell, Word64.compose_self, V4.compose_self]

theorem composeCell_comm (a b : RootCell256) :
    composeCell a b = composeCell b a := by
  cases a
  cases b
  simp [composeCell, Word64.compose_comm, V4.compose_comm]

theorem composeCell_assoc (a b c : RootCell256) :
    composeCell (composeCell a b) c = composeCell a (composeCell b c) := by
  cases a
  cases b
  cases c
  simp [composeCell, Word64.compose_assoc, V4.compose_assoc]

/-- Apply a reading only when it is an operator reading. The result keeps the
argument's reading role and composes the R8 cells by V4^4 XOR. -/
def applyOperatorReading? (op arg : RootReading) : Option RootReading :=
  match op.kind with
  | .cell => none
  | .operator => some ⟨composeCell arg.cell op.cell, arg.kind⟩

@[simp] theorem apply_cellReading_none (cell arg : RootCell256) :
    applyOperatorReading? (cellReading cell) (cellReading arg) = none := rfl

@[simp] theorem apply_operatorReading_cell (mask arg : RootCell256) :
    applyOperatorReading? (operatorReading mask) (cellReading arg) =
      some (cellReading (composeCell arg mask)) := rfl

theorem operator_origin_noop (arg : RootReading) :
    applyOperatorReading? (operatorReading originCell) arg = some arg := by
  cases arg
  simp [applyOperatorReading?, operatorReading, originCell, composeCell,
    Word64.compose_origin_right, V4.compose_dao_right]

/-- Temporal root operators occupy the fourth V4 axis only. -/
def temporalOperator (g : V4) : RootReading :=
  operatorReading ⟨Word64.origin, g⟩

def originOperator : RootReading :=
  operatorReading originCell

/-- Small root-native alias set. This is not a catalogue count; these are
direct structural names for the R8 operator reading space. -/
def operatorAlias? : String → Option RootReading
  | "恒" => some originOperator
  | "恆" => some originOperator
  | "印" => some (temporalOperator .cuo)
  | "投" => some (temporalOperator .zong)
  | "印投" => some (temporalOperator .cuoZong)
  | "非" => some (operatorReading ⟨Word64.kun, .dao⟩)
  | "不" => some (operatorReading ⟨Word64.kun, .dao⟩)
  | _ => none

theorem heng_alias :
    operatorAlias? "恒" = some originOperator := rfl

theorem yin_alias :
    operatorAlias? "印" = some (temporalOperator .cuo) := rfl

theorem tou_alias :
    operatorAlias? "投" = some (temporalOperator .zong) := rfl

theorem yin_tou_alias :
    operatorAlias? "印投" = some (temporalOperator .cuoZong) := rfl

theorem negation_alias :
    operatorAlias? "非" = some (operatorReading ⟨Word64.kun, .dao⟩) := rfl

theorem bu_alias :
    operatorAlias? "不" = some (operatorReading ⟨Word64.kun, .dao⟩) := rfl

structure ApplicationTrace where
  operatorSurface : String
  operator : RootReading
  argumentSurface : String
  argument : RootReading
  result : RootReading
  deriving Repr

theorem root512_summary :
    allCells.length = 256
    ∧ allReadings.length = 512
    ∧ word64CellsAtOrigin.length = 64
    ∧ word64CellReadings.length * 8 = allReadings.length
    ∧ (∀ cell : RootCell256, ofV4Quad cell.word.first cell.word.second
        cell.word.third cell.temporal = cell)
    ∧ (∀ cell : RootCell256, ofMode16Pair (toMode16Pair cell) = cell)
    ∧ (∀ arg : RootReading,
        applyOperatorReading? (operatorReading originCell) arg = some arg)
    ∧ operatorAlias? "恒" = some originOperator
    ∧ operatorAlias? "印" = some (temporalOperator .cuo)
    ∧ operatorAlias? "投" = some (temporalOperator .zong)
    ∧ operatorAlias? "印投" = some (temporalOperator .cuoZong)
    ∧ operatorAlias? "非" = some (operatorReading ⟨Word64.kun, .dao⟩)
    ∧ operatorAlias? "不" = some (operatorReading ⟨Word64.kun, .dao⟩) :=
  ⟨allCells_length, allReadings_length, word64CellsAtOrigin_length,
   word64_cell_readings_one_eighth, ofV4Quad_toV4Quad,
   ofMode16Pair_toMode16Pair, operator_origin_noop, heng_alias,
   yin_alias, tou_alias, yin_tou_alias, negation_alias, bu_alias⟩

end Root512

end SSBX.Foundation.Wen.V4Kernel
