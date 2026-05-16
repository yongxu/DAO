/-
# Wen.RKernel.Root512 -- R8 readings as V4^4 with cell/operator role

This module is the small root layer behind controlled WenScript.

* `Word64 = V4^3` remains the 64-word surface carrier.
* `RootCell256 = Word64 x V4` is the R8 cell read as four V4 axes.
* `RootReading = RootCell256 x {cell, operator}` is the 512-entry R8
  interface reading space.

The extra factor from 256 to 512 is a reading role, not a ninth ontology bit
and not another V4 factor.
-/

import SSBX.Foundation.Wen.RKernel.WenAction

namespace SSBX.Foundation.Wen.RKernel

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

/-! ## § Bridge to R 8 — RootCell256 ≃ R 8 (the V4⁴ carrier)

Per `wen-substrate.md` v1.4 §3.7.8 (distinction monism), the R-family is the
**one mathematical core**.  `RootCell256` = `Word64 × V4` is mathematically
`V4⁴ ≅ R 8 = Fin 8 → Bool`, the algebraic-class realisation at level 8 of the
R-tower (the byte-ceiling).  The extra {cell, operator} reading factor that
takes 256 → 512 in `RootReading` is a meta-tag, *not* a ninth distinction
bit; it stays separate from the R-family substrate.  This section proves the
256-cell equivalence explicitly.  Coordinates 0..5 are the Word64 axes via
`Word64.toR6`; coordinates 6,7 are the temporal V4 axis. -/

open SSBX.Foundation.R in
/-- Project `RootCell256` to `R 8` via `Word64 ≃ R 6` on the word part
    and `V4 ≃ R 2` on the temporal part. -/
def RootCell256.toR8 (c : RootCell256) : R 8 := fun i =>
  if h : i.val < 6 then Word64.toR6 c.word ⟨i.val, h⟩
  else V4.toR2 c.temporal ⟨i.val - 6, by omega⟩

open SSBX.Foundation.R in
/-- Lift `R 8` to `RootCell256` via `R 6 ≃ Word64` on the (0..5) block and
    `R 2 ≃ V4` on the (6,7) block. -/
def RootCell256.ofR8 (v : R 8) : RootCell256 :=
  ⟨Word64.ofR6 (fun i => v ⟨i.val, by omega⟩),
   V4.ofR2 (fun i => v ⟨i.val + 6, by omega⟩)⟩

theorem RootCell256.ofR8_toR8 (c : RootCell256) :
    RootCell256.ofR8 (RootCell256.toR8 c) = c := by
  obtain ⟨w, t⟩ := c
  -- prove the word and temporal halves separately
  have hword : Word64.ofR6 (fun i => RootCell256.toR8 ⟨w, t⟩ ⟨i.val, by omega⟩) = w := by
    have heq : (fun i : Fin 6 => RootCell256.toR8 ⟨w, t⟩ ⟨i.val, by omega⟩)
                = Word64.toR6 w := by
      funext i
      have hi : i.val < 6 := i.isLt
      simp [RootCell256.toR8, hi]
    rw [heq, Word64.ofR6_toR6]
  have htemp : V4.ofR2 (fun i => RootCell256.toR8 ⟨w, t⟩ ⟨i.val + 6, by omega⟩) = t := by
    have heq : (fun i : Fin 2 => RootCell256.toR8 ⟨w, t⟩ ⟨i.val + 6, by omega⟩)
                = V4.toR2 t := by
      funext i
      have hi : ¬ (i.val + 6 < 6) := by omega
      simp [RootCell256.toR8, hi]
    rw [heq, V4.ofR2_toR2]
  show Mode16.R8View.mk _ _ = ⟨w, t⟩
  rw [hword, htemp]

open SSBX.Foundation.R in
theorem RootCell256.toR8_ofR8 (v : R 8) :
    RootCell256.toR8 (RootCell256.ofR8 v) = v := by
  funext i
  simp only [RootCell256.toR8, RootCell256.ofR8]
  by_cases h : i.val < 6
  · simp only [h, dif_pos]
    have hroundtrip := Word64.toR6_ofR6 (fun j : Fin 6 => v ⟨j.val, by omega⟩)
    have hi : Word64.toR6 (Word64.ofR6 (fun j : Fin 6 => v ⟨j.val, by omega⟩))
                ⟨i.val, h⟩ = v ⟨i.val, by omega⟩ := by
      rw [hroundtrip]
    convert hi using 2
  · simp only [h, dif_neg, not_false_eq_true]
    have hi6 : i.val - 6 < 2 := by have := i.isLt; omega
    have hroundtrip := V4.toR2_ofR2 (fun j : Fin 2 => v ⟨j.val + 6, by omega⟩)
    have hi : V4.toR2 (V4.ofR2 (fun j : Fin 2 => v ⟨j.val + 6, by omega⟩))
                ⟨i.val - 6, hi6⟩ = v ⟨(i.val - 6) + 6, by omega⟩ := by
      rw [hroundtrip]
    have hsub : (i.val - 6) + 6 = i.val := by omega
    rw [hi]
    congr 1
    apply Fin.ext
    exact hsub

open SSBX.Foundation.R in
/-- `RootCell256 ≃ R 8` — the R-family canonical reading at level 8 (the
    byte ceiling).  Per `wen-substrate.md` v1.4 §3.7.8 distinction monism.

    The {cell, operator} reading factor of `RootReading` stays as a meta-tag
    separate from this substrate equivalence. -/
def RootCell256.equivR8 : RootCell256 ≃ R 8 where
  toFun := RootCell256.toR8
  invFun := RootCell256.ofR8
  left_inv := RootCell256.ofR8_toR8
  right_inv := RootCell256.toR8_ofR8

end Root512

end SSBX.Foundation.Wen.RKernel
