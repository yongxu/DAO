/-
# Wen.Native.Bridges.RootCell256 -- RootCell256 as native rank-8 Wen data
-/

import SSBX.Foundation.Wen.Native.Eval
import SSBX.Foundation.Wen.Layered.Bridges.RootCell256

namespace SSBX.Foundation.Wen.Native.Bridges.RootCell256

open SSBX.Foundation.Wen.Layered

abbrev Carrier : Type := SSBX.Foundation.Wen.Layered.Bridges.RootCell256.Carrier

def toCell (cell : Carrier) : Cell 8 :=
  SSBX.Foundation.Wen.Layered.Bridges.RootCell256.toBitSpace cell

def fromCell (cell : Cell 8) : Carrier :=
  SSBX.Foundation.Wen.Layered.Bridges.RootCell256.fromBitSpace cell

def expr (cell : Carrier) : Expr 8 :=
  .cell (toCell cell)

def value (cell : Carrier) : Value 8 :=
  .cell (toCell cell)

def fromValue? : Value 8 → Option Carrier
  | .cell cell => some (fromCell cell)
  | _ => none

def xorExpr (a b : Carrier) : Expr 8 :=
  .app (.prim .xor) (Expr.list [expr a, expr b])

def toExistingR8 (cell : Carrier) : SSBX.Foundation.Bagua.R8.R8 :=
  SSBX.Foundation.Wen.Layered.Bridges.RootCell256.toExistingR8 cell

def fromExistingR8 (cell : SSBX.Foundation.Bagua.R8.R8) : Carrier :=
  SSBX.Foundation.Wen.Layered.Bridges.RootCell256.fromExistingR8 cell

@[simp] theorem fromCell_toCell (cell : Carrier) :
    fromCell (toCell cell) = cell := by
  simp [fromCell, toCell]

@[simp] theorem toCell_fromCell (cell : Cell 8) :
    toCell (fromCell cell) = cell := by
  simp [fromCell, toCell]

@[simp] theorem fromValue_value (cell : Carrier) :
    fromValue? (value cell) = some cell := by
  simp [fromValue?, value, fromCell, toCell]

@[simp] theorem toExistingR8_fromExistingR8
    (cell : SSBX.Foundation.Bagua.R8.R8) :
    toExistingR8 (fromExistingR8 cell) = cell := by
  exact SSBX.Foundation.Wen.Layered.Bridges.RootCell256.toExistingR8_fromExistingR8 cell

@[simp] theorem fromExistingR8_toExistingR8 (cell : Carrier) :
    fromExistingR8 (toExistingR8 cell) = cell := by
  exact SSBX.Foundation.Wen.Layered.Bridges.RootCell256.fromExistingR8_toExistingR8 cell

theorem eval_xor (a b : Carrier) :
    evalFuel 8 [] (xorExpr a b) =
      some (value (SSBX.Foundation.Wen.RKernel.Root512.composeCell a b)) := by
  change
    some (Value.cell (BitSpace.xor
      (SSBX.Foundation.Wen.Layered.Bridges.RootCell256.toBitSpace a)
      (SSBX.Foundation.Wen.Layered.Bridges.RootCell256.toBitSpace b))) =
      some (Value.cell (SSBX.Foundation.Wen.Layered.Bridges.RootCell256.toBitSpace
        (SSBX.Foundation.Wen.RKernel.Root512.composeCell a b)))
  rw [← SSBX.Foundation.Wen.Layered.Bridges.RootCell256.toBitSpace_xor a b]

theorem bridge_laws :
    (∀ cell : Carrier, fromValue? (value cell) = some cell)
    ∧ (∀ a b : Carrier,
      evalFuel 8 [] (xorExpr a b) =
        some (value (SSBX.Foundation.Wen.RKernel.Root512.composeCell a b)))
    ∧ (∀ cell : SSBX.Foundation.Bagua.R8.R8,
      toExistingR8 (fromExistingR8 cell) = cell)
    ∧ (∀ cell : Carrier, fromExistingR8 (toExistingR8 cell) = cell) :=
  ⟨fromValue_value, eval_xor, toExistingR8_fromExistingR8,
    fromExistingR8_toExistingR8⟩

end SSBX.Foundation.Wen.Native.Bridges.RootCell256
