/-
# Wen.Native.Bridges.R8 -- existing R8 as native rank-8 Wen data
-/

import SSBX.Foundation.Wen.Native.Eval
import SSBX.Foundation.Wen.Layered.Bridges.R8

namespace SSBX.Foundation.Wen.Native.Bridges.R8

open SSBX.Foundation.Wen.Layered

abbrev Carrier : Type := SSBX.Foundation.Wen.Layered.Bridges.R8.Carrier

def toCell (cell : Carrier) : Cell 8 :=
  SSBX.Foundation.Wen.Layered.Bridges.R8.toBitSpace cell

def fromCell (cell : Cell 8) : Carrier :=
  SSBX.Foundation.Wen.Layered.Bridges.R8.fromBitSpace cell

def expr (cell : Carrier) : Expr 8 :=
  .cell (toCell cell)

def value (cell : Carrier) : Value 8 :=
  .cell (toCell cell)

def fromValue? : Value 8 → Option Carrier
  | .cell cell => some (fromCell cell)
  | _ => none

def xorExpr (a b : Carrier) : Expr 8 :=
  .app (.prim .xor) (Expr.list [expr a, expr b])

@[simp] theorem fromCell_toCell (cell : Carrier) :
    fromCell (toCell cell) = cell := by
  simp [fromCell, toCell]

@[simp] theorem toCell_fromCell (cell : Cell 8) :
    toCell (fromCell cell) = cell := by
  simp [fromCell, toCell]

@[simp] theorem fromValue_value (cell : Carrier) :
    fromValue? (value cell) = some cell := by
  simp [fromValue?, value, fromCell, toCell]

theorem eval_xor (a b : Carrier) :
    evalFuel 8 [] (xorExpr a b) =
      some (value (SSBX.Foundation.Bagua.R8.R8.xor a b)) := by
  change
    some (Value.cell (BitSpace.xor
      (SSBX.Foundation.Wen.Layered.Bridges.R8.toBitSpace a)
      (SSBX.Foundation.Wen.Layered.Bridges.R8.toBitSpace b))) =
      some (Value.cell
        (SSBX.Foundation.Wen.Layered.Bridges.R8.toBitSpace
          (SSBX.Foundation.Bagua.R8.R8.xor a b)))
  rw [← SSBX.Foundation.Wen.Layered.Bridges.R8.toBitSpace_xor a b]

theorem bridge_laws :
    (∀ cell : Carrier, fromValue? (value cell) = some cell)
    ∧ (∀ a b : Carrier,
      evalFuel 8 [] (xorExpr a b) =
        some (value (SSBX.Foundation.Bagua.R8.R8.xor a b))) :=
  ⟨fromValue_value, eval_xor⟩

end SSBX.Foundation.Wen.Native.Bridges.R8
