/-
# Wen.Native.Bridges.Word64 -- R6 Word64 as native rank-6 Wen data
-/

import SSBX.Foundation.Wen.Native.Eval
import SSBX.Foundation.Wen.Layered.Bridges.Word64

namespace SSBX.Foundation.Wen.Native.Bridges.Word64

open SSBX.Foundation.Wen.Layered

abbrev Carrier : Type := SSBX.Foundation.Wen.Layered.Bridges.Word64.Carrier

def toCell (word : Carrier) : Cell 6 :=
  SSBX.Foundation.Wen.Layered.Bridges.Word64.toBitSpace word

def fromCell (cell : Cell 6) : Carrier :=
  SSBX.Foundation.Wen.Layered.Bridges.Word64.fromBitSpace cell

def expr (word : Carrier) : Expr 6 :=
  .cell (toCell word)

def value (word : Carrier) : Value 6 :=
  .cell (toCell word)

def fromValue? : Value 6 → Option Carrier
  | .cell cell => some (fromCell cell)
  | _ => none

def xorExpr (a b : Carrier) : Expr 6 :=
  .app (.prim .xor) (Expr.list [expr a, expr b])

@[simp] theorem fromCell_toCell (word : Carrier) :
    fromCell (toCell word) = word := by
  simp [fromCell, toCell]

@[simp] theorem toCell_fromCell (cell : Cell 6) :
    toCell (fromCell cell) = cell := by
  simp [fromCell, toCell]

@[simp] theorem fromValue_value (word : Carrier) :
    fromValue? (value word) = some word := by
  simp [fromValue?, value, fromCell, toCell]

theorem eval_xor (a b : Carrier) :
    evalFuel 8 [] (xorExpr a b) =
      some (value (SSBX.Foundation.Wen.V4Kernel.Word64.compose a b)) := by
  change
    some (Value.cell (BitSpace.xor
      (SSBX.Foundation.Wen.Layered.Bridges.Word64.toBitSpace a)
      (SSBX.Foundation.Wen.Layered.Bridges.Word64.toBitSpace b))) =
      some (Value.cell (SSBX.Foundation.Wen.Layered.Bridges.Word64.toBitSpace
        (SSBX.Foundation.Wen.V4Kernel.Word64.compose a b)))
  rw [← SSBX.Foundation.Wen.Layered.Bridges.Word64.toBitSpace_xor a b]

theorem eval_qian_kun :
    evalFuel 8 [] (xorExpr
      SSBX.Foundation.Wen.V4Kernel.Word64.qian
      SSBX.Foundation.Wen.V4Kernel.Word64.kun) =
      some (value SSBX.Foundation.Wen.V4Kernel.Word64.kun) := by
  rw [eval_xor]
  rfl

theorem bridge_laws :
    (∀ word : Carrier, fromValue? (value word) = some word)
    ∧ (∀ a b : Carrier,
      evalFuel 8 [] (xorExpr a b) =
        some (value (SSBX.Foundation.Wen.V4Kernel.Word64.compose a b)))
    ∧ evalFuel 8 [] (xorExpr
      SSBX.Foundation.Wen.V4Kernel.Word64.qian
      SSBX.Foundation.Wen.V4Kernel.Word64.kun) =
      some (value SSBX.Foundation.Wen.V4Kernel.Word64.kun) :=
  ⟨fromValue_value, eval_xor, eval_qian_kun⟩

end SSBX.Foundation.Wen.Native.Bridges.Word64
