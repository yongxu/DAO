/-
# Wen.Native.Bridges.V4 -- V4 as native rank-2 Wen data

This file uses `V4` from `Foundation/Hierarchy/Operators/V4/Core.lean`,
which is the constructor-style presentation of `R 2` per
`wen-substrate.md` v1.4 §3.7.8 (distinction monism).  The R-family is the
one mathematical core; `V4` here is the ergonomic 4-constructor surface
over `R 2 = Fin 2 → Bool`.

The native interpreter remains generic over `Expr n`.  This module is only an
adapter from the existing Klein-four carrier into `Expr 2` / `Value 2`.
The rank-2 native Wen data is therefore a direct embedding of `R 2`.
-/

import SSBX.Foundation.Wen.Native.Eval
import SSBX.Foundation.Wen.Layered.Bridges.V4

namespace SSBX.Foundation.Wen.Native.Bridges.V4

open SSBX.Foundation.Wen.Layered

abbrev Carrier : Type := SSBX.Foundation.Wen.Layered.Bridges.V4.Carrier

def toCell (g : Carrier) : Cell 2 :=
  SSBX.Foundation.Wen.Layered.Bridges.V4.toBitSpace g

def fromCell (cell : Cell 2) : Carrier :=
  SSBX.Foundation.Wen.Layered.Bridges.V4.fromBitSpace cell

def expr (g : Carrier) : Expr 2 :=
  .cell (toCell g)

def value (g : Carrier) : Value 2 :=
  .cell (toCell g)

def fromValue? : Value 2 → Option Carrier
  | .cell cell => some (fromCell cell)
  | _ => none

def xorExpr (a b : Carrier) : Expr 2 :=
  .app (.prim .xor) (Expr.list [expr a, expr b])

@[simp] theorem fromCell_toCell (g : Carrier) :
    fromCell (toCell g) = g := by
  simp [fromCell, toCell]

@[simp] theorem toCell_fromCell (cell : Cell 2) :
    toCell (fromCell cell) = cell := by
  simp [fromCell, toCell]

@[simp] theorem fromValue_value (g : Carrier) :
    fromValue? (value g) = some g := by
  simp [fromValue?, value, fromCell, toCell]

theorem eval_xor (a b : Carrier) :
    evalFuel 8 [] (xorExpr a b) =
      some (value (SSBX.Foundation.Hierarchy.Operators.V4.compose a b)) := by
  change
    some (Value.cell (BitSpace.xor
      (SSBX.Foundation.Wen.Layered.Bridges.V4.toBitSpace a)
      (SSBX.Foundation.Wen.Layered.Bridges.V4.toBitSpace b))) =
      some (Value.cell (SSBX.Foundation.Wen.Layered.Bridges.V4.toBitSpace
        (SSBX.Foundation.Hierarchy.Operators.V4.compose a b)))
  rw [← SSBX.Foundation.Wen.Layered.Bridges.V4.toBitSpace_xor a b]

theorem bridge_laws :
    (∀ g : Carrier, fromValue? (value g) = some g)
    ∧ (∀ a b : Carrier,
      evalFuel 8 [] (xorExpr a b) =
        some (value (SSBX.Foundation.Hierarchy.Operators.V4.compose a b))) :=
  ⟨fromValue_value, eval_xor⟩

end SSBX.Foundation.Wen.Native.Bridges.V4
