/-
# Wen.RKernel.LispRSpacePlan -- tree-shaped R-space representation contract

This chooses the next backend shape without importing a concrete R layer:
an R-space backend supplies a cell representation of V4, and Lisp expressions
are encoded as trees over those cells.
-/

import SSBX.Foundation.Wen.RKernel.LispRBackend

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

/-- Binary tree over a future R-space cell carrier. -/
inductive CellTree (Cell : Type) where
  | atom (cell : Cell)
  | node (tag : Cell) (left right : CellTree Cell)

/-- Future R-space carrier only needs a V4 cell codec at this layer. -/
structure LispRSpaceCarrier where
  Cell : Type
  encodeV4Cell : V4 → Cell
  decodeV4Cell : Cell → Option V4
  decode_encodeV4Cell : ∀ g, decodeV4Cell (encodeV4Cell g) = some g

namespace LispRSpaceCarrier

def encodeTree (carrier : LispRSpaceCarrier) : V4Tree → CellTree carrier.Cell
  | .atom g => .atom (carrier.encodeV4Cell g)
  | .node tag left right =>
      .node (carrier.encodeV4Cell tag) (carrier.encodeTree left) (carrier.encodeTree right)

def decodeTree (carrier : LispRSpaceCarrier) : CellTree carrier.Cell → Option V4Tree
  | .atom cell => do
      let g ← carrier.decodeV4Cell cell
      some (.atom g)
  | .node tagCell left right => do
      let tag ← carrier.decodeV4Cell tagCell
      let l ← carrier.decodeTree left
      let r ← carrier.decodeTree right
      some (.node tag l r)

@[simp] theorem decodeTree_encodeTree (carrier : LispRSpaceCarrier) (tree : V4Tree) :
    carrier.decodeTree (carrier.encodeTree tree) = some tree := by
  induction tree with
  | atom g =>
      simp [encodeTree, decodeTree, carrier.decode_encodeV4Cell]
  | node tag left right ihLeft ihRight =>
      simp [encodeTree, decodeTree, carrier.decode_encodeV4Cell, ihLeft, ihRight]

def encodeExprTree (carrier : LispRSpaceCarrier) (expr : Expr) : CellTree carrier.Cell :=
  carrier.encodeTree (encodeExpr expr)

def decodeExprTree (carrier : LispRSpaceCarrier) (code : CellTree carrier.Cell) :
    Option Expr := do
  let tree ← carrier.decodeTree code
  decodeExpr tree

@[simp] theorem decodeExprTree_encodeExprTree
    (carrier : LispRSpaceCarrier) (expr : Expr) :
    carrier.decodeExprTree (carrier.encodeExprTree expr) = some expr := by
  simp [encodeExprTree, decodeExprTree]

def encodeTopFormTree (carrier : LispRSpaceCarrier) (form : TopForm) : CellTree carrier.Cell :=
  carrier.encodeTree (encodeTopForm form)

def decodeTopFormTree (carrier : LispRSpaceCarrier) (code : CellTree carrier.Cell) :
    Option TopForm := do
  let tree ← carrier.decodeTree code
  decodeTopForm tree

@[simp] theorem decodeTopFormTree_encodeTopFormTree
    (carrier : LispRSpaceCarrier) (form : TopForm) :
    carrier.decodeTopFormTree (carrier.encodeTopFormTree form) = some form := by
  simp [encodeTopFormTree, decodeTopFormTree]

def toLispBackend (carrier : LispRSpaceCarrier) : LispBackend where
  Code := CellTree carrier.Cell
  encodeExprCode := carrier.encodeExprTree
  decodeExprCode := carrier.decodeExprTree
  decode_encodeExprCode := carrier.decodeExprTree_encodeExprTree
  encodeTopFormCode := carrier.encodeTopFormTree
  decodeTopFormCode := carrier.decodeTopFormTree
  decode_encodeTopFormCode := carrier.decodeTopFormTree_encodeTopFormTree

end LispRSpaceCarrier

/-- Reference carrier: V4 cells themselves.  Future R-space cells instantiate the same contract. -/
def v4CellCarrier : LispRSpaceCarrier where
  Cell := V4
  encodeV4Cell := id
  decodeV4Cell := some
  decode_encodeV4Cell := by
    intro g
    rfl

theorem lisp_rspace_plan_summary :
    (∀ carrier : LispRSpaceCarrier, ∀ expr : Expr,
      carrier.decodeExprTree (carrier.encodeExprTree expr) = some expr)
    ∧ (∀ carrier : LispRSpaceCarrier, ∀ form : TopForm,
      carrier.decodeTopFormTree (carrier.encodeTopFormTree form) = some form)
    ∧ (∀ fuel : Nat, ∀ expr : Expr,
      (v4CellCarrier.toLispBackend).evalCodeFuel fuel
        ((v4CellCarrier.toLispBackend).encodeExprCode expr) =
          evalFuel fuel [] expr) :=
  ⟨LispRSpaceCarrier.decodeExprTree_encodeExprTree,
    LispRSpaceCarrier.decodeTopFormTree_encodeTopFormTree,
    fun fuel expr => LispBackend.evalCodeFuel_encodeExprCode _ fuel expr⟩

end SSBX.Foundation.Wen.RKernel
