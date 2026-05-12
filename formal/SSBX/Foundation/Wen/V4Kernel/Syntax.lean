/-
# Wen.V4Kernel.Syntax -- free syntax over the V4 alphabet

This is the small interpreter kernel root.  V4 is the alphabet; programs and
quoted programs live in free tree structure over that alphabet.  No R5-R8 or
Cell256 backend is imported here.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Core

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-! ## Object-language terms -/

/-- The first V4 expression fragment: atoms and V4 composition. -/
inductive Term where
  | atom (g : V4)
  | compose (left right : Term)
  deriving DecidableEq, Repr

namespace Term

def size : Term → Nat
  | .atom _ => 1
  | .compose left right => size left + size right + 1

theorem size_pos (t : Term) : 0 < size t := by
  induction t with
  | atom _ => simp [size]
  | compose left right ihLeft ihRight =>
      simp [size]

end Term

/-! ## Quoted syntax carrier -/

/-- Free binary tree over V4.  This is the carrier for quoted programs. -/
inductive V4Tree where
  | atom (g : V4)
  | node (tag : V4) (left right : V4Tree)
  deriving DecidableEq, Repr

namespace V4Tree

/-- Canonical empty/right-padding witness used by the encoder. -/
def unit : V4Tree := .atom .dao

def size : V4Tree → Nat
  | .atom _ => 1
  | .node _ left right => size left + size right + 1

theorem size_pos (t : V4Tree) : 0 < size t := by
  induction t with
  | atom _ => simp [size]
  | node _ left right ihLeft ihRight =>
      simp [size]

end V4Tree

theorem syntax_summary :
    (∀ t : Term, 0 < t.size)
    ∧ (∀ q : V4Tree, 0 < q.size)
    ∧ V4Tree.unit = V4Tree.atom V4.dao :=
  ⟨Term.size_pos, V4Tree.size_pos, rfl⟩

end SSBX.Foundation.Wen.V4Kernel
