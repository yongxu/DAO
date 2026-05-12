/-
# Wen.V4Kernel.Data -- V4-native data values

This layer adds a small Lisp-shaped data carrier without importing an R backend.
Values are encoded as V4-labelled trees and keep a direct roundtrip theorem.
-/

import SSBX.Foundation.Wen.V4Kernel.Encode

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-! ## Data carrier -/

/-- V4-native data fragment: atoms, nil, and cons. -/
inductive Datum where
  | atom (g : V4)
  | nil
  | cons (head tail : Datum)
  deriving DecidableEq, Repr

namespace Datum

def size : Datum → Nat
  | .atom _ => 1
  | .nil => 1
  | .cons head tail => size head + size tail + 1

theorem size_pos (d : Datum) : 0 < size d := by
  induction d with
  | atom _ => simp [size]
  | nil => simp [size]
  | cons head tail ihHead ihTail =>
      simp [size]

def ofAtomList : List V4 → Datum
  | [] => .nil
  | g :: rest => .cons (.atom g) (ofAtomList rest)

def toTree : Datum → V4Tree
  | .atom g => .node CodeTag.atom (.atom g) V4Tree.unit
  | .nil => .node CodeTag.reservedFrame V4Tree.unit V4Tree.unit
  | .cons head tail => .node CodeTag.reservedCompound head.toTree tail.toTree

def ofTree : V4Tree → Option Datum
  | .node .dao (.atom g) (.atom .dao) => some (.atom g)
  | .node .zong (.atom .dao) (.atom .dao) => some .nil
  | .node .cuoZong head tail =>
      match ofTree head, ofTree tail with
      | some h, some t => some (.cons h t)
      | _, _ => none
  | _ => none

@[simp] theorem ofTree_toTree (d : Datum) :
    ofTree d.toTree = some d := by
  induction d with
  | atom g =>
      rfl
  | nil =>
      rfl
  | cons head tail ihHead ihTail =>
      simp [toTree, ofTree, CodeTag.reservedCompound, ihHead, ihTail]

theorem toTree_injective :
    Function.Injective toTree := by
  intro a b h
  have hdec := congrArg ofTree h
  rw [ofTree_toTree a, ofTree_toTree b] at hdec
  injection hdec

@[simp] theorem ofAtomList_nil :
    ofAtomList [] = nil := rfl

@[simp] theorem ofAtomList_cons (g : V4) (rest : List V4) :
    ofAtomList (g :: rest) = cons (atom g) (ofAtomList rest) := rfl

end Datum

/-- Pair constructor as cons with an explicit two-field reading. -/
def pairDatum (left right : Datum) : Datum :=
  .cons left (.cons right .nil)

theorem data_summary :
    (∀ d : Datum, Datum.ofTree d.toTree = some d)
    ∧ Function.Injective Datum.toTree
    ∧ Datum.ofAtomList [.cuo, .zong] =
      Datum.cons (Datum.atom .cuo) (Datum.cons (Datum.atom .zong) Datum.nil) :=
  ⟨Datum.ofTree_toTree, Datum.toTree_injective, rfl⟩

end SSBX.Foundation.Wen.V4Kernel
