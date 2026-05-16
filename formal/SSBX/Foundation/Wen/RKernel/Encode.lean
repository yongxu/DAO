/-
# Wen.RKernel.Encode -- quoting V4 terms as V4 trees

The code format uses only V4 labels:

- `dao` node: atom payload, with `unit` right padding.
- `cuo` node: composition, with left/right subprograms.

The remaining V4 tags are reserved for future syntax extension.
-/

import SSBX.Foundation.Wen.RKernel.Semantics

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

namespace CodeTag

def atom : V4 := .dao
def compose : V4 := .cuo
def reservedFrame : V4 := .zong
def reservedCompound : V4 := .cuoZong

end CodeTag

/-- Encode an object-language term as a V4-labelled tree. -/
def encodeTerm : Term → V4Tree
  | .atom g => .node CodeTag.atom (.atom g) V4Tree.unit
  | .compose left right => .node CodeTag.compose (encodeTerm left) (encodeTerm right)

/-- Decode the current V4 term fragment from a V4-labelled tree. -/
def decodeTerm : V4Tree → Option Term
  | .node .dao (.atom g) (.atom .dao) => some (.atom g)
  | .node .cuo left right =>
      match decodeTerm left, decodeTerm right with
      | some l, some r => some (.compose l r)
      | _, _ => none
  | _ => none

@[simp] theorem decode_encodeTerm (t : Term) :
    decodeTerm (encodeTerm t) = some t := by
  induction t with
  | atom g =>
      rfl
  | compose left right ihLeft ihRight =>
      simp [encodeTerm, decodeTerm, CodeTag.compose, ihLeft, ihRight]

theorem encodeTerm_injective :
    Function.Injective encodeTerm := by
  intro a b h
  have hdec := congrArg decodeTerm h
  rw [decode_encodeTerm a, decode_encodeTerm b] at hdec
  injection hdec

theorem encode_summary :
    (∀ t : Term, decodeTerm (encodeTerm t) = some t)
    ∧ Function.Injective encodeTerm :=
  ⟨decode_encodeTerm, encodeTerm_injective⟩

end SSBX.Foundation.Wen.RKernel
