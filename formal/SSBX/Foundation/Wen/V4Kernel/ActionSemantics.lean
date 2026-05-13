/-
# Wen.V4Kernel.ActionSemantics -- V4/R8 action semantics

This is the reusable action layer below WenScript claims.  It keeps the
domain actions separate:

* V4 acts on the R6/Word64 carrier through the canonical hexagram duals.
* Mode16 acts on the V4-native Word64/R8 coordinate view.
* Root512 operators act on Root512 readings by R8 cell composition.

The unresolved cases stay explicit; they are traceable surface material, not
semantic execution.
-/

import SSBX.Foundation.Wen.V4Kernel.Root512
import SSBX.Foundation.Wen.V4Kernel.WenR6

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-- Minimal terms that the action layer knows how to audit or execute. -/
inductive SemanticTerm where
  | word64 (word : Word64)
  | r5 (view : R5View)
  | root (reading : Root512.RootReading)
  | unresolved (surface : String)
  deriving DecidableEq, Repr

/-- Minimal operators that can act on semantic terms. -/
inductive SemanticOperator where
  | v4 (g : V4)
  | mode16 (mode : Mode16)
  | root (reading : Root512.RootReading)
  | unresolved (surface : String)
  deriving DecidableEq, Repr

namespace ActionSemantics

def mode16RootCell (mode : Mode16) : Root512.RootCell256 :=
  ⟨⟨mode.word, mode.word, mode.word⟩, mode.temporal⟩

def mode16RootOperator (mode : Mode16) : Root512.RootReading :=
  Root512.operatorReading (mode16RootCell mode)

def rootMapWord (f : Word64 → Word64) (reading : Root512.RootReading) :
    Root512.RootReading :=
  ⟨⟨f reading.cell.word, reading.cell.temporal⟩, reading.kind⟩

def rootMapView (f : Root512.RootCell256 → Root512.RootCell256)
    (reading : Root512.RootReading) : Root512.RootReading :=
  ⟨f reading.cell, reading.kind⟩

namespace SemanticTerm

/-- Root512 readings touched by this term.  Unresolved surface material has no
root footprint yet. -/
def footprint : SemanticTerm → List Root512.RootReading
  | .word64 word => [Root512.word64Reading word .cell]
  | .r5 view => [Root512.word64Reading (R5View.toWord64 view) .cell]
  | .root reading => [reading]
  | .unresolved _ => []

@[simp] theorem footprint_unresolved (surface : String) :
    footprint (.unresolved surface) = [] := rfl

@[simp] theorem footprint_word64 (word : Word64) :
    footprint (.word64 word) = [Root512.word64Reading word .cell] := rfl

end SemanticTerm

namespace SemanticOperator

/-- Root512 readings directly touched by this operator.  V4/R6 duals are not
collapsed to a single Root512 mask, since frame reversal is not an R8 XOR mask
in general. -/
def footprint : SemanticOperator → List Root512.RootReading
  | .v4 _ => []
  | .mode16 mode => [mode16RootOperator mode]
  | .root reading => [reading]
  | .unresolved _ => []

def alias? (surface : String) : Option SemanticOperator :=
  (Root512.operatorAlias? surface).map SemanticOperator.root

@[simp] theorem footprint_unresolved (surface : String) :
    footprint (.unresolved surface) = [] := rfl

@[simp] theorem alias_heng :
    alias? "恒" = some (.root Root512.originOperator) := rfl

@[simp] theorem alias_yin :
    alias? "印" = some (.root (Root512.temporalOperator .cuo)) := rfl

@[simp] theorem alias_tou :
    alias? "投" = some (.root (Root512.temporalOperator .zong)) := rfl

@[simp] theorem alias_yin_tou :
    alias? "印投" = some (.root (Root512.temporalOperator .cuoZong)) := rfl

end SemanticOperator

open SemanticTerm SemanticOperator

/-- Execute one semantic operator on one semantic term when the carrier is
known.  R5 terms are lifted to the Word64 carrier before action. -/
def apply? : SemanticOperator → SemanticTerm → Option SemanticTerm
  | .v4 g, .word64 word => some (.word64 (R6View.dual g word))
  | .v4 g, .r5 view => some (.word64 (R6View.dual g (R5View.toWord64 view)))
  | .v4 g, .root reading => some (.root (rootMapWord (R6View.dual g) reading))
  | .mode16 mode, .word64 word => some (.word64 (Mode16.actWord mode word))
  | .mode16 mode, .r5 view =>
      some (.word64 (Mode16.actWord mode (R5View.toWord64 view)))
  | .mode16 mode, .root reading =>
      some (.root (rootMapView (Mode16.actView mode) reading))
  | .root op, .word64 word =>
      (Root512.applyOperatorReading? op (Root512.word64Reading word .cell)).map
        SemanticTerm.root
  | .root op, .r5 view =>
      (Root512.applyOperatorReading? op
        (Root512.word64Reading (R5View.toWord64 view) .cell)).map
        SemanticTerm.root
  | .root op, .root reading =>
      (Root512.applyOperatorReading? op reading).map SemanticTerm.root
  | .unresolved _, _ => none
  | _, .unresolved _ => none

/-- Compose operators when their action families have a closed composition law.
Mixed-family composition is intentionally left undefined. -/
def composeOperator? : SemanticOperator → SemanticOperator → Option SemanticOperator
  | .v4 a, .v4 b => some (.v4 (V4.compose a b))
  | .mode16 a, .mode16 b => some (.mode16 (Mode16.compose a b))
  | .root a, .root b =>
      match a.kind, b.kind with
      | .operator, .operator =>
          some (.root (Root512.operatorReading
            (Root512.composeCell a.cell b.cell)))
      | _, _ => none
  | _, _ => none

@[simp] theorem apply_v4_dao_word64 (word : Word64) :
    apply? (.v4 .dao) (.word64 word) = some (.word64 word) := rfl

theorem apply_v4_self_inverse_word64 (g : V4) (word : Word64) :
    apply? (.v4 g) (.word64 (R6View.dual g word)) = some (.word64 word) := by
  simp [apply?]

theorem apply_v4_compose_word64 (a b : V4) (word : Word64) :
    apply? (.v4 (V4.compose a b)) (.word64 word) =
      (apply? (.v4 b) (.word64 word)).bind (apply? (.v4 a)) := by
  simp [apply?, R6View.dual_compose]

@[simp] theorem apply_v4_cuo_qian :
    apply? (.v4 .cuo) (.word64 Word64.qian) =
      some (.word64 Word64.kun) := rfl

@[simp] theorem apply_v4_zong_complete :
    apply? (.v4 .zong) (.word64 Word64.complete) =
      some (.word64 Word64.incomplete) := rfl

@[simp] theorem apply_v4_cuoZong_incomplete :
    apply? (.v4 .cuoZong) (.word64 Word64.incomplete) =
      some (.word64 Word64.incomplete) := rfl

@[simp] theorem apply_mode16_identity_word64 (word : Word64) :
    apply? (.mode16 Mode16.identity) (.word64 word) = some (.word64 word) := by
  simp [apply?]

theorem apply_mode16_compose_word64 (a b : Mode16) (word : Word64) :
    apply? (.mode16 (Mode16.compose a b)) (.word64 word) =
      (apply? (.mode16 b) (.word64 word)).bind (apply? (.mode16 a)) := by
  simp [apply?, Mode16.actWord_compose]

@[simp] theorem apply_mode16_r5_origin_content :
    apply? (.mode16 (Mode16.pureWord .cuo)) (.r5 R5View.origin) =
      some (.word64 Word64.incomplete) := rfl

@[simp] theorem apply_root_cell_operator_fails
    (cell arg : Root512.RootCell256) :
    apply? (.root (Root512.cellReading cell)) (.root (Root512.cellReading arg)) =
      none := rfl

@[simp] theorem apply_root_operator_cell
    (mask arg : Root512.RootCell256) :
    apply? (.root (Root512.operatorReading mask)) (.root (Root512.cellReading arg)) =
      some (.root (Root512.cellReading (Root512.composeCell arg mask))) := rfl

theorem apply_root_origin_noop (arg : Root512.RootReading) :
    apply? (.root Root512.originOperator) (.root arg) = some (.root arg) := by
  change (Root512.applyOperatorReading? Root512.originOperator arg).map
      SemanticTerm.root = some (.root arg)
  unfold Root512.originOperator
  rw [Root512.operator_origin_noop]
  rfl

@[simp] theorem apply_unresolved_operator_none
    (surface : String) (term : SemanticTerm) :
    apply? (.unresolved surface) term = none := by
  cases term <;> rfl

@[simp] theorem apply_unresolved_term_none
    (op : SemanticOperator) (surface : String) :
    apply? op (.unresolved surface) = none := by
  cases op <;> rfl

@[simp] theorem composeOperator_v4 (a b : V4) :
    composeOperator? (.v4 a) (.v4 b) = some (.v4 (V4.compose a b)) := rfl

@[simp] theorem composeOperator_mode16 (a b : Mode16) :
    composeOperator? (.mode16 a) (.mode16 b) =
      some (.mode16 (Mode16.compose a b)) := rfl

@[simp] theorem composeOperator_root_operator
    (a b : Root512.RootCell256) :
    composeOperator? (.root (Root512.operatorReading a))
        (.root (Root512.operatorReading b)) =
      some (.root (Root512.operatorReading (Root512.composeCell a b))) := rfl

@[simp] theorem composeOperator_mixed_none (g : V4) (mode : Mode16) :
    composeOperator? (.v4 g) (.mode16 mode) = none := rfl

theorem action_semantics_summary :
    apply? (.v4 .cuo) (.word64 Word64.qian) = some (.word64 Word64.kun)
    ∧ apply? (.v4 .zong) (.word64 Word64.complete) =
      some (.word64 Word64.incomplete)
    ∧ apply? (.v4 .cuoZong) (.word64 Word64.incomplete) =
      some (.word64 Word64.incomplete)
    ∧ apply? (.mode16 (Mode16.pureWord .cuo)) (.r5 R5View.origin) =
      some (.word64 Word64.incomplete)
    ∧ (∀ arg : Root512.RootReading,
        apply? (.root Root512.originOperator) (.root arg) = some (.root arg))
    ∧ SemanticOperator.alias? "恒" = some (.root Root512.originOperator)
    ∧ SemanticOperator.alias? "印" =
      some (.root (Root512.temporalOperator .cuo)) :=
  ⟨apply_v4_cuo_qian, apply_v4_zong_complete,
   apply_v4_cuoZong_incomplete, apply_mode16_r5_origin_content,
   apply_root_origin_noop, SemanticOperator.alias_heng,
   SemanticOperator.alias_yin⟩

end ActionSemantics

end SSBX.Foundation.Wen.V4Kernel
