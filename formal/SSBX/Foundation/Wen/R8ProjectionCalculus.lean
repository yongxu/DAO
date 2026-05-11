/-
# R8ProjectionCalculus — Wen expressions projected into the R8 closure

This module records the typed skeleton for the doctrine claim:

* a sentence is first rewritten into a Wen normal form;
* a chosen interpreter maps that Wen form into an R8 semantic shape;
* every such shape has a visible R8 projection;
* higher-than-R8 material can be projected to R8 only with an explicit loss
  ledger;
* returning to Way is a predicate on the visible R8 result, not a claim that
  full natural-language meaning has been exhausted.

It intentionally does not define a complete natural-language semantics.
-/
import SSBX.Foundation.Bagua.R8

namespace SSBX.Foundation.Wen.R8ProjectionCalculus

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8

/-! ## § 1 Sentence, Wen normal form, and semantic shapes -/

/-- Raw finite sentence surface.  The string is only a carrier here. -/
structure Sentence where
  source : String
deriving Repr, DecidableEq

/-- Rewritten Wen normal form.  This is the deliberate intermediate layer. -/
structure WenNormalForm where
  text : String
deriving Repr, DecidableEq

/-- What was lost when a richer object was projected down to R8. -/
inductive ProjectionLoss where
  | none
  | extraAxis
  | history
  | context
  | recursion
  | higherOperator
deriving Repr, DecidableEq

namespace ProjectionLoss

/-- A loss ledger is clear exactly when no higher-than-R8 material was dropped. -/
def clear : ProjectionLoss → Bool
  | .none => true
  | .extraAxis | .history | .context | .recursion | .higherOperator => false

theorem clear_none : clear .none = true := rfl
theorem clear_extraAxis : clear .extraAxis = false := rfl
theorem clear_history : clear .history = false := rfl
theorem clear_context : clear .context = false := rfl
theorem clear_recursion : clear .recursion = false := rfl
theorem clear_higherOperator : clear .higherOperator = false := rfl

end ProjectionLoss

/-- Semantic forms visible from the R8 layer.

The `slice` case keeps an explicit anchor cell: a region is not collapsed to a
single cell, but it still has a chosen R8 point for diagnostics.
-/
inductive R8Semantics where
  | cell : R8 → R8Semantics
  | operator : (R8 → R8) → R8Semantics
  | path : List R8 → R8Semantics
  | slice : R8 → (R8 → Prop) → R8Semantics
  | projected : R8 → ProjectionLoss → R8Semantics

/-! ## § 2 R8 path composition and projection -/

/-- Compose a list of R8 XOR masks. -/
def foldMasks : List R8 → R8
  | [] => R8.origin
  | c :: rest => R8.xor c (foldMasks rest)

@[simp] theorem foldMasks_nil : foldMasks [] = R8.origin := rfl

@[simp] theorem foldMasks_singleton (c : R8) : foldMasks [c] = c := by
  simp [foldMasks]

@[simp] theorem foldMasks_pair_self (c : R8) : foldMasks [c, c] = R8.origin := by
  simp [foldMasks, R8.xor_self]

/-- The visible R8 coordinate for any semantic shape. -/
def visibleR8 : R8Semantics → R8
  | .cell c => c
  | .operator f => f R8.origin
  | .path masks => foldMasks masks
  | .slice anchor _ => anchor
  | .projected c _ => c

/-- The projection loss attached to a semantic shape. -/
def lossOf : R8Semantics → ProjectionLoss
  | .cell _ => .none
  | .operator _ => .none
  | .path _ => .none
  | .slice _ _ => .none
  | .projected _ loss => loss

/-- A semantic object returns to Way when its visible R8 coordinate is origin. -/
def returnsDao (s : R8Semantics) : Prop :=
  visibleR8 s = R8.origin

theorem origin_cell_returnsDao :
    returnsDao (.cell R8.origin) := rfl

theorem empty_path_returnsDao :
    returnsDao (.path []) := rfl

theorem duplicated_mask_path_returnsDao (c : R8) :
    returnsDao (.path [c, c]) := by
  simp [returnsDao, visibleR8]

theorem projected_loss_is_reported (c : R8) (loss : ProjectionLoss) :
    lossOf (.projected c loss) = loss := rfl

theorem projected_visible_is_given_cell (c : R8) (loss : ProjectionLoss) :
    visibleR8 (.projected c loss) = c := rfl

/-! ## § 3 Axis appropriateness certificates -/

/-- Coarse role of a candidate information axis. -/
inductive AxisRole where
  | yuan
  | yao
  | yin
  | guo
  | truth
  | named
  | contextual
deriving Repr, DecidableEq

/-- A candidate axis as seen from R8.  `independentFromPrior` is a certificate
slot supplied by the chosen frame; this file does not compute span membership. -/
structure AxisSpec where
  mask : R8
  role : AxisRole
  independentFromPrior : Prop
  projectable : Bool
deriving Repr

/-- The typed boundary for saying that adding an axis is appropriate. -/
def AxisAppropriate (a : AxisSpec) : Prop :=
  a.mask ≠ R8.origin
    ∧ a.independentFromPrior
    ∧ a.projectable = true

theorem axis_appropriate_has_nonzero_mask (a : AxisSpec) :
    AxisAppropriate a → a.mask ≠ R8.origin := fun h => h.1

theorem axis_appropriate_is_projectable (a : AxisSpec) :
    AxisAppropriate a → a.projectable = true := fun h => h.2.2

/-! ## § 4 Interpreter boundary -/

/-- A Wen-to-R8 interpreter is explicit data, not an implicit property of text. -/
structure WenR8Interpreter where
  rewrite : Sentence → WenNormalForm
  interpret : WenNormalForm → R8Semantics

/-- Interpret a raw sentence through the chosen Wen normal form. -/
def interpretSentence (I : WenR8Interpreter) (s : Sentence) : R8Semantics :=
  I.interpret (I.rewrite s)

/-- Project a raw sentence to the R8-visible coordinate of a chosen interpreter. -/
def sentenceProjection (I : WenR8Interpreter) (s : Sentence) : R8 :=
  visibleR8 (interpretSentence I s)

/-- Report the projection loss produced by the chosen interpreter. -/
def sentenceProjectionLoss (I : WenR8Interpreter) (s : Sentence) : ProjectionLoss :=
  lossOf (interpretSentence I s)

theorem sentence_has_r8_projection (I : WenR8Interpreter) (s : Sentence) :
    ∃ c : R8, sentenceProjection I s = c :=
  ⟨sentenceProjection I s, rfl⟩

theorem sentence_has_loss_ledger (I : WenR8Interpreter) (s : Sentence) :
    ∃ loss : ProjectionLoss, sentenceProjectionLoss I s = loss :=
  ⟨sentenceProjectionLoss I s, rfl⟩

theorem sentence_returnsDao_iff_projection_origin (I : WenR8Interpreter) (s : Sentence) :
    returnsDao (interpretSentence I s) ↔ sentenceProjection I s = R8.origin :=
  Iff.rfl

/-! ## § 5 Public summary -/

/-- Public theorem bundle for the Wen-R8 projection calculus.

It states only the structural boundary:
given an interpreter, every sentence has an R8-visible projection, a loss
ledger, and a precise returns-Dao test.  It does not prove full text semantics.
-/
theorem wen_r8_projection_calculus_summary (I : WenR8Interpreter) :
    (∀ s : Sentence, ∃ c : R8, sentenceProjection I s = c)
    ∧ (∀ s : Sentence, ∃ loss : ProjectionLoss, sentenceProjectionLoss I s = loss)
    ∧ returnsDao (.cell R8.origin)
    ∧ (∀ c : R8, returnsDao (.path [c, c]))
    ∧ (∀ a : AxisSpec, AxisAppropriate a → a.projectable = true) :=
  ⟨ sentence_has_r8_projection I
  , sentence_has_loss_ledger I
  , origin_cell_returnsDao
  , duplicated_mask_path_returnsDao
  , axis_appropriate_is_projectable
  ⟩

end SSBX.Foundation.Wen.R8ProjectionCalculus
