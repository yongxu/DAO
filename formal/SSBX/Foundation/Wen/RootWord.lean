/-
# RootWord -- root-language word boundary for the R8 interpreter target

This module connects the R0..R8 root interface to the existing R8 interpreter.
It is intentionally structural: it does not claim complete natural-language
coverage, but it fixes the gate through which accepted words can gain a root
anchor, an R8-visible meaning, and an optional YiInstr execution target.
-/

import SSBX.Foundation.Wen.RootOperator
import SSBX.Foundation.Atlas.YiLegacy.Bagua.BaguaTuring

namespace SSBX.Foundation.Wen.RootWord

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Hierarchy.RootLanguageTree
open SSBX.Foundation.Wen.R8ProjectionCalculus
open SSBX.Foundation.Wen.RootRuleKernel

/-- Local name for the root-native operator type. -/
abbrev RootNativeOperator : Type :=
  SSBX.Foundation.Wen.RootOperator.RootOperator

namespace RootNativeOperator

/-- R8-visible projection of a root-native operator. -/
def visible (op : RootNativeOperator) : R8 :=
  SSBX.Foundation.Wen.RootOperator.RootOperator.visible op

/-- Loss ledger of a root-native operator. -/
def loss (op : RootNativeOperator) : ProjectionLoss :=
  SSBX.Foundation.Wen.RootOperator.RootOperator.loss op

/-- Program-backed root-native operator. -/
def program (e : CoreForm) : RootNativeOperator :=
  SSBX.Foundation.Wen.RootOperator.RootOperator.program e

end RootNativeOperator

/-! ## Root glyphs and words -/

/-- Execution target class for an accepted root word. -/
inductive ExecutionTarget where
  | core
  | yi
  | metaInterp
  deriving Repr, DecidableEq

/-- A glyph that has entered the root-language boundary.

The `entry` field carries the R-layer, finite root code, and cell/operator role.
The `operator` field gives its root-native R8-visible meaning. -/
structure RootGlyph where
  surface : String
  entry : RootInterfaceEntry
  operator : RootNativeOperator

namespace RootGlyph

/-- R-layer of the glyph root. -/
def layer (g : RootGlyph) : RootLayer :=
  g.entry.cell.layer

/-- Cell/operator role of the glyph root. -/
def role (g : RootGlyph) : RootRole :=
  g.entry.role

/-- Formal reading kind induced by the root role. -/
def readingKind (g : RootGlyph) : RootReadingKind :=
  SSBX.Foundation.Hierarchy.RootLanguageTree.readingKind g.entry

/-- R8-visible operator projection of the glyph. -/
def visible (g : RootGlyph) : R8 :=
  RootNativeOperator.visible g.operator

/-- Loss ledger of the glyph's root-native operator. -/
def loss (g : RootGlyph) : ProjectionLoss :=
  RootNativeOperator.loss g.operator

theorem has_layer (g : RootGlyph) :
    ∃ l : RootLayer, layer g = l :=
  ⟨layer g, rfl⟩

theorem has_role (g : RootGlyph) :
    ∃ r : RootRole, role g = r :=
  ⟨role g, rfl⟩

theorem has_visible_projection (g : RootGlyph) :
    ∃ c : R8, visible g = c :=
  ⟨visible g, rfl⟩

theorem has_loss_ledger (g : RootGlyph) :
    ∃ l : ProjectionLoss, loss g = l :=
  ⟨loss g, rfl⟩

end RootGlyph

/-- A rooted word ready for semantic checking and optional execution lowering. -/
structure RootWord where
  glyph : RootGlyph
  core : CoreForm
  target : ExecutionTarget
  yiInstr? : Option YiInstr

namespace RootWord

/-- R-layer inherited from the glyph. -/
def layer (w : RootWord) : RootLayer :=
  RootGlyph.layer w.glyph

/-- Cell/operator role inherited from the glyph. -/
def role (w : RootWord) : RootRole :=
  RootGlyph.role w.glyph

/-- R8-visible root semantics of the word. -/
def semantics (w : RootWord) : R8Semantics :=
  CoreForm.eval emptyEnv w.core

/-- Visible R8 projection of the word. -/
def visible (w : RootWord) : R8 :=
  CoreForm.visible emptyEnv w.core

/-- Loss ledger for the word semantics. -/
def loss (w : RootWord) : ProjectionLoss :=
  CoreForm.loss emptyEnv w.core

/-- The word read as a root-native program operator. -/
def rootOperator (w : RootWord) : RootNativeOperator :=
  RootNativeOperator.program w.core

theorem has_visible_projection (w : RootWord) :
    ∃ c : R8, visible w = c :=
  ⟨visible w, rfl⟩

theorem has_loss_ledger (w : RootWord) :
    ∃ l : ProjectionLoss, loss w = l :=
  ⟨loss w, rfl⟩

theorem root_operator_visible_matches_core (w : RootWord) :
    RootNativeOperator.visible (rootOperator w) = visible w := rfl

theorem root_operator_loss_matches_core (w : RootWord) :
    RootNativeOperator.loss (rootOperator w) = loss w := rfl

end RootWord

/-! ## Public summary -/

theorem root_word_summary :
    (∀ g : RootGlyph, ∃ l : RootLayer, RootGlyph.layer g = l)
    ∧ (∀ g : RootGlyph, ∃ r : RootRole, RootGlyph.role g = r)
    ∧ (∀ g : RootGlyph, ∃ c : R8, RootGlyph.visible g = c)
    ∧ (∀ g : RootGlyph, ∃ l : ProjectionLoss, RootGlyph.loss g = l)
    ∧ (∀ w : RootWord, ∃ c : R8, RootWord.visible w = c)
    ∧ (∀ w : RootWord, ∃ l : ProjectionLoss, RootWord.loss w = l) := by
  exact
    ⟨ RootGlyph.has_layer
    , RootGlyph.has_role
    , RootGlyph.has_visible_projection
    , RootGlyph.has_loss_ledger
    , RootWord.has_visible_projection
    , RootWord.has_loss_ledger
    ⟩

end SSBX.Foundation.Wen.RootWord
