/-
# RootWordRegistry -- append-friendly registry gate for rooted words

This module gives the small, stable shape for adding accepted words. A registry
entry must carry a `RootWord`, an English reading, review status, and an optional
claim anchor. The registry does not try to enumerate the 1023 review rows by
hand; generated coverage belongs in a later table.
-/

import SSBX.Foundation.Wen.RootWord

namespace SSBX.Foundation.Wen.RootWordRegistry

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Hierarchy.RootLanguageTree
open SSBX.Foundation.Wen.R8ProjectionCalculus
open SSBX.Foundation.Wen.RootRuleKernel
open SSBX.Foundation.Wen.RootWord

/-! ## Registry entries -/

/-- Review status for a rooted word entry. -/
inductive RootWordStatus where
  | canonical
  | provisional
  | reviewAnchor
  deriving Repr, DecidableEq

/-- A word target is well-formed when Yi execution targets carry a concrete
instruction. Core and meta-interpreter entries may leave `yiInstr? = none`. -/
def executionTargetOk (w : RootWord) : Bool :=
  match w.target, w.yiInstr? with
  | .yi, none => false
  | _, _ => true

/-- One append-friendly registry row for a rooted word. -/
structure RootWordRegistryEntry where
  word : RootWord
  english : String
  status : RootWordStatus
  claimAnchor : Option String
  targetOk : executionTargetOk word = true

/-- A registry is just an append-friendly list of accepted rows. Coverage and
no-duplicate checks can be layered on generated registries later. -/
abbrev RootWordRegistry : Type :=
  List RootWordRegistryEntry

namespace RootWordRegistryEntry

/-- R-layer inherited from the entry word. -/
def layer (e : RootWordRegistryEntry) : RootLayer :=
  RootWord.layer e.word

/-- Role inherited from the entry word. -/
def role (e : RootWordRegistryEntry) : RootRole :=
  RootWord.role e.word

/-- Visible R8 projection inherited from the entry word. -/
def visible (e : RootWordRegistryEntry) : R8 :=
  RootWord.visible e.word

/-- Loss ledger inherited from the entry word. -/
def loss (e : RootWordRegistryEntry) : ProjectionLoss :=
  RootWord.loss e.word

theorem has_visible_projection (e : RootWordRegistryEntry) :
    ∃ c : R8, visible e = c :=
  ⟨visible e, rfl⟩

theorem has_loss_ledger (e : RootWordRegistryEntry) :
    ∃ l : ProjectionLoss, loss e = l :=
  ⟨loss e, rfl⟩

end RootWordRegistryEntry

namespace RootWordRegistry

/-- Append one accepted entry. -/
def appendEntry (registry : RootWordRegistry) (entry : RootWordRegistryEntry) :
    RootWordRegistry :=
  registry ++ [entry]

theorem appendEntry_length (registry : RootWordRegistry) (entry : RootWordRegistryEntry) :
    (appendEntry registry entry).length = registry.length + 1 := by
  simp [appendEntry]

theorem entries_target_ok (registry : RootWordRegistry) :
    ∀ entry ∈ registry, executionTargetOk entry.word = true := by
  intro entry _
  exact entry.targetOk

theorem entries_have_visible_projection (registry : RootWordRegistry) :
    ∀ entry ∈ registry, ∃ c : R8, RootWordRegistryEntry.visible entry = c := by
  intro entry _
  exact RootWordRegistryEntry.has_visible_projection entry

theorem entries_have_loss_ledger (registry : RootWordRegistry) :
    ∀ entry ∈ registry, ∃ l : ProjectionLoss, RootWordRegistryEntry.loss entry = l := by
  intro entry _
  exact RootWordRegistryEntry.has_loss_ledger entry

end RootWordRegistry

/-! ## Minimal seed anchor -/

/-- The R0 root cell used by the seed Way entry. -/
def wayRootCell : RootCell :=
  { layer := .r0, code := ⟨0, by decide⟩ }

/-- The seed glyph for the undivided Way anchor. -/
def wayGlyph : RootGlyph :=
  { surface := "Way"
  , entry := { cell := wayRootCell, role := .cell }
  , operator := RootNativeOperator.program (.primitive .returnDao) }

/-- The seed word for the undivided Way anchor. -/
def wayWord : RootWord :=
  { glyph := wayGlyph
  , core := .primitive .returnDao
  , target := .core
  , yiInstr? := none }

/-- The first registry row. It is a seed anchor, not a generated coverage table. -/
def wayRegistryEntry : RootWordRegistryEntry :=
  { word := wayWord
  , english := "Way"
  , status := .canonical
  , claimAnchor := some "R0 origin"
  , targetOk := rfl }

/-- Minimal seed registry. Future generated registries should extend this shape
instead of changing the gate. -/
def seedRegistry : RootWordRegistry :=
  [wayRegistryEntry]

theorem wayWord_layer :
    RootWord.layer wayWord = .r0 := rfl

theorem wayWord_role :
    RootWord.role wayWord = .cell := rfl

theorem seedRegistry_length :
    seedRegistry.length = 1 := rfl

/-! ## Public summary -/

theorem root_word_registry_summary :
    seedRegistry.length = 1
    ∧ RootWord.layer wayWord = .r0
    ∧ RootWord.role wayWord = .cell
    ∧ (∀ entry ∈ seedRegistry, executionTargetOk entry.word = true)
    ∧ (∀ entry ∈ seedRegistry,
        ∃ c : R8, RootWordRegistryEntry.visible entry = c)
    ∧ (∀ entry ∈ seedRegistry,
        ∃ l : ProjectionLoss, RootWordRegistryEntry.loss entry = l)
    ∧ (∀ registry : RootWordRegistry, ∀ entry : RootWordRegistryEntry,
        (RootWordRegistry.appendEntry registry entry).length = registry.length + 1) := by
  exact
    ⟨ seedRegistry_length
    , wayWord_layer
    , wayWord_role
    , RootWordRegistry.entries_target_ok seedRegistry
    , RootWordRegistry.entries_have_visible_projection seedRegistry
    , RootWordRegistry.entries_have_loss_ledger seedRegistry
    , RootWordRegistry.appendEntry_length
    ⟩

end SSBX.Foundation.Wen.RootWordRegistry
