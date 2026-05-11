/-
# RootOperator -- root-native operator boundary

This module separates the v3 root operator interface from the historical
operator catalogue.  A root-native operator is carried by an R8 mask, a
root-rule program, a projected R8 cell with loss ledger, or an alias to another
root-native operator.  A legacy catalogue row can be audited against this
interface, but catalogue cardinality is not an ontology count.
-/

import SSBX.Foundation.Wen.RootRuleKernel
import SSBX.Foundation.Wen.R8ProjectionKernel

namespace SSBX.Foundation.Wen.RootOperator

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Wen.R8ProjectionCalculus
open SSBX.Foundation.Wen.R8ProjectionKernel
open SSBX.Foundation.Wen.RootRuleKernel

/-! ## Root-native operators -/

/-- The source kind of a root-native operator. -/
inductive RootOperatorKind where
  | mask
  | program
  | projection
  | alias
deriving Repr, DecidableEq

/-- Root-native operator carrier.

`alias` preserves behaviour of an already root-native operator.  It is not a
new ontology count. -/
inductive RootOperator where
  | mask : R8 -> RootOperator
  | program : CoreForm -> RootOperator
  | projection : R8 -> ProjectionLoss -> RootOperator
  | alias : String -> RootOperator -> RootOperator

namespace RootOperator

/-- Source kind of a root-native operator. -/
def kind : RootOperator -> RootOperatorKind
  | .mask _ => .mask
  | .program _ => .program
  | .projection _ _ => .projection
  | .alias _ _ => .alias

/-- R8-visible semantics of a root-native operator. -/
def semantics : RootOperator -> R8Semantics
  | .mask c => .path [c]
  | .program e => CoreForm.eval emptyEnv e
  | .projection c loss => .projected c loss
  | .alias _ target => semantics target

/-- Visible R8 cell of a root-native operator. -/
def visible (op : RootOperator) : R8 :=
  visibleR8 (semantics op)

/-- Loss ledger of a root-native operator. -/
def loss (op : RootOperator) : ProjectionLoss :=
  lossOf (semantics op)

theorem mask_visible (c : R8) :
    visible (.mask c) = c := by
  simp [visible, semantics, visibleR8]

theorem projection_visible (c : R8) (l : ProjectionLoss) :
    visible (.projection c l) = c := rfl

theorem projection_loss (c : R8) (l : ProjectionLoss) :
    loss (.projection c l) = l := rfl

theorem alias_visible (name : String) (target : RootOperator) :
    visible (.alias name target) = visible target := rfl

theorem alias_loss (name : String) (target : RootOperator) :
    loss (.alias name target) = loss target := rfl

theorem every_operator_has_visible_projection (op : RootOperator) :
    ∃ c : R8, visible op = c :=
  ⟨visible op, rfl⟩

theorem every_operator_has_loss_ledger (op : RootOperator) :
    ∃ l : ProjectionLoss, loss op = l :=
  ⟨loss op, rfl⟩

theorem duplicated_mask_returns_origin (c : R8) :
    visible (.program (.apply (.atom c) (.atom c))) = R8.origin := by
  simpa [visible, semantics] using CoreForm.duplicated_apply_returns_origin emptyEnv c

end RootOperator

/-! ## Legacy catalogue quarantine -/

/-- The only allowed roles for legacy catalogue rows after quarantine. -/
inductive LegacyCatalogueRole where
  | alias
  | corpus
  | evidenceNote
  | delete
deriving Repr, DecidableEq

namespace LegacyCatalogueRole

/-- A legacy row requires a root target only when it is kept as an alias. -/
def requiresRootTarget : LegacyCatalogueRole -> Bool
  | .alias => true
  | .corpus | .evidenceNote | .delete => false

/-- No legacy catalogue role is itself an ontology count. -/
def isOntologyCount (_ : LegacyCatalogueRole) : Bool := false

theorem no_legacy_role_is_ontology_count (role : LegacyCatalogueRole) :
    isOntologyCount role = false := rfl

theorem alias_requires_root_target :
    requiresRootTarget .alias = true := rfl

theorem corpus_not_root_target :
    requiresRootTarget .corpus = false := rfl

theorem evidence_note_not_root_target :
    requiresRootTarget .evidenceNote = false := rfl

theorem delete_not_root_target :
    requiresRootTarget .delete = false := rfl

end LegacyCatalogueRole

/-! ## Public summary -/

theorem root_operator_summary :
    (∀ op : RootOperator, ∃ c : R8, RootOperator.visible op = c)
    ∧ (∀ op : RootOperator, ∃ l : ProjectionLoss, RootOperator.loss op = l)
    ∧ (∀ name : String, ∀ target : RootOperator,
        RootOperator.visible (.alias name target) = RootOperator.visible target)
    ∧ (∀ name : String, ∀ target : RootOperator,
        RootOperator.loss (.alias name target) = RootOperator.loss target)
    ∧ (∀ role : LegacyCatalogueRole,
        LegacyCatalogueRole.isOntologyCount role = false)
    ∧ LegacyCatalogueRole.requiresRootTarget .alias = true
    ∧ LegacyCatalogueRole.requiresRootTarget .corpus = false
    ∧ LegacyCatalogueRole.requiresRootTarget .evidenceNote = false
    ∧ LegacyCatalogueRole.requiresRootTarget .delete = false := by
  exact
    ⟨ RootOperator.every_operator_has_visible_projection
    , RootOperator.every_operator_has_loss_ledger
    , RootOperator.alias_visible
    , RootOperator.alias_loss
    , LegacyCatalogueRole.no_legacy_role_is_ontology_count
    , LegacyCatalogueRole.alias_requires_root_target
    , LegacyCatalogueRole.corpus_not_root_target
    , LegacyCatalogueRole.evidence_note_not_root_target
    , LegacyCatalogueRole.delete_not_root_target
    ⟩

end SSBX.Foundation.Wen.RootOperator
