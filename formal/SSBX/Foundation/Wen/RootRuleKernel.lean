/-
# RootRuleKernel -- conservative Wen/Lisp root-rule syntax over R8

This module is the next step after `RootLanguageTree`: it gives the roadmap's
root rules a small syntax and an R8-visible evaluator.

The evaluator is deliberately conservative. It proves that every expression has
an R8-visible projection and a loss ledger; it does not claim complete natural
language semantics or an injective encoding of all syntax into one R8 cell.
-/

import SSBX.Foundation.Hierarchy.RootLanguageTree
import SSBX.Foundation.Wen.R8ProjectionCalculus

namespace SSBX.Foundation.Wen.RootRuleKernel

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Hierarchy.RootLanguageTree
open SSBX.Foundation.Wen.R8ProjectionCalculus

/-! ## Environment and primitive paths -/

/-- A minimal lookup environment for named R8 cells. -/
abbrev Env : Type := String -> Option R8

/-- Empty environment: every lookup misses. -/
def emptyEnv : Env := fun _ => none

/-- Rule syntax is represented as a path of R8 masks.

The path, not only its folded visible cell, is the syntax-level carrier. This is
why a finite rule kernel can be represented without pretending that each rule is
exhausted by a unique single R8 cell. -/
def primitivePath : RootRule -> List R8
  | .quote => []
  | .apply => [R8.imprint_mask]
  | .compose => [R8.project_mask]
  | .xor => [R8.imprint_mask, R8.project_mask]
  | .neg => [R8.imprint_mask, R8.imprint_mask, R8.project_mask]
  | .equal => [R8.project_mask, R8.imprint_mask, R8.project_mask]
  | .ite => [R8.imprint_mask, R8.project_mask, R8.imprint_mask]
  | .lookup => [R8.project_mask, R8.project_mask, R8.imprint_mask]
  | .recurse => [R8.imprint_mask, R8.project_mask, R8.project_mask]
  | .project => [R8.project_mask, R8.imprint_mask, R8.imprint_mask]
  | .lift => [R8.imprint_mask, R8.imprint_mask, R8.project_mask, R8.project_mask]
  | .returnDao => [R8.project_mask, R8.project_mask, R8.imprint_mask, R8.imprint_mask]

/-- Primitive rule as an R8-visible path. -/
def primitiveSemantics (r : RootRule) : R8Semantics :=
  .path (primitivePath r)

theorem primitive_has_visible_projection (r : RootRule) :
    ∃ c : R8, visibleR8 (primitiveSemantics r) = c :=
  ⟨visibleR8 (primitiveSemantics r), rfl⟩

/-! ## Core forms -/

/-- Conservative root-rule program syntax. -/
inductive CoreForm : Type
  | atom : R8 -> CoreForm
  | primitive : RootRule -> CoreForm
  | quote : CoreForm -> CoreForm
  | apply : CoreForm -> CoreForm -> CoreForm
  | compose : CoreForm -> CoreForm -> CoreForm
  | ite : CoreForm -> CoreForm -> CoreForm -> CoreForm
  | equal : CoreForm -> CoreForm -> CoreForm
  | lookup : String -> CoreForm
  | recurse : Nat -> CoreForm -> CoreForm
  | project : CoreForm -> CoreForm

namespace CoreForm

/-- R8-visible evaluation.

`quote`, `recurse`, missing `lookup`, and `project` make the loss ledger
explicit. `apply` and `compose` use XOR because the exact cell-transform layer
is Cayley-style R8 self-action. -/
def eval (env : Env) : CoreForm -> R8Semantics
  | .atom c => .cell c
  | .primitive r => primitiveSemantics r
  | .quote e =>
      let s := eval env e
      .projected (visibleR8 s) .higherOperator
  | .apply f x =>
      let vf := visibleR8 (eval env f)
      let vx := visibleR8 (eval env x)
      .cell (R8.xor vf vx)
  | .compose f g =>
      let vf := visibleR8 (eval env f)
      let vg := visibleR8 (eval env g)
      .cell (R8.xor vf vg)
  | .ite p a b =>
      if visibleR8 (eval env p) = R8.origin then
        eval env a
      else
        eval env b
  | .equal a b =>
      if visibleR8 (eval env a) = visibleR8 (eval env b) then
        .cell R8.origin
      else
        .cell R8.imprint_mask
  | .lookup name =>
      match env name with
      | some c => .cell c
      | none => .projected R8.origin .context
  | .recurse _ body =>
      let s := eval env body
      .projected (visibleR8 s) .recursion
  | .project e =>
      let s := eval env e
      .projected (visibleR8 s) (lossOf s)

/-- Visible projection of a core form. -/
def visible (env : Env) (e : CoreForm) : R8 :=
  visibleR8 (eval env e)

/-- Loss ledger of a core form. -/
def loss (env : Env) (e : CoreForm) : ProjectionLoss :=
  lossOf (eval env e)

theorem atom_visible (env : Env) (c : R8) :
    visible env (.atom c) = c := rfl

theorem apply_atoms_visible (env : Env) (f x : R8) :
    visible env (.apply (.atom f) (.atom x)) = R8.xor f x := rfl

theorem compose_atoms_visible (env : Env) (f g : R8) :
    visible env (.compose (.atom f) (.atom g)) = R8.xor f g := rfl

theorem equal_same_atom_returns_origin (env : Env) (c : R8) :
    visible env (.equal (.atom c) (.atom c)) = R8.origin := by
  simp [visible, eval, visibleR8]

theorem duplicated_apply_returns_origin (env : Env) (c : R8) :
    visible env (.apply (.atom c) (.atom c)) = R8.origin := by
  simp [visible, eval, visibleR8, R8.xor_self]

theorem missing_lookup_has_context_loss (name : String) :
    loss emptyEnv (.lookup name) = .context := rfl

theorem quote_reports_higher_operator_loss (env : Env) (e : CoreForm) :
    loss env (.quote e) = .higherOperator := rfl

theorem recurse_reports_recursion_loss (env : Env) (fuel : Nat) (e : CoreForm) :
    loss env (.recurse fuel e) = .recursion := rfl

theorem every_form_has_visible_projection (env : Env) (e : CoreForm) :
    ∃ c : R8, visible env e = c :=
  ⟨visible env e, rfl⟩

theorem every_form_has_loss_ledger (env : Env) (e : CoreForm) :
    ∃ l : ProjectionLoss, loss env e = l :=
  ⟨loss env e, rfl⟩

end CoreForm

/-! ## Public summary -/

theorem root_rule_kernel_summary :
    RootRule.all.length = 12
    ∧ (∀ r : RootRule, ∃ c : R8, visibleR8 (primitiveSemantics r) = c)
    ∧ (∀ env : Env, ∀ e : CoreForm, ∃ c : R8, CoreForm.visible env e = c)
    ∧ (∀ env : Env, ∀ e : CoreForm, ∃ l : ProjectionLoss, CoreForm.loss env e = l)
    ∧ (∀ env : Env, ∀ c : R8,
        CoreForm.visible env (.apply (.atom c) (.atom c)) = R8.origin)
    ∧ (∀ name : String, CoreForm.loss emptyEnv (.lookup name) = .context) := by
  exact
    ⟨ RootRule.all_length
    , primitive_has_visible_projection
    , CoreForm.every_form_has_visible_projection
    , CoreForm.every_form_has_loss_ledger
    , CoreForm.duplicated_apply_returns_origin
    , CoreForm.missing_lookup_has_context_loss
    ⟩

end SSBX.Foundation.Wen.RootRuleKernel
