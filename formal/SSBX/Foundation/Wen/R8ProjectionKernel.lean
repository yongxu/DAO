/-
# R8ProjectionKernel -- generic projection-to-R8 interface

This module abstracts the projection boundary used by Wen/R8 semantics:
any richer carrier `H` can expose an R8-visible coordinate plus a loss ledger.
The kernel is the equivalence relation induced by equal R8 projections.
-/

import SSBX.Foundation.Wen.R8ProjectionCalculus

namespace SSBX.Foundation.Wen.R8ProjectionKernel

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Wen.R8ProjectionCalculus

/-! ## Generic projection interface -/

/-- A carrier with an R8-visible projection and a loss ledger. -/
structure ProjectionToR8 (H : Type) where
  project : H -> R8
  loss : H -> ProjectionLoss

/-- Two richer objects are projection-equivalent when R8 cannot distinguish them. -/
def ProjectionEquivalent {H : Type} (P : ProjectionToR8 H) (a b : H) : Prop :=
  P.project a = P.project b

/-- The projection kernel at Way/origin. -/
def InProjectionKernel {H : Type} (P : ProjectionToR8 H) (a : H) : Prop :=
  P.project a = R8.origin

theorem projectionEquivalent_refl {H : Type} (P : ProjectionToR8 H) (a : H) :
    ProjectionEquivalent P a a := rfl

theorem projectionEquivalent_symm {H : Type} (P : ProjectionToR8 H) {a b : H} :
    ProjectionEquivalent P a b -> ProjectionEquivalent P b a := by
  intro h
  exact h.symm

theorem projectionEquivalent_trans {H : Type} (P : ProjectionToR8 H) {a b c : H} :
    ProjectionEquivalent P a b ->
    ProjectionEquivalent P b c ->
    ProjectionEquivalent P a c := by
  intro hab hbc
  exact hab.trans hbc

theorem projection_has_visible_cell {H : Type} (P : ProjectionToR8 H) (a : H) :
    ∃ c : R8, P.project a = c :=
  ⟨P.project a, rfl⟩

theorem projection_has_loss_ledger {H : Type} (P : ProjectionToR8 H) (a : H) :
    ∃ loss : ProjectionLoss, P.loss a = loss :=
  ⟨P.loss a, rfl⟩

/-! ## Canonical instances -/

/-- R8 itself projects to R8 with no loss. -/
def identityProjection : ProjectionToR8 R8 where
  project := id
  loss := fun _ => .none

theorem identityProjection_project (c : R8) :
    identityProjection.project c = c := rfl

theorem identityProjection_loss (c : R8) :
    identityProjection.loss c = .none := rfl

/-- Existing `R8Semantics` already carries a projection and loss ledger. -/
def semanticsProjection : ProjectionToR8 R8Semantics where
  project := visibleR8
  loss := lossOf

theorem semanticsProjection_project (s : R8Semantics) :
    semanticsProjection.project s = visibleR8 s := rfl

theorem semanticsProjection_loss (s : R8Semantics) :
    semanticsProjection.loss s = lossOf s := rfl

theorem origin_cell_in_semantics_kernel :
    InProjectionKernel semanticsProjection (.cell R8.origin) := rfl

theorem duplicated_mask_path_in_semantics_kernel (c : R8) :
    InProjectionKernel semanticsProjection (.path [c, c]) := by
  simp [InProjectionKernel, semanticsProjection, visibleR8]

/-! ## Public summary -/

theorem r8_projection_kernel_summary :
    (∀ s : R8Semantics, semanticsProjection.project s = visibleR8 s)
    ∧ (∀ s : R8Semantics, semanticsProjection.loss s = lossOf s)
    ∧ InProjectionKernel semanticsProjection (.cell R8.origin)
    ∧ (∀ c : R8, InProjectionKernel semanticsProjection (.path [c, c]))
    ∧ (∀ H : Type, ∀ P : ProjectionToR8 H, ∀ a : H, ProjectionEquivalent P a a)
    ∧ (∀ H : Type, ∀ P : ProjectionToR8 H, ∀ a : H,
        ∃ c : R8, P.project a = c)
    ∧ (∀ H : Type, ∀ P : ProjectionToR8 H, ∀ a : H,
        ∃ loss : ProjectionLoss, P.loss a = loss) := by
  exact
    ⟨ semanticsProjection_project
    , semanticsProjection_loss
    , origin_cell_in_semantics_kernel
    , duplicated_mask_path_in_semantics_kernel
    , fun _ P a => projectionEquivalent_refl P a
    , fun _ P a => projection_has_visible_cell P a
    , fun _ P a => projection_has_loss_ledger P a
    ⟩

end SSBX.Foundation.Wen.R8ProjectionKernel
