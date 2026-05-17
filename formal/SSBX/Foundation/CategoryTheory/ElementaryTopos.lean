/-
Copyright (c) 2026 Yongxu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxu Ren
-/
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
# Elementary topoi

An **elementary topos**, in the sense of Lawvere–Tierney 1970, is a category that is
simultaneously

1. finitely complete (`HasFiniteLimits`),
2. cartesian closed (`CartesianMonoidalCategory` together with `MonoidalClosed`), and
3. equipped with a subobject classifier (`HasSubobjectClassifier`).

Equivalently, it is a cartesian closed category with all finite limits and a generic
mono `truth : Ω₀ ⟶ Ω` classifying subobjects.

Mathlib already supplies each of the three component pieces independently:

* `CategoryTheory.Limits.HasFiniteLimits`
  (in `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits`),
* `CategoryTheory.MonoidalClosed` over a `CategoryTheory.CartesianMonoidalCategory`
  (in `Mathlib.CategoryTheory.Monoidal.Closed.Basic` and
  `Mathlib.CategoryTheory.Monoidal.Closed.Cartesian`; note that the old
  `CartesianClosed` is now a deprecated alias for `MonoidalClosed`),
* `CategoryTheory.HasSubobjectClassifier`
  (in `Mathlib.CategoryTheory.Subobject.Classifier.Defs`).

What is **not** yet upstream is a single typeclass bundling the three. This file
provides such a bundle, `CategoryTheory.ElementaryTopos`, together with the
expected propagation instances and a canonical instance on `Type u`.

## Main definitions

* `CategoryTheory.ElementaryTopos C` — a `Prop`-valued mixin asserting that `C` carries
  finite limits, a subobject classifier, and (via instance parameters) the
  cartesian-closed structure.
* `CategoryTheory.ElementaryTopos.Ω` — the chosen subobject classifier object (re-export
  of `HasSubobjectClassifier.Ω`).
* `CategoryTheory.ElementaryTopos.truth` — the truth morphism `Ω₀ ⟶ Ω` (re-export).
* `CategoryTheory.ElementaryTopos.PowerObject A` — the *power object* `Ω ^^ A`, i.e.
  the internal hom from `A` into `Ω`. In the topos of sets it is the powerset `2 ^ A`.

## Main results

* `CategoryTheory.ElementaryTopos.toHasTerminal`,
  `CategoryTheory.ElementaryTopos.toHasFiniteProducts`,
  `CategoryTheory.ElementaryTopos.toHasPullbacks`,
  `CategoryTheory.ElementaryTopos.toHasEqualizers`,
  `CategoryTheory.ElementaryTopos.toHasBinaryProducts` — propagation instances derived
  from `HasFiniteLimits`.
* `CategoryTheory.Types.subobjectClassifier`,
  `CategoryTheory.Types.hasSubobjectClassifier` — the classical Lawvere construction
  `Ω := ULift Prop` on `Type u`, with `truth : PUnit ⟶ ULift Prop` picking out `True`.
* `CategoryTheory.Types.instElementaryTopos : ElementaryTopos (Type u)` — the
  prototypical topos.

## Implementation notes

`ElementaryTopos` is declared as a `Prop` mixin whose `extends` clauses are the two
propositional component classes (`HasFiniteLimits`, `HasSubobjectClassifier`). The
data-bearing classes `CartesianMonoidalCategory` and `MonoidalClosed` are taken as
*instance parameters* rather than via `extends`, since their content is data (a choice
of binary products / internal homs) rather than a proposition. This matches the
pattern of `CategoryTheory.ObjectProperty.IsMonoidalClosed` in
`Mathlib.CategoryTheory.Monoidal.Subcategory`, which also takes `[MonoidalClosed C]`
as an instance parameter. It also mirrors `CategoryTheory.Regular` in
`Mathlib.CategoryTheory.RegularCategory.Basic`, which extends `HasFiniteLimits` only
and keeps data-bearing structures as parameters.

The canonical instance on `Type u` uses `Ω := ULift.{u} Prop`, lifting the classical
`Prop` (which lives in `Type 0`) into the ambient universe. The characteristic map of
a mono `m : U ⟶ X` sends `x : X` to the proposition "there exists `u : U` with
`m u = x`" (which, since `m` is injective, is equivalent to `x ∈ Set.range m`).

## References

* [F. W. Lawvere and M. Tierney, *Quantifiers and sheaves*][LT70] (Actes du Congrès
  International des Mathématiciens, 1970, vol. 1, pp. 329–334; origin of the
  *elementary* topos).
* [S. Mac Lane and I. Moerdijk, *Sheaves in geometry and logic: a first introduction
  to topos theory*][MM92] (Springer, 1992; standard reference, esp. Chap. I–IV for
  definitions and Chap. IV.5 for the `Type` case).
* [P. T. Johnstone, *Sketches of an elephant: a topos theory compendium*][Joh02]
  (Oxford, 2002).
* nLab pages: <https://ncatlab.org/nlab/show/topos>,
  <https://ncatlab.org/nlab/show/elementary+topos>.
-/

@[expose] public section

universe v u

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

/-! ### Definition of an elementary topos -/

/-- An **elementary topos** in the sense of Lawvere–Tierney is a category equipped with
finite limits, a cartesian-closed structure, and a subobject classifier.

We model this as a `Prop`-valued class extending `HasFiniteLimits` and
`HasSubobjectClassifier`, with `CartesianMonoidalCategory C` and `MonoidalClosed C`
required as instance parameters (these carry data rather than a proposition).

Equivalently (cf. Mac Lane–Moerdijk, *Sheaves in geometry and logic*, I.1):
*a category `C` is an elementary topos iff it has finite limits, is cartesian closed,
and has a subobject classifier*. -/
class ElementaryTopos (C : Type u) [Category.{v} C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] : Prop
    extends HasFiniteLimits C, HasSubobjectClassifier C

namespace ElementaryTopos

variable (C : Type u) [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [ElementaryTopos C]

/-! ### Derived instances

These are pure forwarding instances. They make `inferInstance` succeed for any
client that needs finite products, pullbacks, etc., from an `ElementaryTopos`.
The underlying lemmas live in:
* `Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts`
  (`hasFiniteProducts_of_hasFiniteLimits`), and
* `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits`
  (`HasFiniteLimits` already implies `HasLimitsOfShape J` for every finite `J`).
-/

/-- An elementary topos has a terminal object. -/
instance (priority := 100) toHasTerminal : HasTerminal C :=
  haveI : HasFiniteLimits C := inferInstance
  inferInstance

/-- An elementary topos has all finite products. -/
instance (priority := 100) toHasFiniteProducts : HasFiniteProducts C :=
  hasFiniteProducts_of_hasFiniteLimits C

/-- An elementary topos has all binary products. -/
instance (priority := 100) toHasBinaryProducts : HasBinaryProducts C :=
  haveI : HasFiniteLimits C := inferInstance
  inferInstance

/-- An elementary topos has all pullbacks. -/
instance (priority := 100) toHasPullbacks : HasPullbacks C :=
  haveI : HasFiniteLimits C := inferInstance
  inferInstance

/-- An elementary topos has all equalizers. -/
instance (priority := 100) toHasEqualizers : HasEqualizers C :=
  haveI : HasFiniteLimits C := inferInstance
  inferInstance

/-! ### The subobject classifier `Ω` and the power object `Ω ^^ A` -/

/-- The chosen subobject classifier object of an elementary topos.

This is a re-export of `CategoryTheory.HasSubobjectClassifier.Ω` provided so that
`ElementaryTopos.Ω C` is the canonical entry-point. -/
noncomputable abbrev Ω : C := HasSubobjectClassifier.Ω C

/-- The truth morphism `Ω₀ ⟶ Ω` of the classifier. Re-export of
`CategoryTheory.HasSubobjectClassifier.truth`. -/
noncomputable abbrev truth : HasSubobjectClassifier.Ω₀ C ⟶ Ω C :=
  HasSubobjectClassifier.truth C

/-- The **power object** of `A` in an elementary topos is the internal hom `Ω ^^ A`.
In the topos of sets it is the powerset `2 ^ A`.

This uses the scoped notation `_ ^^ _` from
`Mathlib.CategoryTheory.Monoidal.Closed.Cartesian`, which expands to `(ihom A).obj _`.

The carrier category `C` is left implicit and inferred from the argument `A`. -/
noncomputable abbrev PowerObject {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [ElementaryTopos C]
    (A : C) : C :=
  open scoped CartesianClosed in
  Ω C ^^ A

end ElementaryTopos

/-! ### The canonical instance: the topos of types

We exhibit the classical Lawvere construction: in `Type u`, set `Ω := ULift.{u} Prop`.
The truth value `⊤_ ⟶ Ω` picks out `True`, and the characteristic map of a mono
`m : U ⟶ X` sends `x : X` to `∃ u, m u = x`. -/

namespace Types

open Subobject Limits

/-- The truth morphism in `Type u`: the function `PUnit ⟶ ULift.{u} Prop`
sending `PUnit.unit` to `ULift.up True`. -/
noncomputable def truth : PUnit.{u + 1} ⟶ ULift.{u} Prop :=
  ↾fun _ => ULift.up True

/-- The characteristic map of a mono `m : U ⟶ X` in `Type u`: it sends `x : X` to
`ULift.up (∃ u, m u = x)`.

By monicity (i.e. injectivity in `Type`), this proposition is `True` iff `x` lies in
the image of `m`. -/
noncomputable def χ {U X : Type u} (m : U ⟶ X) [Mono m] : X ⟶ ULift.{u} Prop :=
  ↾fun x => ULift.up (∃ u, m u = x)

/-- The image of `x : X` under `χ m`, as a `Prop`. -/
@[simp]
lemma χ_apply_down {U X : Type u} (m : U ⟶ X) [Mono m] (x : X) :
    (χ m x).down = (∃ u, m u = x) := rfl

/-- The image of `p : PUnit` under `truth`, as a `Prop`. -/
@[simp]
lemma truth_apply_down (p : PUnit.{u + 1}) : (truth p).down = True := rfl

/-- The truth square commutes: composing `m` with `χ m` yields the constant `True` map. -/
lemma comp_χ_eq {U X : Type u} (m : U ⟶ X) [Mono m] :
    m ≫ χ m = Types.isTerminalPUnit.from U ≫ truth := by
  ext u
  -- Goal is `(∃ u', m u' = m u) ↔ True`.
  exact ⟨fun _ => trivial, fun _ => ⟨u, rfl⟩⟩

/-- The truth square for `χ m` is a pullback square in `Type u`. -/
lemma isPullback_χ_truth {U X : Type u} (m : U ⟶ X) [Mono m] :
    IsPullback m (Types.isTerminalPUnit.from U) (χ m) truth := by
  rw [Types.isPullback_iff]
  refine ⟨comp_χ_eq m, ?_, ?_⟩
  · -- Injectivity of the pair `(m, terminal)`: `m` is mono, hence injective.
    intro u₁ u₂ ⟨h, _⟩
    exact (CategoryTheory.mono_iff_injective m).mp inferInstance h
  · -- Existence: for `x : X` and `p : PUnit` with `χ m x = truth p`, the down-equality
    -- says `∃ u, m u = x`, providing the desired witness.
    intro x p hxp
    have hdown : (∃ u, m u = x) = True := by
      have h := congrArg ULift.down hxp
      simpa using h
    obtain ⟨u, hu⟩ : ∃ u, m u = x := hdown ▸ trivial
    exact ⟨u, hu, Subsingleton.elim _ _⟩

/-- Uniqueness of the characteristic map for a given mono `m` in `Type u`. -/
lemma χ_unique {U X : Type u} (m : U ⟶ X) [Mono m]
    (χ' : X ⟶ ULift.{u} Prop)
    (hχ' : IsPullback m (Types.isTerminalPUnit.from U) χ' truth) :
    χ' = χ m := by
  rw [Types.isPullback_iff] at hχ'
  obtain ⟨hw, _hinj, hex⟩ := hχ'
  ext x
  -- After `ext`, the goal is `(χ' x).down ↔ (∃ u, m u = x)`.
  constructor
  · -- If `χ' x` is `True`, use existence to extract `u` with `m u = x`.
    intro hx
    have hχ'eq : χ' x = ULift.up True := by
      apply ULift.ext
      exact propext ⟨fun _ => trivial, fun _ => hx⟩
    obtain ⟨u, hu, _⟩ := hex x PUnit.unit (by rw [hχ'eq]; rfl)
    exact ⟨u, hu⟩
  · -- Conversely, if `∃ u, m u = x`, then `χ' (m u) = True` by commutativity.
    rintro ⟨u, rfl⟩
    -- `hw : m ≫ χ' = (terminal map) ≫ truth`; apply `ConcreteCategory.congr_hom` at `u`.
    have h := ConcreteCategory.congr_hom hw u
    have h' := congrArg ULift.down h
    simpa using h'

/-- The subobject classifier on `Type u`: `Ω = ULift.{u} Prop`, with `truth` picking out
`True` and `χ m` sending `x` to `∃ u, m u = x`.

This is the standard Lawvere construction (Mac Lane–Moerdijk IV.1). The universe lifting
`ULift.{u} Prop` is needed because `Prop : Type 0` while we need `Ω : Type u`. -/
noncomputable def subobjectClassifier : Subobject.Classifier (Type u) :=
  .mkOfTerminalΩ₀ PUnit Types.isTerminalPUnit (ULift Prop) truth
    (fun {_ _} m _ => χ m)
    (fun {_ _} m _ => isPullback_χ_truth m)
    (fun {_ _} m _ χ' hχ' => χ_unique m χ' hχ')

/-- `Type u` has a subobject classifier (the classical Lawvere construction). -/
instance hasSubobjectClassifier : HasSubobjectClassifier (Type u) where
  exists_classifier := ⟨subobjectClassifier⟩

end Types

/-! ### The topos of types -/

namespace Types

/-- The category `Type u` is an elementary topos.

This is the prototypical Lawvere–Tierney example. The four required ingredients are
supplied by:

* `CartesianMonoidalCategory (Type u)` — `Mathlib.CategoryTheory.Monoidal.Types.Basic`,
* `MonoidalClosed (Type u)` — `Mathlib.CategoryTheory.Monoidal.Closed.Types`,
* `HasLimitsOfSize (Type u)` — `Mathlib.CategoryTheory.Limits.Types.Limits`, which
  yields `HasFiniteLimits` via `hasFiniteLimits_of_hasLimitsOfSize`,
* `HasSubobjectClassifier (Type u)` — `Types.hasSubobjectClassifier` above. -/
instance instElementaryTopos : ElementaryTopos (Type u) where

end Types

/-! ### Sanity examples

These `example` declarations exercise the propagation instances: a client that
opens `ElementaryTopos` should be able to recover finite-limit data, the
subobject classifier, and power objects without any extra `haveI` boilerplate.
-/

namespace ElementaryTopos

section Examples

variable (C : Type u) [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [ElementaryTopos C]

/-- An elementary topos has a terminal object (recovered by instance search). -/
example : HasTerminal C := inferInstance

/-- An elementary topos has finite products (recovered by instance search). -/
example : HasFiniteProducts C := inferInstance

/-- An elementary topos has binary products. -/
example : HasBinaryProducts C := inferInstance

/-- An elementary topos has pullbacks. -/
example : HasPullbacks C := inferInstance

/-- An elementary topos has equalizers. -/
example : HasEqualizers C := inferInstance

/-- An elementary topos has finite limits. -/
example : HasFiniteLimits C := inferInstance

/-- An elementary topos has a subobject classifier. -/
example : HasSubobjectClassifier C := inferInstance

/-- The subobject classifier `Ω : C` is well-defined. -/
noncomputable example : C := Ω C

/-- The truth morphism `Ω₀ ⟶ Ω` is well-defined. -/
noncomputable example : HasSubobjectClassifier.Ω₀ C ⟶ Ω C := truth C

/-- Every object `A : C` admits a power object `Ω ^^ A`. -/
noncomputable example (A : C) : C := PowerObject A

end Examples

end ElementaryTopos

end CategoryTheory
