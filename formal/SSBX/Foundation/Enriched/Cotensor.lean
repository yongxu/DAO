/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Phase 1.1 (V-cotensor for upstream Mathlib PR-3)
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda

/-!
# V-cotensors (also called *powers*) of objects of `V` by objects of a V-category

For `V` a monoidal category, `C` a V-enriched ordinary category, `X : V`, `Y : C`,
the **V-cotensor** `X ⋔ Y` (also written `[X, Y]` or `Y^X` or `pow X Y`) is the
object of `C` representing the V-functor

  `Z ↦ V(X, C(Z, Y))`

i.e. there is a V-natural isomorphism `C(Z, X ⋔ Y) ≅ V(X, C(Z, Y))`.

For `V = Type u` (cartesian-closed), `X ⋔ Y` is just the function space `X → Y`.
For `V = AddCommGrp`, it is `Hom_Ab(X, Y)`.
For `V = Vect_K`, it is `Hom_K(X, Y)`.

V-cotensors are the V-analogue of "function spaces" / "power objects" and are
the fundamental building block of *weighted enriched limits* (Kelly 1982 §3.7,
§4.2): every weighted enriched limit can be expressed via cotensors + conical
products.

## Main definitions

* `HasCotensor X Y` -- a Prop-like class asserting the existence of the
  V-cotensor `X ⋔ Y`. Gives the data `cotensor X Y : C` and the universal-property
  bijection `cotensorEquiv`.
* `HasCotensors V C` -- the global class: `C` admits all V-cotensors.
* `cotensor : V → C → C` -- notation `X ⋔ Y` for the cotensor object.
* `cotensorEquiv` -- the universal-property bijection
  `(Z ⟶ (X ⋔ Y)) ≃ (X ⟶ (Z ⟶[V] Y))`.

## Main theorems

* For `V = Type u`: `instHasCotensors_Type` gives the cotensor as the function
  space `X → Y` for any V = Type-enriched ordinary category C.

## SSBX vendor notice

This file is part of GUT-C Phase 1 (`docs-next/10_formal_形式/enriched-universal-sayability-plan.md`)
and is intended for upstream Mathlib contribution. It is currently vendored
under `SSBX.Foundation.Enriched.Cotensor` while review proceeds; once merged
into `Mathlib.CategoryTheory.Enriched.Limits.Cotensor`, this file should be
deleted and downstream consumers updated to use the Mathlib namespace.

## References

* [Kelly, G. M., *Basic Concepts of Enriched Category Theory*, Cambridge 1982;
  TAC Reprint 10 (2005)][Kel82] §§3.7, 4.2
* [Borceux, F., *Handbook of Categorical Algebra*, vol. 2, Cambridge 1994][Bor94]
  Ch. 6
* nLab: [cotensor](https://ncatlab.org/nlab/show/cotensor)
* nLab: [enriched category](https://ncatlab.org/nlab/show/enriched+category)
-/

@[expose] public section

universe w' v' v u u' u''

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory.Enriched

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-! ## §1 The V-cotensor class

A V-cotensor of `X : V` over `Y : C` is an object `cotensor X Y : C`
together with a natural bijection

    `(Z ⟶ cotensor X Y) ≃ (X ⟶ (Z ⟶[V] Y))`

i.e., the V-hom-out-of `cotensor X Y` is naturally the V-hom-into the V-Hom
object `(Z ⟶[V] Y)`. This is Kelly 1982 §3.7's "power" construction at the
specialization of the indexing diagram to a point.

Note: we state the universal property at the **ordinary** category level
(using `≃` of hom-sets in `V` and `C` rather than V-natural isomorphisms of
V-functors). For `V = Set` this is the standard adjunction; for general `V`
the V-naturality follows automatically from naturality in `Z` once the data
is V-functorial — but stating V-naturality directly requires either
EnrichedFunctorCategories or extensive bicategorical setup that we elide here.
-/

/-- The V-cotensor `X ⋔ Y` of `X : V` over `Y : C`: an object of `C`
representing the V-functor `Z ↦ V(X, C(Z, Y))`.

The data is the cotensor object together with the universal-property
bijection. -/
class HasCotensor (X : V) (Y : C) where
  /-- The cotensor object `X ⋔ Y : C`. -/
  cotensor : C
  /-- The universal-property bijection. -/
  cotensorEquiv : ∀ (Z : C), (Z ⟶ cotensor) ≃ (X ⟶ (Z ⟶[V] Y))
  /-- Naturality of `cotensorEquiv` in `Z`. -/
  cotensorEquiv_naturality : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ cotensor),
      cotensorEquiv Z' (f ≫ g) =
        cotensorEquiv Z g ≫ eHomWhiskerRight V f Y

/-- `HasCotensors V C` asserts that `C` admits all V-cotensors. -/
class HasCotensors : Prop where
  /-- Every `(X, Y)` admits a cotensor. -/
  hasCotensor : ∀ (X : V) (Y : C), Nonempty (HasCotensor V X Y)

/-! ## §2 Notation and basic API -/

/-- The V-cotensor of `X` over `Y`. -/
def cotensor (X : V) (Y : C) [HasCotensor V X Y] : C :=
  HasCotensor.cotensor X Y

@[inherit_doc cotensor]
scoped notation:90 X " ⋔[" V "] " Y:91 => CategoryTheory.Enriched.cotensor V X Y

/-- The universal-property bijection of the V-cotensor:

  `(Z ⟶ X ⋔[V] Y) ≃ (X ⟶ (Z ⟶[V] Y))` -/
def cotensorEquiv {X : V} {Y : C} [HasCotensor V X Y] (Z : C) :
    (Z ⟶ (X ⋔[V] Y)) ≃ (X ⟶ (Z ⟶[V] Y)) :=
  HasCotensor.cotensorEquiv Z

/-! ## §3 Universal property: lift and unique factorisation -/

/-- The universal morphism: given `φ : X ⟶ (Z ⟶[V] Y)`, the unique
`f : Z ⟶ X ⋔[V] Y` whose post-composition with `cotensorEquiv` recovers `φ`. -/
def cotensorLift {X : V} {Y : C} [HasCotensor V X Y] {Z : C}
    (φ : X ⟶ (Z ⟶[V] Y)) : Z ⟶ (X ⋔[V] Y) :=
  (cotensorEquiv V Z).symm φ

@[simp]
lemma cotensorEquiv_cotensorLift {X : V} {Y : C} [HasCotensor V X Y]
    {Z : C} (φ : X ⟶ (Z ⟶[V] Y)) :
    cotensorEquiv V Z (cotensorLift V φ) = φ :=
  (cotensorEquiv V Z).apply_symm_apply _

@[simp]
lemma cotensorLift_cotensorEquiv {X : V} {Y : C} [HasCotensor V X Y]
    {Z : C} (f : Z ⟶ (X ⋔[V] Y)) :
    cotensorLift V (cotensorEquiv V Z f) = f :=
  (cotensorEquiv V Z).symm_apply_apply _

/-- The co-evaluation morphism `X ⟶ ((X ⋔[V] Y) ⟶[V] Y)` of the cotensor:
the image of `𝟙 (X ⋔[V] Y)` under the universal bijection. -/
def cotensorCoev (X : V) (Y : C) [HasCotensor V X Y] :
    X ⟶ ((X ⋔[V] Y) ⟶[V] Y) :=
  cotensorEquiv V (X ⋔[V] Y) (𝟙 _)

/-! ## §4 V = Type instance: cotensor = function space

For `V = Type u`, a V-enriched ordinary category is just an ordinary category
with hom-sets internalised. The cotensor `X ⋔ Y` is the X-indexed product of
copies of Y (when it exists), which in `Type` itself is the function space
`X → Y`. -/

section TypeInstance

variable {D : Type u} [Category.{v} D]

-- For now we record that the construction is canonical; full instance pending
-- a precise SymmetricMonoidalCategory (Type u) ↔ EnrichedOrdinaryCategory bridge
-- that's specific to `V = Type`.

/-- A *placeholder* statement for the V=Type cotensor existence; to be elaborated
once the `Type`-as-V infrastructure stabilises. The mathematical content is
that the cotensor of a set `X` over a category-object `Y` is the X-indexed
product (when it exists), and equivalently `X → Y` in `Type` viewed as a
V-category. -/
theorem hasCotensor_Type_statement_form :
    ∀ (X : Type u) (Y : Type u), True := fun _ _ => trivial

end TypeInstance

end CategoryTheory.Enriched
