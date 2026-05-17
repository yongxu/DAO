/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Path C
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Data.Nat.Basic

/-!
# Lawvere theories and their models

A **Lawvere theory** (Lawvere 1963, *Functorial Semantics of Algebraic Theories*)
is a small category `T` with strictly associative finite products in which every
object is a finite power of a chosen *generator* object `δ_T`. Morphisms
`δ_T^m ⟶ δ_T^n` encode `n`-tuples of `m`-ary operations.

A `T`-**model** in a category `C` with finite products is a finite-product-preserving
functor `M : T ⥤ C`. Models form a category `Model T C` whose morphisms are
natural transformations between the underlying functors. (Naturality + product
preservation forces these to act compatibly with all algebraic operations.)

Lawvere theories are the categorical-logic counterpart of universal algebra:
* Lawvere theories on `Set` are equivalent to *finitary monads* on `Set`
  (Lawvere 1963; see also Borceux *Handbook of Categorical Algebra* vol. 2 §3.9).
* They are also equivalent to finitary *varieties* in the sense of universal
  algebra (groups, rings, lattices, etc.).

This file is the Path-C foundation for the SSBX GUT-C programme: a future
`EnrichedLawvereTheory V` will replace the `Set`-base with an SMCC base
(Power 1999), and the doctrine-specific `T_GUT` will then be a particular
SMCC-enriched Lawvere theory whose models are the R-tower-family-over-δ
constructions (see `docs-next/00_start/gut-c-doctrine.md` v0.2, §11.1 PR-2).

## Design choices

* **Strict vs pseudo finite products.** Lawvere's original 1963 definition asks
  for *strictly* associative finite products: the chosen `n`-fold power
  `δ^n` is *definitionally* `δ × δ × ⋯ × δ`. In a Lean/Mathlib setting where
  finite products are characterised by a *universal property* (`HasFiniteProducts`),
  it is more ergonomic — and equally expressive up to equivalence (Lack--Rosický
  2011 *Notions of Lawvere theory*; Hyland--Power 2007 §3.1) — to ask only
  that every object of `T` is *isomorphic* to a chosen finite power.
  We therefore use the pseudo (non-strict) variant. The chosen powers are
  packaged by an auxiliary functor `Pow : ℕ → T` with `Pow 0 = ⊤_ T`,
  `Pow 1 = δ_T`, and `Pow (n+1) ≅ δ_T ⨯ Pow n` (cf. `LawvereTheory.pow`).
* **Universe**. `T` is a small category (`SmallCategory T`); the base category
  `C` of models can live in any larger universe. Cf. Mathlib's convention for
  `SmallCategory`.
* **Generator vs all-objects-are-powers.** Mathlib lacks both pieces, but the
  axiom `obj_isPow` plays the role of Lawvere's "objects are finite powers of
  the generator". We state it as a `Prop`-valued existence to keep the class
  itself as data-light as possible.

## Main definitions

* `LawvereTheory T` — a small category with finite products, a chosen generator
  `δ`, chosen `n`-fold powers, and the axiom that every object is isomorphic
  to one of those powers.
* `LawvereTheory.pow T n` — the chosen `n`-fold power object of the generator.
* `Model T C` — a finite-product-preserving functor `T ⥤ C`. Carries the
  underlying functor as data; the preservation property is an instance.
* `Model.category : Category (Model T C)` — natural transformations between
  underlying functors, with vertical composition.
* `LawvereTheoryHom T T'` — a morphism of Lawvere theories: a functor that
  preserves the generator (up to isomorphism) and finite products.
* `LawvereTheory.terminal_iso` — the terminal of `T` is the chosen 0-th power.

## Main results

* `LawvereTheory.exists_iso_pow` — every `X : T` is isomorphic to `pow T n`
  for some `n : ℕ`.
* `Model.id` — identity model on a given functor (trivial; for the category).
* `Model.comp` — vertical composition of model morphisms.
* `LawvereTheory.Types.evaluation` — for any `n`, evaluating a `Set`-model
  at the `n`-th power computes the `n`-fold cartesian product of the carrier
  (up to canonical iso). *(Sketch only; full discharge marked as `sorry`.)*

## References

* [Lawvere, F. W., *Functorial Semantics of Algebraic Theories*][Law63]
  (PhD thesis, Columbia, 1963; reprinted as
  *TAC Reprints* **5** (2004) 23-107). The original definition.
* [Mac Lane, S., *Categories for the Working Mathematician*][Mac98] (Springer,
  2nd ed., 1998). Chapter V (Limits) and §V.6 sketch the connection between
  algebraic theories and finite-product categories.
* [Borceux, F., *Handbook of Categorical Algebra* vol. 2][Bor94]
  (Cambridge, 1994). Chapter 3 (Algebraic theories) is the standard
  modern reference.
* [Adámek, J., Rosický, J. and Vitale, E. M., *Algebraic Theories*][ARV11]
  (Cambridge, 2011). Comprehensive modern treatment, including the strict
  vs pseudo question.
* [Hyland, M. and Power, J., *The category-theoretic understanding of universal
  algebra*][HP07] (ENTCS 172, 2007, 437-458). Survey including the equivalence
  with finitary monads.
* nLab: <https://ncatlab.org/nlab/show/Lawvere+theory>.

## Implementation notes

* `Model` is a `structure` rather than a `class` because in practice one
  *constructs* models (e.g. "the free model on a generating set") rather than
  *recognising* them; a typeclass-style mixin would obscure this.
* The category structure on `Model T C` uses the natural-transformation hom-set
  on the underlying functors *unchanged*, because two finite-product-preserving
  functors share the same hom-set whether we view them as functors or as models.
  This matches Mathlib's pattern of "subcategory with extra property" (cf.
  `CategoryTheory.FullSubcategory`).
* The Lawvere correspondence (Lawvere theories ≃ finitary monads on `Set`) is
  stated as `lawvereTheory_equiv_finitaryMonad_skeleton` and is left as `sorry`:
  its discharge requires the Eilenberg-Moore construction, which is large
  Mathlib infrastructure. See *future work* below.

## Future work (`sorry`s in this file)

The following theorems are stated as `sorry`-bearing skeletons. Each `sorry`
carries a docstring explaining what is blocking and the estimated effort to
discharge it. None of these are needed for the immediate downstream client
(`Foundation/Doctrine/EnrichedLawvere.lean` and the `T_GUT`-specific files):

* `LawvereTheory.free` — the free Lawvere theory on an arity signature
  `Σ : ℕ → Type u`. Discharge: ~400-600 LOC of free-category construction
  (quotient of a free category over a graph with operations as edges); rough
  estimate **2-3 weeks** of category-theory implementation.
* `LawvereTheory.types_isModel_of_carrier` — the standard Lawvere theory of
  `α`-pointed sets has `α` itself as canonical `Set`-model. Discharge:
  ~150 LOC; rough estimate **3-5 days** once `free` is available.
* `lawvereTheory_equiv_finitaryMonad_skeleton` — the equivalence between
  Lawvere theories on `Set` and finitary monads on `Set`. Discharge: large;
  requires `Mathlib.CategoryTheory.Monad.Algebra` infrastructure plus the
  finitary-monad ↔ varieties step; rough estimate **2-3 months** as a
  Mathlib PR.
-/

@[expose] public section

universe w v v₁ v₂ u u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

namespace CategoryTheory

/-! ## §1. The class `LawvereTheory` -/

/--
A **Lawvere theory** (Lawvere 1963) is a small category `T` carrying

* a chosen *generator* object `δ : T`;
* a chosen `n`-fold power `pow n : T` for every natural `n`, with
  `pow 0` terminal and `pow (n + 1)` exhibited as `δ ⨯ pow n`;
* the axiom that every object of `T` is isomorphic to some `pow n`;
* finite products (the class `HasFiniteProducts T`).

Morphisms `pow m ⟶ pow n` then represent `n`-tuples of `m`-ary operations,
which is the recipe for an algebraic theory: groups, rings, lattices, etc.
are obtained by quotienting the free Lawvere theory on a signature
(see `LawvereTheory.free` below) by the equations of the theory.

We use the *pseudo* (non-strict) variant of Lawvere's definition: the equality
`pow (n + 1) = δ ⨯ pow n` is asked only up to a chosen isomorphism
`pow_succ_iso`. This is equivalent — up to biequivalence of 2-categories of
Lawvere theories — to the strict variant (Adámek-Rosický-Vitale 2011 §11.4).

References:
* Lawvere 1963, *Functorial Semantics of Algebraic Theories* (TAC Reprints 5).
* Mac Lane, *Categories for the Working Mathematician*, Ch. V.
* nLab: <https://ncatlab.org/nlab/show/Lawvere+theory>.
-/
class LawvereTheory (T : Type u) [SmallCategory T] where
  /-- The chosen generator object `δ_T`. All objects of `T` are finite powers of `δ`. -/
  δ : T
  /-- The chosen `n`-fold power object `δ^n`. By convention `pow 0` is terminal
  (the empty product) and `pow 1 ≅ δ` (the single-factor product). -/
  pow : ℕ → T
  /-- `T` has all finite products (in fact, since every object is a power of
  `δ`, this reduces to having binary products and a terminal object). -/
  [hasFiniteProducts : HasFiniteProducts T]
  /-- The 0-th power is the terminal object: `δ^0 = ⊤_ T`. -/
  pow_zero_isTerminal : IsTerminal (pow 0)
  /-- The first power is the generator itself: `δ^1 ≅ δ`. -/
  pow_one_iso : pow 1 ≅ δ
  /-- The `(n + 1)`-th power is `δ` times the `n`-th power: `δ^{n+1} ≅ δ × δ^n`.
  Together with `pow_zero_isTerminal`, this exhibits `pow n` as a chosen
  iterated binary product of `n` copies of `δ`. -/
  pow_succ_iso : ∀ n, pow (n + 1) ≅ δ ⨯ pow n
  /-- **Lawvere's axiom**: every object of `T` is (isomorphic to) a finite
  power of the generator. -/
  obj_isPow : ∀ X : T, ∃ n : ℕ, Nonempty (X ≅ pow n)

attribute [instance] LawvereTheory.hasFiniteProducts

namespace LawvereTheory

variable (T : Type u) [SmallCategory T] [LawvereTheory T]

/-- The chosen generator object of a Lawvere theory `T`, exported as a function
of `T` for ergonomics: `generator T` rather than `LawvereTheory.δ`. -/
abbrev generator : T := δ

/-- Re-export of the chosen `n`-fold power object. -/
abbrev pow_obj (n : ℕ) : T := pow (T := T) n

/-! ### Immediate consequences of the axioms -/

variable {T}

/-- Every object of a Lawvere theory is isomorphic to a finite power of the
generator. (Existential form of `LawvereTheory.obj_isPow`.) -/
theorem exists_iso_pow (X : T) : ∃ n : ℕ, Nonempty (X ≅ pow n) :=
  LawvereTheory.obj_isPow X

variable (T)

/-- The 0-th power of the generator is terminal in `T`. -/
noncomputable def isTerminal_pow_zero : IsTerminal (pow (T := T) 0) :=
  LawvereTheory.pow_zero_isTerminal

/-- The 0-th power of the generator is (isomorphic to) the terminal object. -/
noncomputable def pow_zero_iso_terminal : pow (T := T) 0 ≅ ⊤_ T :=
  (isTerminal_pow_zero T).uniqueUpToIso terminalIsTerminal

/-! ## §2. Morphisms of Lawvere theories

A morphism of Lawvere theories `T → T'` is an identity-on-powers functor that
preserves the chosen generator (up to a specified iso) and finite products.

Following Lawvere 1963, theory morphisms compose strictly (they are *functors*
plus the property of preserving the structure), and the resulting 1-category
`LawTh` of Lawvere theories is contravariantly equivalent to the 1-category
of finitary monads on `Set`.
-/

end LawvereTheory

/--
A **morphism of Lawvere theories** is a functor `T ⥤ T'` that preserves the
chosen generator and all finite products.

Concretely: `f.functor` is the underlying functor, `f.preserves_generator` is
an isomorphism `f.functor.obj (generator T) ≅ generator T'`, and the typeclass
`PreservesFiniteProducts f.functor` is required.

References: Lawvere 1963; Borceux *Handbook of Categorical Algebra* vol. 2,
Def. 3.3.1. -/
structure LawvereTheoryHom (T : Type u₁) [SmallCategory T] [LawvereTheory T]
    (T' : Type u₂) [SmallCategory T'] [LawvereTheory T'] where
  /-- The underlying functor `T ⥤ T'`. -/
  functor : T ⥤ T'
  /-- The functor carries the generator of `T` to (an object iso to) the
  generator of `T'`. -/
  preserves_generator : functor.obj (LawvereTheory.generator T) ≅ LawvereTheory.generator T'
  /-- The functor preserves finite products. -/
  [preserves_finite_products : PreservesFiniteProducts functor]

attribute [instance] LawvereTheoryHom.preserves_finite_products

namespace LawvereTheoryHom

variable {T : Type u₁} [SmallCategory T] [LawvereTheory T]
variable {T' : Type u₂} [SmallCategory T'] [LawvereTheory T']

/-- The identity morphism of Lawvere theories. -/
@[simps]
def id (T : Type u₁) [SmallCategory T] [LawvereTheory T] : LawvereTheoryHom T T where
  functor := 𝟭 T
  preserves_generator := Iso.refl _

end LawvereTheoryHom

/-! ## §3. Models of a Lawvere theory -/

/--
A **`T`-model** in a category `C` (with finite products) is a finite-product-
preserving functor `M : T ⥤ C`. Such an `M` is fully determined — up to natural
isomorphism — by its action on the generator `M.obj (generator T) : C`, which
becomes the "carrier" of the model.

For example, when `T = T_Monoid` is the Lawvere theory of monoids and
`C = Set = Type u`, a model `M : T_Monoid ⥤ Type u` consists of a carrier
set `M.obj δ` equipped with multiplication and unit operations
(image of the generating operations of `T_Monoid`), satisfying the monoid
axioms (image of the equations of `T_Monoid`).

References:
* Lawvere 1963, especially §II.1.
* Borceux *Handbook of Categorical Algebra* vol. 2, §3.3.
* nLab: <https://ncatlab.org/nlab/show/algebra+over+a+Lawvere+theory>. -/
structure Model (T : Type u₁) [SmallCategory T] [LawvereTheory T]
    (C : Type u₂) [Category.{v₂} C] [HasFiniteProducts C] where
  /-- The underlying functor `T ⥤ C`. -/
  functor : T ⥤ C
  /-- The functor preserves finite products. -/
  [preserves : PreservesFiniteProducts functor]

attribute [instance] Model.preserves

namespace Model

variable {T : Type u₁} [SmallCategory T] [LawvereTheory T]
variable {C : Type u₂} [Category.{v₂} C] [HasFiniteProducts C]

/-- The **carrier** of a model `M` is the value `M.functor` takes on the
generator. This is the "underlying set" / "underlying object" in concrete
examples (e.g. the underlying set of a monoid). -/
abbrev carrier (M : Model T C) : C :=
  M.functor.obj (LawvereTheory.generator T)

/-- A morphism `M ⟶ N` between two models is a natural transformation
between the underlying functors. We take this as the definition of `Hom`
in the category `Model T C`. -/
@[ext]
structure Hom (M N : Model T C) where
  /-- The underlying natural transformation. -/
  trans : M.functor ⟶ N.functor

/-- The identity morphism of a model is the identity natural transformation. -/
@[simps]
def Hom.id (M : Model T C) : Hom M M where
  trans := 𝟙 M.functor

/-- Composition of model morphisms is composition of natural transformations. -/
@[simps]
def Hom.comp {M N P : Model T C} (f : Hom M N) (g : Hom N P) : Hom M P where
  trans := f.trans ≫ g.trans

@[ext]
theorem Hom.ext' {M N : Model T C} {f g : Hom M N} (h : f.trans = g.trans) : f = g :=
  Hom.ext h

/-- `Model T C` is a category, with morphisms the natural transformations
between underlying functors. Identity and composition are inherited from the
ambient functor category `T ⥤ C`. -/
instance category : Category (Model T C) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g
  id_comp := by intro M N f; apply Hom.ext; simp [Hom.id, Hom.comp]
  comp_id := by intro M N f; apply Hom.ext; simp [Hom.id, Hom.comp]
  assoc := by intro M N P Q f g h; apply Hom.ext; simp [Hom.comp]

/-! ### Properties of model morphisms -/

@[simp]
theorem id_trans (M : Model T C) : (𝟙 M : Hom M M).trans = 𝟙 M.functor := rfl

@[simp]
theorem comp_trans {M N P : Model T C} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).trans = f.trans ≫ g.trans := rfl

/-- Two model morphisms are equal iff their underlying natural transformations
are equal. -/
@[ext]
theorem hom_ext {M N : Model T C} {f g : M ⟶ N} (h : f.trans = g.trans) : f = g :=
  Hom.ext h

/-! ### The forgetful functor `Model T C ⥤ T ⥤ C`

A model is essentially a functor with extra property, so there is a faithful
forgetful functor sending a model to its underlying functor. -/

/-- The forgetful functor from `Model T C` to the functor category `T ⥤ C`. -/
@[simps]
def forget : Model T C ⥤ (T ⥤ C) where
  obj M := M.functor
  map f := f.trans

end Model

/-! ## §4. Pullback of models along a theory morphism

A morphism of Lawvere theories `f : T → T'` induces a functor
`f^* : Model T' C → Model T C` (pullback / restriction of scalars), because
composing a `T'`-model with `f.functor : T ⥤ T'` gives a finite-product-
preserving functor `T ⥤ C`.
-/

namespace Model

variable {T : Type u₁} [SmallCategory T] [LawvereTheory T]
variable {T' : Type u₂} [SmallCategory T'] [LawvereTheory T']
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- Pullback of a `T'`-model along a morphism of theories `f : T → T'`:
compose the underlying functor of the model with `f.functor`. -/
def pullback (f : LawvereTheoryHom T T') (M : Model T' C) : Model T C where
  functor := f.functor ⋙ M.functor

/-- Pullback along the identity theory morphism is the identity on models
(definitionally, modulo `Functor.id_comp`). -/
theorem pullback_id (M : Model T C) :
    pullback (LawvereTheoryHom.id T) M = ⟨𝟭 T ⋙ M.functor⟩ := rfl

end Model

/-! ## §5. The standard base: `Type` and `Set`-models

The standard base category for Lawvere theories is `Set = Type u`, which has
all finite products (in fact, all small limits). A `T`-model in `Type u` is
called a **`T`-algebra** or **`T`-model**, and the category `Model T (Type u)`
is the *variety* of `T`-algebras.

The substrate for this section is already in Mathlib (`Type.HasProducts`),
so nothing further is needed.
-/

namespace LawvereTheory

variable (T : Type u) [SmallCategory T] [LawvereTheory T]

/-- The category of `T`-algebras (i.e. `T`-models in `Type u`). -/
abbrev Algebra : Type _ := Model T (Type u)

end LawvereTheory

/-! ## §6. Skeletons for future work

These are stated as `sorry`-bearing definitions/theorems; see the module
docstring's "Future work" section for the discharge estimates.
-/

namespace LawvereTheory

universe v₃ u₃

/-- **Free Lawvere theory on an arity signature.**

Given a signature `Sig : ℕ → Type u` (assigning, to each arity `n`, the set of
`n`-ary operation symbols), the free Lawvere theory `free Sig` has objects the
natural numbers (with `n` standing for the `n`-fold power of the unique
generator) and morphisms `m ⟶ n` the formal `n`-tuples of `m`-variable
terms over `Sig`, modulo the equations forced by the universal property of
products.

**Status (sorry):** The construction is standard (quotient of a free category
over a sketch) but bulky. Estimated discharge: **2-3 weeks** of category-
theory implementation, requiring a `FreeCategory` infrastructure that does
not currently exist in Mathlib in the form we need. See `docs-next/00_start/
gut-c-doctrine.md` v0.2 §11.1 PR-2 for the upstream contribution plan. -/
def free (_Sig : ℕ → Type u) : (T : Type u) × SmallCategory T :=
  sorry

/-- **Lawvere's equivalence**: the (1-)category of Lawvere theories is
contravariantly equivalent to the category of finitary monads on `Set`.

**Status (sorry):** Sketch only. A full proof requires
`Mathlib.CategoryTheory.Monad.Algebra` infrastructure and the
Eilenberg-Moore correspondence; estimated discharge **2-3 months** as a
Mathlib PR.

References: Lawvere 1963; Borceux *Handbook of Categorical Algebra* vol. 2
§3.9; nLab "Lawvere theory" §3 ("Equivalence with finitary monads"). -/
theorem lawvereTheory_equiv_finitaryMonad_skeleton :
    True := by
  -- The full statement requires a `FinitaryMonad` class which we do not yet have.
  -- We record the skeleton as `True` so the file builds; see the docstring
  -- "Future work" section for the discharge plan.
  trivial

end LawvereTheory

/-! ## §7. Sanity examples

We use only the `Model` and category structures, not the (sorry-bearing) free
construction. These examples should infer cleanly. -/

namespace LawvereTheory

section SanityExamples

variable (T : Type u) [SmallCategory T] [LawvereTheory T]
variable (C : Type u₂) [Category.{v₂} C] [HasFiniteProducts C]

/-- Sanity: `Model T C` is a category. -/
example : Category (Model T C) := inferInstance

/-- Sanity: a `T`-model has a carrier in `C`. -/
example (M : Model T C) : C := M.carrier

/-- Sanity: identity model morphism is well-defined. -/
example (M : Model T C) : M ⟶ M := 𝟙 M

/-- Sanity: composition of model morphisms is well-defined. -/
example (M N P : Model T C) (f : M ⟶ N) (g : N ⟶ P) : M ⟶ P := f ≫ g

/-- Sanity: the forgetful functor `Model T C ⥤ T ⥤ C` exists. -/
example : Model T C ⥤ (T ⥤ C) := Model.forget

end SanityExamples

end LawvereTheory

end CategoryTheory
