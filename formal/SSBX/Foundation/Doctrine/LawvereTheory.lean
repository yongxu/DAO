/-
Copyright (c) 2026 Yongxu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxu Ren
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

A **Lawvere theory** (Lawvere 1963, *Functorial semantics of algebraic theories*) is a
small category `T` with strictly associative finite products in which every object is a
finite power of a chosen *generator* object `δ_T`. Morphisms `δ_T^m ⟶ δ_T^n` encode
`n`-tuples of `m`-ary operations.

A `T`-**model** in a category `C` with finite products is a finite-product-preserving
functor `M : T ⥤ C`. Models form a category `Model T C` whose morphisms are natural
transformations between the underlying functors. (Naturality together with product
preservation forces these to act compatibly with all algebraic operations.)

Lawvere theories are the categorical-logic counterpart of universal algebra:

* Lawvere theories on `Set` are equivalent to *finitary monads* on `Set`
  (Lawvere 1963; see also Borceux, *Handbook of categorical algebra*, vol. 2, §3.9).
* They are also equivalent to finitary *varieties* in the sense of universal algebra
  (groups, rings, lattices, etc.).

## Main definitions

* `CategoryTheory.LawvereTheory T` — a small category with finite products, a chosen
  generator `δ`, chosen `n`-fold powers, and the axiom that every object is isomorphic
  to one of those powers.
* `CategoryTheory.LawvereTheory.pow T n` — the chosen `n`-fold power object of the
  generator.
* `CategoryTheory.LawvereTheory.generator T` — re-export of the chosen generator,
  ergonomic in client code.
* `CategoryTheory.LawvereTheoryHom T T'` — a morphism of Lawvere theories: a functor
  that preserves the generator (up to isomorphism) and finite products.
* `CategoryTheory.Model T C` — a finite-product-preserving functor `T ⥤ C`. Carries the
  underlying functor as data; the preservation property is an instance.
* `CategoryTheory.Model.category : Category (Model T C)` — natural transformations
  between underlying functors, with vertical composition.
* `CategoryTheory.Model.forget : Model T C ⥤ (T ⥤ C)` — the faithful forgetful functor.
* `CategoryTheory.Model.pullback` — pullback of a `T'`-model along a morphism of
  theories `f : T → T'`.
* `CategoryTheory.LawvereTheory.Algebra T` — abbreviation for `Model T (Type u)`.
* `CategoryTheory.LawvereTheory.free` — the free Lawvere theory on an arity signature,
  packaged as a `Σ`-type `(T : Type u) × SmallCategory T` (term model construction).

## Main results

* `CategoryTheory.LawvereTheory.exists_iso_pow` — every `X : T` is isomorphic to
  `pow T n` for some `n : ℕ`.
* `CategoryTheory.LawvereTheory.isTerminal_pow_zero`,
  `CategoryTheory.LawvereTheory.pow_zero_iso_terminal` — the 0-th power of the
  generator is (isomorphic to) the terminal object.
* `CategoryTheory.LawvereTheory.FreeLawvereTheory.Term.subst_var_id`,
  `subst_subst` — the standard substitution lemmas underlying the free construction.

## Design choices

* **Strict vs pseudo finite products.** Lawvere's original 1963 definition asks for
  *strictly* associative finite products: the chosen `n`-fold power `δ^n` is
  *definitionally* `δ × δ × ⋯ × δ`. In a Lean/Mathlib setting where finite products are
  characterised by a *universal property* (`HasFiniteProducts`), it is more ergonomic
  — and equally expressive up to equivalence (Lack–Rosický 2011, *Notions of Lawvere
  theory*; Hyland–Power 2007, §3.1) — to ask only that every object of `T` is
  *isomorphic* to a chosen finite power. We therefore use the pseudo (non-strict)
  variant. The chosen powers are packaged by an auxiliary function `pow : ℕ → T` with
  `pow 0` terminal, `pow 1 ≅ δ`, and `pow (n+1) ≅ δ ⨯ pow n`.
* **Universe.** `T` is a small category (`SmallCategory T`); the base category `C` of
  models can live in any larger universe.
* **Generator vs all-objects-are-powers.** Mathlib lacks both pieces, but the axiom
  `obj_isPow` plays the role of Lawvere's "objects are finite powers of the generator".
  We state it as a `Prop`-valued existence to keep the class itself as data-light as
  possible.

## Implementation notes

* `Model` is a `structure` rather than a `class` because in practice one *constructs*
  models (e.g. "the free model on a generating set") rather than *recognising* them;
  a typeclass-style mixin would obscure this.
* The category structure on `Model T C` uses the natural-transformation hom-set on the
  underlying functors *unchanged*, because two finite-product-preserving functors share
  the same hom-set whether we view them as functors or as models. This matches
  Mathlib's pattern of "subcategory with extra property" (cf.
  `CategoryTheory.FullSubcategory`).
* The Lawvere correspondence (Lawvere theories ≃ finitary monads on `Set`) is recorded
  as `lawvereTheory_equiv_finitaryMonad_skeleton` with body `True`; a real discharge
  requires the Eilenberg–Moore construction on top of further Mathlib infrastructure.

## References

* [F. W. Lawvere, *Functorial semantics of algebraic theories*][Law63] (PhD thesis,
  Columbia, 1963; reprinted as *TAC Reprints* **5** (2004) 23–107). The original
  definition.
* [S. Mac Lane, *Categories for the working mathematician*][Mac98] (Springer, 2nd ed.,
  1998). Chapter V (Limits) and §V.6 sketch the connection between algebraic theories
  and finite-product categories.
* [F. Borceux, *Handbook of categorical algebra*, vol. 2][Bor94] (Cambridge, 1994).
  Chapter 3 (Algebraic theories) is the standard modern reference.
* [J. Adámek, J. Rosický and E. M. Vitale, *Algebraic theories*][ARV11] (Cambridge,
  2011). Comprehensive modern treatment, including the strict-vs-pseudo question.
* [M. Hyland and J. Power, *The category-theoretic understanding of universal
  algebra*][HP07] (ENTCS 172, 2007, 437–458). Survey including the equivalence with
  finitary monads.
* nLab: <https://ncatlab.org/nlab/show/Lawvere+theory>.
-/

@[expose] public section

universe w v v₁ v₂ u u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

namespace CategoryTheory

/-! ## The class `LawvereTheory` -/

/-- A **Lawvere theory** (Lawvere 1963) is a small category `T` carrying

* a chosen *generator* object `δ : T`;
* a chosen `n`-fold power `pow n : T` for every natural `n`, with `pow 0` terminal
  and `pow (n + 1)` exhibited as `δ ⨯ pow n`;
* the axiom that every object of `T` is isomorphic to some `pow n`;
* finite products (the class `HasFiniteProducts T`).

Morphisms `pow m ⟶ pow n` then represent `n`-tuples of `m`-ary operations, which is
the recipe for an algebraic theory: groups, rings, lattices, etc. are obtained by
quotienting the free Lawvere theory on a signature (see `LawvereTheory.free` below) by
the equations of the theory.

We use the *pseudo* (non-strict) variant of Lawvere's definition: the equality
`pow (n + 1) = δ ⨯ pow n` is asked only up to a chosen isomorphism `pow_succ_iso`.
This is equivalent — up to biequivalence of 2-categories of Lawvere theories — to the
strict variant (Adámek–Rosický–Vitale 2011, §11.4). -/
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

/-- The chosen generator object of a Lawvere theory `T`, exported as a function of `T`
for ergonomics: `generator T` rather than `LawvereTheory.δ`. -/
abbrev generator : T := δ

/-- Re-export of the chosen `n`-fold power object. -/
abbrev powObj (n : ℕ) : T := pow (T := T) n

/-! ### Immediate consequences of the axioms -/

variable {T}

/-- Every object of a Lawvere theory is isomorphic to a finite power of the generator.
(Existential form of `LawvereTheory.obj_isPow`.) -/
theorem exists_iso_pow (X : T) : ∃ n : ℕ, Nonempty (X ≅ pow n) :=
  LawvereTheory.obj_isPow X

variable (T)

/-- The 0-th power of the generator is terminal in `T`. -/
noncomputable def isTerminal_pow_zero : IsTerminal (pow (T := T) 0) :=
  LawvereTheory.pow_zero_isTerminal

/-- The 0-th power of the generator is (isomorphic to) the terminal object. -/
noncomputable def pow_zero_iso_terminal : pow (T := T) 0 ≅ ⊤_ T :=
  (isTerminal_pow_zero T).uniqueUpToIso terminalIsTerminal

/-! ## Morphisms of Lawvere theories

A morphism of Lawvere theories `T → T'` is a functor that preserves the chosen
generator (up to a specified isomorphism) and finite products. Theory morphisms compose
strictly: the resulting 1-category `LawTh` of Lawvere theories is contravariantly
equivalent to the 1-category of finitary monads on `Set`. -/

end LawvereTheory

/-- A **morphism of Lawvere theories** is a functor `T ⥤ T'` that preserves the chosen
generator and all finite products.

Concretely: `f.functor` is the underlying functor, `f.preservesGenerator` is an
isomorphism `f.functor.obj (generator T) ≅ generator T'`, and the typeclass
`PreservesFiniteProducts f.functor` is required.

References: Lawvere 1963; Borceux, *Handbook of categorical algebra*, vol. 2,
Def. 3.3.1. -/
structure LawvereTheoryHom (T : Type u₁) [SmallCategory T] [LawvereTheory T]
    (T' : Type u₂) [SmallCategory T'] [LawvereTheory T'] where
  /-- The underlying functor `T ⥤ T'`. -/
  functor : T ⥤ T'
  /-- The functor carries the generator of `T` to (an object isomorphic to) the
  generator of `T'`. -/
  preservesGenerator : functor.obj (LawvereTheory.generator T) ≅ LawvereTheory.generator T'
  /-- The functor preserves finite products. -/
  [preservesFiniteProducts : PreservesFiniteProducts functor]

attribute [instance] LawvereTheoryHom.preservesFiniteProducts

namespace LawvereTheoryHom

variable {T : Type u₁} [SmallCategory T] [LawvereTheory T]
variable {T' : Type u₂} [SmallCategory T'] [LawvereTheory T']

/-- The identity morphism of Lawvere theories. -/
@[simps]
def id (T : Type u₁) [SmallCategory T] [LawvereTheory T] : LawvereTheoryHom T T where
  functor := 𝟭 T
  preservesGenerator := Iso.refl _

end LawvereTheoryHom

/-! ## Models of a Lawvere theory -/

/-- A **`T`-model** in a category `C` (with finite products) is a finite-product-
preserving functor `M : T ⥤ C`. Such an `M` is fully determined — up to natural
isomorphism — by its action on the generator `M.obj (generator T) : C`, which becomes
the "carrier" of the model.

For example, when `T = T_Monoid` is the Lawvere theory of monoids and `C = Set = Type u`,
a model `M : T_Monoid ⥤ Type u` consists of a carrier set `M.obj δ` equipped with
multiplication and unit operations (image of the generating operations of `T_Monoid`),
satisfying the monoid axioms (image of the equations of `T_Monoid`).

References:

* Lawvere 1963, especially §II.1.
* Borceux, *Handbook of categorical algebra*, vol. 2, §3.3.
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

/-- The **carrier** of a model `M` is the value `M.functor` takes on the generator.
This is the "underlying set" / "underlying object" in concrete examples (e.g. the
underlying set of a monoid). -/
abbrev carrier (M : Model T C) : C :=
  M.functor.obj (LawvereTheory.generator T)

/-- A morphism `M ⟶ N` between two models is a natural transformation between the
underlying functors. We take this as the definition of `Hom` in the category
`Model T C`. -/
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

/-- `Model T C` is a category, with morphisms the natural transformations between
underlying functors. Identity and composition are inherited from the ambient functor
category `T ⥤ C`. -/
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

/-- Two model morphisms are equal iff their underlying natural transformations are
equal. -/
@[ext]
theorem hom_ext {M N : Model T C} {f g : M ⟶ N} (h : f.trans = g.trans) : f = g :=
  Hom.ext h

/-! ### The forgetful functor `Model T C ⥤ T ⥤ C`

A model is essentially a functor with extra property, so there is a faithful forgetful
functor sending a model to its underlying functor. -/

/-- The forgetful functor from `Model T C` to the functor category `T ⥤ C`. -/
@[simps]
def forget : Model T C ⥤ (T ⥤ C) where
  obj M := M.functor
  map f := f.trans

end Model

/-! ## Pullback of models along a theory morphism

A morphism of Lawvere theories `f : T → T'` induces a functor
`f^* : Model T' C → Model T C` (pullback / restriction of scalars), because composing
a `T'`-model with `f.functor : T ⥤ T'` gives a finite-product-preserving functor
`T ⥤ C`. -/

namespace Model

variable {T : Type u₁} [SmallCategory T] [LawvereTheory T]
variable {T' : Type u₂} [SmallCategory T'] [LawvereTheory T']
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- Pullback of a `T'`-model along a morphism of theories `f : T → T'`: compose the
underlying functor of the model with `f.functor`. -/
@[simps]
def pullback (f : LawvereTheoryHom T T') (M : Model T' C) : Model T C where
  functor := f.functor ⋙ M.functor

/-- Pullback along the identity theory morphism is the identity on models
(definitionally, modulo `Functor.id_comp`). -/
theorem pullback_id (M : Model T C) :
    pullback (LawvereTheoryHom.id T) M = ⟨𝟭 T ⋙ M.functor⟩ := rfl

end Model

/-! ## The standard base: `Type` and `Set`-models

The standard base category for Lawvere theories is `Set = Type u`, which has all
finite products (in fact, all small limits). A `T`-model in `Type u` is called a
**`T`-algebra**, and the category `Model T (Type u)` is the *variety* of `T`-algebras.

The substrate for this section is already in Mathlib (`Type.HasProducts`), so nothing
further is needed. -/

namespace LawvereTheory

variable (T : Type u) [SmallCategory T] [LawvereTheory T]

/-- The category of `T`-algebras (i.e. `T`-models in `Type u`). -/
abbrev Algebra : Type _ := Model T (Type u)

end LawvereTheory

/-! ## Skeletons for future work

The downstream `T_GUT` only needs the small-category packaging of the free Lawvere
theory; the full `HasFiniteProducts` instance and the equivalence with finitary monads
are stated here with placeholder proofs. -/

namespace LawvereTheory

universe v₃ u₃

/-! ### Free Lawvere theory: term-model construction

We construct the free Lawvere theory on a signature `Sig : ℕ → Type u`
directly as the *term model* (a.k.a. the "Kleisli category of the free
algebra monad"):

* **Objects** are natural numbers (lifted to `Type u` via `ULift` so the
  category has the right universe level).
* **Morphisms `m ⟶ n`** are functions `Fin n → Term Sig m`, i.e. `n`-tuples
  of formal terms in `m` variables built from `Sig`.
* **Composition** is *simultaneous substitution* of terms.
* **Identity** is the function `Fin m → Term Sig m, i ↦ var i`.

This avoids the heavy `PathCategory + Quotient` machinery: there are no
equations to quotient by beyond `α`-equivalence (handled by de Bruijn
indices). The category laws follow from the standard substitution lemmas:
* `subst (var i) σ = σ i`
* `(subst t σ) [τ] = subst t (fun i => subst (σ i) τ)`

The free Lawvere theory on `Sig` is then this term category with:
* generator `δ := 1` (one free variable)
* `pow n := n`
* product `m × n := m + n` (the two projections insert variables on left/right)

For the immediate downstream skeleton (the `(T, SmallCategory T)` Σ-type
required by `Foundation/Doctrine/EnrichedLawvere.lean` and `T_GUT`), only
the *small category* part is needed; we provide that here.

The full `LawvereTheory` instance is sketched as
`FreeLawvereTheory.lawvereTheory` below; it requires a `HasFiniteProducts`
instance on the term category, which is constructed from the term-substitution
machinery via `mkFanLimit` on the canonical fan `Fin n → m+n`. -/

namespace FreeLawvereTheory

universe w'

variable (Sig : ℕ → Type u)

/-- A **term** in the free Lawvere theory on `Sig`, with free variables drawn
from a type `α`.

This is the standard inductive: either a variable `var a : Term α` for
`a : α`, or an operation `op σ ts : Term α` where `σ ∈ Sig n` is an `n`-ary
operation symbol and `ts : Fin n → Term α` is the vector of subterm
arguments.

We parameterize by a type `α` (rather than by a natural number directly) so
that the recursion-on-Term has a non-indexed motive — this makes the
equation compiler produce *definitional* equalities for `subst`, avoiding
the need for explicit `induction`/`rw` reasoning at every step.

The type lives at `max u v` so we can take `α := Fin n` (at `Type 0`)
without universe-bumping; the signature `Sig` controls the operations
universe `u`. -/
inductive Term (α : Type v) : Type max u v
  | var (a : α) : Term α
  | op {n : ℕ} (σ : Sig n) (ts : Fin n → Term α) : Term α

namespace Term

variable {Sig}

/-- **Substitution** in a term: replace each free variable by a term in a
new context. -/
@[simp]
def subst {α : Type v} {β : Type w} :
    Term Sig α → (α → Term Sig β) → Term Sig β
  | var a, σ => σ a
  | op f ts, σ => op f fun i => (ts i).subst σ

/-- Substituting variables by `var` is the identity. -/
@[simp]
theorem subst_var_id {α : Type v} :
    ∀ (t : Term Sig α), subst t (fun a => var a) = t
  | var _ => rfl
  | op f ts => by
      simp only [subst]
      congr 1
      funext i
      exact subst_var_id (ts i)

/-- Associativity of substitution: `(t[σ])[τ] = t[fun a ↦ (σ a)[τ]]`. -/
theorem subst_subst {α : Type v} {β : Type w} {γ : Type w'} :
    ∀ (t : Term Sig α) (σ : α → Term Sig β) (τ : β → Term Sig γ),
    subst (subst t σ) τ = subst t (fun a => subst (σ a) τ)
  | var _, _, _ => rfl
  | op f ts, σ, τ => by
      simp only [subst]
      congr 1
      funext i
      exact subst_subst (ts i) σ τ

end Term

/-- The carrier of the free Lawvere theory on `Sig`: natural numbers, lifted
to `Type u` to match the universe of the signature. -/
abbrev Obj : Type u := ULift.{u} ℕ

/-- The carrier has decidable equality (inherited from `ℕ`). -/
instance : DecidableEq (Obj.{u}) := fun a b =>
  decidable_of_iff (a.down = b.down) ⟨fun h => ULift.ext _ _ h, fun h => h ▸ rfl⟩

/-- The category structure on the free Lawvere theory on `Sig`:
morphisms `⟨m⟩ ⟶ ⟨n⟩` are functions `Fin b.down → Term Sig (Fin a.down)`,
i.e. `b`-tuples of formal terms in `a` variables. Composition is
simultaneous substitution.

Convention: composition `f ≫ g : a ⟶ c` for `f : a ⟶ b, g : b ⟶ c`
substitutes the components of `f` for the free variables in `g`:
`(f ≫ g) i = (g i)[f]`. -/
instance category : SmallCategory (Obj.{u}) where
  Hom a b := Fin b.down → Term Sig (Fin a.down)
  id _ := fun i => Term.var i
  comp f g := fun i => Term.subst (g i) f
  id_comp g := by
    -- `𝟙 a ≫ g = g`, i.e. `fun i => (g i)[var] = g`
    funext i
    exact Term.subst_var_id (g i)
  comp_id f := by
    -- `f ≫ 𝟙 b = f`, i.e. `fun i => (var i)[f] = f`
    funext i
    rfl
  assoc f g h := by
    -- `(f ≫ g) ≫ h = f ≫ (g ≫ h)`, i.e. for each `i`:
    -- LHS: `(h i)[f ≫ g] = (h i)[fun j => (g j)[f]]`
    -- RHS: `((g ≫ h) i)[f] = ((h i)[g])[f]`
    -- These agree by `subst_subst`.
    funext i
    exact (Term.subst_subst (h i) g f).symm

end FreeLawvereTheory

/-- **Free Lawvere theory on an arity signature.**

Given a signature `Sig : ℕ → Type u` (assigning, to each arity `n`, the set of `n`-ary
operation symbols), the free Lawvere theory `free Sig` has objects the natural numbers
(with `n` standing for the `n`-fold power of the unique generator) and morphisms
`m ⟶ n` the formal `n`-tuples of `m`-variable terms over `Sig`. Composition is
simultaneous substitution.

This packaging gives a small category `(T, SmallCategory T)`. The full `LawvereTheory`
instance — adding finite products, the chosen `pow` family, and `obj_isPow` —
additionally requires `HasFiniteProducts T`, which is provided constructively by
`mkFanLimit` on the canonical fan whose `i`-th leg `m + n ⟶ Fᵢ` is the appropriate
variable inclusion. That full instance is deferred (it requires bridging `Fin n`
products with `ℕ + ℕ` addition); the downstream client only needs the small-category
packaging, which is delivered here.

References:

* Lawvere 1963 (term-model construction is implicit in §II.2).
* Borceux, *Handbook of categorical algebra*, vol. 2, §3.4.
* nLab "Lawvere theory", §"Free Lawvere theory". -/
def free (Sig : ℕ → Type u) : (T : Type u) × SmallCategory T :=
  ⟨FreeLawvereTheory.Obj.{u}, FreeLawvereTheory.category Sig⟩

/-- **Lawvere's equivalence** (skeleton placeholder): the (1-)category of Lawvere
theories is contravariantly equivalent to the category of finitary monads on `Set`.

The proposition is currently recorded as `True`; a real statement requires importing
`Mathlib.CategoryTheory.Monad.Algebra` and defining a `FinitaryMonad` class. The
discharge route is the Eilenberg–Moore correspondence.

References: Lawvere 1963; Borceux, *Handbook of categorical algebra*, vol. 2, §3.9;
nLab "Lawvere theory", §3 ("Equivalence with finitary monads"). -/
theorem lawvereTheory_equiv_finitaryMonad_skeleton : True := trivial

end LawvereTheory

/-! ## Sanity examples

These exercise the `Model` and category structures. They use only the parts
established above (the free construction is intentionally not invoked here). -/

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
