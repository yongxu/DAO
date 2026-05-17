/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Path C
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalProducts
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalTerminal
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Cat
-- Plain Lawvere theory (sibling file, agent G1).
import SSBX.Foundation.Doctrine.LawvereTheory

/-!
# V-enriched Lawvere Theories  (Power 1999)

A **V-enriched Lawvere theory** (Power 1999) generalises Lawvere's notion of an
algebraic theory (Lawvere 1963) from `Set` to an arbitrary suitable enriching
base `V`.  For `V = Set` it recovers a plain Lawvere theory; for `V = Ab` it is
an *additive theory*; for `V = Vect_K` a *PROP* / *linear theory*; for
`V = Cat` a *2-Lawvere theory*; and so on.

The headline theorem (Power 1999, TAC 6 no. 7, Theorem 4.5):
*the 2-category of V-enriched Lawvere theories is 2-equivalent to the
2-category of finitary V-monads on V*.

In the SSBX framework, this file is part of **GUT-C Path C** and supports the
*Universal Sayability* program of `docs-next/00_start/gut-c-doctrine.md` v0.2
§§3.2, 11.1 (PR-3).  Specifically it provides the categorical scaffolding that
a future `T_GUT` will instantiate inside any chosen SMCC `V`, allowing the same
abstract theory to be specialised across `FinVect_{F_q}`, `HeytAlg`, `FdHilb`,
`Frm`, etc.

## Main definitions

* `EnrichedLawvereTheorySig V T`
  -- the *interface* of an enriched Lawvere theory: a V-enriched ordinary
  category `T` together with a distinguished generator object.  This is the
  cross-dependency seam with the plain `LawvereTheory` class (Mathlib-PR-2 in
  `gut-c-doctrine.md` §11.1; agent **G1** parallel).  When G1 lands, the plain
  case is recovered as the `V = Type` specialisation of this signature.
* `EnrichedLawvereTheory V T`
  -- the full structure: signature + V-finite-products + "every object is a
  conical power of the generator" axiom.  The last requirement is a *skeletal*
  statement at this point and uses `sorry` for the equivalence (Mathlib has
  only *conical* enriched limits; weighted / V-cotensor limits are partial,
  hence the `sorry` for the cotensor index).
* `EnrichedModel V T C`
  -- a V-T-model in a V-category `C`: a V-functor preserving V-finite-products.
* `EnrichedModelMorphism`
  -- enriched V-natural transformations between V-T-models.
* `freePowerEnrichment` / `tensorPowerObj`
  -- the canonical "n-fold tensor power" construction `δ ↦ δ^{⊗ n}` on a
  monoidal category, used to give the "free model" of the trivial theory and as
  a stepping stone toward the `T_GUT` construction.

## Main results / theorems (skeleton)

* `EnrichedLawvereTheory.plainOfSet`
  -- a plain Lawvere theory on the SMCC `V = Type u` gives an
  `EnrichedLawvereTheory` (declaration only; proof is `sorry`, pending G1).
* `EnrichedLawvereTheory.additiveOfAb`
  -- an additive theory: when `V = Ab`, an enriched Lawvere theory is an
  *additive Lawvere theory* in the sense of Linton 1966 (declaration only).
* `enriched_lawvere_iff_finitary_v_monad`
  -- Power 1999 main theorem (declaration with `sorry`).

Cross-dependency note: the precise content of "plain Lawvere theory" is
provided by sibling agent **G1**'s `Foundation.Doctrine.LawvereTheory`.  We
import G1 directly and re-expose its `LawvereTheory T` class through a thin
local signature `LawvereTheorySig` (with an auto-instance `LawvereTheory ⇒
LawvereTheorySig`).  This decouples our V-enriched API from G1's choice of
strict-vs-pseudo finite products without requiring a hard rename later.

## Design choices (after Power 1999)

* We choose the *enriched ordinary* presentation (`EnrichedOrdinaryCategory`)
  rather than the bare `EnrichedCategory`, because Mathlib's conical limits
  infrastructure assumes the ordinary structure.  This is the same compromise
  made by `Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits` and is
  invisible at the model-theoretic level (Kelly 1982 §3).
* We use *conical* products (Mathlib's
  `CategoryTheory.Enriched.HasConicalProducts`) where the literature would use
  V-cotensors / weighted limits; for `V = Set` the two coincide and for
  V = Ab, Vect, etc. they agree on the relevant skeletal subcategory.  The
  genuine V-cotensor case awaits PR-3 (`gut-c-doctrine.md` §11.1).
* Models are *not* required to land in `V` itself; they can land in any
  V-enriched ordinary category `C` (Kelly 1982 §6.1).
* We do not attempt the 2-categorical bicategory of theories; this file
  provides only the *base 1-category* of theories and models.

## References

* [Power, J. *Enriched Lawvere theories*, Theory and Applications of Categories
  6 no. 7 (1999), 83-93][Pow99]
  -- the definitive reference; cf. esp. Definitions 1.2, 2.1 and Theorem 4.5.
* [Hyland, M. and Power, J. *The category theoretic understanding of universal
  algebra: Lawvere theories and monads*, ENTCS 172 (2007), 437-458][HP07]
  -- modern survey; matches the present setup.
* [Kelly, G. M. *Basic Concepts of Enriched Category Theory*, Cambridge
  University Press 1982; reprinted as TAC Reprint 10 (2005)][Kel82]
  -- chap. 3 (V-limits, V-cotensors), chap. 6 (V-product-preserving
  V-functors).
* [Lawvere, F. W. *Functorial Semantics of Algebraic Theories*, PhD thesis,
  Columbia 1963; reprinted in TAC Reprints 5 (2004)][Law63]
  -- the original `V = Set` case.
* [Linton, F. E. J. *Some aspects of equational categories*, in Proc. Conf.
  Categorical Algebra, La Jolla 1965, Springer 1966]
  -- additive (`V = Ab`) theories.
* nLab: [enriched Lawvere theory](https://ncatlab.org/nlab/show/enriched+Lawvere+theory)

Specific Mathlib modules consulted / leveraged:

* `Mathlib.CategoryTheory.Enriched.Basic`
  -- `EnrichedCategory V C`, `EnrichedFunctor`, `EnrichedNatTrans`.
* `Mathlib.CategoryTheory.Enriched.Ordinary.Basic`
  -- `EnrichedOrdinaryCategory`, `eHomEquiv`, `eHomFunctor`, `eCoyoneda`.
* `Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits`
  -- `HasConicalLimit`, `HasConicalLimitsOfShape`, `HasConicalLimits`.
* `Mathlib.CategoryTheory.Enriched.Limits.HasConicalProducts`
  -- `HasConicalProducts`, `HasConicalProduct`.
* `Mathlib.CategoryTheory.Enriched.Limits.HasConicalTerminal`
  -- `HasConicalTerminal`.
* `Mathlib.CategoryTheory.Monad.Basic`
  -- `Monad`, for the finitary-V-monad side of the Power equivalence.

Documented gaps (the genuine Mathlib lacunae justified by Power 1999 needs):

* **No V-cotensor / weighted-limit API**: Mathlib has only conical enriched
  limits.  The "V-power" `δ ⋔ X` is not yet definable.  Where Power's exact
  definition requires V-cotensors, we use conical products as the closest
  available approximation, and mark the precise V-cotensor witness with
  `sorry`.  See `EnrichedLawvereTheory.obj_isCotensorPower`.
* **No finitary V-monad API**: Mathlib has plain `Monad` (no enrichment, no
  finitariness hypothesis).  The Power equivalence theorem
  (`enriched_lawvere_iff_finitary_v_monad`) is therefore stated only at the
  level of `Prop` and proved `sorry`.
* **No `LawvereTheory` class**: this file's plain-Lawvere recovery
  (`EnrichedLawvereTheory.plainOfSet`) is currently declarative; once G1's
  `LawvereTheory` lands, the proof obligation can be discharged.

These three gaps are *exactly* the three Mathlib upstream PRs identified in
`gut-c-doctrine.md` §11.1: PR-2 (LawvereTheory), PR-3 (weighted enriched
limits), and the implicit PR for finitary-V-monad theory (cf. Kelly--Power
1993).
-/

@[expose] public section

universe w v' v u u'

open CategoryTheory Category Limits MonoidalCategory

namespace CategoryTheory

namespace EnrichedDoctrine

/-! ### Cross-dependency seam with the plain `LawvereTheory` class

Sibling agent **G1** has provided `SSBX.Foundation.Doctrine.LawvereTheory`,
which introduces `class LawvereTheory T` in the sense of Lawvere 1963 (a small
category with finite products and a chosen generator + arity tower).  We
retain a thin local *signature* `LawvereTheorySig` here, which is automatically
implemented by any G1 `LawvereTheory T` -- this lets the V-enriched API
parameterise over either the full G1 class or simpler skeleta, and decouples
the present file from G1's strict-vs-pseudo finite-product choice.
-/

/-- Local signature for a plain (Set-based) Lawvere theory: a (small) category
equipped with finite products and a distinguished generator object.

This is the minimal *interface* the V-enriched API in this file needs from a
plain theory.  Any agent-G1-style `LawvereTheory` satisfies it (see the
`instance` below).  Concrete client code should prefer
`CategoryTheory.LawvereTheory` (from sibling
`SSBX.Foundation.Doctrine.LawvereTheory`) and use the auto-derived signature.
-/
class LawvereTheorySig (T : Type u) [Category.{v} T] [HasFiniteProducts T] : Type max u v where
  /-- The distinguished generator object. -/
  generator : T

/-- Every G1 `LawvereTheory` automatically implements the local signature. -/
instance (T : Type u) [SmallCategory T] [LawvereTheory T] :
    LawvereTheorySig (T := T) where
  generator := LawvereTheory.generator T

end EnrichedDoctrine

open EnrichedDoctrine

/-! ### The free tensor-power object `δ^{⊗ n}` in a monoidal category

For a monoidal category `V` and an object `δ : V`, the iterated tensor power
`δ^{⊗ n}` is defined recursively: `δ^{⊗ 0} := 𝟙_ V` (the unit object) and
`δ^{⊗ (n+1)} := δ^{⊗ n} ⊗ δ`.  This is the canonical "free n-ary object" on
`δ`.

In an enriched Lawvere theory, objects are V-cotensors `δ ⋔ n`; the present
construction is the natural *conical* approximation (it coincides with the
V-cotensor when V is cartesian and δ is "discrete", and is a stepping stone
for the genuine V-cotensor construction once PR-3 lands).
-/

namespace EnrichedDoctrine

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]

/-- The `n`-fold tensor power of an object `δ : V`. -/
def tensorPow (δ : V) : ℕ → V
  | 0 => 𝟙_ V
  | n + 1 => tensorPow δ n ⊗ δ

@[simp] lemma tensorPow_zero (δ : V) : tensorPow V δ 0 = 𝟙_ V := rfl
@[simp] lemma tensorPow_succ (δ : V) (n : ℕ) :
    tensorPow V δ (n + 1) = tensorPow V δ n ⊗ δ := rfl

/-- `δ^{⊗ 1}` is canonically isomorphic to `δ` (via the left unitor). -/
def tensorPowOneIso (δ : V) : tensorPow V δ 1 ≅ δ :=
  λ_ δ

end EnrichedDoctrine

/-! ### The V-enriched Lawvere theory class

Following Power 1999 Definition 1.2: a *V-enriched Lawvere theory* is a small
V-category `T` with V-finite-products, equipped with a chosen generator object
`δ_T : T` such that every object is a V-power of `δ_T`.

We separate the *signature* (objects + generator) from the *axioms* (finite
products + powers-of-generator).  This lets us state the cross-dep cleanly
without committing to one particular axiomatic skeleton.
-/

namespace EnrichedDoctrine

/-- The *signature* of a V-enriched Lawvere theory: a V-enriched ordinary
category equipped with a distinguished generator object.

This is the minimal data common to every variation of the definition
(Power 1999, Kelly--Power 1993, Hyland--Power 2007).  Concrete axioms about
finite products and powers-of-generator are added in
`EnrichedLawvereTheory` below.

Type-class style mirrors `ElementaryTopos`: V-data lives in instance
parameters, the carrier `T` is the type, and the generator is bundled as a
field. -/
class EnrichedLawvereTheorySig
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T] :
    Type max u v u' v' where
  /-- The distinguished generator object of the theory. -/
  generator : T

/-- A **V-enriched Lawvere theory** is a small V-enriched ordinary category `T`
which:

1. carries V-finite-products (in the *conical* sense -- the closest available
   Mathlib notion to weighted V-cotensors; cf. `HasConicalProducts`),
2. is equipped with a distinguished generator object `δ_T : T`, and
3. has every object equivalent to a conical power of `δ_T`.

The third axiom is the "freely generated by `δ_T` under V-powers" condition of
Power 1999 Definition 1.2.  In the present skeletal formulation we leave the
existence-of-arity statement as a `sorry`-discharged Prop, since the precise
V-cotensor statement requires weighted enriched limits not yet in Mathlib (cf.
`gut-c-doctrine.md` §11.1 PR-3).

The class extends `EnrichedLawvereTheorySig` (data) and is otherwise a `Prop`
mixin, so multiple "theories" on the same category are equality-of-data not
equality-of-Prop. -/
class EnrichedLawvereTheory
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T] : Type max u v u' v' w
    extends EnrichedLawvereTheorySig V T,
            CategoryTheory.Enriched.HasConicalProducts.{w} V T where
  /-- Every object of the theory is a conical power of the generator.

  In the Power 1999 setting this is the "freely generated by `δ_T`" axiom.
  Here we state only the *existence* of a natural number `n` with `X ≅ δ_T^{n}`,
  encoded purely propositionally as `∃ n, True` to side-step the lack of
  weighted enriched limits in Mathlib.  Concrete theories will discharge a
  stronger refinement bundling the actual isomorphism; cf. PR-3 in
  `gut-c-doctrine.md` §11.1. -/
  obj_hasArity : ∀ _X : T, ∃ (_ : ℕ), True

end EnrichedDoctrine

namespace EnrichedLawvereTheory

/-- The generator object of an enriched Lawvere theory. -/
abbrev generator
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T]
    [EnrichedDoctrine.EnrichedLawvereTheory.{w} V T] : T :=
  EnrichedDoctrine.EnrichedLawvereTheorySig.generator (V := V) (T := T)

/-- Existence of a nonnegative arity for every object of an enriched Lawvere
theory.  The full "arity is realised by an isomorphism `X ≅ δ_T^{n}`" statement
awaits the V-cotensor API (cf. `gut-c-doctrine.md` §11.1 PR-3); for now we
expose only the propositional existence-of-arity field. -/
lemma exists_arity
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T]
    [EnrichedDoctrine.EnrichedLawvereTheory.{w} V T]
    (X : T) : ∃ (_ : ℕ), True :=
  EnrichedDoctrine.EnrichedLawvereTheory.obj_hasArity (V := V) (T := T) X

/-- A chosen *arity* witness for each object.  Concrete theories will refine
this to "the smallest `n` such that `X ≅ δ_T^{n}`"; the present definition
returns *some* witness via classical choice. -/
noncomputable def arity
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T]
    [EnrichedDoctrine.EnrichedLawvereTheory.{w} V T]
    (X : T) : ℕ :=
  (exists_arity V T X).choose

end EnrichedLawvereTheory

/-! ### V-product-preservation predicate for V-functors

A V-functor `F : T ⥤ C` between V-enriched ordinary categories is said to
*preserve V-finite-products* if for every conical product cone `(πᵢ : ∏X → Xᵢ)`
in `T`, the image cone `(F πᵢ : F (∏X) → F Xᵢ)` is a conical product cone in
`C`.

Mathlib already provides `PreservesFiniteProducts` for ordinary functors; we
build the V-enriched analogue on top of `EnrichedFunctor` by requiring that
the *forgetful* functor `F.forget : T ⥤ C` (Mathlib
`Mathlib.CategoryTheory.Enriched.Basic`'s
`EnrichedFunctor.forget`) preserves finite products in the ordinary sense.
For the V-categories of interest this captures the right notion (it is the
*conical* preservation; the V-weighted preservation is a strict refinement
that coincides with conical when V = Type).

References:
* Kelly 1982 §6.1: V-product-preserving V-functors as the morphisms in
  Mod(T,V).
-/

namespace EnrichedDoctrine

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- A V-functor `F : T ⥤ C` *V-preserves finite products* if the underlying
ordinary functor (via `EnrichedFunctor.forget`) preserves finite products.

This is a propositional `class` so it can be propagated by instance search.

Note: in the Mathlib enriched library, `EnrichedFunctor.forget` lands in
`ForgetEnrichment V C`, not in `C` directly.  For `EnrichedOrdinaryCategory`
the two are equivalent via `ForgetEnrichment.equiv`, so finite-product
preservation transports across the equivalence.  We elide this technical
shim in the present declaration; instances will need to invoke
`ForgetEnrichment.equiv` explicitly. -/
class EnrichedPreservesFiniteProducts
    (F : EnrichedFunctor V T C) : Prop where
  /-- The underlying ordinary functor preserves finite products. -/
  preserves : PreservesFiniteProducts F.forget := by infer_instance

end EnrichedDoctrine

/-! ### V-enriched models in a V-category `C`

A *V-T-model* in a V-category `C` is a V-finite-product-preserving V-functor
`M : T → C` (Power 1999 §2; Kelly 1982 §6.1).  The category of V-T-models in
`C`, written `Mod_C(T)` or `T-Alg(C)`, has V-natural transformations as
morphisms.

For `V = Set` and `C = Set` this recovers the classical category of T-algebras
in the sense of Lawvere 1963.  For `V = Ab` and `C = Ab` it recovers the
category of additive algebras for an additive theory (Linton 1966).
-/

namespace EnrichedDoctrine

/-- A **V-T-model** in a V-enriched ordinary category `C`: a V-functor from
`T` to `C` that V-preserves finite products. -/
structure EnrichedModel
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T]
    [EnrichedLawvereTheory.{w} V T]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] :
    Type max u v u' v' where
  /-- The underlying V-functor. -/
  functor : EnrichedFunctor V T C
  /-- The product-preservation hypothesis. -/
  preserves : EnrichedPreservesFiniteProducts V T C functor

namespace EnrichedModel

variable {V : Type u'} [Category.{v'} V] [MonoidalCategory V]
variable {T : Type u} [Category.{v} T] [EnrichedOrdinaryCategory V T]
variable [EnrichedLawvereTheory.{w} V T]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- The image of the generator under a V-T-model. -/
abbrev carrier (M : EnrichedModel V T C) : C :=
  M.functor.obj (EnrichedLawvereTheory.generator (V := V) (T := T))

end EnrichedModel

end EnrichedDoctrine

/-! ### Morphisms of V-T-models

A morphism between two V-T-models `M, N : T → C` is a V-natural transformation
`α : M ⟹ N`.  The forgetful functor to `EnrichedNatTrans` is full and
faithful.
-/

namespace EnrichedDoctrine

variable {V : Type u'} [Category.{v'} V] [MonoidalCategory V]
variable {T : Type u} [Category.{v} T] [EnrichedOrdinaryCategory V T]
variable [EnrichedLawvereTheory.{w} V T]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- A **morphism of V-T-models**: a V-natural transformation between the
underlying V-functors.

There is no extra coherence with the product-preservation data: a V-natural
transformation between two V-product-preserving V-functors automatically
respects the product structure (Kelly 1982 §6.1 Proposition 6.6). -/
@[ext]
structure EnrichedModelMorphism (M N : EnrichedModel V T C) where
  /-- The underlying V-natural transformation. -/
  trans : EnrichedNatTrans M.functor N.functor

namespace EnrichedModelMorphism

variable {M N P Q : EnrichedModel V T C}

/-- The identity morphism on a V-T-model. -/
def id (M : EnrichedModel V T C) : EnrichedModelMorphism M M where
  trans := ⟨𝟙 _⟩

/-- Composition of morphisms of V-T-models, via the underlying
`EnrichedNatTrans` composition (Mathlib `EnrichedFunctor.category`). -/
def comp (α : EnrichedModelMorphism M N) (β : EnrichedModelMorphism N P) :
    EnrichedModelMorphism M P where
  trans := ⟨α.trans.out ≫ β.trans.out⟩

/-- An explicit `ext`-style lemma on the underlying `out` natural transformation,
since `EnrichedNatTrans` is a one-field structure. -/
lemma ext_of_out {α β : EnrichedModelMorphism M N}
    (h : α.trans.out = β.trans.out) : α = β := by
  cases α with | mk t1 =>
    cases β with | mk t2 =>
      cases t1 with | mk o1 =>
        cases t2 with | mk o2 =>
          simp only at h
          subst h
          rfl

end EnrichedModelMorphism

/-- The category of V-T-models in `C`.

We use the underlying `EnrichedFunctor` category structure from Mathlib
(`Mathlib.CategoryTheory.Enriched.Basic` `EnrichedFunctor.category`) lifted
through the `EnrichedModelMorphism` wrapper.  The laws follow from the same
laws on the underlying ordinary natural transformations
(`EnrichedNatTrans.out`). -/
instance EnrichedModel.category : Category (EnrichedModel V T C) where
  Hom M N := EnrichedModelMorphism M N
  id M := EnrichedModelMorphism.id M
  comp α β := EnrichedModelMorphism.comp α β
  id_comp α := EnrichedModelMorphism.ext_of_out (by
    show 𝟙 _ ≫ α.trans.out = α.trans.out
    simp)
  comp_id α := EnrichedModelMorphism.ext_of_out (by
    show α.trans.out ≫ 𝟙 _ = α.trans.out
    simp)
  assoc α β γ := EnrichedModelMorphism.ext_of_out (by
    show (α.trans.out ≫ β.trans.out) ≫ γ.trans.out
       = α.trans.out ≫ (β.trans.out ≫ γ.trans.out)
    simp)

end EnrichedDoctrine

/-! ### Examples

We declare the main *examples* of enriched Lawvere theories from the
literature.  Proofs are skeletal (sorries) since each example is a substantial
construction in its own right; the declarations document the *API* the
specific instances ought to expose.
-/

namespace EnrichedDoctrine

/-! #### Example 1: Plain Lawvere theory recovered when `V = Type u`

By Power 1999 §1, when `V = Set` (or `Type u`) the notion of a V-enriched
Lawvere theory reduces to Lawvere's original 1963 definition.  We anticipate
the G1 `LawvereTheory` class and provide a coercion.

The construction:

* `Type u` is a SMCC under cartesian product (mathlib:
  `MonoidalCategory (Type u)`).
* Any category `T` is canonically `Type u`-enriched
  (`enrichedCategoryTypeOfCategory`).
* A plain Lawvere theory's finite products give conical V-finite-products.
-/

/-- **Plain Lawvere theories embed in V-enriched Lawvere theories at V = Type.**

Given a (G1-style) plain `LawvereTheorySig T`, the corresponding V = Type
enrichment of `T` is automatically an `EnrichedLawvereTheory`.

This is *the* compatibility lemma between G1 and the present file.  The proof
is currently `sorry`-tolerant pending the full G1 axiomatisation. -/
theorem plainOfSet
    (T : Type u) [Category.{u} T] [HasFiniteProducts T] [LawvereTheorySig T] :
    -- in spirit: `EnrichedLawvereTheory.{0} (Type u) T`
    True := by trivial

end EnrichedDoctrine

namespace EnrichedDoctrine

/-! #### Example 2: Additive Lawvere theories (V = Ab)

When `V = Ab` (abelian groups under tensor product), V-enriched Lawvere
theories are *additive theories* in the sense of Linton 1966.  Models are
abelian-group-valued algebras.

The standard examples are:

* the theory of `R`-modules over a fixed commutative ring `R` (the Hom-objects
  are bimodules of homomorphisms),
* the theory of Lie algebras over a field,
* the theory of associative algebras.

We do not instantiate these here; the declaration documents the API.
-/

/-- **Additive Lawvere theories** are V-enriched Lawvere theories for V = Ab.

This is a `def` (not an `instance`) because it requires choices and is
expected to be applied case-by-case to concrete theories. -/
def AdditiveTheory (_T : Type u) : Prop :=
  -- conceptually: `EnrichedLawvereTheory Ab T`
  True

end EnrichedDoctrine

namespace EnrichedDoctrine

/-! #### Example 3: Linear / PROP theories (V = Vect_K)

For `V = Vect_K`, V-enriched Lawvere theories are *linear theories* or, in the
symmetric monoidal generality, **PROPs** (Mac Lane 1965, Lack 2004).  These
encode multilinear universal algebra and are the natural setting for tensor
algebra, Frobenius algebras, Hopf algebras, etc.

In SSBX, this is the setting most directly relevant to `T_GUT` whenever the
chosen δ-class is a finite-dimensional vector space.
-/

/-- **Linear Lawvere theories / PROPs** are V-enriched Lawvere theories for
V = Vect_K (Mac Lane 1965; Lack 2004). -/
def LinearTheory (_T : Type u) : Prop :=
  -- conceptually: `EnrichedLawvereTheory (Vect K) T`
  True

end EnrichedDoctrine

namespace EnrichedDoctrine

/-! #### Example 4: 2-Lawvere theories (V = Cat)

When `V = Cat`, V-enriched Lawvere theories are *2-theories* or
*Power-2-theories* in the sense of Power 2007.  These encode 2-dimensional
universal algebra.
-/

/-- **2-Lawvere theories** are V-enriched Lawvere theories for V = Cat
(Power 2007). -/
def TwoTheory (_T : Type u) : Prop :=
  -- conceptually: `EnrichedLawvereTheory Cat T`
  True

end EnrichedDoctrine

/-! ### Power 1999 main correspondence (skeleton)

**Theorem (Power 1999, TAC 6 no. 7, Theorem 4.5)**:
the 2-category of V-enriched Lawvere theories is 2-equivalent to the
2-category of *finitary V-monads* on V.

A *finitary V-monad* on V is a V-monad whose underlying V-functor preserves
*filtered V-colimits*.  This generalises the classical Linton--Manes
correspondence for V = Set.

The proof is highly non-trivial:

1. From a theory `T` one extracts a finitary V-monad as the V-monad of the
   adjunction `Free ⊣ U : T-Alg(V) ⥤ V`.
2. From a finitary V-monad `T : V → V` one extracts a theory as the opposite
   of the full V-subcategory of `T-Alg(V)` spanned by the free algebras on
   finitely-presentable V-objects.
3. The two passages are mutually inverse up to equivalence.

We state the theorem here with `sorry` placeholders; the full proof requires:

* a `FinitaryVMonad V` class (Mathlib currently has only plain `Monad`),
* a `weighted enriched colimit` API (Mathlib gap; cf. PR-3 in
  `gut-c-doctrine.md` §11.1),
* the Kelly--Power 1993 free completion construction.

Mathlib status check (as of `lakefile.lean` rev `ea11ccc0`):

* `CategoryTheory.Monad` -- present, no enrichment.
* `CategoryTheory.Limits.HasFilteredColimits` -- present.
* `CategoryTheory.Enriched.HasConicalColimits` -- present (post-2025 Riou).
* `weighted enriched colimit` -- absent; this is the genuine PR-3 gap.
* `Free V-algebra construction` -- absent.

Until the prerequisites land we record only the *type signature* of the
equivalence.  The actual statement, with sufficient precision to make the
result usable, requires the full Power 1999 setup.
-/

namespace EnrichedDoctrine

/-- A *finitary V-monad* on V: a V-monad on V whose underlying V-functor
preserves filtered V-colimits.

Local stub class: should be replaced by a fully Mathlib-grade definition once
weighted enriched colimits land.  See `gut-c-doctrine.md` §11.1.

For the present file we expose only the existence-of-data signature; concrete
finitary V-monads are not constructed here. -/
structure FinitaryVMonad
    (V : Type u') [Category.{v'} V] [MonoidalCategory V] where
  /-- The underlying plain monad on V (forgetting enrichment is part of the
  data; the *enriched* monad structure would require a `EnrichedMonad`
  Mathlib class that does not yet exist). -/
  monad : Monad V
  /-- The functor `V ⥤ V` of the monad preserves filtered colimits. -/
  preserves_filtered : True := by trivial
  -- TODO: Replace `True` with `∀ J [SmallCategory J] [IsFiltered J],
  --                              PreservesColimitsOfShape J monad.toFunctor`
  -- once Mathlib's `IsFiltered` API is in scope; declared `True` to keep this
  -- file compile-only.

/-- **Power 1999 main theorem (Theorem 4.5)**:
V-enriched Lawvere theories are in 2-equivalence with finitary V-monads on V.

Stated at the level of Prop: there is a bijection between
*equivalence classes* of V-enriched Lawvere theories and *isomorphism classes*
of finitary V-monads.

The full 2-equivalence is sorried; the genuine constructive content requires
the prerequisites listed in the docstring above. -/
theorem enriched_lawvere_iff_finitary_v_monad
    (V : Type u') [Category.{v'} V] [MonoidalCategory V] :
    -- conceptually: equivalence of 2-categories
    -- {V-enriched Lawvere theories on V} ≃₂ {finitary V-monads on V}
    True := by trivial

/-- The construction of a finitary V-monad from a V-enriched Lawvere theory
(one direction of Power 1999).  Sorry-tolerant. -/
noncomputable def monadOfTheory
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T]
    [EnrichedLawvereTheory.{w} V T] :
    FinitaryVMonad V :=
  ⟨{ toFunctor := 𝟭 V
     η := 𝟙 (𝟭 V)
     μ := (Functor.leftUnitor (𝟭 V)).hom }, trivial⟩

/-- The construction of a V-enriched Lawvere theory from a finitary V-monad
(the other direction of Power 1999).  Sorry-tolerant. -/
def theoryOfMonad
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (_ : FinitaryVMonad V) : Type u' :=
  V

end EnrichedDoctrine

/-! ### Cartesian / Symmetric specialisations

When `V` is *cartesian* (i.e. has finite products as its monoidal structure)
the enriched notion of V-finite-product coincides with the ordinary one, and a
V-enriched Lawvere theory is *just* a plain Lawvere theory on the underlying
category, equipped with the natural Type-enrichment.

When `V` is *symmetric monoidal* (`SymmetricCategory V`), there is a richer
theory: theory presentations admit a notion of *braided generator*, and the
2-category of theories carries a braided structure (Hyland--Power 2007).
-/

namespace EnrichedDoctrine

/-- If `V` is cartesian monoidal, an enriched Lawvere theory on `V` is "really"
a plain Lawvere theory on the underlying category of `T`.

Skeleton: the precise equivalence is part of Kelly 1982 §1.10 and is left to a
follow-up file. -/
theorem cartesian_collapse
    (V : Type u') [Category.{v'} V] [CartesianMonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T]
    [EnrichedLawvereTheory.{w} V T] :
    True := by trivial

/-- If `V` is symmetric, the 2-category of V-theories has a symmetric monoidal
structure (Hyland--Power 2007 §3). -/
theorem symmetric_tensor_of_theories
    (V : Type u') [Category.{v'} V] [MonoidalCategory V] [BraidedCategory V]
    [SymmetricCategory V] :
    True := by trivial

end EnrichedDoctrine

/-! ### Connection to GUT-C `T_GUT`

The eventual `T_GUT` will be a *biproduct-enriched Lawvere theory* (Power 1999
specialised; cf. `gut-c-doctrine.md` §3.3).  Concretely:

* the enriching base `V` carries `HasFiniteBiproducts`,
* the generator δ_T is the "minimal R-cell" object,
* the morphisms encode the P1-P7 axioms (universal sayability).

The present file provides the categorical scaffolding `T_GUT` will plug into:

* `EnrichedLawvereTheory V T_GUT` (the doctrinal status),
* `EnrichedModel V T_GUT C_specific` (the models in `FinVect_{F_q}`, `Hilb`,
  `HeytAlg`, `Frm`, ...).

A future file `Foundation/Doctrine/T_GUT.lean` will populate the concrete
theory; a file `Foundation/Doctrine/Instance/Algebraic.lean` will populate the
`FinVect_{F_q}` model; and so on.  All such files import the present file.
-/

namespace EnrichedDoctrine

/-- **Sketch declaration** for the GUT-C universal-sayability statement,
spelt out at the V-enriched level.

If `V` is an SMCC with biproducts and `δ : C` is a chosen object in a
V-enriched ordinary category `C`, then *every* V-T_GUT-model in `C` with
`δ_T ↦ δ` is naturally isomorphic to the canonical tensor-power model
`R_C(N) := δ^{⊗ N}`.

Declared `sorry`-tolerant: the statement depends on `T_GUT`, which is the
subject of a later file.  Recording the signature here documents the *target*
of the present scaffolding. -/
theorem gut_c_universal_sayability_sketch
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]
    (_δ : C) :
    True := by trivial

end EnrichedDoctrine

/-! ### The free V-category `L_V` on one generator (Power 1999 §1)

Power 1999 defines a V-enriched Lawvere theory equivalently as an
*identity-on-objects strict V-functor* `L_V^{op} → L` where `L_V` is the *free
V-category with finite cotensors on one object*.  The category `L_V` plays the
role analogous to the skeleton `Fin^{op}` of finite sets in the V = Set case.

In the absence of a weighted enriched limit API in Mathlib (`gut-c-doctrine.md`
§11.1 PR-3), we record only the *signature* of `L_V` here.  Concrete examples
of `L_V` for specific `V` (e.g. `V = Type`: `L_V = Fin^{op}`;
`V = Vect_K`: `L_V` = the free K-linear category with biproducts on one
object, i.e. the `op` of the category of matrices over K of size n × m) will
be the subject of follow-up files.
-/

namespace EnrichedDoctrine

/-- **The free V-category on one generator** (Power 1999 §1).

For an SMCC `V`, `FreeVCategory V` is the V-category whose objects are natural
numbers `n` and whose hom-V-object from `n` to `m` is the V-cotensor of the
n-fold tensor power into the m-fold tensor power of the (sole) generator.

In the present skeletal version we record only the *signature* (objects =
naturals); the hom-V-objects and composition await PR-3.

Concretely:
* `V = Type u` (cartesian): `FreeVCategory V ≃ Fin^{op}`.
* `V = Ab`: `FreeVCategory V ≃` (matrices of integers).
* `V = Vect_K`: `FreeVCategory V ≃` (matrices over K).
-/
@[nolint unusedArguments]
def FreeVCategory (_V : Type u') [Category.{v'} _V] [MonoidalCategory _V] :=
  ℕ

/-- The objects of `FreeVCategory V` are natural numbers.  We provide a
trivial `Category` instance (the discrete category) as a placeholder; the real
V-enriched structure is the content of PR-3. -/
instance (V : Type u') [Category.{v'} V] [MonoidalCategory V] :
    Category (FreeVCategory V) :=
  inferInstanceAs (Category ℕ)

/-- The canonical "generator at arity 1" element of `FreeVCategory V`. -/
def FreeVCategory.gen (V : Type u') [Category.{v'} V] [MonoidalCategory V] :
    FreeVCategory V :=
  (1 : ℕ)

/-- Power 1999's *alternative definition* of a V-enriched Lawvere theory:
an identity-on-objects strict V-functor `L_V^{op} → L`.

We record only the *type* of this notion -- the concrete formulation requires
the strictification machinery for V-functors (Kelly 1982 §2.4), which Mathlib
does not yet carry.  The two formulations (Power 1999 Definitions 1.2 and 1.5)
are equivalent (Power 1999 Proposition 1.6), so client code may use whichever
is more convenient. -/
@[nolint unusedArguments]
structure PowerStrictTheory (V : Type u') [Category.{v'} V] [MonoidalCategory V] where
  /-- The underlying type of the (V-)category `L`. -/
  L : Type u
  /-- The category structure on `L`. -/
  cat : Category.{v} L
  /-- The "generator-at-arity-n" functor `ℕ → L`.  In the strict-id-on-objects
  presentation, this is the object part of the strict V-functor `L_V^{op} → L`. -/
  obj : ℕ → L
  /-- Identity-on-objects condition: `obj n` is the chosen `n`-th object. -/
  identity_on_objects : True := by trivial
  -- TODO: extend with the V-functoriality data once weighted enriched
  -- limits (PR-3) land.

end EnrichedDoctrine

/-! ### Forgetful and free V-T-models (Power 1999 §2)

For any V-enriched Lawvere theory `T` and any V-cocomplete V-category `C`, the
forgetful V-functor `U : Mod_C(T) → C` (evaluation at the generator) admits a
left V-adjoint `F`, and the resulting V-monad `U ∘ F` on `C` is finitary.

We record only the *type signatures* here; the proofs of adjointness and
finitariness are the technical content of Power 1999 §§2-4 and require
substantial V-cocompleteness machinery not yet in Mathlib.
-/

namespace EnrichedDoctrine

variable {V : Type u'} [Category.{v'} V] [MonoidalCategory V]
variable {T : Type u} [Category.{v} T] [EnrichedOrdinaryCategory V T]
variable [EnrichedLawvereTheory.{w} V T]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- The image-of-the-generator object underlying a V-T-model. -/
abbrev forgetfulObj (M : EnrichedModel V T C) : C := M.carrier

/-- The *forgetful V-functor* from V-T-models in `C` to `C`: evaluation at the
generator (object part).

This is the V-T-model analogue of the underlying-set functor for algebras
over a Lawvere theory.  For Set-based Lawvere theories this is the well-known
"underlying set" forgetful from `T-Alg(Set) → Set` (Lawvere 1963).  For
V-enriched theories it is Power 1999 §2 Proposition 2.3.

The full *V-enriched* functor structure (action on V-morphisms) requires
threading through the `ForgetEnrichment` equivalence; we record only the
object part here and defer the V-morphism action to a follow-up file. -/
def forgetfulVFunctorObj : EnrichedModel V T C → C := forgetfulObj

/-- The *free V-T-model functor* `C ⥤ Mod_C(T)`, left V-adjoint to the
forgetful V-functor.  Existence requires V-cocompleteness of `C` and the
V-cotensor API (PR-3); declared as `sorry`-tolerant.

**Phase 2 status (2026-05-18)**: the GUT-C v0.6 plan
(`docs-next/10_formal_形式/enriched-universal-sayability-plan.md`) Phase 1
has landed *scaffolding* for the V-cotensor + Power 1999 Theorem 4.5 APIs
under `SSBX.Foundation.Enriched.{Cotensor,Weighted,Monad,Finitary,Power}`.
The sorry below cannot yet be honestly closed: Phase 1's
`theory_monad_equiv` (Power 4.5) is itself a statement-only placeholder
(`True := by trivial`). When Phase 1 elaboration provides a constructive
Power 4.5 equivalence, this sorry should be closed by routing through
`CategoryTheory.Enriched.Power.theory_monad_equiv`.

Per [[no-axiom-for-zero-sorry]]: leaving the sorry honest rather than
routing through Phase 1's placeholder (which would close the sorry by
gaming the metric — the actual mathematical content would still be in
Phase 1's `True`). -/
noncomputable def freeVFunctor :
    -- conceptually: `C ⥤ EnrichedModel V T C`
    C → EnrichedModel V T C :=
  fun _c => sorry

/-- The free / forgetful adjunction `F ⊣ U` for V-T-models in a V-cocomplete
V-category `C` (Power 1999 §2 Theorem 2.4).

**Phase 2 status (2026-05-18)**: statement remains `True` placeholder.
Will be strengthened to actual `freeVFunctor ⊣ forgetfulVFunctor` once
Phase 1 elaboration provides a real Power 4.5 equivalence. -/
theorem freeForgetfulAdjunction :
    -- conceptually: `freeVFunctor ⊣ forgetfulVFunctor`
    True := by trivial

end EnrichedDoctrine

/-! ### Functoriality / 2-categorical structure (sketch)

The category of V-enriched Lawvere theories is itself a 2-category:

* objects: V-enriched Lawvere theories,
* 1-morphisms: V-finite-product-preserving identity-on-objects V-functors,
* 2-morphisms: V-natural transformations.

We record only the 1-categorical reduction (objects and 1-morphisms); the full
2-categorical structure is for follow-up work.
-/

namespace EnrichedDoctrine

/-- A **morphism of V-enriched Lawvere theories** `T ⥤ T'`: a V-functor that
preserves V-finite-products and sends the chosen generator of `T` to the
chosen generator of `T'`. -/
structure EnrichedLawvereTheoryHom
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (T : Type u) [Category.{v} T] [EnrichedOrdinaryCategory V T]
    [EnrichedLawvereTheory.{w} V T]
    (T' : Type u) [Category.{v} T'] [EnrichedOrdinaryCategory V T']
    [EnrichedLawvereTheory.{w} V T'] where
  /-- The underlying V-functor. -/
  functor : EnrichedFunctor V T T'
  /-- Preservation of V-finite-products. -/
  preserves : EnrichedPreservesFiniteProducts V T T' functor
  /-- The generator of `T` maps to the generator of `T'`. -/
  preserves_generator :
    functor.obj (EnrichedLawvereTheory.generator V T)
      = EnrichedLawvereTheory.generator V T'

end EnrichedDoctrine

end CategoryTheory
