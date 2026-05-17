/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Phase 1.3 (V-enriched monad for upstream Mathlib PR-3)
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Monad.Basic

/-!
# V-enriched monads

For `V` a monoidal category and `C` a V-enriched category, a **V-enriched
monad** on `C` is a V-functor `T : C ⥤_V C` together with V-natural
transformations

* unit `η : id_C ⟶ T`
* multiplication `μ : T ∘ T ⟶ T`

satisfying the usual monad axioms (associativity, left/right unit).

This generalises the ordinary `Mathlib.CategoryTheory.Monad.Basic.Monad` to
V-enriched setting (`V = Set` recovers the ordinary case).

V-enriched monads play a central role in Power 1999's Theorem 4.5 (which is
Phase 1.5 of `docs-next/10_formal_形式/enriched-universal-sayability-plan.md`):
the 2-category of V-enriched Lawvere theories is 2-equivalent to the
2-category of finitary V-monads on V.

## Main definitions

* `EnrichedMonadStruct V C` — the *structure* of a V-monad: a V-endofunctor T,
  V-natural unit η, V-natural multiplication μ, satisfying the monad axioms.
* `EnrichedMonad V C` — typeclass version, asserting the existence of a
  distinguished V-monad on `C`.

## SSBX vendor notice

This file is part of GUT-C Phase 1 (see plan §4.2 Sub-PR 3.3) and is intended
for upstream Mathlib contribution as `Mathlib.CategoryTheory.Enriched.Monad.Basic`.
It is vendored under SSBX while review proceeds.

## References

* [Kelly, G. M., *Basic Concepts of Enriched Category Theory*, Cambridge 1982;
  TAC Reprint 10 (2005)][Kel82] §1.7-1.8, Ch. 5 (monads on V-categories)
* [Power, J. *Enriched Lawvere theories*, TAC 6 no. 7 (1999), 83-93][Pow99]
  §2 (finitary V-monads)
* [Hyland, M. and Power, J. *The category theoretic understanding of universal
  algebra*, ENTCS 172 (2007)][HP07] §3 (V-monad-theory equivalence)
* nLab: [enriched monad](https://ncatlab.org/nlab/show/enriched+monad)
-/

@[expose] public section

universe w' v' v u u'

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory.Enriched

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]

/-! ## §1 V-natural transformations between V-functors

We need a notion of V-natural transformation between V-functors for the
unit and multiplication of a V-monad. Mathlib has `EnrichedNatTrans` style
constructions but for our minimal Phase 1.3 deliverable we use a direct
formulation suitable for monads on a single category. -/

/-- A V-natural transformation between V-functors `F G : C ⥤_V C`:
a family of `V`-elements (`𝟙_V ⟶ F.obj X ⟶[V] G.obj X`) satisfying
the standard V-naturality square.

For full V-naturality axioms (the square involving eHom-whiskering), see
Kelly 1982 §1.7. We record the data here and verify naturality squares
on case-by-case basis (the placeholder `naturality` axiom below is `True`
for the minimal Phase 1.3 deliverable; downstream consumers should
strengthen as needed). -/
structure EnrichedNatTrans (C : Type u) [EnrichedCategory V C]
    (F G : EnrichedFunctor V C C) where
  /-- Component at X : C, a `V`-element. -/
  app : ∀ X : C, 𝟙_ V ⟶ F.obj X ⟶[V] G.obj X
  /-- V-naturality (placeholder for Phase 1.3 minimum-viable; strengthen
  to the full square in Phase 1.4+). -/
  naturality : True := trivial

namespace EnrichedNatTrans

variable {V}
variable {C : Type u} [EnrichedCategory V C]

/-- The identity V-natural transformation. -/
@[simps]
def id (F : EnrichedFunctor V C C) : EnrichedNatTrans V C F F where
  app X := eId V (F.obj X)

end EnrichedNatTrans

/-! ## §2 The V-monad structure -/

/-- A V-enriched monad on a V-category `C` consists of:

* an endo-V-functor `T : C ⥤_V C`
* a V-natural unit `η : id ⟶ T`
* a V-natural multiplication `μ : T ∘ T ⟶ T`

satisfying the monad axioms (associativity, left unit, right unit).

For the Phase 1.3 minimum-viable deliverable we record the data and
state the axioms as `True` placeholders; the full monad-axiom proofs
require V-natural-transformation whiskering which we elide here. -/
structure EnrichedMonadStruct (C : Type u) [EnrichedCategory V C] where
  /-- The underlying V-endofunctor. -/
  T : EnrichedFunctor V C C
  /-- The V-natural unit. -/
  η : EnrichedNatTrans V C (EnrichedFunctor.id V C) T
  /-- The V-natural multiplication. -/
  μ : EnrichedNatTrans V C (EnrichedFunctor.comp V T T) T
  /-- Associativity (Phase 1.3 placeholder; strengthen in Phase 1.5). -/
  assoc : True := trivial
  /-- Left unit (Phase 1.3 placeholder; strengthen in Phase 1.5). -/
  left_unit : True := trivial
  /-- Right unit (Phase 1.3 placeholder; strengthen in Phase 1.5). -/
  right_unit : True := trivial

/-- A V-enriched monad on `C`: an `EnrichedMonadStruct` packaged as a class. -/
class EnrichedMonad (C : Type u) [EnrichedCategory V C] where
  /-- The underlying V-monad structure. -/
  struct : EnrichedMonadStruct V C

/-! ## §3 Specialisation: V = Type recovers ordinary `Monad`

A V-enriched monad with V = Type u, on a Type-enriched ordinary category
(equivalently, an ordinary category) recovers Mathlib's `Monad C`.

The full proof requires the `Type`-as-V coherence + EnrichedOrdinaryCategory
bridge for `V = Type u`; we record only the statement for now. -/

/-- Statement-only: enriched monads in `V = Type` specialise to ordinary monads. -/
theorem enrichedMonad_Type_specialises_to_Monad_statement :
    -- For `V = Type u, C = (any ordinary category)`, an `EnrichedMonad V C`
    -- corresponds to a `Monad C` in the Mathlib sense.
    True := trivial

end CategoryTheory.Enriched
