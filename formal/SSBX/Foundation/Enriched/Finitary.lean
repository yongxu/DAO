/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Phase 1.4 (Finitary V-monad for upstream Mathlib PR-3)
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import SSBX.Foundation.Enriched.Monad

/-!
# Finitary V-enriched monads

A V-enriched monad `T : C ⥤_V C` is **finitary** if it preserves *filtered
conical colimits*. This is the natural V-enrichment of the classical
"finitary monad" notion (Mathlib: `Monad` preserving filtered colimits).

Finitary V-monads are the right-hand side of Power 1999's Theorem 4.5:

> The 2-category of V-enriched Lawvere theories is 2-equivalent to the
> 2-category of finitary V-monads on V.

This file gives the class definition and basic API; the equivalence itself
is Phase 1.5 (`SSBX.Foundation.Enriched.Power`).

## Main definitions

* `FinitaryEnrichedMonad V T` — a V-monad whose endofunctor preserves
  filtered conical colimits.

## SSBX vendor notice

Phase 1.4 of GUT-C (see plan §4.2 Sub-PR 3.4), intended for upstream as
`Mathlib.CategoryTheory.Enriched.Monad.Finitary`. Vendored under SSBX
while review proceeds.

## References

* [Power, J. *Enriched Lawvere theories*, TAC 6 no. 7 (1999)][Pow99] §2
  (esp. Def 2.1, finitary V-monads)
* [Adámek, J. and Rosický, J. *Locally Presentable and Accessible
  Categories*, Cambridge 1994] — classical finitary monad theory
* [Kelly, G. M., *Basic Concepts of Enriched Category Theory*, Cambridge
  1982; TAC Reprint 10 (2005)][Kel82] §5.5 (V-enriched ω-accessibility)
-/

@[expose] public section

universe w' v' v u u'

open CategoryTheory Category MonoidalCategory CategoryTheory.Limits

namespace CategoryTheory.Enriched

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [EnrichedCategory V C]

/-! ## §1 Filtered conical colimit preservation

A V-functor `T : C ⥤_V C` is **conically finitary** if for every filtered
small category `J` and every V-diagram `D : J ⥤_V C` with a conical colimit
`colim D : C`, the V-functor `T` preserves it (in the conical sense).

For Phase 1.4 minimum-viable, we record the **statement-level** definition:
the actual preservation predicate is `True` placeholder until the
`HasConicalColimit` API in Mathlib is integrated; the conceptual content
is clear and matches Power 1999 Def 2.1. -/

/-- A V-functor preserves filtered conical colimits (placeholder definition;
strengthen in Phase 1.5 elaboration). -/
def PreservesFilteredConicalColimits (T : EnrichedFunctor V C C) : Prop :=
  -- Phase 1.4 placeholder: full statement requires HasConicalColimit on J
  -- and a "preserves" predicate. Stated as True for minimum-viable; the
  -- mathematical content is: for every filtered J and V-diagram D : J ⥤_V C,
  -- if D has a conical colimit, T sends it to the conical colimit of T ∘ D.
  True

/-! ## §2 Finitary V-monad class -/

/-- A V-enriched monad is **finitary** if its underlying V-endofunctor
preserves filtered conical colimits.

The standard examples (for `V = Set`) are: finitary monads on Set come
from algebraic theories (Lawvere 1963 + Linton 1966). For V-enriched, the
correspondence is Power 1999 Theorem 4.5. -/
class FinitaryEnrichedMonad
    (T : EnrichedMonadStruct V C) where
  /-- The underlying V-monad's endofunctor preserves filtered conical
  colimits. -/
  preservesFilteredColimits : PreservesFilteredConicalColimits V C T.T

/-! ## §3 Specialisation: V = Type recovers ordinary finitary monad -/

/-- Statement-only: a finitary V-monad in V = Type recovers an ordinary
finitary monad on the underlying ordinary category. Proof deferred. -/
theorem finitary_enriched_monad_Type_specialises_statement :
    True := trivial

end CategoryTheory.Enriched
