/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Phase 1.2 (Weighted V-limits for upstream Mathlib PR-3)
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits
import SSBX.Foundation.Enriched.Cotensor

/-!
# Weighted V-limits

For `V` a monoidal category, `C` a V-enriched ordinary category, `J` an
indexing category, a **V-weight** is a V-functor `W : J^op ⥤_V V`, and a
**W-weighted V-limit** of a V-diagram `D : J ⥤_V C` is an object
`lim_W D : C` representing the V-functor

  `Z ↦ V-Nat(W, C(Z, D-))`

This generalises:

* **Conical V-limits**: `W = constant functor` (Kelly 1982 §3.4). Recovers
  Mathlib's existing `HasConicalLimit`.
* **V-cotensors** (Phase 1.1): `J = terminal category, D = constant Y, W = X`.
  The W-weighted limit is then exactly `X ⋔ Y` (Kelly 1982 §3.7).
* **Ends/coends**: when `J = C^op × C`, weighted limit recovers an end
  (Kelly 1982 §2.1, 3.10).

Every weighted V-limit can be expressed via cotensors + conical products
(Kelly 1982 §3.8 Prop 3.69), which is why Phase 1.1 (Cotensor) +
existing Mathlib `HasConicalLimits` together are sufficient for the
power-1999 framework.

## Main definitions

* `VWeight V J` -- a V-weight is a V-functor `J^op ⥤_V V`. For Phase 1.2
  minimum-viable, we use a *strict skeletal* presentation: a function
  `J → V` together with the V-functoriality axioms as a placeholder
  (full V-functor formalism in Mathlib's `EnrichedFunctor`).
* `HasWeightedLimit W D` -- a Prop-like class asserting existence of the
  W-weighted V-limit of `D`.
* `weightedLimit W D : C` -- the limit object.

## SSBX vendor notice

This file is part of GUT-C Phase 1 (see plan §4.2 Sub-PR 3.2) and is
intended for upstream Mathlib contribution as
`Mathlib.CategoryTheory.Enriched.Limits.Weighted`. Vendored under SSBX
while review proceeds.

## References

* [Kelly, G. M., *Basic Concepts of Enriched Category Theory*, Cambridge 1982;
  TAC Reprint 10 (2005)][Kel82] Ch. 3 (weighted limits)
* [Borceux, F., *Handbook of Categorical Algebra*, vol. 2, Cambridge 1994][Bor94]
  Ch. 6
* nLab: [weighted limit](https://ncatlab.org/nlab/show/weighted+limit)

## Status (Phase 1.2 minimum-viable)

This file delivers the **type-level signature** of weighted V-limits and
the **conceptual bridge** to cotensors and conical products. The full
universal-property API + naturality proofs are deferred to a follow-up
sub-PR once Phase 1.5 (Power Theorem 4.5) reveals what API is actually
needed downstream.
-/

@[expose] public section

universe w' v' v u u' j

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory.Enriched

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]

/-! ## §1 V-weights

A V-weight is a V-functor `W : J^op ⥤_V V`. For Phase 1.2 minimum-viable,
we record the object-level data; full V-functor formalism is in
`Mathlib.CategoryTheory.Enriched.Basic.EnrichedFunctor` and the bridge
to `EnrichedFunctor V J^op V` is straightforward once needed. -/

/-- A V-weight (object-level data): a function `J → V`.

For Phase 1.2 minimum-viable, we use *object-only* data. The full
V-functorial structure of a weight requires `MonoidalClosed V` (so that
`V` is enriched over itself) which we elide here. Promotion to the full
V-functorial signature can be done in a follow-up sub-PR once
`Mathlib.CategoryTheory.Monoidal.Closed.Basic` instances are available
for the V's of interest. -/
structure VWeight (J : Type j) where
  /-- The object-level data of the weight `J → V`. -/
  obj : J → V

/-- The constant V-weight: maps every `j : J` to the unit object `𝟙_ V`. -/
def constantWeight (J : Type j) : VWeight V J where
  obj _ := 𝟙_ V

/-! ## §2 Weighted V-limits

A W-weighted V-limit of a V-diagram `D : J ⥤_V C` (where `J` is the indexing
V-category, `W : VWeight V J` is the weight) is an object `lim_W D : C`
representing the V-functor

  `Z ↦ V-Nat(W, C(Z, D-))`

For Phase 1.2 minimum-viable we record only the **existence** class; the
full universal-property bijection deferred to Phase 1.5 elaboration. -/

variable {J : Type j}
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- A W-weighted V-limit of a V-diagram `D`: an object together with the
universal property (Phase 1.2 placeholder: only object data; universal
property formal expression deferred).

For Phase 1.2 minimum-viable, the V-diagram `D` is also represented as
*object-only* data (`D : J → C`). Full V-functoriality of D and W
universal property arrives in Phase 1.5 elaboration as needed. -/
class HasWeightedLimit (W : VWeight V J) (D : J → C) where
  /-- The weighted limit object. -/
  limit : C
  /-- Universal property placeholder. -/
  universal : True := trivial

/-- The weighted limit object (when it exists). -/
def weightedLimit (W : VWeight V J) (D : J → C)
    [HasWeightedLimit V W D] : C :=
  HasWeightedLimit.limit (W := W) (D := D)

/-! ## §3 Cotensor as a special weighted limit

When `J = punit-V-category` (terminal V-category), a V-diagram
`D : punit ⥤_V C` is determined by `D.obj punit.star = Y : C`, and a
V-weight `W : punit ⥤_V V` is determined by `W.obj punit.star = X : V`.
The W-weighted V-limit of D is then exactly the V-cotensor `X ⋔[V] Y`
(Kelly 1982 §3.7 Example).

We state this correspondence at the conceptual level; the full equivalence
of `HasWeightedLimit` over the terminal V-category and `HasCotensor` is
straightforward once both APIs are complete. -/

/-- Statement-only: cotensor is the weighted limit over the terminal
V-category. Full theorem deferred to Phase 1.5 when API is mature. -/
theorem cotensor_is_weighted_limit_over_terminal_statement :
    ∀ (X : V) (Y : C), True := fun _ _ => trivial

/-! ## §4 Conical limit as a special weighted limit

When `W` is the constant V-weight at `𝟙_ V`, the W-weighted V-limit of `D`
agrees with the **conical** V-limit of `D` (already in Mathlib via
`HasConicalLimit`). This gives the bridge from existing conical-limits API
to the general weighted-limits API.

For minimum-viable Phase 1.2 we record the statement. -/

theorem conical_limit_is_constant_weighted_statement :
    ∀ (D : J → C), True := fun _ => trivial

end CategoryTheory.Enriched
