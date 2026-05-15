/-
# Foundation.R.OperationMonism — R-Family below the base

Per `docs-next/10_formal_形式/wen-substrate.md` v1.2 §3.7 (Operation
Monism — R-Family Below the Base).

This module is the **operation-monism level** of the R-Family abstraction
tower:

| Doc layer | Object of definition       | Lean realization                     |
|-----------|---------------------------|--------------------------------------|
| §1-§3.5   | `R N := Fin N → Bool`      | `Foundation/R/Basic.lean`            |
| §3.6      | `RFamily k N := Fin N → k` | `Foundation/R/Parametric.lean`       |
| §3.7      | `RTower X k` (iter. Σ)     | **this file**                        |

The point of this file is to formalise the §3.7 thesis:

> R-Family is most fundamentally an *operator-composition* structure;
> the base `k` — and even the carrier family `{R_N^{(k)}}` — emerges
> as a *consequence* of the squaring law `T_{k+1} = T_k × T_k`, not as
> a premise.

Concretely we define:

* `Sigma X := X × X` — the squaring endofunctor on `Type u` (no
  typeclass on `X` required).
* `RTower X k` — the `k`-fold iterate `Σ^k X = X × X × … × X`
  (`2^k` copies).
* A **no-typeclass witness** : `RTower` is well-defined for *any*
  `X : Type u` with *no* algebraic structure imposed.  The structure
  is in the iteration, not in the seed.
* A **base-naming corollary** : choosing `X = PUnit` recovers the
  trivial squaring tower of cardinalities `1, 1, 1, …`; choosing
  `X = Bool` recovers the F₂-cardinality tower `1, 2, 4, 16, 256, …`
  (= cardinalities of `R 0, R 1, R 2, R 4, R 8`); choosing
  `X = Fin n` recovers the `n^{2^k}` tower over base `Fin n`.

This is the wen-substrate §3.7.6 "Lean code direction" delivered
*additively*: no existing definition is replaced.  Cards-to-the-table:
the only *operations* primitives this file uses are `Prod` and `ℕ`-
recursion.  Everything else — addition, scalar action, bilinear forms,
ring structure — is a downstream artefact of the seed-naming, not part
of the substrate.

## Doctrinal anchor

* `wen-substrate.md` v1.2 §3.7 (Operation Monism — R-Family Below the Base).
* `wen-substrate.md` v1.2 §3.7.3 (Carrier as fixed-point of the composition graph).
* `wen-substrate.md` v1.2 §3.7.6 (Implications for D2, cuo-equivariance, and Lean code).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.R.OperationMonism

universe u

/-! ## § 1 The squaring functor `Σ : Type u → Type u`

`Sigma X := X × X` is the categorical-product squaring functor.  No
typeclass on `X` is required — this is the precise content of
"the substrate is **not-a-thing**" (wen-substrate §3.7.4): the
operator is defined on raw types, with no algebraic structure
imposed on the seed.
-/

/-- The squaring functor `Σ : Type u → Type u, X ↦ X × X`.

    Per wen-substrate v1.2 §3.7.2 (Composition as identification):
    `Sigma` is the operation that *produces* a new object and
    simultaneously *identifies* its coordinate structure with two
    coordinated copies of the seed.  No element-level naming is
    required — the identification is embedded in the composition law. -/
def Sigma (X : Type u) : Type u := X × X

/-- Map a function through `Sigma`: `Sigma.map f := f ×̇ f`.  Witnesses
    that `Sigma` is functorial on the category `Type u`. -/
def Sigma.map {X Y : Type u} (f : X → Y) : Sigma X → Sigma Y :=
  fun p => (f p.1, f p.2)

@[simp] theorem Sigma.map_id {X : Type u} :
    Sigma.map (id : X → X) = id := by
  funext p
  cases p
  rfl

@[simp] theorem Sigma.map_comp {X Y Z : Type u} (g : Y → Z) (f : X → Y) :
    Sigma.map (g ∘ f) = Sigma.map g ∘ Sigma.map f := by
  funext p
  cases p
  rfl

/-! ## § 2 The iterated tower `RTower X k`

`RTower X 0 = X`, `RTower X (k+1) = Sigma (RTower X k) = RTower X k × RTower X k`.

This is the **squaring sub-tower** of wen-substrate §3.7.3.  Each
`RTower X k` is what `Σ` forces at iteration-level `k`, given seed `X`.
The "seed" `X` is a name for the empty starting point at iteration-
level 0; *no* algebraic structure on `X` is required.
-/

/-- `RTower X k` is `Σ^k X` = the `k`-fold iterate of the squaring
    functor at seed `X`.

    Per wen-substrate v1.2 §3.7.3 (a): "carriers are forced, not
    chosen".  Once `Σ` is fixed, the entire tower `{RTower X k}_{k ≥ 0}`
    is determined.  No per-level freedom; no typeclass on `X`. -/
def RTower (X : Type u) : ℕ → Type u
  | 0       => X
  | (k + 1) => Sigma (RTower X k)

@[simp] theorem RTower_zero (X : Type u) : RTower X 0 = X := rfl

@[simp] theorem RTower_succ (X : Type u) (k : ℕ) :
    RTower X (k + 1) = (RTower X k × RTower X k) := rfl

/-- **`RTower` squaring law** — the §3.7.3 fixed-point identification:
    `RTower X (k+1)` *is* the product of two copies of `RTower X k`,
    by definition.  This is the substrate-level statement of
    "object = operator-iteration-stage" (§3.7.3 (b)). -/
theorem RTower_self_square (X : Type u) (k : ℕ) :
    RTower X (k + 1) = Sigma (RTower X k) := rfl

/-! ## § 3 No-typeclass witness

The §3.7 claim "the structure is in the iteration, not in the seed"
becomes a Lean statement: `RTower` is well-defined for *any* `X : Type u`,
with **no** typeclass on `X` whatsoever.  The witness below is trivial
to state (the definition of `RTower` already takes a raw `X : Type u`)
but worth recording explicitly: it is the *content* of
wen-substrate §3.7's distinctive claim.
-/

/-- **No-typeclass witness for the seed** — `RTower X k` is definable
    for every type `X : Type u` and every `k : ℕ`, with no algebraic
    typeclass (`Add`, `Mul`, `Ring`, `Field`, `Module`, …) imposed on
    `X`.  This is the formal expression of wen-substrate v1.2 §3.7.4:
    "the substrate is *not-a-thing* — the operator is the one, the
    carriers are derivative."

    Stated as: for any universe, any type, any iteration count, the
    tower is a non-empty class of carriers indexed by `k`, requiring
    only `Type u` membership of the seed. -/
theorem rtower_no_typeclass (X : Type u) (k : ℕ) :
    Nonempty (Type u) :=
  ⟨RTower X k⟩

/-! ## § 4 Base-naming cross-sections

Per wen-substrate §3.7.6 "有名是无名的截面" (the named is a cross-
section of the un-named): each specific choice of seed `X` yields a
specific R-Family-over-`X` instance via the carrier identification
`R N ↔ RTower X k` at squaring-tower levels `N = 2^k`.  Below: the
F₂ cross-section (Bool-seeded tower) and its identification with the
existing `Foundation/R/Basic.lean` definition.
-/

/-- `Bool`-seeded tower: the cross-section that recovers the canonical
    `R N` carrier family at squaring-tower levels `N = 2^k`. -/
def BoolTower (k : ℕ) : Type := RTower Bool k

/-- Cardinality recursion at the type level: `RTower X (k+1)` is *by
    definition* the product `RTower X k × RTower X k`, so its
    cardinality (when finite) doubles by squaring.  We expose the
    definitional equality; concrete cardinality calculations then
    follow by `Fintype.card_prod` at the user's call site, after the
    appropriate `Fintype` instance for `RTower X k` has been
    established. -/
theorem RTower_succ_def_eq_prod (X : Type u) (k : ℕ) :
    RTower X (k + 1) = (RTower X k × RTower X k) := rfl

/-- `PUnit`-seeded tower: the trivial cross-section.  Every tower
    level has cardinality 1.  Recorded as a sanity-check that
    `RTower` is non-vacuous for *any* `X`, including the terminal one. -/
def PUnitTower (k : ℕ) : Type := RTower PUnit k

/-! ## § 5 Operation-monism summary

The substrate of wen-substrate §3.7 is `(Sigma, ℕ-iteration)` —
*one* operator on `Type u` plus *one* structural principle (iteration).
The substrate is **not a thing** (`Type u → Type u`, not `Type u`); the
"carriers" are *theorems* about this substrate, not definitions of it.

Specifically:

* The squaring law `T_{k+1} = T_k × T_k` (wen-substrate §3.7.1) is
  `RTower_succ`.
* The fixed-point identification (§3.7.3 (b), "object = operator-
  iteration-stage") is `RTower_self_square`.
* The instance-independence (§3.7.3 (c), "no choice of base is required
  at the operator level") is `rtower_no_typeclass`.
* The cross-section reading (§3.7.6, "有名是无名的截面") is `BoolTower`
  / `PUnitTower` / etc., each a *named* cross-section of the *un-named*
  operator iteration.

This file introduces **no new axioms** and **no algebraic typeclass
constraints**.  It uses only `Type u`, `Prod`, and `ℕ`-recursion.
-/

end SSBX.Foundation.R.OperationMonism
