/-
# Foundation.R.ClaimZ.Analytic.P2 — D1 ⟹ P2 (composition / direct sum / biproduct)

**GUT roadmap Phase 1 Stream A2** (per `docs-next/10_formal_形式/gut-roadmap.md`):

This file discharges the **analytic step** `D1 ⟹ P2` for the F₂-Boolean
realisation of the R-Family.  Per
`docs-next/10_formal_形式/wen-substrate/01-foundations.md`:

> **P2** says any D1-articulation has a **direct-sum / biproduct**
> structure — for any two sub-articulations of sizes `N` and `M`,
> their composition has a canonical structure equivalent to
> `R N × R M ≃ R (N + M)`.

For the canonical δ = Bool / F₂ instance, this becomes the concrete
isomorphism on underlying sets

    R N × R M  ≃  R (N + M)              (analytic P2_F2)

which is the F₂-vector-space biproduct (direct-sum = product = coproduct
in the F₂-Vec category, as in every additive category).

The bijection follows from the basic `Fin`-arithmetic chain:

```
R N × R M  =  (Fin N → Bool) × (Fin M → Bool)
           ≃  Fin N ⊕ Fin M → Bool        -- sumArrowEquivProdArrow.symm
           ≃  Fin (N + M) → Bool          -- arrowCongr finSumFinEquiv refl
           =  R (N + M)
```

Each step is a generic Mathlib `Equiv`; the composition is the analytic-
step bijection witnessing P2 at the F₂-Boolean level.

## Categorical biproduct remark

In the F₂-vector-space category (= `Mod F₂` = the category of abelian
2-groups with `F₂`-linear maps), the **biproduct** of two objects `R N`
and `R M` is the object that simultaneously satisfies the universal
property of the product (with projections π_N, π_M) and of the coproduct
(with injections ι_N, ι_M).  In any **additive category**, the biproduct
exists and coincides with both the product and the coproduct; F₂-Vec is
the prototypical additive category in characteristic 2.

The R-Family's P2 closure is precisely the *substrate-level exhibition*
of this universal property: the carrier `R (N + M)` is the biproduct of
`R N` and `R M`, with the bijection `R N × R M ≃ R (N + M)` being the
underlying-set component of the biproduct iso.  Specifically:

* **Product side**: projections `π_N : R (N + M) → R N` and
  `π_M : R (N + M) → R M` are the two components of `e.symm`.
* **Coproduct side**: injections `ι_N : R N → R (N + M)` and
  `ι_M : R M → R (N + M)` send `v ↦ e (v, 0)` and `w ↦ e (0, w)`.
* **Biproduct identities** `π_N ∘ ι_N = id`, `π_M ∘ ι_M = id`,
  `π_M ∘ ι_N = 0`, `π_N ∘ ι_M = 0`, and `ι_N ∘ π_N + ι_M ∘ π_M = id`
  all follow from the bijection together with the `Bool.xor`
  characteristic-2 group structure on `R k`.

So P2 = "the substrate has a direct-sum / biproduct structure" is
*tautologically discharged* by exhibiting this bijection: the
biproduct's universal property is satisfied because `R (N + M)` *is*
(up to canonical equivalence) the product/coproduct of `R N` and `R M`
in F₂-Vec.

## What this file delivers

* `R_prod_equiv_R_add : R N × R M ≃ R (N + M)` — the underlying-set
  bijection witnessing P2 at the F₂-Boolean level.
* `D1_implies_P2_F2 : (N M : ℕ) → R N × R M ≃ R (N + M)` —
  the named analytic-step theorem (alias of `R_prod_equiv_R_add`).
* `D1_implies_P2_F2_prop : (N M : ℕ) → Nonempty (R N × R M ≃ R (N + M))` —
  the propositional shadow, suitable for `PClosure.p2` contexts where
  the type-level `Equiv` is awkward.

## Strength of the statement

The theorem statement is a **bijection on the underlying sets** of
`R N × R M` and `R (N + M)`.  This is the strongest *purely analytic*
form (any stronger form involves the additional `AddCommGroup` /
`F₂-linear` structure, which is the content of the categorical-
biproduct remark above and lifts in a straightforward but not-needed-
for-the-bijection way through `Pi.addCommGroup`).

The bijection is moreover **structure-preserving** in the sense that:

* `(0, 0) ↦ 0` — the zero of the product maps to the zero of the sum.

This is recorded as a separate lemma so downstream analytic proofs can
use the equivalence transparently.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` (Phase 1 Stream A2).
* `docs-next/10_formal_形式/wen-substrate/01-foundations.md` (P2
  statement: composition / direct sum / biproduct).
* `wen-substrate.md` v1.2 §1.5.1 (D1 — D1.2 comp item), §2.2 (P2
  closure condition), §7.8.3 (D1.2 ⟹ P2 analytic mapping).
* `wen-algebra.md` v0.6 §1.2 (R-Family direct sum: `R N ⊕ R M = R (N+M)`).
* `Foundation/R/Basic.lean` — the `R N` carrier definition.
* `Foundation/R/ClaimZ.lean` — the `D1Articulation` / `PClosure`
  interface bundles.
-/

import SSBX.Foundation.R.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

namespace SSBX.Foundation.R.ClaimZ.Analytic

open SSBX.Foundation.R

/-! ## § 1 The P2-F₂ equivalence: `R N × R M ≃ R (N + M)`

The chain (sum-index bit-encoding):

```
R N × R M  =  (Fin N → Bool) × (Fin M → Bool)
           ≃  Fin N ⊕ Fin M → Bool        -- (sumArrowEquivProdArrow).symm
           ≃  Fin (N + M) → Bool          -- arrowCongr finSumFinEquiv.symm
           =  R (N + M)
```

Each step is a generic Mathlib `Equiv`; the composition is the analytic-
step bijection witnessing P2 at the F₂-Boolean level.
-/

/-- The P2-F₂ analytic bijection: pairs `(v, w) : R N × R M` are
    bijectively classified by an `R (N + M)` element via concatenation:
    the first `N` coordinates record `v`, the last `M` coordinates
    record `w`.

    Concretely: `(v, w) : R N × R M` encodes to the `R (N + M)` vector
    whose coordinate at `finSumFinEquiv (inl i) = Fin.castAdd M i` is
    `v i`, and whose coordinate at `finSumFinEquiv (inr j) =
    Fin.natAdd N j` is `w j`.  The inverse decodes by splitting the
    index at the boundary.

    This is the **strongest purely analytic form** of P2 at the
    F₂-Boolean level.  See the module docstring's *categorical
    biproduct remark* for why this bijection is precisely the universal
    property of `R (N + M)` as the biproduct of `R N` and `R M` in
    F₂-Vec. -/
def R_prod_equiv_R_add (N M : ℕ) : R N × R M ≃ R (N + M) :=
  -- Step 1: combine the pair into a sum-indexed function
  --   (Fin N → Bool) × (Fin M → Bool)  ≃  Fin N ⊕ Fin M → Bool
  (Equiv.sumArrowEquivProdArrow (Fin N) (Fin M) Bool).symm.trans <|
  -- Step 2: pack the sum index into a single Fin index
  --   Fin N ⊕ Fin M → Bool  ≃  Fin (N + M) → Bool
  -- `arrowCongr e e'` needs `e : Fin N ⊕ Fin M ≃ Fin (N+M)` on the
  -- *domain* side; we want to rewrite the domain via the inverse of
  -- `finSumFinEquiv`, so we pass `finSumFinEquiv.symm.symm = finSumFinEquiv`.
  -- Equivalently: think of `arrowCongr e _` as "if `α ≃ β` then `α → γ`
  -- has the same elements as `β → γ`"; here α = Fin N ⊕ Fin M and
  -- β = Fin (N+M), so e = finSumFinEquiv.
  Equiv.arrowCongr finSumFinEquiv (Equiv.refl Bool)

/-! ## § 2 Sanity / unfolding

`R_prod_equiv_R_add` is a composition of Mathlib `Equiv`s.  Its
forward map computes (per `Equiv.arrowCongr` and
`Equiv.sumArrowEquivProdArrow` definitions):

    R_prod_equiv_R_add N M (v, w) k
      = (Sum.elim v w) (finSumFinEquiv.symm k)

The two simp lemmas below give the value at the canonical
`Fin.castAdd` / `Fin.natAdd` summand-indices.
-/

/-- Generic apply: at any `k : Fin (N + M)`, the encoded vector reads
    `Sum.elim v w` at the index obtained by splitting `k` via
    `finSumFinEquiv.symm`. -/
theorem R_prod_equiv_R_add_apply (N M : ℕ)
    (v : R N) (w : R M) (k : Fin (N + M)) :
    R_prod_equiv_R_add N M (v, w) k =
      Sum.elim v w (finSumFinEquiv.symm k) := rfl

/-- Reading the encoded vector at a `Fin.castAdd M i` index returns
    the `i`-th coordinate of the first component. -/
theorem R_prod_equiv_R_add_apply_castAdd (N M : ℕ)
    (v : R N) (w : R M) (i : Fin N) :
    R_prod_equiv_R_add N M (v, w) (Fin.castAdd M i) = v i := by
  rw [R_prod_equiv_R_add_apply, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- Reading the encoded vector at a `Fin.natAdd N j` index returns
    the `j`-th coordinate of the second component. -/
theorem R_prod_equiv_R_add_apply_natAdd (N M : ℕ)
    (v : R N) (w : R M) (j : Fin M) :
    R_prod_equiv_R_add N M (v, w) (Fin.natAdd N j) = w j := by
  rw [R_prod_equiv_R_add_apply, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-! ## § 3 Structure-preservation bridge

The bijection sends the pair of zeros to the zero content vector. -/

/-- Zero ↦ zero: `(0, 0) : R N × R M` encodes to `0 : R (N + M)`.
    This is one of the *biproduct identities* — the additive identity
    of the product matches the additive identity of the sum, witnessing
    the F₂-Vec biproduct universal property at the unit. -/
theorem R_prod_equiv_R_add_zero (N M : ℕ) :
    R_prod_equiv_R_add N M ((0 : R N), (0 : R M)) = (0 : R (N + M)) := by
  funext k
  -- Reduce to `Sum.elim 0 0 (finSumFinEquiv.symm k) = false`; case on
  -- the sum-component result.
  rw [R_prod_equiv_R_add_apply]
  cases h : finSumFinEquiv.symm k with
  | inl i => simp
  | inr j => simp

/-! ## § 4 Cardinality shadow

The cardinality identity `|R N × R M| = |R (N + M)| = 2^(N + M)` is the
*counting* shadow of `R_prod_equiv_R_add`.  Below is a direct calculation
that does not require the bijection itself; it is recorded under the P2
name for legibility. -/

/-- |R N × R M| = |R (N + M)| = 2^(N + M).  The counting shadow of P2. -/
theorem T_P2_card (N M : ℕ) :
    Fintype.card (R N × R M) = Fintype.card (R (N + M)) := by
  rw [Fintype.card_prod, R.card_eq, R.card_eq, R.card_eq, pow_add]

/-! ## § 5 The packaged analytic theorem

`D1_implies_P2_F2` is the named analytic-step theorem for Phase 1
Stream A2.  Given any two layer indices `N M : ℕ`, the F₂-Boolean
realisation of the R-Family satisfies P2 (composition / direct-sum /
biproduct) in the concrete bijection form:

    R N × R M  ≃  R (N + M)

i.e., the product / coproduct / biproduct of two R-Family sub-carriers
is canonically the next-larger R-Family carrier.  This discharges the
D1.2 comp ⟹ P2 entailment of wen-substrate §7.8.3.

**No new axioms.**  The proof is a composition of two Mathlib `Equiv`s.
-/

/-- **D1 ⟹ P2 (F₂-Boolean analytic step, Phase 1 Stream A2)** —
    `R N × R M ≃ R (N + M)`.

    Per the module docstring's categorical-biproduct remark, this
    equivalence is the underlying-set component of the canonical
    F₂-Vec biproduct iso; P2 is just the R-Family substrate exhibiting
    that universal property concretely.

    This is the named theorem; the proof is `R_prod_equiv_R_add`.
    (Declared as `def` rather than `theorem` because `Equiv` is a
    `Type`-valued bundle, not a `Prop`.  The propositional shadow
    — `Nonempty (R N × R M ≃ R (N + M))` — is recorded immediately
    below as `D1_implies_P2_F2_prop`.) -/
def D1_implies_P2_F2 (N M : ℕ) : R N × R M ≃ R (N + M) :=
  R_prod_equiv_R_add N M

/-- The propositional shadow: `Nonempty (R N × R M ≃ R (N + M))`.
    Useful when downstream code wants a `Prop`-valued conjunct of
    `PClosure.p2` rather than the data-bearing `Equiv`. -/
theorem D1_implies_P2_F2_prop (N M : ℕ) :
    Nonempty (R N × R M ≃ R (N + M)) :=
  ⟨D1_implies_P2_F2 N M⟩

/-- The `N = M = 1` specialisation — the simplest non-trivial case:
    a pair of bits maps to a 2-bit vector.  `R 1 × R 1 ≃ R 2`. -/
def D1_implies_P2_F2_at_1_1 : R 1 × R 1 ≃ R 2 :=
  D1_implies_P2_F2 1 1

/-- The `N = 4, M = 4` specialisation — the byte-from-nibbles case:
    `R 4 × R 4 ≃ R 8`.  Used downstream for the R₈ = R₄ ⊕ R₄
    factorisation. -/
def D1_implies_P2_F2_at_4_4 : R 4 × R 4 ≃ R 8 :=
  D1_implies_P2_F2 4 4

/-! ## § 6 Phase 1 Stream A2 summary

A single bundled lemma recording that P2 is closed at every concrete
layer pairing relevant to the R-Family tower (`R 1 × R 1`, `R 4 × R 4`)
plus the universal `(N, M)` form, and that the interface-level analytic
step `D1.2 ⟹ P2` is fully realised. -/

/-- **Phase 1 Stream A2 summary witness** — the analytic step
    `D1 ⟹ P2` is fully closed at:

    * universal `(N, M)`: `R N × R M ≃ R (N + M)` via
      `D1_implies_P2_F2`
    * propositional shadow at universal `(N, M)`: via
      `D1_implies_P2_F2_prop`
    * the `R 1 × R 1 ≃ R 2` specialisation (smallest non-trivial)
    * the `R 4 × R 4 ≃ R 8` specialisation (byte-from-nibbles, the
      operationally salient case for the squaring tower at R₈)

    No `sorry`, no new axiom.  Per `gut-roadmap.md` Phase 1 Stream A2,
    this discharges the **D1 ⟹ P2 analytic obligation** for the
    F₂-Boolean scope.  The categorical-biproduct flavour of the
    statement is recorded in the module docstring. -/
theorem A2_summary_witness :
    -- Universal form (propositional shadow)
    (∀ (N M : ℕ), Nonempty (R N × R M ≃ R (N + M))) ∧
    -- N=M=1 specialisation (propositional shadow)
    (Nonempty (R 1 × R 1 ≃ R 2)) ∧
    -- N=M=4 specialisation (propositional shadow)
    (Nonempty (R 4 × R 4 ≃ R 8)) ∧
    -- Cardinality shadow
    (∀ (N M : ℕ), Fintype.card (R N × R M) = Fintype.card (R (N + M))) :=
  ⟨D1_implies_P2_F2_prop,
   ⟨D1_implies_P2_F2_at_1_1⟩,
   ⟨D1_implies_P2_F2_at_4_4⟩,
   T_P2_card⟩

end SSBX.Foundation.R.ClaimZ.Analytic
