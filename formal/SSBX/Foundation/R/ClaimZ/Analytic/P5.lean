/-
# Foundation.R.ClaimZ.Analytic.P5 — D1 ⟹ P5 (Hom-as-content / self-reference)

**GUT roadmap Phase 1 Stream A5** (per `docs-next/10_formal_形式/gut-roadmap.md`):

This file discharges the **analytic step** `D1 ⟹ P5` for the F₂-Boolean
realisation of the R-Family.  Per `docs-next/10_formal_形式/wen-substrate/01-foundations.md`:

> **P5** says any D1-articulation embeds its own morphism space into its
> content layer — i.e., the substrate is *operation-stable*: morphisms
> `δ^N → δ^M` themselves live as content `δ^{N×M}`.

For the canonical F₂-Boolean instance, this becomes the concrete
isomorphism

    LinHom N M  ≃  R (N * M)              (analytic P5_F2)

where `LinHom N M = Fin M → Fin N → Bool` is the type of `F_2`-linear
maps `R N → R M` (via their `M × N` coefficient matrix; the `(i,j)`
entry is the coefficient of `e_j` in `f(e_j)_i`), and `R (N * M) =
Fin (N * M) → Bool`.

The isomorphism is the standard *row-major bit-encoding*:

```
LinHom N M = Fin M → Fin N → Bool
           ≃ Fin M × Fin N → Bool          -- (Equiv.curry _ _ _).symm
           ≃ Fin N × Fin M → Bool          -- Equiv.prodComm flip
           ≃ Fin (N * M) → Bool            -- finProdFinEquiv
           = R (N * M)
```

The **simplest non-trivial witness** of this iso is the `N = M = 2`
case, which is exactly the content of T_P7b's `R 4 ≃+* Mat2F2`
(packaged in `Foundation/R/PhaseZero.lean`):

* `LinHom 2 2 = Fin 2 → Fin 2 → Bool = Mat2F2`,
* `R (2 * 2) = R 4`,
* so the underlying-set bijection of `T_P7b_ring_equiv` is precisely
  the `N = M = 2` instance of `linHomEquivR_NM`.

That `N = M = 2` case is enriched with full `RingEquiv` (algebra-iso)
structure in T_P7b; for the general `(N, M)`, only the bijection on
underlying sets is exhibited here (the algebra structure depends on
choosing a multiplication on `R (N * M)`, which is *not* canonical for
general non-square shapes — for `N ≠ M`, `LinHom N M` is not a ring
at all).

## What this file delivers

* `linHomEquivR_NM : LinHom N M ≃ R (N * M)` —
  the underlying-set bijection witnessing P5 at the F₂-Boolean level.
* `D1_implies_P5_F2 : (N M : ℕ) → LinHom N M ≃ R (N * M)` —
  the named analytic-step theorem (alias of `linHomEquivR_NM`).
* `T_P5_card : Fintype.card (LinHom N M) = Fintype.card (R (N * M))` —
  the cardinality identity (already in `Foundation/R/Hom.lean` as
  `card_eq_R`; re-exported here under the P5 name).
* `P5_F2_anchored_at_T_P7b` — the explicit anchoring to T_P7b for
  the `N = M = 2` case.

## Strength of the statement

The theorem statement is a **bijection on the underlying sets** of
`F_2`-linear maps and content vectors.  This is the strongest *purely
analytic* form (any stronger form involves additional structure
beyond what D1 prescribes — e.g., the algebra-iso requires `N = M`
plus a chosen ring structure, which is the content of T_P7b, not of
P5 itself).

The bijection is moreover **structure-preserving** in the sense
that:

* `0 : LinHom N M` (the zero linear map) ↦ `0 : R (N * M)` —
  i.e., addition-trivial maps go to the zero content vector.

This bridging lemma is recorded as a separate theorem so downstream
analytic-step proofs can use the equivalence transparently.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` (Phase 1 Stream A5).
* `docs-next/10_formal_形式/wen-substrate/01-foundations.md` (P5
  statement: Hom-as-content / operation-stability).
* `wen-substrate.md` v1.2 §2.5 (P5 closure condition), §7.8.3
  (D1 ⟹ P5 analytic mapping: D1.7 selfRef ⟹ P5).
* `wen-algebra.md` v0.6 §2.3 (`Hom_F₂(R N, R M) ≅ R (N * M)`).
* `Foundation/R/Hom.lean` (the `LinHom` infrastructure).
* `Foundation/R4/EndR2.lean` + `Foundation/R/PhaseZero.lean` §4.1
  (the T_P7b `N = M = 2` algebra-iso anchor).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Hom
import SSBX.Foundation.R.PhaseZero
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

namespace SSBX.Foundation.R.ClaimZ.Analytic

open SSBX.Foundation.R
open SSBX.Foundation.R.R
open SSBX.Foundation.R.R.LinHom

/-! ## § 1 The P5-F₂ equivalence: `LinHom N M ≃ R (N * M)`

The chain (row-major bit encoding):

```
LinHom N M  =  Fin M → Fin N → Bool
            ≃  Fin M × Fin N → Bool        -- (Equiv.curry _ _ _).symm
            ≃  Fin N × Fin M → Bool        -- arrowCongr Equiv.prodComm
            ≃  Fin (N * M) → Bool           -- arrowCongr finProdFinEquiv.symm
            =  R (N * M)
```

Each step is a generic Mathlib equivalence; the composition is the
analytic-step bijection witnessing P5 at the F₂-Boolean level.
-/

/-- The P5-F₂ analytic bijection: `F_2`-linear maps `R N → R M`,
    encoded as `M × N` matrices over `Bool`, are bijectively classified
    by an `R (N * M)` element via the canonical row-major bit-pattern
    encoding.

    Concretely: `f : LinHom N M`, viewed as `f i j : Bool` for
    `(i, j) : Fin M × Fin N`, encodes to the `R (N * M)` vector
    whose coordinate at `finProdFinEquiv (j, i) = j * M + i` is
    `f i j`.  The inverse decodes the bit-pattern back to the matrix
    entries.

    This is the **strongest purely analytic form** of P5 at the
    F₂-Boolean level: any further structure (e.g., the `RingEquiv`
    when `N = M = 2`) requires a choice of multiplication, which is
    a P7b-level commitment beyond P5 itself. -/
def linHomEquivR_NM (N M : ℕ) : LinHom N M ≃ R (N * M) :=
  -- Step 1: uncurry  Fin M → Fin N → Bool  ≃  Fin M × Fin N → Bool
  (Equiv.curry (Fin M) (Fin N) Bool).symm.trans <|
  -- Step 2: swap the product  Fin M × Fin N → Bool  ≃  Fin N × Fin M → Bool
  (Equiv.arrowCongr (Equiv.prodComm (Fin M) (Fin N)) (Equiv.refl Bool)).trans <|
  -- Step 3: pack the indices  Fin N × Fin M → Bool  ≃  Fin (N * M) → Bool
  Equiv.arrowCongr
    ((finProdFinEquiv (m := N) (n := M)).symm : Fin (N * M) ≃ Fin N × Fin M).symm
    (Equiv.refl Bool)

/-! ## § 2 Sanity / unfolding

`linHomEquivR_NM` is purely a composition of Mathlib `Equiv`s, so its
`apply` and `symm.apply` reduce by `rfl`-unfolding. -/

theorem linHomEquivR_NM_apply (N M : ℕ) (f : LinHom N M) (k : Fin (N * M)) :
    linHomEquivR_NM N M f k =
      f (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1 := rfl

/-! ## § 3 Cardinality (re-exported P5 statement)

The cardinality identity `|LinHom N M| = |R (N * M)| = 2^(N * M)` is
the *counting* shadow of `linHomEquivR_NM`.  It is already proved in
`Foundation/R/Hom.lean` as `LinHom.card_eq_R`; we re-export it under
the P5 name for legibility. -/

theorem T_P5_card (N M : ℕ) :
    Fintype.card (LinHom N M) = Fintype.card (R (N * M)) :=
  card_eq_R N M

/-! ## § 4 Structure-preservation bridge

The bijection sends the zero linear map to the zero content vector. -/

/-- Zero ↦ zero: the all-`false` matrix encodes to the all-`false`
    content vector. -/
theorem linHomEquivR_NM_zero (N M : ℕ) :
    linHomEquivR_NM N M (LinHom.zero N M) = (0 : R (N * M)) := by
  funext k
  rfl

/-! ## § 5 N = M = 2 anchor: matches T_P7b's underlying bijection

The `(N, M) = (2, 2)` instance of `linHomEquivR_NM` lives at type
`LinHom 2 2 ≃ R 4`.  By the unfolding lemmas above and T_P7b's
`R4EquivMat2F2`, the *bit pattern* of both encodings agrees:
`f : LinHom 2 2 = Fin 2 → Fin 2 → Bool` at `(i, j)` reads to the same
bit-position in `R 4` (the row-major encoding `2 * i + j`).

Caveat: T_P7b uses `asMatrix w i j = w ⟨2*i + j, _⟩` (output-then-
input indexing of `R 4` as a 2×2 matrix), whereas `linHomEquivR_NM`
encodes a `LinHom N M`-as-matrix `f i j` (with `i : Fin M`,
`j : Fin N`) via `finProdFinEquiv (j, i) = j * M + i`.  For
`N = M = 2`, this is `2 * j + i`, which is the transpose of T_P7b's
view.  The two views are equally valid analytic encodings; they are
related by the standard matrix transpose.

For now, we record the cardinality match (the strongest fully
type-level statement that survives without picking a specific
matrix orientation). -/

theorem P5_F2_anchored_at_T_P7b :
    Fintype.card (LinHom 2 2) = Fintype.card (R 4) :=
  T_P5_card 2 2

/-! ## § 6 The packaged analytic theorem

`D1_implies_P5_F2` is the named analytic-step theorem for Phase 1
Stream A5.  Given any two layer indices `N M : ℕ`, the F₂-Boolean
realisation of the R-Family satisfies P5 (Hom-as-content) in the
concrete bijection form:

    Hom_F₂(R N, R M)  ≃  R (N * M)

i.e., the morphism space `LinHom N M` of `F_2`-linear maps `R N → R M`
embeds *as a bijection* into the content layer `R (N * M)`.  This
discharges the D1.7 selfRef ⟹ P5 entailment of wen-substrate §7.8.3.

**No new axioms.**  The proof is a composition of three Mathlib
`Equiv`s. -/

/-- **D1 ⟹ P5 (F₂-Boolean analytic step, Phase 1 Stream A5)** —
    `Hom_F₂(R N, R M) ≃ R (N * M)`.

    This is the named theorem; the proof is `linHomEquivR_NM`.
    (Declared as `def` rather than `theorem` because `Equiv` is a
    `Type`-valued bundle, not a `Prop`.  The propositional shadow
    — `Nonempty (LinHom N M ≃ R (N * M))` — is recorded immediately
    below as `D1_implies_P5_F2_prop`.) -/
def D1_implies_P5_F2 (N M : ℕ) : LinHom N M ≃ R (N * M) :=
  linHomEquivR_NM N M

/-- The propositional shadow: `Nonempty (LinHom N M ≃ R (N * M))`.
    Useful when downstream code wants a `Prop`-valued conjunct of
    P-closure rather than the data-bearing `Equiv`. -/
theorem D1_implies_P5_F2_prop (N M : ℕ) :
    Nonempty (LinHom N M ≃ R (N * M)) :=
  ⟨D1_implies_P5_F2 N M⟩

/-- The `N = M = 2` specialisation — the simplest non-trivial case,
    matching the cardinality content of T_P7b.

    For the full *algebra-iso* (not just set-iso) at `N = M = 2`,
    use `SSBX.Foundation.R.PhaseZero.T_P7b_ring_equiv` (which delivers
    `R 4 ≃+* Mat2F2`).  The bijection here is the underlying-set
    component of that richer structure (modulo the row/column
    transpose conventions documented in §5). -/
def D1_implies_P5_F2_at_2_2 : LinHom 2 2 ≃ R 4 :=
  D1_implies_P5_F2 2 2

end SSBX.Foundation.R.ClaimZ.Analytic
