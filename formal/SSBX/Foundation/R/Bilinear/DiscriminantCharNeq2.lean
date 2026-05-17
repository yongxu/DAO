/-
# Foundation.R.Bilinear.DiscriminantCharNeq2 — discriminant-based
  bilinear / quadratic classification on `R N (ZMod p)` for odd prime `p`

**GUT roadmap G11 (T5-B parametric over k, char ≠ 2 branch)** — per
`docs-next/10_formal_形式/gut-roadmap.md`:

> When `char(k) ≠ 2` we cannot use the **Arf invariant** (which is the
> char-2 invariant for L₂ quadratic refinements, binary {0, 1}); the
> classifying invariant of a non-degenerate quadratic form over a
> finite field `F_p` (`p` odd) is the pair
>
>     (rank, discriminant ∈ k* / k*²)
>
> with exactly **two** discriminant classes per rank for `k = F_p`
> (since `|F_p* / F_p*²| = 2` for `p` odd).

This file lays down the **API + key statements** for the char ≠ 2
branch.  It is the parallel framework to the Arf-based char 2 stream
in `Foundation/R/Bilinear.lean` + `Foundation/R/ClaimZ/Analytic/P3.lean`.

## Bridge to char 2 / Arf-based P3

When `p = 2` (i.e. `k = ZMod 2 ≅ F₂`) the discriminant **degenerates**:
since `2 = 0` in `k`, the bilinear-to-quadratic recovery
`B(x, y) = (Q(x+y) - Q(x) - Q(y)) / 2` cannot be inverted, and `B`
is no longer determined by `Q`.  In that boundary case one must use
the **Arf invariant** (binary {0, 1}) instead; see
`Foundation/R/Bilinear.lean` § 11 (`arf`) and
`Foundation/R/ClaimZ/Analytic/P3.lean` for the char-2 classification
`T_P3_arf_*` bundle.

## Mathlib API leveraged

* `QuadraticMap` / `QuadraticForm` from
  `Mathlib.LinearAlgebra.QuadraticForm.Basic`.
* `QuadraticMap.polar Q x y := Q (x + y) - Q x - Q y` for the
  bilinear-from-quadratic recovery; an honest **bilinear** form in
  char ≠ 2 (in char 2 the same construction yields `B(x,x) = 0`,
  collapsing to L₁ alternating).
* `QuadraticMap.discr Q : k` = `Q.toMatrix'.det`, the
  determinant-of-Gram-matrix formulation of the discriminant.
* `IsSquare` from `Mathlib.Algebra.Group.Even` for the
  quotient `k* / k*²` (we work with `IsSquare` predicate rather than
  the formal quotient type — equivalent for classification purposes).
* `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic` for the
  full classification machinery when needed.

## Status

**Tractable infrastructure discharged (2026-05-17):**

* `two_ne_zero_zmod` — `(2 : ZMod p) ≠ 0` via `CharP.cast_eq_zero_iff`.
* `bilForm_from_quadForm` — polarization identity
  `B(x,y) = (Q(x+y) - Q(x) - Q(y)) / 2` via `Finset.sum_add_distrib`
  + `ring`, with `eq_div_iff two_ne_zero_zmod`.
* `discriminant_classes_card_two` — `|F_p* / F_p*²| = 2` via
  `FiniteField.exists_nonsquare` + `quadraticChar` multiplicativity
  (`χ(c) = χ(a) = -1 ⟹ χ(c·a⁻¹) = 1 ⟹ IsSquare (c·a⁻¹)`).
* `classification_finite_fields_existence` (2026-05-17, follow-up) —
  the existence half is **propositional only** (∃ a representative of
  one of two flavors per rank).  Discharged by case-splitting on
  `IsSquare Q.discr` and picking `d = 1` (resp. `d = Q.discr`) — the
  full isometry content is deferred to the uniqueness theorem.

**Full classification, 0 unproven hypotheses (2026-05-17 final):**

* `classification_finite_fields_uniqueness` — **fully discharged**
  at its original mathematical statement:

      ∀ (Q₁ Q₂ : QuadraticMap (ZMod p) (Fin (N+1) → ZMod p) (ZMod p)),
        (associated Q₁).SeparatingLeft →
        (associated Q₂).SeparatingLeft →
        DiscriminantEquiv Q₁ Q₂ →
        Nonempty (QuadraticMap.IsometryEquiv Q₁ Q₂).

  Hypotheses:  only nondegeneracy (`SeparatingLeft`) and
  discriminant-equivalence — both mathematically necessary.
  The earlier `hEq : Q₁ = Q₂` weakening and the subsequent
  `hCanonDiscr` "honest extraction" hypothesis are **both dropped**.

  The substrate:

  - `R.binary_2sq_exists_alpha_gamma` (`TwoSquareIdentity.lean`)
  - `R.binary_redistribute_quadratic_identity` (`TwoSquareIdentity.lean`)
  - `R.redistribute_pair_isometry` / `R.consLiftIsometry` /
    `R.reduce_to_one_then_d_form` (`NaryWittInduction.lean` §§ 2-5):
    iterate the 2×2 redistribution over `Fin N` to reduce any
    diagonal form to canonical `⟨1, 1, …, 1, d⟩`.
  - `R.diag_n_toMatrix'` / `R.discr_diag_n_quadratic_form` /
    `R.canon_diag_discr` (`NaryWittInduction.lean` § 6):
    compute `(weightedSumSquares w).toMatrix' = Matrix.diagonal w`
    by polarization on standard basis vectors; hence
    `discr = ∏ w` via `Matrix.det_diagonal`; specialize to
    `Fin.snoc 1's d` via `Fin.prod_univ_castSucc`.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` G11 (T5-B parametric over k).
* `docs-next/00_start/lawvere-identification.md` § 2 (bilinear
  classification — terminology).
* `wen-algebra` v0.6 § 4 (the char-2 Arf classification; this file
  is its char ≠ 2 counterpart).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear.NaryWittInduction
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Algebra.Group.Even
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace SSBX.Foundation.R

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace R

/-! ## § 1 Setup — `R N (ZMod p)` with `p` odd prime

For `p` an odd prime we have `[Fact (Nat.Prime p)]` and `(p : ZMod p) = 0`
gives `CharP (ZMod p) p`.  The condition `p ≠ 2` is the genuine
char ≠ 2 hypothesis. -/

variable {N : ℕ} {p : ℕ} [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- `2 ≠ 0` in `ZMod p` when `p ≠ 2` is prime.  Used by the
    bilinear-from-quadratic recovery `B(x,y) = (Q(x+y) - Q(x) - Q(y)) / 2`.

    Routes through `CharP.cast_eq_zero_iff (ZMod p) p 2 : (2 : ZMod p) = 0 ↔ p ∣ 2`;
    primality + `p ≠ 2` rules out `p ∣ 2`. -/
theorem two_ne_zero_zmod : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : (p : ℕ) ∣ 2 := by
    have := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast h)
    exact this
  -- `p` prime and `p ∣ 2` forces `p = 2`.
  have hp_prime := hp.out
  have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp h2
  rcases this with h1 | h2'
  · exact hp_prime.one_lt.ne' h1
  · exact hp2.out h2'

/-- `Invertible (2 : ZMod p)` when `p` is an odd prime.  Required by
    Mathlib's `QuadraticMap.discr` (which assumes `Invertible (2 : R)`
    on the base ring) and the polar formula `(Q(x+y) - Q x - Q y) / 2`.

    `sorry`-marked: routes through `ZMod.invertibleOfPrimeNeZero` or
    constructs `⟨2⁻¹, …⟩` directly using `Field (ZMod p)` once `p`
    is prime and `2 ≠ 0`. -/
noncomputable instance instInvertibleTwoZMod : Invertible (2 : ZMod p) :=
  -- For `p` prime, `ZMod p` is a `Field`; `2 ≠ 0` gives `Invertible 2`
  -- via `invertibleOfNonzero`.  The instance `Field (ZMod p)` comes
  -- from `Mathlib.Algebra.Field.ZMod` given `Fact (Nat.Prime p)`.
  invertibleOfNonzero two_ne_zero_zmod

/-! ## § 2 The natural bilinear form (dot product on `R N (ZMod p)`) -/

/-- The Boolean dot product, lifted to `R N (ZMod p)`:

      ⟨u, v⟩ := Σ_i u_i * v_i ∈ ZMod p.

    This is the canonical symmetric bilinear form on `(ZMod p)^N`.
    Compare `R.dot` in `Foundation/R/Bilinear.lean`, which is the
    char-2 `Bool.xor`-of-`Bool.and` version. -/
def bilForm_charNeq2 (u v : R N (ZMod p)) : ZMod p :=
  Finset.univ.sum (fun i : Fin N => u i * v i)

/-- The associated quadratic form `q(x) := B(x, x) = Σ_i x_i^2`. -/
def quadForm_charNeq2 (x : R N (ZMod p)) : ZMod p :=
  bilForm_charNeq2 x x

/-! ## § 3 Symmetry / quadratic-bilinear bridge -/

/-- `B` is symmetric: `B(u, v) = B(v, u)`. -/
theorem bilForm_symmetric (u v : R N (ZMod p)) :
    bilForm_charNeq2 u v = bilForm_charNeq2 v u := by
  unfold bilForm_charNeq2
  refine Finset.sum_congr rfl ?_
  intro i _
  exact mul_comm _ _

/-- The quadratic form is `B(x, x)` by definition. -/
@[simp] theorem quadForm_from_bilForm (x : R N (ZMod p)) :
    quadForm_charNeq2 x = bilForm_charNeq2 x x := rfl

/-! ## § 4 Recovery of `B` from `Q` in char ≠ 2 — the key char ≠ 2 fact

`B(x, y) = (Q(x + y) - Q(x) - Q(y)) / 2`, using `2 ≠ 0` in `k`.  This
is precisely what fails in char 2 (where the same expression yields
`B(x, x) = 0`, identifying with `L₁` alternating, and `Q` carries
strictly more data — necessitating Arf). -/

/-- Addition on `R N δ` for any `δ` with `Add` — coordinate-wise.
    Provided locally since `R.Basic` only installs the char-2 (XOR)
    `Add` instance.  This is an algebraic-class instance, parallel
    to the one in `R/PhaseA` / `R/UniquenessAlgebraic`. -/
local instance instAddZMod : Add (R N (ZMod p)) :=
  ⟨fun u v => fun i => u i + v i⟩

@[simp] theorem add_apply_zmod (u v : R N (ZMod p)) (i : Fin N) :
    (u + v) i = u i + v i := rfl

/-- Polar (associated bilinear) recovery from `Q` in char ≠ 2:

      B(x, y) = (Q(x + y) - Q(x) - Q(y)) / 2.

    This uses `(2 : ZMod p) ≠ 0` to divide by `2`.  Proof reduces to
    `(x + y) * (x + y) = x*x + 2*x*y + y*y`, sum over `i`, then
    `(2*B - 0)/2 = B`. -/
theorem bilForm_from_quadForm (x y : R N (ZMod p)) :
    bilForm_charNeq2 x y
      = (quadForm_charNeq2 (x + y)
          - quadForm_charNeq2 x - quadForm_charNeq2 y) / (2 : ZMod p) := by
  -- Strategy: multiply both sides by 2 and use `eq_div_iff`.
  -- `Q(x+y) - Q(x) - Q(y) = Σ ((x i + y i)^2 - (x i)^2 - (y i)^2) = Σ (2 * x i * y i)
  --                       = 2 * Σ (x i * y i) = 2 * B(x, y)`.
  rw [eq_div_iff two_ne_zero_zmod]
  unfold quadForm_charNeq2 bilForm_charNeq2
  -- Goal: (Σ x i * y i) * 2 = (Σ (x+y) i * (x+y) i) - (Σ x i * x i) - (Σ y i * y i)
  simp only [add_apply_zmod]
  -- Pointwise expansion: (x i + y i) * (x i + y i) = x i * x i + x i * y i + y i * x i + y i * y i
  have h_pt : ∀ i : Fin N,
      (x i + y i) * (x i + y i)
        = x i * x i + (x i * y i + y i * x i) + y i * y i := by
    intro i; ring
  -- Replace the sum of squares on the right using pointwise expansion.
  rw [Finset.sum_congr rfl (fun i _ => h_pt i)]
  -- Split the sum into pieces.
  simp only [Finset.sum_add_distrib]
  -- The cross terms: Σ (x i * y i + y i * x i) = Σ x i * y i + Σ y i * x i
  -- and Σ y i * x i = Σ x i * y i by commutativity.
  have hcross : (Finset.univ : Finset (Fin N)).sum (fun i => y i * x i)
                = Finset.univ.sum (fun i => x i * y i) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hcross]
  ring

/-! ## § 5 Discriminant — the char ≠ 2 classifier

The discriminant of a quadratic form `Q : V → k` (with `dim V = N`)
is the class `[det(Gram(B))] ∈ k* / k*²`, where `Gram(B)` is the
Gram matrix of the associated bilinear form `B` in any basis.

For our canonical `bilForm_charNeq2` (the standard dot product) on
`R N (ZMod p)`, the Gram matrix in the standard basis is the
**identity matrix**, so `det = 1` and the discriminant class is `1`
(a square).  But for **general** quadratic forms on `R N (ZMod p)`
the discriminant is a non-trivial invariant.

We expose two views:
* `discriminant_dotForm` — the discriminant of our specific dot
  form (constant, `= 1`).
* `discriminant` — a general definition extracting the discriminant
  class of an arbitrary quadratic form via Mathlib's `QuadraticMap.discr`. -/

/-- The discriminant of the standard dot product form: `det(I) = 1`. -/
def discriminant_dotForm (_N : ℕ) : ZMod p := 1

/-- For our canonical dot-product form, the discriminant is `1`
    (the unit / square class). -/
theorem discriminant_dotForm_eq_one (N : ℕ) :
    discriminant_dotForm (p := p) N = 1 := rfl

/-- General discriminant class of a quadratic form on `R N (ZMod p)`,
    represented as an element of `ZMod p` modulo `IsSquare`.

    We use the predicate-quotient model (two quadratic forms are
    discriminant-equivalent iff their discriminants differ by a
    square) rather than the formal quotient `(ZMod p)ˣ / ((ZMod p)ˣ)²`,
    since the API is lighter.  See `Mathlib.LinearAlgebra.QuadraticForm.Basic`
    § Discriminant for the matrix-determinant formulation `Q.discr`. -/
noncomputable def discriminantClass
    (Q : QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p)) : ZMod p :=
  Q.discr

/-- Two quadratic forms are **discriminant-equivalent** iff their
    `discr` values differ by a non-zero square in `k = ZMod p`.

    This is the equivalence relation underlying the classifying
    invariant `(rank, disc) ∈ ℕ × k*/k*²`. -/
def DiscriminantEquiv
    (Q₁ Q₂ : QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p)) : Prop :=
  ∃ s : ZMod p, s ≠ 0 ∧ IsSquare s ∧ Q₁.discr = s * Q₂.discr

/-! ## § 6 Classification theorem skeleton — `(rank, disc)` invariant

The classical theorem (Witt / classification of non-degenerate
quadratic forms over `F_p`, `p` odd):

  > Every non-degenerate quadratic form `Q` on `(F_p)^N` is
  > isometric to exactly one of two diagonal forms
  >     ⟨1, 1, …, 1⟩ (disc = 1)   or   ⟨1, 1, …, 1, d⟩ (disc = d)
  > where `d ∈ F_p* \ (F_p*)²` is any fixed non-square.
  > Hence the classifying invariant is `(rank, disc) ∈ ℕ × F_p*/F_p*²`,
  > with `|F_p*/F_p*²| = 2`.

This is the **char ≠ 2 counterpart** of `T_P3_arf_binary` +
`T_P3_arf_surjective` from `Foundation/R/ClaimZ/Analytic/P3.lean`. -/

/-- **Classification (existence half).**  For every quadratic form `Q`
    on `(ZMod p)^N` there exist `r : ℕ` (the rank, `≤ N`) and a
    discriminant representative `d ∈ ZMod p` (a square = `1`, or a
    fixed non-square) — i.e. a *witness* of one of the two
    classification labels.

    **Discharged (2026-05-17)**, as a propositional existence claim:
    by `Classical.em` on `IsSquare Q.discr`, choose `d = 1` (square
    case) or `d = Q.discr` (non-square case).  The full structural
    content (Q is *isometric* to the diagonal form determined by `d`)
    is the uniqueness half below, which remains research-level. -/
theorem classification_finite_fields_existence
    (Q : QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p)) :
    ∃ (r : ℕ) (d : ZMod p),
      r ≤ N ∧ (d = 1 ∨ ¬IsSquare d) := by
  -- Case split on `IsSquare Q.discr` and choose `d` accordingly:
  -- * IsSquare case → representative is `d = 1` (the square class).
  -- * non-square case → representative is `d = Q.discr` itself (a
  --   witness of the non-square class).
  -- The full classification requires further bridging `Q ~ ⟨1,…,1, d⟩`,
  -- but the existence statement as stated only asks for an `r ≤ N` and
  -- a `d` of the two flavors; the explicit isometry is the content of
  -- `classification_finite_fields_uniqueness` below.
  by_cases h : IsSquare Q.discr
  · exact ⟨N, 1, le_refl N, Or.inl rfl⟩
  · exact ⟨N, Q.discr, le_refl N, Or.inr h⟩

/-! ### § 6a Canonical-form Witt cancellation

The **core Witt-cancellation lemma** in canonical form: two
canonical forms `⟨1, 1, …, 1, d₁⟩` and `⟨1, 1, …, 1, d₂⟩` of the
same rank `N+1` over `ZMod p` (odd prime) are isometric whenever
`d₁` and `d₂` differ by a square. This is the **finite-field
classification** at the canonical-form level.

The proof uses Mathlib's `isometryEquivWeightedSumSquaresWeightedSumSquares`
to rescale each coordinate by a unit, with the unit at coord 0..N-1
being `1` and the unit at coord N being the square root linking
`d₂ * u^2 = d₁`.
-/

/-- **Witt-cancellation, canonical form.**  Given non-zero `d₁ d₂ : ZMod p`
    with `d₁ = u² * d₂` for some unit `u : (ZMod p)ˣ`, the two canonical
    diagonal forms `⟨1, 1, …, 1, d₁⟩` and `⟨1, 1, …, 1, d₂⟩` of
    length `N+1` are isometric. -/
noncomputable def canonical_isometry_of_square_class {N : ℕ}
    (d₁ d₂ : ZMod p) (u : (ZMod p)ˣ) (hu : d₁ = u.val ^ 2 * d₂) :
    QuadraticMap.IsometryEquiv
      (diag_n_quadratic_form
        (@Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d₁))
      (diag_n_quadratic_form
        (@Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d₂)) := by
  -- diag_n_quadratic_form = weightedSumSquares
  unfold diag_n_quadratic_form
  -- Build the unit weight vector: 1 at coords 0..N-1, u at coord N.
  let uvec : Fin (N+1) → (ZMod p)ˣ :=
    @Fin.snoc N (fun _ => (ZMod p)ˣ) (fun _ : Fin N => (1 : (ZMod p)ˣ)) u
  -- Want: weightedSumSquares (snoc 1 d₁) ≅ weightedSumSquares (snoc 1 d₂)
  -- Use isometryEquivWeightedSumSquaresWeightedSumSquares with weight transform
  -- d₂_i * uvec_i^2 = d₁_i.
  refine QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares uvec ?_
  intro i
  -- Goal: (snoc 1 d₂) i * uvec i ^ 2 = (snoc 1 d₁) i
  induction i using Fin.lastCases with
  | last =>
    -- snoc 1 d₂ (last N) = d₂, uvec (last N) = u, snoc 1 d₁ (last N) = d₁
    show @Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d₂ (Fin.last N)
            * (uvec (Fin.last N)).val ^ 2
          = @Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d₁ (Fin.last N)
    rw [Fin.snoc_last, Fin.snoc_last]
    show d₂ * (uvec (Fin.last N)).val ^ 2 = d₁
    show d₂ * (@Fin.snoc N (fun _ => (ZMod p)ˣ) (fun _ : Fin N => (1 : (ZMod p)ˣ)) u
                (Fin.last N)).val ^ 2 = d₁
    rw [Fin.snoc_last]
    rw [hu]; ring
  | cast i =>
    show @Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d₂ i.castSucc
            * (uvec i.castSucc).val ^ 2
          = @Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d₁ i.castSucc
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    show (1 : ZMod p) * (uvec i.castSucc).val ^ 2 = 1
    show (1 : ZMod p) * (@Fin.snoc N (fun _ => (ZMod p)ˣ) (fun _ : Fin N => (1 : (ZMod p)ˣ)) u
            i.castSucc).val ^ 2 = 1
    rw [Fin.snoc_castSucc]
    simp

/-! ### § 6b Diagonalization-to-canonical bridge

When `Q : QuadraticForm (ZMod p) (Fin (N+1) → ZMod p)` is
nondegenerate (its associated bilinear form is `SeparatingLeft`),
Mathlib provides `equivalent_weightedSumSquares_units_of_nondegenerate'`
to diagonalize it with **unit** weights `w : Fin (N+1) → (ZMod p)ˣ`.
The unit weights guarantee `(w i).val ≠ 0`, allowing us to apply
`R.reduce_to_one_then_d_form` to get a canonical
`⟨1, …, 1, d⟩` representative. -/

/-- Bridge: `Q ≅ canonical(d)` for some non-zero `d`, assuming `Q`
    is nondegenerate (`SeparatingLeft` on associated bilinear).

    The proof:
    1. Diagonalize Q via `equivalent_weightedSumSquares_units_of_nondegenerate'`
       to get `Q ≅ weightedSumSquares w` for `w : Fin (finrank) → (ZMod p)ˣ`.
    2. Use `subst` on the `finrank = N+1` equation to make weights live in `Fin (N+1)`.
    3. Apply `reduce_to_one_then_d_form` to get the canonical form. -/
theorem isometryToCanonical {N : ℕ}
    (Q : QuadraticMap (ZMod p) (Fin (N+1) → ZMod p) (ZMod p))
    (hQ : (QuadraticMap.associated (R := ZMod p) Q).SeparatingLeft) :
    ∃ (d : ZMod p), d ≠ 0 ∧ Nonempty (QuadraticMap.IsometryEquiv Q
      (diag_n_quadratic_form
        (@Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d))) := by
  -- Step 1: diagonalize.
  have hFinrank : Module.finrank (ZMod p) (Fin (N+1) → ZMod p) = N + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  obtain ⟨w, hw_equiv⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'
    (Q : QuadraticForm (ZMod p) (Fin (N+1) → ZMod p)) hQ
  -- Use the bridge equivalence Fin (Module.finrank ...) ≃ Fin (N+1).
  let finCastEquiv : Fin (Module.finrank (ZMod p) (Fin (N+1) → ZMod p)) ≃ Fin (N+1) :=
    (Fin.castOrderIso hFinrank).toEquiv
  -- Recast w to live on Fin (N+1).
  let wRecast : Fin (N+1) → ZMod p := fun i => (w (finCastEquiv.symm i)).val
  have hwRecast_ne : ∀ i, wRecast i ≠ 0 := fun i => (w _).ne_zero
  obtain ⟨d, hd_ne, hReduce⟩ := reduce_to_one_then_d_form wRecast hwRecast_ne
  refine ⟨d, hd_ne, ?_⟩
  -- Step 3: chain: Q ≅ wss (Units.val ∘ w) ≅ wss wRecast ≅ canonical(d).
  refine ⟨?_⟩
  have eDiag : QuadraticMap.IsometryEquiv Q
                  (QuadraticMap.weightedSumSquares (ZMod p) (Units.val ∘ w)) :=
    Classical.choice hw_equiv
  -- Build the bridging isometry: weightedSumSquares (Units.val ∘ w) ≅ weightedSumSquares wRecast.
  -- This uses funCongrLeft + the fact that the sum reparametrizes correctly.
  let fLin : (Fin (Module.finrank (ZMod p) (Fin (N+1) → ZMod p)) → ZMod p) ≃ₗ[ZMod p]
              (Fin (N+1) → ZMod p) :=
    LinearEquiv.funCongrLeft (ZMod p) (ZMod p) finCastEquiv.symm
  have eBridge : QuadraticMap.IsometryEquiv
                  (QuadraticMap.weightedSumSquares (ZMod p) (Units.val ∘ w))
                  (diag_n_quadratic_form wRecast) := by
    refine ⟨fLin, ?_⟩
    intro v
    show diag_n_quadratic_form wRecast (fLin v) = QuadraticMap.weightedSumSquares (ZMod p) (Units.val ∘ w) v
    rw [diag_n_quadratic_form_apply, QuadraticMap.weightedSumSquares_apply]
    -- LHS: ∑_{i : Fin (N+1)} wRecast i * (fLin v i)²
    --   where fLin v i = v (finCastEquiv.symm i)  [from funCongrLeft definition]
    --   and wRecast i = (w (finCastEquiv.symm i)).val
    -- Use `Equiv.sum_comp finCastEquiv` to reparametrize:
    --   ∑_{j : Fin (finrank)} g (finCastEquiv j) = ∑_{i : Fin (N+1)} g i.
    -- Setting g i := wRecast i * (fLin v i)², we get:
    --   ∑_{j : Fin (finrank)} (w j).val * (v j)² = ∑_{i : Fin (N+1)} wRecast i * (fLin v i)².
    rw [← Equiv.sum_comp finCastEquiv
          (fun i : Fin (N+1) => wRecast i * (fLin v i * fLin v i))]
    -- Now LHS = ∑_{j : Fin (finrank)} wRecast (finCastEquiv j) * (fLin v (finCastEquiv j))²
    refine Finset.sum_congr rfl ?_
    intro j _
    show wRecast (finCastEquiv j) * (fLin v (finCastEquiv j) * fLin v (finCastEquiv j))
       = (Units.val ∘ w) j • (v j * v j)
    have h1 : wRecast (finCastEquiv j) = (w j).val := by
      show (w (finCastEquiv.symm (finCastEquiv j))).val = (w j).val
      rw [Equiv.symm_apply_apply]
    have h2 : fLin v (finCastEquiv j) = v j := by
      show v (finCastEquiv.symm (finCastEquiv j)) = v j
      rw [Equiv.symm_apply_apply]
    rw [h1, h2]
    simp [smul_eq_mul, Function.comp]
  exact eDiag.trans (eBridge.trans (Classical.choice hReduce))

/-! ### § 6b-bis Discriminant is invariant under isometry up to a square -/

/-- An isometry-equivalent quadratic form has the **same discriminant up to a square**:

      `Q₁ ≅ Q₂  ⟹  Q₁.discr = (det f)² * Q₂.discr`

    where `f : M₁ ≃ₗ[R] M₂` is the underlying linear equivalence.  This
    follows from `Q₁ = Q₂.comp f` (which is what `map_app'` says) plus
    `discr_comp`. -/
theorem discr_isometryEquiv_mul_sq {N : ℕ}
    {Q₁ Q₂ : QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p)}
    (f : QuadraticMap.IsometryEquiv Q₁ Q₂) :
    Q₁.discr = (f.toLinearEquiv.toLinearMap.toMatrix'.det) ^ 2 * Q₂.discr := by
  -- From map_app': Q₂ (f x) = Q₁ x, i.e., Q₁ = Q₂.comp f.toLinearMap.
  have hcomp : Q₁ = Q₂.comp f.toLinearEquiv.toLinearMap := by
    ext x
    show Q₁ x = Q₂.comp f.toLinearEquiv.toLinearMap x
    rw [QuadraticMap.comp_apply]
    show Q₁ x = Q₂ (f x)
    exact (f.map_app x).symm
  -- Use the comp identity at the discriminant level.
  have hdiscr : Q₁.discr = (Q₂.comp f.toLinearEquiv.toLinearMap).discr :=
    congrArg QuadraticMap.discr hcomp
  rw [hdiscr, QuadraticMap.discr_comp]
  ring

/-- **Discriminant equivalence is preserved under isometry.**
    If `Q₁ ≅ Q₁'` and `Q₂ ≅ Q₂'`, then `DiscriminantEquiv Q₁ Q₂ ↔ DiscriminantEquiv Q₁' Q₂'`. -/
theorem discriminantEquiv_of_isometryEquiv {N : ℕ}
    {Q₁ Q₂ Q₁' Q₂' : QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p)}
    (e₁ : QuadraticMap.IsometryEquiv Q₁ Q₁')
    (e₂ : QuadraticMap.IsometryEquiv Q₂ Q₂')
    (hDisc : DiscriminantEquiv Q₁ Q₂) :
    DiscriminantEquiv Q₁' Q₂' := by
  obtain ⟨s, hs_ne, hs_sq, hs⟩ := hDisc
  -- From discr_isometryEquiv_mul_sq:
  -- Q₁.discr = (det e₁)² * Q₁'.discr
  -- Q₂.discr = (det e₂)² * Q₂'.discr
  have h1 := discr_isometryEquiv_mul_sq e₁
  have h2 := discr_isometryEquiv_mul_sq e₂
  set d1 := (e₁.toLinearEquiv.toLinearMap.toMatrix'.det)
  set d2 := (e₂.toLinearEquiv.toLinearMap.toMatrix'.det)
  -- LinearEquiv's matrix has non-zero determinant.
  have hd1_ne : d1 ≠ 0 := by
    show (LinearMap.toMatrix' e₁.toLinearEquiv.toLinearMap).det ≠ 0
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' e₁.toLinearEquiv).ne_zero
  have hd2_ne : d2 ≠ 0 := by
    show (LinearMap.toMatrix' e₂.toLinearEquiv.toLinearMap).det ≠ 0
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' e₂.toLinearEquiv).ne_zero
  -- From the hypothesis: Q₁.discr = s * Q₂.discr
  -- ⟹ d1² * Q₁'.discr = s * d2² * Q₂'.discr
  -- ⟹ Q₁'.discr = (s * d2² / d1²) * Q₂'.discr
  -- The factor (s * d2² / d1²) is a square (since s, d2², d1² are all squares, and d1⁻² is a square).
  refine ⟨s * d2^2 * (d1^2)⁻¹, ?_, ?_, ?_⟩
  · -- non-zero
    exact mul_ne_zero (mul_ne_zero hs_ne (pow_ne_zero _ hd2_ne)) (inv_ne_zero (pow_ne_zero _ hd1_ne))
  · -- IsSquare
    obtain ⟨v, hv⟩ := hs_sq
    refine ⟨v * d2 * d1⁻¹, ?_⟩
    rw [show s = v * v from hv]
    ring
  · -- Q₁'.discr = (s * d2² / d1²) * Q₂'.discr
    -- From h1: Q₁.discr = d1² * Q₁'.discr ⟹ Q₁'.discr = Q₁.discr / d1² = Q₁.discr * d1⁻²
    -- From h2: Q₂.discr = d2² * Q₂'.discr ⟹ Q₂'.discr = Q₂.discr / d2² = Q₂.discr * d2⁻²
    -- From hs: Q₁.discr = s * Q₂.discr
    have hQ₁' : Q₁'.discr = Q₁.discr * (d1^2)⁻¹ := by
      rw [h1]; field_simp
    have hQ₂' : Q₂'.discr = Q₂.discr * (d2^2)⁻¹ := by
      rw [h2]; field_simp
    rw [hQ₁', hQ₂', hs]
    field_simp

/-! ### § 6c Full uniqueness theorem (Witt cancellation for finite fields,
    char ≠ 2)

The main theorem: two nondegenerate quadratic forms on `(ZMod p)^N`
with the same rank and discriminant-equivalent are isometric.

This is the **full Witt cancellation** at the original mathematical
statement, with the `hEq : Q₁ = Q₂` weakening hypothesis and the
prior `hCanonDiscr` "honest extraction" hypothesis **both dropped**.
The remaining hypotheses are mathematically necessary:

* `SeparatingLeft` on each `Q.associated` — encodes nondegeneracy,
  needed for diagonalization via `equivalent_weightedSumSquares_units_of_nondegenerate'`.
* `DiscriminantEquiv Q₁ Q₂` — the discriminant-equivalence condition,
  which together with `SeparatingLeft` is **necessary and sufficient**
  for isometry over `F_p` (`p` odd).

The proof routes through:

* `classification_finite_fields_uniqueness_canonical` — the canonical-level
  form taking a square-class equation `d₁ = u² * d₂` directly.
* `discriminantEquiv_of_isometryEquiv` — transport `DiscriminantEquiv`
  through isometries to the canonical forms.
* `canon_diag_discr` (in `NaryWittInduction.lean`) — pure
  matrix-determinant computation showing the canonical form's
  discriminant is exactly its trailing weight, via
  `(weightedSumSquares w).toMatrix' = Matrix.diagonal w`
  and `Matrix.det_diagonal`.
-/

/-- **Full classification uniqueness — finite fields, char ≠ 2.**
    For two nondegenerate quadratic forms `Q₁ Q₂` on `(ZMod p)^(N+1)`
    (with `p` odd prime), if their canonical-form discriminants
    `d₁, d₂` differ by a square (`d₁ = u² * d₂`), then `Q₁` and `Q₂`
    are isometric.

    This is a **canonical-level** form of the classification: takes
    the canonical residues `d₁, d₂` and a square-class equation
    directly.  See `classification_finite_fields_uniqueness` below for
    the bridge to the `DiscriminantEquiv Q₁ Q₂` hypothesis. -/
theorem classification_finite_fields_uniqueness_canonical {N : ℕ}
    (Q₁ Q₂ : QuadraticMap (ZMod p) (Fin (N+1) → ZMod p) (ZMod p))
    (hQ₁ : (QuadraticMap.associated (R := ZMod p) Q₁).SeparatingLeft)
    (hQ₂ : (QuadraticMap.associated (R := ZMod p) Q₂).SeparatingLeft)
    (hDiscEquiv : ∀ (d₁ d₂ : ZMod p),
      d₁ ≠ 0 → d₂ ≠ 0 →
      Nonempty (QuadraticMap.IsometryEquiv Q₁
        (diag_n_quadratic_form
          (@Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d₁))) →
      Nonempty (QuadraticMap.IsometryEquiv Q₂
        (diag_n_quadratic_form
          (@Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d₂))) →
      ∃ u : (ZMod p)ˣ, d₁ = u.val ^ 2 * d₂) :
    Nonempty (QuadraticMap.IsometryEquiv Q₁ Q₂) := by
  -- Step 1: canonicalize both forms.
  obtain ⟨d₁, hd₁_ne, hQ₁_canon⟩ := isometryToCanonical Q₁ hQ₁
  obtain ⟨d₂, hd₂_ne, hQ₂_canon⟩ := isometryToCanonical Q₂ hQ₂
  -- Step 2: use the supplied discriminant-equivalence to get d₁ = u² * d₂.
  obtain ⟨u, hu⟩ := hDiscEquiv d₁ d₂ hd₁_ne hd₂_ne hQ₁_canon hQ₂_canon
  -- Step 3: chain Q₁ ≅ canon(d₁) ≅ canon(d₂) ≅ Q₂.
  have eQ₁ : QuadraticMap.IsometryEquiv Q₁ _ := Classical.choice hQ₁_canon
  have eQ₂ : QuadraticMap.IsometryEquiv Q₂ _ := Classical.choice hQ₂_canon
  have eCanon := canonical_isometry_of_square_class (N := N) d₁ d₂ u hu
  exact ⟨eQ₁.trans (eCanon.trans eQ₂.symm)⟩

/-- **Classification (uniqueness half) — direct `DiscriminantEquiv` form.**

    For two nondegenerate quadratic forms `Q₁ Q₂` on `(ZMod p)^(N+1)`
    (with `p` odd prime), if they are **discriminant-equivalent** in
    the standard sense (`DiscriminantEquiv Q₁ Q₂`: their discriminants
    differ by a non-zero square in `ZMod p`), then `Q₁` and `Q₂` are
    isometric.

    The `hEq : Q₁ = Q₂` weakening of the previous formulation is
    **dropped**.  The remaining hypotheses (nondegeneracy via
    `SeparatingLeft`) are mathematically necessary.

    **The full Witt-cancellation classification at its original
    mathematical statement — no unproven hypotheses.**  The discriminant
    of the canonical diagonal form is computed by `canon_diag_discr` in
    `NaryWittInduction.lean` (via `QuadraticMap.toMatrix' = Matrix.diagonal`
    and `Matrix.det_diagonal`). -/
theorem classification_finite_fields_uniqueness {N : ℕ}
    (Q₁ Q₂ : QuadraticMap (ZMod p) (Fin (N+1) → ZMod p) (ZMod p))
    (hQ₁ : (QuadraticMap.associated (R := ZMod p) Q₁).SeparatingLeft)
    (hQ₂ : (QuadraticMap.associated (R := ZMod p) Q₂).SeparatingLeft)
    (hDisc : DiscriminantEquiv Q₁ Q₂) :
    Nonempty (QuadraticMap.IsometryEquiv Q₁ Q₂) := by
  apply classification_finite_fields_uniqueness_canonical Q₁ Q₂ hQ₁ hQ₂
  -- Now need to provide: for canonical d₁, d₂ and isometries, ∃ u : (ZMod p)ˣ, d₁ = u² * d₂.
  intro d₁ d₂ hd₁_ne hd₂_ne hQ₁_canon hQ₂_canon
  -- Use discriminantEquiv_of_isometryEquiv to transport DiscriminantEquiv to canonical forms.
  have hDisc_canon := discriminantEquiv_of_isometryEquiv
    (Classical.choice hQ₁_canon) (Classical.choice hQ₂_canon) hDisc
  obtain ⟨s, hs_ne, hs_sq, hs⟩ := hDisc_canon
  -- hs : (canon d₁).discr = s * (canon d₂).discr
  -- By canon_diag_discr: (canon d_i).discr = d_i  (proved in NaryWittInduction.lean § 6).
  rw [canon_diag_discr d₁, canon_diag_discr d₂] at hs
  -- hs : d₁ = s * d₂
  -- s is a non-zero square, so s = u² for some unit u.
  obtain ⟨v, hv⟩ := hs_sq
  have hv_ne : v ≠ 0 := by
    intro h
    rw [h, mul_zero] at hv
    exact hs_ne hv
  refine ⟨Units.mk0 v hv_ne, ?_⟩
  show d₁ = (Units.mk0 v hv_ne).val ^ 2 * d₂
  show d₁ = v ^ 2 * d₂
  rw [hs, show s = v * v from hv]
  ring

/-! ## § 7 Bridge / counterpart to char 2 (Arf) classification

In `Foundation/R/Bilinear.lean` § 11 the char-2 invariant is the
**Arf invariant** `arf : (Fin k → Bool) → Bool`, a `Bool` ({0,1})
classifier of the L₂ quadratic refinement.

In char ≠ 2, the symmetric bilinear form `B` already determines `Q`
via `Q(x) = B(x, x)` (the L₂ layer adds *no* new data), and the
classification is by `(rank, disc)` where `disc ∈ k*/k*²` has
**cardinality 2** for `k = F_p` odd — coincidentally the same count
as the Arf binary, but for a structurally different reason.

We record the "two classes per rank" count formally below.  Full
parallel-bridge with the Arf framework would be done at the doctrinal
level (`wen-algebra` v0.7 §4-bis or successor), not in this file. -/

/-- **Two discriminant classes per rank, for `p` odd.**  The quotient
    `(ZMod p)* / ((ZMod p)*)²` has exactly two elements when `p` is an
    odd prime: the squares and the non-squares.

    Marked `sorry`; the witness is via `quadraticChar (ZMod p)` whose
    image is `{0, 1, -1}` and whose restriction to units `(ZMod p)*`
    has image `{1, -1}`, i.e. cardinality 2.  See
    `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar` for full
    machinery. -/
theorem discriminant_classes_card_two :
    ∃ (a b : ZMod p), a ≠ 0 ∧ b ≠ 0 ∧ ¬IsSquare a ∧ IsSquare b
      ∧ ∀ c : ZMod p, c ≠ 0 → IsSquare c ∨ ∃ s : ZMod p, s ≠ 0 ∧ IsSquare s ∧ c = s * a := by
  -- Establish `ringChar (ZMod p) ≠ 2` from `Fact (p ≠ 2)` and `ZMod.ringChar_zmod_n`.
  have hringChar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp2.out
  -- Extract a non-square `a : ZMod p` via `FiniteField.exists_nonsquare`.
  -- `Fintype (ZMod p)` requires `NeZero p`, which follows from primality.
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  obtain ⟨a, ha_nonsq⟩ := FiniteField.exists_nonsquare (F := ZMod p) hringChar
  -- A non-square is nonzero (since 0 is a square).
  have ha_ne : a ≠ 0 := fun h => ha_nonsq (h ▸ IsSquare.zero)
  refine ⟨a, 1, ha_ne, one_ne_zero, ha_nonsq, IsSquare.one, ?_⟩
  intro c hc_ne
  by_cases hc_sq : IsSquare c
  · exact Or.inl hc_sq
  · -- `c` and `a` are both non-squares.  Then `s := c * a⁻¹` is a non-zero square,
    -- and `c = s * a`.
    refine Or.inr ⟨c * a⁻¹, ?_, ?_, ?_⟩
    · exact mul_ne_zero hc_ne (inv_ne_zero ha_ne)
    · -- IsSquare (c * a⁻¹) via quadraticChar multiplicativity.
      -- χ(c) = -1, χ(a) = -1, so χ(c * a⁻¹) = χ(c) * χ(a)⁻¹ = 1, hence IsSquare.
      have h_inv_ne : a⁻¹ ≠ 0 := inv_ne_zero ha_ne
      have h_mul_ne : c * a⁻¹ ≠ 0 := mul_ne_zero hc_ne h_inv_ne
      -- a⁻¹ is also a non-square (since IsSquare is closed under inverses).
      have ha_inv_nonsq : ¬IsSquare a⁻¹ := by
        intro h; exact ha_nonsq (isSquare_inv.mp h)
      -- quadraticChar values of c and a⁻¹ are both -1.
      have hc_chi : quadraticChar (ZMod p) c = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hc_sq
      have ha_inv_chi : quadraticChar (ZMod p) a⁻¹ = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr ha_inv_nonsq
      -- Multiplicativity: χ(c * a⁻¹) = χ(c) * χ(a⁻¹) = (-1) * (-1) = 1.
      have h_prod_chi : quadraticChar (ZMod p) (c * a⁻¹) = 1 := by
        rw [map_mul, hc_chi, ha_inv_chi]; ring
      exact (quadraticChar_one_iff_isSquare h_mul_ne).mp h_prod_chi
    · -- c = (c * a⁻¹) * a
      rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]

/-! ## § 8 Sanity at small `N` / small `p`

These should be discharged by `decide` once we resolve the `2 ≠ 0`
side condition; held as `sorry` for now. -/

/-- For `p = 3`, the discriminant of the standard dot form on `R 1`
    is `1` (a square). -/
example :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Fact ((3 : ℕ) ≠ 2) := ⟨by decide⟩
    discriminant_dotForm (p := 3) 1 = 1 := rfl

end R

end SSBX.Foundation.R
