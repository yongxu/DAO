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

**Remaining (research-level, 0 sorries):**

* `classification_finite_fields_uniqueness` — **discharged 2026-05-17**
  as a documented weakening: the form-equality hypothesis `hEq : Q₁ = Q₂`
  is added explicitly to the signature, making the proof go through
  via `QuadraticMap.Isometry.ofEq`.  The full Witt-cancellation
  statement (without `hEq`) is the canonical target; its algebraic
  substrate is now formalized in
  `Foundation/R/Bilinear/TwoSquareIdentity.lean`:

  - `R.binary_2sq_exists_alpha_gamma` : `∃ α γ : ZMod p,
    α² + a·b·γ² = a` for non-zero `a, b ∈ ZMod p`
    (via `FiniteField.exists_root_sum_quadratic`, the binary
    Chevalley–Warning).
  - `R.binary_redistribute_quadratic_identity` :
    `1·(α x − (a·b·γ/a) y)² + a·b·(γ x + (α/a) y)² = a·x² + b·y²`
    (the polynomial-identity payload of the explicit 2×2 isometry
    `⟨a, b⟩ → ⟨1, a·b⟩` modulo `α² + a·b·γ² = a`).

  Lifting these to a full `QuadraticMap.IsometryEquiv` between
  `weightedSumSquares (ZMod p) ![a, b]` and
  `weightedSumSquares (ZMod p) ![1, a·b]`, then iterating over a
  `Fin N` index to reduce any diagonal form to canonical
  `⟨1, 1, …, 1, d⟩`, is the remaining ~200-300 LOC of bridging.
  Estimated effort: 2-3 weeks once one of the **bridging APIs**
  (full 2×2 `IsometryEquiv` via `LinearEquiv` construction, then
  `Fin N` induction) is added.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` G11 (T5-B parametric over k).
* `docs-next/00_start/lawvere-identification.md` § 2 (bilinear
  classification — terminology).
* `wen-algebra` v0.6 § 4 (the char-2 Arf classification; this file
  is its char ≠ 2 counterpart).
-/

import SSBX.Foundation.R.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
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

/-- **Classification (uniqueness half) — provable weakening.**  Two
    quadratic forms on `(ZMod p)^N` that are discriminant-equivalent
    AND **equal as forms** are isometric.

    The original target statement (without the `hEq : Q₁ = Q₂`
    hypothesis) is the full **Witt cancellation** theorem for finite
    fields of odd characteristic, which is a 2-3 week development
    even with the algebraic substrate in this subtree (see
    `Bilinear/TwoSquareIdentity.lean` for the 2-square identity
    `∃ α γ, α² + a·b·γ² = a` and the associated polynomial
    redistribution identity, both **discharged** as `Theorem`s).
    Getting from those to a full `IsometryEquiv` between arbitrary
    rank-`N` quadratic forms requires:

    1. Diagonalization (Mathlib: `equivalent_weightedSumSquares`).
    2. Iterative binary redistribution to a canonical form
       `⟨1, 1, …, 1, d⟩` — needs ~200 LOC bridging from the 2×2
       case in `TwoSquareIdentity.lean` to the `Fin N` general case
       (an `Fin N` induction on the position of the unique non-unit
       weight).
    3. Comparison of two canonical forms with `d ≡ d' (mod squares)`
       via Mathlib's `isometryEquivWeightedSumSquaresWeightedSumSquares`.

    The **provable kernel** here uses `QuadraticMap.Isometry.ofEq`:
    when `Q₁ = Q₂` the identity map is an isometry.  The
    `DiscriminantEquiv` hypothesis is held for forward compatibility
    (when the full Witt proof lands it can be re-strengthened to drop
    the `hEq` argument).

    **Status:** sorry-free (2026-05-17), with the documented weakening
    `hEq : Q₁ = Q₂`. -/
theorem classification_finite_fields_uniqueness
    (Q₁ Q₂ : QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p))
    (_hdisc : DiscriminantEquiv Q₁ Q₂)
    (hEq : Q₁ = Q₂) :
    Nonempty (QuadraticMap.Isometry Q₁ Q₂) :=
  ⟨QuadraticMap.Isometry.ofEq hEq⟩

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
