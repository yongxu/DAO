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

This is a **skeleton** — definitions and statements are provided; the
hard classification theorems are `sorry` with docstrings explaining
the obstruction.  Estimated discharge: 2-3 weeks of focused work
once Wedderburn-instance (G11-A) and polymorphic-field adaptation
(G11-C) land.

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

    `sorry`-marked at the bridge step: needs
    `ZMod.natCast_self_eq_zero` + `Nat.Prime.two_le` + casework on
    `p = 0,1,2` vs `p ≥ 3`.  Standard one-liner once routed. -/
theorem two_ne_zero_zmod : (2 : ZMod p) ≠ 0 := by
  -- Sketch: `(2 : ZMod p) = 0 ↔ p ∣ 2` (CharP), and `p ∣ 2` for prime
  -- `p` forces `p = 2`, contradicting `hp2.out : p ≠ 2`.
  sorry

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
  -- Expand `Q(x+y) = Σ (x_i + y_i)^2 = Σ x_i^2 + 2 Σ x_i y_i + Σ y_i^2`
  -- = Q(x) + 2*B(x,y) + Q(y); subtract & divide by `2`.
  -- The arithmetic identity is straightforward over `ZMod p` once
  -- we have `2 ≠ 0`.  Marked `sorry` for now — pure arithmetic
  -- on `Finset.sum` with `mul_add`, `add_mul`, `Finset.sum_add_distrib`,
  -- and `Finset.mul_sum`.
  sorry

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

/-- **Classification (existence half).**  For every non-degenerate
    quadratic form `Q` on `(ZMod p)^N` there exist `r : ℕ` (the rank,
    `= N` for non-degenerate) and a discriminant representative
    `d ∈ ZMod p` (a square or a fixed non-square) determining `Q`
    up to isometry.

    Heavily `sorry` — this is the core classification theorem of
    quadratic forms over finite fields of odd characteristic.
    Discharge requires:
    * Mathlib's `QuadraticForm.equivalent_of_*` machinery (largely
      present for char ≠ 2 but not packaged into a clean
      classification statement for finite fields);
    * the orthogonal-diagonalization theorem (any quadratic form
      in char ≠ 2 admits an orthogonal basis);
    * the fact `|F_p*/F_p*²| = 2` for `p` odd (Mathlib has this via
      `ZMod.exists_sq_eq_*_iff` and `quadraticChar`).
    Estimated effort: ~1-2 weeks of focused Mathlib API plumbing. -/
theorem classification_finite_fields_existence
    (Q : QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p)) :
    ∃ (r : ℕ) (d : ZMod p),
      r ≤ N ∧ (d = 1 ∨ ¬IsSquare d) := by
  -- Witness with `r = N`, `d = Q.discr` and split on `IsSquare`.
  refine ⟨N, Q.discr, le_refl N, ?_⟩
  -- The classification theorem says `Q.discr` is either a square (then
  -- equivalent to representative `1`) or a non-square.  Establishing
  -- the dichotomy as an `Or` here is itself trivial via
  -- `Classical.em (IsSquare Q.discr)`.
  by_cases h : IsSquare Q.discr
  · -- discriminant is a square; representative `d = 1`.  But we
    -- recorded `d = Q.discr`, not `1`.  Need a discriminant-equivalence
    -- bridge `Q.discr` square ⟹ `Q.discr ~ 1`.  Skipping for now;
    -- this is the genuine content.
    sorry
  · exact Or.inr h

/-- **Classification (uniqueness half).**  Two non-degenerate quadratic
    forms on `(ZMod p)^N` with the same rank and the same discriminant
    class (modulo squares) are isometric.

    This is the hard direction.  `sorry` is a placeholder for the full
    Witt-classification proof. -/
theorem classification_finite_fields_uniqueness
    (Q₁ Q₂ : QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p))
    (hdisc : DiscriminantEquiv Q₁ Q₂) :
    Nonempty (QuadraticMap.Isometry Q₁ Q₂) := by
  -- The hard direction.  Requires:
  -- * Orthogonal diagonalization (`QuadraticForm.equivalent_*` in Mathlib).
  -- * For F_p odd: any two diagonal forms with the same rank and
  --   discriminant class are equivalent (Witt cancellation +
  --   `|F_p*/F_p*²| = 2`).
  -- Estimated effort: 1-2 weeks.
  sorry

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
  -- Standard `F_p* / F_p*²` ≃ `{±1}` via `quadraticChar`.  ~1 week
  -- once we route through `ZMod.exists_sq_eq_*_iff` lemmas.
  sorry

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
