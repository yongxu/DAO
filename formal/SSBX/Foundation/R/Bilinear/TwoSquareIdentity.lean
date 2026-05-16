/-
# Foundation.R.Bilinear.TwoSquareIdentity — 2-square identity helpers for
  the discriminant classification on `R N (ZMod p)`, odd prime `p`

This file establishes the **binary 2-square existence** on `ZMod p`
(odd prime `p`):

  > For `a, b ∈ (ZMod p)*` (with `p` odd prime), the equation
  > `α² + a·b·γ² = a` always has a solution `(α, γ) ∈ (ZMod p)²`,
  > as a consequence of `Polynomial.exists_root_sum_quadratic`
  > (≈ pigeonhole on the (p+1)/2 values of `X²` over `F_p`).

This is the algebraic substrate underneath the binary diagonal
redistribution `⟨a, b⟩ ~ ⟨1, a·b⟩` used in the discriminant
classification of quadratic forms over `F_p` (`Bilinear/DiscriminantCharNeq2.lean`
§ 6).

The **explicit 2×2 isometry matrix** witnessing the redistribution is

       M = [[α, -a·b·γ/a],
            [γ,      α/a]]

which has determinant `(α² + a·b·γ²)/a = a/a = 1` and satisfies the
Gram relation `Mᵀ · diag(1, a·b) · M = diag(a, b)` precisely because
of the identity `α² + a·b·γ² = a`.  The full `IsometryEquiv` wiring
between `weightedSumSquares (ZMod p) ![a, b]` and
`weightedSumSquares (ZMod p) ![1, a*b]` is intentionally **not**
packaged here — see `DiscriminantCharNeq2.lean` for the consumer.

## Provides

* `R.binary_2sq_exists_alpha_gamma {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ α γ : ZMod p, α^2 + a*b * γ^2 = a` — the 2-square existence
  (Chevalley–Warning, binary version, via Mathlib's
  `Polynomial.exists_root_sum_quadratic`).

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` G11 (T5-B parametric over k,
  char ≠ 2 branch).
* `wen-algebra` v0.6 § 4 (char-2 Arf classification; this file feeds its
  char ≠ 2 counterpart in `Bilinear/DiscriminantCharNeq2.lean`).
-/

import SSBX.Foundation.R.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Defs

namespace SSBX.Foundation.R

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace R

open Polynomial FiniteField

variable {p : ℕ} [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-! ## § 1 Cardinality of `ZMod p` is odd

For `p` an odd prime, `Fintype.card (ZMod p) = p` is odd, satisfying the
hypothesis of `Polynomial.exists_root_sum_quadratic`. -/

private lemma card_zmod_odd : Fintype.card (ZMod p) % 2 = 1 := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  rw [ZMod.card]
  rcases hp.out.eq_two_or_odd with h2 | hodd
  · exact absurd h2 hp2.out
  · exact hodd

/-! ## § 2 The binary 2-square existence

For `a, b ∈ ZMod p` both non-zero, there exist `α, γ ∈ ZMod p` with
`α² + a·b·γ² = a`.

**Proof.** Apply `FiniteField.exists_root_sum_quadratic` to the two
quadratic polynomials `f = X² - C a` and `g = C (a*b) * X²`.  Both have
degree exactly 2 (`a ≠ 0`, `a*b ≠ 0`), and `|ZMod p|` is odd.  This
yields `α, γ ∈ ZMod p` with `f.eval α + g.eval γ = 0`, i.e.
`α² - a + a*b * γ² = 0`, rearranged to `α² + a*b·γ² = a`. -/
theorem binary_2sq_exists_alpha_gamma {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ α γ : ZMod p, α ^ 2 + a * b * γ ^ 2 = a := by
  -- Define the two quadratic polynomials.
  set f : (ZMod p)[X] := X ^ 2 - C a with hf_def
  set g : (ZMod p)[X] := C (a * b) * X ^ 2 with hg_def
  have hab_ne : a * b ≠ 0 := mul_ne_zero ha hb
  -- `degree f = 2`: `X^n - C a` has degree `n` for any `a` (with `n ≥ 1`).
  have hf : degree f = 2 := by
    rw [hf_def]
    exact degree_X_pow_sub_C (n := 2) (by decide) a
  -- `degree g = 2`: `C c * X^n` has degree `n` for `c ≠ 0`.
  have hg : degree g = 2 := by
    rw [hg_def]
    exact degree_C_mul_X_pow 2 hab_ne
  -- Apply Mathlib's `exists_root_sum_quadratic`.
  obtain ⟨α, γ, hαγ⟩ := exists_root_sum_quadratic (R := ZMod p)
    (f := f) (g := g) hf hg card_zmod_odd
  refine ⟨α, γ, ?_⟩
  -- `f.eval α = α^2 - a` and `g.eval γ = a*b * γ^2`.
  have hf_eval : f.eval α = α ^ 2 - a := by
    rw [hf_def]; simp
  have hg_eval : g.eval γ = a * b * γ ^ 2 := by
    rw [hg_def]; simp
  rw [hf_eval, hg_eval] at hαγ
  -- `α^2 - a + a*b*γ^2 = 0` ↔ `α^2 + a*b*γ^2 = a`.
  linear_combination hαγ

/-! ## § 3 The binary redistribution quadratic identity

Given `α, γ ∈ ZMod p` with `α² + a·b·γ² = a` (and `a ≠ 0`), the
expression

       1·(α x − (a·b·γ/a) y)² + a·b·(γ x + (α/a) y)²

equals `a·x² + b·y²` for all `x, y ∈ ZMod p`.

**Proof.** Direct polynomial identity, modulo the hypothesis
`α² + a·b·γ² = a`.  Clear the `1/a` denominators via `field_simp`,
then both sides reduce to the same polynomial in `α, γ, x, y, a, b`
(using the hypothesis to identify `α² + a·b·γ²` with `a`). -/
theorem binary_redistribute_quadratic_identity
    {a b : ZMod p} (ha : a ≠ 0)
    {α γ : ZMod p} (hαγ : α ^ 2 + a * b * γ ^ 2 = a)
    (x y : ZMod p) :
    1 * (α * x - (a * b * γ / a) * y) ^ 2
      + a * b * (γ * x + (α / a) * y) ^ 2
    = a * x ^ 2 + b * y ^ 2 := by
  -- Multiply through by `a²`.  Both sides become polynomial
  -- identities modulo `α² + a*b*γ² = a`.
  -- We use `field_simp` + `linear_combination` with hypothesis hαγ.
  -- Rewrite `a * b * γ / a = b * γ` (uses `a ≠ 0`).
  have hsimp : a * b * γ / a = b * γ := by
    field_simp
  rw [hsimp]
  -- After this rewrite the LHS becomes `(α*x - b*γ*y)² + a*b*(γ*x + (α/a)*y)²`.
  -- Multiply through to clear `α/a` via `field_simp` again; the residual is
  -- then `a · x² · (α² + a·b·γ² - a) = 0` mod ring, hence
  -- `linear_combination (a * x²) * hαγ`.
  field_simp
  linear_combination (a * x ^ 2 + b * y ^ 2) * hαγ

end R

end SSBX.Foundation.R
