/-
# Foundation.R.Aut — GL(N, F_2) automorphism counts

Per `wen-algebra` v0.6 §5 and `v4-foundation` v0.5 §13:

    |Aut(R N)| = |GL(N, F_2)| = ∏_{k=0}^{N-1} (2^N - 2^k)

This file provides:

* `Aut N` — the type of group automorphisms of `R N` (modelled as
  bijective linear endomorphisms).
* `Aut.id` — the identity automorphism.
* `card_GL N` — the explicit cardinality formula for GL(N, F_2).
* Concrete cardinalities for N = 0, 1, 2 (the only ones where the
  product is easy to display; higher N is checkable but expensive).

Note: building a fully general `Fintype (Aut N)` instance with the
Mathlib `Equiv.Perm` infrastructure would require the universal
`AddCommGroup.Equiv` machinery; we keep this layer light and provide
the cardinality formula directly.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Hom
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 Group automorphism type -/

/-- An F_2-linear automorphism of `R N`: a linear map `R N → R N`
    together with proof of bijection.  We use `Equiv` to capture
    bijectivity. -/
structure Aut (N : ℕ) where
  /-- Underlying linear map. -/
  toLinHom : LinHom N N
  /-- Inverse linear map. -/
  invLinHom : LinHom N N
  /-- Composition with inverse is the identity. -/
  left_inv : LinHom.compose invLinHom toLinHom = LinHom.id N
  /-- Composition with the other side is the identity. -/
  right_inv : LinHom.compose toLinHom invLinHom = LinHom.id N

namespace Aut

variable {N : ℕ}

/-- The identity automorphism of `R N`.

    The proof obligation `LinHom.compose (LinHom.id N) (LinHom.id N) = LinHom.id N`
    reduces pointwise to a `xorSum_pick` application. -/
def id (N : ℕ) : Aut N where
  toLinHom := LinHom.id N
  invLinHom := LinHom.id N
  left_inv := compose_id_id N
  right_inv := compose_id_id N
where
  /-- `LinHom.compose (LinHom.id N) (LinHom.id N) = LinHom.id N`. -/
  compose_id_id (N : ℕ) :
      LinHom.compose (LinHom.id N) (LinHom.id N) = LinHom.id N := by
    funext i k
    show LinHom.xorSum (fun j => Bool.and (LinHom.id N i j) (LinHom.id N j k))
      = LinHom.id N i k
    -- Each j contributes `id N i j ∧ id N j k`, which is `(i = j) ∧ (j = k)`
    -- as a Bool conjunction.  This is `true` iff `i = j = k`.
    -- The xorSum picks out exactly the term at j = i (only one such j), and
    -- there `id N i i ∧ id N i k = true ∧ (i = k) = (i = k) = id N i k`.
    have h : (fun j => Bool.and (LinHom.id N i j) (LinHom.id N j k))
              = (fun j => if i = j then LinHom.id N i k else false) := by
      funext j
      by_cases hij : i = j
      · subst hij; simp [LinHom.id]
      · rw [LinHom.id_apply_off _ hij]
        simp [hij]
    rw [h, LinHom.xorSum_pick]

end Aut

/-! ## § 2 The order of GL(N, F_2)

We give the explicit product formula

    |GL(N, F_2)| = ∏_{k=0}^{N-1} (2^N - 2^k)

without requiring an explicit `Fintype (Aut N)` instance. -/

/-- The cardinality of GL(N, F_2) as a closed-form product.
    Per `wen-algebra` v0.6 §5.1. -/
def card_GL (N : ℕ) : ℕ :=
  (Finset.range N).prod (fun k => 2 ^ N - 2 ^ k)

/-! ## § 3 Concrete cardinalities at small N -/

@[simp] theorem card_GL_zero : card_GL 0 = 1 := by
  unfold card_GL; simp

@[simp] theorem card_GL_one : card_GL 1 = 1 := by
  unfold card_GL; decide

@[simp] theorem card_GL_two : card_GL 2 = 6 := by
  unfold card_GL; decide

@[simp] theorem card_GL_three : card_GL 3 = 168 := by
  unfold card_GL; decide

@[simp] theorem card_GL_four : card_GL 4 = 20160 := by
  unfold card_GL; decide

end R

end SSBX.Foundation.R
