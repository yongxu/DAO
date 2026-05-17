/-
# Foundation.R.Bilinear.NaryWittInduction — `Fin N` lift of the binary
  redistribution `⟨a, b⟩ ≅ ⟨1, a·b⟩` over `ZMod p` (odd prime `p`)

This file lifts the **binary** isometry redistribution

    ⟨a, b⟩  ≅  ⟨1, a·b⟩    (on `Fin 2 → ZMod p`)

from `Foundation/R/Bilinear/BinaryIsometry.lean` to **arbitrary
arity** `Fin N`.  The mathematical content (Witt cancellation, char ≠ 2,
finite-field flavour):

  > For any weights `w : Fin N → ZMod p` with `w i ≠ 0` for all `i`,
  > the diagonal quadratic form `Q_w(x) := Σ_i w_i · x_i²` is
  > isometric to the *canonical form*
  >     ⟨1, 1, …, 1, ∏_i w_i⟩
  > (all weights equal to `1` except the last, which carries the full
  > discriminant `d = ∏ w_i`).

The proof is by induction on `N`, repeatedly applying the binary
redistribution to the leading pair `(w₀, w₁) ↦ (1, w₀·w₁)` and then
shifting the accumulated product down the tuple.

## Provides

* `R.diag_n_quadratic_form (w : Fin N → ZMod p)` — the diagonal
  quadratic form `Σ_i w_i · x_i²`, packaged via
  `QuadraticMap.weightedSumSquares`.
* `R.pairRedistributeFwd` / `Inv` / `LinearEquiv` — the `LinearEquiv`
  on `Fin (N+2) → ZMod p` that applies the binary 2×2 redistribution
  to positions `0, 1` and the identity on positions `2, …, N+1`.
* `R.redistribute_pair_isometry` — the step lemma: an `IsometryEquiv`
  between `diag_n_quadratic_form (Fin.cons a (Fin.cons b w))` and
  `diag_n_quadratic_form (Fin.cons 1 (Fin.cons (a·b) w))`.
* `R.redistribute_to_canonical` — main theorem: existence of the
  canonical reduction via Nat-induction on the tuple length.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` G11 (T5-B parametric over k).
* `Foundation/R/Bilinear/DiscriminantCharNeq2.lean` § 6
  (`classification_finite_fields_uniqueness` — the
  `Fin N → canonical` reduction lands here, completing the chain).
* `wen-algebra` v0.6 § 4 (char-2 Arf classification; this is the
  char ≠ 2 parallel).
-/

import SSBX.Foundation.R.Bilinear.BinaryIsometry
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Basic

namespace SSBX.Foundation.R

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace R

variable {p : ℕ} [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-! ## § 1 The diagonal quadratic form on `Fin N → ZMod p` -/

/-- The diagonal quadratic form with weights `w : Fin N → ZMod p`:

      `Q_w(x) := Σ_i w_i · x_i²`.

  Packaged directly via Mathlib's `QuadraticMap.weightedSumSquares`. -/
noncomputable def diag_n_quadratic_form {N : ℕ} (w : Fin N → ZMod p) :
    QuadraticMap (ZMod p) (Fin N → ZMod p) (ZMod p) :=
  QuadraticMap.weightedSumSquares (ZMod p) w

@[simp] lemma diag_n_quadratic_form_apply {N : ℕ} (w : Fin N → ZMod p)
    (v : Fin N → ZMod p) :
    diag_n_quadratic_form w v = ∑ i, w i * (v i * v i) := by
  unfold diag_n_quadratic_form
  rw [QuadraticMap.weightedSumSquares_apply]
  simp [smul_eq_mul]

/-! ## § 2 The pair-redistribute `LinearEquiv` on `Fin (N+2) → ZMod p`

  The map applies the binary 2×2 redistribution (from
  `BinaryIsometry.lean`) to positions 0, 1, and is the identity on
  positions `2..N+1`.  Concretely:

      (x₀, x₁, x₂, ..., x_{N+1}) ↦ (α·x₀ - b·γ·x₁, γ·x₀ + (α/a)·x₁, x₂, ..., x_{N+1})

  with hypothesis `α² + a·b·γ² = a` carried through.  -/

/-- Forward map of the pair-redistribution: `Fin.cons` of the binary
    redistribution head/middle, followed by the tail unchanged. -/
noncomputable def pairRedistributeFwd {N : ℕ} (a b α γ : ZMod p)
    (v : Fin (N+2) → ZMod p) : Fin (N+2) → ZMod p :=
  Fin.cons (α * v 0 - b * γ * v 1)
    (Fin.cons (γ * v 0 + (α / a) * v 1) (fun i : Fin N => v i.succ.succ))

/-- Inverse map of the pair-redistribution. -/
noncomputable def pairRedistributeInv {N : ℕ} (a b α γ : ZMod p)
    (v : Fin (N+2) → ZMod p) : Fin (N+2) → ZMod p :=
  Fin.cons ((α / a) * v 0 + b * γ * v 1)
    (Fin.cons (-γ * v 0 + α * v 1) (fun i : Fin N => v i.succ.succ))

@[simp] lemma pairRedistributeFwd_zero {N : ℕ} (a b α γ : ZMod p) (v : Fin (N+2) → ZMod p) :
    pairRedistributeFwd a b α γ v 0 = α * v 0 - b * γ * v 1 := by
  simp [pairRedistributeFwd]

@[simp] lemma pairRedistributeFwd_one {N : ℕ} (a b α γ : ZMod p) (v : Fin (N+2) → ZMod p) :
    pairRedistributeFwd a b α γ v 1 = γ * v 0 + (α / a) * v 1 := by
  show pairRedistributeFwd a b α γ v (Fin.succ (0 : Fin (N+1))) = _
  simp [pairRedistributeFwd]

@[simp] lemma pairRedistributeFwd_succ_succ {N : ℕ} (a b α γ : ZMod p)
    (v : Fin (N+2) → ZMod p) (i : Fin N) :
    pairRedistributeFwd a b α γ v i.succ.succ = v i.succ.succ := by
  simp [pairRedistributeFwd]

@[simp] lemma pairRedistributeInv_zero {N : ℕ} (a b α γ : ZMod p) (v : Fin (N+2) → ZMod p) :
    pairRedistributeInv a b α γ v 0 = (α / a) * v 0 + b * γ * v 1 := by
  simp [pairRedistributeInv]

@[simp] lemma pairRedistributeInv_one {N : ℕ} (a b α γ : ZMod p) (v : Fin (N+2) → ZMod p) :
    pairRedistributeInv a b α γ v 1 = -γ * v 0 + α * v 1 := by
  show pairRedistributeInv a b α γ v (Fin.succ (0 : Fin (N+1))) = _
  simp [pairRedistributeInv]

@[simp] lemma pairRedistributeInv_succ_succ {N : ℕ} (a b α γ : ZMod p)
    (v : Fin (N+2) → ZMod p) (i : Fin N) :
    pairRedistributeInv a b α γ v i.succ.succ = v i.succ.succ := by
  simp [pairRedistributeInv]

/-- The pair-redistribution `LinearEquiv` on `Fin (N+2) → ZMod p`.
    The first two coordinates undergo the binary redistribution; the
    remaining `N` coordinates are unchanged. -/
noncomputable def pairRedistributeLinearEquiv {N : ℕ} (a b α γ : ZMod p)
    (ha : a ≠ 0) (hαγ : α ^ 2 + a * b * γ ^ 2 = a) :
    (Fin (N+2) → ZMod p) ≃ₗ[ZMod p] (Fin (N+2) → ZMod p) where
  toFun  := pairRedistributeFwd a b α γ
  invFun := pairRedistributeInv a b α γ
  map_add' u v := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · -- i = 0
      simp only [pairRedistributeFwd_zero, Pi.add_apply]; ring
    · -- i = Fin.succ 0 = 1
      change pairRedistributeFwd a b α γ (u + v) 1
        = pairRedistributeFwd a b α γ u 1 + pairRedistributeFwd a b α γ v 1
      simp only [pairRedistributeFwd_one, Pi.add_apply]; ring
    · -- i = k.succ.succ
      simp only [pairRedistributeFwd_succ_succ, Pi.add_apply]
  map_smul' r v := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp only [pairRedistributeFwd_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    · change pairRedistributeFwd a b α γ (r • v) 1 = (RingHom.id _) r * pairRedistributeFwd a b α γ v 1
      simp only [pairRedistributeFwd_one, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    · simp only [pairRedistributeFwd_succ_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · -- i = 0
      change pairRedistributeInv a b α γ (pairRedistributeFwd a b α γ v) 0 = v 0
      rw [pairRedistributeInv_zero, pairRedistributeFwd_zero, pairRedistributeFwd_one]
      have key : (α / a) * (α * v 0 - b * γ * v 1)
                  + b * γ * (γ * v 0 + (α / a) * v 1)
                = ((α ^ 2 + a * b * γ ^ 2) / a) * v 0 := by
        field_simp; ring
      rw [key, hαγ, div_self ha, one_mul]
    · -- i = Fin.succ 0 = 1
      change pairRedistributeInv a b α γ (pairRedistributeFwd a b α γ v) 1 = v 1
      rw [pairRedistributeInv_one, pairRedistributeFwd_zero, pairRedistributeFwd_one]
      have key : -γ * (α * v 0 - b * γ * v 1)
                  + α * (γ * v 0 + (α / a) * v 1)
                = ((α ^ 2 + a * b * γ ^ 2) / a) * v 1 := by
        field_simp; ring
      rw [key, hαγ, div_self ha, one_mul]
    · -- i = k.succ.succ
      rw [pairRedistributeInv_succ_succ, pairRedistributeFwd_succ_succ]
  right_inv v := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · -- i = 0
      change pairRedistributeFwd a b α γ (pairRedistributeInv a b α γ v) 0 = v 0
      rw [pairRedistributeFwd_zero, pairRedistributeInv_zero, pairRedistributeInv_one]
      have key : α * ((α / a) * v 0 + b * γ * v 1)
                  - b * γ * (-γ * v 0 + α * v 1)
                = ((α ^ 2 + a * b * γ ^ 2) / a) * v 0 := by
        field_simp; ring
      rw [key, hαγ, div_self ha, one_mul]
    · -- i = 1
      change pairRedistributeFwd a b α γ (pairRedistributeInv a b α γ v) 1 = v 1
      rw [pairRedistributeFwd_one, pairRedistributeInv_zero, pairRedistributeInv_one]
      have key : γ * ((α / a) * v 0 + b * γ * v 1)
                  + (α / a) * (-γ * v 0 + α * v 1)
                = ((α ^ 2 + a * b * γ ^ 2) / a) * v 1 := by
        field_simp; ring
      rw [key, hαγ, div_self ha, one_mul]
    · -- i = k.succ.succ
      rw [pairRedistributeFwd_succ_succ, pairRedistributeInv_succ_succ]

/-! ## § 3 The step lemma -/

/-- **Step lemma.**  Given non-zero `a, b` and an arbitrary remainder
    vector `w : Fin N → ZMod p`, the diagonal form with weights
    `Fin.cons a (Fin.cons b w)` is isometric to the diagonal form
    with weights `Fin.cons 1 (Fin.cons (a·b) w)`.

    Proof: use `pairRedistributeLinearEquiv` for the `LinearEquiv`
    backbone and verify `map_app'` by splitting `Fin.sum_univ_succ`
    twice to peel off positions 0 and 1, applying the
    `binary_redistribute_quadratic_identity`, and observing that the
    tail terms are identical (since the redistribution is the identity
    on positions 2..N+1). -/
theorem redistribute_pair_isometry {N : ℕ} (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) (w : Fin N → ZMod p) :
    Nonempty (QuadraticMap.IsometryEquiv
      (diag_n_quadratic_form (Fin.cons a (Fin.cons b w)))
      (diag_n_quadratic_form (Fin.cons 1 (Fin.cons (a*b) w)))) := by
  obtain ⟨α, γ, hαγ⟩ := binary_2sq_exists_alpha_gamma (a := a) (b := b) ha hb
  refine ⟨{ pairRedistributeLinearEquiv (N := N) a b α γ ha hαγ with map_app' := ?_ }⟩
  intro v
  show diag_n_quadratic_form (Fin.cons 1 (Fin.cons (a*b) w))
        (pairRedistributeFwd a b α γ v)
      = diag_n_quadratic_form (Fin.cons a (Fin.cons b w)) v
  rw [diag_n_quadratic_form_apply, diag_n_quadratic_form_apply]
  -- Peel off positions 0 and 1 from both sides using `Fin.sum_univ_succ` twice.
  rw [Fin.sum_univ_succ (n := N+1), Fin.sum_univ_succ (n := N)]
  conv_rhs => rw [Fin.sum_univ_succ (n := N+1), Fin.sum_univ_succ (n := N)]
  -- Normalize `Fin.succ 0 : Fin (N+2)` to `1 : Fin (N+2)`.
  have hsucc01 : (Fin.succ (0 : Fin (N+1)) : Fin (N+2)) = (1 : Fin (N+2)) := rfl
  simp only [hsucc01]
  -- Evaluate the cons weights at positions 0, 1, and tail.
  -- We need helpers for `Fin.cons _ _ (1 : Fin (N+2))` since `Fin.cons_succ` requires literal `.succ`.
  have hcons1 : ∀ (x y : ZMod p) (z : Fin N → ZMod p),
      (Fin.cons x (Fin.cons y z) : Fin (N+2) → ZMod p) 1 = y := fun x y z => by
    show (Fin.cons x (Fin.cons y z) : Fin (N+2) → ZMod p) (Fin.succ 0) = y
    rw [Fin.cons_succ]; rfl
  simp only [Fin.cons_zero, Fin.cons_succ, hcons1, pairRedistributeFwd_zero,
    pairRedistributeFwd_one, pairRedistributeFwd_succ_succ]
  -- Goal now:
  -- 1 * ((α*v0 - b*γ*v1) * (α*v0 - b*γ*v1))
  --   + ((a*b) * ((γ*v0 + (α/a)*v1) * (γ*v0 + (α/a)*v1))
  --       + ∑ w i * (v i.succ.succ)²)
  -- = a * (v 0 * v 0) + (b * (v 1 * v 1) + ∑ w i * (v i.succ.succ)²)
  -- The tail sums match; reduce to the binary identity.
  have hbin := binary_redistribute_quadratic_identity (a := a) (b := b)
    ha hαγ (v 0) (v 1)
  -- Simplify `a*b*γ/a = b*γ` in hbin.
  have hsimp : a * b * γ / a = b * γ := by field_simp
  rw [hsimp] at hbin
  -- hbin: 1 * (α*v0 - b*γ*v1)^2 + a*b * (γ*v0 + (α/a)*v1)^2 = a * v0^2 + b * v1^2
  -- Convert (v 0 * v 0) to (v 0)^2 etc. and apply hbin.
  linear_combination hbin

/-! ## § 4 Lifting isometries across `Fin.cons`

  Given an isometry between `weightedSumSquares w` and
  `weightedSumSquares w'` on `Fin n → ZMod p`, we obtain an isometry
  between `weightedSumSquares (Fin.cons c w)` and
  `weightedSumSquares (Fin.cons c w')` on `Fin (n+1) → ZMod p` —
  by acting as identity on coord 0 and the original isometry on the
  tail.

  This is used in the canonical-reduction induction to "preserve the
  already-canonicalized leading coordinate" while operating on the
  remaining tail. -/

/-- The cons-lift forward map: identity on coord 0, `f` on coords 1..n. -/
noncomputable def consLiftFwd {n : ℕ} (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))
    (v : Fin (n+1) → ZMod p) : Fin (n+1) → ZMod p :=
  Fin.cons (v 0) (fun i : Fin n => f (fun j => v j.succ) i)

@[simp] lemma consLiftFwd_zero {n : ℕ} (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))
    (v : Fin (n+1) → ZMod p) :
    consLiftFwd f v 0 = v 0 := by
  simp [consLiftFwd]

@[simp] lemma consLiftFwd_succ {n : ℕ} (f : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p))
    (v : Fin (n+1) → ZMod p) (i : Fin n) :
    consLiftFwd f v i.succ = f (fun j => v j.succ) i := by
  simp [consLiftFwd]

/-- The cons-lift `LinearEquiv`: identity on coord 0, `f` on coords 1..n. -/
noncomputable def consLiftLinearEquiv {n : ℕ}
    (f : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :
    (Fin (n+1) → ZMod p) ≃ₗ[ZMod p] (Fin (n+1) → ZMod p) where
  toFun  := consLiftFwd f.toLinearMap
  invFun := consLiftFwd f.symm.toLinearMap
  map_add' u v := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [consLiftFwd_zero]
    · rw [Pi.add_apply, consLiftFwd_succ, consLiftFwd_succ, consLiftFwd_succ]
      have hadd : (fun j : Fin n => (u + v) j.succ)
                 = (fun j : Fin n => u j.succ) + (fun j : Fin n => v j.succ) := by
        funext j; rfl
      rw [hadd, LinearMap.map_add]
      rfl
  map_smul' r v := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [consLiftFwd_zero]
    · rw [Pi.smul_apply, consLiftFwd_succ, consLiftFwd_succ]
      have hsmul : (fun j : Fin n => (r • v) j.succ) = r • (fun j : Fin n => v j.succ) := by
        funext j; rfl
      rw [hsmul, LinearMap.map_smul]
      rfl
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [consLiftFwd_zero]
    · rw [consLiftFwd_succ]
      have htail : (fun j : Fin n => consLiftFwd f.toLinearMap v j.succ)
                  = f.toLinearMap (fun j : Fin n => v j.succ) := by
        funext j; rw [consLiftFwd_succ]
      rw [htail]
      have : f.symm.toLinearMap (f.toLinearMap (fun j : Fin n => v j.succ))
              = (fun j : Fin n => v j.succ) :=
        f.left_inv _
      rw [this]
  right_inv v := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [consLiftFwd_zero]
    · rw [consLiftFwd_succ]
      have htail : (fun j : Fin n => consLiftFwd f.symm.toLinearMap v j.succ)
                  = f.symm.toLinearMap (fun j : Fin n => v j.succ) := by
        funext j; rw [consLiftFwd_succ]
      rw [htail]
      have : f.toLinearMap (f.symm.toLinearMap (fun j : Fin n => v j.succ))
              = (fun j : Fin n => v j.succ) :=
        f.right_inv _
      rw [this]

/-- **Cons-lift isometry.**  Given an `IsometryEquiv` between
    `weightedSumSquares w` and `weightedSumSquares w'`, the cons-lift
    gives an `IsometryEquiv` between
    `weightedSumSquares (Fin.cons c w)` and
    `weightedSumSquares (Fin.cons c w')`. -/
noncomputable def consLiftIsometry {n : ℕ} (c : ZMod p) {w w' : Fin n → ZMod p}
    (e : QuadraticMap.IsometryEquiv
            (diag_n_quadratic_form w) (diag_n_quadratic_form w')) :
    QuadraticMap.IsometryEquiv
      (diag_n_quadratic_form (Fin.cons c w))
      (diag_n_quadratic_form (Fin.cons c w')) where
  __ := consLiftLinearEquiv (e.toLinearEquiv)
  map_app' := by
    intro v
    show diag_n_quadratic_form (Fin.cons c w')
            (consLiftFwd e.toLinearEquiv.toLinearMap v)
          = diag_n_quadratic_form (Fin.cons c w) v
    rw [diag_n_quadratic_form_apply, diag_n_quadratic_form_apply]
    -- Peel off coord 0 from both sums.
    rw [Fin.sum_univ_succ (n := n), Fin.sum_univ_succ (n := n)]
    -- Coord 0 contributions are equal (Fin.cons_zero + consLiftFwd_zero).
    rw [show (Fin.cons c w : Fin (n+1) → ZMod p) 0 = c from rfl,
        show (Fin.cons c w' : Fin (n+1) → ZMod p) 0 = c from rfl,
        consLiftFwd_zero]
    -- Tail sums: ∑ (cons c w'.succ) * (consLiftFwd f v).succ²
    --          = ∑ (cons c w.succ) * v.succ²
    -- After Fin.cons_succ: cons c w (i.succ) = w i.
    -- After consLiftFwd_succ: consLiftFwd f v i.succ = f (v.succ) i.
    simp only [Fin.cons_succ, consLiftFwd_succ]
    -- Goal: c * (v 0 * v 0) + ∑ w' i * (f (v.succ) i * f (v.succ) i)
    --     = c * (v 0 * v 0) + ∑ w i * (v.succ i * v.succ i)
    -- The c * (v 0 * v 0) terms match. The tails are related via e.map_app
    -- on the tail `(v ∘ Fin.succ)`.
    have h := e.map_app (fun j : Fin n => v j.succ)
    rw [diag_n_quadratic_form_apply, diag_n_quadratic_form_apply] at h
    -- h : ∑ w' i * (e.toLinearEquiv (v ∘ Fin.succ) i * e.toLinearEquiv (v ∘ Fin.succ) i)
    --     = ∑ w i * (v.succ i * v.succ i)
    linear_combination h

/-! ## § 5 Canonical reduction by induction on `Fin (N+1)`

  Given non-zero weights `w : Fin (N+1) → ZMod p`, we prove by
  induction on `N` that
      `diag_n_quadratic_form w ≅ diag_n_quadratic_form ![w 0 * w 1 * ... * w N]`
  for `N = 0`, and in general the canonical form
  `Fin.cons 1 (Fin.cons 1 (... (Fin.cons (∏ w) 0)))` of suitable length.

  We provide a cleaner formulation: the canonical form has length `N+1`
  and is `1`'s except for the **last** coordinate which carries the
  full product. -/

/-- The canonical weights `[1, 1, ..., 1, d]` of length `N+1` defined
    via `Fin.snoc`. -/
noncomputable def canonicalWeights (N : ℕ) (d : ZMod p) : Fin (N+1) → ZMod p :=
  Fin.snoc (fun _ : Fin N => (1 : ZMod p)) d

@[simp] lemma canonicalWeights_castSucc (N : ℕ) (d : ZMod p) (i : Fin N) :
    canonicalWeights N d i.castSucc = 1 := by
  unfold canonicalWeights
  rw [Fin.snoc_castSucc]

@[simp] lemma canonicalWeights_last (N : ℕ) (d : ZMod p) :
    canonicalWeights N d (Fin.last N) = d := by
  unfold canonicalWeights
  rw [Fin.snoc_last]

/-- Equality between `diag_n_quadratic_form` on equal weights. -/
private noncomputable def diag_n_equal_isom {N : ℕ} {w w' : Fin N → ZMod p}
    (h : w = w') : QuadraticMap.IsometryEquiv
      (diag_n_quadratic_form w) (diag_n_quadratic_form w') :=
  { (LinearEquiv.refl (ZMod p) (Fin N → ZMod p)) with
    map_app' := by intro v; show diag_n_quadratic_form w' v = diag_n_quadratic_form w v
                   rw [h] }

/-- Equality lemma: `Fin.cons 1 (Fin.snoc (fun _ => 1) d) = Fin.snoc (fun _ => 1) d`
    when both are interpreted at length `(M+1)+1` vs `(M+1)+1`. -/
private lemma cons_one_snoc_eq_snoc (M : ℕ) (d : ZMod p) :
    @Fin.cons (M+1) (fun _ => ZMod p) (1 : ZMod p)
      (@Fin.snoc M (fun _ => ZMod p) (fun _ : Fin M => (1 : ZMod p)) d)
    = @Fin.snoc (M+1) (fun _ => ZMod p) (fun _ : Fin (M+1) => (1 : ZMod p)) d := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    -- LHS at Fin.last (M+1) = ?
    -- (M+1+1).Fin.last = Fin.succ (Fin.last M) in our Fin context
    have hlast_eq : (Fin.last (M+1) : Fin (M+2)) = Fin.succ (Fin.last M) := rfl
    rw [hlast_eq]
    -- Now LHS = Fin.cons 1 (Fin.snoc ...) (Fin.succ (Fin.last M))
    --        = Fin.snoc (fun _ => 1) d (Fin.last M)  [by cons_succ]
    --        = d                                       [by snoc_last]
    -- RHS = Fin.snoc (fun _ => 1) d (Fin.last (M+1))
    --    = d                                          [by snoc_last]
    -- For LHS evaluation:
    rw [show @Fin.cons (M+1) (fun _ => ZMod p) (1 : ZMod p)
            (@Fin.snoc M (fun _ => ZMod p) (fun _ : Fin M => (1 : ZMod p)) d)
            (Fin.succ (Fin.last M))
          = @Fin.snoc M (fun _ => ZMod p) (fun _ : Fin M => (1 : ZMod p)) d (Fin.last M)
        from rfl]
    rw [Fin.snoc_last]
    rw [show @Fin.snoc (M+1) (fun _ => ZMod p) (fun _ : Fin (M+1) => (1 : ZMod p)) d
              (Fin.succ (Fin.last M))
            = d from by
        have : (Fin.succ (Fin.last M) : Fin (M+2)) = Fin.last (M+1) := rfl
        rw [this, Fin.snoc_last]]
  | cast i =>
    -- i.castSucc : Fin (M+2)
    induction i using Fin.cases with
    | zero =>
      -- (0 : Fin (M+1)).castSucc = (0 : Fin (M+2))
      have hzero : ((0 : Fin (M+1)).castSucc : Fin (M+2)) = (0 : Fin (M+2)) := rfl
      rw [hzero]
      -- LHS: Fin.cons 1 (...) 0 = 1.  RHS: Fin.snoc (fun _ => 1) d 0 = (fun _ => 1) (0 : Fin (M+1)).castSucc = 1.
      rfl
    | succ k =>
      -- (Fin.succ k).castSucc = Fin.succ (k.castSucc) in Fin (M+2)
      have hsucc : ((Fin.succ k).castSucc : Fin (M+2)) = Fin.succ k.castSucc := rfl
      rw [hsucc]
      rw [show @Fin.cons (M+1) (fun _ => ZMod p) (1 : ZMod p)
            (@Fin.snoc M (fun _ => ZMod p) (fun _ : Fin M => (1 : ZMod p)) d)
            (Fin.succ k.castSucc)
          = @Fin.snoc M (fun _ => ZMod p) (fun _ : Fin M => (1 : ZMod p)) d k.castSucc
        from rfl]
      rw [Fin.snoc_castSucc]
      -- RHS: Fin.snoc (fun _ => 1) d k.castSucc.succ
      -- = Fin.snoc (fun _ => 1) d (Fin.succ k).castSucc  [since k.castSucc.succ = (Fin.succ k).castSucc]
      -- = (fun _ => 1) (Fin.succ k) = 1   [by snoc_castSucc]
      rw [show (k.castSucc.succ : Fin (M+2)) = (Fin.succ k).castSucc from rfl]
      rw [Fin.snoc_castSucc]

/-- **Canonical reduction theorem.**  For any non-zero weight vector
    `w : Fin (N+1) → ZMod p` (i.e. all components non-zero), the
    diagonal form is isometric to a canonical form with all-`1`
    leading coordinates and a non-zero `d` at the final coordinate.

    Proof: by induction on the length, repeatedly applying
    `redistribute_pair_isometry` to combine the leading pair, then
    `consLiftIsometry` to recurse on the tail. -/
theorem reduce_to_one_then_d_form : ∀ {N : ℕ}
    (w : Fin (N+1) → ZMod p), (∀ i, w i ≠ 0) →
    ∃ d : ZMod p, d ≠ 0 ∧ Nonempty (QuadraticMap.IsometryEquiv
      (diag_n_quadratic_form w)
      (diag_n_quadratic_form
        (Fin.snoc (fun _ : Fin N => (1 : ZMod p)) d))) := by
  intro N
  induction N with
  | zero =>
      intro w hw
      refine ⟨w 0, hw 0, ?_⟩
      -- w : Fin 1 → ZMod p. Canonical form: Fin.snoc (fun _ : Fin 0 => 1) (w 0) of type Fin 1 → ZMod p.
      -- They're equal as functions.
      have heq : w = @Fin.snoc 0 (fun _ => ZMod p) (fun _ : Fin 0 => (1 : ZMod p)) (w 0) := by
        funext i
        haveI : Subsingleton (Fin 1) := Fin.subsingleton_one
        have : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst this
        simp [Fin.snoc]
      exact ⟨diag_n_equal_isom heq⟩
  | succ M ih =>
      intro w hw
      -- w : Fin (M+2) → ZMod p
      let wTail : Fin M → ZMod p := fun i => w i.succ.succ
      -- Build the cons-cons form explicitly with non-dependent typing.
      let wConsConsTail : Fin (M+2) → ZMod p :=
        @Fin.cons (M+1) (fun _ => ZMod p) (w 0)
          (@Fin.cons M (fun _ => ZMod p) (w 1) wTail)
      have hcons_eq : w = wConsConsTail := by
        funext i
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
        · rfl
        · -- i = Fin.succ 0 in Fin (M+2) (= position 1)
          rfl
        · rfl
      -- The reduced form after step.
      let wConsConsReduced : Fin (M+2) → ZMod p :=
        @Fin.cons (M+1) (fun _ => ZMod p) (1 : ZMod p)
          (@Fin.cons M (fun _ => ZMod p) (w 0 * w 1) wTail)
      -- Step lemma: isometry from wConsConsTail to wConsConsReduced.
      have hstep : Nonempty (QuadraticMap.IsometryEquiv
          (diag_n_quadratic_form wConsConsTail)
          (diag_n_quadratic_form wConsConsReduced)) :=
        redistribute_pair_isometry (w 0) (w 1) (hw 0) (hw 1) wTail
      -- The remaining "tail" after the head-1: Fin.cons (w 0 * w 1) wTail : Fin (M+1) → ZMod p.
      let wRest : Fin (M+1) → ZMod p :=
        @Fin.cons M (fun _ => ZMod p) (w 0 * w 1) wTail
      have hwRest_ne : ∀ i, wRest i ≠ 0 := by
        intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · -- wRest 0 = (Fin.cons (w 0 * w 1) wTail) 0 = w 0 * w 1
          show (w 0 * w 1 : ZMod p) ≠ 0
          exact mul_ne_zero (hw 0) (hw 1)
        · -- wRest k.succ = wTail k = w k.succ.succ
          show wTail k ≠ 0
          exact hw k.succ.succ
      obtain ⟨d, hd_ne, hRest⟩ := ih wRest hwRest_ne
      refine ⟨d, hd_ne, ?_⟩
      -- wConsConsReduced = Fin.cons 1 wRest (definitionally).
      have hReducedEq : wConsConsReduced
                      = @Fin.cons (M+1) (fun _ => ZMod p) (1 : ZMod p) wRest := rfl
      -- Apply consLiftIsometry with c = 1 to the IH isometry.
      let canonM : Fin (M+1) → ZMod p :=
        @Fin.snoc M (fun _ => ZMod p) (fun _ : Fin M => (1 : ZMod p)) d
      let consOneCanonM : Fin (M+2) → ZMod p :=
        @Fin.cons (M+1) (fun _ => ZMod p) (1 : ZMod p) canonM
      have hLift : Nonempty (QuadraticMap.IsometryEquiv
          (diag_n_quadratic_form (@Fin.cons (M+1) (fun _ => ZMod p) (1 : ZMod p) wRest))
          (diag_n_quadratic_form consOneCanonM)) :=
        hRest.map (consLiftIsometry (1 : ZMod p))
      -- The leading-1 cons of canonical is again canonical (one longer).
      have hConsSnocEq : consOneCanonM
            = @Fin.snoc (M+1) (fun _ => ZMod p) (fun _ : Fin (M+1) => (1 : ZMod p)) d :=
        cons_one_snoc_eq_snoc M d
      -- Build the final isometry by chaining.
      have eEq1 := diag_n_equal_isom (w := w) (w' := wConsConsTail) hcons_eq
      have eEq2 := diag_n_equal_isom (w := wConsConsReduced)
                    (w' := @Fin.cons (M+1) (fun _ => ZMod p) (1 : ZMod p) wRest)
                    hReducedEq
      have eEq3 := diag_n_equal_isom (w := consOneCanonM)
                    (w' := @Fin.snoc (M+1) (fun _ => ZMod p) (fun _ : Fin (M+1) => (1 : ZMod p)) d)
                    hConsSnocEq
      refine ⟨eEq1.trans (Classical.choice hstep |>.trans
        (eEq2.trans (Classical.choice hLift |>.trans eEq3)))⟩

/-! ## § 6 Discriminant of `diag_n_quadratic_form` — a pure matrix-determinant fact

We now compute the discriminant of `diag_n_quadratic_form w`.  By
construction this is `weightedSumSquares (ZMod p) w`, whose Gram matrix
(under `QuadraticMap.toMatrix'`) is the diagonal matrix `Matrix.diagonal w`.
Hence `Q.discr = Matrix.det (Matrix.diagonal w) = ∏ i, w i`.

This is precisely the lemma that closes the last hypothesis in
`Foundation/R/Bilinear/DiscriminantCharNeq2.lean` § 6c
(`classification_finite_fields_uniqueness`):  given canonical weights
`Fin.snoc 1's d`, the discriminant equals `d`. -/

/-- `2 ≠ 0` in `ZMod p` when `p ≠ 2` is an odd prime.  Local copy of the
    statement in `DiscriminantCharNeq2.lean` (which depends on this file). -/
private theorem two_ne_zero_zmod' : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : (p : ℕ) ∣ 2 := by
    have := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast h)
    exact this
  have hp_prime := hp.out
  have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp h2
  rcases this with h1 | h2'
  · exact hp_prime.one_lt.ne' h1
  · exact hp2.out h2'

/-- Local `Invertible (2 : ZMod p)` instance needed for `QuadraticMap.toMatrix'`. -/
private noncomputable instance instInvertibleTwoZMod' : Invertible (2 : ZMod p) :=
  invertibleOfNonzero two_ne_zero_zmod'

/-- The Gram matrix of `diag_n_quadratic_form w` is the diagonal matrix
    with entries `w i`.  Proof entry-by-entry via `toMatrix₂'_apply` and
    direct calculation of the polar `(Q(eᵢ+eⱼ) - Q(eᵢ) - Q(eⱼ))/2`. -/
theorem diag_n_toMatrix' {N : ℕ} (w : Fin N → ZMod p) :
    (diag_n_quadratic_form w).toMatrix' = Matrix.diagonal w := by
  ext i j
  -- Unfold toMatrix' and associated to expose the polarization formula.
  show (QuadraticMap.toMatrix' (diag_n_quadratic_form w)) i j
      = Matrix.diagonal w i j
  rw [QuadraticMap.toMatrix', LinearMap.toMatrix₂'_apply]
  -- Goal: associated (diag_n_quadratic_form w) (Pi.single i 1) (Pi.single j 1) = diagonal w i j
  rw [QuadraticMap.associated_apply]
  -- Now we have ⅟2 • (Q(eᵢ + eⱼ) - Q(eᵢ) - Q(eⱼ)) = diagonal w i j.
  -- Evaluate Q on standard basis vectors.
  have hQ : ∀ x : Fin N → ZMod p,
      diag_n_quadratic_form w x = ∑ k, w k * (x k * x k) :=
    fun x => diag_n_quadratic_form_apply w x
  rw [hQ, hQ, hQ]
  by_cases hij : i = j
  · -- Diagonal case i = j: Pi.single i 1 + Pi.single j 1 = 2 • Pi.single i 1.
    subst hij
    have hii : Matrix.diagonal w i i = w i := Matrix.diagonal_apply_eq _ i
    rw [hii]
    -- Pi.single i 1 has support {i}; the sum collapses to one term.
    have hsingle : ∀ k : Fin N, (Pi.single i 1 : Fin N → ZMod p) k
        = if k = i then 1 else 0 := by
      intro k
      by_cases hk : k = i
      · subst hk; rw [Pi.single_eq_same]; simp
      · rw [Pi.single_eq_of_ne hk]; simp [hk]
    -- The sum (∑ k, w k * (c * Pi.single i 1 k)²) = c² * w i.
    have hsum_single : ∀ (c : ZMod p),
        ∑ k, w k * ((c * (Pi.single i 1 : Fin N → ZMod p) k)
          * (c * (Pi.single i 1 : Fin N → ZMod p) k))
            = c * c * w i := by
      intro c
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]; ring
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk]; ring
      · intro h; exact (h (Finset.mem_univ _)).elim
    -- Q(eᵢ + eᵢ) = Q(2eᵢ) = 4 * w i.
    have hsum_add : ∑ k, w k * (((Pi.single i 1 + Pi.single i 1 : Fin N → ZMod p) k)
                          * ((Pi.single i 1 + Pi.single i 1 : Fin N → ZMod p) k))
                  = 4 * w i := by
      have hrewrite : ∀ k : Fin N,
          w k * (((Pi.single i 1 + Pi.single i 1 : Fin N → ZMod p) k)
                * ((Pi.single i 1 + Pi.single i 1 : Fin N → ZMod p) k))
            = w k * ((2 * (Pi.single i 1 : Fin N → ZMod p) k)
                * (2 * (Pi.single i 1 : Fin N → ZMod p) k)) := by
        intro k; rw [Pi.add_apply]; ring
      rw [Finset.sum_congr rfl (fun k _ => hrewrite k)]
      have h2 := hsum_single 2
      have h4 : (2 : ZMod p) * 2 = 4 := by norm_num
      rw [h4] at h2
      exact h2
    have hsum_eqi : ∑ k, w k * ((Pi.single i 1 : Fin N → ZMod p) k
                            * (Pi.single i 1 : Fin N → ZMod p) k) = w i := by
      have h1 := hsum_single 1
      rw [one_mul, one_mul] at h1
      convert h1 using 1
      apply Finset.sum_congr rfl
      intro k _; ring
    rw [hsum_add, hsum_eqi]
    -- Goal: ⅟2 • (4 * w i - w i - w i) = w i.
    have h2 : (4 : ZMod p) * w i - w i - w i = 2 * w i := by ring
    rw [h2]
    -- ⅟2 • (2 * w i) = w i.
    show ⅟(2 : ZMod p) • (2 * w i) = w i
    rw [smul_eq_mul]
    rw [show (2 : ZMod p) * w i = (2 : ZMod p) * w i from rfl]
    rw [show ⅟(2 : ZMod p) * (2 * w i) = (⅟(2 : ZMod p) * 2) * w i from (mul_assoc _ _ _).symm]
    rw [invOf_mul_self, one_mul]
  · -- Off-diagonal case i ≠ j.
    have hij_off : Matrix.diagonal w i j = 0 := Matrix.diagonal_apply_ne _ hij
    rw [hij_off]
    -- For each k: (Pi.single i 1 k) * (Pi.single i 1 k) is 1 if k = i else 0; similarly for j.
    -- The sum ∑ k, w k * (Pi.single i 1 k)² = w i (since only k = i contributes).
    have hsum_i : ∑ k, w k * ((Pi.single i 1 : Fin N → ZMod p) k
                          * (Pi.single i 1 : Fin N → ZMod p) k) = w i := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]; ring
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk]; ring
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hsum_j : ∑ k, w k * ((Pi.single j 1 : Fin N → ZMod p) k
                          * (Pi.single j 1 : Fin N → ZMod p) k) = w j := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]; ring
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk]; ring
      · intro h; exact (h (Finset.mem_univ _)).elim
    -- Q(eᵢ + eⱼ): expand (single i 1 + single j 1)² = single i 1² + 2 single i 1 * single j 1
    --             + single j 1²; the cross term vanishes for i ≠ j.
    -- Concretely: (single i 1 + single j 1) k =
    --   if k = i then 1 else if k = j then 1 else 0  (for i ≠ j).
    have hadd_val : ∀ k : Fin N,
        ((Pi.single i 1 + Pi.single j 1 : Fin N → ZMod p) k)
          * ((Pi.single i 1 + Pi.single j 1 : Fin N → ZMod p) k)
        = ((Pi.single i 1 : Fin N → ZMod p) k) * ((Pi.single i 1 : Fin N → ZMod p) k)
        + ((Pi.single j 1 : Fin N → ZMod p) k) * ((Pi.single j 1 : Fin N → ZMod p) k) := by
      intro k
      by_cases hki : k = i
      · subst hki
        rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij]
        simp
      · by_cases hkj : k = j
        · subst hkj
          rw [Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_same]
          simp
        · rw [Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
          simp
    have hsum_add : ∑ k, w k * (((Pi.single i 1 + Pi.single j 1 : Fin N → ZMod p) k)
                            * ((Pi.single i 1 + Pi.single j 1 : Fin N → ZMod p) k))
                  = w i + w j := by
      have hreduce : ∀ k, w k * (((Pi.single i 1 + Pi.single j 1 : Fin N → ZMod p) k)
                            * ((Pi.single i 1 + Pi.single j 1 : Fin N → ZMod p) k))
                  = w k * ((Pi.single i 1 : Fin N → ZMod p) k * (Pi.single i 1 : Fin N → ZMod p) k)
                    + w k * ((Pi.single j 1 : Fin N → ZMod p) k * (Pi.single j 1 : Fin N → ZMod p) k) := by
        intro k; rw [hadd_val]; ring
      rw [Finset.sum_congr rfl (fun k _ => hreduce k)]
      rw [Finset.sum_add_distrib, hsum_i, hsum_j]
    rw [hsum_add, hsum_i, hsum_j]
    -- Goal: ⅟2 • ((w i + w j) - w i - w j) = 0.
    have hz : (w i + w j) - w i - w j = 0 := by ring
    rw [hz, smul_zero]

/-- **Discriminant of `diag_n_quadratic_form`** — `det (Matrix.diagonal w) = ∏ w`. -/
theorem discr_diag_n_quadratic_form {N : ℕ} (w : Fin N → ZMod p) :
    (diag_n_quadratic_form w).discr = ∏ i, w i := by
  rw [QuadraticMap.discr, diag_n_toMatrix']
  exact Matrix.det_diagonal

/-- **Canonical-form discriminant** — for `Fin.snoc 1's d`, the
    discriminant is just `d`.  This closes the `hCanonDiscr` hypothesis
    in `DiscriminantCharNeq2.classification_finite_fields_uniqueness`. -/
theorem canon_diag_discr {N : ℕ} (d : ZMod p) :
    (diag_n_quadratic_form
      (@Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d)).discr = d := by
  rw [discr_diag_n_quadratic_form]
  -- Product over Fin (N+1) of (Fin.snoc 1's d), use Fin.prod_univ_castSucc.
  rw [Fin.prod_univ_castSucc]
  -- ∏_{i : Fin N} snoc 1's d (i.castSucc) * snoc 1's d (last N)
  -- = ∏_{i : Fin N} 1 * d   = 1 * d = d.
  rw [Fin.snoc_last]
  have hcs : ∀ i : Fin N,
      (@Fin.snoc N (fun _ => ZMod p) (fun _ : Fin N => (1 : ZMod p)) d) i.castSucc = 1 := by
    intro i; rw [Fin.snoc_castSucc]
  rw [Finset.prod_congr rfl (fun i _ => hcs i), Finset.prod_const_one, one_mul]

end R

end SSBX.Foundation.R
