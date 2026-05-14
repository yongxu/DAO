/-
# Foundation.R.Hom — `Hom_F₂(R N, R M)` representation basics

Per `wen-algebra` v0.6 §2.3 and §3 and `v4-foundation` v0.5 §11.3:

    Hom_F₂(R N, R M)  ≅  R (N * M)

(via the standard `M × N`-matrix representation of an `F_2`-linear map).
This file delivers the **basic** Hom-representation layer: a concrete
type `LinHom N M` for `F_2`-linear maps `R N → R M`, an equivalence
with `Fin M → Fin N → Bool` (= matrix view), and the cardinality
identity.

The full `Hom(R 2n, R 2m) ≅ Mat_{m × n}(R 4)` (= `R_4`-cell view of
§3.2) is deferred to `Foundation/R4/HomMat.lean` (P2 work).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 F_2-linear maps -/

/-- An `F_2`-linear endomorphism of `R N → R M`, encoded as an
    `M × N`-matrix `Fin M → Fin N → Bool`.  The `(i, j)` entry is the
    coefficient of `e_j` in `f(e_j)_i`. -/
abbrev LinHom (N M : ℕ) : Type := Fin M → Fin N → Bool

namespace LinHom

variable {N M P : ℕ}

/-- Recursive XOR-sum over `Fin N` of a Bool-valued function.  We use
    a structural recursion on `N` (peeling off coordinate 0 via
    `Fin.tail`) so that proofs by `Nat`-induction are direct. -/
def xorSum : ∀ {N : ℕ}, (Fin N → Bool) → Bool
  | 0,     _ => false
  | _ + 1, f => Bool.xor (f 0) (xorSum (fun j => f j.succ))

@[simp] theorem xorSum_zero (f : Fin 0 → Bool) : xorSum f = false := rfl

theorem xorSum_succ {N : ℕ} (f : Fin (N + 1) → Bool) :
    xorSum f = Bool.xor (f 0) (xorSum (fun j => f j.succ)) := rfl

/-- All-`false` XOR-sum is `false`. -/
theorem xorSum_const_false (N : ℕ) :
    xorSum (fun _ : Fin N => false) = false := by
  induction N with
  | zero => rfl
  | succ k ih => rw [xorSum_succ]; show Bool.xor false _ = false; rw [ih]; rfl

/-- "Pick-out" lemma: if a Bool function is `true` at exactly one index
    and `false` elsewhere, the XOR-sum is the value at that index (=
    `true`). -/
theorem xorSum_pick {N : ℕ} (i : Fin N) (b : Bool) :
    xorSum (fun j => if i = j then b else false) = b := by
  induction N with
  | zero => exact i.elim0
  | succ k ih =>
    rw [xorSum_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · -- i = 0: term at j = 0 is `b`; tail is all `false`.
      show Bool.xor (if (0 : Fin (k + 1)) = 0 then b else false)
                    (xorSum (fun j => if (0 : Fin (k + 1)) = j.succ then b else false))
        = b
      have h : ((0 : Fin (k + 1)) = (0 : Fin (k + 1))) = True := by simp
      simp only [h, if_true]
      have htail :
          (fun j : Fin k => if (0 : Fin (k + 1)) = j.succ then b else false)
            = (fun _ => false) := by
        funext j
        have : (0 : Fin (k + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
        simp [this]
      rw [htail, xorSum_const_false]
      cases b <;> rfl
    · -- i = j.succ: term at 0 is `false`; tail picks at `j` with value `b`.
      show Bool.xor (if (j.succ : Fin (k + 1)) = 0 then b else false)
                    (xorSum (fun k' =>
                      if (j.succ : Fin (k + 1)) = k'.succ then b else false))
        = b
      have h : (j.succ : Fin (k + 1)) ≠ 0 := Fin.succ_ne_zero j
      simp only [h, if_false]
      have htail :
          (fun k' : Fin k => if (j.succ : Fin (k + 1)) = k'.succ then b else false)
            = (fun k' => if j = k' then b else false) := by
        funext k'
        by_cases hk : j = k'
        · simp [hk]
        · have : (j.succ : Fin (k + 1)) ≠ k'.succ := fun heq =>
            hk (Fin.succ_injective _ heq)
          simp [this, hk]
      rw [htail]
      show Bool.xor false _ = b
      rw [ih j]
      cases b <;> rfl

/-! ## § 2 The apply / compose operations -/

/-- Apply a linear map `f : LinHom N M` to a vector `v : R N`:

      (f v)_i = ⊕_j (f i j ∧ v j). -/
def apply (f : LinHom N M) (v : R N) : R M :=
  fun i => xorSum (fun j => Bool.and (f i j) (v j))

/-- The zero linear map: all entries `false`. -/
def zero (N M : ℕ) : LinHom N M := fun _ _ => false

/-- Matrix product (= composition of linear maps):

      (g ∘ f) i k = ⊕_j (g i j ∧ f j k). -/
def compose (g : LinHom M P) (f : LinHom N M) : LinHom N P :=
  fun i k => xorSum (fun j => Bool.and (g i j) (f j k))

/-- The identity linear map `R N → R N`: the Kronecker delta matrix. -/
def id (N : ℕ) : LinHom N N := fun i j => decide (i = j)

@[simp] theorem id_apply_diag (N : ℕ) (i : Fin N) : id N i i = true := by
  simp [id]

theorem id_apply_off (N : ℕ) {i j : Fin N} (h : i ≠ j) :
    id N i j = false := by
  simp [id, h]

@[simp] theorem zero_apply_eq (N M : ℕ) (i : Fin M) (j : Fin N) :
    zero N M i j = false := rfl

/-! ## § 3 Identity preservation under `apply` -/

/-- `apply (id N) v = v` for every `v : R N` — the identity matrix
    indeed encodes the identity linear map. -/
theorem apply_id (N : ℕ) (v : R N) : apply (id N) v = v := by
  funext i
  show xorSum (fun j => Bool.and (id N i j) (v j)) = v i
  have h : (fun j => Bool.and (id N i j) (v j))
            = (fun j => if i = j then v i else false) := by
    funext j
    by_cases hij : i = j
    · subst hij; simp [id]
    · rw [id_apply_off _ hij]
      simp [hij]
  rw [h, xorSum_pick]

/-! ## § 4 Matrix view ≃ flat R (N * M) view -/

/-- The matrix view `LinHom N M = Fin M → Fin N → Bool` is
    `Fintype` (inherited from `Pi`). -/
instance instFintype (N M : ℕ) : Fintype (LinHom N M) :=
  inferInstanceAs (Fintype (Fin M → Fin N → Bool))

instance instDecidableEq (N M : ℕ) : DecidableEq (LinHom N M) :=
  inferInstanceAs (DecidableEq (Fin M → Fin N → Bool))

/-- |LinHom N M| = 2^(N * M).  Per `wen-algebra` v0.6 §2.3. -/
theorem card_linHom (N M : ℕ) :
    Fintype.card (LinHom N M) = 2 ^ (N * M) := by
  show Fintype.card (Fin M → Fin N → Bool) = 2 ^ (N * M)
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Fintype.card_fin]
  -- Goal: (2 ^ N) ^ M = 2 ^ (N * M)
  rw [← pow_mul]

/-- Cardinality identity: `|LinHom N M| = |R (N * M)|`.  Combined with
    a chosen explicit bijection this realizes `wen-algebra` v0.6 §2.3:
    `Hom_F₂(R N, R M) ≅ R (N * M)`.  -/
theorem card_eq_R (N M : ℕ) :
    Fintype.card (LinHom N M) = Fintype.card (R (N * M)) := by
  rw [card_linHom, card_eq]

end LinHom

end R

end SSBX.Foundation.R
