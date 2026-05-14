/-
# Foundation.R.Bilinear — three layers of bilinear forms on R N

Per `wen-algebra` v0.6 §4 and `v4-foundation` v0.5 §4.6, §6.8, §10.7:

* **Layer 0** dot product `⟨u, v⟩ := ⊕_i (u_i ∧ v_i)` — defined for
  all N.
* **Layer 1** symplectic form `σ(u, v)` — defined for even N as a
  k-block alternating sum where k = N/2.
* **Layer 2** quadratic refinements `q^c` parameterised by
  `c : Fin (N/2) → Bool`, with **Arf invariant** `arf c = ⊕_k c_k`.
* **Decomposition**: `⟨u, v⟩ = σ(u, v) ⊕ L(u) ∧ L(v)` (even N), where
  `L(v) := ⊕_i v_i` is the diagonal projection.

All forms are F_2-valued and Bool-typed.

## Implementation note

For the even-N bilinear forms we use a **k-blockwise** recursion: each
step peels off the first 2-coordinate block.  This makes the
decomposition theorem provable by direct induction with a per-block
4-bit `decide` at each step.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §4.1 (three layers overview), §4.2 (Layer 0
  on R_N), §4.3 (Layer 1 on R_{2k}), §4.4 (Layer 2), §4.5 (Arf).
* `v4-foundation.md` v0.5 §4.6 (R_2 bilinear), §6.8 (R_4 bilinear),
  §10.7 (R_8 bilinear), §12 (cross-layer summary).
-/

import SSBX.Foundation.R.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 xorFold over Fin N -/

/-- Recursive XOR-sum of a Bool-valued function on `Fin N`. -/
def xorFold : ∀ {N : ℕ}, (Fin N → Bool) → Bool
  | 0,     _ => false
  | _ + 1, f => Bool.xor (f 0) (xorFold (fun j => f j.succ))

@[simp] theorem xorFold_zero (f : Fin 0 → Bool) : xorFold f = false := rfl

theorem xorFold_succ {N : ℕ} (f : Fin (N + 1) → Bool) :
    xorFold f = Bool.xor (f 0) (xorFold (fun j => f j.succ)) := rfl

theorem xorFold_const_false (N : ℕ) :
    xorFold (fun _ : Fin N => false) = false := by
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [xorFold_succ]
    show Bool.xor false _ = false
    rw [ih]
    rfl

/-! ## § 2 Coordinate-wise primitives (apply to all R N) -/

/-- The Boolean dot product on `R N`: `⟨u, v⟩ := ⊕_i (u_i ∧ v_i)`.
    Per `wen-algebra` v0.6 §4.2. -/
def dot {N : ℕ} (u v : R N) : Bool :=
  xorFold (fun i => Bool.and (u i) (v i))

/-- The diagonal F_2-linear form `L(v) := ⊕_i v_i`.  Per
    `wen-algebra` v0.6 §4.2 and `v4-foundation` v0.5 §4.4. -/
def L {N : ℕ} (v : R N) : Bool := xorFold v

/-! ## § 3 Recursion helpers -/

theorem dot_zero_dim (u v : R 0) : dot u v = false := rfl

theorem L_zero_dim (v : R 0) : L v = false := rfl

theorem dot_succ {N : ℕ} (u v : R (N + 1)) :
    dot u v = Bool.xor (Bool.and (u 0) (v 0))
                       (dot (Fin.tail u) (Fin.tail v)) := by
  show xorFold _ = Bool.xor _ (xorFold _)
  rw [xorFold_succ]
  rfl

theorem L_succ {N : ℕ} (v : R (N + 1)) :
    L v = Bool.xor (v 0) (L (Fin.tail v)) := xorFold_succ v

/-! ## § 4 Symmetry of dot -/

theorem dot_symm {N : ℕ} (u v : R N) : dot u v = dot v u := by
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [dot_succ, dot_succ, Bool.and_comm (u 0) (v 0),
        ih (Fin.tail u) (Fin.tail v)]

theorem dot_zero_left {N : ℕ} (v : R N) : dot (0 : R N) v = false := by
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [dot_succ]
    show Bool.xor (Bool.and ((0 : R (k + 1)) 0) (v 0))
                  (dot (Fin.tail (0 : R (k + 1))) (Fin.tail v)) = false
    have h0 : ((0 : R (k + 1)) 0 : Bool) = false := rfl
    have ht : (Fin.tail (0 : R (k + 1)) : R k) = (0 : R k) := by
      funext j; rfl
    rw [h0, ht, ih]
    rfl

theorem dot_zero_right {N : ℕ} (u : R N) : dot u (0 : R N) = false := by
  rw [dot_symm]; exact dot_zero_left u

theorem L_zero {N : ℕ} : L (0 : R N) = false := by
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [L_succ]
    show Bool.xor ((0 : R (k + 1)) 0) (L (Fin.tail (0 : R (k + 1)))) = false
    have h0 : ((0 : R (k + 1)) 0 : Bool) = false := rfl
    have ht : (Fin.tail (0 : R (k + 1)) : R k) = (0 : R k) := by
      funext j; rfl
    rw [h0, ht, ih]
    rfl

/-! ## § 5 Block-wise recursion for even-N forms

We provide a `blockTail : R (2 * (k + 1)) → R (2 * k)` that drops the
first 2-coordinate block, plus accessors for the first block's two
coordinates.  All Layer-1/Layer-2 forms are defined by recursion on
`k` using this. -/

/-- The two-coordinate `R 2`-view of the first block of `R (2 * (k + 1))`. -/
def blockHead {k : ℕ} (v : R (2 * (k + 1))) (b : Fin 2) : Bool :=
  v ⟨b.val, by have := b.isLt; omega⟩

/-- The remainder of `R (2 * (k + 1))` after dropping the first
    2-coordinate block. -/
def blockTail {k : ℕ} (v : R (2 * (k + 1))) : R (2 * k) :=
  fun j => v ⟨j.val + 2, by have := j.isLt; omega⟩

@[simp] theorem blockHead_zero {k : ℕ} (v : R (2 * (k + 1))) :
    blockHead v 0 = v ⟨0, by omega⟩ := rfl

@[simp] theorem blockHead_one {k : ℕ} (v : R (2 * (k + 1))) :
    blockHead v 1 = v ⟨1, by omega⟩ := rfl

/-! ## § 6 Layer 0 block decomposition

We re-express `dot` on `R (2 * (k + 1))` as: dot of the first block
(2 coordinates of `u` and `v`) XOR dot on `R (2 * k)` of the tails. -/

/-- Two `Fin.tail` applications equal one `blockTail`. -/
theorem tail_tail_eq_blockTail {k : ℕ} (v : R (2 * (k + 1))) :
    Fin.tail (Fin.tail v) = blockTail v := by
  funext j
  show v ⟨j.val + 1 + 1, _⟩ = v ⟨j.val + 2, _⟩
  rfl

/-- Block recursion for `dot` on `R (2 * (k + 1))`. -/
theorem dot_blockwise {k : ℕ} (u v : R (2 * (k + 1))) :
    dot u v
      = Bool.xor
          (Bool.xor (Bool.and (u ⟨0, by omega⟩) (v ⟨0, by omega⟩))
                    (Bool.and (u ⟨1, by omega⟩) (v ⟨1, by omega⟩)))
          (dot (blockTail u) (blockTail v)) := by
  rw [dot_succ, dot_succ]
  have h1u : (Fin.tail u) 0 = u 1 := rfl
  have h1v : (Fin.tail v) 0 = v 1 := rfl
  have h_idx0_u : (u 0 : Bool) = u ⟨0, by omega⟩ := rfl
  have h_idx0_v : (v 0 : Bool) = v ⟨0, by omega⟩ := rfl
  have h_idx1_u : (u 1 : Bool) = u ⟨1, by omega⟩ := rfl
  have h_idx1_v : (v 1 : Bool) = v ⟨1, by omega⟩ := rfl
  have htail_u : Fin.tail (Fin.tail u) = blockTail u := tail_tail_eq_blockTail u
  have htail_v : Fin.tail (Fin.tail v) = blockTail v := tail_tail_eq_blockTail v
  rw [h1u, h1v, h_idx0_u, h_idx0_v, h_idx1_u, h_idx1_v, htail_u, htail_v]
  -- Bool.xor rearrangement: a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c
  generalize u ⟨0, by omega⟩ = a0
  generalize v ⟨0, by omega⟩ = b0
  generalize u ⟨1, by omega⟩ = a1
  generalize v ⟨1, by omega⟩ = b1
  generalize dot (blockTail u) (blockTail v) = d
  cases a0 <;> cases b0 <;> cases a1 <;> cases b1 <;> cases d <;> rfl

/-! ## § 7 Layer 1 — symplectic σ -/

/-- The block-symplectic form on `R (2 * k)`: defined recursively as
    XOR of per-block alternating pairings.

      σ on R (2 * 0)        = false
      σ on R (2 * (k + 1))  = (u_0 ∧ v_1 ⊕ u_1 ∧ v_0) ⊕ σ (blockTail u) (blockTail v)

    Per `wen-algebra` v0.6 §4.3. -/
def sigma : ∀ {k : ℕ}, R (2 * k) → R (2 * k) → Bool
  | 0,     _, _ => false
  | _ + 1, u, v =>
      Bool.xor
        (Bool.xor (Bool.and (u ⟨0, by omega⟩) (v ⟨1, by omega⟩))
                  (Bool.and (u ⟨1, by omega⟩) (v ⟨0, by omega⟩)))
        (sigma (blockTail u) (blockTail v))

@[simp] theorem sigma_zero (u v : R (2 * 0)) : sigma u v = false := rfl

theorem sigma_succ {k : ℕ} (u v : R (2 * (k + 1))) :
    sigma u v
      = Bool.xor
          (Bool.xor (Bool.and (u ⟨0, by omega⟩) (v ⟨1, by omega⟩))
                    (Bool.and (u ⟨1, by omega⟩) (v ⟨0, by omega⟩)))
          (sigma (blockTail u) (blockTail v)) := rfl

/-- σ is symmetric. -/
theorem sigma_symm {k : ℕ} (u v : R (2 * k)) : sigma u v = sigma v u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sigma_succ, sigma_succ, ih (blockTail u) (blockTail v)]
    congr 1
    generalize u ⟨0, by omega⟩ = a0
    generalize u ⟨1, by omega⟩ = a1
    generalize v ⟨0, by omega⟩ = b0
    generalize v ⟨1, by omega⟩ = b1
    cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

/-- σ is alternating: `σ(v, v) = false`.  Each block contributes
    `(v_0 ∧ v_1) ⊕ (v_1 ∧ v_0) = 0`. -/
theorem sigma_alternating {k : ℕ} (v : R (2 * k)) : sigma v v = false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sigma_succ, ih (blockTail v)]
    generalize v ⟨0, by omega⟩ = a0
    generalize v ⟨1, by omega⟩ = a1
    cases a0 <;> cases a1 <;> rfl

/-! ## § 8 Block decomposition of L -/

/-- Block recursion for `L` on `R (2 * (k + 1))`. -/
theorem L_blockwise {k : ℕ} (v : R (2 * (k + 1))) :
    L v
      = Bool.xor (Bool.xor (v ⟨0, by omega⟩) (v ⟨1, by omega⟩))
                 (L (blockTail v)) := by
  rw [L_succ]
  have h1v : (Fin.tail v) 0 = v 1 := rfl
  rw [L_succ, h1v]
  have h_idx0 : (v 0 : Bool) = v ⟨0, by omega⟩ := rfl
  have h_idx1 : (v 1 : Bool) = v ⟨1, by omega⟩ := rfl
  have htail_v : Fin.tail (Fin.tail v) = blockTail v := tail_tail_eq_blockTail v
  rw [h_idx0, h_idx1, htail_v]
  generalize v ⟨0, by omega⟩ = a0
  generalize v ⟨1, by omega⟩ = a1
  generalize L (blockTail v) = Lv
  cases a0 <;> cases a1 <;> cases Lv <;> rfl

/-! ## § 9 The decomposition theorem `dot = σ ⊕ LL`

The classical R_2-block identity `dot = σ ⊕ L(u) ∧ L(v)` holds **per
block**.  On `R (2 * k)` the correct global identity uses the
per-block outer-product `LL`, which sums `(u₀⊕u₁) ∧ (v₀⊕v₁)` across
the `k` blocks.  At `k = 1` we recover `LL = L u ∧ L v` and the
classical R_2-block formula. -/

/-- Per-block outer-product of L: on `R (2 * k)`, the XOR-sum across
    the `k` blocks of `(u_{2j} ⊕ u_{2j+1}) ∧ (v_{2j} ⊕ v_{2j+1})`.

    This is the correct quadratic refinement that makes the global
    decomposition `dot = σ ⊕ LL` hold on `R (2 * k)`. -/
def LL : ∀ {k : ℕ}, R (2 * k) → R (2 * k) → Bool
  | 0,     _, _ => false
  | _ + 1, u, v =>
      Bool.xor
        (Bool.and (Bool.xor (u ⟨0, by omega⟩) (u ⟨1, by omega⟩))
                  (Bool.xor (v ⟨0, by omega⟩) (v ⟨1, by omega⟩)))
        (LL (blockTail u) (blockTail v))

@[simp] theorem LL_zero (u v : R (2 * 0)) : LL u v = false := rfl

theorem LL_succ {k : ℕ} (u v : R (2 * (k + 1))) :
    LL u v
      = Bool.xor
          (Bool.and (Bool.xor (u ⟨0, by omega⟩) (u ⟨1, by omega⟩))
                    (Bool.xor (v ⟨0, by omega⟩) (v ⟨1, by omega⟩)))
          (LL (blockTail u) (blockTail v)) := rfl

/-- The Layer-0 ↔ Layer-1 decomposition (on R_{2k}):

      dot u v = σ(u, v) ⊕ LL(u, v).

    Per `wen-algebra` v0.6 §4.6 (block-typed Sense 2 form).  Proven by
    induction on `k` with a block-wise 64-case Bool identity at the
    inductive step. -/
theorem dot_eq_sigma_xor_LL {k : ℕ} (u v : R (2 * k)) :
    dot u v = Bool.xor (sigma u v) (LL u v) := by
  induction k with
  | zero =>
    have hdot : dot u v = false := by
      show xorFold _ = false
      have : (fun i : Fin (2 * 0) => Bool.and (u i) (v i)) = (fun _ => false) := by
        funext i; exact i.elim0
      rw [this, xorFold_const_false]
    rw [hdot]
    rfl
  | succ k ih =>
    have ih_b := ih (blockTail u) (blockTail v)
    rw [dot_blockwise u v, sigma_succ, LL_succ, ih_b]
    -- Goal is now a Bool identity in 6 variables:
    --   u0, u1, v0, v1, sigma_tail, LL_tail.
    generalize u ⟨0, by omega⟩ = a0
    generalize u ⟨1, by omega⟩ = a1
    generalize v ⟨0, by omega⟩ = b0
    generalize v ⟨1, by omega⟩ = b1
    generalize sigma (blockTail u) (blockTail v) = st
    generalize LL (blockTail u) (blockTail v) = lt
    cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
      cases st <;> cases lt <;> rfl

/-- R_2 corollary: on a single 2-block, `LL` reduces to `L u ∧ L v`.
    This is the classical `wen-algebra` v0.6 §4.6 R_2-block identity. -/
theorem LL_R2 (u v : R 2) :
    LL (k := 1) u v = Bool.and (L u) (L v) := by
  have hLu : L u = Bool.xor (u ⟨0, by omega⟩) (u ⟨1, by omega⟩) := by
    show xorFold u = _
    rw [xorFold_succ]
    show Bool.xor (u 0) (xorFold (fun j => u j.succ)) = _
    have h1 : (fun j : Fin 1 => u j.succ) 0 = u 1 := rfl
    rw [xorFold_succ]
    show Bool.xor (u 0) (Bool.xor (u 1) (xorFold (fun _ : Fin 0 => _))) = _
    rw [xorFold_zero]
    have h_idx0 : (u 0 : Bool) = u ⟨0, by omega⟩ := rfl
    have h_idx1 : (u 1 : Bool) = u ⟨1, by omega⟩ := rfl
    rw [h_idx0, h_idx1]
    cases u ⟨0, by omega⟩ <;> cases u ⟨1, by omega⟩ <;> rfl
  have hLv : L v = Bool.xor (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) := by
    show xorFold v = _
    rw [xorFold_succ]
    show Bool.xor (v 0) (xorFold (fun j => v j.succ)) = _
    rw [xorFold_succ]
    show Bool.xor (v 0) (Bool.xor (v 1) (xorFold (fun _ : Fin 0 => _))) = _
    rw [xorFold_zero]
    have h_idx0 : (v 0 : Bool) = v ⟨0, by omega⟩ := rfl
    have h_idx1 : (v 1 : Bool) = v ⟨1, by omega⟩ := rfl
    rw [h_idx0, h_idx1]
    cases v ⟨0, by omega⟩ <;> cases v ⟨1, by omega⟩ <;> rfl
  show Bool.xor (Bool.and (Bool.xor (u ⟨0, by omega⟩) (u ⟨1, by omega⟩))
                          (Bool.xor (v ⟨0, by omega⟩) (v ⟨1, by omega⟩))) false
        = Bool.and (L u) (L v)
  rw [hLu, hLv]
  cases u ⟨0, by omega⟩ <;> cases u ⟨1, by omega⟩ <;>
    cases v ⟨0, by omega⟩ <;> cases v ⟨1, by omega⟩ <;> rfl

/-- R_2 instance of the decomposition: `dot = σ ⊕ L(u) ∧ L(v)` on R 2. -/
theorem dot_eq_sigma_xor_L_R2 (u v : R 2) :
    dot u v = Bool.xor (sigma (k := 1) u v) (Bool.and (L u) (L v)) := by
  rw [dot_eq_sigma_xor_LL (k := 1) u v, LL_R2 u v]

/-! ## § 10 Layer 2 — quadratic refinements -/

/-- Atomic q0 block: `v_0 ∧ v_1` on a single 2-block. -/
def q0Block {k : ℕ} (v : R (2 * (k + 1))) : Bool :=
  Bool.and (v ⟨0, by omega⟩) (v ⟨1, by omega⟩)

/-- Atomic q1 block: `v_0 ⊕ v_1 ⊕ (v_0 ∧ v_1)` on a single 2-block. -/
def q1Block {k : ℕ} (v : R (2 * (k + 1))) : Bool :=
  Bool.xor (Bool.xor (v ⟨0, by omega⟩) (v ⟨1, by omega⟩))
           (Bool.and (v ⟨0, by omega⟩) (v ⟨1, by omega⟩))

/-- The Layer-2 quadratic refinement of σ on `R (2 * k)` selected by
    choice vector `c : Fin k → Bool`.  Per `wen-algebra` v0.6 §4.4. -/
def q : ∀ {k : ℕ}, (Fin k → Bool) → R (2 * k) → Bool
  | 0,     _, _ => false
  | _ + 1, c, v =>
      Bool.xor
        (if c 0 then q1Block v else q0Block v)
        (q (fun j => c j.succ) (blockTail v))

@[simp] theorem q_zero (c : Fin 0 → Bool) (v : R (2 * 0)) : q c v = false := rfl

theorem q_succ {k : ℕ} (c : Fin (k + 1) → Bool) (v : R (2 * (k + 1))) :
    q c v = Bool.xor
        (if c 0 then q1Block v else q0Block v)
        (q (fun j => c j.succ) (blockTail v)) := rfl

/-- q vanishes on the origin. -/
theorem q_zero_vec {k : ℕ} (c : Fin k → Bool) :
    q c (0 : R (2 * k)) = false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [q_succ]
    have h0 : q0Block (0 : R (2 * (k + 1))) = false := by
      show Bool.and _ _ = false
      rfl
    have h1 : q1Block (0 : R (2 * (k + 1))) = false := by
      show Bool.xor (Bool.xor _ _) (Bool.and _ _) = false
      rfl
    have htail : blockTail (0 : R (2 * (k + 1))) = (0 : R (2 * k)) := by
      funext j; rfl
    rw [htail]
    cases c 0
    · rw [show (if (false : Bool) then q1Block (0 : R (2 * (k + 1)))
                else q0Block (0 : R (2 * (k + 1)))) = q0Block (0 : R (2 * (k + 1))) from rfl,
          h0, ih (fun j => c j.succ)]
      rfl
    · rw [show (if (true : Bool) then q1Block (0 : R (2 * (k + 1)))
                else q0Block (0 : R (2 * (k + 1)))) = q1Block (0 : R (2 * (k + 1))) from rfl,
          h1, ih (fun j => c j.succ)]
      rfl

/-! ## § 11 The Arf invariant -/

/-- The Arf invariant of a quadratic refinement specified by `c`:
    the XOR-sum of the choice vector.  Per `wen-algebra` v0.6 §4.5. -/
def arf {k : ℕ} (c : Fin k → Bool) : Bool := xorFold c

@[simp] theorem arf_zero (c : Fin 0 → Bool) : arf c = false := rfl

theorem arf_succ {k : ℕ} (c : Fin (k + 1) → Bool) :
    arf c = Bool.xor (c 0) (arf (fun j => c j.succ)) := xorFold_succ c

theorem arf_const_false (k : ℕ) :
    arf (fun _ : Fin k => false) = false := xorFold_const_false k

/-! ## § 12 Concrete sanity checks at small layers -/

example : dot (oo : R 2) (xx : R 2) = false := by decide
example : dot (xo : R 2) (xo : R 2) = true := by decide
example : dot (xx : R 2) (xx : R 2) = false := by decide

example : sigma (k := 1) (oo : R 2) (xx : R 2) = false := by decide
example : sigma (k := 1) (xx : R 2) (xx : R 2) = false := by decide
example : sigma (k := 1) (xo : R 2) (ox : R 2) = true := by decide

example : L (oo : R 2) = false := by decide
example : L (xx : R 2) = false := by decide
example : L (xo : R 2) = true := by decide
example : L (ox : R 2) = true := by decide

example : arf (fun _ : Fin 2 => false) = false := by decide
example : arf (fun _ : Fin 2 => true) = false := by decide
example : arf (fun i : Fin 2 => decide (i.val = 0)) = true := by decide

end R

end SSBX.Foundation.R
