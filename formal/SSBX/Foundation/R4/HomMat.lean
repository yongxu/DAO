/-
# Foundation.R4.HomMat — `Hom(R (2n), R (2m)) ≃ Mat_{m × n}(R 4)`

Per `r4.md` v0.2 §10 ("Hom representation: Mat(R 4)") and
`wen-algebra` v0.6 §3.2:

For even `2n` and `2m`, an `F_2`-linear map `R (2n) → R (2m)` can be
encoded as an `m × n` matrix whose entries are `R 4`-cells (since
`R 4 = End(R 2)`).  This is **method C** of r4.md §10.2 — the
canonical structured representation:

    HomMat n m := Fin m → Fin n → R 4

with `apply : HomMat n m × R (2n) → R (2m)` and
`compose : HomMat m p × HomMat n m → HomMat n p` defined block-wise
using the `R 4` operations from `EndR2.lean`.

## Doctrinal anchor

* `r4.md` v0.2 §10.1 (general Hom representation),
  §10.2 (method A/B/C comparison), §10.3 (why C),
  §10.4 (examples), §10.5 (apply / compose).
* `wen-algebra` v0.6 §3.2 (Mat(R 4) Hom encoding).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R4.EndR2

namespace SSBX.Foundation.R4

open SSBX.Foundation.R

/-! ## § 1 The HomMat type

`HomMat n m` is an `m × n` matrix whose cells are `R 4`-cells.
Each cell encodes a 2×2 `F_2`-block. -/

/-- An `m × n` matrix of `R 4`-cells.  Represents an `F_2`-linear map
    `R (2n) → R (2m)` via method C of `r4.md §10`. -/
abbrev HomMat (n m : ℕ) : Type := Fin m → Fin n → R 4

namespace HomMat

variable {n m p : ℕ}

/-! ## § 2 The zero matrix -/

/-- The zero `HomMat`: every cell is the `oooo` zero matrix. -/
def zero (n m : ℕ) : HomMat n m := fun _ _ => (0 : R 4)

@[simp] theorem zero_cell (n m : ℕ) (i : Fin m) (j : Fin n) :
    zero n m i j = (0 : R 4) := rfl

/-! ## § 3 The "identity" `HomMat n n`

The identity carries `idR4 = xoox` on the diagonal and `oooo` off it. -/

/-- The identity `HomMat n n`. -/
def idMat (n : ℕ) : HomMat n n := fun i j =>
  if i = j then idR4 else (0 : R 4)

theorem idMat_diag (n : ℕ) (i : Fin n) :
    idMat n i i = idR4 := by
  simp [idMat]

theorem idMat_off {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    idMat n i j = (0 : R 4) := by
  simp [idMat, h]

/-! ## § 4 Apply: `HomMat n m × R (2n) → R (2m)`

Per `r4.md §10.5`:

    f (U)_i := ⊕_j applyR2 (f_{ij}) (U_j)        ∈ R 2

where `U : R (2n)` is decomposed into n `R 2`-blocks.

We need to:

* Extract the `j`-th `R 2`-block from `U : R (2n)`: `blockOf U j`.
* Inject an `R 2` block at position `i` of the output `R (2m)`:
  `blockInject`.
* XOR-sum over `j` (using the same fold as in `Foundation/R/Bilinear.xorFold`).
-/

/-- Extract the `j`-th `R 2`-block from a vector `U : R (2 * n)`. -/
def blockOf {n : ℕ} (U : R (2 * n)) (j : Fin n) : R 2 := fun b =>
  U ⟨2 * j.val + b.val, by
    have hj := j.isLt
    have hb := b.isLt
    omega⟩

/-- XOR-sum over `Fin n` of `R 2`-valued functions: coordinate-wise XOR. -/
def xorSumR2 : ∀ {n : ℕ}, (Fin n → R 2) → R 2
  | 0,     _ => (0 : R 2)
  | _ + 1, f => f 0 + xorSumR2 (fun j => f j.succ)

@[simp] theorem xorSumR2_zero (f : Fin 0 → R 2) :
    xorSumR2 f = (0 : R 2) := rfl

theorem xorSumR2_succ {n : ℕ} (f : Fin (n + 1) → R 2) :
    xorSumR2 f = f 0 + xorSumR2 (fun j => f j.succ) := rfl

/-- Apply `f : HomMat n m` to `U : R (2 * n)` giving `R (2 * m)`.

    Output row `i` is the XOR-sum (over `j`) of
    `applyR2 (f_{ij}) (block_j U)`, packed back into the appropriate
    coordinates of `R (2 * m)`. -/
def apply {n m : ℕ} (f : HomMat n m) (U : R (2 * n)) : R (2 * m) := fun k =>
  let i : Fin m := ⟨k.val / 2, by
    have hk := k.isLt
    have : k.val / 2 < m := by omega
    exact this⟩
  let b : Fin 2 := ⟨k.val % 2, by omega⟩
  let row : R 2 := xorSumR2 (fun j => applyR2 (f i j) (blockOf U j))
  row b

/-! ## § 5 Compose: `HomMat m p × HomMat n m → HomMat n p`

Per `r4.md §10.5`:

    (g ∘ f)_{ik} := ⊕_j composeR2 (g_{ij}) (f_{jk})         ∈ R 4
-/

/-- XOR-sum over `Fin n` of `R 4`-valued functions. -/
def xorSumR4 : ∀ {n : ℕ}, (Fin n → R 4) → R 4
  | 0,     _ => (0 : R 4)
  | _ + 1, f => f 0 + xorSumR4 (fun j => f j.succ)

@[simp] theorem xorSumR4_zero (f : Fin 0 → R 4) :
    xorSumR4 f = (0 : R 4) := rfl

theorem xorSumR4_succ {n : ℕ} (f : Fin (n + 1) → R 4) :
    xorSumR4 f = f 0 + xorSumR4 (fun j => f j.succ) := rfl

/-- Compose two `HomMat` matrices.

    `(g ∘ f)_{ik} = ⊕_j composeR2 (g_{ij}) (f_{jk})`. -/
def compose {n m p : ℕ} (g : HomMat m p) (f : HomMat n m) : HomMat n p :=
  fun i k => xorSumR4 (fun j => composeR2 (g i j) (f j k))

/-! ## § 6 Cardinality identity

`|HomMat n m| = 16^(m * n) = 2^(4 * m * n) = |R (4 * m * n)|`. -/

instance instFintype (n m : ℕ) : Fintype (HomMat n m) :=
  inferInstanceAs (Fintype (Fin m → Fin n → R 4))

instance instDecidableEq (n m : ℕ) : DecidableEq (HomMat n m) :=
  inferInstanceAs (DecidableEq (Fin m → Fin n → R 4))

/-- `|HomMat n m| = 16^(m * n)`. -/
theorem card_eq (n m : ℕ) :
    Fintype.card (HomMat n m) = 16 ^ (m * n) := by
  show Fintype.card (Fin m → Fin n → R 4) = 16 ^ (m * n)
  rw [Fintype.card_fun, Fintype.card_fun, R.R4_card, Fintype.card_fin, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm n m]

/-- `|HomMat n m| = 2^(4 * m * n) = |R (4 * m * n)|`. -/
theorem card_eq_R (n m : ℕ) :
    Fintype.card (HomMat n m) = Fintype.card (R (4 * m * n)) := by
  rw [card_eq, R.card_eq]
  -- `16^(m * n) = 2^(4 * m * n)`
  have h16 : (16 : ℕ) = 2 ^ 4 := by decide
  rw [h16, ← pow_mul]
  congr 1
  show 4 * (m * n) = 4 * m * n
  rw [Nat.mul_assoc]

/-! ## § 7 Degenerate / sanity cases -/

/-- `HomMat 1 1 = R 4` (a single `R 4`-cell), per `r4.md §10.4`:
    `Hom(R 2, R 2) ≅ Mat_{1×1}(R 4)`. -/
theorem card_homMat_1_1 :
    Fintype.card (HomMat 1 1) = 16 := by
  rw [card_eq]; rfl

/-- `|HomMat 2 2| = 16^4 = 65536`, matching `|R 16|`.  Per `r4.md §10.4`:
    `Hom(R 4, R 4) ≅ Mat_{2×2}(R 4)`, total cardinality `16^4`. -/
theorem card_homMat_2_2 :
    Fintype.card (HomMat 2 2) = 65536 := by
  rw [card_eq]; rfl

end HomMat

end SSBX.Foundation.R4
