/-
# Foundation.R.SubTower — the intrinsic 2ⁿ sub-tower of R (2 * n)

Per `wen-algebra` v0.4 §3.5 (whose math survives unchanged in v0.6):
inside every `R (2 * n)` lives an intrinsic 2ⁿ sub-tower:

    {U : R (2 * n) // ∀ k, U ⟨2k, _⟩ = U ⟨2k+1, _⟩}

i.e., the cells whose every 2-block has both coordinates equal (each
R 2-block is either `oo` or `xx`).

This sub-tower has cardinality `2ⁿ` and admits **three equivalent
characterisations** on R 2 (atomic case):

1. **Diagonal predicate** — `v 0 = v 1` (the block is `oo` or `xx`).
2. **Self-pairing isotropy** — `dot v v = false` (geometric isotropy).
3. **Kernel of L** — `L v = false` (the diagonal projection vanishes).

Following the v0.6 doctrine, the names `{道, 错综}` etc. are NOT used.
The sub-tower is named purely structurally.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 Atomic R 2 sub-tower predicate -/

/-- `v : R 2` is in the atomic sub-tower iff its two coordinates agree
    (i.e., `v 0 = v 1`).  Equivalently `v ∈ {oo, xx}` as a set. -/
def InSubTowerAtomic (v : R 2) : Prop :=
  v ⟨0, by decide⟩ = v ⟨1, by decide⟩

instance instDecidableInSubTowerAtomic (v : R 2) :
    Decidable (InSubTowerAtomic v) := by
  unfold InSubTowerAtomic
  exact instDecidableEqBool _ _

/-- `oo` is in the atomic sub-tower (both coords are false). -/
theorem oo_inSubTowerAtomic : InSubTowerAtomic (oo : R 2) := by
  unfold InSubTowerAtomic; rfl

/-- `xx` is in the atomic sub-tower (both coords are true). -/
theorem xx_inSubTowerAtomic : InSubTowerAtomic (xx : R 2) := by
  unfold InSubTowerAtomic; rfl

/-- `xo` is *not* in the atomic sub-tower (coords differ). -/
theorem xo_not_inSubTowerAtomic : ¬ InSubTowerAtomic (xo : R 2) := by
  unfold InSubTowerAtomic
  show ¬ (xo ⟨0, _⟩ = xo ⟨1, _⟩)
  decide

/-- `ox` is *not* in the atomic sub-tower (coords differ). -/
theorem ox_not_inSubTowerAtomic : ¬ InSubTowerAtomic (ox : R 2) := by
  unfold InSubTowerAtomic
  show ¬ (ox ⟨0, _⟩ = ox ⟨1, _⟩)
  decide

/-! ## § 2 Three-in-one characterisation on R 2

We package the three equivalent descriptions of the atomic R 2
sub-tower:

* (1) diagonal predicate: `v 0 = v 1`
* (2) self-pairing isotropy: `dot v v = false`
* (3) kernel of L: `L v = false`

All three are equivalent — proven by 4-case `decide` over R 2. -/

/-- The atomic L is `v 0 ⊕ v 1` on R 2. -/
theorem L_R2 (v : R 2) :
    L (N := 2) v = Bool.xor (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) := by
  show xorFold v = _
  rw [xorFold_succ]
  show Bool.xor (v 0) (xorFold (fun j => v j.succ)) = _
  -- xorFold over Fin 1 = Bool.xor (f 0) false = f 0; here f 0 = v 1.
  have h_inner : xorFold (fun j : Fin 1 => v j.succ) = v 1 := by
    rw [xorFold_succ]
    show Bool.xor (v (Fin.succ 0)) (xorFold (fun j : Fin 0 => v j.succ.succ)) = v 1
    rw [xorFold_zero]
    have : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := rfl
    rw [this]
    cases v 1 <;> rfl
  rw [h_inner]
  have h_idx0 : (v 0 : Bool) = v ⟨0, by decide⟩ := rfl
  have h_idx1 : (v 1 : Bool) = v ⟨1, by decide⟩ := rfl
  rw [h_idx0, h_idx1]

/-- The atomic dot self-pairing equals L on R 2:
    `dot v v = (v 0 ∧ v 0) ⊕ (v 1 ∧ v 1) = v 0 ⊕ v 1 = L v`. -/
theorem dot_self_eq_L_R2 (v : R 2) :
    dot v v = L (N := 2) v := by
  rw [L_R2 v]
  -- dot v v = (v 0 ∧ v 0) ⊕ ((v 1 ∧ v 1) ⊕ 0) ... = v 0 ⊕ v 1
  show xorFold (fun i => Bool.and (v i) (v i)) = _
  rw [xorFold_succ]
  show Bool.xor (Bool.and (v 0) (v 0))
        (xorFold (fun j : Fin 1 => Bool.and (v j.succ) (v j.succ))) = _
  rw [xorFold_succ]
  show Bool.xor (Bool.and (v 0) (v 0))
        (Bool.xor (Bool.and (v (Fin.succ 0)) (v (Fin.succ 0)))
                  (xorFold (fun j : Fin 0 => Bool.and (v j.succ.succ) (v j.succ.succ))))
      = _
  rw [xorFold_zero]
  have h_succ : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := rfl
  rw [h_succ]
  have h_idx0 : (v 0 : Bool) = v ⟨0, by decide⟩ := rfl
  have h_idx1 : (v 1 : Bool) = v ⟨1, by decide⟩ := rfl
  rw [h_idx0, h_idx1]
  cases v ⟨0, by decide⟩ <;> cases v ⟨1, by decide⟩ <;> rfl

/-- Three-in-one characterisation, part 1: predicate ↔ L vanishes.

      v ∈ sub-tower ↔ L v = false. -/
theorem inSubTowerAtomic_iff_L (v : R 2) :
    InSubTowerAtomic v ↔ L (N := 2) v = false := by
  rw [L_R2]
  unfold InSubTowerAtomic
  cases v ⟨0, by decide⟩ <;> cases v ⟨1, by decide⟩ <;> simp

/-- Three-in-one characterisation, part 2: predicate ↔ self-pairing
    vanishes.

      v ∈ sub-tower ↔ dot v v = false.

    Direct corollary of `dot_self_eq_L_R2` + `inSubTowerAtomic_iff_L`. -/
theorem inSubTowerAtomic_iff_self_dot (v : R 2) :
    InSubTowerAtomic v ↔ dot v v = false := by
  rw [inSubTowerAtomic_iff_L, dot_self_eq_L_R2]

/-! ## § 3 The R (2 * n) sub-tower as a predicate -/

/-- `U : R (2 * n)` is in the sub-tower iff every 2-block has both
    coordinates equal.  Per `wen-algebra` v0.4 §3.5. -/
def InSubTower {n : ℕ} (U : R (2 * n)) : Prop :=
  ∀ k : Fin n, U ⟨2 * k.val, by have := k.isLt; omega⟩
             = U ⟨2 * k.val + 1, by have := k.isLt; omega⟩

instance instDecidableInSubTower {n : ℕ} (U : R (2 * n)) :
    Decidable (InSubTower U) :=
  Fintype.decidableForallFintype

/-! ## § 4 Cardinality of the sub-tower

The sub-tower of `R (2 * n)` has cardinality `2ⁿ`, witnessed by an
equivalence with `Fin n → Bool` (each block selects oo or xx). -/

/-- The sub-tower as a subtype. -/
abbrev SubTower (n : ℕ) : Type :=
  { U : R (2 * n) // InSubTower U }

instance instFintypeSubTower (n : ℕ) : Fintype (SubTower n) :=
  Subtype.fintype _

/-- Construct an R (2 * n) element from a per-block bit choice:
    block `k` gets `(b k, b k)`.  This is the inverse of the
    "extract block values" map. -/
def ofChoice {n : ℕ} (b : Fin n → Bool) : R (2 * n) :=
  fun i =>
    -- index i ∈ Fin (2 * n) decomposes as (i.val / 2, i.val % 2)
    b ⟨i.val / 2, by
      have h := i.isLt
      have : i.val / 2 < n := by omega
      exact this⟩

theorem ofChoice_inSubTower {n : ℕ} (b : Fin n → Bool) :
    InSubTower (ofChoice b) := by
  intro k
  show ofChoice b ⟨2 * k.val, _⟩ = ofChoice b ⟨2 * k.val + 1, _⟩
  show b ⟨(2 * k.val) / 2, _⟩ = b ⟨(2 * k.val + 1) / 2, _⟩
  congr 1
  apply Fin.ext
  show (2 * k.val) / 2 = (2 * k.val + 1) / 2
  omega

end R

end SSBX.Foundation.R
