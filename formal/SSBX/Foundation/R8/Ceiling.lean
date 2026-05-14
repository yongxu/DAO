/-
# Foundation.R8.Ceiling — R N ↪ R 8 for all N ≤ 8

Per `r8.md` v0.2 §2, every layer `R N` with `N ≤ 7` embeds into `R 8`
as a subspace (and `R 8 ↪ R 8` is the identity).  The canonical
"front-N" embedding sends `v : R N` to the `R 8`-vector that copies `v`
in positions `0..N-1` and is `false` in positions `N..7`.

This makes `R 8` the **ceiling** of the root layers `R 0`–`R 8`: every
algebraic fact about `R N` with `N ≤ 7` can be re-stated inside `R 8`.

## Doctrinal anchor

* `r8.md` v0.2 §2.1 (front-N embedding), §2.2 (full table), §2.4
  (ceiling sufficiency).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 The generic front-N embedding -/

/-- The canonical "front-N" embedding `R N → R 8` for any `N ≤ 8`.
    Coordinates `0..N-1` come from `v`; coordinates `N..7` are `false`. -/
def embedFrom {N : ℕ} (h : N ≤ 8) (v : R N) : R 8 := fun i =>
  if hLt : i.val < N then v ⟨i.val, hLt⟩ else false

@[simp] theorem embedFrom_apply {N : ℕ} (h : N ≤ 8) (v : R N) (i : Fin 8) :
    embedFrom h v i = (if hLt : i.val < N then v ⟨i.val, hLt⟩ else false) := rfl

theorem embedFrom_apply_lt {N : ℕ} (h : N ≤ 8) (v : R N) (i : Fin 8)
    (hLt : i.val < N) : embedFrom h v i = v ⟨i.val, hLt⟩ := by
  simp [embedFrom, hLt]

theorem embedFrom_apply_ge {N : ℕ} (h : N ≤ 8) (v : R N) (i : Fin 8)
    (hGe : N ≤ i.val) : embedFrom h v i = false := by
  simp [embedFrom, Nat.not_lt.mpr hGe]

/-! ## § 2 Injectivity -/

/-- The front-N embedding is injective. -/
theorem embedFrom_injective {N : ℕ} (h : N ≤ 8) :
    Function.Injective (embedFrom h) := by
  intro v₁ v₂ heq
  funext i
  rcases i with ⟨k, hk⟩
  have hk' : k < 8 := lt_of_lt_of_le hk h
  have := congrFun heq ⟨k, hk'⟩
  simp [embedFrom, hk] at this
  exact this

/-! ## § 3 Additivity (preserves XOR / direct-sum group structure) -/

theorem embedFrom_zero {N : ℕ} (h : N ≤ 8) :
    embedFrom h (0 : R N) = (0 : R 8) := by
  funext i
  by_cases hi : i.val < N
  · rw [embedFrom_apply_lt h _ i hi]; rfl
  · rw [embedFrom_apply_ge h _ i (Nat.le_of_not_lt hi)]; rfl

theorem embedFrom_add {N : ℕ} (h : N ≤ 8) (u v : R N) :
    embedFrom h (u + v) = embedFrom h u + embedFrom h v := by
  funext i
  show embedFrom h (u + v) i = Bool.xor (embedFrom h u i) (embedFrom h v i)
  by_cases hi : i.val < N
  · rw [embedFrom_apply_lt h _ i hi, embedFrom_apply_lt h _ i hi,
        embedFrom_apply_lt h _ i hi]
    rfl
  · rw [embedFrom_apply_ge h _ i (Nat.le_of_not_lt hi),
        embedFrom_apply_ge h _ i (Nat.le_of_not_lt hi),
        embedFrom_apply_ge h _ i (Nat.le_of_not_lt hi)]
    rfl

/-! ## § 4 Subspace characterisation

The image of `R N → R 8` is the subset of `R 8`-vectors with
all coordinates `≥ N` set to `false`.  We package this as a
`Set`-equality theorem. -/

/-- The set of `w : R 8` with all coordinates ≥ N false. -/
def frontSubspace (N : ℕ) : Set (R 8) :=
  { w | ∀ i : Fin 8, N ≤ i.val → w i = false }

theorem embedFrom_mem_frontSubspace {N : ℕ} (h : N ≤ 8) (v : R N) :
    embedFrom h v ∈ frontSubspace N := by
  intro i hi
  exact embedFrom_apply_ge h v i hi

/-! ## § 5 Concrete embeddings at all small N -/

/-- `R 0 → R 8`: the zero vector. -/
def embed_R0 : R 0 → R 8 := embedFrom (by omega)

theorem embed_R0_eq (v : R 0) : embed_R0 v = (0 : R 8) := by
  have hv : v = 0 := @Subsingleton.elim _ R.R0_subsingleton _ _
  rw [hv]
  exact embedFrom_zero (N := 0) (by omega)

/-- `R 1 → R 8`: the embedding with all but the first coordinate `false`. -/
def embed_R1 : R 1 → R 8 := embedFrom (by omega)

/-- `R 2 → R 8`: the embedding with all but the first two coordinates `false`. -/
def embed_R2 : R 2 → R 8 := embedFrom (by omega)

/-- `R 3 → R 8`: the embedding with all but the first three coordinates `false`. -/
def embed_R3 : R 3 → R 8 := embedFrom (by omega)

/-- `R 4 → R 8`: the "left half" embedding (cf. View B in
    `FiveIdentities.lean`). -/
def embed_R4 : R 4 → R 8 := embedFrom (by omega)

/-- `R 5 → R 8`. -/
def embed_R5 : R 5 → R 8 := embedFrom (by omega)

/-- `R 6 → R 8`. -/
def embed_R6 : R 6 → R 8 := embedFrom (by omega)

/-- `R 7 → R 8`: the "codim-1" embedding. -/
def embed_R7 : R 7 → R 8 := embedFrom (by omega)

/-- `R 8 → R 8`: the identity. -/
def embed_R8 : R 8 → R 8 := id

/-! ## § 6 Right-half embedding for R 4 ↪ R 8 (special case) -/

/-- The "right half" embedding `R 4 ↪ R 8`: copy `v` into positions
    4..7 and leave 0..3 as `false`.  This is the second canonical R 4
    subspace of R 8 (cf. `r8.md` §2.3). -/
def embed_R4_right (v : R 4) : R 8 := fun i =>
  if hLt : i.val < 4 then false else v ⟨i.val - 4, by have := i.isLt; omega⟩

private theorem embed_R4_right_at_lt (v : R 4) (i : Fin 8) (hi : i.val < 4) :
    embed_R4_right v i = false := by
  show (if hLt : i.val < 4 then false else _) = false
  rw [dif_pos hi]

private theorem embed_R4_right_at_ge (v : R 4) (i : Fin 8) (hi : ¬ i.val < 4) :
    embed_R4_right v i = v ⟨i.val - 4, by have := i.isLt; omega⟩ := by
  show (if hLt : i.val < 4 then false else v _) = _
  rw [dif_neg hi]

/-- The right-half embedding is injective. -/
theorem embed_R4_right_injective : Function.Injective embed_R4_right := by
  intro v₁ v₂ heq
  funext i
  rcases i with ⟨k, hk⟩
  have hk' : k + 4 < 8 := by omega
  have hcongr := congrFun heq ⟨k + 4, hk'⟩
  have h1 : ¬ ((⟨k + 4, hk'⟩ : Fin 8).val < 4) := by
    show ¬ (k + 4 < 4); omega
  rw [embed_R4_right_at_ge v₁ ⟨k + 4, hk'⟩ h1,
      embed_R4_right_at_ge v₂ ⟨k + 4, hk'⟩ h1] at hcongr
  have h_idx_eq : (k + 4 - 4 : ℕ) = k := by omega
  have h_idx : (⟨k + 4 - 4, by omega⟩ : Fin 4) = ⟨k, hk⟩ :=
    Fin.ext h_idx_eq
  rw [h_idx] at hcongr
  exact hcongr

/-- The right-half R 4 embedding sends 0 to 0. -/
theorem embed_R4_right_zero : embed_R4_right (0 : R 4) = (0 : R 8) := by
  funext i
  by_cases hi : i.val < 4
  · rw [embed_R4_right_at_lt _ i hi]; rfl
  · rw [embed_R4_right_at_ge _ i hi]; rfl

/-- The right-half R 4 embedding is additive. -/
theorem embed_R4_right_add (u v : R 4) :
    embed_R4_right (u + v) = embed_R4_right u + embed_R4_right v := by
  funext i
  show embed_R4_right (u + v) i
      = Bool.xor (embed_R4_right u i) (embed_R4_right v i)
  by_cases hi : i.val < 4
  · rw [embed_R4_right_at_lt _ i hi, embed_R4_right_at_lt _ i hi,
        embed_R4_right_at_lt _ i hi]
    rfl
  · rw [embed_R4_right_at_ge _ i hi, embed_R4_right_at_ge _ i hi,
        embed_R4_right_at_ge _ i hi]
    rfl

/-! ## § 7 Ceiling sufficiency

The ceiling principle: every algebraic statement about `R N` with
N ≤ 7 has a corresponding statement inside `R 8` (via the embedding).
This is `r8.md` v0.2 Theorem 2.4. -/

/-- The ceiling property: every `R N` with N ≤ 8 admits an
    injective additive embedding into `R 8`. -/
theorem ceiling_property (N : ℕ) (h : N ≤ 8) :
    ∃ φ : R N → R 8, Function.Injective φ
                    ∧ φ 0 = 0
                    ∧ ∀ u v, φ (u + v) = φ u + φ v :=
  ⟨embedFrom h, embedFrom_injective h, embedFrom_zero h, embedFrom_add h⟩

end SSBX.Foundation.R8
