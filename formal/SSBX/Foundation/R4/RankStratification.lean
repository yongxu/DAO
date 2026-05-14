/-
# Foundation.R4.RankStratification — rank 0 / 1 / 2 classification on R 4

Per `r4.md` v0.2 §4 ("rank stratification"):

`R 4`, viewed as `Mat_{2×2}(F_2) = End_{F_2}(R 2)`, decomposes into
three rank-strata:

* **rank 0** — 1 element  (the zero matrix `oooo`)
* **rank 1** — 9 elements (det = 0 but matrix ≠ 0)
* **rank 2** — 6 elements (det = 1, i.e. invertible)

The det over `F_2` of `M_w = [[w₀, w₁], [w₂, w₃]]` is `w₀ ∧ w₃ ⊕ w₁ ∧ w₂`,
so the rank is determined by two Bool inputs (`isZero`, `det`).

R 4 is the **first** R-Family layer with rank stratification — the
companion of `End(R 2) = R 4` self-closure (§8 of r4.md).

## Doctrinal anchor

* `r4.md` v0.2 §4.1 (rank-0), §4.2 (rank-1 9 elements), §4.3 (rank-2 6 = GL(2,F_2)).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R4.Enumeration

namespace SSBX.Foundation.R4

open SSBX.Foundation.R

/-! ## § 1 Determinant of the 2×2 matrix view

`M_w = [[w₀, w₁], [w₂, w₃]]`, so `det M_w = w₀ ∧ w₃ ⊕ w₁ ∧ w₂` over
`F_2`.  This Bool-valued function is the rank-2 indicator. -/

/-- The determinant of `R 4` viewed as a 2×2 matrix.
    `det w = w₀ ∧ w₃ ⊕ w₁ ∧ w₂` (over `F_2`). -/
def det (w : R 4) : Bool :=
  Bool.xor
    (Bool.and (w ⟨0, by decide⟩) (w ⟨3, by decide⟩))
    (Bool.and (w ⟨1, by decide⟩) (w ⟨2, by decide⟩))

/-- `w` is the zero matrix iff all four bits are `false`. -/
def isZero (w : R 4) : Bool :=
  Bool.not (Bool.or (Bool.or (w ⟨0, by decide⟩) (w ⟨1, by decide⟩))
                    (Bool.or (w ⟨2, by decide⟩) (w ⟨3, by decide⟩)))

/-! ## § 2 The rank function

Three strata:

* `rank w = 0` iff `isZero w`
* `rank w = 2` iff `det w = true`
* `rank w = 1` otherwise (det 0 but not zero matrix)
-/

/-- The matrix rank of `R 4 = Mat_{2×2}(F_2)`. -/
def rank (w : R 4) : Fin 3 :=
  if isZero w = true then ⟨0, by decide⟩
  else if det w = true then ⟨2, by decide⟩
  else ⟨1, by decide⟩

/-! ## § 3 Rank-stratum predicates -/

/-- The rank-0 stratum: just the zero matrix. -/
def IsRank0 (w : R 4) : Prop := rank w = ⟨0, by decide⟩

/-- The rank-1 stratum: non-zero matrices with det 0. -/
def IsRank1 (w : R 4) : Prop := rank w = ⟨1, by decide⟩

/-- The rank-2 stratum: matrices with det 1 (invertibles). -/
def IsRank2 (w : R 4) : Prop := rank w = ⟨2, by decide⟩

instance instDecidableIsRank0 (w : R 4) : Decidable (IsRank0 w) := by
  unfold IsRank0; infer_instance

instance instDecidableIsRank1 (w : R 4) : Decidable (IsRank1 w) := by
  unfold IsRank1; infer_instance

instance instDecidableIsRank2 (w : R 4) : Decidable (IsRank2 w) := by
  unfold IsRank2; infer_instance

/-! ## § 4 Witnesses at the 16 atoms

Each of the 16 atoms gets its rank computed concretely by `decide`. -/

example : rank oooo = ⟨0, by decide⟩ := by decide
example : rank xoox = ⟨2, by decide⟩ := by decide
example : rank oxxo = ⟨2, by decide⟩ := by decide
example : rank xxxx = ⟨1, by decide⟩ := by decide

theorem oooo_rank0 : IsRank0 oooo := by decide
theorem xoox_rank2 : IsRank2 xoox := by decide
theorem oxxo_rank2 : IsRank2 oxxo := by decide
theorem oxxx_rank2 : IsRank2 oxxx := by decide
theorem xoxx_rank2 : IsRank2 xoxx := by decide
theorem xxox_rank2 : IsRank2 xxox := by decide
theorem xxxo_rank2 : IsRank2 xxxo := by decide

/-! ## § 5 The 1 + 9 + 6 partition

The 16 atoms split into 1 rank-0, 9 rank-1, and 6 rank-2 elements.
We materialize each stratum as a `Finset (R 4)` derived from
`list16` and verify the cardinality. -/

/-- The rank-0 stratum as a `Finset (R 4)`. -/
def rank0Set : Finset (R 4) :=
  (Finset.univ : Finset (R 4)).filter IsRank0

/-- The rank-1 stratum as a `Finset (R 4)`. -/
def rank1Set : Finset (R 4) :=
  (Finset.univ : Finset (R 4)).filter IsRank1

/-- The rank-2 stratum as a `Finset (R 4)`. -/
def rank2Set : Finset (R 4) :=
  (Finset.univ : Finset (R 4)).filter IsRank2

/-- |rank-0 stratum| = 1. -/
theorem rank0_card : rank0Set.card = 1 := by decide

/-- |rank-1 stratum| = 9. -/
theorem rank1_card : rank1Set.card = 9 := by decide

/-- |rank-2 stratum| = 6.  These are exactly the elements of
    `GL(2, F_2) ⊂ R 4`; see `GL2Embedding.lean`. -/
theorem rank2_card : rank2Set.card = 6 := by decide

/-- The three strata are pairwise disjoint. -/
theorem rank_strata_disjoint01 : Disjoint rank0Set rank1Set := by
  rw [Finset.disjoint_left]
  intro w h0 h1
  rw [rank0Set, Finset.mem_filter] at h0
  rw [rank1Set, Finset.mem_filter] at h1
  have hr0 : rank w = ⟨0, by decide⟩ := h0.2
  have hr1 : rank w = ⟨1, by decide⟩ := h1.2
  rw [hr0] at hr1
  exact absurd hr1 (by decide)

theorem rank_strata_disjoint02 : Disjoint rank0Set rank2Set := by
  rw [Finset.disjoint_left]
  intro w h0 h2
  rw [rank0Set, Finset.mem_filter] at h0
  rw [rank2Set, Finset.mem_filter] at h2
  have hr0 : rank w = ⟨0, by decide⟩ := h0.2
  have hr2 : rank w = ⟨2, by decide⟩ := h2.2
  rw [hr0] at hr2
  exact absurd hr2 (by decide)

theorem rank_strata_disjoint12 : Disjoint rank1Set rank2Set := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  rw [rank1Set, Finset.mem_filter] at h1
  rw [rank2Set, Finset.mem_filter] at h2
  have hr1 : rank w = ⟨1, by decide⟩ := h1.2
  have hr2 : rank w = ⟨2, by decide⟩ := h2.2
  rw [hr1] at hr2
  exact absurd hr2 (by decide)

/-- The three strata sum to `|R 4| = 16`. -/
theorem rank_card_sum :
    rank0Set.card + rank1Set.card + rank2Set.card = 16 := by
  rw [rank0_card, rank1_card, rank2_card]

end SSBX.Foundation.R4
