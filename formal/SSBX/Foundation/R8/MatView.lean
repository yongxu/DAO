/-
# Foundation.R8.MatView — R 8 as pair of R 4 cells

Per `r8.md` v0.2 §7, `R 8` admits the matrix-style "pair of R 4 cells"
presentation: every `R 8`-element corresponds to either a 2×4 binary
matrix (= an F_2-linear map `R 4 → R 2`, view D₁ in `FiveIdentities`)
or a 4×2 binary matrix (= an F_2-linear map `R 2 → R 4`, view D₂).

This file packages the **`R 8 ≃ R 4 × R 4`** pair view directly:

* `splitPair w` extracts the two R 4-cells `(c₁, c₂)` where
  `c₁ = w_0 w_1 w_4 w_5` (positions 0,1,4,5 ↦ R 4) and
  `c₂ = w_2 w_3 w_6 w_7` (positions 2,3,6,7 ↦ R 4).  This is the
  "interleaved 2×2-block" pair (cf. `r8.md` §7.1: each R 4-cell is a
  2×2 binary block).
* `joinPair (c₁, c₂)` rebuilds `R 8` from the two cells.

In addition we provide the simpler **left/right halves** view from
`FiveIdentities.viewB` as `splitHalves` here so all `R 4 × R 4`
presentations live in one place.

## Doctrinal anchor

* `r8.md` v0.2 §7.1 (Hom(R 4, R 2) view), §7.2 (Hom(R 2, R 4) view),
  §7.3 (rank distribution 1 + 45 + 210 = 256).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R8.FiveIdentities

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 The left/right halves pair view (re-export of viewB) -/

/-- `R 8 ≃ R 4 × R 4` via left/right halves (cf. View B of
    `FiveIdentities`). -/
def splitHalves : R 8 ≃ R 4 × R 4 := viewB

@[simp] theorem splitHalves_apply (w : R 8) : splitHalves w = viewB w := rfl

/-! ## § 2 The interleaved-block pair view

Per `r8.md` v0.2 §7.1, the canonical "pair of R 4-cells" treats each
R 4-cell as a 2×2 binary block: the first cell is positions
`(0, 1, 4, 5)` (top row + bottom row of column block 1) and the second
cell is positions `(2, 3, 6, 7)` (top row + bottom row of column block 2).

The mapping between flat index `k ∈ Fin 4` and `R 8`-position:

    cell 0:  k = 0 ↦ 0,  k = 1 ↦ 1,  k = 2 ↦ 4,  k = 3 ↦ 5
    cell 1:  k = 0 ↦ 2,  k = 1 ↦ 3,  k = 2 ↦ 6,  k = 3 ↦ 7
-/

/-- The first R 4-cell: positions 0, 1, 4, 5 of `w`. -/
def cellLeft (w : R 8) : R 4 := fun k =>
  match k.val with
  | 0 => w ⟨0, by decide⟩
  | 1 => w ⟨1, by decide⟩
  | 2 => w ⟨4, by decide⟩
  | _ => w ⟨5, by decide⟩

/-- The second R 4-cell: positions 2, 3, 6, 7 of `w`. -/
def cellRight (w : R 8) : R 4 := fun k =>
  match k.val with
  | 0 => w ⟨2, by decide⟩
  | 1 => w ⟨3, by decide⟩
  | 2 => w ⟨6, by decide⟩
  | _ => w ⟨7, by decide⟩

/-- Split `R 8` into the two interleaved R 4-cells. -/
def splitPair (w : R 8) : R 4 × R 4 := (cellLeft w, cellRight w)

/-- Join two R 4-cells back into `R 8` via the interleaved-block layout. -/
def joinPair (p : R 4 × R 4) : R 8 := fun i =>
  match i.val with
  | 0 => p.1 ⟨0, by decide⟩
  | 1 => p.1 ⟨1, by decide⟩
  | 2 => p.2 ⟨0, by decide⟩
  | 3 => p.2 ⟨1, by decide⟩
  | 4 => p.1 ⟨2, by decide⟩
  | 5 => p.1 ⟨3, by decide⟩
  | 6 => p.2 ⟨2, by decide⟩
  | _ => p.2 ⟨3, by decide⟩

@[simp] theorem joinPair_splitPair (w : R 8) : joinPair (splitPair w) = w := by
  funext i
  rcases i with ⟨k, hk⟩
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

@[simp] theorem splitPair_joinPair (p : R 4 × R 4) :
    splitPair (joinPair p) = p := by
  obtain ⟨a, b⟩ := p
  refine Prod.ext ?_ ?_
  · funext i; rcases i with ⟨k, hk⟩
    match k, hk with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  · funext i; rcases i with ⟨k, hk⟩
    match k, hk with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl

/-- The interleaved pair equivalence `R 8 ≃ R 4 × R 4`. -/
def pairEquiv : R 8 ≃ R 4 × R 4 where
  toFun := splitPair
  invFun := joinPair
  left_inv := joinPair_splitPair
  right_inv := splitPair_joinPair

/-! ## § 3 Rank distribution as published values

Per `r8.md` v0.2 §7.3, the rank distribution of `R 8` viewed as a 2×4
matrix is:

* rank 0:   1
* rank 1:  45
* rank 2: 210

Total = 256.  We expose these as `def`s; the explicit Mathlib proof
that the matrix-rank decomposition matches these is application-layer
and out of scope here. -/

/-- Number of rank-0 `2 × 4` F_2 matrices (= the zero matrix only). -/
def rankCount_0 : ℕ := 1

/-- Number of rank-1 `2 × 4` F_2 matrices. -/
def rankCount_1 : ℕ := 45

/-- Number of rank-2 `2 × 4` F_2 matrices. -/
def rankCount_2 : ℕ := 210

/-- The rank counts add up to `|R 8| = 256`. -/
theorem rankCount_sum : rankCount_0 + rankCount_1 + rankCount_2 = 256 := by decide

/-! ## § 4 Sanity: equivalences are inverses -/

@[simp] theorem pairEquiv_to_from (p : R 4 × R 4) :
    pairEquiv (pairEquiv.symm p) = p := pairEquiv.right_inv p

@[simp] theorem pairEquiv_from_to (w : R 8) :
    pairEquiv.symm (pairEquiv w) = w := pairEquiv.left_inv w

end SSBX.Foundation.R8
