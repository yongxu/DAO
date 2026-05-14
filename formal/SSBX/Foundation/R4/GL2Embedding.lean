/-
# Foundation.R4.GL2Embedding — the 6 rank-2 elements = GL(2, F_2) ≃ S_3

Per `r4.md` v0.2 §5 ("GL(2, F_2) ≃ S_3 inside R 4"):

The 6 rank-2 (invertible) elements of `R 4` form a subset of size 6
that — under the matrix-product composition (defined in `EndR2.lean`)
— is isomorphic to `GL(2, F_2) ≃ S_3`.  These are the **automorphisms
of R 2** internalized as elements of `R 4`:

| element | matrix | S_3 element | order |
|---------|--------|-------------|-------|
| `xoox`  | id     | identity     | 1     |
| `oxxo`  | swap   | involution   | 2     |
| `xxox`  | shear₁ | involution   | 2     |
| `xoxx`  | shear₂ | involution   | 2     |
| `oxxx`  | rot₊   | 3-cycle      | 3     |
| `xxxo`  | rot₋   | 3-cycle      | 3     |

This file fixes the 6-element set as `gl2List` plus the canonical
identity / involutions / rotations decomposition.  Closure under
`compose` (and hence the actual group structure) is established in
`EndR2.lean` once the matrix product is available.

## Doctrinal anchor

* `r4.md` v0.2 §5.1 (6 rank-2 elements table), §5.2 (S_3 structure),
  §5.4 (Aut(R 2) → R 4 embedding ι).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Aut
import SSBX.Foundation.R4.Enumeration
import SSBX.Foundation.R4.RankStratification

namespace SSBX.Foundation.R4

open SSBX.Foundation.R

/-! ## § 1 The six rank-2 elements as a canonical list -/

/-- The 6 rank-2 (invertible) elements of `R 4`, in canonical order:

    identity → involutions → rotations. -/
def gl2List : List (R 4) :=
  [ xoox,           -- identity         (order 1)
    oxxo, xxox, xoxx,  -- 3 involutions (order 2)
    oxxx, xxxo ]    -- 2 rotations     (order 3)

@[simp] theorem gl2List_length : gl2List.length = 6 := rfl

/-- The 6 rank-2 elements are all distinct. -/
theorem gl2List_nodup : gl2List.Nodup := by decide

/-! ## § 2 Each entry is rank-2 -/

theorem gl2List_subset_rank2 :
    ∀ w ∈ gl2List, IsRank2 w := by
  intro w h
  simp [gl2List, List.mem_cons] at h
  rcases h with h | h | h | h | h | h
  · subst h; exact xoox_rank2
  · subst h; exact oxxo_rank2
  · subst h; exact xxox_rank2
  · subst h; exact xoxx_rank2
  · subst h; exact oxxx_rank2
  · subst h; exact xxxo_rank2

/-! ## § 3 |gl2List| = |GL(2, F_2)|

The cardinality matches Mathlib's GL formula at N = 2: per
`Foundation/R/Aut.lean §3`, `card_GL 2 = 6`. -/

theorem gl2List_card_eq_GL : gl2List.length = R.card_GL 2 := by
  rw [gl2List_length, R.card_GL_two]

/-! ## § 4 S_3 structural roles

We label the six elements by their abstract S_3 roles. -/

/-- The identity of GL(2, F_2): `[[1,0],[0,1]]` = `xoox`. -/
def gl2_id : R 4 := xoox

/-- The swap involution: `[[0,1],[1,0]]` = `oxxo`. -/
def gl2_swap : R 4 := oxxo

/-- Upper-triangular shear: `[[1,1],[0,1]]` = `xxox`. -/
def gl2_shear1 : R 4 := xxox

/-- Lower-triangular shear: `[[1,0],[1,1]]` = `xoxx`. -/
def gl2_shear2 : R 4 := xoxx

/-- Forward 3-cycle: `[[0,1],[1,1]]` = `oxxx`. -/
def gl2_rotPlus : R 4 := oxxx

/-- Backward 3-cycle: `[[1,1],[1,0]]` = `xxxo`. -/
def gl2_rotMinus : R 4 := xxxo

/-! ## § 5 The role list matches `gl2List` -/

example : gl2List =
    [gl2_id, gl2_swap, gl2_shear1, gl2_shear2, gl2_rotPlus, gl2_rotMinus] := rfl

/-! ## § 6 The role list distinctness -/

theorem gl2_roles_nodup :
    [gl2_id, gl2_swap, gl2_shear1, gl2_shear2,
     gl2_rotPlus, gl2_rotMinus].Nodup := by
  decide

end SSBX.Foundation.R4
