/-
# Foundation.R8.FiveIdentities — the five structural identities of R 8

Per `r8.md` v0.2 §1, the carrier `R 8 = Fin 8 → Bool` admits five
structurally equivalent presentations:

* **View A — flat**     `R 8 = F_2^8`            (the canonical layout)
* **View B — sum** ★    `R 8 = R 4 ⊕ R 4`        (L/R halves; key for pair semantics)
* **View C — 4-fold**   `R 8 = R 2^{⊕ 4}`        (four R 2-blocks; symplectic)
* **View D — Hom** ★    `R 8 = Hom_F₂(R 4, R 2)` (2×4 matrix view)
                       `R 8 = Hom_F₂(R 2, R 4)` (4×2 matrix view)
* **View E — flat mat** `R 8 = Mat_{2×4}(F_2)`   (matrix reshape of A)

The "tensor identity" `R 4 ⊗ R 4 = R 16` is **not** an identity for
`R 8`; the squaring tower uses direct sum (per `r8.md` §1.6).

All identities are presented as `Equiv` between `R 8` and the target
type plus cardinality witnesses; the underlying group structure is
inherited from `R N` (see `Foundation/R/Basic.lean`).

## Doctrinal anchor

* `r8.md` v0.2 §1 (five structural identities), §1.6 (tensor vs sum),
  §1.7 (summary table).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R.Hom
import Mathlib.Logic.Equiv.Basic

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 View A — the flat F_2^8 layout

By definition `R 8 = Fin 8 → Bool`.  This is the canonical layout;
no Equiv is needed — `R 8` is literally `F_2^8`. -/

/-- View A: `R 8` is by definition the flat 8-bit space. -/
theorem viewA_card : Fintype.card (R 8) = 2 ^ 8 := R.card_eq 8

/-- The cardinality of `R 8` is 256. -/
theorem viewA_card_256 : Fintype.card (R 8) = 256 := R.R8_card

/-! ## § 2 View B — direct sum `R 4 ⊕ R 4` ★

This is the canonical "left half / right half" presentation that
underlies the squaring tower step `R 8 = R 4 ⊕ R 4`. -/

/-- View B: `R 8 ≃ R 4 × R 4`.  The first 4 coordinates form the left
    block; the last 4 coordinates form the right block. -/
def viewB : R 8 ≃ R 4 × R 4 :=
  show R (4 + 4) ≃ R 4 × R 4 from R.directSumEquiv (N := 4) (M := 4)

/-- View B: explicit "split into halves" function. -/
def splitLR (w : R 8) : R 4 × R 4 := viewB w

/-- View B: explicit "join halves" function. -/
def joinLR (u v : R 4) : R 8 := viewB.symm (u, v)

@[simp] theorem splitLR_joinLR (u v : R 4) : splitLR (joinLR u v) = (u, v) :=
  viewB.right_inv (u, v)

@[simp] theorem joinLR_splitLR (w : R 8) : joinLR (splitLR w).1 (splitLR w).2 = w := by
  show viewB.symm (viewB w) = w
  exact viewB.left_inv w

/-- View B cardinality identity: `|R 8| = |R 4| · |R 4|`. -/
theorem viewB_card : Fintype.card (R 8) = Fintype.card (R 4) * Fintype.card (R 4) := by
  rw [Fintype.card_congr viewB, Fintype.card_prod]

/-- The left half of `R 8`: 4 coordinates 0..3. -/
def leftHalf (w : R 8) : R 4 := (splitLR w).1

/-- The right half of `R 8`: 4 coordinates 4..7. -/
def rightHalf (w : R 8) : R 4 := (splitLR w).2

@[simp] theorem leftHalf_apply (w : R 8) (i : Fin 4) :
    leftHalf w i = w (Fin.castAdd 4 i) := rfl

@[simp] theorem rightHalf_apply (w : R 8) (i : Fin 4) :
    rightHalf w i = w (Fin.natAdd 4 i) := rfl

/-! ## § 3 View C — 4-fold sum `R 2^{⊕ 4}`

The four 2-bit blocks (positions 0-1, 2-3, 4-5, 6-7).  This is the
view used by the symplectic σ-form (`r8.md` §6.2). -/

/-- The first 2-block of `R 8`. -/
def block0 (w : R 8) : R 2 := fun i => w ⟨i.val, by have := i.isLt; omega⟩

/-- The second 2-block of `R 8`. -/
def block1 (w : R 8) : R 2 := fun i => w ⟨i.val + 2, by have := i.isLt; omega⟩

/-- The third 2-block of `R 8`. -/
def block2 (w : R 8) : R 2 := fun i => w ⟨i.val + 4, by have := i.isLt; omega⟩

/-- The fourth 2-block of `R 8`. -/
def block3 (w : R 8) : R 2 := fun i => w ⟨i.val + 6, by have := i.isLt; omega⟩

/-- View C: extract all four 2-blocks. -/
def viewC_toFun (w : R 8) : R 2 × R 2 × R 2 × R 2 :=
  (block0 w, block1 w, block2 w, block3 w)

/-- View C: rebuild `R 8` from four 2-blocks. -/
def viewC_invFun (p : R 2 × R 2 × R 2 × R 2) : R 8 := fun i =>
  if h0 : i.val < 2 then p.1 ⟨i.val, h0⟩
  else if h1 : i.val < 4 then p.2.1 ⟨i.val - 2, by omega⟩
  else if h2 : i.val < 6 then p.2.2.1 ⟨i.val - 4, by omega⟩
  else p.2.2.2 ⟨i.val - 6, by
    have := i.isLt
    omega⟩

/-- View C: `R 8 ≃ R 2 × R 2 × R 2 × R 2`.  Four R_2-blocks. -/
def viewC : R 8 ≃ R 2 × R 2 × R 2 × R 2 where
  toFun := viewC_toFun
  invFun := viewC_invFun
  left_inv := by
    intro w
    funext i
    show viewC_invFun (viewC_toFun w) i = w i
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
  right_inv := by
    intro p
    obtain ⟨a, b, c, d⟩ := p
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    all_goals (funext i; rcases i with ⟨k, hk⟩; match k, hk with
      | 0, _ => rfl
      | 1, _ => rfl)

/-- View C cardinality: `|R 8| = |R 2|^4`. -/
theorem viewC_card :
    Fintype.card (R 8) =
      Fintype.card (R 2) * Fintype.card (R 2) *
        Fintype.card (R 2) * Fintype.card (R 2) := by
  have h : Fintype.card (R 8) = Fintype.card (R 2 × R 2 × R 2 × R 2) :=
    Fintype.card_congr viewC
  rw [h]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  ac_rfl

/-! ## § 4 View D — `R 8 = Hom_F₂(R 4, R 2)` ★

The "Hom block view".  An `R 8`-element is identified with a 2×4
binary matrix, i.e. an F_2-linear map `R 4 → R 2`. -/

/-- View D₁: `R 8` as a 2×4 binary matrix (row i = pos 4·i .. 4·i+3). -/
def asMat2x4 (w : R 8) (i : Fin 2) (j : Fin 4) : Bool :=
  w ⟨4 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

/-- View D₁ inverse: assemble `R 8` from a 2×4 binary matrix. -/
def fromMat2x4 (M : Fin 2 → Fin 4 → Bool) : R 8 := fun k =>
  M ⟨k.val / 4, by have := k.isLt; omega⟩
    ⟨k.val % 4, by have := k.isLt; omega⟩

/-- View D₁ equivalence: `R 8 ≃ LinHom 4 2 = Fin 2 → Fin 4 → Bool`. -/
def viewD_2x4 : R 8 ≃ R.LinHom 4 2 where
  toFun := asMat2x4
  invFun := fromMat2x4
  left_inv := by
    intro w
    funext k
    show fromMat2x4 (asMat2x4 w) k = w k
    rcases k with ⟨n, hn⟩
    show w ⟨4 * (n / 4) + n % 4, _⟩ = w ⟨n, hn⟩
    congr 1
    apply Fin.ext
    show 4 * (n / 4) + n % 4 = n
    omega
  right_inv := by
    intro M
    funext i j
    show asMat2x4 (fromMat2x4 M) i j = M i j
    rcases i with ⟨ii, hii⟩
    rcases j with ⟨jj, hjj⟩
    show M ⟨(4 * ii + jj) / 4, _⟩ ⟨(4 * ii + jj) % 4, _⟩ = M ⟨ii, hii⟩ ⟨jj, hjj⟩
    have h1 : (4 * ii + jj) / 4 = ii := by omega
    have h2 : (4 * ii + jj) % 4 = jj := by omega
    congr 1
    · apply Fin.ext; exact h1
    apply Fin.ext; exact h2

/-- View D₁ cardinality: `|R 8| = |LinHom 4 2| = 2^8`. -/
theorem viewD_2x4_card : Fintype.card (R 8) = Fintype.card (R.LinHom 4 2) := by
  rw [R.LinHom.card_linHom, R.card_eq]

/-- View D₂: `R 8` as a 4×2 binary matrix (row i = pos 2·i, 2·i+1). -/
def asMat4x2 (w : R 8) (i : Fin 4) (j : Fin 2) : Bool :=
  w ⟨2 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

/-- View D₂ inverse: assemble `R 8` from a 4×2 binary matrix. -/
def fromMat4x2 (M : Fin 4 → Fin 2 → Bool) : R 8 := fun k =>
  M ⟨k.val / 2, by have := k.isLt; omega⟩
    ⟨k.val % 2, by have := k.isLt; omega⟩

/-- View D₂ equivalence: `R 8 ≃ LinHom 2 4 = Fin 4 → Fin 2 → Bool`. -/
def viewD_4x2 : R 8 ≃ R.LinHom 2 4 where
  toFun := asMat4x2
  invFun := fromMat4x2
  left_inv := by
    intro w
    funext k
    show fromMat4x2 (asMat4x2 w) k = w k
    rcases k with ⟨n, hn⟩
    show w ⟨2 * (n / 2) + n % 2, _⟩ = w ⟨n, hn⟩
    congr 1
    apply Fin.ext
    show 2 * (n / 2) + n % 2 = n
    omega
  right_inv := by
    intro M
    funext i j
    show asMat4x2 (fromMat4x2 M) i j = M i j
    rcases i with ⟨ii, hii⟩
    rcases j with ⟨jj, hjj⟩
    show M ⟨(2 * ii + jj) / 2, _⟩ ⟨(2 * ii + jj) % 2, _⟩ = M ⟨ii, hii⟩ ⟨jj, hjj⟩
    have h1 : (2 * ii + jj) / 2 = ii := by omega
    have h2 : (2 * ii + jj) % 2 = jj := by omega
    congr 1
    · apply Fin.ext; exact h1
    apply Fin.ext; exact h2

/-- View D₂ cardinality: `|R 8| = |LinHom 2 4| = 2^8`. -/
theorem viewD_4x2_card : Fintype.card (R 8) = Fintype.card (R.LinHom 2 4) := by
  rw [R.LinHom.card_linHom, R.card_eq]

/-! ## § 5 View E — flat-matrix reshapes

These are equivalent to view A; we just record the available shapes
for completeness.  Each one is a reshape of the 8 binary entries. -/

/-- `R 8 ≃ Fin 8 → Bool` (the underlying definition, recorded as Equiv). -/
def viewE_flat : R 8 ≃ (Fin 8 → Bool) := Equiv.refl _

/-- The cardinality of any reshape of `R 8` is 256. -/
theorem viewE_card : Fintype.card (R 8) = 256 := R.R8_card

/-! ## § 6 Tensor vs direct sum distinction

Per `r8.md` §1.6: the squaring tower goes by *direct sum*, not tensor.
`R 4 ⊕ R 4 = R 8` (cardinality 16·16 = 256), while
`R 4 ⊗ R 4 = R 16` (cardinality 2^16 = 65536). -/

/-- Direct sum cardinality at the R 4 squaring: `|R 4 ⊕ R 4| = |R 4|^2 = 256`. -/
theorem directSum_R4_card :
    Fintype.card (R 8) = Fintype.card (R 4) * Fintype.card (R 4) := viewB_card

/-- The tensor of R 4 with itself has dimension 4·4 = 16, *not* 8. -/
theorem tensor_R4_dim : Fintype.card (R 16) = 2 ^ 16 := R.card_eq 16

/-- `|R 4 ⊗ R 4|` and `|R 4 ⊕ R 4|` only coincide when one factor is
    R 2 (the unique case where `N + N = N · N`).  At N = 4 they differ:
    direct-sum view gives R 8 (256), tensor view gives R 16 (65536). -/
theorem tensor_neq_directSum_at_R4 :
    Fintype.card (R 16) ≠ Fintype.card (R 8) := by
  rw [R.card_eq, R.card_eq]
  decide

end SSBX.Foundation.R8
