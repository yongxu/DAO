/-
# Wen.Xiang.Dot — F₂-bilinear dot product on `X n`

`wen-algebra` v0.4 §5: the canonical pairing on the 𝕏ⁿ tower.  Per §5.2:

    ⟨U, V⟩ := Σᵢ ⟨uᵢ, vᵢ⟩_𝕏 ∈ F₂

i.e. the orthogonal direct sum of the atomic `Image.dot` over each
image-coordinate.  This file delivers:

* `X.dot` — recursive definition mirroring the squaring chain.
* `dot_symm` — symmetry (§5.3.1).
* `dot_origin_left / dot_origin_right` — the origin annihilates.
* `X.basisAlpha / X.basisBeta` — the canonical basis (§4.2):
    `basisAlpha i` has `Image.xo` at coordinate `i`, `Image.oo` elsewhere;
    `basisBeta i` has `Image.ox` at coordinate `i`.
* `dot_basisAlpha / dot_basisBeta` — basis pairings recover coordinates
  (§5.4 Sense 1).
* `coord_independent_recovery` — the full v0.4 §5.4 Sense 1 + Sense 2
  result: every `U : X n` is reconstructed from its `2n` basis pairings,
  parallel and independent across image factors.
* `nondegenerate` / `nondegenerate_iff` / `nondegenerate_iff_coord` —
  v0.4 §5.3.3 non-degeneracy in three forms (forward implication, iff
  with origin, iff with the per-coordinate `∀ i, U i = .oo`
  formulation).

The dot is structurally recursive on `n` (peeling off coordinate 0 via
`Fin.tail`), which makes induction on `n` the natural proof strategy.
-/

import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.X
import Mathlib.Data.Fin.Tuple.Basic

namespace SSBX.Foundation.Wen.Xiang

namespace X

/-! ## § 1 Bool/`Bit` helpers (avoid Mathlib simp-lemma name churn) -/

private theorem bit_xor_false (b : Bit) : Bool.xor b false = b := by
  cases b <;> rfl

private theorem false_xor_bit (b : Bit) : Bool.xor false b = b := by
  cases b <;> rfl

/-! ## § 2 The dot product (recursive definition) -/

/-- F₂-bilinear dot product on `X n`: orthogonal direct sum of the
    atomic `Image.dot` per coordinate.

    Defined recursively by peeling off coordinate 0; the recursion is
    structural and makes induction on `n` a one-liner. -/
def dot : ∀ {n : Nat}, X n → X n → Bit
  | 0,     _, _ => false
  | _ + 1, U, V =>
      Bool.xor (Image.dot (U 0) (V 0))
               (dot (Fin.tail U) (Fin.tail V))

@[simp] theorem dot_zero (U V : X 0) : dot U V = false := rfl

theorem dot_succ {n : Nat} (U V : X (n + 1)) :
    dot U V = Bool.xor (Image.dot (U 0) (V 0))
                       (dot (Fin.tail U) (Fin.tail V)) := rfl

/-! ## § 3 Symmetry and the origin -/

theorem dot_symm {n : Nat} (U V : X n) : dot U V = dot V U := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [dot_succ, dot_succ, Image.dot_symm (U 0) (V 0), ih (Fin.tail U) (Fin.tail V)]

theorem dot_origin_right {n : Nat} (U : X n) : dot U (origin n) = false := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [dot_succ]
    have h_zero : (origin (k + 1)) 0 = Image.oo := rfl
    have h_tail : Fin.tail (origin (k + 1)) = origin k := rfl
    rw [h_zero, h_tail, Image.dot_oo_right, ih (Fin.tail U)]
    rfl

theorem dot_origin_left {n : Nat} (U : X n) : dot (origin n) U = false := by
  rw [dot_symm]
  exact dot_origin_right U

/-! ## § 4 Canonical basis (`wen-algebra` v0.4 §4.2)

The basis `B = {E_α(i), E_β(i)}_{i = 1..n}` of `X n` as a `2n`-dim
F₂-vector space.  Each basis element has the corresponding `Image`
basis atom (`xo` or `ox`) at coordinate `i` and `Image.oo` elsewhere. -/

/-- α-basis vector at coordinate `i`: `Image.xo` at position `i`,
    `Image.oo` elsewhere.  This is `E_i^{(α)}` of v0.4 §4.2. -/
def basisAlpha {n : Nat} (i : Fin n) : X n :=
  fun j => if i = j then .xo else .oo

/-- β-basis vector at coordinate `i`: `Image.ox` at position `i`,
    `Image.oo` elsewhere.  This is `E_i^{(β)}` of v0.4 §4.2. -/
def basisBeta {n : Nat} (i : Fin n) : X n :=
  fun j => if i = j then .ox else .oo

@[simp] theorem basisAlpha_self {n : Nat} (i : Fin n) :
    basisAlpha i i = .xo := by simp [basisAlpha]

@[simp] theorem basisBeta_self {n : Nat} (i : Fin n) :
    basisBeta i i = .ox := by simp [basisBeta]

theorem basisAlpha_other {n : Nat} {i j : Fin n} (h : i ≠ j) :
    basisAlpha i j = .oo := by simp [basisAlpha, h]

theorem basisBeta_other {n : Nat} {i j : Fin n} (h : i ≠ j) :
    basisBeta i j = .oo := by simp [basisBeta, h]

/-! ### Tail decomposition of the basis vectors -/

theorem tail_basisAlpha_zero {n : Nat} :
    Fin.tail (basisAlpha (n := n + 1) 0) = origin n := by
  funext j
  show (if (0 : Fin (n + 1)) = j.succ then Image.xo else Image.oo) = Image.oo
  have h : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  simp [h]

theorem tail_basisAlpha_succ {n : Nat} (j : Fin n) :
    Fin.tail (basisAlpha (n := n + 1) j.succ) = basisAlpha j := by
  funext k
  show (if (j.succ : Fin (n + 1)) = k.succ then Image.xo else Image.oo)
        = (if j = k then Image.xo else Image.oo)
  by_cases h : j = k
  · simp [h]
  · have h' : (j.succ : Fin (n + 1)) ≠ k.succ := fun heq =>
      h (Fin.succ_injective _ heq)
    simp [h, h']

theorem tail_basisBeta_zero {n : Nat} :
    Fin.tail (basisBeta (n := n + 1) 0) = origin n := by
  funext j
  show (if (0 : Fin (n + 1)) = j.succ then Image.ox else Image.oo) = Image.oo
  have h : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  simp [h]

theorem tail_basisBeta_succ {n : Nat} (j : Fin n) :
    Fin.tail (basisBeta (n := n + 1) j.succ) = basisBeta j := by
  funext k
  show (if (j.succ : Fin (n + 1)) = k.succ then Image.ox else Image.oo)
        = (if j = k then Image.ox else Image.oo)
  by_cases h : j = k
  · simp [h]
  · have h' : (j.succ : Fin (n + 1)) ≠ k.succ := fun heq =>
      h (Fin.succ_injective _ heq)
    simp [h, h']

/-! ## § 5 Basis pairings recover coordinates (§5.4 Sense 1) -/

theorem dot_basisAlpha {n : Nat} (U : X n) (i : Fin n) :
    dot U (basisAlpha i) = (U i).alpha := by
  induction n with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · -- i = 0
      rw [dot_succ, basisAlpha_self, tail_basisAlpha_zero, dot_origin_right,
          Image.dot_xo_right, bit_xor_false]
    · -- i = j.succ
      rw [dot_succ, basisAlpha_other (Fin.succ_ne_zero j),
          tail_basisAlpha_succ, Image.dot_oo_right, false_xor_bit]
      exact ih (Fin.tail U) j

theorem dot_basisBeta {n : Nat} (U : X n) (i : Fin n) :
    dot U (basisBeta i) = (U i).beta := by
  induction n with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · -- i = 0
      rw [dot_succ, basisBeta_self, tail_basisBeta_zero, dot_origin_right,
          Image.dot_ox_right, bit_xor_false]
    · -- i = j.succ
      rw [dot_succ, basisBeta_other (Fin.succ_ne_zero j),
          tail_basisBeta_succ, Image.dot_oo_right, false_xor_bit]
      exact ih (Fin.tail U) j

/-! ## § 6 Coordinate-independent recovery (§5.4 Sense 1 + Sense 2)

Given any `U : X n`, the two atomic-basis pairings at coordinate `i`
suffice to reconstruct `U i` — and the recovery is **parallel** across
image factors (no cross-talk).  This is the v0.4 hallmark of typed
self-duality on the 𝕏ⁿ tower (§5.4). -/

/-- Coordinate-independent recovery of `U i` from its two basis
    pairings.  Per `wen-algebra` v0.4 §5.4, this expresses both Sense 1
    (linear, basis-driven recovery) and Sense 2 (image-typed,
    component-wise recovery): each image coordinate is reconstructed
    from **only its own** two basis pairings, with no cross-coordinate
    information mixing. -/
theorem coord_independent_recovery {n : Nat} (U : X n) (i : Fin n) :
    U i = Image.ofBits (dot U (basisAlpha i)) (dot U (basisBeta i)) := by
  rw [dot_basisAlpha, dot_basisBeta]
  exact (Image.ofBits_alpha_beta (U i)).symm

/-! ## § 7 Non-degeneracy (§5.3.3)

`X n` is non-degenerate under `dot`: `U` pairs trivially against
every `V` *iff* `U` is the origin.  Direct corollary of the basis
recovery theorems.  The iff form `nondegenerate_iff` matches the v0.4
§6.1 specification verbatim; `nondegenerate_iff_coord` is its
per-coordinate restatement. -/

theorem dot_eq_zero_of_eq_origin {n : Nat} (U V : X n) (hU : U = origin n) :
    dot U V = false := by
  subst hU
  exact dot_origin_left V

theorem nondegenerate {n : Nat} (U : X n) :
    (∀ V : X n, dot U V = false) → U = origin n := by
  intro h
  funext i
  have hα : (U i).alpha = false := by
    rw [← dot_basisAlpha U i]; exact h (basisAlpha i)
  have hβ : (U i).beta = false := by
    rw [← dot_basisBeta U i]; exact h (basisBeta i)
  show U i = .oo
  rw [← Image.ofBits_alpha_beta (U i), hα, hβ]
  rfl

/-- Non-degeneracy as an iff, matching `wen-algebra` v0.4 §6.1's specification:

      (∀ V, dot U V = 0)  ↔  U = origin

    The forward direction is `nondegenerate`; the reverse is
    `dot_eq_zero_of_eq_origin`.  Together they witness that `dot`
    detects the origin exactly. -/
theorem nondegenerate_iff {n : Nat} (U : X n) :
    (∀ V : X n, dot U V = false) ↔ U = origin n :=
  ⟨nondegenerate U, fun hU V => dot_eq_zero_of_eq_origin U V hU⟩

/-- Per-coordinate restatement of non-degeneracy (v0.4 §6.1 form): the origin
    is exactly the cell whose every image-coordinate is `Image.oo` (= 道). -/
theorem nondegenerate_iff_coord {n : Nat} (U : X n) :
    (∀ V : X n, dot U V = false) ↔ ∀ i : Fin n, U i = .oo := by
  rw [nondegenerate_iff]
  exact ⟨fun h i => by rw [h]; rfl, fun h => funext h⟩

end X

end SSBX.Foundation.Wen.Xiang
