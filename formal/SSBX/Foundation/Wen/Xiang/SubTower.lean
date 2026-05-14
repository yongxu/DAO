/-
# Wen.Xiang.SubTower — the {道, 错综}ⁿ intrinsic sub-tower of `X n`

Per `wen-algebra` v0.4 §3.5, every `X n` carries a canonical diagonal
sub-group

    {道, 错综}ⁿ  ⊂  𝕏ⁿ

— the cells whose every image-coordinate is `.oo` (= 道) or `.xx` (=
错综).  This sub-tower has cardinality `2ⁿ` and is an intrinsic feature
of `X` (not externally grafted).  Per §3.5.3, it admits three
equivalent characterisations on `Image`:

1. **Homomorphism preservation** — `{.oo, .xx}` is the unique `Z/2`
   subgroup of `Image` preserving demorgan / contrapositive symmetry.
2. **Geometric isotropy** — `{.oo, .xx}` is the zero-locus of the
   self-pairing `dot v v = v_α + v_β = L v` (= `Image.dot.self`).
3. **Linear kernel** — `{.oo, .xx}` is exactly `ker (Image.L)`.

This module exposes the sub-tower as a predicate on `X n`, computes its
cardinality (= `2ⁿ`), and proves the kernel characterisation via the
`Symplectic.Image.L` of `Symplectic.lean` (= sense (3) above).

## Connection to other Layers

* §5.6.3 dot decomposition: on the sub-tower (where `L = 0`)
  `dot` and `σ` agree pointwise.
* §5.7.7 Arf zero-loci: `q0⁻¹(0)` and `q1⁻¹(0)` both contain `.oo` and
  `.xx`; the sub-tower is the geometric anchor underneath the
  Arf-invariant story.
* §3.6.4 quotient: `X n / {道, 错综}ⁿ ≅ F₂ⁿ` — the "polarity-quotient"
  view of `X n` as `F₂ⁿ` extended by the diagonal.
-/

import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.X
import SSBX.Foundation.Wen.Xiang.Symplectic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

namespace SSBX.Foundation.Wen.Xiang

namespace Image

/-! ## § 1 The atomic sub-tower predicate -/

/-- An `Image` atom is in the sub-tower iff it is `.oo` (= 道) or `.xx`
    (= 错综).  Equivalently, `L v = 0`. -/
def InSubTower (v : Image) : Prop := v = .oo ∨ v = .xx

instance instDecidableInSubTower (v : Image) : Decidable (InSubTower v) :=
  inferInstanceAs (Decidable (v = .oo ∨ v = .xx))

/-- Sub-tower characterisation via `L` (v0.4 §3.5.3 sense (3)):

      v ∈ {道, 错综}  ↔  L v = 0. -/
theorem inSubTower_iff_L (v : Image) :
    InSubTower v ↔ L v = false := by
  cases v <;> simp [InSubTower, L]

/-- Image-self-pairing equals `L`: directly from `dot v v = v_α ∧ v_α
    ⊕ v_β ∧ v_β = v_α ⊕ v_β = L v` (in Bool, `b ∧ b = b`). -/
@[simp] theorem dot_self_eq_L (v : Image) : Image.dot v v = L v := by
  cases v <;> rfl

/-- Sub-tower characterisation via self-pairing (v0.4 §3.5.3 sense (2)):

      v ∈ {道, 错综}  ↔  ⟨v, v⟩ = 0.

    A direct corollary of `dot_self_eq_L` and `inSubTower_iff_L`. -/
theorem inSubTower_iff_self_dot (v : Image) :
    InSubTower v ↔ Image.dot v v = false := by
  rw [inSubTower_iff_L, dot_self_eq_L]

end Image

/-! ## § 2 The `X n` sub-tower -/

namespace X

/-- A cell `U : X n` is in the sub-tower `{道, 错综}ⁿ` iff every
    coordinate is in `Image.InSubTower`. -/
def InSubTower {n : Nat} (U : X n) : Prop :=
  ∀ i : Fin n, Image.InSubTower (U i)

instance instDecidableInSubTower {n : Nat} (U : X n) :
    Decidable (InSubTower U) :=
  Fintype.decidableForallFintype

/-- Sub-tower characterisation via `Image.L` per coordinate
    (v0.4 §3.5.3): `U` is in the sub-tower iff each `Image.L (U i) = 0`. -/
theorem inSubTower_iff_L {n : Nat} (U : X n) :
    InSubTower U ↔ ∀ i, Image.L (U i) = false := by
  unfold InSubTower
  simp only [Image.inSubTower_iff_L]

/-! ## § 3 As a Subtype + cardinality -/

/-- The sub-tower as a subtype.  Per v0.4 §3.5.2, `|SubTower n| = 2ⁿ`. -/
abbrev SubTower (n : Nat) : Type := { U : X n // InSubTower U }

instance instFintypeSubTower (n : Nat) : Fintype (SubTower n) :=
  Subtype.fintype _

/-- Bijection witnessing `SubTower n ≃ Fin n → Bool`: a sub-tower cell
    is determined by which coordinates are 错综 (= `true`) vs 道 (=
    `false`).  This is the §3.5.2/§3.6.4 identification with `F₂ⁿ`. -/
def subTowerEquiv (n : Nat) : SubTower n ≃ (Fin n → Bool) where
  toFun U i := decide (U.val i = .xx)
  invFun b := ⟨fun i => bif b i then .xx else .oo, by
    intro i
    cases h : b i
    · left; simp [h]
    · right; simp [h]⟩
  left_inv := by
    rintro ⟨U, hU⟩
    apply Subtype.ext
    funext i
    rcases hU i with h | h
    · simp [h]
    · simp [h]
  right_inv := by
    intro b
    funext i
    show decide ((bif b i then Image.xx else Image.oo) = Image.xx) = b i
    cases b i <;> decide

/-- Cardinality of the sub-tower (v0.4 §3.5.2):

      |{道, 错综}ⁿ ∩ X n| = 2ⁿ. -/
theorem subTower_card (n : Nat) : Fintype.card (SubTower n) = 2 ^ n := by
  rw [Fintype.card_congr (subTowerEquiv n), Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]

end X

end SSBX.Foundation.Wen.Xiang
