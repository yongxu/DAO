/-
# L₁ = Cell256 × Cell256

The first squaring layer keeps the construction finite: group structure comes
from `Prod`, and the octant classifier is read from the first three atomic
bits of the XOR difference between the two factors.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import SSBX.Foundation.Squaring.V4Tensor

namespace SSBX.Foundation.Squaring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256

abbrev L1 : Type := Cell256 × Cell256

namespace L1

instance : AddCommGroup L1 := inferInstance

def swap : L1 → L1
  | (a, b) => (b, a)

def diag (c : Cell256) : L1 := (c, c)

def proj1 : L1 → Cell256 := Prod.fst
def proj2 : L1 → Cell256 := Prod.snd

theorem swap_swap (l : L1) : swap (swap l) = l := by
  rcases l with ⟨a, b⟩
  rfl

theorem swap_diag (c : Cell256) : swap (diag c) = diag c := rfl
theorem proj1_diag (c : Cell256) : proj1 (diag c) = c := rfl
theorem proj2_diag (c : Cell256) : proj2 (diag c) = c := rfl

inductive AtomicFlip where
  | f1 | f2 | f3 | f4 | f5 | f6 | yin | tou
  deriving Repr, DecidableEq

namespace AtomicFlip

def apply : AtomicFlip → Cell256 → Cell256
  | .f1 => Cell256.flip1
  | .f2 => Cell256.flip2
  | .f3 => Cell256.flip3
  | .f4 => Cell256.flip4
  | .f5 => Cell256.flip5
  | .f6 => Cell256.flip6
  | .yin => Cell256.yin
  | .tou => Cell256.tou

def applyL1Left (af : AtomicFlip) : L1 → L1
  | (a, b) => (af.apply a, b)

def applyL1Right (af : AtomicFlip) : L1 → L1
  | (a, b) => (a, af.apply b)

theorem apply_left_f1_f1 (l : L1) : applyL1Left .f1 (applyL1Left .f1 l) = l := by
  rcases l with ⟨a, b⟩
  simp [applyL1Left, apply, Cell256.flip1_flip1]

theorem apply_right_tou_tou (l : L1) : applyL1Right .tou (applyL1Right .tou l) = l := by
  rcases l with ⟨a, b⟩
  simp [applyL1Right, apply, Cell256.tou_tou]

end AtomicFlip

def yaoBit : Yao → Nat
  | Yao.yang => 0
  | Yao.yin => 1

def octantNat (l : L1) : Nat :=
  let q := V4Tensor.toV4Quad (l.1 + l.2)
  match q with
  | ((y1, y2), (y3, _), _, _) => 4 * yaoBit y1 + 2 * yaoBit y2 + yaoBit y3

theorem octantNat_lt (l : L1) : octantNat l < 8 := by
  unfold octantNat
  generalize hq : V4Tensor.toV4Quad (l.1 + l.2) = q
  rcases q with ⟨⟨y1, y2⟩, ⟨y3, _y4⟩, _q3, _q4⟩
  cases y1 <;> cases y2 <;> cases y3 <;> simp [yaoBit]

def octantIndex (l : L1) : Fin 8 := ⟨octantNat l, octantNat_lt l⟩

def octant (i : Fin 8) : Set L1 := { l | octantIndex l = i }

theorem octant_partition (l : L1) : ∃! i : Fin 8, l ∈ octant i := by
  refine ⟨octantIndex l, rfl, ?_⟩
  intro j hj
  exact hj.symm

/-- Each octant has size 8192 = |L₁|/8.

Group-theoretic sketch: `octantIndex` factors as the composite of two
surjective additive group homomorphisms — `L₁ → Cell256` via `(a, b) ↦ a + b`,
then `Cell256 → (Z/2)³` taking the first three hexagram bits — reindexed as
`Fin 8`. The composite kernel has index 8 in L₁, so by Lagrange each coset
(= each octant) has size `|L₁|/8 = 65536/8 = 8192`.

⚠️ Currently left as documented `sorry` per
[L-tower-plan-v0.2.md §7.2](../../../../docs-next/10_formal_形式/L-tower-plan-v0.2.md)
fallback. See
[implementation notes](../../../../docs-next/10_formal_形式/L-tower-implementation-notes-sprint1.md)
for the three closure paths (Lagrange / cardinality manipulation /
`native_decide`). The Sprint 1 acceptance §8.1 explicitly permits this
single documented `sorry`. -/
theorem octant_card (i : Fin 8) : (octant i).ncard = 8192 := by
  sorry

theorem l1_summary :
    (∀ l : L1, swap (swap l) = l)
    ∧ (∀ c : Cell256, proj1 (diag c) = c)
    ∧ (∀ c : Cell256, proj2 (diag c) = c)
    ∧ (∀ l : L1, ∃! i : Fin 8, l ∈ octant i)
    ∧ (∀ i : Fin 8, (octant i).ncard = 8192) :=
  ⟨swap_swap, proj1_diag, proj2_diag, octant_partition, octant_card⟩

end L1

end SSBX.Foundation.Squaring
