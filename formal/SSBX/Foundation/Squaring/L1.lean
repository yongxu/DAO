/-
# L₁ = Cell256 × Cell256

The first squaring layer keeps the construction finite: group structure comes
from `Prod`, and the octant classifier is read from the first three atomic
bits of the XOR difference between the two factors.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
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
  | f1 | f2 | f3 | f4 | f5 | f6 | imprint | project
  deriving Repr, DecidableEq

namespace AtomicFlip

def apply : AtomicFlip → Cell256 → Cell256
  | .f1 => Cell256.flip1
  | .f2 => Cell256.flip2
  | .f3 => Cell256.flip3
  | .f4 => Cell256.flip4
  | .f5 => Cell256.flip5
  | .f6 => Cell256.flip6
  | .imprint => Cell256.imprint
  | .project => Cell256.project

def applyL1Left (af : AtomicFlip) : L1 → L1
  | (a, b) => (af.apply a, b)

def applyL1Right (af : AtomicFlip) : L1 → L1
  | (a, b) => (a, af.apply b)

theorem apply_left_f1_f1 (l : L1) : applyL1Left .f1 (applyL1Left .f1 l) = l := by
  rcases l with ⟨a, b⟩
  simp [applyL1Left, apply, Cell256.flip1_flip1]

theorem apply_right_project_project (l : L1) : applyL1Right .project (applyL1Right .project l) = l := by
  rcases l with ⟨a, b⟩
  simp [applyL1Right, apply, Cell256.project_project]

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

`octantIndex` factors as the composite of two surjective additive group
homomorphisms — `L₁ → Cell256` via `(a, b) ↦ a + b`, then `Cell256 → (Z/2)³`
taking the first three hexagram bits — reindexed as `Fin 8`. The composite
kernel has index 8 in L₁, so each coset (= each octant) has size
`|L₁|/8 = 65536/8 = 8192` by Lagrange.

Proven concretely by bridging `Set.ncard` to a `Finset.filter.card` over the
finite type L₁, then running `native_decide` on each of the 8 cases for `i`.
This consumes 65536 `Cell256 × Cell256` checks per case — fast in native code
since `Fintype Cell256` is computable (see `V4Tensor.lean`). -/
theorem octant_card (i : Fin 8) : (octant i).ncard = 8192 := by
  have h_eq : (octant i : Set L1) =
      ↑(Finset.univ.filter (fun l : L1 => octantIndex l = i)) := by
    ext l
    simp [octant]
  rw [h_eq, Set.ncard_coe_finset]
  fin_cases i <;> native_decide

theorem l1_summary :
    (∀ l : L1, swap (swap l) = l)
    ∧ (∀ c : Cell256, proj1 (diag c) = c)
    ∧ (∀ c : Cell256, proj2 (diag c) = c)
    ∧ (∀ l : L1, ∃! i : Fin 8, l ∈ octant i)
    ∧ (∀ i : Fin 8, (octant i).ncard = 8192) :=
  ⟨swap_swap, proj1_diag, proj2_diag, octant_partition, octant_card⟩

end L1

end SSBX.Foundation.Squaring
