/-
# QuantumR8Bridge — Modern/Quantum ↔ R₈ thin bridge

This file records only the already-formal finite bridge:

* one line bit: Pauli X matches the basis action of `Yao.neg`;
* one trigram: the three position operators match `Fin 8` basis bit operations;
* R₈: the carrier is already `V₄⁴`, and cells act by regular XOR translation
  on the finite function space `R8 → ℂ`.

It deliberately does not construct a full `R8 → Fin 256 → ℂ` unitary
representation or a physical Pauli-string system.

## History

Originally this file imported `Foundation/Squaring/V4Tensor.lean` for the
Yi-flavoured `R₈ ≃+ V₄⁴` Mathlib `AddEquiv` (`V4Tensor.iso`) and the
`V4Tensor.V4Coord = Yao × Yao` abbreviation.  The v0.6 R-Family restructure
retired `Foundation/Squaring/`; this file's Yi-flavoured carriers are not
part of the parametric core, so the relevant pieces are inlined locally
below (`V4Coord`, `iso`) rather than re-imported from a non-existent
module.  (A future Atlas/Yi migration may rebase this on the parametric
`R 8` carrier; that is out of scope for the P4.4 cleanup.)
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Basic
import SSBX.Foundation.Modern.Quantum
import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8

namespace SSBX.Foundation.Modern.QuantumR8Bridge

open Matrix
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Modern

/-! ## Local re-statement of `R₈ ≃+ V₄⁴`

Adapted (inlined) from the retired `Foundation/Squaring/V4Tensor.lean` so
this file no longer depends on the `Squaring/` subtree.  Only the pieces
actually used downstream (`V4Coord`, `iso`, the supporting Mathlib
instances) are kept; the F₂ machinery itself is also covered by the
parametric `Foundation/R8/MathlibInstances.lean` for the `R 8` carrier. -/

namespace V4Tensor

/-- Mathlib `Fintype Yao`. -/
instance instFintypeYao : Fintype Yao where
  elems := [Yao.yang, Yao.yin].toFinset
  complete := by
    intro y
    cases y <;> decide

instance instAddYao : Add Yao := ⟨R8.yaoXor⟩
instance instZeroYao : Zero Yao := ⟨Yao.yang⟩
instance instNegYao : Neg Yao := ⟨id⟩
instance instSubYao : Sub Yao := ⟨R8.yaoXor⟩

@[simp] theorem yao_add_eq_xor (a b : Yao) : a + b = R8.yaoXor a b := rfl

instance instAddCommGroupYao : AddCommGroup Yao where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  zero_add := by
    intro a
    cases a <;> rfl
  add_zero := by
    intro a
    cases a <;> rfl
  neg_add_cancel := by
    intro a
    cases a <;> rfl
  add_comm := by
    intro a b
    cases a <;> cases b <;> rfl

instance instFintypeHexagram : Fintype Hexagram where
  elems := Hexagram.allHex.toFinset
  complete := fun h => List.mem_toFinset.mpr (hexagram_mem_allHex h)

instance instFintypeR8 : Fintype R8 where
  elems := R8.all.toFinset
  complete := fun c => List.mem_toFinset.mpr (R8.mem_all c)

instance instAddCommGroupR8 : AddCommGroup R8 where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := R8.xor_assoc
  zero_add := R8.origin_xor
  add_zero := R8.xor_origin
  neg_add_cancel := by
    intro c
    simpa [R8.neg_def] using R8.xor_self c
  add_comm := R8.xor_comm

/-- Coordinate model of a Klein-four carrier represented as two Yao bits.
    Local re-statement of `Foundation/Squaring/V4Tensor.V4Coord`. -/
abbrev V4Coord : Type := Yao × Yao

def boolToYao : Bool → Yao
  | false => Yao.yang
  | true => Yao.yin

def yaoToBool : Yao → Bool
  | Yao.yang => false
  | Yao.yin => true

def shiToV4Coord (s : Shi) : V4Coord :=
  (boolToYao (Shi.toYinGuo s).1, boolToYao (Shi.toYinGuo s).2)

def v4CoordToShi (v : V4Coord) : Shi :=
  Shi.ofYinGuo (yaoToBool v.1, yaoToBool v.2)

def toV4CoordQuad (c : R8) : V4Coord × V4Coord × V4Coord × V4Coord :=
  ((c.1.y1, c.1.y2), (c.1.y3, c.1.y4), (c.1.y5, c.1.y6), shiToV4Coord c.2)

def ofV4CoordQuad : V4Coord × V4Coord × V4Coord × V4Coord → R8
  | ((y1, y2), (y3, y4), (y5, y6), shi) =>
      (⟨y1, y2, y3, y4, y5, y6⟩, v4CoordToShi shi)

theorem to_of (q : V4Coord × V4Coord × V4Coord × V4Coord) :
    toV4CoordQuad (ofV4CoordQuad q) = q := by
  rcases q with ⟨⟨y1, y2⟩, ⟨y3, y4⟩, ⟨y5, y6⟩, ⟨s1, s2⟩⟩
  cases s1 <;> cases s2 <;> rfl

theorem of_to (c : R8) : ofV4CoordQuad (toV4CoordQuad c) = c := by
  rcases c with ⟨h, s⟩
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  rcases s with ⟨yin, guo⟩
  cases yin <;> cases guo <;> rfl

/-- `R₈ ≃+ V₄⁴` Mathlib `AddEquiv`. -/
def iso : R8 ≃+ (V4Coord × V4Coord × V4Coord × V4Coord) where
  toFun := toV4CoordQuad
  invFun := ofV4CoordQuad
  left_inv := of_to
  right_inv := to_of
  map_add' := by
    intro a b
    rcases a with ⟨ha, sa⟩
    rcases b with ⟨hb, sb⟩
    rcases ha with ⟨a1, a2, a3, a4, a5, a6⟩
    rcases hb with ⟨b1, b2, b3, b4, b5, b6⟩
    rcases sa with ⟨ay, ag⟩
    rcases sb with ⟨byin, bg⟩
    cases ay <;> cases ag <;> cases byin <;> cases bg <;>
      simp [toV4CoordQuad, R8.add_def, R8.xor, R8.hexXor,
        R8.shiXor, R8.yaoXor, Shi.toYinGuo, Shi.ofYinGuo, shiToV4Coord, boolToYao]

end V4Tensor

/-! ## One-bit bridge -/

/-- On the computational basis, Pauli X is exactly the R₁ line xor toggle. -/
theorem pauliX_matches_r1_xor (y : Yao) :
    Matrix.mulVec Quantum.pauliX (Quantum.Yao.toQubit y) =
      Quantum.Yao.toQubit y.neg :=
  Quantum.pauliX_apply_yao_basis y

/-! ## Trigram basis bridge -/

/-- The three trigram bit operators are the three `Fin 8` computational-basis flips.

This is only a basis-index statement; it is not a tensor-product Hilbert-space
operator construction. -/
theorem trigram_pauli_basis_matches_r3_xor :
    (∀ t : Trigram,
        Quantum.Trigram.toFin8 (motion t) =
          Quantum.flipInitialIndex (Quantum.Trigram.toFin8 t))
    ∧ (∀ t : Trigram,
        Quantum.Trigram.toFin8 (middleFlip t) =
          Quantum.flipMiddleIndex (Quantum.Trigram.toFin8 t))
    ∧ (∀ t : Trigram,
        Quantum.Trigram.toFin8 (topFlip t) =
          Quantum.flipTopIndex (Quantum.Trigram.toFin8 t)) := by
  rcases Quantum.operator_position_index_alignment with ⟨hdong, hhua, hbian, _, _⟩
  exact ⟨hdong, hhua, hbian⟩

/-! ## R₈ regular-representation bridge -/

/-- The small finite function-space carrier used here for R₈ semantics. -/
abbrev R8Hilbert : Type := R8 → ℂ

/-- Point indicator on the finite R₈ function space. -/
def r8Indicator (c : R8) : R8Hilbert :=
  fun s => if s = c then 1 else 0

/-- Regular right-translation action on finite R₈ functions, by precomposition.

This is a finite basis/function-space action only; no inner-product or unitarity
claim is made here. -/
def r8RegularTranslate (c : R8) (ψ : R8Hilbert) : R8Hilbert :=
  fun s => ψ (R8.xor s c)

@[simp] theorem r8_regular_translate_apply (c s : R8) (ψ : R8Hilbert) :
    r8RegularTranslate c ψ s = ψ (R8.xor s c) := rfl

/-- Way/origin acts as the no-op on the finite R₈ function space. -/
theorem r8_regular_translate_origin :
    r8RegularTranslate R8.origin = id := by
  funext ψ s
  simp [r8RegularTranslate]

/-- Regular translations compose by XOR of cells. -/
theorem r8_regular_translate_comp (a b : R8) :
    r8RegularTranslate a ∘ r8RegularTranslate b =
      r8RegularTranslate (R8.xor a b) := by
  funext ψ s
  simp [r8RegularTranslate, Function.comp_apply, R8.xor_assoc]

/-- Each regular translation is an involutive permutation of the finite
function space. This is still only a finite permutation fact, not an
inner-product/unitarity claim. -/
theorem r8_regular_translate_involutive (c : R8) :
    r8RegularTranslate c ∘ r8RegularTranslate c = id := by
  funext ψ s
  simp [r8RegularTranslate, Function.comp_apply, R8.xor_assoc, R8.xor_self]

/-- The regular translation as an explicit equivalence of the finite function
space, with itself as inverse. -/
def r8RegularTranslateEquiv (c : R8) : R8Hilbert ≃ R8Hilbert where
  toFun := r8RegularTranslate c
  invFun := r8RegularTranslate c
  left_inv ψ := by
    have h := congrFun (r8_regular_translate_involutive c) ψ
    simpa [Function.comp_apply] using h
  right_inv ψ := by
    have h := congrFun (r8_regular_translate_involutive c) ψ
    simpa [Function.comp_apply] using h

/-- The regular function-space action is faithful: the translating cell can be
recovered from its action on point indicators. -/
theorem r8_regular_translate_faithful :
    Function.Injective r8RegularTranslate := by
  intro a b h
  have hpoint := congrFun (congrFun h (r8Indicator a)) R8.origin
  by_cases hba : b = a
  · exact hba.symm
  · simp [r8RegularTranslate, r8Indicator, hba] at hpoint

/-- R₈ is exposed as `V₄⁴`; each cell acts as an injective regular translation,
and Way/origin is the no-op translation.

This is the finite regular-representation bridge over `R8 → ℂ`, not a claim
about physical Pauli strings or analytic Hilbert-space structure. -/
theorem r8_regular_representation_quantum_bridge_summary :
    Nonempty (R8 ≃+ (V4Tensor.V4Coord × V4Tensor.V4Coord × V4Tensor.V4Coord × V4Tensor.V4Coord))
    ∧ Function.Injective R8.cayley
    ∧ R8.cayley R8.origin = id
    ∧ Nonempty R8Hilbert
    ∧ r8RegularTranslate R8.origin = id
    ∧ (∀ c : R8, r8RegularTranslate c ∘ r8RegularTranslate c = id)
    ∧ Function.Injective r8RegularTranslate := by
  refine ⟨⟨V4Tensor.iso⟩, R8.cayley_inj, ?_, ⟨fun _ => 0⟩,
    r8_regular_translate_origin, r8_regular_translate_involutive,
    r8_regular_translate_faithful⟩
  funext c
  simp [R8.cayley]

/-! ## Scope boundary -/

/-- Marker for the intentionally deferred construction:
`R8 → Fin 256 → ℂ` unitary semantics and a physical Pauli-string system. -/
def FullR8HilbertPauliStringSystemConstructedHere : Prop := False

/-- This bridge does not claim the full Hilbert-space / physical Pauli-string
system. It only packages finite basis, function-space, and regular-translation
facts above. -/
theorem quantum_r8_bridge_scope_boundary :
    ¬ FullR8HilbertPauliStringSystemConstructedHere := by
  intro h
  exact h

end SSBX.Foundation.Modern.QuantumR8Bridge
