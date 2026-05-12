/-
# QuantumR8Bridge — Modern/Quantum ↔ R₈ thin bridge

This file records only the already-formal finite bridge:

* one line bit: Pauli X matches the basis action of `Yao.neg`;
* one trigram: the three position operators match `Fin 8` basis bit operations;
* R₈: the carrier is already `V₄⁴`, and cells act by regular XOR translation
  on the finite function space `R8 → ℂ`.

It deliberately does not construct a full `R8 → Fin 256 → ℂ` unitary
representation or a physical Pauli-string system.
-/
import SSBX.Foundation.Modern.Quantum
import SSBX.Foundation.Squaring.V4Tensor

namespace SSBX.Foundation.Modern.QuantumR8Bridge

open Matrix
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Modern
open SSBX.Foundation.Squaring

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
