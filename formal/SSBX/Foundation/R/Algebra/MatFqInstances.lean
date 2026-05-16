/-
# Foundation.R.Algebra.MatFqInstances — `Mat_n(F_q)` simple-Artinian instances

Per `docs-next/10_formal_形式/gut-roadmap.md` **G11 (T5-B parametric over k)**:
the main bottleneck for the char(k)≠2 generalization of the Wedderburn anchor
is *applying* Mathlib's `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`
(in `Mathlib.RingTheory.SimpleModule.WedderburnArtin`).  Mathlib has the
abstract theorem; our `Mat2F2` and the standard carrier
`Matrix (Fin 2) (Fin 2) (ZMod p)` need explicit `IsSimpleRing` /
`IsArtinianRing` instances so the theorem applies *directly*.

This file installs the bottleneck-removing typeclass scaffolding.

## What's installed

* **§1** — Verified instances on `Matrix (Fin n) (Fin n) (ZMod p)` for
  `[Fact (Nat.Prime p)]` and `[NeZero n]`:
  * `IsSimpleRing` (via `DivisionRing.isSimpleRing` ∘ `IsSimpleRing.matrix`).
  * `IsArtinianRing` (via `DivisionRing.instIsArtinianRing` ∘
    `Matrix.IsArtinianRing` global instance from
    `Mathlib.RingTheory.Artinian.Module`).

  These are *re-exports*: Mathlib derives them automatically once the
  required imports are in scope; this file documents them so downstream
  modules (G11-B discriminant work, G11-C polymorphic field work) can
  rely on a single import.

* **§2** — Polymorphic generalization: `Matrix (Fin n) (Fin n) k` for
  any `[Field k] [NeZero n]` is simple Artinian.  The `[Fintype k]`
  case (finite field) additionally yields `Fintype`.

* **§3** — Transport to the bespoke `Mat2F2` carrier (which is
  `Fin 2 → Fin 2 → Bool` with custom `[Mul] [Add] [Zero] [One]` only —
  not a `Ring`, hence cannot carry `IsSimpleRing` directly).  We expose
  the Wedderburn-Artin decomposition for `Mat2F2` in `Nonempty
  (Mat2F2 ≃+* Matrix (Fin n) (Fin n) D)` form via the existing
  `T_P7b_mat2f2_equiv_matrix_zmod2` bridge.

* **§4** — The concrete applied corollary: a clean theorem
  `wedderburn_applied_matrix_zmod` showing that Mathlib's abstract
  `IsSimpleRing.exists_ringEquiv_matrix_divisionRing` resolves on
  `Matrix (Fin 2) (Fin 2) (ZMod p)` to give the expected
  matrix-over-division-ring witness.

## Strategy

All hard work is already in Mathlib:

* `DivisionRing.isSimpleRing` (`Mathlib.RingTheory.SimpleRing.Basic`).
* `DivisionRing.instIsArtinianRing` (`Mathlib.RingTheory.Artinian.Module`).
* `IsSimpleRing.matrix` (`Mathlib.RingTheory.SimpleRing.Matrix`).
* `Matrix.IsArtinianRing` instance, also in `Artinian.Module`.
* `Mathlib.Algebra.Field.ZMod` gives `Field (ZMod p)` from
  `[Fact (Nat.Prime p)]`.

We chain them and verify with `example : IsSimpleRing ...`. No new
theorems require proof; we only re-export, document, and add
`example`-level health checks.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` G11 (T5-B parametric over k).
* `Foundation/R/PhaseZero/TP7bFormB.lean` (already uses
  `IsSimpleRing.exists_ringEquiv_matrix_divisionRing` on the `ZMod 2`
  carrier; this file generalizes to arbitrary prime `p`).

## Constraints honoured

* **No new axioms** — all instances are Mathlib re-derivations.
* **No `sorry`** — every statement is a direct Mathlib application.
* No modification of existing Foundation files (except for the
  `SSBX.lean` import line).
-/

import SSBX.Foundation.R.PhaseZero
import SSBX.Foundation.R.PhaseZero.TP7bUniqueness
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Data.Matrix.Mul

namespace SSBX.Foundation.R.Algebra

universe u

/-! ## § 1 Concrete instances on `Matrix (Fin n) (Fin n) (ZMod p)` -/

section ZModMatrix

variable (p : ℕ) [hp : Fact (Nat.Prime p)]
variable (n : ℕ) [hn : NeZero n]

-- Mathlib already derives these via the chain
--   Fact (Nat.Prime p) → Field (ZMod p) → IsSimpleRing (ZMod p)
--                                       → IsSimpleRing (Matrix (Fin n) (Fin n) (ZMod p))
-- and similarly for IsArtinianRing.  We expose them as `example`s so
-- downstream code can rely on this file as a single import.

example : Field (ZMod p) := inferInstance
example : IsSimpleRing (ZMod p) := inferInstance
example : IsArtinianRing (ZMod p) := inferInstance

example : Ring (Matrix (Fin n) (Fin n) (ZMod p)) := inferInstance
example : IsSimpleRing (Matrix (Fin n) (Fin n) (ZMod p)) := inferInstance
example : IsArtinianRing (Matrix (Fin n) (Fin n) (ZMod p)) := inferInstance

/-- **Named re-export** — `IsSimpleRing` on `Mat_n(F_p)`.  Downstream
    modules can call this by name rather than re-deriving the chain. -/
theorem isSimpleRing_matrix_zmod :
    IsSimpleRing (Matrix (Fin n) (Fin n) (ZMod p)) :=
  inferInstance

/-- **Named re-export** — `IsArtinianRing` on `Mat_n(F_p)`. -/
theorem isArtinianRing_matrix_zmod :
    IsArtinianRing (Matrix (Fin n) (Fin n) (ZMod p)) := by
  -- `IsArtinianRing` does not literally depend on `[NeZero n]`, but we
  -- keep the hypothesis in the signature for symmetry with the simple-ring
  -- counterpart.  Mark it as used to silence the unused-variable linter.
  let _ := hn
  infer_instance

end ZModMatrix

/-! ## § 2 Polymorphic generalization: `Matrix (Fin n) (Fin n) k`

For any field `k` (with no characteristic restriction) and any
`[NeZero n]`, the matrix ring `Mat_n(k)` is simple Artinian.  This is
the key parametric statement that unblocks G11 (T5-B over a polymorphic
field). -/

section FieldMatrix

variable (k : Type u) [Field k]
variable (n : ℕ) [hn : NeZero n]

example : IsSimpleRing k := inferInstance
example : IsArtinianRing k := inferInstance

example : Ring (Matrix (Fin n) (Fin n) k) := inferInstance
example : IsSimpleRing (Matrix (Fin n) (Fin n) k) := inferInstance
example : IsArtinianRing (Matrix (Fin n) (Fin n) k) := inferInstance

/-- **`Mat_n(k)` is simple, for any field `k` and `n ≥ 1`** —
    the parametric form unblocking G11 (T5-B over polymorphic field). -/
theorem isSimpleRing_matrix_field :
    IsSimpleRing (Matrix (Fin n) (Fin n) k) :=
  inferInstance

/-- **`Mat_n(k)` is Artinian, for any field `k` and `n ≥ 1`** — same
    parametric scope as `isSimpleRing_matrix_field`. -/
theorem isArtinianRing_matrix_field :
    IsArtinianRing (Matrix (Fin n) (Fin n) k) := by
  let _ := hn
  infer_instance

end FieldMatrix

/-! Further generalization: arbitrary division ring `D` (no
    commutativity needed). -/

section DivisionRingMatrix

variable (D : Type u) [DivisionRing D]
variable (n : ℕ) [hn : NeZero n]

example : IsSimpleRing (Matrix (Fin n) (Fin n) D) := inferInstance
example : IsArtinianRing (Matrix (Fin n) (Fin n) D) := inferInstance

/-- **`Mat_n(D)` is simple, for any division ring `D`** — the maximal
    parametric form, covering both commutative (field) and
    non-commutative (e.g. quaternion) base. -/
theorem isSimpleRing_matrix_divisionRing :
    IsSimpleRing (Matrix (Fin n) (Fin n) D) :=
  inferInstance

/-- **`Mat_n(D)` is Artinian, for any division ring `D`**. -/
theorem isArtinianRing_matrix_divisionRing :
    IsArtinianRing (Matrix (Fin n) (Fin n) D) := by
  let _ := hn
  infer_instance

end DivisionRingMatrix

/-! ## § 3 Transport to `Mat2F2`

`Mat2F2 := Fin 2 → Fin 2 → Bool` carries only `[Add] [Mul] [Zero] [One]`
(installed in `Foundation/R/PhaseZero.lean`), not the full `[Ring]`
required by `IsSimpleRing` / `IsArtinianRing`.  We cannot install those
typeclasses directly on `Mat2F2` without committing to a full ring
structure (XOR/AND-based) — which is out of scope for this bottleneck
removal.

Instead, we expose the *Wedderburn-Artin decomposition for `Mat2F2`*
as a `Nonempty (... ≃+* ...)` statement, transported via the existing
`T_P7b_mat2f2_equiv_matrix_zmod2 : Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)`
bridge (proved in `Foundation/R/PhaseZero/TP7bUniqueness.lean`).  This
gives downstream code the same operational content. -/

open SSBX.Foundation.R.PhaseZero in
/-- **Wedderburn-Artin decomposition for `Mat2F2`** — transports the
    `IsSimpleRing.exists_ringEquiv_matrix_divisionRing` witness from
    `Matrix (Fin 2) (Fin 2) (ZMod 2)` to `Mat2F2` via the existing
    `RingEquiv`. -/
theorem mat2F2_wedderburn_artin :
    ∃ (m : ℕ) (_ : NeZero m) (D : Type) (_ : DivisionRing D),
      Nonempty (Mat2F2 ≃+* Matrix (Fin m) (Fin m) D) := by
  obtain ⟨m, hm, D, hD, ⟨e⟩⟩ :=
    IsSimpleRing.exists_ringEquiv_matrix_divisionRing
      (Matrix (Fin 2) (Fin 2) (ZMod 2))
  exact ⟨m, hm, D, hD,
    ⟨T_P7b_mat2f2_equiv_matrix_zmod2.trans e⟩⟩

/-! ## § 4 Concrete applied corollary

The clean statement that lets downstream G11 work proceed: applying
`IsSimpleRing.exists_ringEquiv_matrix_divisionRing` to `Mat_2(F_p)`
yields a matrix-over-division-ring decomposition.  For `p = 2` the
trivial decomposition is `(m = 2, D = ZMod 2)`; for arbitrary primes
the decomposition exists by the same abstract theorem. -/

/-- **`wedderburn_applied` — abstract Wedderburn-Artin applied to
    `Mat_2(F_p)`**.  For any prime `p`, the standard 2×2 matrix carrier
    over `ZMod p` admits a matrix-over-division-ring decomposition.

    This is the existential form: even though for `Mat_2(F_p)` the
    expected witness is `(m = 2, D = ZMod p)`, this theorem records the
    *application* of Mathlib's abstract theorem to our anchor carrier.

    G11-B (discriminant) and G11-C (polymorphic field) build on this by
    constraining the `(m, D)` pair. -/
theorem wedderburn_applied_matrix_zmod
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ (m : ℕ) (_ : NeZero m) (D : Type) (_ : DivisionRing D),
      Nonempty (Matrix (Fin 2) (Fin 2) (ZMod p) ≃+* Matrix (Fin m) (Fin m) D) :=
  IsSimpleRing.exists_ringEquiv_matrix_divisionRing _

/-- **`wedderburn_applied` for arbitrary `Mat_n(F_p)`** — same abstract
    theorem applied to the general `n × n` matrix carrier. -/
theorem wedderburn_applied_matrix_zmod_general
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero n] :
    ∃ (m : ℕ) (_ : NeZero m) (D : Type) (_ : DivisionRing D),
      Nonempty (Matrix (Fin n) (Fin n) (ZMod p) ≃+* Matrix (Fin m) (Fin m) D) :=
  IsSimpleRing.exists_ringEquiv_matrix_divisionRing _

/-- **`wedderburn_applied` over arbitrary field `k`** — the polymorphic
    parametric form.  This is the statement G11-C needs: for any field
    `k` and any `n ≥ 1`, the matrix ring `Mat_n(k)` admits a
    Wedderburn-Artin decomposition. -/
theorem wedderburn_applied_matrix_field
    (k : Type u) [Field k] (n : ℕ) [NeZero n] :
    ∃ (m : ℕ) (_ : NeZero m) (D : Type u) (_ : DivisionRing D),
      Nonempty (Matrix (Fin n) (Fin n) k ≃+* Matrix (Fin m) (Fin m) D) :=
  IsSimpleRing.exists_ringEquiv_matrix_divisionRing _

/-- **`wedderburn_applied` over arbitrary division ring `D₀`** — the
    maximal parametric form (no commutativity restriction on the base). -/
theorem wedderburn_applied_matrix_divisionRing
    (D₀ : Type u) [DivisionRing D₀] (n : ℕ) [NeZero n] :
    ∃ (m : ℕ) (_ : NeZero m) (D : Type u) (_ : DivisionRing D),
      Nonempty (Matrix (Fin n) (Fin n) D₀ ≃+* Matrix (Fin m) (Fin m) D) :=
  IsSimpleRing.exists_ringEquiv_matrix_divisionRing _

/-! ## § 5 `Fintype` for the finite-field case

When `k` is *both* a finite field, `Mat_n(k)` is finite, which combined
with the simple-Artinian instances above gives a fully discrete
setting suitable for `decide`-based corollaries.  `ZMod p` for prime
`p` is finite, so this applies uniformly. -/

section FiniteFieldMatrix

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (n : ℕ) [NeZero n]

example : Fintype (ZMod p) := inferInstance
example : Fintype (Matrix (Fin n) (Fin n) (ZMod p)) := inferInstance
example : DecidableEq (Matrix (Fin n) (Fin n) (ZMod p)) := inferInstance

/-- **`Mat_n(F_p)` is finite** — re-export for downstream cardinality
    arithmetic (e.g. the `|A| = p^{n²}` step in the full T_P7b
    uniqueness chain).  `Fintype` is data, so this is an `abbrev`, not
    `theorem`; `[NeZero n]` is required only to align with the
    simple-Artinian re-exports above (Mathlib's `Fintype (Matrix ...)`
    works for `n = 0` too). -/
abbrev fintype_matrix_zmod : Fintype (Matrix (Fin n) (Fin n) (ZMod p)) :=
  let _ := n
  inferInstance

end FiniteFieldMatrix

end SSBX.Foundation.R.Algebra
