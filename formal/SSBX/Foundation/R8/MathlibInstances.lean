/-
# Foundation.R8.MathlibInstances — Mathlib `Fintype` / `AddCommGroup` bridge

Per `r8.md` v0.2 §15.1, `R 8 = Fin 8 → Bool` already inherits `Fintype`,
`DecidableEq`, `AddCommGroup` from the parametric `R N` layer
(`Foundation/R/Basic.lean`).  This module records the **Mathlib-facing
re-exports** of those instances at the concrete `R 8` type, so that
downstream code that works against the byte-scale ceiling can `import
SSBX.Foundation.R8.MathlibInstances` and have everything in scope.

Adapted from `Foundation/Squaring/V4Tensor.lean` (the F_2-instance
machinery there).  Any semantic Klein-4 axis naming is **not** migrated
here — that is Atlas-level (P3), not core.

## What is exported

* `instFintypeR8` — Mathlib `Fintype (R 8)` (re-exported from parametric layer).
* `instDecidableEqR8` — `DecidableEq (R 8)` (re-exported).
* `instAddCommGroupR8` — `AddCommGroup (R 8)` (re-exported).
* `instInhabitedR8` — `Inhabited (R 8)` (re-exported).
* `R8.card` — the cardinality 256.

## Doctrinal anchor

* `r8.md` v0.2 §15.1 (Lean 4 type definition + instances).
* This module is the Mathlib-bridge analogue of the
  `Foundation/Squaring/V4Tensor.lean` machinery, but stripped of all
  V₄-by-name content.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 Re-export instances at `R 8` -/

/-- `R 8` is a `Fintype` (inherited from parametric `R N`). -/
instance instFintypeR8 : Fintype (R 8) := R.instFintype 8

/-- `R 8` has `DecidableEq` (inherited from parametric `R N`). -/
instance instDecidableEqR8 : DecidableEq (R 8) := R.instDecidableEq 8

/-- `R 8` is inhabited (the zero vector). -/
instance instInhabitedR8 : Inhabited (R 8) := R.instInhabited 8

/-- `R 8` carries the F_2-vector-space `AddCommGroup` (inherited from
    parametric `R N` via coordinate-wise XOR). -/
instance instAddCommGroupR8 : AddCommGroup (R 8) := R.instAddCommGroup 8

/-! ## § 2 Concrete cardinality at the Mathlib-facing layer -/

/-- The cardinality of `R 8` as a Mathlib `Fintype`. -/
def card : ℕ := Fintype.card (R 8)

/-- `|R 8| = 256`. -/
theorem card_eq_256 : card = 256 := R.R8_card

/-- `|R 8| = 2^8`. -/
theorem card_eq_pow : card = 2 ^ 8 := R.card_eq 8

/-! ## § 3 The Mathlib `Prod` view (re-exporting the L/R halves split) -/

/-- `R 8 ≃+ R 4 × R 4` at the type level (no group homomorphism
    structure imposed; just an `Equiv`).  The Mathlib `Prod` view
    realises the `R 4 ⊕ R 4` algebraic direct sum. -/
def equivProd : R 8 ≃ R 4 × R 4 :=
  show R (4 + 4) ≃ R 4 × R 4 from R.directSumEquiv (N := 4) (M := 4)

/-- The Mathlib `Prod` view preserves cardinality. -/
theorem card_equivProd :
    Fintype.card (R 8) = Fintype.card (R 4 × R 4) :=
  Fintype.card_congr equivProd

/-! ## § 4 Sanity check — the zero vector and all-ones -/

example : (0 : R 8) = (fun _ => false) := rfl

example : (R.constx 8 : R 8) = (fun _ => true) := rfl

example : (0 : R 8) + R.constx 8 = R.constx 8 := by
  funext i; show Bool.xor false true = true; rfl

end SSBX.Foundation.R8
