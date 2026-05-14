/-
# Foundation.R.Judgment.Information — tower-level information judgment

Per `wen-algebra` v0.6 §7.1: information judgment functions on the
R-Family.  Three layers:

* **overlap** (Layer 0) — the dot product `R N × R N → Bool`, defined
  for all N.
* **direction** (Layer 1) — the symplectic σ, defined for even N.
* **signature** (Layer 2) — a quadratic refinement parameterised by
  a choice vector, defined for even N.

All three are F_2-valued.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear

namespace SSBX.Foundation.R.Judgment

open SSBX.Foundation.R

namespace Information

/-! ## § 1 Layer 0 — overlap (all N) -/

/-- Information overlap: the Layer-0 dot product on `R N`. -/
def overlap {N : ℕ} (u v : R N) : Bool := R.dot u v

@[simp] theorem overlap_eq (N : ℕ) (u v : R N) :
    overlap u v = R.dot u v := rfl

theorem overlap_symm {N : ℕ} (u v : R N) :
    overlap u v = overlap v u := R.dot_symm u v

theorem overlap_zero {N : ℕ} (v : R N) : overlap (0 : R N) v = false :=
  R.dot_zero_left v

/-! ## § 2 Layer 1 — direction (even N) -/

/-- Information direction: the symplectic σ on `R (2 * k)`. -/
def direction {k : ℕ} (u v : R (2 * k)) : Bool := R.sigma u v

theorem direction_alternating {k : ℕ} (v : R (2 * k)) :
    direction v v = false := R.sigma_alternating v

theorem direction_symm {k : ℕ} (u v : R (2 * k)) :
    direction u v = direction v u := R.sigma_symm u v

/-! ## § 3 Layer 2 — signature (even N) -/

/-- Information signature: the Layer-2 quadratic refinement q^c on
    `R (2 * k)`, parameterised by `c : Fin k → Bool`. -/
def signature {k : ℕ} (c : Fin k → Bool) (v : R (2 * k)) : Bool :=
  R.q c v

theorem signature_zero {k : ℕ} (c : Fin k → Bool) :
    signature c (0 : R (2 * k)) = false := R.q_zero_vec c

/-- The Arf invariant of the chosen quadratic refinement. -/
def signature_arf {k : ℕ} (c : Fin k → Bool) : Bool := R.arf c

end Information

end SSBX.Foundation.R.Judgment
