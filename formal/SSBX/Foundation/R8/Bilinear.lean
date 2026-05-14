/-
# Foundation.R8.Bilinear — three bilinear layers on R 8

Per `r8.md` v0.2 §6, `R 8` (even-dimensional, k = 4 blocks) supports
all three bilinear layers from `Foundation/R/Bilinear.lean` specialised
to `R (2 * 4) = R 8`:

* **Layer 0** — dot product `dot8 : R 8 → R 8 → Bool`.
* **Layer 1** — symplectic `sigma8 : R 8 → R 8 → Bool`, with 4 blocks.
* **Layer 2** — quadratic refinements `q8 c` parameterised by
  `c : Fin 4 → Bool`, giving `2^4 = 16` variants split into 2 Arf
  classes of 8 each.

This is a **thin re-export wrapper** — the actual implementations live
in `Foundation/R/Bilinear.lean`.  We provide `R 8`-typed aliases plus
sanity-check theorems specific to `R 8` (the 4-block count, 16
quadratic variants, etc.).

## Doctrinal anchor

* `r8.md` v0.2 §6.1 (Layer 0 dot), §6.2 (Layer 1 σ with 4 blocks),
  §6.3 (Layer 2 q with 16 variants), §6.4 (Arf 2-class split),
  §6.5 (self-similarity / block doubling).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 Layer 0 — dot product on R 8 -/

/-- The dot product on `R 8`. -/
def dot8 (u v : R 8) : Bool := R.dot u v

theorem dot8_symm (u v : R 8) : dot8 u v = dot8 v u := R.dot_symm u v

@[simp] theorem dot8_zero_left (v : R 8) : dot8 (0 : R 8) v = false :=
  R.dot_zero_left v

@[simp] theorem dot8_zero_right (u : R 8) : dot8 u (0 : R 8) = false :=
  R.dot_zero_right u

/-! ## § 2 Layer 1 — symplectic σ on R 8 (k = 4 blocks) -/

/-- The symplectic form on `R 8`, with 4 blocks. -/
def sigma8 (u v : R 8) : Bool := R.sigma (k := 4) u v

theorem sigma8_symm (u v : R 8) : sigma8 u v = sigma8 v u :=
  R.sigma_symm (k := 4) u v

theorem sigma8_alternating (v : R 8) : sigma8 v v = false :=
  R.sigma_alternating (k := 4) v

/-! ## § 3 Layer 2 — quadratic refinements on R 8 (16 variants) -/

/-- The Layer-2 quadratic refinement on `R 8` parameterised by
    `c : Fin 4 → Bool`.  There are `2^4 = 16` such refinements. -/
def q8 (c : Fin 4 → Bool) (v : R 8) : Bool := R.q c v

theorem q8_zero (c : Fin 4 → Bool) : q8 c (0 : R 8) = false :=
  R.q_zero_vec (k := 4) c

/-- The Arf invariant of the chosen `c`. -/
def arf8 (c : Fin 4 → Bool) : Bool := R.arf c

/-- There are 16 quadratic refinements on `R 8`. -/
theorem q8_variant_count :
    (Finset.univ : Finset (Fin 4 → Bool)).card = 16 := by decide

/-- 8 quadratic refinements have Arf = 0. -/
theorem q8_arf_zero_count :
    (Finset.univ.filter (fun c : Fin 4 → Bool => arf8 c = false)).card = 8 := by
  decide

/-- 8 quadratic refinements have Arf = 1. -/
theorem q8_arf_one_count :
    (Finset.univ.filter (fun c : Fin 4 → Bool => arf8 c = true)).card = 8 := by
  decide

/-! ## § 4 Decomposition `dot = σ ⊕ LL` on R 8

The Layer-0 ↔ Layer-1 decomposition holds: `dot u v = σ(u, v) ⊕ LL(u, v)`
on `R 8 = R (2 * 4)`, where LL is the per-block outer-product. -/

/-- The per-block outer-product `LL` on `R 8`. -/
def LL8 (u v : R 8) : Bool := R.LL (k := 4) u v

/-- The decomposition theorem on R 8: `dot = σ ⊕ LL`. -/
theorem dot8_eq_sigma8_xor_LL8 (u v : R 8) :
    dot8 u v = Bool.xor (sigma8 u v) (LL8 u v) :=
  R.dot_eq_sigma_xor_LL (k := 4) u v

/-! ## § 5 Sanity checks at small basis elements -/

example : dot8 0 0 = false := dot8_zero_left 0

example : sigma8 0 0 = false := sigma8_alternating 0

example : sigma8 (R.basis (0 : Fin 8)) (R.basis (1 : Fin 8)) = true := by
  decide

end SSBX.Foundation.R8
