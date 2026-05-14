/-
# Foundation.R4.Bilinear — three-layer bilinear forms specialized to R 4

Per `r4.md` v0.2 §7 ("three layers of bilinear pairings on R 4"):

`R 4` is even-dimensional (`= 2 * 2`), so all three bilinear layers
from `Foundation/R/Bilinear.lean` apply.  This file specializes the
generic constructions to `R 4` and verifies the concrete §7 facts:

* **Layer 0** — dot product `dot4` (Bool-valued, symmetric).
* **Layer 1** — symplectic `sigma4` (alternating; 2 blocks).
* **Layer 2** — quadratic refinements `q4` parameterised by
  `c : Fin 2 → Bool` (4 forms), with **Arf invariant** = `c 0 ⊕ c 1`.

The §7.5 fact "Arf-class internal multiplicity first appears at R 4"
is exhibited concretely: among the 4 refinements,

* **Arf 0**: `q^(0,0)` and `q^(1,1)`
* **Arf 1**: `q^(0,1)` and `q^(1,0)`

## Doctrinal anchor

* `r4.md` v0.2 §7.1 (dot), §7.2 (σ), §7.3 (4 quadratic forms),
  §7.4 (Arf table), §7.5 (Arf internal diversity first occurs at R 4).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.R4.Enumeration

namespace SSBX.Foundation.R4

open SSBX.Foundation.R

/-! ## § 1 Layer 0 — dot product on R 4

Re-export `R.dot` specialized to `R 4`. -/

/-- Dot product on `R 4`, re-exported from `Foundation/R/Bilinear.dot`. -/
def dot4 (u v : R 4) : Bool := R.dot u v

@[simp] theorem dot4_def (u v : R 4) : dot4 u v = R.dot u v := rfl

/-- Symmetry of `dot4`. -/
theorem dot4_symm (u v : R 4) : dot4 u v = dot4 v u :=
  R.dot_symm u v

/-! ## § 2 Layer 1 — symplectic σ on R 4

`R 4 = R (2 * 2)`, so `R.sigma` with `k = 2` applies. -/

/-- Symplectic form on `R 4`: `σ(u, v) = (u₀v₁ ⊕ u₁v₀) ⊕ (u₂v₃ ⊕ u₃v₂)`. -/
def sigma4 (u v : R 4) : Bool :=
  R.sigma (k := 2) u v

@[simp] theorem sigma4_def (u v : R 4) :
    sigma4 u v = R.sigma (k := 2) u v := rfl

/-- σ is symmetric (Bool symmetry of XOR-pairings). -/
theorem sigma4_symm (u v : R 4) : sigma4 u v = sigma4 v u :=
  R.sigma_symm (k := 2) u v

/-- σ is alternating: `σ(v, v) = false` on `R 4`. -/
theorem sigma4_alternating (v : R 4) : sigma4 v v = false :=
  R.sigma_alternating (k := 2) v

/-! ## § 3 Decomposition `dot = σ ⊕ LL` on R 4 -/

/-- Layer-0 / Layer-1 decomposition on `R 4`. -/
theorem dot4_eq_sigma4_xor_LL (u v : R 4) :
    dot4 u v = Bool.xor (sigma4 u v) (R.LL (k := 2) u v) :=
  R.dot_eq_sigma_xor_LL (k := 2) u v

/-! ## § 4 Layer 2 — quadratic refinements with `c : Fin 2 → Bool`

There are `2² = 4` quadratic refinements on `R 4` indexed by
`(c₁, c₂) ∈ Bool × Bool`.  -/

/-- The quadratic refinement on `R 4` selected by `c : Fin 2 → Bool`. -/
def q4 (c : Fin 2 → Bool) (v : R 4) : Bool := R.q c v

@[simp] theorem q4_def (c : Fin 2 → Bool) (v : R 4) : q4 c v = R.q c v := rfl

/-- `q4 c` vanishes on the origin. -/
theorem q4_zero (c : Fin 2 → Bool) : q4 c (0 : R 4) = false :=
  R.q_zero_vec c

/-! ## § 5 Arf invariants of the 4 refinements

Per `r4.md §7.4`: `Arf(q^(c₁, c₂)) = c₁ ⊕ c₂`. -/

/-- The Arf invariant of `q4 c`: `c₀ ⊕ c₁` (over F_2). -/
def arf4 (c : Fin 2 → Bool) : Bool := R.arf c

@[simp] theorem arf4_def (c : Fin 2 → Bool) : arf4 c = R.arf c := rfl

/-- The Arf invariant explicit formula on `R 4`: `arf4 c = c 0 ⊕ c 1`. -/
theorem arf4_explicit (c : Fin 2 → Bool) :
    arf4 c = Bool.xor (c 0) (c 1) := by
  show R.arf c = _
  rw [R.arf_succ]
  show Bool.xor (c 0) (R.arf (fun j : Fin 1 => c j.succ)) = _
  rw [R.arf_succ]
  show Bool.xor (c 0) (Bool.xor (c (Fin.succ 0))
        (R.arf (fun j : Fin 0 => c j.succ.succ))) = _
  rw [show R.arf (fun j : Fin 0 => c j.succ.succ) = false from rfl]
  have h : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := rfl
  rw [h]
  cases c 0 <;> cases c 1 <;> rfl

/-! ## § 6 The Arf-class partition at R 4

The 4 quadratic refinements split 2 + 2 by Arf class.  -/

/-- Refinement `(c₁ = false, c₂ = false)` has Arf 0. -/
example : arf4 (fun i => if i = 0 then false else false) = false := by decide

/-- Refinement `(c₁ = true, c₂ = true)` has Arf 0. -/
example : arf4 (fun _ => true) = false := by decide

/-- Refinement `(c₁ = true, c₂ = false)` has Arf 1. -/
example : arf4 (fun i => if i = 0 then true else false) = true := by decide

/-- Refinement `(c₁ = false, c₂ = true)` has Arf 1. -/
example : arf4 (fun i => if i = 0 then false else true) = true := by decide

/-! ## § 7 Sanity checks on the 16 atoms -/

example : dot4 oooo oooo = false := by decide
example : dot4 xxxx xxxx = false := by decide
example : dot4 xoox xoox = false := by decide
example : dot4 xooo xooo = true := by decide
example : sigma4 oooo oooo = false := by decide
example : sigma4 oxxo oxxo = false := by decide
example : sigma4 xoox oxxo = false := by decide

end SSBX.Foundation.R4
