/-
# Foundation.R4.Enumeration — explicit 16 bit-pattern atoms of R 4

Per `r4.md` v0.2 §2 ("complete enumeration"):

`R 4 = F_2^4` has 16 elements indexed by 4-bit patterns `w_0 w_1 w_2 w_3`
written with the convention `o = false`, `x = true`.  This file
introduces a name for each of the 16 elements (`oooo`, `ooox`, …,
`xxxx`) and a single `list16` that enumerates them in canonical order.

These names are **purely bit patterns** — no semantic interpretation
attached.  Any Yi/Pauli/Boolean reading is an Atlas-level overlay
(`Foundation/Atlas/`, P3 work).

## Doctrinal anchor

* `r4.md` v0.2 §2.1 (full table), §2.3 (4×4 layout).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.R4

open SSBX.Foundation.R

/-! ## § 1 Bit-pattern constructor

Build an `R 4` element from four explicit Booleans.  The convention
matches `r4.md §2.1`: position `0` is most significant in the surface
notation `w₀w₁w₂w₃`. -/

/-- Build `R 4` from four Booleans `b₀ b₁ b₂ b₃` placed at coordinates
    `0, 1, 2, 3` respectively. -/
def mk4 (b0 b1 b2 b3 : Bool) : R 4 := fun i =>
  match i.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | _ => b3

@[simp] theorem mk4_zero (b0 b1 b2 b3 : Bool) :
    mk4 b0 b1 b2 b3 ⟨0, by decide⟩ = b0 := rfl

@[simp] theorem mk4_one (b0 b1 b2 b3 : Bool) :
    mk4 b0 b1 b2 b3 ⟨1, by decide⟩ = b1 := rfl

@[simp] theorem mk4_two (b0 b1 b2 b3 : Bool) :
    mk4 b0 b1 b2 b3 ⟨2, by decide⟩ = b2 := rfl

@[simp] theorem mk4_three (b0 b1 b2 b3 : Bool) :
    mk4 b0 b1 b2 b3 ⟨3, by decide⟩ = b3 := rfl

/-! ## § 2 The 16 bit-pattern atoms

Names follow `r4.md §2.1`: four `o/x` characters indicating the bit
pattern.  `o = false`, `x = true`. -/

/-- 0000 — rank 0, zero matrix. -/
def oooo : R 4 := mk4 false false false false

/-- 0001 — rank 1. -/
def ooox : R 4 := mk4 false false false true

/-- 0010 — rank 1. -/
def ooxo : R 4 := mk4 false false true  false

/-- 0011 — rank 1. -/
def ooxx : R 4 := mk4 false false true  true

/-- 0100 — rank 1. -/
def oxoo : R 4 := mk4 false true  false false

/-- 0101 — rank 1. -/
def oxox : R 4 := mk4 false true  false true

/-- 0110 — rank 2 (det 1). The "swap" matrix `[[0,1],[1,0]]`. -/
def oxxo : R 4 := mk4 false true  true  false

/-- 0111 — rank 2 (det 1). -/
def oxxx : R 4 := mk4 false true  true  true

/-- 1000 — rank 1. -/
def xooo : R 4 := mk4 true  false false false

/-- 1001 — rank 2 (det 1). The 2×2 identity `[[1,0],[0,1]]`. -/
def xoox : R 4 := mk4 true  false false true

/-- 1010 — rank 1. -/
def xoxo : R 4 := mk4 true  false true  false

/-- 1011 — rank 2 (det 1). -/
def xoxx : R 4 := mk4 true  false true  true

/-- 1100 — rank 1. -/
def xxoo : R 4 := mk4 true  true  false false

/-- 1101 — rank 2 (det 1). -/
def xxox : R 4 := mk4 true  true  false true

/-- 1110 — rank 2 (det 1). -/
def xxxo : R 4 := mk4 true  true  true  false

/-- 1111 — rank 1 (all-ones). -/
def xxxx : R 4 := mk4 true  true  true  true

/-! ## § 3 Canonical 16-element list -/

/-- The 16 elements of `R 4` in canonical order (row-major over the
    4×4 grid `w₀w₁ × w₂w₃` from `r4.md §2.3`). -/
def list16 : List (R 4) :=
  [ oooo, ooox, ooxo, ooxx,
    oxoo, oxox, oxxo, oxxx,
    xooo, xoox, xoxo, xoxx,
    xxoo, xxox, xxxo, xxxx ]

@[simp] theorem list16_length : list16.length = 16 := rfl

/-- The canonical list exhausts `R 4`: it has 16 elements, equal to
    `|R 4|`. -/
theorem list16_card : list16.length = Fintype.card (R 4) := by
  rw [list16_length, R.R4_card]

/-! ## § 4 The zero atom matches the additive zero -/

theorem oooo_eq_zero : oooo = (0 : R 4) := by
  funext i
  fin_cases i <;> rfl

end SSBX.Foundation.R4
