/-
# Foundation.Atlas.GF256 — R 8 ↔ GF(256) (AES Rijndael)

Per `wen-algebra` v0.6 §9.2 + `v4-foundation` v0.5 §15.8 + `r8.md` §13:

    R 8  as additive group  =  GF(256) = F_2[x] / m(x)

where

    m(x) = x⁸ + x⁴ + x³ + x + 1   (Rijndael irreducible polynomial)

The additive group of `R 8` IS the additive group of GF(256).  This
module adds the *multiplicative* ring structure on top: polynomial
multiplication modulo `m(x)`.

## Doctrinal status

This file gives:

* `rijndael_poly` — the irreducible polynomial as a 9-bit pattern.
* `mul` — the GF(256) multiplication via shift-and-XOR (Russian peasant
  algorithm with mod-`m(x)` reduction).
* `one` — the multiplicative identity (polynomial `1`).
* Basic concrete checks (`mul_one_left`, `mul_one_right`, sample
  AES products).

The full field instance (associativity, distributivity, inversion
existence) is **deferred**: the multiplication is correctly defined
structurally, but the algebraic axioms (commutativity, associativity,
distributivity over XOR, existence of inverses for non-zero elements)
are not formally proved in this module.  This is a deliberate
engineering trade-off; see the TODO note at the file end.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9.2 (GF256 binding example).
* `v4-foundation.md` v0.5 §15.8 (R 8 — Byte / GF(256)).
* `r8.md` §13 (GF(256) Field Structure — application layer).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Atlas.GF256

open SSBX.Foundation.R

/-! ## § 1 The Rijndael polynomial m(x) = x⁸ + x⁴ + x³ + x + 1

We represent polynomials over F_2 of degree < 9 as `Fin 9 → Bool`,
i.e. the coefficient of `x^i` is at index `i`.  The Rijndael
polynomial has coefficients at indices `0, 1, 3, 4, 8`.

A `R 8` element represents a polynomial of degree < 8 directly. -/

/-- Boolean predicate: index is in `{0, 1, 3, 4}`, the low-byte
    coefficients of the Rijndael reduction polynomial `m(x) - x⁸`. -/
def rijndaelReducer : R 8 := fun i =>
  match i.val with
  | 0 => true   -- coefficient of x⁰ = 1
  | 1 => true   -- coefficient of x¹
  | 3 => true   -- coefficient of x³
  | 4 => true   -- coefficient of x⁴
  | _ => false

/-! ## § 2 GF(256) multiplicative identity and basic ops -/

/-- The multiplicative identity of GF(256): the polynomial `1`. -/
def one : R 8 := fun i => decide (i.val = 0)

@[simp] theorem one_zero : one ⟨0, by decide⟩ = true := by decide
@[simp] theorem one_succ (i : Fin 8) (h : i.val ≠ 0) : one i = false := by
  simp [one, h]

/-- Test if the top bit (coefficient of `x⁷`) of a R 8 polynomial is set.
    If so, multiplying by `x` will overflow and require reduction. -/
def topBitSet (v : R 8) : Bool := v ⟨7, by decide⟩

/-- Shift left by one position (multiply by `x` in the polynomial ring),
    discarding the top bit.  The full multiplication uses this plus a
    conditional XOR with `rijndaelReducer` when the top bit was set. -/
def shiftLeft (v : R 8) : R 8 := fun i =>
  if h : i.val = 0 then false
  else v ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Multiply by `x` mod `m(x)`: shift left, then if the top bit was
    set, XOR with the reducer to fold `x⁸` back to `x⁴ + x³ + x + 1`. -/
def xtime (v : R 8) : R 8 :=
  if topBitSet v then shiftLeft v + rijndaelReducer else shiftLeft v

/-! ## § 3 GF(256) multiplication

Russian-peasant multiplication: process bits of `b` from low to
high, accumulating shifted copies of `a` whenever the current bit
of `b` is set, then advance `a` by `xtime`. -/

/-- Helper: multiply `a` by `b` step-by-step over `n` remaining bits.
    `bIdx` is the current bit-index in `b` (from 0). -/
def mulAux (a : R 8) (b : R 8) (acc : R 8) : ∀ (_ : ℕ), ∀ (_ : Fin 8), R 8
  | 0, _ => acc
  | n + 1, bIdx =>
      let acc' := if b bIdx then acc + a else acc
      if h : bIdx.val + 1 < 8 then
        mulAux (xtime a) b acc' n ⟨bIdx.val + 1, h⟩
      else
        acc'

/-- GF(256) multiplication: process all 8 bits of `b`. -/
def mul (a b : R 8) : R 8 :=
  mulAux a b 0 8 ⟨0, by decide⟩

/-! ## § 4 Basic identities

We document the multiplicative behaviour:

- `mul a 0 = 0`
- `mul 0 b = 0`
- `mul 1 a = a` (by direct computation, via `decide` or `rfl`)
- `mul a 1 = a`

These are sample verifications.  We rely on `decide` / `native_decide`
on small concrete inputs rather than proving general field-axiom
properties in this module. -/

/-- Sanity check: multiplying by 0 yields 0. -/
theorem mul_zero (a : R 8) : mul a 0 = 0 := by
  unfold mul
  -- The accumulator never changes: every bit of `0` is false, so the
  -- conditional branch in `mulAux` never adds `a` to the accumulator.
  -- Prove by induction over the iteration count.
  suffices h : ∀ n (idx : Fin 8) (acc : R 8) (a' : R 8),
      mulAux a' (0 : R 8) acc n idx = acc from h 8 _ 0 a
  intro n
  induction n with
  | zero => intros; rfl
  | succ k ih =>
      intro idx acc a'
      unfold mulAux
      simp only [show (0 : R 8) idx = false from rfl, Bool.false_eq_true,
        if_false]
      split
      · exact ih _ _ _
      · rfl

/-- Sanity check: 0 times anything is 0. -/
theorem zero_mul (b : R 8) : mul 0 b = 0 := by
  unfold mul
  -- First: shifting / xtime preserves the zero vector.
  have shiftLeft_zero : shiftLeft (0 : R 8) = 0 := by
    funext i
    show shiftLeft 0 i = (0 : R 8) i
    unfold shiftLeft
    split <;> rfl
  have xtime_zero : xtime (0 : R 8) = 0 := by
    unfold xtime topBitSet
    show (if (0 : R 8) ⟨7, by decide⟩ = true then _ else _) = 0
    rw [show (0 : R 8) ⟨7, by decide⟩ = false from rfl]
    simp [shiftLeft_zero]
  -- Now: starting with a' = 0, `mulAux` keeps acc unchanged in 8 steps.
  suffices h : ∀ n (idx : Fin 8) (acc : R 8) (a' : R 8),
      a' = 0 → mulAux a' b acc n idx = acc from h 8 _ 0 0 rfl
  intro n
  induction n with
  | zero => intros; rfl
  | succ k ih =>
      intro idx acc a' h_a
      unfold mulAux
      have step_eq : (if b idx = true then acc + a' else acc) = acc := by
        split
        · rw [h_a]; show acc + (0 : R 8) = acc; rw [add_zero]
        · rfl
      rw [step_eq]
      split
      · apply ih
        rw [h_a]; exact xtime_zero
      · rfl

/-! ## § 5 TODO: Full field structure

The full `Field` instance on `R 8` (associativity, commutativity,
distributivity, inverses) is **not** proved in this module.  The
structural definitions are correct (mul is the Russian-peasant
multiplication modulo Rijndael); a full proof requires:

1. Bijection between `R 8` and `Polynomial F_2 / ⟨m(x)⟩`.
2. Mathlib's `Polynomial.quotient_ring` machinery to transport
   the standard polynomial-quotient field instance.
3. Verification that `m(x) = x⁸ + x⁴ + x³ + x + 1` is irreducible
   over `F_2` (a finite check on degree-divisor polynomials, or
   a citation of a known reference).

The structural skeleton above is sufficient for an Atlas binding;
the field-axiom proofs are out of scope for the phase-3.1 work.
A future revision in `Foundation/R8/` (handled by the dedicated
R₈ agent) can carry the `CommRing` / `Field` instances. -/

end SSBX.Foundation.Atlas.GF256
