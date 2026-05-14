/-
# Foundation.R.Basic — R N := Fin N → Bool, the parametric R-Family carrier

Per `wen-algebra` v0.6 §1.1 and `v4-foundation` v0.5 §0.2:

    R N := F_2^N,   |R N| = 2^N

implemented as `Fin N → Bool`.  This is the **canonical** carrier of the
R-Family tower:

* `R 0` = trivial layer (single empty function)
* `R 1` = bit (the primitive F_2 element)
* `R 2` = Klein four-group (pair-of-bits)
* `R 3` = Fano-plane / 3-bit
* `R 4` = minimum complete unit
* …
* `R 8` = byte / ceiling
* `R N` for N > 8 = constructed via direct-sum/tensor of root layers

The doctrine is **language-independent**: there are *no* Chinese / Pauli /
Yi names anywhere in this directory.  Semantic mappings live in
`Foundation/Atlas/` (P3 of the restructure plan).

## Algebraic content

`R N` is an `F_2`-vector space; we install the `AddCommGroup` instance
by hand using `Bool.xor` coordinate-wise.  Negation is self-inverse
because we are in characteristic 2 (`v + v = 0`).

Helpers:

* `R.zero` — the all-false vector (origin of `R N`).
* `R.constx` — the all-true vector (the "saturating" vector).
* `R.coord` — read coordinate `i` of `v : R N`.
* `R.basis i` — the canonical basis vector `e_i` (true at `i`, false
  elsewhere).
* `R 2` helper atoms `oo / xo / ox / xx` — the four Klein-4 elements
  named **purely by their bit pattern** (no semantic interpretation).

## Doctrinal anchor

* `wen-algebra.md` v0.6 §1 (R-Family Tower Recap), §10.1 (Lean type).
* `v4-foundation.md` v0.5 §0.2 (notation: o/x strings), §1
  (R-Family overview), §4.1–§4.5 (R 2 structure).
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases

namespace SSBX.Foundation.R

/-! ## § 1 The R-Family carrier

`R N` is the N-fold product of `Bool`, i.e. `F_2^N`.  We use `def`
(rather than `abbrev`) so that the layer index `N` is *not* eagerly
inlined and downstream code can talk about `R N` uniformly.  The
operations below provide all the structure that `Pi.addCommGroup`
would give for an `abbrev`. -/

/-- `R N = F_2^N`, the N-th layer of the R-Family tower.  Implemented
    as `Fin N → Bool` so that the bit-pattern is the primary identity
    of every element.

    Per `wen-algebra` v0.6 §1.1 and `v4-foundation` v0.5 §0.2. -/
def R (N : ℕ) : Type := Fin N → Bool

namespace R

variable {N M : ℕ}

/-! ## § 2 Basic structure instances -/

instance instFintype (N : ℕ) : Fintype (R N) :=
  inferInstanceAs (Fintype (Fin N → Bool))

instance instDecidableEq (N : ℕ) : DecidableEq (R N) :=
  inferInstanceAs (DecidableEq (Fin N → Bool))

instance instInhabited (N : ℕ) : Inhabited (R N) := ⟨fun _ => false⟩

/-- Coordinate read: `coord v i = v i`. -/
@[reducible] def coord {N : ℕ} (v : R N) (i : Fin N) : Bool := v i

/-! ## § 3 Group structure (AddCommGroup via XOR)

`R N` carries the `(F_2)^N` additive group, given coordinate-wise by
`Bool.xor`.  Negation is the identity (every element is self-inverse
in characteristic 2). -/

instance instAdd (N : ℕ) : Add (R N) :=
  ⟨fun u v => fun i => Bool.xor (u i) (v i)⟩

instance instZero (N : ℕ) : Zero (R N) := ⟨fun _ => false⟩

instance instNeg (N : ℕ) : Neg (R N) := ⟨id⟩

instance instSub (N : ℕ) : Sub (R N) :=
  ⟨fun u v => fun i => Bool.xor (u i) (v i)⟩

@[simp] theorem add_apply (u v : R N) (i : Fin N) :
    (u + v) i = Bool.xor (u i) (v i) := rfl

@[simp] theorem sub_apply (u v : R N) (i : Fin N) :
    (u - v) i = Bool.xor (u i) (v i) := rfl

@[simp] theorem zero_apply (i : Fin N) : (0 : R N) i = false := rfl

@[simp] theorem neg_apply (v : R N) (i : Fin N) : (-v) i = v i := rfl

theorem xor_self_eq_false (b : Bool) : Bool.xor b b = false := by
  cases b <;> rfl

theorem xor_assoc' (a b c : Bool) :
    Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor_comm' (a b : Bool) : Bool.xor a b = Bool.xor b a := by
  cases a <;> cases b <;> rfl

theorem false_xor (b : Bool) : Bool.xor false b = b := by
  cases b <;> rfl

theorem xor_false (b : Bool) : Bool.xor b false = b := by
  cases b <;> rfl

/-- `R N` is a commutative group of exponent 2 under coordinate-wise XOR. -/
instance instAddCommGroup (N : ℕ) : AddCommGroup (R N) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  sub := (· - ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro u v w; funext i; exact xor_assoc' (u i) (v i) (w i)
  zero_add := by
    intro u; funext i
    show Bool.xor false (u i) = u i
    exact false_xor _
  add_zero := by
    intro u; funext i
    show Bool.xor (u i) false = u i
    exact xor_false _
  neg_add_cancel := by
    intro u; funext i
    show Bool.xor (u i) (u i) = false
    exact xor_self_eq_false _
  add_comm := by
    intro u v; funext i; exact xor_comm' (u i) (v i)

/-- Self-inverse: every `R N` element is its own additive inverse
    (characteristic 2). -/
@[simp] theorem neg_eq_self (v : R N) : -v = v := rfl

/-- Self-cancellation: `v + v = 0` for every `v : R N`. -/
@[simp] theorem add_self (v : R N) : v + v = 0 := by
  funext i; exact xor_self_eq_false _

/-! ## § 4 Distinguished vectors -/

/-- The zero/origin vector `0 : R N`. -/
@[reducible] def zero_vec (N : ℕ) : R N := (0 : R N)

/-- The all-true vector `1...1` of `R N`. -/
def constx (N : ℕ) : R N := fun _ => true

/-- The canonical basis vector `e_i` of `R N`: true at `i`, false
    elsewhere. -/
def basis {N : ℕ} (i : Fin N) : R N := fun j => decide (i = j)

@[simp] theorem basis_self {N : ℕ} (i : Fin N) : basis i i = true := by
  simp [basis]

theorem basis_other {N : ℕ} {i j : Fin N} (h : i ≠ j) :
    basis i j = false := by
  simp [basis, h]

@[simp] theorem constx_apply (N : ℕ) (i : Fin N) :
    (constx N) i = true := rfl

/-! ## § 5 Cardinality -/

/-- `|R N| = 2^N`.  Per `v4-foundation` v0.5 §0.2. -/
theorem card_eq (N : ℕ) : Fintype.card (R N) = 2 ^ N := by
  show Fintype.card (Fin N → Bool) = 2 ^ N
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-! ## § 6 R 0 — the trivial layer -/

/-- `R 0` has a unique element. -/
theorem R0_subsingleton : Subsingleton (R 0) :=
  ⟨fun a b => funext fun i => i.elim0⟩

/-- |R 0| = 1. -/
theorem R0_card : Fintype.card (R 0) = 1 := by
  rw [card_eq]; rfl

/-! ## § 7 R 1 — the bit -/

/-- |R 1| = 2. -/
theorem R1_card : Fintype.card (R 1) = 2 := by
  rw [card_eq]; rfl

/-! ## § 8 R 2 — the Klein-four helper atoms

For the four-element Klein-four group `R 2` we provide bit-pattern
named helper atoms (`oo / xo / ox / xx`).  **These names refer only
to the bit pattern** — they carry no semantic interpretation.  Any
Pauli/Yi/Boolean reading is an Atlas-level overlay (see
`Foundation/Atlas/`). -/

/-- `oo : R 2` = `(false, false)` — the origin of `R 2`. -/
def oo : R 2 := fun _ => false

/-- `xo : R 2` = `(true, false)` — the first basis vector of `R 2`. -/
def xo : R 2 := fun i => decide (i.val = 0)

/-- `ox : R 2` = `(false, true)` — the second basis vector of `R 2`. -/
def ox : R 2 := fun i => decide (i.val = 1)

/-- `xx : R 2` = `(true, true)` — the all-ones vector of `R 2`. -/
def xx : R 2 := fun _ => true

@[simp] theorem oo_apply (i : Fin 2) : oo i = false := rfl

@[simp] theorem xx_apply (i : Fin 2) : xx i = true := rfl

theorem xo_zero : xo ⟨0, by decide⟩ = true := by decide
theorem xo_one  : xo ⟨1, by decide⟩ = false := by decide
theorem ox_zero : ox ⟨0, by decide⟩ = false := by decide
theorem ox_one  : ox ⟨1, by decide⟩ = true := by decide

/-- |R 2| = 4. -/
theorem R2_card : Fintype.card (R 2) = 4 := by
  rw [card_eq]; rfl

/-- Helpful concrete check: `oo + xx = xx` and similar V₄ identities. -/
theorem R2_oo_add_xx : (oo + xx : R 2) = xx := by
  funext i; simp [add_apply, oo, xx]

theorem R2_xx_add_xx : (xx + xx : R 2) = 0 := by
  apply add_self

theorem R2_xo_add_ox : (xo + ox : R 2) = xx := by
  funext i; fin_cases i <;> simp [add_apply, xo, ox, xx]

/-! ## § 9 R 4 / R 8 cardinality sanity -/

theorem R4_card : Fintype.card (R 4) = 16 := by rw [card_eq]; rfl

theorem R8_card : Fintype.card (R 8) = 256 := by rw [card_eq]; rfl

end R

end SSBX.Foundation.R
