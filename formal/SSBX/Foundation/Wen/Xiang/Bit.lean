/-
# Wen.Xiang.Bit — Layer 0 substrate for the 𝕏ⁿ kernel

This file defines the **substrate** layer (Layer 0 of the Xiang kernel
per `wen-algebra` v0.4 §7.1) used by the atomic `Image` carrier (V₄
inductive in `Image.lean`) and indirectly by the family
`X n := Fin n → Image` (`X.lean`).

The default substrate is `Bool` (classical bit) and `Bit := Bool` is
the alias used throughout the kernel for the two-valued atom-of-an-atom.
A future quantum work may replace the substrate with a `Qbit` type via
the `BitLike` typeclass; this file is the **interface seam** so that
the substitution is a single-line change here, not a sprawling refactor
across `Image`, `X`, `OX`, `Squaring`, `Dot`, and every
`Mapping/*.lean` module.

For the v0.4 phase only the interface is stable; `Qbit` semantics are
deferred (see § 4 below).

## Conventions

- `o` = `false` / 阳 / yang / identity-bit / "open"
- `x` = `true`  / 阴 / yin  / set-bit / "marked"

These conventions are inherited by the OX literal: `OX!"oxoxox"` is
six characters that decode three image atoms (since each `Image` has
two F₂-coordinates).
-/

namespace SSBX.Foundation.Wen.Xiang

/-! ## § 1 `BitLike` typeclass

A `BitLike B` instance lets `B` play the role of a single bit in
`Cell n := Fin n → B`. The contract is the abelian group of exponent 2:

- two distinguished elements `o` (identity) and `x` (set)
- commutative associative XOR with `o` as identity and every element
  self-inverse

Decidable equality on `B` is required separately at use-sites via
`[DecidableEq B]`; this typeclass intentionally does **not** extend
`DecidableEq` so the class definition stays minimal and Lean-version-
neutral.

`Bool` satisfies the contract with `o = false`, `x = true`,
`xor = Bool.xor`. A future `Qbit` instance can plug in here without
touching `Cell` or any mapping module.
-/

class BitLike (B : Type) where
  /-- The identity bit (阳, "o", `false` in the `Bool` substrate). -/
  o : B
  /-- The set bit (阴, "x", `true` in the `Bool` substrate). -/
  x : B
  /-- Componentwise XOR; the group operation of the substrate. -/
  xor : B → B → B
  /-- The two distinguished bits are distinct. -/
  o_ne_x : o ≠ x
  /-- Self-inverse: every bit XORed with itself yields `o`. -/
  xor_self : ∀ b : B, xor b b = o
  /-- `o` is the left identity of XOR. -/
  xor_o_left : ∀ b : B, xor o b = b
  /-- XOR is commutative. -/
  xor_comm : ∀ a b : B, xor a b = xor b a
  /-- XOR is associative. -/
  xor_assoc : ∀ a b c : B, xor (xor a b) c = xor a (xor b c)

namespace BitLike

variable {B : Type} [BitLike B]

theorem xor_o_right (b : B) : xor b (o : B) = b := by
  rw [xor_comm]
  exact xor_o_left b

end BitLike

/-! ## § 2 Default substrate: classical `Bool`

`Bool` is the default substrate. Constructors:

- `false` plays `o` (identity bit, "open")
- `true`  plays `x` (set bit,    "marked")

`Bool.xor` is commutative XOR and provides the abelian-group-of-exponent-2
structure required by `BitLike`.
-/

instance instBitLikeBool : BitLike Bool where
  o := false
  x := true
  xor := Bool.xor
  o_ne_x := by decide
  xor_self := by intro b; cases b <;> rfl
  xor_o_left := by intro b; cases b <;> rfl
  xor_comm := by intro a b; cases a <;> cases b <;> rfl
  xor_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-! ## § 3 The default `Bit` alias

The canonical-carrier files in this cluster reference `Bit` rather than
`Bool` directly so that a future `Qbit` substitution is a single-line
change here.

For v0.4 the substrate is pinned at `Bool`; later phases may
parameterize `Image` by a `BitLike B` argument and provide a `Qbit`
instance.
-/

abbrev Bit : Type := Bool

namespace Bit

/-- The identity bit: 阳, "o", `false` in the `Bool` substrate. -/
abbrev o : Bit := false

/-- The set bit: 阴, "x", `true` in the `Bool` substrate. -/
abbrev x : Bit := true

@[simp] theorem o_def : (o : Bit) = false := rfl
@[simp] theorem x_def : (x : Bit) = true := rfl

/-- Decode an ASCII character (`'o'` / `'x'`) to a `Bit`.
    Anything other than `'x'` decodes to `o`; this matches the
    parse-time contract of `OX["..."]` literals. -/
@[inline] def ofChar : Char → Bit
  | 'x' => x
  | _   => o

@[simp] theorem ofChar_o : ofChar 'o' = o := rfl
@[simp] theorem ofChar_x : ofChar 'x' = x := rfl

/-- Encode a `Bit` back to its ASCII character. -/
@[inline] def toChar : Bit → Char
  | true  => 'x'
  | false => 'o'

@[simp] theorem toChar_o : toChar o = 'o' := rfl
@[simp] theorem toChar_x : toChar x = 'x' := rfl

@[simp] theorem ofChar_toChar (b : Bit) : ofChar (toChar b) = b := by
  cases b <;> rfl

end Bit

/-! ## § 4 Future quantum substrate (interface only)

A future phase will introduce a quantum-bit substrate `Qbit` and a
`BitLike Qbit` instance.  The interface here (the `BitLike` typeclass,
the `Bit := Bool` abbrev, and the `Bit.o` / `Bit.x` / `Bit.ofChar`
helpers) is the seam at which that substitution will happen.

**No `Qbit` definition or quantum semantics is provided in this phase**,
per `wen-algebra` v0.4 §6.1 (the doctrine fixes the substrate at the
classical bit; quantum lifts are explicitly deferred to follow-up work).

TODO (Quantum phase): add `Qbit` carrier + `BitLike Qbit` instance +
measurement semantics + entanglement-aware `Image`.  The
abelian-group-of-exponent-2 contract may need to be relaxed or split
into a weaker base typeclass for non-classical substrates; that
decision is deferred.
-/

end SSBX.Foundation.Wen.Xiang
