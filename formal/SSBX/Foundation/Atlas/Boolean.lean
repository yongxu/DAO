/-
# Foundation.Atlas.Boolean — R 4 ↔ 16 Boolean functions of 2 variables

Per `wen-algebra` v0.6 §9.2 and `v4-foundation` v0.5 §15.4:

    R 4 = F_2^4  ≃  Boolean functions  Bool × Bool → Bool

The 4-bit pattern encodes the truth table of a 2-variable Boolean
function:

    w : R 4   ↔   (f(0,0), f(0,1), f(1,0), f(1,1)) = (w 0, w 1, w 2, w 3)

This file gives:

* `toFunction` — `R 4 → (Bool × Bool → Bool)`
* `fromFunction` — `(Bool × Bool → Bool) → R 4`
* Roundtrip theorems
* 16 named common Boolean operators (`falseConst`, `and`, `or`, `xor`,
  `implies`, …, `trueConst`) by their `R 4` bit pattern.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9.3 (application-layer bindings).
* `v4-foundation.md` v0.5 §15.4 (R 4 — 16 Boolean functions of 2 vars).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Atlas.Boolean

open SSBX.Foundation.R

/-! ## § 1 R 4 ↔ Boolean function bijection

The truth-table convention: index `i ∈ {0,1,2,3}` corresponds to the
input `(x, y)` via the standard binary encoding `i = 2·x + y`, i.e.

    i = 0 : (x, y) = (false, false)
    i = 1 : (x, y) = (false, true)
    i = 2 : (x, y) = (true,  false)
    i = 3 : (x, y) = (true,  true)

This matches the lexicographic ordering of `Bool × Bool`. -/

/-- Decode `(x, y) : Bool × Bool` to its truth-table index in `Fin 4`. -/
def indexOf : Bool × Bool → Fin 4
  | (false, false) => ⟨0, by decide⟩
  | (false, true ) => ⟨1, by decide⟩
  | (true,  false) => ⟨2, by decide⟩
  | (true,  true ) => ⟨3, by decide⟩

/-- Encode `i : Fin 4` to a `(x, y) : Bool × Bool` pair. -/
def pairOf : Fin 4 → Bool × Bool
  | ⟨0, _⟩ => (false, false)
  | ⟨1, _⟩ => (false, true )
  | ⟨2, _⟩ => (true,  false)
  | _      => (true,  true )

theorem indexOf_pairOf (i : Fin 4) : indexOf (pairOf i) = i := by
  fin_cases i <;> rfl

theorem pairOf_indexOf : ∀ p : Bool × Bool, pairOf (indexOf p) = p
  | (false, false) => rfl
  | (false, true ) => rfl
  | (true,  false) => rfl
  | (true,  true ) => rfl

/-- The Boolean function of 2 vars encoded by `w : R 4`. -/
def toFunction (w : R 4) : Bool × Bool → Bool :=
  fun p => w (indexOf p)

/-- The `R 4` element encoding a given 2-variable Boolean function. -/
def fromFunction (f : Bool × Bool → Bool) : R 4 :=
  fun i => f (pairOf i)

/-! ## § 2 Roundtrip theorems -/

theorem toFunction_fromFunction (f : Bool × Bool → Bool) :
    toFunction (fromFunction f) = f := by
  funext p
  unfold toFunction fromFunction
  rw [pairOf_indexOf]

theorem fromFunction_toFunction (w : R 4) :
    fromFunction (toFunction w) = w := by
  funext i
  unfold fromFunction toFunction
  rw [indexOf_pairOf]

/-- The full bijection `R 4 ≃ (Bool × Bool → Bool)`. -/
def equiv : R 4 ≃ (Bool × Bool → Bool) where
  toFun := toFunction
  invFun := fromFunction
  left_inv := fromFunction_toFunction
  right_inv := toFunction_fromFunction

/-! ## § 3 R 4 helper — bit-pattern constructor

A private helper to build `R 4` from four explicit Booleans, used to
seed the 16 named Boolean operators below.  This duplicates a helper
in `Foundation/R4/Enumeration.lean` (which Atlas/ cannot depend on);
the duplication is acceptable because Atlas is intentionally
self-contained.  -/

/-- Build `R 4` from four Booleans `b₀ b₁ b₂ b₃` placed at coordinates
    `0, 1, 2, 3` respectively. -/
def mk4 (b0 b1 b2 b3 : Bool) : R 4 := fun i =>
  match i.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | _ => b3

@[simp] theorem mk4_apply_zero (b0 b1 b2 b3 : Bool) :
    mk4 b0 b1 b2 b3 ⟨0, by decide⟩ = b0 := rfl

@[simp] theorem mk4_apply_one (b0 b1 b2 b3 : Bool) :
    mk4 b0 b1 b2 b3 ⟨1, by decide⟩ = b1 := rfl

@[simp] theorem mk4_apply_two (b0 b1 b2 b3 : Bool) :
    mk4 b0 b1 b2 b3 ⟨2, by decide⟩ = b2 := rfl

@[simp] theorem mk4_apply_three (b0 b1 b2 b3 : Bool) :
    mk4 b0 b1 b2 b3 ⟨3, by decide⟩ = b3 := rfl

/-! ## § 4 The 16 named Boolean operators

Truth-table indexing:

    index 0  : input (false, false)
    index 1  : input (false, true)
    index 2  : input (true,  false)
    index 3  : input (true,  true)

Below, the 4-tuple `(b0, b1, b2, b3)` in `mk4` is the truth table in
that order.  E.g. AND has truth table `(false, false, false, true)`. -/

/-- `false` constant. -/
def falseConst : R 4 := mk4 false false false false

/-- AND `x ∧ y`. -/
def and : R 4 := mk4 false false false true

/-- `x ∧ ¬y` (left projection without right). -/
def andNotRight : R 4 := mk4 false false true false

/-- `x` — left projection. -/
def projLeft : R 4 := mk4 false false true true

/-- `¬x ∧ y` (right projection without left). -/
def andNotLeft : R 4 := mk4 false true false false

/-- `y` — right projection. -/
def projRight : R 4 := mk4 false true false true

/-- XOR `x ⊕ y`. -/
def xor : R 4 := mk4 false true true false

/-- OR `x ∨ y`. -/
def or : R 4 := mk4 false true true true

/-- NOR `¬(x ∨ y)`. -/
def nor : R 4 := mk4 true false false false

/-- XNOR / IFF `x ↔ y`. -/
def iff : R 4 := mk4 true false false true

/-- `¬y`. -/
def notRight : R 4 := mk4 true false true false

/-- `x ∨ ¬y` (converse implication). -/
def converse : R 4 := mk4 true false true true

/-- `¬x`. -/
def notLeft : R 4 := mk4 true true false false

/-- `¬x ∨ y` — implication `x → y`. -/
def implies : R 4 := mk4 true true false true

/-- NAND `¬(x ∧ y)`. -/
def nand : R 4 := mk4 true true true false

/-- `true` constant. -/
def trueConst : R 4 := mk4 true true true true

/-! ## § 5 Sanity checks: a few operators do what they say -/

theorem and_truth :
    toFunction and (true, true) = true ∧
    toFunction and (false, true) = false ∧
    toFunction and (true, false) = false ∧
    toFunction and (false, false) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

theorem or_truth :
    toFunction or (true, true) = true ∧
    toFunction or (false, true) = true ∧
    toFunction or (true, false) = true ∧
    toFunction or (false, false) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

theorem xor_truth :
    toFunction xor (true, true) = false ∧
    toFunction xor (false, true) = true ∧
    toFunction xor (true, false) = true ∧
    toFunction xor (false, false) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

theorem implies_truth :
    toFunction implies (true, true) = true ∧
    toFunction implies (false, true) = true ∧
    toFunction implies (true, false) = false ∧
    toFunction implies (false, false) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## § 6 The list of all 16 named operators -/

/-- All 16 named Boolean operators in canonical truth-table order. -/
def all16 : List (R 4) :=
  [ falseConst, and,        andNotRight, projLeft,
    andNotLeft, projRight,  xor,         or,
    nor,        iff,        notRight,    converse,
    notLeft,    implies,    nand,        trueConst ]

theorem all16_length : all16.length = 16 := by decide

end SSBX.Foundation.Atlas.Boolean
