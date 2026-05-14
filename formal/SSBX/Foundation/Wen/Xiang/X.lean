/-
# Wen.Xiang.X — `X n := Fin n → Image`, the n-fold image family

Per `wen-algebra` v0.4 §1.1–§1.3 the canonical n-th 𝕏-tower carrier is

    𝕏ⁿ := the n-fold direct product of `Image`

i.e. an n-tuple of V₄ atoms.  We render this in Lean as

    abbrev X (n : Nat) : Type := Fin n → Image

with `abbrev` so that all `Pi`-class instances on `Fin n → Image`
(`CommGroup`, `Fintype`, `DecidableEq`, …) are inherited transparently.

| n | `X n`                | |X n|  | bit-string length | layer name (see `Layers.lean`)        |
|---|----------------------|-------|--------------------|---------------------------------------|
| 0 | `X 0` = empty tuple  | 1     | 0                  | `Origin` (太极)                        |
| 1 | `X 1`                | 4     | 2                  | `Image1` (象 / 四象)                   |
| 2 | `X 2`                | 16    | 4                  | `PairedImage` (对象)                   |
| 3 | `X 3`                | 64    | 6                  | `Hexagram` (卦 / 六十四卦)              |
| 4 | `X 4`                | 256   | 8                  | `TemporalHexagram` (时卦)              |

For `n ≥ 5` the family is IR-internal; v0.4 §3.1 forbids surface
exposure beyond `n = 4`.

## Group structure

`Image` is a `CommGroup` (V₄), so `Pi.commGroup` lifts componentwise to
`X n = Fin n → Image`.  All group laws for `X n` come for free; the
explicit `instance` statements below pin them so `inferInstance` does
not have to unfold `abbrev` in user code.

## Naming note

The single character `X` is reused by `Mapping/Pauli.lean` for the Pauli
σ_x atom (`X : Image`).  Both are inhabited at distinct types and live
in distinct namespaces (`Xiang.X : Nat → Type` vs
`Mapping.Pauli.X : Image`); usage may require a fully qualified name
when both are imported.
-/

import SSBX.Foundation.Wen.Xiang.Image
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic

namespace SSBX.Foundation.Wen.Xiang

/-! ## § 1 The `X n` family -/

/-- `X n` = n-fold direct product of `Image`, the canonical 𝕏ⁿ carrier
    of `wen-algebra` v0.4.  Indexed by `Fin n`; values are `Image` atoms
    in each coordinate. -/
abbrev X (n : Nat) : Type := Fin n → Image

namespace X

/-- The all-`oo` element: the n-fold product of V₄ identities.  This is
    the multiplicative identity of `X n` (= 道 in every coordinate). -/
def origin (n : Nat) : X n := fun _ => .oo

@[simp] theorem origin_apply (n : Nat) (i : Fin n) :
    origin n i = .oo := rfl

/-! ## § 2 Group instances inherited from `Pi` + `Image` -/

instance instMul     {n : Nat} : Mul (X n)      := Pi.instMul
instance instOne     {n : Nat} : One (X n)      := Pi.instOne
instance instInv     {n : Nat} : Inv (X n)      := Pi.instInv
instance instCommGroup {n : Nat} : CommGroup (X n) := Pi.commGroup

@[simp] theorem mul_apply {n : Nat} (a b : X n) (i : Fin n) :
    (a * b) i = a i * b i := rfl

@[simp] theorem one_apply {n : Nat} (i : Fin n) :
    (1 : X n) i = .oo := rfl

@[simp] theorem inv_apply {n : Nat} (a : X n) (i : Fin n) :
    a⁻¹ i = a i := rfl

@[simp] theorem one_eq_origin {n : Nat} : (1 : X n) = origin n := rfl

/-- Every `X n` element is self-inverse (V₄ⁿ has exponent 2). -/
@[simp] theorem mul_self {n : Nat} (a : X n) : a * a = 1 := by
  funext i
  exact Image.mul_self (a i)

/-! ## § 3 Decidable equality, finiteness -/

instance instDecidableEq {n : Nat} : DecidableEq (X n) :=
  inferInstanceAs (DecidableEq (Fin n → Image))

instance instFintype {n : Nat} : Fintype (X n) :=
  inferInstanceAs (Fintype (Fin n → Image))

/-! ## § 4 Construction helpers -/

/-- Construct an `X n` from an explicit list of `Image` atoms (length
    `n`).  Useful for tests and surface-level enumeration. -/
def ofList {n : Nat} (l : List Image) (h : l.length = n) : X n :=
  fun i => l.get ⟨i.val, by simp [h, i.isLt]⟩

/-- Recover the `List Image` view of an `X n` cell, in coordinate
    order. -/
def toList {n : Nat} (x : X n) : List Image := List.ofFn x

@[simp] theorem toList_length {n : Nat} (x : X n) :
    (toList x).length = n := List.length_ofFn

/-! ## § 5 Atomic-↔-family bridge `X 1 ≃ Image`

The single-coordinate cell `X 1` is naturally equivalent to the atomic
`Image`.  This is the trivial bottom case of the Xiang squaring chain
and the precondition for every layered mapping (`Mapping/*.lean`) to
read its 1-cell content as an atomic `Image`. -/

/-- `X 1 ≃ Image`: a single-coordinate cell is just an `Image` atom. -/
def equivImage : X 1 ≃ Image where
  toFun u := u 0
  invFun i := fun _ => i
  left_inv u := by
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  right_inv _ := rfl

@[simp] theorem equivImage_apply (u : X 1) : equivImage u = u 0 := rfl

@[simp] theorem equivImage_symm_apply (i : Image) :
    equivImage.symm i = (fun _ => i : X 1) := rfl

end X

end SSBX.Foundation.Wen.Xiang
