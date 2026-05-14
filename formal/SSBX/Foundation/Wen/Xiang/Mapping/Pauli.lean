/-
# Wen.Xiang.Mapping.Pauli — single-qubit Pauli group (mod phase)

The single-qubit Pauli group `P₁` modulo phase `{±1, ±i}` is exactly
V₄ (`wen-algebra` v0.4 §0.2 / `v4-foundation.md` §3.2):

    P₁ / ⟨±1, ±i⟩  ≅  V₄  =  Image

| Pauli | bit pattern | V₄ Math | 文        |
|-------|-------------|---------|-----------|
| `I`   | `Image.oo`  | `e`     | 道         |
| `X`   | `Image.xo`  | `a`     | 错 (bit-flip σₓ)   |
| `Z`   | `Image.ox`  | `b`     | 综 (phase-flip σ_z) |
| `Y`   | `Image.xx`  | `ab`    | 错综 (= iXZ, σ_y) |

The product structure modulo phase:

    X · X = Z · Z = Y · Y = I,
    X · Z = Y,    Z · X = Y,
    X · Y = Z,    Y · X = Z,
    Z · Y = X,    Y · Z = X.

This is exactly the `Image` group multiplication.

## Naming caution

The Pauli `X` aliases `Image.xo` and lives in this module's namespace
(`SSBX.Foundation.Wen.Xiang.Mapping.Pauli.X`).  At the same
time the Xiang kernel exposes the type family
`SSBX.Foundation.Wen.Xiang.X : Nat → Type`.  The two are at
distinct types and in distinct namespaces; ambiguity arises only if a
caller `open`s both `Pauli` and `Xiang`, in which case the
type family must be referred to by its fully qualified name (or via
the layer aliases `Origin / Image1 / PairedImage / Hexagram /
TemporalHexagram`).

## Pauli tensors

A length-`8`-character `OX!` literal gives a `TemporalHexagram = X 4`
cell, which the `Squaring.lean` decomposition `X 4 ≃ X 1⁴` lets us
read as a 4-qubit Pauli tensor `P ⊗ Q ⊗ R ⊗ S`.  The `tensor4` helper
below packages this. -/

import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.X
import SSBX.Foundation.Wen.Xiang.OX
import SSBX.Foundation.Wen.Xiang.Layers
import SSBX.Foundation.Wen.Xiang.Squaring

namespace SSBX.Foundation.Wen.Xiang.Mapping.Pauli

open SSBX.Foundation.Wen.Xiang

/-! ## § 1 Single-qubit Pauli atoms at `Image` -/

/-- Pauli `I` (identity, modulo phase). (= e, 道, dao). -/
abbrev I : Image := .oo

/-- Pauli `X` (bit-flip σₓ, modulo phase). (= a, 错, cuo). -/
abbrev X : Image := .xo

/-- Pauli `Z` (phase-flip σ_z, modulo phase). (= b, 综, zong). -/
abbrev Z : Image := .ox

/-- Pauli `Y` (= iXZ, modulo phase). (= ab, 错综, cuozong). -/
abbrev Y : Image := .xx

/-! ## § 2 Pauli group structure (modulo phase) — `decide`-verified -/

example : X * X = I := by decide
example : Z * Z = I := by decide
example : Y * Y = I := by decide
example : X * Z = Y := by decide
example : Z * X = Y := by decide
example : X * Y = Z := by decide
example : Y * X = Z := by decide
example : Z * Y = X := by decide
example : Y * Z = X := by decide

/-! ## § 3 4-qubit Pauli tensors at `TemporalHexagram = X 4` -/

/-- 4-fold Pauli tensor encoded as a `TemporalHexagram` (`X 4`) cell.

    `tensor4 P Q R S` corresponds to `P ⊗ Q ⊗ R ⊗ S`, with each Pauli
    factor at one image-coordinate of `X 4` via the squaring
    decomposition `X 4 ≃ X 1 × X 1 × X 1 × X 1` (`X.ofQuartic`). -/
def tensor4 (P Q R S : Image) : TemporalHexagram :=
  X.ofQuartic (fun _ => P, fun _ => Q, fun _ => R, fun _ => S)

example : tensor4 I I I I = OX!"oooooooo" := by decide
example : tensor4 X X X X = OX!"xoxoxoxo" := by decide
example : tensor4 Z Z Z Z = OX!"oxoxoxox" := by decide
example : tensor4 Y Y Y Y = OX!"xxxxxxxx" := by decide

/-- Sample mixed 4-qubit Pauli tensor `X ⊗ Z ⊗ X ⊗ Z`. -/
def XZXZ : TemporalHexagram := tensor4 X Z X Z

end SSBX.Foundation.Wen.Xiang.Mapping.Pauli
