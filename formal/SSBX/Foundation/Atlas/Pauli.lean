/-
# Foundation.Atlas.Pauli — R 2 ↔ Pauli operators mod phase

Per `wen-algebra` v0.6 §9.2 and `v4-foundation` v0.5 §15.2:

    R 2  ≃  {I, X, Y, Z}  (Pauli group mod phase, Klein-four)

This is an **application-layer binding**: a semantic overlay on top of
the language-independent `R 2 := Fin 2 → Bool`.  The core
`Foundation/R/` carries no Pauli naming; everything Pauli-related lives
in this module.

## Convention

The bit pattern → Pauli operator assignment is:

| `R 2` atom | Bit pattern | Pauli |
|------------|-------------|-------|
| `oo`       | `(0, 0)`    | `I`   |
| `xo`       | `(1, 0)`    | `X`   |
| `ox`       | `(0, 1)`    | `Z`   |
| `xx`       | `(1, 1)`    | `Y`   |

This matches the standard symplectic-form convention used in
stabiliser-formalism literature: the first bit indexes `X`-content and
the second bit indexes `Z`-content; `Y = X ⋅ Z` mod phase.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9.2 (Atlas Bindings — Pauli example).
* `v4-foundation.md` v0.5 §15.2 ($R_2$ — Klein-four, Pauli mod phase).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Atlas.Pauli

open SSBX.Foundation.R
open SSBX.Foundation.R.R (oo xo ox xx)

/-! ## § 1 The Pauli operator inductive type -/

/-- The four Pauli operators mod phase. -/
inductive PauliOp
  | I
  | X
  | Y
  | Z
deriving DecidableEq, Repr, Inhabited

namespace PauliOp

/-- Display name. -/
def toString : PauliOp → String
  | I => "I"
  | X => "X"
  | Y => "Y"
  | Z => "Z"

instance : ToString PauliOp := ⟨toString⟩

/-- The list of all four Pauli operators in canonical order. -/
def all : List PauliOp := [I, X, Y, Z]

theorem mem_all : ∀ p : PauliOp, p ∈ all
  | I => by decide
  | X => by decide
  | Y => by decide
  | Z => by decide

theorem all_nodup : all.Nodup := by decide

instance : Fintype PauliOp where
  elems := ⟨⟦all⟧, all_nodup⟩
  complete := mem_all

end PauliOp

/-! ## § 2 The R 2 ↔ Pauli bijection -/

/-- Map `R 2 → PauliOp`.  Reads each `R 2` element via its two
    coordinates `(v 0, v 1)` and assigns by the §1 convention. -/
def fromR2 (v : R 2) : PauliOp :=
  match v ⟨0, by decide⟩, v ⟨1, by decide⟩ with
  | false, false => PauliOp.I
  | true,  false => PauliOp.X
  | false, true  => PauliOp.Z
  | true,  true  => PauliOp.Y

/-- Inverse: each Pauli operator picks the canonical `R 2` representative. -/
def toR2 : PauliOp → R 2
  | PauliOp.I => oo
  | PauliOp.X => xo
  | PauliOp.Y => xx
  | PauliOp.Z => ox

/-! ## § 3 Anchor lemmas on the four named atoms -/

theorem fromR2_oo : fromR2 oo = PauliOp.I := by
  simp [fromR2, oo]

theorem fromR2_xo : fromR2 xo = PauliOp.X := by
  simp [fromR2, xo]

theorem fromR2_ox : fromR2 ox = PauliOp.Z := by
  simp [fromR2, ox]

theorem fromR2_xx : fromR2 xx = PauliOp.Y := by
  simp [fromR2, xx]

@[simp] theorem toR2_I : toR2 PauliOp.I = oo := rfl
@[simp] theorem toR2_X : toR2 PauliOp.X = xo := rfl
@[simp] theorem toR2_Y : toR2 PauliOp.Y = xx := rfl
@[simp] theorem toR2_Z : toR2 PauliOp.Z = ox := rfl

/-! ## § 4 Roundtrip theorems -/

/-- Roundtrip: `fromR2 ∘ toR2 = id` on `PauliOp`. -/
theorem fromR2_toR2 : ∀ p : PauliOp, fromR2 (toR2 p) = p
  | PauliOp.I => fromR2_oo
  | PauliOp.X => fromR2_xo
  | PauliOp.Y => fromR2_xx
  | PauliOp.Z => fromR2_ox

/-- Roundtrip: `toR2 ∘ fromR2 = id` on `R 2`. -/
theorem toR2_fromR2 (v : R 2) : toR2 (fromR2 v) = v := by
  funext i
  have h0 : v ⟨0, by decide⟩ = v 0 := rfl
  have h1 : v ⟨1, by decide⟩ = v 1 := rfl
  fin_cases i <;>
    (rcases hv0 : v 0 with _ | _ <;>
     rcases hv1 : v 1 with _ | _ <;>
     simp [fromR2, toR2, oo, xo, ox, xx, hv0, hv1])

/-! ## § 5 Equivalence packaging -/

/-- The full bijection `R 2 ≃ PauliOp` (mod phase). -/
def equiv : R 2 ≃ PauliOp where
  toFun := fromR2
  invFun := toR2
  left_inv := toR2_fromR2
  right_inv := fromR2_toR2

/-- |Pauli mod phase| = 4 = |R 2|. -/
theorem card : Fintype.card PauliOp = 4 := by decide

end SSBX.Foundation.Atlas.Pauli
