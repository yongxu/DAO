/-
# Foundation.Atlas.Greimas — R 2 ↔ Greimas semiotic square

Per `wen-algebra` v0.6 §9.2 and `v4-foundation` v0.5 §15.2:

    R 2  ≃  {A, ¬A, B, ¬B}  (Greimas semiotic square)

The semiotic square is Algirdas J. Greimas' four-term structure used in
structural semiotics: a base term `A`, its contrary `B`, and the two
contradictories `¬A`, `¬B`.  All four together form a Klein-four group
under composition.

## Convention

The bit pattern → semiotic-square assignment is:

| `R 2` atom | Bit pattern | Greimas |
|------------|-------------|---------|
| `oo`       | `(0, 0)`    | `A`     |
| `xo`       | `(1, 0)`    | `notA`  |
| `ox`       | `(0, 1)`    | `B`     |
| `xx`       | `(1, 1)`    | `notB`  |

- First bit toggles the contradiction axis: `A ↔ ¬A`, `B ↔ ¬B`.
- Second bit toggles the contrariety axis: `A ↔ B`, `¬A ↔ ¬B`.

This is one of several valid conventions for the semiotic square; the
choice here pairs the §15.2 doctrine ordering with the `R 2`
bit-pattern ordering.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9.3 (multiple bindings coexist on R 2).
* `v4-foundation.md` v0.5 §15.2 (R 2 — Greimas semiotic square).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Atlas.Greimas

open SSBX.Foundation.R
open SSBX.Foundation.R.R (oo xo ox xx)

/-! ## § 1 The semiotic-square inductive type -/

/-- The four positions of Greimas' semiotic square. -/
inductive Term
  | A
  | notA
  | B
  | notB
deriving DecidableEq, Repr, Inhabited

namespace Term

/-- Display name. -/
def toString : Term → String
  | A    => "A"
  | notA => "¬A"
  | B    => "B"
  | notB => "¬B"

instance : ToString Term := ⟨toString⟩

/-- The list of all four positions in canonical order. -/
def all : List Term := [A, notA, B, notB]

theorem mem_all : ∀ t : Term, t ∈ all
  | A    => by decide
  | notA => by decide
  | B    => by decide
  | notB => by decide

theorem all_nodup : all.Nodup := by decide

instance : Fintype Term where
  elems := ⟨⟦all⟧, all_nodup⟩
  complete := mem_all

end Term

/-! ## § 2 The R 2 ↔ Greimas bijection -/

/-- Map `R 2 → Term` reading bit pattern `(v 0, v 1)`. -/
def fromR2 (v : R 2) : Term :=
  match v ⟨0, by decide⟩, v ⟨1, by decide⟩ with
  | false, false => Term.A
  | true,  false => Term.notA
  | false, true  => Term.B
  | true,  true  => Term.notB

/-- Inverse map. -/
def toR2 : Term → R 2
  | Term.A    => oo
  | Term.notA => xo
  | Term.B    => ox
  | Term.notB => xx

/-! ## § 3 Anchor lemmas on the four atoms -/

theorem fromR2_oo : fromR2 oo = Term.A := by
  simp [fromR2, oo]

theorem fromR2_xo : fromR2 xo = Term.notA := by
  simp [fromR2, xo]

theorem fromR2_ox : fromR2 ox = Term.B := by
  simp [fromR2, ox]

theorem fromR2_xx : fromR2 xx = Term.notB := by
  simp [fromR2, xx]

@[simp] theorem toR2_A    : toR2 Term.A    = oo := rfl
@[simp] theorem toR2_notA : toR2 Term.notA = xo := rfl
@[simp] theorem toR2_B    : toR2 Term.B    = ox := rfl
@[simp] theorem toR2_notB : toR2 Term.notB = xx := rfl

/-! ## § 4 Roundtrip theorems -/

theorem fromR2_toR2 : ∀ t : Term, fromR2 (toR2 t) = t
  | Term.A    => fromR2_oo
  | Term.notA => fromR2_xo
  | Term.B    => fromR2_ox
  | Term.notB => fromR2_xx

theorem toR2_fromR2 (v : R 2) : toR2 (fromR2 v) = v := by
  funext i
  fin_cases i <;>
    (rcases hv0 : v 0 with _ | _ <;>
     rcases hv1 : v 1 with _ | _ <;>
     simp [fromR2, toR2, oo, xo, ox, xx, hv0, hv1])

/-! ## § 5 Equivalence packaging -/

/-- The full bijection `R 2 ≃ Term`. -/
def equiv : R 2 ≃ Term where
  toFun := fromR2
  invFun := toR2
  left_inv := toR2_fromR2
  right_inv := fromR2_toR2

theorem card : Fintype.card Term = 4 := by decide

/-! ## § 6 Semiotic axes -/

/-- The contradiction axis: maps each term to its negation
    (`A ↔ ¬A`, `B ↔ ¬B`).  Realised as XOR with `xo`. -/
def contradiction : Term → Term
  | Term.A    => Term.notA
  | Term.notA => Term.A
  | Term.B    => Term.notB
  | Term.notB => Term.B

/-- The contrariety axis: maps each term to its contrary on the other
    axis (`A ↔ B`, `¬A ↔ ¬B`).  Realised as XOR with `ox`. -/
def contrariety : Term → Term
  | Term.A    => Term.B
  | Term.notA => Term.notB
  | Term.B    => Term.A
  | Term.notB => Term.notA

theorem contradiction_involutive : ∀ t, contradiction (contradiction t) = t
  | Term.A    => rfl
  | Term.notA => rfl
  | Term.B    => rfl
  | Term.notB => rfl

theorem contrariety_involutive : ∀ t, contrariety (contrariety t) = t
  | Term.A    => rfl
  | Term.notA => rfl
  | Term.B    => rfl
  | Term.notB => rfl

end SSBX.Foundation.Atlas.Greimas
