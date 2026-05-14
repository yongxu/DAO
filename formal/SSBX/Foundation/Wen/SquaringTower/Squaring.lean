/-
# Wen.SquaringTower.Squaring — `X (a + b) ≃ X a × X b` decompositions

The squaring tower is the chain

    X 1 → X 2 → X 4 → X 8 → …      with     X (2k) ≃ X k × X k

i.e. the cardinality squares at each step (4 → 16 → 256 → 65536 → …).
More generally `X (a + b) ≃ X a × X b`, the standard direct-sum split
on `Fin (a + b) → Image`.

This file delivers:

* `X.append : X a → X b → X (a + b)`            — concatenate cells
* `X.takeLeft  : X (a + b) → X a`               — first `a` images
* `X.takeRight : X (a + b) → X b`               — last `b` images
* `X.split     : X (a + b) → X a × X b`         — pairing form
* `X.splitEquiv : X (a + b) ≃ X a × X b`        — full equivalence
* The three canonical squaring witnesses
    `x2_split / x4_split / x8_split` (= `X 2 ≃ X 1 × X 1`, etc.).
* The `Hexagram + TimeImage = TemporalHexagram` decomposition
    `X 4 ≃ X 3 × X 1` (per `wen-algebra` v0.2 §4.4).
* `X.quarticEquiv : X 4 ≃ X 1 × X 1 × X 1 × X 1` — the full unfolding
    of `TemporalHexagram` as four single-image factors, with both
    round-trip lemmas as `@[simp]`.

All splits use Mathlib's `Fin.append` / `Fin.castAdd` / `Fin.natAdd`
machinery; the structure is identical to the bit-level Cell version
that this file replaces, with `Image` substituted for `Bit`.
-/

import SSBX.Foundation.Wen.SquaringTower.X
import SSBX.Foundation.Wen.SquaringTower.Layers
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Basic

namespace SSBX.Foundation.Wen.SquaringTower

namespace X

/-! ## § 1 General `(a + b)`-split / append -/

/-- Concatenate an `X a` cell with an `X b` cell to obtain `X (a + b)`,
    using `Fin.append`: indices `0 .. a-1` come from the first cell;
    `a .. a+b-1` from the second. -/
def append {a b : Nat} (p : X a) (q : X b) : X (a + b) :=
  Fin.append p q

/-- The first `a` image coordinates of an `X (a + b)` cell. -/
def takeLeft {a b : Nat} (c : X (a + b)) : X a :=
  fun i => c (Fin.castAdd b i)

/-- The last `b` image coordinates of an `X (a + b)` cell. -/
def takeRight {a b : Nat} (c : X (a + b)) : X b :=
  fun j => c (Fin.natAdd a j)

@[simp] theorem takeLeft_apply {a b : Nat} (c : X (a + b)) (i : Fin a) :
    takeLeft c i = c (Fin.castAdd b i) := rfl

@[simp] theorem takeRight_apply {a b : Nat} (c : X (a + b)) (j : Fin b) :
    takeRight c j = c (Fin.natAdd a j) := rfl

@[simp] theorem takeLeft_append {a b : Nat} (p : X a) (q : X b) :
    takeLeft (append p q) = p := by
  funext i
  simp [takeLeft, append, Fin.append_left]

@[simp] theorem takeRight_append {a b : Nat} (p : X a) (q : X b) :
    takeRight (append p q) = q := by
  funext j
  simp [takeRight, append, Fin.append_right]

theorem append_takeLeft_takeRight {a b : Nat} (c : X (a + b)) :
    append (takeLeft c) (takeRight c) = c := by
  funext i
  refine Fin.addCases (motive := fun j =>
      append (takeLeft c) (takeRight c) j = c j) ?_ ?_ i
  · intro k
    simp [append, takeLeft, Fin.append_left]
  · intro k
    simp [append, takeRight, Fin.append_right]

/-- Pair the first `a` and last `b` image coordinates. -/
def split {a b : Nat} (c : X (a + b)) : X a × X b :=
  (takeLeft c, takeRight c)

@[simp] theorem split_append {a b : Nat} (p : X a) (q : X b) :
    split (append p q) = (p, q) := by
  simp [split]

@[simp] theorem append_split {a b : Nat} (c : X (a + b)) :
    append (split c).1 (split c).2 = c :=
  append_takeLeft_takeRight c

/-- The full equivalence `X (a + b) ≃ X a × X b`. -/
def splitEquiv {a b : Nat} : X (a + b) ≃ X a × X b where
  toFun := split
  invFun := fun p => append p.1 p.2
  left_inv := append_split
  right_inv := by intro p; cases p; simp

end X

/-! ## § 2 The three canonical squaring witnesses

`X 2 ≃ X 1 × X 1`, `X 4 ≃ X 2 × X 2`, `X 8 ≃ X 4 × X 4` — the
`T_{k+1} = T_k × T_k` chain that gives the squaring tower its name.
For `n ≥ 5` the family is IR-internal but the witness is the same
`X.splitEquiv` shape. -/

/-- The atomic squaring step: `X 2 ≃ X 1 × X 1`. -/
def x2_split : X 2 ≃ X 1 × X 1 := X.splitEquiv (a := 1) (b := 1)

/-- The first non-trivial squaring step: `X 4 ≃ X 2 × X 2`
    (= `PairedImage × PairedImage`). -/
def x4_split : X 4 ≃ X 2 × X 2 := X.splitEquiv (a := 2) (b := 2)

/-- The final surface-layer squaring step: `X 8 ≃ X 4 × X 4`
    (= `TemporalHexagram × TemporalHexagram`).  `X 8` is IR-internal
    per v0.2 §3.1; this witness is exposed for use in normalize-pass
    bookkeeping where doubled cells appear as intermediates. -/
def x8_split : X 8 ≃ X 4 × X 4 := X.splitEquiv (a := 4) (b := 4)

/-! ## § 3 The temporal-hexagram split (`wen-algebra` v0.2 §4.4)

`TemporalHexagram = X 4 = X 3 × X 1 = Hexagram × Image1`.  The first
three image coordinates are the `Hexagram` factor; the fourth is the
`Time-Image` factor (`{Atemporal, Not-Yet, Already, Composite-Now}` in
the temporal reading per v0.2 §0.2). -/

/-- The canonical 卦 ⊕ 时 split: `TemporalHexagram ≃ Hexagram × Image1`.
    The `Image1` factor is the time-image coordinate (= the "4th 象"
    of `X 4`, per v0.2 §4.4). -/
def temporal_split : TemporalHexagram ≃ Hexagram × Image1 :=
  X.splitEquiv (a := 3) (b := 1)

/-! ## § 4 Iterated `R₂`-quartic decomposition

`X 4 ≃ X 1 × X 1 × X 1 × X 1` — the full unfolding of `TemporalHexagram`
as four single-image factors.  Useful when threading position-wise
mappings (e.g. Pauli `I ⊗ X ⊗ Z ⊗ Y` tensors) through the squaring
tower; see `Mapping/Pauli.lean` for the tensor4 helper.

Defined via direct `X.append` chains rather than wrapping
`splitEquiv` to keep the `simp` reduction path short.  Both round-trip
lemmas (`quartic_ofQuartic` / `ofQuartic_quartic`) are `@[simp]`, and
the equivalence is packaged as `X.quarticEquiv`. -/

namespace X

/-- Inverse of `quartic`: assemble four single-image cells into an
    `X 4` cell using two `X.append` steps. -/
def ofQuartic (p : X 1 × X 1 × X 1 × X 1) : X 4 :=
  X.append (X.append p.1 p.2.1) (X.append p.2.2.1 p.2.2.2)

/-- `X 4 → X 1 × X 1 × X 1 × X 1` via two `X.split` steps. -/
def quartic (c : X 4) : X 1 × X 1 × X 1 × X 1 :=
  let h := X.takeLeft (a := 2) (b := 2) c
  let t := X.takeRight (a := 2) (b := 2) c
  (X.takeLeft (a := 1) (b := 1) h,
   X.takeRight (a := 1) (b := 1) h,
   X.takeLeft (a := 1) (b := 1) t,
   X.takeRight (a := 1) (b := 1) t)

@[simp] theorem quartic_ofQuartic (p : X 1 × X 1 × X 1 × X 1) :
    quartic (ofQuartic p) = p := by
  rcases p with ⟨h1, h2, h3, h4⟩
  simp [quartic, ofQuartic]

@[simp] theorem ofQuartic_quartic (c : X 4) : ofQuartic (quartic c) = c := by
  simp [ofQuartic, quartic, append_takeLeft_takeRight]

/-- The full equivalence `X 4 ≃ X 1⁴`, packaged from `ofQuartic` and
    `quartic`.  Useful when threading 4-qubit Pauli tensors through the
    squaring tower (see `Mapping/Pauli.lean.tensor4`). -/
def quarticEquiv : X 4 ≃ X 1 × X 1 × X 1 × X 1 where
  toFun := quartic
  invFun := ofQuartic
  left_inv := ofQuartic_quartic
  right_inv := quartic_ofQuartic

end X

end SSBX.Foundation.Wen.SquaringTower
