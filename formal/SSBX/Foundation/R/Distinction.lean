/-
# Foundation.R.Distinction — the substrate-most-primitive distinction layer

Per `docs-next/10_formal_形式/wen-substrate.md` v1.4 §3.7.8 (Distinction
Monism — the primitive binary mark below operation monism).

This module sits **one level below** the operation-monism layer
(`Foundation/R/OperationMonism.lean`, §3.7) of the R-Family abstraction
tower:

| Doc layer | Object of definition       | Lean realization                     |
|-----------|---------------------------|--------------------------------------|
| §3.7.8    | `Distinction` (= {o, x})  | **this file**                        |
| §3.7      | `RTower X k` (iter. Σ)    | `Foundation/R/OperationMonism.lean`  |
| §3.6      | `RFamily k N := Fin N → k`| `Foundation/R/Parametric.lean`       |
| §1-§3.5   | `R N := Fin N → Bool`     | `Foundation/R/Basic.lean`            |

The point of this file is to articulate the §3.7.8 thesis:

> Before any algebraic structure, before any base `k`, the substrate
> commits only to *the observable binary difference*.  The two marks
> `o` and `x` are abstract distinction-poles; they are *not*
> definitionally `false` / `true`.  The classical computational
> realization `o ↦ false`, `x ↦ true` is one specific bridge — the
> minimum one — into the algebraic layer.

This file is **additive**.  Because the classical realization is an
`Equiv` to `Bool`, and because `R N := Fin N → Bool` is precisely the
`δ = Bool` instance of `R' N δ := Fin N → δ`, no existing R-Family
definition or proof is disturbed.

## Doctrinal lineage

* George Spencer-Brown, *Laws of Form* (1969) — the primary "mark of
  distinction" `( )`.
* Gregory Bateson, *Steps to an Ecology of Mind* (1972) — "a
  difference that makes a difference".
* John Archibald Wheeler, "it from bit" (1990) — the binary observer
  question.
* Yi-jing — the primary binary inscription (yang `⚊` / yin `⚋`),
  whose canonical interpretive overlay is *Atlas-level*, not
  substrate-level.

## Doctrinal anchor

* `wen-substrate.md` v1.4 §3.7.8 (Distinction Monism — primitive
  binary mark).
* `wen-substrate.md` v1.4 §3.7 (Operation Monism — context: this
  file is the layer immediately below §3.7).
-/

import SSBX.Foundation.R.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Basic

namespace SSBX.Foundation.R

/-! ## § 1 The primitive distinction type

`Distinction` is the two-element type carrying the **abstract binary
mark**.  Per wen-substrate v1.4 §3.7.8, the constructors `o` and `x`
are *not* committed to being `false` / `true`; they are the abstract
poles of the observable difference.  The classical computational
realization (`o ↦ false`, `x ↦ true`) is the equivalence
`Distinction.equivBool` below — one minimal bridge into the algebraic
layer, not the definition of `Distinction` itself. -/

/-- The primitive distinction type: two abstract marks `o` and `x`.

    Per `wen-substrate` v1.4 §3.7.8.  The classical computational
    realization is `o ↦ false`, `x ↦ true`; alternative substantive
    readings (yang/yin, ⊥/⊤, |0⟩/|1⟩, silent/sayable, …) are
    Atlas-level overlays. -/
inductive Distinction : Type
  /-- The "negative" pole of the distinction — false / yang / silent /
      ⊥ / |0⟩ in the classical / yi-jing / semantic / logical / quantum
      readings.  Substrate-level: just the mark `o`. -/
  | o
  /-- The "positive" pole of the distinction — true / yin / sayable /
      ⊤ / |1⟩ in the classical / yi-jing / semantic / logical / quantum
      readings.  Substrate-level: just the mark `x`. -/
  | x
  deriving DecidableEq, Repr

namespace Distinction

/-- `Distinction` is a `Fintype` of cardinality two.  Derived via the
    standard Lean machinery for finite enumerated inductives. -/
instance : Fintype Distinction where
  elems := {Distinction.o, Distinction.x}
  complete := by intro d; cases d <;> decide

/-! ## § 2 Classical computational realization (`Bool`-bridge)

The bridge `Distinction ≃ Bool` is the **classical computational
realization** of the substrate.  Per wen-substrate v1.4 §3.7.8: this
equivalence is not the definition of `Distinction`; it is the minimum
named cross-section from substrate into the algebraic (F₂) layer. -/

/-- Map the distinction marks to their classical-computational
    realization in `Bool`: `o ↦ false`, `x ↦ true`. -/
def toBool : Distinction → Bool
  | .o => false
  | .x => true

/-- Inverse map: read a `Bool` as a distinction mark.
    `false ↦ o`, `true ↦ x`. -/
def ofBool : Bool → Distinction
  | false => .o
  | true  => .x

@[simp] theorem toBool_o : toBool .o = false := rfl
@[simp] theorem toBool_x : toBool .x = true  := rfl

@[simp] theorem ofBool_false : ofBool false = .o := rfl
@[simp] theorem ofBool_true  : ofBool true  = .x := rfl

@[simp] theorem ofBool_toBool (d : Distinction) : ofBool (toBool d) = d := by
  cases d <;> rfl

@[simp] theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b <;> rfl

/-- **Classical-computational realization** — the equivalence
    `Distinction ≃ Bool` that bridges the substrate-most-primitive
    distinction layer into the canonical F₂ algebraic layer.

    Per `wen-substrate` v1.4 §3.7.8.  This is the minimum named
    cross-section; alternative bridges (e.g., to `Fin 2`, to a
    `ZMod 2`-element, to a Pauli eigenstate, …) factor through this
    one via `Bool ≃ Fin 2 ≃ ZMod 2 ≃ ⋯` standard equivalences. -/
def equivBool : Distinction ≃ Bool where
  toFun     := toBool
  invFun    := ofBool
  left_inv  := ofBool_toBool
  right_inv := toBool_ofBool

/-! ## § 3 Cardinality sanity -/

/-- `|Distinction| = 2`.  Cards-on-the-table sanity check. -/
theorem card : Fintype.card Distinction = 2 := by decide

end Distinction

/-! ## § 4 The δ-parametric substrate carrier `R'`

`R' N δ := Fin N → δ` is the **substrate-level carrier** over an
arbitrary realization `δ` of the primitive distinction.  This is the
same shape as `RFamily` from `Foundation/R/Parametric.lean`; we restate
it here to keep the §3.7.8 narrative self-contained at the substrate
layer.

When `δ = Bool`, this is *definitionally* `R N` from
`Foundation/R/Basic.lean`.  When `δ = Distinction`, it is equivalent
to `R N` via `Distinction.equivBool`. -/

/-- Substrate-level carrier over a δ-realization of the primitive
    distinction.  When `δ = Bool`, this is *definitionally* `R N`
    from `Foundation/R/Basic.lean`. -/
def R' (N : ℕ) (δ : Type) : Type := Fin N → δ

/-- `R' N δ` is a `Fintype` when `δ` is finite (cardinality `|δ|^N`).
    Lifted directly from the underlying `Fin N → δ` `Pi`-type instance. -/
instance instFintypeR' (N : ℕ) (δ : Type) [Fintype δ] : Fintype (R' N δ) :=
  inferInstanceAs (Fintype (Fin N → δ))

/-- Decidable equality on `R' N δ` when `δ` has decidable equality. -/
instance instDecidableEqR' (N : ℕ) (δ : Type) [DecidableEq δ] :
    DecidableEq (R' N δ) :=
  inferInstanceAs (DecidableEq (Fin N → δ))

/-! ## § 5 Bridge to the existing `R N`

The classical-computational realization of the distinction substrate
**is** the existing F₂ R-Family carrier, in two senses:

* `R' N Bool = R N` is a **definitional equality** — the canonical
  `R N` is literally the `δ = Bool` instance of `R'`.
* `R' N Distinction ≃ R N` is a (non-trivial-by-type, trivial-by-proof)
  equivalence built from `Distinction.equivBool` via `Equiv.arrowCongr`. -/

/-- `R' N Bool` is definitionally `R N`.  The canonical F₂ R-Family
    carrier is the `δ = Bool` instance of the substrate carrier. -/
example (N : ℕ) : R' N Bool = R N := rfl

/-- Same as the previous example, restated as a named theorem for
    downstream use. -/
theorem R'_bool_eq_R (N : ℕ) : R' N Bool = R N := rfl

/-- The classical-computational realization of the distinction
    substrate **is** the F₂ R-Family carrier: `R' N Distinction ≃ R N`,
    via coordinate-wise application of `Distinction.equivBool`.

    Stated as `Nonempty` to keep the substrate level free of any
    chosen-equivalence baggage; concrete callers can unfold or
    re-derive the equivalence as needed. -/
theorem R'_distinction_equiv_R (N : ℕ) :
    Nonempty (R' N Distinction ≃ R N) :=
  ⟨Equiv.arrowCongr (Equiv.refl (Fin N)) Distinction.equivBool⟩

/-! ## § 6 Sanity examples

Cards-on-the-table substrate-level cardinality checks.  These confirm
that the δ-parametric carrier behaves as expected at the canonical
seed levels: `R' 8 Distinction` is the 256-element byte layer (i.e.,
`R 8`), via the classical-computational realization. -/

/-- `Distinction.x.toBool = true` — sanity check of the classical
    bridge at the positive pole. -/
example : Distinction.x.toBool = true := rfl

/-- `Distinction.o.toBool = false` — sanity check of the classical
    bridge at the negative pole. -/
example : Distinction.o.toBool = false := rfl

/-- `R' 8 Distinction` has cardinality `2^8 = 256` — the byte layer
    under the classical-computational realization.  Proven via
    `Fintype.card_fun` to avoid recursion-depth blowup on `decide`. -/
example : Fintype.card (R' 8 Distinction) = 256 := by
  show Fintype.card (Fin 8 → Distinction) = 256
  rw [Fintype.card_fun, Fintype.card_fin, Distinction.card]; rfl

/-- `R' 0 Distinction` is a singleton (cardinality 1). -/
example : Fintype.card (R' 0 Distinction) = 1 := by
  show Fintype.card (Fin 0 → Distinction) = 1
  rw [Fintype.card_fun, Fintype.card_fin, Distinction.card]; rfl

/-- `R' 1 Distinction` is two-valued (cardinality 2). -/
example : Fintype.card (R' 1 Distinction) = 2 := by
  show Fintype.card (Fin 1 → Distinction) = 2
  rw [Fintype.card_fun, Fintype.card_fin, Distinction.card]; rfl

/-- `R' 2 Distinction` is the Klein-four layer (cardinality 4). -/
example : Fintype.card (R' 2 Distinction) = 4 := by
  show Fintype.card (Fin 2 → Distinction) = 4
  rw [Fintype.card_fun, Fintype.card_fin, Distinction.card]; rfl

end SSBX.Foundation.R
