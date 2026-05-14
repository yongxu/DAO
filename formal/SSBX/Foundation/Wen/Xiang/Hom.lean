/-
# Wen.Xiang.Hom — `Hom_F₂(X^n, X^m) ≅ Mat_{m×n}(对象)` representation

Per `wen-algebra` v0.4 §6, the F₂-linear map space between two Xiang
cells

    Hom_F₂(𝕏ⁿ, 𝕏ᵐ)  ≅  Mat_{m × n}(对象)

where 对象 = `PairedImage` = `X 2` is itself a 16-element image carrier
seen in **op mode** (= an F₂-linear endomorphism of `Image`).  The
identification
                                  (f : Image → Image)  ↔  (f .xo, f .ox)
realises `Hom_F₂(Image, Image) = X 2`; the matrix lift makes
`Hom_F₂(X^n, X^m)` a `b × a` grid of such 16-element cells.

This file delivers:

* `Op` — the F₂-linear endomorphism of `Image` packaged as `X 2`,
  with an `applyOp` interpretation `(f, x) ↦ f x` per v0.4 §6.4.1.
* `Op.id` / `Op.comp` — identity and composition, witnessing `Op` as
  a monoid under composition.
* `HomMat n m` — `Fin m → Fin n → Op`, a `b × a` grid of `Op`s, with
  `apply` (matrix-vector) and `compose` (matrix-matrix) per v0.4 §6.4.
* `idMat n` — the identity matrix `diag(Op.id, …, Op.id)`.

Per v0.4 §6.3, in surface language `对象` carries a phantom mode tag
(state vs op).  We model that with a simple `Mode` inductive in §1
below, but the kernel work uses `Op` directly (= 对象 in op mode);
the state mode is just `X 2` itself, which already carries the full
`Image`-coord and `CommGroup` structure from `X.lean`.

## Why this lives in the kernel

Per v0.4 §2.5 + §6.5, Hom-closure is the technical underpinning of
the family-level "normalize pass closed under composition" guarantee.
A Hom matrix is itself an `X^{2nm}` (so the kernel stays self-contained
on its own carrier), and the matrix-vs-flat distinction is purely a
view choice — the underlying data is the same.
-/

import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.X
import SSBX.Foundation.Wen.Xiang.Layers
import Mathlib.Data.Fin.Tuple.Basic

namespace SSBX.Foundation.Wen.Xiang

/-! ## § 1 Phantom mode discipline (v0.4 §6.3) -/

namespace Hom

/-- Phantom mode tag for `PairedImage = X 2`.  Per v0.4 §6.3 the same
    16-element data is read either as a *state* (a pair of `Image`
    atoms) or as an *op* (an F₂-linear map `Image → Image`); the mode
    distinguishes these readings without changing the underlying data. -/
inductive Mode where
  | state
  | op
  deriving DecidableEq, Repr

end Hom

/-! ## § 2 `Op` — `Image` endomorphisms as `X 2`

An F₂-linear endomorphism `f : Image → Image` is determined by its
values on the basis atoms `.xo` (= e_α) and `.ox` (= e_β), since
`f .oo = .oo` and `f .xx = f .xo * f .ox` follow by F₂-linearity.

We pack this data as a single `X 2` cell `f` with
`f 0 = f .xo` and `f 1 = f .ox`.  `applyOp` reverses the encoding. -/

/-- An F₂-linear endomorphism of `Image`, encoded as `X 2`:
    `f 0 = image of e_α (= .xo)`, `f 1 = image of e_β (= .ox)`. -/
abbrev Op : Type := X 2

namespace Op

/-- Apply `f : Op` to an `Image` atom, recovering the F₂-linear map
    `Image → Image` it encodes (v0.4 §6.4.1):

      f .oo = .oo
      f .xo = f 0
      f .ox = f 1
      f .xx = f 0 * f 1. -/
def applyOp (f : Op) : Image → Image
  | .oo => .oo
  | .xo => f 0
  | .ox => f 1
  | .xx => f 0 * f 1

@[simp] theorem applyOp_oo (f : Op) : applyOp f .oo = .oo := rfl
@[simp] theorem applyOp_xo (f : Op) : applyOp f .xo = f 0 := rfl
@[simp] theorem applyOp_ox (f : Op) : applyOp f .ox = f 1 := rfl
@[simp] theorem applyOp_xx (f : Op) : applyOp f .xx = f 0 * f 1 := rfl

/-- The identity endomorphism on `Image`, packaged as `Op`.  Per v0.4
    §6.4.3 it sends `.xo ↦ .xo` and `.ox ↦ .ox`, i.e. `id 0 = .xo` and
    `id 1 = .ox`. -/
def id : Op := fun i => if i = 0 then .xo else .ox

@[simp] theorem id_zero : Op.id 0 = .xo := rfl
@[simp] theorem id_one  : Op.id 1 = .ox := rfl

/-- `applyOp Op.id` is the identity on `Image`. -/
@[simp] theorem applyOp_id (x : Image) : applyOp Op.id x = x := by
  cases x <;> rfl

/-- The zero endomorphism `f x = .oo` for all `x`. -/
def zero : Op := fun _ => .oo

@[simp] theorem applyOp_zero (x : Image) : applyOp Op.zero x = .oo := by
  cases x <;> rfl

/-- F₂-linearity of `applyOp`: `g (a * b) = g a * g b` (Image-mul on
    both sides).  Proved by full case split — `a, b ∈ Image` (4 × 4 =
    16 cases) and `g 0, g 1 ∈ Image` (4 × 4 = 16 cases) — each reducing
    to a concrete V₄ multiplication.  This is the algebraic payoff of
    encoding an F₂-linear map by its (e_α, e_β)-image pair. -/
theorem applyOp_mul (g : Op) (a b : Image) :
    applyOp g (a * b) = applyOp g a * applyOp g b := by
  -- Force `g 0` and `g 1` to surface in the goal by unfolding `applyOp`
  -- against the concrete cases of `a` and `b`, then full case-split on
  -- both `g 0` and `g 1` to reduce to concrete V₄ identities.
  cases a <;> cases b <;>
    cases hg0 : g 0 <;> cases hg1 : g 1 <;>
    simp_all [applyOp, Image.mul_def, Image.mul,
              Image.ofBits, Image.alpha, Image.beta]

/-- Composition of `Op`s: `(g ∘ f) 0 = applyOp g (f 0)`,
    `(g ∘ f) 1 = applyOp g (f 1)`.  This realises functional
    composition `g ∘ f : Image → Image` by composing the two
    representative basis values. -/
def comp (g f : Op) : Op := fun i => applyOp g (f i)

@[simp] theorem comp_zero_apply (g f : Op) : (comp g f) 0 = applyOp g (f 0) := rfl
@[simp] theorem comp_one_apply  (g f : Op) : (comp g f) 1 = applyOp g (f 1) := rfl

/-- `applyOp` interacts with `comp` as expected: composition of
    representations equals representation of composition.  The non-
    trivial case is `x = .xx`, which uses `applyOp_mul` to push `g`
    through the `f 0 * f 1` product. -/
@[simp] theorem applyOp_comp (g f : Op) (x : Image) :
    applyOp (comp g f) x = applyOp g (applyOp f x) := by
  cases x
  · rfl
  · rfl
  · rfl
  · -- x = .xx case: uses `applyOp_mul` to commute `g` with `f`'s product.
    show applyOp g (f 0) * applyOp g (f 1) = applyOp g (f 0 * f 1)
    exact (applyOp_mul g (f 0) (f 1)).symm

/-- `Op.id` is a left identity for `comp`. -/
@[simp] theorem id_comp (f : Op) : comp Op.id f = f := by
  funext i
  match i with
  | ⟨0, _⟩ => exact applyOp_id (f 0)
  | ⟨1, _⟩ => exact applyOp_id (f 1)

/-- `Op.id` is a right identity for `comp`. -/
@[simp] theorem comp_id (f : Op) : comp f Op.id = f := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Composition is associative.  The proof is by F₂-linearity at each
    of the two coordinate slots, reduced to `applyOp_comp`. -/
theorem comp_assoc (h g f : Op) : comp (comp h g) f = comp h (comp g f) := by
  funext i
  match i with
  | ⟨0, _⟩ => simp [comp, applyOp_comp]
  | ⟨1, _⟩ => simp [comp, applyOp_comp]

end Op

/-! ## § 3 `HomMat n m` — `b × a` matrix of Ops (v0.4 §6.2)

`HomMat n m = Fin m → Fin n → Op`.  Application sends an `X n` cell to
an `X m` cell coordinate-wise; composition is the obvious matrix
product with `Op` scalars (under `Op.comp`) and `Image` mul as
addition. -/

namespace Hom

/-- `HomMat n m = Fin m → Fin n → Op` — the matrix-of-`Op` representation
    of `Hom_F₂(X n, X m)` (v0.4 §6.2). -/
abbrev HomMat (n m : Nat) : Type := Fin m → Fin n → Op

/-- Application of a `HomMat n m` to an `X n` cell, producing an
    `X m` cell (v0.4 §6.4.1):

      (apply f U) i  =  ⊕_j  (f i j) (U j).

    Implementation note: the `Image`-multiplication `*` plays the role
    of `⊕` (group addition in V₄ = abelian-of-exponent-2). -/
def apply {n m : Nat} (f : HomMat n m) (U : X n) : X m :=
  fun i =>
    (List.finRange n).foldr (fun j acc => Op.applyOp (f i j) (U j) * acc) Image.oo

/-- Composition of two `HomMat`s as the standard matrix product over
    the `(Op.comp, Image.mul)` semiring (v0.4 §6.4.2):

      (g ∘ f) i k  =  ⊕_j  (g i j) ∘ (f j k).

    The "addition" `⊕` here is the F₂-pointwise Image-mul on `Op = X 2`
    (inherited from `Pi.commGroup`); the unit `(1 : Op) = origin 2` is
    the all-`.oo` map. -/
def compose {n m p : Nat} (g : HomMat m p) (f : HomMat n m) : HomMat n p :=
  fun i k =>
    (List.finRange m).foldr
      (fun j acc => Op.comp (g i j) (f j k) * acc) (1 : Op)

/-- The identity `HomMat n n`: a diagonal of `Op.id`s, with the
    `(1 : Op)` map (= `Op.zero`) on off-diagonal positions
    (v0.4 §6.4.3). -/
def idMat (n : Nat) : HomMat n n :=
  fun i j => if i = j then Op.id else (1 : Op)

/-! ## § 4 Sanity: `idMat` apply on concrete cells -/

/-- `apply (idMat 1) (.xx)¹ = (.xx)¹` — concrete smoke test that
    `apply` and `idMat` line up correctly.  Verified by `decide` on the
    fully-concrete `X 1 = Fin 1 → Image` at `Image.xx`. -/
example : apply (idMat 1) (fun _ : Fin 1 => Image.xx)
            = (fun _ : Fin 1 => Image.xx) := by decide

/-- `apply (idMat 1) (.oo)¹ = (.oo)¹`. -/
example : apply (idMat 1) (fun _ : Fin 1 => Image.oo)
            = (fun _ : Fin 1 => Image.oo) := by decide

end Hom

end SSBX.Foundation.Wen.Xiang
