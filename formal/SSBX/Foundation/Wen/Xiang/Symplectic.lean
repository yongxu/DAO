/-
# Wen.Xiang.Symplectic — Layer 1 of the Xiang kernel: σ + L⊗L decomposition

Per `wen-algebra` v0.4 §5.6, the symmetric `Image.dot` (Layer 0) admits a
decomposition

    ⟨u, v⟩  =  σ(u, v)  ⊕  L(u) ∧ L(v)

where

* `Image.symplectic` (= σ) is the canonical **alternating** F₂-bilinear
  form on `Image`:        σ(u, v) := u_α · v_β + u_β · v_α
* `Image.L` is the canonical **diagonal** linear functional:
                          L(v)    := v_α + v_β  (image-diagonal projection)

Together these realise the doctrine's "Layer 1" view of `⟨·, ·⟩`: σ is
the alternating part, `L⊗L` is the rank-1 diagonal correction supported
on the {错, 综} pair.  The kernel of `L` is exactly the {道, 错综}
sub-tower of §3.5, witnessing that ⟨·, ·⟩, σ, L, and the sub-tower are
all the same structural fact under different names.

Per v0.4 §5.6.4 the form lifts to `X n` as orthogonal direct sum
`σⁿ(U, V) := Σᵢ σ(uᵢ, vᵢ)` and the decomposition

    ⟨U, V⟩  =  σⁿ(U, V)  ⊕  Σᵢ L(uᵢ) ∧ L(vᵢ)

continues to hold componentwise.  This file delivers both levels with
their alternating, symmetric, and decomposition theorems.

## Why this file exists

* Layer 0 (`Image.dot` / `X.dot` in `Dot.lean`) is symmetric but **not
  alternating** — `dot xo xo = 1`.  That is wanted for §5 information
  recovery but blocks Heisenberg-style commutation calculations.
* Layer 1 (this file) gives the alternating cousin σ, used for
  symplectic geometry, non-commutative lifts, and the Pauli phase
  algebra.  Layer 2 (`Quadratic.lean`) builds quadratic refinements on
  top of σ for the Arf classification.
-/

import SSBX.Foundation.Wen.Xiang.Image
import SSBX.Foundation.Wen.Xiang.Dot
import SSBX.Foundation.Wen.Xiang.X
import Mathlib.Data.Fin.Tuple.Basic

namespace SSBX.Foundation.Wen.Xiang

namespace Image

/-! ## § 1 The symplectic form σ on `Image` (v0.4 §5.6.2)

    σ(u, v) := u_α · v_β  ⊕  u_β · v_α

In char-2 this is alternating (`σ v v = 0`) and symmetric.  The full
table at the four V₄ atoms matches v0.4 §5.6.2 verbatim. -/

/-- The alternating F₂-bilinear form σ on `Image` (= V₄), the Layer 1
    cousin of `Image.dot`.  Per v0.4 §5.6.2:
    `σ(u, v) := u_α · v_β + u_β · v_α`.  Alternating in char 2, hence
    `σ v v = false` for every `v`. -/
def symplectic (u v : Image) : Bit :=
  Bool.xor (Bool.and u.alpha v.beta) (Bool.and u.beta v.alpha)

@[simp] theorem symplectic_oo_left (u : Image) :
    symplectic .oo u = false := by cases u <;> rfl

@[simp] theorem symplectic_oo_right (u : Image) :
    symplectic u .oo = false := by cases u <;> rfl

/-- σ is symmetric: in char 2, the bilinear pairing
    `u_α · v_β + u_β · v_α` is unchanged when `(u, v)` swap. -/
theorem symplectic_symm (u v : Image) : symplectic u v = symplectic v u := by
  cases u <;> cases v <;> rfl

/-- σ is **alternating**: every self-pairing vanishes.  This is the
    defining property that distinguishes σ from `Image.dot` (which has
    `dot xo xo = 1`). -/
theorem symplectic_alternating (v : Image) : symplectic v v = false := by
  cases v <;> rfl

/-- The full σ-table at the four V₄ atoms (v0.4 §5.6.2). -/
theorem symplectic_table :
    symplectic .xo .ox = true ∧ symplectic .ox .xo = true ∧
    symplectic .xo .xx = true ∧ symplectic .xx .xo = true ∧
    symplectic .ox .xx = true ∧ symplectic .xx .ox = true ∧
    symplectic .xo .xo = false ∧ symplectic .ox .ox = false ∧
    symplectic .xx .xx = false := by decide

/-! ## § 2 The diagonal linear functional `L` (v0.4 §5.6.3)

    L(v) := v_α + v_β

`L` is the F₂-linear "image-diagonal projection" `Image → F₂` whose
kernel is exactly the {道, 错综} sub-tower of §3.5.  This is one of the
three equivalent characterisations of the sub-tower (homomorphism
preservation / isotropy / kernel of L). -/

/-- The image-diagonal projection: `L(v) := v_α + v_β` ∈ F₂.  Per v0.4
    §5.6.3, `ker L = {道, 错综}` is the §3.5 sub-tower at `n = 1`. -/
def L (v : Image) : Bit := Bool.xor v.alpha v.beta

@[simp] theorem L_oo : L .oo = false := rfl
@[simp] theorem L_xo : L .xo = true  := rfl
@[simp] theorem L_ox : L .ox = true  := rfl
@[simp] theorem L_xx : L .xx = false := rfl

/-- `ker L = {道, 错综}` — the §3.5 sub-tower characterised as the
    zero locus of `L`. -/
theorem L_eq_false_iff (v : Image) :
    L v = false ↔ v = .oo ∨ v = .xx := by
  cases v <;> simp [L]

/-! ## § 3 The decomposition `dot = σ ⊕ L⊗L` (v0.4 §5.6.3) -/

/-- The Layer 0 ↔ Layer 1 decomposition of v0.4 §5.6.3:

      ⟨u, v⟩ = σ(u, v) ⊕ L(u) ∧ L(v).

This is the precise sense in which σ is the "alternating projection" of
`Image.dot` and `L⊗L` is the "diagonal rank-1 correction".  The
correction is supported on {错, 综} (where `L = 1`); on the {道, 错综}
sub-tower (where `L = 0`) `dot` and `σ` agree. -/
theorem dot_eq_symplectic_xor_L (u v : Image) :
    Image.dot u v = Bool.xor (symplectic u v) (Bool.and (L u) (L v)) := by
  cases u <;> cases v <;> rfl

end Image

/-! ## § 4 σ on `X n` as orthogonal direct sum (v0.4 §5.6.4) -/

namespace X

/-- F₂-bilinear symplectic form on `X n`: orthogonal direct sum of the
    atomic `Image.symplectic` per coordinate.

    Mirrors `X.dot` in shape — same recursion-on-`n` skeleton, same
    `Fin.tail` peel — so the proofs of symmetry and alternation are
    structurally identical to `dot_symm`. -/
def symplectic : ∀ {n : Nat}, X n → X n → Bit
  | 0,     _, _ => false
  | _ + 1, U, V =>
      Bool.xor (Image.symplectic (U 0) (V 0))
               (symplectic (Fin.tail U) (Fin.tail V))

@[simp] theorem symplectic_zero (U V : X 0) : symplectic U V = false := rfl

theorem symplectic_succ {n : Nat} (U V : X (n + 1)) :
    symplectic U V = Bool.xor (Image.symplectic (U 0) (V 0))
                              (symplectic (Fin.tail U) (Fin.tail V)) := rfl

/-- σⁿ inherits symmetry from atomic `Image.symplectic_symm`. -/
theorem symplectic_symm {n : Nat} (U V : X n) :
    symplectic U V = symplectic V U := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [symplectic_succ, symplectic_succ,
        Image.symplectic_symm (U 0) (V 0), ih (Fin.tail U) (Fin.tail V)]

/-- σⁿ is alternating: every self-pairing vanishes.  Each component
    contributes `Image.symplectic (U i) (U i) = false`, so the XOR-fold
    is `false`. -/
theorem symplectic_alternating {n : Nat} (U : X n) :
    symplectic U U = false := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [symplectic_succ, Image.symplectic_alternating (U 0), ih (Fin.tail U)]
    rfl

/-! ## § 5 The `L`-fold and the Layer 0/1 decomposition on `X n` -/

/-- Coordinate-wise XOR-fold of `Image.L (U i) ∧ Image.L (V i)` over
    `Fin n`.  This is the rank-1 "diagonal correction" term of v0.4
    §5.6.4 lifted to the `X n` tower. -/
def Lfold : ∀ {n : Nat}, X n → X n → Bit
  | 0,     _, _ => false
  | _ + 1, U, V =>
      Bool.xor (Bool.and (Image.L (U 0)) (Image.L (V 0)))
               (Lfold (Fin.tail U) (Fin.tail V))

@[simp] theorem Lfold_zero (U V : X 0) : Lfold U V = false := rfl

theorem Lfold_succ {n : Nat} (U V : X (n + 1)) :
    Lfold U V = Bool.xor (Bool.and (Image.L (U 0)) (Image.L (V 0)))
                         (Lfold (Fin.tail U) (Fin.tail V)) := rfl

/-- Global decomposition (v0.4 §5.6.4):

      ⟨U, V⟩ = σⁿ(U, V) ⊕ Σᵢ L(uᵢ) ∧ L(vᵢ).

The proof is a direct induction on `n`: the atomic case is
`Image.dot_eq_symplectic_xor_L`, and at each step the XOR-fold
preserves the identity by `Bool.xor` re-association (a `decide`
on the substrate-`Bool` algebra). -/
theorem dot_eq_symplectic_xor_Lfold {n : Nat} (U V : X n) :
    X.dot U V = Bool.xor (symplectic U V) (Lfold U V) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [X.dot_succ, symplectic_succ, Lfold_succ,
        Image.dot_eq_symplectic_xor_L (U 0) (V 0),
        ih (Fin.tail U) (Fin.tail V)]
    -- Goal: xor (xor σ_atom L_atom) (xor σ_tail L_tail)
    --     = xor (xor σ_atom σ_tail) (xor L_atom L_tail)
    -- This is a `Bool.xor` rearrangement, decidable by case on the
    -- four bits.
    cases Image.symplectic (U 0) (V 0) <;>
      cases Bool.and (Image.L (U 0)) (Image.L (V 0)) <;>
      cases symplectic (Fin.tail U) (Fin.tail V) <;>
      cases Lfold (Fin.tail U) (Fin.tail V) <;> rfl

end X

end SSBX.Foundation.Wen.Xiang
