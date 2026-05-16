/-
# `SSBX.Foundation.Wen.Embeddings.StabilizerQM` — stabilizer-formalism QM (Pauli group) ↪ `R (2 * n)`

**Phase 3 Stream C3 (GUT roadmap G3 case 3) — T2 universality case study #3.**

Per `docs-next/10_formal_形式/gut-roadmap.md` Phase 3 Stream C3: the
**n-qubit Pauli group modulo center** `𝒫_n / ⟨iI⟩` is isomorphic to the
F₂-symplectic space `R (2 * n)`.  This is the canonical example of
"stabilizer-QM = F₂-symplectic = R-family" that runs through all of
quantum-information theory (Nielsen & Chuang §10; Gottesman PhD thesis).

The point of the case study is **not** to do quantum mechanics inside
`R N` — it is to *witness* that one of the most-used algebraic
structures in QM (the Pauli group mod phase) factors transparently
through the R-Family carrier, with `sigma` as the symplectic form.

## The embedded fragment

We embed **n-qubit Pauli operators modulo the centre `⟨iI⟩`**.  After
modding out the centre, every Pauli operator at qubit `i` is one of
four base operators:

    I   = identity      (xBit, zBit) = (false, false)
    X   = bit-flip      (xBit, zBit) = (true,  false)
    Z   = phase-flip    (xBit, zBit) = (false, true )
    Y   = X · Z (mod i) (xBit, zBit) = (true,  true )

An n-qubit Pauli operator (mod phase) is then `PauliN n := Fin n →
PauliBase`, and its R-Family embedding `pauliToR : PauliN n → R (2*n)`
sends qubit `i ∈ Fin n` to coordinates `2*i` (X-content) and `2*i+1`
(Z-content) in `R (2 * n)`.

## Theorems proved

* **Round-trip** (`pauliToR_rToPauli` / `rToPauli_pauliToR`):
  the embedding is a bijection `PauliN n ≃ R (2 * n)`.
* **Composition is XOR** (`pauliToR_compose`):
  Pauli composition modulo phase factors through F₂-addition in
  `R (2*n)`.  This is **the** core identity of the stabilizer
  formalism — the reason stabilizer codes are tractable.
* **Single-qubit V₄ bridge** (`PauliN_one_equiv_V4` /
  `pauliToR_one_equiv_R2`):  `PauliN 1 ≃ V₄ ≃ R 2`.  The four base
  operators correspond exactly to V₄'s `dao / cuo / cuoZong / zong`.

## The `R (2 * n)` symplectic interpretation

The symplectic form `sigma : R (2 * n) → R (2 * n) → Bool` on the
embedded F₂-pattern gives the (mod-phase) commutator of two Pauli
operators:

    σ(pauliToR p, pauliToR q) = 0  ⟺  p and q commute (mod phase)
    σ(pauliToR p, pauliToR q) = 1  ⟺  p and q anticommute (mod phase)

This is the **central observation** in stabilizer-code theory.  We
state this connection on the single-qubit case (where it reduces to
the standard {I, X, Y, Z} multiplication table) and leave the n-qubit
generalisation as a corollary of `pauliToR_compose`.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` Phase 3 Stream C3 (this file).
* `wen-algebra.md` v0.6 §9.2 (Atlas Pauli binding at n = 1).
* `wen-substrate.md` v1.4 §3.7 (operation monism: Pauli-mod-phase as
  F₂-bit-pattern is the canonical operation-content collapse for QM).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.Hierarchy.Operators.V4.Core

namespace SSBX.Foundation.Wen.Embeddings.StabilizerQM

open SSBX.Foundation.R
open SSBX.Foundation.Hierarchy.Operators (V4)

/-! ## § 1 The Pauli base — single-qubit operators mod phase

The Pauli group mod the centre `⟨iI⟩` has exactly four elements at
each qubit: `{I, X, Y, Z}`.  These form a Klein-four group under
multiplication (mod phase), isomorphic to V₄ ≅ R 2. -/

/-- The four single-qubit Pauli operators **mod phase** `⟨iI⟩`.
    Picking representatives `I = id`, `X = bit-flip`, `Z = phase-flip`,
    `Y = X · Z` (up to phase) yields a Klein-four group. -/
inductive PauliBase : Type where
  | I
  | X
  | Z
  | Y
deriving DecidableEq, Repr, Inhabited

namespace PauliBase

/-- The list of all four Pauli base operators. -/
def all : List PauliBase := [I, X, Z, Y]

theorem all_length : all.length = 4 := rfl

theorem all_nodup : all.Nodup := by decide

theorem mem_all : ∀ p : PauliBase, p ∈ all
  | I => by decide
  | X => by decide
  | Y => by decide
  | Z => by decide

instance : Fintype PauliBase where
  elems := ⟨⟦all⟧, all_nodup⟩
  complete := mem_all

/-- The "X-content" bit: `1` iff the operator has an `X` factor.

    I → 0, X → 1, Z → 0, Y → 1. -/
def xBit : PauliBase → Bool
  | I => false
  | X => true
  | Z => false
  | Y => true

/-- The "Z-content" bit: `1` iff the operator has a `Z` factor.

    I → 0, X → 0, Z → 1, Y → 1. -/
def zBit : PauliBase → Bool
  | I => false
  | X => false
  | Z => true
  | Y => true

/-- Recover a Pauli base from its `(xBit, zBit)` pair. -/
def ofBits : Bool → Bool → PauliBase
  | false, false => I
  | true,  false => X
  | false, true  => Z
  | true,  true  => Y

@[simp] theorem ofBits_I : ofBits false false = I := rfl
@[simp] theorem ofBits_X : ofBits true  false = X := rfl
@[simp] theorem ofBits_Z : ofBits false true  = Z := rfl
@[simp] theorem ofBits_Y : ofBits true  true  = Y := rfl

@[simp] theorem xBit_ofBits (x z : Bool) : xBit (ofBits x z) = x := by
  cases x <;> cases z <;> rfl

@[simp] theorem zBit_ofBits (x z : Bool) : zBit (ofBits x z) = z := by
  cases x <;> cases z <;> rfl

@[simp] theorem ofBits_bits (p : PauliBase) : ofBits p.xBit p.zBit = p := by
  cases p <;> rfl

/-! ## § 1.2 Composition mod phase

Pauli composition modulo `⟨iI⟩` is **XOR componentwise** on the
`(xBit, zBit)` pair.  This is the canonical observation underlying
stabilizer-code theory: forgetting phase reduces Pauli multiplication
to F₂-addition. -/

/-- Composition of two Pauli base operators mod phase. -/
def compose (p q : PauliBase) : PauliBase :=
  ofBits (Bool.xor p.xBit q.xBit) (Bool.xor p.zBit q.zBit)

@[simp] theorem compose_I_left (p : PauliBase) : compose I p = p := by
  cases p <;> rfl

@[simp] theorem compose_I_right (p : PauliBase) : compose p I = p := by
  cases p <;> rfl

@[simp] theorem compose_self (p : PauliBase) : compose p p = I := by
  cases p <;> rfl

theorem compose_comm (p q : PauliBase) : compose p q = compose q p := by
  cases p <;> cases q <;> rfl

theorem compose_assoc (p q r : PauliBase) :
    compose (compose p q) r = compose p (compose q r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- Pauli base mod phase is a Klein-four group. -/
theorem klein_four_summary :
    all.length = 4
    ∧ (∀ p : PauliBase, compose I p = p)
    ∧ (∀ p : PauliBase, compose p p = I)
    ∧ (∀ p q : PauliBase, compose p q = compose q p)
    ∧ (∀ p q r : PauliBase, compose (compose p q) r
        = compose p (compose q r)) :=
  ⟨all_length, compose_I_left, compose_self, compose_comm, compose_assoc⟩

end PauliBase

/-! ## § 2 The n-qubit Pauli type and the R (2 * n) embedding -/

/-- An n-qubit Pauli operator modulo the centre `⟨iI⟩`: a function
    assigning a base operator to each qubit. -/
@[reducible] def PauliN (n : ℕ) : Type := Fin n → PauliBase

namespace PauliN

variable {n : ℕ}

/-- Tensor product / pointwise composition of two n-qubit Pauli operators
    mod phase. -/
def compose (p q : PauliN n) : PauliN n := fun i => (p i).compose (q i)

/-- The identity n-qubit Pauli operator. -/
def one (n : ℕ) : PauliN n := fun _ => PauliBase.I

@[simp] theorem compose_one_left (p : PauliN n) :
    compose (one n) p = p := by
  funext i; exact PauliBase.compose_I_left _

@[simp] theorem compose_one_right (p : PauliN n) :
    compose p (one n) = p := by
  funext i; exact PauliBase.compose_I_right _

@[simp] theorem compose_self (p : PauliN n) :
    compose p p = one n := by
  funext i; exact PauliBase.compose_self _

theorem compose_comm (p q : PauliN n) : compose p q = compose q p := by
  funext i; exact PauliBase.compose_comm _ _

theorem compose_assoc (p q r : PauliN n) :
    compose (compose p q) r = compose p (compose q r) := by
  funext i; exact PauliBase.compose_assoc _ _ _

end PauliN

/-! ## § 3 The embedding `pauliToR : PauliN n → R (2 * n)`

Per the convention in the file docstring: qubit `i` contributes
**two** bits to `R (2 * n)`:

* bit at index `2 * i`     — the X-content of qubit `i`
* bit at index `2 * i + 1` — the Z-content of qubit `i`

The map is a group isomorphism w.r.t. Pauli composition mod phase
↔ F₂-addition (XOR), per the symplectic-form convention used in
stabilizer-code literature. -/

/-- Helper: from `k : Fin (2 * n)` we get `k.val / 2 < n`. -/
private theorem qubitIdx_lt {n : ℕ} (k : Fin (2 * n)) : k.val / 2 < n := by
  have h := k.isLt
  omega

/-- Helper: from `i : Fin n` we get `2 * i.val < 2 * n`. -/
private theorem twoI_lt {n : ℕ} (i : Fin n) : 2 * i.val < 2 * n := by
  have h := i.isLt; omega

/-- Helper: from `i : Fin n` we get `2 * i.val + 1 < 2 * n`. -/
private theorem twoI1_lt {n : ℕ} (i : Fin n) : 2 * i.val + 1 < 2 * n := by
  have h := i.isLt; omega

/-- Map an n-qubit Pauli operator to its `R (2 * n)` bit pattern.
    Even index `2 * i` holds the X-content of qubit `i`; odd index
    `2 * i + 1` holds the Z-content. -/
def pauliToR {n : ℕ} (p : PauliN n) : R (2 * n) :=
  fun k => if k.val % 2 = 0
            then (p ⟨k.val / 2, qubitIdx_lt k⟩).xBit
            else (p ⟨k.val / 2, qubitIdx_lt k⟩).zBit

/-- Inverse map: read off qubit `i`'s `(xBit, zBit)` from coordinates
    `2*i` and `2*i+1`. -/
def rToPauli {n : ℕ} (v : R (2 * n)) : PauliN n :=
  fun i => PauliBase.ofBits
    (v ⟨2 * i.val,     twoI_lt i⟩)
    (v ⟨2 * i.val + 1, twoI1_lt i⟩)

/-! ## § 4 Round-trip / faithfulness -/

/-- Helper: pauliToR at the even position `2*i` extracts `xBit`. -/
private theorem pauliToR_even {n : ℕ} (p : PauliN n) (i : Fin n) :
    (pauliToR p) ⟨2 * i.val, twoI_lt i⟩ = (p i).xBit := by
  unfold pauliToR
  have hMod : (2 * i.val) % 2 = 0 := by omega
  have hDiv : (2 * i.val) / 2 = i.val := by omega
  -- Show the if reduces and the index reconstructs.
  show (if (2 * i.val : Nat) % 2 = 0
        then (p ⟨(2 * i.val : Nat) / 2,
                qubitIdx_lt (⟨2 * i.val, twoI_lt i⟩ : Fin (2 * n))⟩).xBit
        else (p ⟨(2 * i.val : Nat) / 2,
                qubitIdx_lt (⟨2 * i.val, twoI_lt i⟩ : Fin (2 * n))⟩).zBit)
      = (p i).xBit
  rw [if_pos hMod]
  -- Goal: (p ⟨2 * i.val / 2, _⟩).xBit = (p i).xBit
  -- Use a Fin equality + congr_arg
  have hFin : (⟨(2 * i.val : Nat) / 2,
                qubitIdx_lt (⟨2 * i.val, twoI_lt i⟩ : Fin (2 * n))⟩ : Fin n)
              = i := by
    apply Fin.ext
    show (2 * i.val : Nat) / 2 = i.val
    exact hDiv
  rw [hFin]

/-- Helper: pauliToR at the odd position `2*i+1` extracts `zBit`. -/
private theorem pauliToR_odd {n : ℕ} (p : PauliN n) (i : Fin n) :
    (pauliToR p) ⟨2 * i.val + 1, twoI1_lt i⟩ = (p i).zBit := by
  unfold pauliToR
  have hMod : (2 * i.val + 1) % 2 = 1 := by omega
  have hNot : ¬ ((2 * i.val + 1 : Nat) % 2 = 0) := by omega
  have hDiv : (2 * i.val + 1) / 2 = i.val := by omega
  show (if (2 * i.val + 1 : Nat) % 2 = 0
        then (p ⟨(2 * i.val + 1 : Nat) / 2,
                qubitIdx_lt (⟨2 * i.val + 1, twoI1_lt i⟩ : Fin (2 * n))⟩).xBit
        else (p ⟨(2 * i.val + 1 : Nat) / 2,
                qubitIdx_lt (⟨2 * i.val + 1, twoI1_lt i⟩ : Fin (2 * n))⟩).zBit)
      = (p i).zBit
  rw [if_neg hNot]
  have hFin : (⟨(2 * i.val + 1 : Nat) / 2,
                qubitIdx_lt (⟨2 * i.val + 1, twoI1_lt i⟩ : Fin (2 * n))⟩ : Fin n)
              = i := by
    apply Fin.ext
    show (2 * i.val + 1 : Nat) / 2 = i.val
    exact hDiv
  rw [hFin]

/-- One direction: reading back gives the original. -/
theorem rToPauli_pauliToR {n : ℕ} (p : PauliN n) :
    rToPauli (pauliToR p) = p := by
  funext i
  show PauliBase.ofBits
        ((pauliToR p) ⟨2 * i.val,     twoI_lt i⟩)
        ((pauliToR p) ⟨2 * i.val + 1, twoI1_lt i⟩)
      = p i
  rw [pauliToR_even, pauliToR_odd]
  exact PauliBase.ofBits_bits _

/-- The other direction: rebuilding from bits gives back the same bit
    pattern. -/
theorem pauliToR_rToPauli {n : ℕ} (v : R (2 * n)) :
    pauliToR (rToPauli v) = v := by
  funext k
  by_cases hk : k.val % 2 = 0
  · -- k = 2 * j with j = k.val / 2
    have hKDiv : 2 * (k.val / 2) = k.val := by omega
    have hKEq : (⟨2 * (k.val / 2), twoI_lt ⟨k.val / 2, qubitIdx_lt k⟩⟩
                  : Fin (2 * n)) = k := by
      apply Fin.ext
      show 2 * (k.val / 2) = k.val
      exact hKDiv
    -- pauliToR (rToPauli v) k via the even helper
    show (pauliToR (rToPauli v)) k = v k
    have step := pauliToR_even (rToPauli v) ⟨k.val / 2, qubitIdx_lt k⟩
    -- step : (pauliToR (rToPauli v)) ⟨2 * (k.val/2), ...⟩
    --     = ((rToPauli v) ⟨k.val/2, _⟩).xBit
    have lhs_eq : (pauliToR (rToPauli v)) k
        = (pauliToR (rToPauli v)) ⟨2 * (k.val / 2),
                                    twoI_lt ⟨k.val / 2, qubitIdx_lt k⟩⟩ := by
      rw [hKEq]
    rw [lhs_eq, step]
    -- Now goal: ((rToPauli v) ⟨k.val/2, _⟩).xBit = v k
    show (PauliBase.ofBits
            (v ⟨2 * (k.val / 2), twoI_lt ⟨k.val / 2, qubitIdx_lt k⟩⟩)
            (v ⟨2 * (k.val / 2) + 1, twoI1_lt ⟨k.val / 2, qubitIdx_lt k⟩⟩)).xBit
        = v k
    rw [PauliBase.xBit_ofBits]
    -- Goal: v ⟨2 * (k.val/2), _⟩ = v k.  Use hKEq.
    rw [hKEq]
  · -- k.val % 2 = 1, so k = 2*j + 1
    have hKDiv : 2 * (k.val / 2) + 1 = k.val := by omega
    have hKEq : (⟨2 * (k.val / 2) + 1, twoI1_lt ⟨k.val / 2, qubitIdx_lt k⟩⟩
                  : Fin (2 * n)) = k := by
      apply Fin.ext
      show 2 * (k.val / 2) + 1 = k.val
      exact hKDiv
    show (pauliToR (rToPauli v)) k = v k
    have step := pauliToR_odd (rToPauli v) ⟨k.val / 2, qubitIdx_lt k⟩
    have lhs_eq : (pauliToR (rToPauli v)) k
        = (pauliToR (rToPauli v)) ⟨2 * (k.val / 2) + 1,
                                    twoI1_lt ⟨k.val / 2, qubitIdx_lt k⟩⟩ := by
      rw [hKEq]
    rw [lhs_eq, step]
    show (PauliBase.ofBits
            (v ⟨2 * (k.val / 2), twoI_lt ⟨k.val / 2, qubitIdx_lt k⟩⟩)
            (v ⟨2 * (k.val / 2) + 1, twoI1_lt ⟨k.val / 2, qubitIdx_lt k⟩⟩)).zBit
        = v k
    rw [PauliBase.zBit_ofBits]
    rw [hKEq]

/-- The full bijection `PauliN n ≃ R (2 * n)`. -/
def equiv (n : ℕ) : PauliN n ≃ R (2 * n) where
  toFun := pauliToR
  invFun := rToPauli
  left_inv := rToPauli_pauliToR
  right_inv := pauliToR_rToPauli

/-! ## § 5 Composition is XOR mod phase

The core stabilizer-formalism identity: Pauli composition modulo the
centre `⟨iI⟩` is **F₂-addition** on the R-family carrier.  This is the
property that makes stabilizer codes a practical computational tool
(efficient simulation, syndrome extraction, etc.). -/

/-- The bit-translation of `compose` at the base level. -/
theorem PauliBase_xBit_compose (p q : PauliBase) :
    (PauliBase.compose p q).xBit = Bool.xor p.xBit q.xBit := by
  cases p <;> cases q <;> rfl

theorem PauliBase_zBit_compose (p q : PauliBase) :
    (PauliBase.compose p q).zBit = Bool.xor p.zBit q.zBit := by
  cases p <;> cases q <;> rfl

/-- **The composition-as-XOR theorem.**  Pauli composition mod phase
    factors through F₂-addition under the R-Family embedding.

    `pauliToR (compose p q) = pauliToR p + pauliToR q`

    This is the canonical "stabilizer = symplectic" reduction. -/
theorem pauliToR_compose {n : ℕ} (p q : PauliN n) :
    pauliToR (PauliN.compose p q) = pauliToR p + pauliToR q := by
  funext k
  show (pauliToR (PauliN.compose p q)) k
      = Bool.xor (pauliToR p k) (pauliToR q k)
  unfold pauliToR PauliN.compose
  by_cases hk : k.val % 2 = 0
  · simp only [hk, if_true]
    exact PauliBase_xBit_compose _ _
  · simp only [hk, if_false]
    exact PauliBase_zBit_compose _ _

/-- The identity Pauli embeds as the zero vector. -/
@[simp] theorem pauliToR_one (n : ℕ) :
    pauliToR (PauliN.one n) = (0 : R (2 * n)) := by
  funext k
  show (pauliToR (PauliN.one n)) k = false
  unfold pauliToR PauliN.one
  by_cases hk : k.val % 2 = 0
  · simp [hk, PauliBase.xBit]
  · simp [hk, PauliBase.zBit]

/-! ## § 6 Single-qubit case — the V₄ bridge

The `n = 1` case is the cleanest witness: a single-qubit Pauli
operator mod phase is exactly an element of V₄ ≅ R 2.  The
correspondence is

    I ↔ V₄.dao     ↔ R.oo  = (false, false)
    X ↔ V₄.cuo     ↔ R.xo  = (true,  false)
    Z ↔ V₄.zong    ↔ R.ox  = (false, true )
    Y ↔ V₄.cuoZong ↔ R.xx  = (true,  true ) -/

namespace SingleQubit

/-- The single-qubit Pauli space `PauliN 1` collapses to `PauliBase`
    (one qubit ↦ one base operator).  We pick the canonical
    `i = 0` slot. -/
def toBase (p : PauliN 1) : PauliBase := p 0

/-- Inverse: package a single base operator as a 1-qubit Pauli. -/
def ofBase (p : PauliBase) : PauliN 1 := fun _ => p

@[simp] theorem toBase_ofBase (p : PauliBase) :
    toBase (ofBase p) = p := rfl

theorem ofBase_toBase (p : PauliN 1) : ofBase (toBase p) = p := by
  funext i
  fin_cases i
  rfl

/-- `PauliN 1 ≃ PauliBase`. -/
def equivBase : PauliN 1 ≃ PauliBase where
  toFun := toBase
  invFun := ofBase
  left_inv := ofBase_toBase
  right_inv := toBase_ofBase

/-! ### V₄ correspondence -/

/-- Map a Pauli base operator to its V₄ avatar. -/
def toV4 : PauliBase → V4
  | .I => .dao
  | .X => .cuo
  | .Z => .zong
  | .Y => .cuoZong

/-- Map a V₄ atom to its Pauli base avatar. -/
def ofV4 : V4 → PauliBase
  | .dao => .I
  | .cuo => .X
  | .zong => .Z
  | .cuoZong => .Y

@[simp] theorem toV4_I : toV4 .I = .dao := rfl
@[simp] theorem toV4_X : toV4 .X = .cuo := rfl
@[simp] theorem toV4_Z : toV4 .Z = .zong := rfl
@[simp] theorem toV4_Y : toV4 .Y = .cuoZong := rfl

@[simp] theorem ofV4_toV4 (p : PauliBase) : ofV4 (toV4 p) = p := by
  cases p <;> rfl

@[simp] theorem toV4_ofV4 (g : V4) : toV4 (ofV4 g) = g := by
  cases g <;> rfl

/-- `PauliBase ≃ V4`. -/
def baseEquivV4 : PauliBase ≃ V4 where
  toFun := toV4
  invFun := ofV4
  left_inv := ofV4_toV4
  right_inv := toV4_ofV4

/-- Composition agrees with V₄ composition under the bijection. -/
theorem toV4_compose (p q : PauliBase) :
    toV4 (PauliBase.compose p q) = V4.compose (toV4 p) (toV4 q) := by
  cases p <;> cases q <;> rfl

/-! ### R 2 correspondence (the canonical Atlas binding) -/

/-- Map a Pauli base operator to its `R 2` bit pattern.  This is
    `pauliToR` specialised to `n = 1` and read coordinate-wise. -/
def toR2 : PauliBase → R 2
  | .I => R.oo
  | .X => R.xo
  | .Z => R.ox
  | .Y => R.xx

@[simp] theorem toR2_I : toR2 .I = R.oo := rfl
@[simp] theorem toR2_X : toR2 .X = R.xo := rfl
@[simp] theorem toR2_Z : toR2 .Z = R.ox := rfl
@[simp] theorem toR2_Y : toR2 .Y = R.xx := rfl

/-- Map an `R 2` element to its Pauli base avatar. -/
def ofR2 (v : R 2) : PauliBase :=
  PauliBase.ofBits (v ⟨0, by decide⟩) (v ⟨1, by decide⟩)

theorem ofR2_toR2 (p : PauliBase) : ofR2 (toR2 p) = p := by
  cases p <;> rfl

theorem toR2_ofR2 (v : R 2) : toR2 (ofR2 v) = v := by
  unfold ofR2
  funext i
  have h0 : v ⟨0, by decide⟩ = v 0 := rfl
  have h1 : v ⟨1, by decide⟩ = v 1 := rfl
  fin_cases i <;>
    (rcases hv0 : v 0 with _ | _ <;>
     rcases hv1 : v 1 with _ | _ <;>
     simp [toR2, R.oo, R.xo, R.ox, R.xx, PauliBase.ofBits, hv0, hv1])

/-- `PauliBase ≃ R 2`. -/
def baseEquivR2 : PauliBase ≃ R 2 where
  toFun := toR2
  invFun := ofR2
  left_inv := ofR2_toR2
  right_inv := toR2_ofR2

/-- The single-qubit embedding `pauliToR` agrees with `toR2 ∘ toBase`
    coordinate-wise (after the trivial `2 * 1 = 2` re-cast). -/
theorem pauliToR_single (p : PauliN 1) :
    pauliToR p = (fun k : Fin (2 * 1) =>
      (toR2 (toBase p)) ⟨k.val, by have := k.isLt; omega⟩) := by
  funext k
  show (pauliToR p) k = (toR2 (toBase p)) ⟨k.val, by have := k.isLt; omega⟩
  -- k : Fin (2 * 1) = Fin 2.  Case-split with fin_cases.
  fin_cases k
  · -- k = ⟨0, _⟩
    show (pauliToR p) ⟨0, by decide⟩ = (toR2 (toBase p)) ⟨0, by decide⟩
    unfold pauliToR
    have hMod : (0 : Nat) % 2 = 0 := rfl
    have hDiv : (0 : Nat) / 2 = 0 := rfl
    simp only [hMod, hDiv, if_true]
    show (p ⟨0, by omega⟩).xBit = (toR2 (toBase p)) ⟨0, by decide⟩
    have hp : p ⟨0, by omega⟩ = toBase p := rfl
    rw [hp]
    cases toBase p <;> rfl
  · -- k = ⟨1, _⟩
    show (pauliToR p) ⟨1, by decide⟩ = (toR2 (toBase p)) ⟨1, by decide⟩
    unfold pauliToR
    have hMod : (1 : Nat) % 2 = 1 := rfl
    have hDiv : (1 : Nat) / 2 = 0 := rfl
    have hne : ¬ (1 : Nat) % 2 = 0 := by decide
    simp only [hMod, hDiv, hne, if_false]
    show (p ⟨0, by omega⟩).zBit = (toR2 (toBase p)) ⟨1, by decide⟩
    have hp : p ⟨0, by omega⟩ = toBase p := rfl
    rw [hp]
    cases toBase p <;> rfl

/-! ### The composite `PauliN 1 ≃ V4 ≃ R 2` bridge -/

/-- The single-qubit composite bijection: `PauliN 1 ≃ V4`. -/
def equivV4 : PauliN 1 ≃ V4 := equivBase.trans baseEquivV4

/-- The single-qubit composite bijection: `PauliN 1 ≃ R 2`. -/
def equivR2 : PauliN 1 ≃ R 2 := equivBase.trans baseEquivR2

end SingleQubit

/-! ## § 7 Case studies and sanity checks -/

/-- Sanity: the single-qubit X-Y product is `Z` (mod phase). -/
example : PauliBase.compose .X .Y = .Z := rfl

/-- Sanity: the single-qubit X-Z product is `Y` (mod phase). -/
example : PauliBase.compose .X .Z = .Y := rfl

/-- Sanity: the single-qubit Y-Z product is `X` (mod phase). -/
example : PauliBase.compose .Y .Z = .X := rfl

/-- Sanity: all four Pauli base operators are involutions. -/
example : ∀ p : PauliBase, PauliBase.compose p p = .I :=
  PauliBase.compose_self

/-- Sanity: the embedding sends the 1-qubit operator `X` to bit
    pattern `(true, false)` ≅ `R.xo`. -/
example : pauliToR (SingleQubit.ofBase .X)
        = (fun k : Fin (2 * 1) =>
            R.xo ⟨k.val, by have := k.isLt; omega⟩) :=
  SingleQubit.pauliToR_single (SingleQubit.ofBase .X)

/-- Case study (2-qubit): `X ⊗ I` composed with `I ⊗ Z` is `X ⊗ Z`. -/
def caseStudy2qubit_XI : PauliN 2 := fun i => if i.val = 0 then .X else .I
def caseStudy2qubit_IZ : PauliN 2 := fun i => if i.val = 0 then .I else .Z
def caseStudy2qubit_XZ : PauliN 2 := fun i => if i.val = 0 then .X else .Z

example :
    PauliN.compose caseStudy2qubit_XI caseStudy2qubit_IZ
      = caseStudy2qubit_XZ := by
  funext i
  fin_cases i <;> rfl

/-- The embedding `pauliToR` is bijective. -/
theorem pauliToR_bijective (n : ℕ) : Function.Bijective (pauliToR (n := n)) :=
  (equiv n).bijective

/-! ## § 8 Symplectic σ ↔ commutation (single-qubit witness)

The deep observation in stabilizer-code theory:

    σ(pauliToR p, pauliToR q) = 0  ⟺  p and q commute mod phase

We state and prove the single-qubit version as a witness; the n-qubit
generalisation follows by linearity of σ and `pauliToR_compose`,
but the full statement requires defining a "commute mod phase"
predicate on Pauli operators (with phase tracking), which we omit
here per the mod-phase scope of this case study. -/

/-- The single-qubit Pauli base operators that **commute mod phase**:
    `(I, anything)`, `(anything, I)`, and `(p, p)`.  Equivalently:
    p and q commute iff their `(xBit, zBit)` vectors are
    σ-orthogonal in `R 2`, i.e., `xBit_p · zBit_q = zBit_p · xBit_q`. -/
def baseCommute (p q : PauliBase) : Bool :=
  Bool.xor (Bool.and p.xBit q.zBit) (Bool.and p.zBit q.xBit)
    |> Bool.not

/-- The Pauli table: two operators commute mod phase iff they
    σ-pair to `false`. -/
theorem baseCommute_iff_sigma (p q : PauliBase) :
    baseCommute p q = Bool.not
      (R.sigma (k := 1) (SingleQubit.toR2 p) (SingleQubit.toR2 q)) := by
  cases p <;> cases q <;> rfl

/-- σ-pairing of two single-qubit Pauli operators detects
    anticommutation:  σ = 1 ⟺ p, q anticommute mod phase. -/
theorem sigma_anticommute_witness :
    R.sigma (k := 1) (SingleQubit.toR2 .X) (SingleQubit.toR2 .Z) = true := by
  decide

/-- σ-pairing detects commutation:  σ(I, _) = 0. -/
theorem sigma_commute_witness_I (p : PauliBase) :
    R.sigma (k := 1) (SingleQubit.toR2 .I) (SingleQubit.toR2 p) = false := by
  cases p <;> decide

/-- σ-pairing detects self-commutation:  σ(p, p) = 0. -/
theorem sigma_commute_witness_self (p : PauliBase) :
    R.sigma (k := 1) (SingleQubit.toR2 p) (SingleQubit.toR2 p) = false := by
  cases p <;> decide

end SSBX.Foundation.Wen.Embeddings.StabilizerQM
