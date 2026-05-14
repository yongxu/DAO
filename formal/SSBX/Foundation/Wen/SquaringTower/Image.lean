/-
# Wen.SquaringTower.Image — `Image` (= V₄ = 𝕏) atomic carrier

The atomic V₄ Klein four-group as a four-constructor inductive whose
**constructor names are the bit pattern**.  `Image` plays the role of
$\mathbb{X}$ in `wen-algebra` v0.2 §0.2 / §1.1: the algebraic centre of
the entire 𝕏ⁿ tower.

| ctor | F₂² coord | 文 (Chinese) | Math | English          | Pinyin   | Pauli (mod φ) |
|------|-----------|---------------|------|------------------|----------|---------------|
| `oo` | (0, 0)    | 道            | `e`  | `Identity`       | dao      | `I`           |
| `xo` | (1, 0)    | 错            | `a`  | `ContentFlip`    | cuo      | `X` (bit)     |
| `ox` | (0, 1)    | 综            | `b`  | `FrameFlip`      | zong     | `Z` (phase)   |
| `xx` | (1, 1)    | 错综          | `ab` | `CompoundFlip`   | cuozong  | `Y` (= iXZ)   |

The bit pattern is **primary identity**.  Every other reading
(Chinese, English, Math, Pauli, Time-Image) is a layered alias added in
`Mapping/*.lean`.

## Algebraic content

* `Mul / One / Inv / CommGroup` instance — `Image` is a `CommGroup`
  isomorphic to V₄ = (Z/2)².  Multiplication is XOR on coordinates.
* `alpha`, `beta` — the two F₂-coordinates.
* `ofBits` — the inverse: `(α, β) ↦ Image.ofBits α β`.
* `dot : Image → Image → Bit` — the canonical F₂-bilinear pairing
  (`wen-algebra` v0.2 §5.1):

      ⟨u, v⟩ = (u_α ∧ v_α) ⊕ (u_β ∧ v_β)

  This is the **atomic** dot product; the `n`-fold version on `X n`
  (orthogonal direct sum) lives in `Dot.lean`.

`Image` is `DecidableEq`, `Fintype`, `Repr`, so `decide` proves any
Image-only equation, and `Fintype.card Image = 4` is a `decide`.
-/

import SSBX.Foundation.Wen.SquaringTower.Bit
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Basic

namespace SSBX.Foundation.Wen.SquaringTower

/-! ## § 1 The `Image` inductive

Bit-pattern primary: the four constructors are named by their `(α, β)`
coordinates, with `'o' = 0` and `'x' = 1` matching the substrate
convention from `Bit.lean`. -/

/-- `Image` = V₄ = (Z/2)² = the atomic carrier of the 𝕏ⁿ tower. -/
inductive Image where
  /-- `(α, β) = (0, 0)` — the V₄ identity (道 / Identity / e / Pauli I). -/
  | oo
  /-- `(α, β) = (1, 0)` — the α-axis generator (错 / ContentFlip / a / Pauli X). -/
  | xo
  /-- `(α, β) = (0, 1)` — the β-axis generator (综 / FrameFlip / b / Pauli Z). -/
  | ox
  /-- `(α, β) = (1, 1)` — the diagonal element (错综 / CompoundFlip / ab / Pauli Y). -/
  | xx
  deriving DecidableEq, Repr

instance instFintype : Fintype Image where
  elems := ([Image.oo, Image.xo, Image.ox, Image.xx] : List Image).toFinset
  complete := by intro i; cases i <;> decide

namespace Image

/-! ## § 2 Enumeration -/

/-- All four `Image` atoms in canonical bit-pattern order. -/
def all : List Image := [.oo, .xo, .ox, .xx]

@[simp] theorem all_length : all.length = 4 := rfl

theorem all_nodup : all.Nodup := by decide

theorem mem_all (i : Image) : i ∈ all := by cases i <;> decide

/-! ## § 3 F₂-coordinate accessors

`alpha` and `beta` are the two F₂-coordinates, read off the constructor's
bit pattern: `oo / xo / ox / xx ↦ (α, β) ∈ {(0,0), (1,0), (0,1), (1,1)}`.
-/

/-- α-coordinate (first bit, content-axis). -/
def alpha : Image → Bit
  | .oo => Bit.o
  | .xo => Bit.x
  | .ox => Bit.o
  | .xx => Bit.x

/-- β-coordinate (second bit, frame-axis). -/
def beta : Image → Bit
  | .oo => Bit.o
  | .xo => Bit.o
  | .ox => Bit.x
  | .xx => Bit.x

@[simp] theorem alpha_oo : alpha .oo = Bit.o := rfl
@[simp] theorem alpha_xo : alpha .xo = Bit.x := rfl
@[simp] theorem alpha_ox : alpha .ox = Bit.o := rfl
@[simp] theorem alpha_xx : alpha .xx = Bit.x := rfl

@[simp] theorem beta_oo : beta .oo = Bit.o := rfl
@[simp] theorem beta_xo : beta .xo = Bit.o := rfl
@[simp] theorem beta_ox : beta .ox = Bit.x := rfl
@[simp] theorem beta_xx : beta .xx = Bit.x := rfl

/-- Reconstruct an `Image` from its two F₂-coordinates. -/
def ofBits : Bit → Bit → Image
  | false, false => .oo
  | true,  false => .xo
  | false, true  => .ox
  | true,  true  => .xx

@[simp] theorem ofBits_oo : ofBits Bit.o Bit.o = .oo := rfl
@[simp] theorem ofBits_xo : ofBits Bit.x Bit.o = .xo := rfl
@[simp] theorem ofBits_ox : ofBits Bit.o Bit.x = .ox := rfl
@[simp] theorem ofBits_xx : ofBits Bit.x Bit.x = .xx := rfl

@[simp] theorem alpha_ofBits (a b : Bit) : (ofBits a b).alpha = a := by
  cases a <;> cases b <;> rfl

@[simp] theorem beta_ofBits (a b : Bit) : (ofBits a b).beta = b := by
  cases a <;> cases b <;> rfl

@[simp] theorem ofBits_alpha_beta (i : Image) : ofBits i.alpha i.beta = i := by
  cases i <;> rfl

/-! ## § 4 V₄ group structure

`Image ≅ (Z/2)²` with the group operation `mul = XOR on coordinates`.
This makes `oo` the identity and every element self-inverse. -/

/-- Group multiplication: componentwise XOR on the two F₂-coordinates.
    Per `wen-algebra` v0.2 §1.1, this realises the V₄ Klein four-group
    multiplication table. -/
def mul (a b : Image) : Image :=
  ofBits (Bool.xor a.alpha b.alpha) (Bool.xor a.beta b.beta)

instance : Mul Image := ⟨mul⟩
instance : One Image := ⟨.oo⟩
/-- Every `Image` element is its own inverse (V₄ has exponent 2). -/
instance : Inv Image := ⟨id⟩

@[simp] theorem mul_def (a b : Image) : a * b = mul a b := rfl
@[simp] theorem one_def : (1 : Image) = .oo := rfl
@[simp] theorem inv_def (a : Image) : a⁻¹ = a := rfl

instance : CommGroup Image where
  mul_assoc       := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul         := by intro a; cases a <;> rfl
  mul_one         := by intro a; cases a <;> rfl
  inv_mul_cancel  := by intro a; cases a <;> rfl
  mul_comm        := by intro a b; cases a <;> cases b <;> rfl

/-- Self-inverse: every `Image` squared is the identity (V₄ has exponent 2). -/
@[simp] theorem mul_self (a : Image) : a * a = 1 := by
  cases a <;> rfl

/-- The V₄ multiplication table — verifiable by `decide`. -/
theorem mul_table_summary :
    (.oo * .oo : Image) = .oo ∧ (.oo * .xo : Image) = .xo ∧
    (.oo * .ox : Image) = .ox ∧ (.oo * .xx : Image) = .xx ∧
    (.xo * .xo : Image) = .oo ∧ (.xo * .ox : Image) = .xx ∧
    (.xo * .xx : Image) = .ox ∧ (.ox * .ox : Image) = .oo ∧
    (.ox * .xx : Image) = .xo ∧ (.xx * .xx : Image) = .oo := by
  decide

/-! ## § 5 F₂-bilinear dot product (`wen-algebra` v0.2 §5.1)

The atomic pairing on `Image`:

    ⟨u, v⟩ := (u_α ∧ v_α) ⊕ (u_β ∧ v_β) ∈ F₂

This is the canonical F₂-bilinear, symmetric, non-degenerate form on V₄.
Its `n`-fold orthogonal direct sum lives on `X n` and is defined in
`Dot.lean`. -/

/-- The F₂-bilinear dot product on `Image` (= V₄ pairing). -/
def dot (u v : Image) : Bit :=
  Bool.xor (Bool.and u.alpha v.alpha) (Bool.and u.beta v.beta)

@[simp] theorem dot_oo_left (u : Image) : dot .oo u = false := by
  cases u <;> rfl

@[simp] theorem dot_oo_right (u : Image) : dot u .oo = false := by
  cases u <;> rfl

@[simp] theorem dot_xo_right (u : Image) : dot u .xo = u.alpha := by
  cases u <;> rfl

@[simp] theorem dot_ox_right (u : Image) : dot u .ox = u.beta := by
  cases u <;> rfl

theorem dot_symm (u v : Image) : dot u v = dot v u := by
  cases u <;> cases v <;> rfl

/-- The full V₄ pairing table per `wen-algebra` v0.2 §5.1, verifiable by
    `decide`. -/
theorem dot_table_summary :
    dot .xo .xo = true ∧ dot .xo .ox = false ∧ dot .xo .xx = true ∧
    dot .ox .ox = true ∧ dot .ox .xx = true ∧ dot .xx .xx = false := by
  decide

/-! ## § 6 Coordinate basis (atomic case)

The two basis Images that pick out the α- and β-axes. They are the
atoms of the canonical basis of `X n` (`Dot.lean §3`). -/

/-- The α-basis atom: `xo`, with `(α, β) = (1, 0)`. -/
abbrev basisAlpha : Image := .xo
/-- The β-basis atom: `ox`, with `(α, β) = (0, 1)`. -/
abbrev basisBeta : Image := .ox

@[simp] theorem dot_basisAlpha (u : Image) : dot u basisAlpha = u.alpha := by
  cases u <;> rfl

@[simp] theorem dot_basisBeta (u : Image) : dot u basisBeta = u.beta := by
  cases u <;> rfl

/-- Atomic recovery: any `Image` is reconstructed from its two basis
    pairings.  This is `wen-algebra` v0.2 §5.4 Sense 1 + Sense 2 at the
    atomic level. -/
theorem coord_recovery (u : Image) :
    u = ofBits (dot u basisAlpha) (dot u basisBeta) := by
  cases u <;> rfl

end Image

end SSBX.Foundation.Wen.SquaringTower
