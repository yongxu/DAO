/-
# Operators · V4.Core — constructor-style presentation of R 2

Per `wen-substrate.md` v1.4 §3.7.8 (distinction monism), the **one mathematical
core** of the framework is the R-family.  `V4` here is the **constructor-style
presentation of R 2** (the algebraic-class realisation `δ = Bool` of the
substrate-level binary distinction): four named constructors that bijectively
correspond to the four elements of `R 2 = Fin 2 → Bool`.

* `V4 ≃ R 2` is proven below (`V4.equivR2`).
* `V4.compose ≃ R 2 addition (XOR)` is the same Klein-four group operation.
* The pinyin names `dao` / `cuo` / `zong` / `cuoZong` are **Atlas-level
  overlays** preserved here for ergonomic pattern matching; the R-family
  canonical reading is the bit-pattern `oo` / `xo` / `ox` / `xx` from
  `Foundation/R/Basic.lean`.

This file does not know about Shi, Hexagram, Turing machines, or any atlas
reading.  Those modules project this carrier into their own domains.
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Hierarchy.Operators

open SSBX.Foundation.R

/-! ## Carrier -/

/-- `V4` is the constructor-style presentation of `R 2`.

    Per `wen-substrate.md` v1.4 §3.7.8: the mathematical core is R-family;
    `V4` is the ergonomic 4-constructor view of the canonical δ = Bool
    realisation `R 2 = Fin 2 → Bool`.  Use `V4.equivR2` (below) to bridge
    between presentations; the algebra is identical. -/
inductive V4 where
  | dao
  | cuo
  | zong
  | cuoZong
  deriving DecidableEq, Repr

namespace V4

def all : List V4 := [.dao, .cuo, .zong, .cuoZong]

theorem all_length : all.length = 4 := rfl

/-- First coordinate: content/value duality. -/
def contentBit : V4 → Bool
  | .dao | .zong => false
  | .cuo | .cuoZong => true

/-- Second coordinate: frame/order duality. -/
def frameBit : V4 → Bool
  | .dao | .cuo => false
  | .zong | .cuoZong => true

def ofBits : Bool → Bool → V4
  | false, false => .dao
  | true, false => .cuo
  | false, true => .zong
  | true, true => .cuoZong

def compose (a b : V4) : V4 :=
  ofBits (Bool.xor (contentBit a) (contentBit b))
    (Bool.xor (frameBit a) (frameBit b))

def inv (g : V4) : V4 := g

theorem ofBits_content_frame (g : V4) :
    ofBits (contentBit g) (frameBit g) = g := by
  cases g <;> rfl

theorem contentBit_ofBits (content frame : Bool) :
    contentBit (ofBits content frame) = content := by
  cases content <;> cases frame <;> rfl

theorem frameBit_ofBits (content frame : Bool) :
    frameBit (ofBits content frame) = frame := by
  cases content <;> cases frame <;> rfl

theorem compose_dao_left (g : V4) :
    compose .dao g = g := by
  cases g <;> rfl

theorem compose_dao_right (g : V4) :
    compose g .dao = g := by
  cases g <;> rfl

theorem compose_self (g : V4) :
    compose g g = .dao := by
  cases g <;> rfl

theorem compose_comm (a b : V4) :
    compose a b = compose b a := by
  cases a <;> cases b <;> rfl

theorem compose_assoc (a b c : V4) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem cuo_zong_eq_cuoZong :
    compose .cuo .zong = .cuoZong := rfl

theorem zong_cuo_eq_cuoZong :
    compose .zong .cuo = .cuoZong := rfl

theorem cuoZong_self :
    compose .cuoZong .cuoZong = .dao := rfl

theorem v4_core_summary :
    all.length = 4
    ∧ (∀ g : V4, compose .dao g = g)
    ∧ (∀ g : V4, compose g .dao = g)
    ∧ (∀ g : V4, compose g g = .dao)
    ∧ (∀ a b : V4, compose a b = compose b a)
    ∧ (∀ a b c : V4, compose (compose a b) c = compose a (compose b c))
    ∧ compose .cuo .zong = .cuoZong := by
  exact
    ⟨ all_length
    , compose_dao_left
    , compose_dao_right
    , compose_self
    , compose_comm
    , compose_assoc
    , rfl
    ⟩

/-! ## § Bridge to R 2 — V4 is the constructor-style presentation of R 2

Per wen-substrate.md v1.4 §3.7.8, the **one mathematical core** is the R-family.
The four V4 constructors bijectively correspond to the four bit patterns of
`R 2 = Fin 2 → Bool` from `Foundation/R/Basic.lean`:

    dao     ↔ R.oo  = (false, false)
    cuo     ↔ R.xo  = (true,  false)
    zong    ↔ R.ox  = (false, true)
    cuoZong ↔ R.xx  = (true,  true)

Under this bridge, `V4.compose` is exactly XOR (= R 2's `+` from
`Foundation/R/Basic.lean`), and `V4.inv = id` matches characteristic-2
self-inverse.  This is not a coincidence — V4 *is* R 2, presented with
named constructors instead of `Fin 2 → Bool` function literals. -/

/-- Project V4 to its R-family canonical bit-pattern in R 2. -/
def toR2 : V4 → R 2
  | .dao => fun _ => false
  | .cuo => fun i => decide (i.val = 0)
  | .zong => fun i => decide (i.val = 1)
  | .cuoZong => fun _ => true

/-- Lift R 2 to the V4 constructor presentation. -/
def ofR2 (v : R 2) : V4 := ofBits (v ⟨0, by decide⟩) (v ⟨1, by decide⟩)

@[simp] theorem toR2_dao : toR2 .dao = (fun _ => false) := rfl
@[simp] theorem toR2_cuoZong : toR2 .cuoZong = (fun _ => true) := rfl

theorem ofR2_toR2 (g : V4) : ofR2 (toR2 g) = g := by
  cases g <;> rfl

theorem toR2_ofR2 (v : R 2) : toR2 (ofR2 v) = v := by
  unfold ofR2 toR2
  funext i
  fin_cases i <;> cases h : v ⟨0, by decide⟩ <;> cases h' : v ⟨1, by decide⟩ <;>
    simp_all [ofBits]

/-- `V4 ≃ R 2` — the canonical bijection. R-family is the **one core**;
    V4 is its constructor-style presentation.  Per wen-substrate.md v1.4
    §3.7.8 distinction monism. -/
def equivR2 : V4 ≃ R 2 where
  toFun := toR2
  invFun := ofR2
  left_inv := ofR2_toR2
  right_inv := toR2_ofR2

/-- The V4 Klein-four composition **is** R 2 addition (XOR) under the bridge. -/
theorem compose_eq_R2_add (a b : V4) :
    toR2 (compose a b) = toR2 a + toR2 b := by
  cases a <;> cases b <;> funext i <;> fin_cases i <;> rfl

/-- The V4 inverse is identity, matching R 2's characteristic-2 self-inverse. -/
theorem inv_eq_R2_neg (g : V4) : toR2 (inv g) = -(toR2 g) := by
  cases g <;> funext i <;> fin_cases i <;> rfl

/-! ## § R-family canonical operation aliases

Per `wen-substrate.md` v1.4 §3.7.8 + chapter 01's P1 / P6 framing, the
R-family canonical reading of the three non-trivial V4 elements is by their
bit patterns (= the **algebraic-minimum δ = Bool realisation** of R 2):

* `cuo` is "flip-axis-0" (toggle bit 0)
* `zong` is "flip-axis-1" (toggle bit 1)
* `cuoZong` is "flip-both" (P ∘ T composite)

The pinyin names are kept as the Atlas-overlay terminology; the canonical
R-family names below name the same elements by their algebraic role. -/

/-- R-family canonical: the identity element of R 2 (= bit pattern `oo`).
    Pinyin alias: `dao`. -/
abbrev origin : V4 := .dao

/-- R-family canonical: flip-axis-0 (= bit pattern `xo`, P involution).
    Pinyin alias: `cuo`. -/
abbrev flipAxis0 : V4 := .cuo

/-- R-family canonical: flip-axis-1 (= bit pattern `ox`, T involution).
    Pinyin alias: `zong`. -/
abbrev flipAxis1 : V4 := .zong

/-- R-family canonical: flip-both (= bit pattern `xx`, PT composite).
    Pinyin alias: `cuoZong`. -/
abbrev flipBoth : V4 := .cuoZong

/-! ## § V4.elim — explicit 4-branch eliminator

`V4.elim` is the universal destructor for V4: it takes a V4 value and four
branches (one per atom) and returns the appropriate branch.  This recovers
the constructor-style pattern matching for clients that want to treat V4
as a 4-element type without committing to the inductive presentation.

Mathematically: `V4.elim v d c z cz = if v = .dao then d else if v = .cuo
then c else if v = .zong then z else cz` (under `V4 ≃ R 2`).

Use this whenever you would otherwise write
  cases v with | .dao => d | .cuo => c | .zong => z | .cuoZong => cz
Especially in contexts where V4 might later become `abbrev V4 := R 2`. -/

@[reducible] def elim {α : Sort*} (v : V4) (d c z cz : α) : α :=
  match v with
  | .dao => d
  | .cuo => c
  | .zong => z
  | .cuoZong => cz

@[simp] theorem elim_dao {α} (d c z cz : α) : elim .dao d c z cz = d := rfl
@[simp] theorem elim_cuo {α} (d c z cz : α) : elim .cuo d c z cz = c := rfl
@[simp] theorem elim_zong {α} (d c z cz : α) : elim .zong d c z cz = z := rfl
@[simp] theorem elim_cuoZong {α} (d c z cz : α) : elim .cuoZong d c z cz = cz := rfl

end V4

end SSBX.Foundation.Hierarchy.Operators
