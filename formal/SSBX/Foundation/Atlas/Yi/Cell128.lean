/-
# Foundation.Atlas.Yi.Cell128 — R₇ = Hexagram × YinBit, the 128-cell layer

Per `wen-algebra` v0.6 §9 (Atlas separation) and the R-Family doctrine:

    Cell128 := Hexagram × YinBit   ≃   R 7   =   F_2^7   =   128 cells

This is the R-Family port of the classical `SSBX.Foundation.Bagua.R7` module
(formerly under `Atlas/Yi/Classical/Cells/R7.lean`).  Differences:

* `Hexagram` is the R-Family type `R 6 = Fin 6 → Bool` (not the legacy
  struct).  All hexagram operators come from `Atlas.Yi.Operators` and
  `Atlas.Yi.Hexagrams`.
* The 7th bit (因 / YinBit) is the only Cell128-native atom.
* `imprint` is the toggle on that 7th bit.  We also expose the
  XOR-with-mask form `imprintM` (used at R₈ to compose with 投).

The (Z/2)⁷ Abelian group structure is exposed via componentwise XOR
combining `R.instAdd` on `Hexagram` (= `R 6`) and `Bool.xor` on the
YinBit.  `origin = (0, false)` (= qianqian × no-trace).

## Doctrinal anchor

* `wen-algebra.md` v0.6 §1.7 (R 7 readings) — R₇ as a halfway layer
  between Hexagram (R 6) and Cell256 (R 8).
* `v4-foundation.md` v0.5 §15.7 (Cell128 binding).
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Hexagrams
import SSBX.Foundation.Atlas.Yi.Operators

namespace SSBX.Foundation.Atlas.Yi

open SSBX.Foundation.R

/-! ## § 1 The cell type -/

/-- 因 (yīn) bit — the 7th, R₇-native, atom: a binary past-trace bit.

    * `false` (0) = 无因 (no past trace)
    * `true`  (1) = 有因 (with past trace) -/
abbrev YinBit : Type := Bool

/-- `Cell128 := Hexagram × YinBit` ≃ `R 7`.  128 cells. -/
abbrev Cell128 : Type := Hexagram × YinBit

namespace Cell128

/-! ## § 2 (Z/2)⁷ group structure via componentwise XOR -/

/-- Componentwise XOR on `Cell128`: hexagram + bit XOR. -/
def xor (c₁ c₂ : Cell128) : Cell128 :=
  (c₁.1 + c₂.1, Bool.xor c₁.2 c₂.2)

/-- 道 cell at R₇ = (qianqian, false) = (Z/2)⁷ identity. -/
def origin : Cell128 := (Hexagram.qianqian, false)

/-- `qianqian = 0` as elements of `Hexagram = R 6`. -/
theorem qianqian_eq_zero : (Hexagram.qianqian : Hexagram) = 0 := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

@[simp] theorem origin_xor (c : Cell128) : xor origin c = c := by
  rcases c with ⟨h, b⟩
  show ((Hexagram.qianqian : Hexagram) + h, Bool.xor false b) = (h, b)
  rw [qianqian_eq_zero, zero_add]
  cases b <;> rfl

@[simp] theorem xor_origin (c : Cell128) : xor c origin = c := by
  rcases c with ⟨h, b⟩
  show (h + (Hexagram.qianqian : Hexagram), Bool.xor b false) = (h, b)
  rw [qianqian_eq_zero, add_zero]
  cases b <;> rfl

theorem xor_self (c : Cell128) : xor c c = origin := by
  rcases c with ⟨h, b⟩
  show (h + h, Bool.xor b b) = (Hexagram.qianqian, false)
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · rw [R.add_self, ← qianqian_eq_zero]
  · cases b <;> rfl

theorem xor_comm (c₁ c₂ : Cell128) : xor c₁ c₂ = xor c₂ c₁ := by
  rcases c₁ with ⟨h₁, b₁⟩
  rcases c₂ with ⟨h₂, b₂⟩
  show (h₁ + h₂, Bool.xor b₁ b₂) = (h₂ + h₁, Bool.xor b₂ b₁)
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · exact add_comm h₁ h₂
  · cases b₁ <;> cases b₂ <;> rfl

theorem xor_assoc (c₁ c₂ c₃ : Cell128) :
    xor (xor c₁ c₂) c₃ = xor c₁ (xor c₂ c₃) := by
  rcases c₁ with ⟨h₁, b₁⟩
  rcases c₂ with ⟨h₂, b₂⟩
  rcases c₃ with ⟨h₃, b₃⟩
  show (h₁ + h₂ + h₃, Bool.xor (Bool.xor b₁ b₂) b₃)
        = (h₁ + (h₂ + h₃), Bool.xor b₁ (Bool.xor b₂ b₃))
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · exact add_assoc h₁ h₂ h₃
  · cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-! ## § 3 Add / Zero / Neg / Sub instance binding

Bind the standard arithmetic notation to the XOR form so callers can
use `+ / 0 / -` on `Cell128`. -/

instance : Add Cell128 := ⟨xor⟩
instance : Zero Cell128 := ⟨origin⟩
/-- Self-inverse in characteristic 2. -/
instance : Neg Cell128 := ⟨id⟩
instance : Sub Cell128 := ⟨xor⟩

@[simp] theorem add_def (c₁ c₂ : Cell128) : c₁ + c₂ = xor c₁ c₂ := rfl
@[simp] theorem zero_def : (0 : Cell128) = origin := rfl
@[simp] theorem neg_def (c : Cell128) : -c = c := rfl
@[simp] theorem sub_def (c₁ c₂ : Cell128) : c₁ - c₂ = xor c₁ c₂ := rfl

/-! ## § 4 印 (imprint) — toggle the YinBit -/

/-- 印 (yìn) — toggle YinBit only (legacy direct form). -/
def imprint (c : Cell128) : Cell128 := (c.1, !c.2)

/-- 印 is involutive. -/
theorem imprint_involutive (c : Cell128) : imprint (imprint c) = c := by
  rcases c with ⟨h, b⟩
  cases b <;> rfl

/-- 印 preserves the hexagram component. -/
theorem imprint_preserves_hex (c : Cell128) : (imprint c).1 = c.1 := rfl

/-- 印 mask at R₇: only the YinBit is set.  `(qianqian, true)`. -/
def imprint_mask : Cell128 := (Hexagram.qianqian, true)

/-- 印 (mask form): XOR with `imprint_mask`. -/
def imprintM (c : Cell128) : Cell128 := xor c imprint_mask

/-- Mask form coincides with the legacy direct toggle. -/
theorem imprintM_eq_imprint (c : Cell128) : imprintM c = imprint c := by
  rcases c with ⟨h, b⟩
  show (h + (Hexagram.qianqian : Hexagram), Bool.xor b true) = (h, !b)
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · rw [qianqian_eq_zero, add_zero]
  · cases b <;> rfl

/-- Mask form is involutive. -/
theorem imprintM_imprintM (c : Cell128) : imprintM (imprintM c) = c := by
  unfold imprintM
  rw [xor_assoc, xor_self, xor_origin]

/-! ## § 5 Projection: forget the YinBit -/

/-- Project a `Cell128` back down to its `Hexagram` (forget the 7th bit). -/
def project128to6 (c : Cell128) : Hexagram := c.1

@[simp] theorem project128to6_apply (h : Hexagram) (b : YinBit) :
    project128to6 (h, b) = h := rfl

@[simp] theorem project128to6_imprint (c : Cell128) :
    project128to6 (imprint c) = project128to6 c := rfl

@[simp] theorem project128to6_origin :
    project128to6 origin = Hexagram.qianqian := rfl

/-! ## § 6 Hexagram operators lifted to Cell128 (preserve the YinBit) -/

/-- 錯 (cuo) lifted to `Cell128` — flip all 6 yao, preserve YinBit. -/
def hexCuo (c : Cell128) : Cell128 := (Hexagram.cuo c.1, c.2)

/-- 綜 (zong) lifted to `Cell128` — reverse the 6 yao, preserve YinBit. -/
def hexZong (c : Cell128) : Cell128 := (Hexagram.zong c.1, c.2)

/-- 互 (hu) lifted to `Cell128` — extract 2-3-4 / 3-4-5, preserve YinBit. -/
def hexHu (c : Cell128) : Cell128 := (Hexagram.hu c.1, c.2)

/-- 錯綜 lifted (= V₄ central element on the hexagram, preserve YinBit). -/
def hexCuoZong (c : Cell128) : Cell128 := (Hexagram.cuoZong c.1, c.2)

theorem hexCuo_involutive (c : Cell128) : hexCuo (hexCuo c) = c := by
  rcases c with ⟨h, b⟩
  unfold hexCuo
  rw [Hexagram.cuo_involutive]

theorem hexZong_involutive (c : Cell128) : hexZong (hexZong c) = c := by
  rcases c with ⟨h, b⟩
  unfold hexZong
  rw [Hexagram.zong_involutive]

theorem hexCuoZong_involutive (c : Cell128) : hexCuoZong (hexCuoZong c) = c := by
  rcases c with ⟨h, b⟩
  unfold hexCuoZong
  rw [Hexagram.cuoZong_involutive]

/-- hexCuo and 印 commute. -/
theorem hexCuo_imprint_comm (c : Cell128) :
    hexCuo (imprint c) = imprint (hexCuo c) := by
  rcases c with ⟨h, b⟩; rfl

/-- hexZong and 印 commute. -/
theorem hexZong_imprint_comm (c : Cell128) :
    hexZong (imprint c) = imprint (hexZong c) := by
  rcases c with ⟨h, b⟩; rfl

/-- hexHu and 印 commute. -/
theorem hexHu_imprint_comm (c : Cell128) :
    hexHu (imprint c) = imprint (hexHu c) := by
  rcases c with ⟨h, b⟩; rfl

/-! ## § 7 Six single-yao flips lifted -/

/-- Flip the i-th yao (0-indexed) of a hexagram, preserve YinBit. -/
private def hexFlip (i : Fin 6) (h : Hexagram) : Hexagram :=
  fun j => if j = i then !(h j) else h j

/-- flip yao 1 (bottom). -/
def flip1 (c : Cell128) : Cell128 := (hexFlip ⟨0, by decide⟩ c.1, c.2)
/-- flip yao 2. -/
def flip2 (c : Cell128) : Cell128 := (hexFlip ⟨1, by decide⟩ c.1, c.2)
/-- flip yao 3 (top of inner trigram). -/
def flip3 (c : Cell128) : Cell128 := (hexFlip ⟨2, by decide⟩ c.1, c.2)
/-- flip yao 4 (bottom of outer trigram). -/
def flip4 (c : Cell128) : Cell128 := (hexFlip ⟨3, by decide⟩ c.1, c.2)
/-- flip yao 5. -/
def flip5 (c : Cell128) : Cell128 := (hexFlip ⟨4, by decide⟩ c.1, c.2)
/-- flip yao 6 (top). -/
def flip6 (c : Cell128) : Cell128 := (hexFlip ⟨5, by decide⟩ c.1, c.2)

/-- Single-yao flips are involutions. -/
private theorem hexFlip_involutive (i : Fin 6) (h : Hexagram) :
    hexFlip i (hexFlip i h) = h := by
  funext j
  unfold hexFlip
  by_cases hj : j = i
  · simp [hj, Bool.not_not]
  · simp [hj]

theorem flip1_involutive (c : Cell128) : flip1 (flip1 c) = c := by
  rcases c with ⟨h, b⟩; unfold flip1; rw [hexFlip_involutive]
theorem flip2_involutive (c : Cell128) : flip2 (flip2 c) = c := by
  rcases c with ⟨h, b⟩; unfold flip2; rw [hexFlip_involutive]
theorem flip3_involutive (c : Cell128) : flip3 (flip3 c) = c := by
  rcases c with ⟨h, b⟩; unfold flip3; rw [hexFlip_involutive]
theorem flip4_involutive (c : Cell128) : flip4 (flip4 c) = c := by
  rcases c with ⟨h, b⟩; unfold flip4; rw [hexFlip_involutive]
theorem flip5_involutive (c : Cell128) : flip5 (flip5 c) = c := by
  rcases c with ⟨h, b⟩; unfold flip5; rw [hexFlip_involutive]
theorem flip6_involutive (c : Cell128) : flip6 (flip6 c) = c := by
  rcases c with ⟨h, b⟩; unfold flip6; rw [hexFlip_involutive]

/-- Each single-yao flip commutes with 印 (they act on disjoint axes). -/
theorem flip1_imprint_comm (c : Cell128) :
    flip1 (imprint c) = imprint (flip1 c) := by
  rcases c with ⟨h, b⟩; rfl

/-! ## § 8 Cayley regular representation (R₇ self-action) -/

instance : SMul Cell128 Cell128 := ⟨xor⟩

@[simp] theorem smul_def (c s : Cell128) : c • s = xor c s := rfl

/-- Cayley left-translation by `c` on `Cell128`. -/
def cayley (c : Cell128) : Cell128 → Cell128 := fun s => xor c s

/-- Evaluate any endo at the origin to recover its translation amount. -/
def epsAtOrigin (f : Cell128 → Cell128) : Cell128 := f origin

/-- ε ∘ Cayley = id (retraction). -/
@[simp] theorem epsAtOrigin_cayley (c : Cell128) :
    epsAtOrigin (cayley c) = c := by
  unfold epsAtOrigin cayley
  exact xor_origin c

/-- Cayley is injective: distinct shifts give distinct functions. -/
theorem cayley_inj : Function.Injective cayley := by
  intro c₁ c₂ h
  have := congrFun h origin
  unfold cayley at this
  rwa [xor_origin, xor_origin] at this

/-- Cayley is a group homomorphism w.r.t. XOR / composition. -/
theorem cayley_hom (c₁ c₂ : Cell128) :
    cayley (xor c₁ c₂) = cayley c₁ ∘ cayley c₂ := by
  funext s
  unfold cayley
  rw [Function.comp_apply, xor_assoc]

/-! ## § 9 Public Phase-A summary -/

/-- R₇ Phase-A summary: (Z/2)⁷ group laws + Cayley fusion + 印 mask form. -/
theorem cell128_phaseA_summary :
    (∀ c : Cell128, xor origin c = c)
    ∧ (∀ c : Cell128, xor c c = origin)
    ∧ (∀ a b : Cell128, xor a b = xor b a)
    ∧ (∀ a b c : Cell128, xor (xor a b) c = xor a (xor b c))
    ∧ Function.Injective cayley
    ∧ (∀ c : Cell128, epsAtOrigin (cayley c) = c)
    ∧ (∀ c : Cell128, imprintM c = imprint c)
    ∧ (∀ c : Cell128, imprint (imprint c) = c) :=
  ⟨origin_xor, xor_self, xor_comm, xor_assoc,
   cayley_inj, epsAtOrigin_cayley, imprintM_eq_imprint, imprint_involutive⟩

end Cell128

end SSBX.Foundation.Atlas.Yi
