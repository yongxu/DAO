/-
# Foundation.Atlas.Yi.Cell256 — R₈ = Hexagram × Shi V₄, the 256-cell layer

Per `wen-algebra` v0.6 §9 (Atlas separation) and the R-Family doctrine:

    Cell256 := Hexagram × Shi   ≃   R 6 × R 2   ≃   R 8   =   F_2^8   =   256 cells

This is the R-Family port of the classical `SSBX.Foundation.Bagua.R8` module
(formerly under `Atlas/Yi/Classical/Cells/R8.lean`).  Differences:

* `Hexagram` is the R-Family type `R 6 = Fin 6 → Bool`.
* `Shi` is the R-Family type `R 2 = Fin 2 → Bool` carrying the V₄
  structure exposed in `Atlas.Yi.ShiV4`.
* The (Z/2)⁸ Abelian group structure comes from `R.instAdd` on both
  components.  `origin = (qianqian, dao)`.
* 印 / 投 are XOR-with-mask forms picking out the two Shi bits.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §1.8 (R 8 readings) — R₈ = Cell256 as the ceiling
  of the squaring tower.
* `v4-foundation.md` v0.5 §15.8 (Cell256 binding).
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Hexagrams
import SSBX.Foundation.Atlas.Yi.Operators
import SSBX.Foundation.Atlas.Yi.ShiV4
import SSBX.Foundation.Atlas.Yi.Cell128

namespace SSBX.Foundation.Atlas.Yi

open SSBX.Foundation.R

/-- `Cell256 := Hexagram × Shi` ≃ `R 8`.  256 cells.

    Per `wen-algebra` v0.6 §1.8 and `v4-foundation` v0.5 §15.8, the
    256-cell layer is the natural product of the 64 hexagrams with the
    4-element Shi V₄ Klein four-group. -/
abbrev Cell256 : Type := Hexagram × Shi

namespace Cell256

/-! ## § 1 (Z/2)⁸ group structure via componentwise XOR -/

/-- Componentwise XOR on `Cell256` (Hexagram XOR, Shi XOR). -/
def xor (c₁ c₂ : Cell256) : Cell256 := (c₁.1 + c₂.1, c₁.2 + c₂.2)

/-- 道 cell at R₈ = (qianqian, dao) = (Z/2)⁸ identity. -/
def origin : Cell256 := (Hexagram.qianqian, Shi.dao)

/-- `qianqian = 0` as element of `Hexagram = R 6` (re-export from Cell128). -/
theorem qianqian_eq_zero : (Hexagram.qianqian : Hexagram) = 0 :=
  Cell128.qianqian_eq_zero

/-- `Shi.dao = 0` as element of `Shi = R 2`. -/
theorem dao_eq_zero : (Shi.dao : Shi) = 0 := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem origin_xor (c : Cell256) : xor origin c = c := by
  rcases c with ⟨h, s⟩
  show ((Hexagram.qianqian : Hexagram) + h, (Shi.dao : Shi) + s) = (h, s)
  rw [qianqian_eq_zero, dao_eq_zero, zero_add, zero_add]

@[simp] theorem xor_origin (c : Cell256) : xor c origin = c := by
  rcases c with ⟨h, s⟩
  show (h + (Hexagram.qianqian : Hexagram), s + (Shi.dao : Shi)) = (h, s)
  rw [qianqian_eq_zero, dao_eq_zero, add_zero, add_zero]

theorem xor_self (c : Cell256) : xor c c = origin := by
  rcases c with ⟨h, s⟩
  show (h + h, s + s) = (Hexagram.qianqian, Shi.dao)
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · rw [R.add_self, ← qianqian_eq_zero]
  · rw [R.add_self, ← dao_eq_zero]

theorem xor_comm (c₁ c₂ : Cell256) : xor c₁ c₂ = xor c₂ c₁ := by
  rcases c₁ with ⟨h₁, s₁⟩
  rcases c₂ with ⟨h₂, s₂⟩
  show (h₁ + h₂, s₁ + s₂) = (h₂ + h₁, s₂ + s₁)
  refine Prod.mk.injEq .. |>.mpr ⟨add_comm h₁ h₂, add_comm s₁ s₂⟩

theorem xor_assoc (c₁ c₂ c₃ : Cell256) :
    xor (xor c₁ c₂) c₃ = xor c₁ (xor c₂ c₃) := by
  rcases c₁ with ⟨h₁, s₁⟩
  rcases c₂ with ⟨h₂, s₂⟩
  rcases c₃ with ⟨h₃, s₃⟩
  show (h₁ + h₂ + h₃, s₁ + s₂ + s₃) = (h₁ + (h₂ + h₃), s₁ + (s₂ + s₃))
  refine Prod.mk.injEq .. |>.mpr ⟨add_assoc h₁ h₂ h₃, add_assoc s₁ s₂ s₃⟩

/-! ## § 2 Add / Zero / Neg / Sub instance binding -/

instance : Add Cell256 := ⟨xor⟩
instance : Zero Cell256 := ⟨origin⟩
/-- Self-inverse in characteristic 2. -/
instance : Neg Cell256 := ⟨id⟩
instance : Sub Cell256 := ⟨xor⟩

@[simp] theorem add_def (c₁ c₂ : Cell256) : c₁ + c₂ = xor c₁ c₂ := rfl
@[simp] theorem zero_def : (0 : Cell256) = origin := rfl
@[simp] theorem neg_def (c : Cell256) : -c = c := rfl
@[simp] theorem sub_def (c₁ c₂ : Cell256) : c₁ - c₂ = xor c₁ c₂ := rfl

/-! ## § 3 Shi V₄ operators lifted to Cell256 (preserve the hexagram) -/

/-- 印 (yìn) — Shi complement (V₄ "P-like" axis), preserve hexagram.
    On named Shi: `dao ↔ ji`, `jin ↔ wei`. -/
def shiCuo (c : Cell256) : Cell256 := (c.1, Shi.complement c.2)

/-- 投 (tóu) — Shi reverse (V₄ "T-like" axis), preserve hexagram.
    On named Shi: `dao ↔ wei`, `ji ↔ jin`. -/
def shiZong (c : Cell256) : Cell256 := (c.1, Shi.reverse c.2)

/-- Shi cuoZong (= PT) lifted to Cell256, preserve hexagram.
    On named Shi: `dao ↔ jin`, `ji ↔ wei`. -/
def shiCuoZong (c : Cell256) : Cell256 := (c.1, Shi.cuoZong c.2)

theorem shiCuo_involutive (c : Cell256) : shiCuo (shiCuo c) = c := by
  rcases c with ⟨h, s⟩
  unfold shiCuo
  rw [Shi.complement_involutive]

theorem shiZong_involutive (c : Cell256) : shiZong (shiZong c) = c := by
  rcases c with ⟨h, s⟩
  unfold shiZong
  rw [Shi.reverse_involutive]

theorem shiCuoZong_involutive (c : Cell256) : shiCuoZong (shiCuoZong c) = c := by
  rcases c with ⟨h, s⟩
  unfold shiCuoZong
  rw [Shi.cuoZong_involutive]

/-! ## § 4 Hexagram operators lifted to Cell256 (preserve the Shi) -/

/-- 錯 (cuo) lifted to Cell256 — flip all 6 yao, preserve Shi. -/
def hexCuo (c : Cell256) : Cell256 := (Hexagram.cuo c.1, c.2)

/-- 綜 (zong) lifted to Cell256 — reverse the 6 yao, preserve Shi. -/
def hexZong (c : Cell256) : Cell256 := (Hexagram.zong c.1, c.2)

/-- 互 (hu) lifted to Cell256 — extract 2-3-4 / 3-4-5, preserve Shi. -/
def hexHu (c : Cell256) : Cell256 := (Hexagram.hu c.1, c.2)

/-- 錯綜 lifted (= V₄ central on hex), preserve Shi. -/
def hexCuoZong (c : Cell256) : Cell256 := (Hexagram.cuoZong c.1, c.2)

theorem hexCuo_involutive (c : Cell256) : hexCuo (hexCuo c) = c := by
  rcases c with ⟨h, s⟩
  unfold hexCuo
  rw [Hexagram.cuo_involutive]

theorem hexZong_involutive (c : Cell256) : hexZong (hexZong c) = c := by
  rcases c with ⟨h, s⟩
  unfold hexZong
  rw [Hexagram.zong_involutive]

theorem hexCuoZong_involutive (c : Cell256) : hexCuoZong (hexCuoZong c) = c := by
  rcases c with ⟨h, s⟩
  unfold hexCuoZong
  rw [Hexagram.cuoZong_involutive]

/-- hex and shi operators commute (act on disjoint axes). -/
theorem hexCuo_shiCuo_comm (c : Cell256) :
    hexCuo (shiCuo c) = shiCuo (hexCuo c) := by
  rcases c with ⟨h, s⟩; rfl

theorem hexZong_shiZong_comm (c : Cell256) :
    hexZong (shiZong c) = shiZong (hexZong c) := by
  rcases c with ⟨h, s⟩; rfl

theorem hexCuo_shiZong_comm (c : Cell256) :
    hexCuo (shiZong c) = shiZong (hexCuo c) := by
  rcases c with ⟨h, s⟩; rfl

theorem hexHu_shiCuo_comm (c : Cell256) :
    hexHu (shiCuo c) = shiCuo (hexHu c) := by
  rcases c with ⟨h, s⟩; rfl

/-! ## § 5 Six single-yao flips lifted -/

/-- Flip the i-th yao (0-indexed) of a hexagram, preserve Shi. -/
private def hexFlip (i : Fin 6) (h : Hexagram) : Hexagram :=
  fun j => if j = i then !(h j) else h j

private theorem hexFlip_involutive (i : Fin 6) (h : Hexagram) :
    hexFlip i (hexFlip i h) = h := by
  funext j
  unfold hexFlip
  by_cases hj : j = i
  · simp [hj, Bool.not_not]
  · simp [hj]

/-- flip yao 1 (bottom). -/
def flip1 (c : Cell256) : Cell256 := (hexFlip ⟨0, by decide⟩ c.1, c.2)
def flip2 (c : Cell256) : Cell256 := (hexFlip ⟨1, by decide⟩ c.1, c.2)
def flip3 (c : Cell256) : Cell256 := (hexFlip ⟨2, by decide⟩ c.1, c.2)
def flip4 (c : Cell256) : Cell256 := (hexFlip ⟨3, by decide⟩ c.1, c.2)
def flip5 (c : Cell256) : Cell256 := (hexFlip ⟨4, by decide⟩ c.1, c.2)
def flip6 (c : Cell256) : Cell256 := (hexFlip ⟨5, by decide⟩ c.1, c.2)

theorem flip1_involutive (c : Cell256) : flip1 (flip1 c) = c := by
  rcases c with ⟨h, s⟩; unfold flip1; rw [hexFlip_involutive]
theorem flip2_involutive (c : Cell256) : flip2 (flip2 c) = c := by
  rcases c with ⟨h, s⟩; unfold flip2; rw [hexFlip_involutive]
theorem flip3_involutive (c : Cell256) : flip3 (flip3 c) = c := by
  rcases c with ⟨h, s⟩; unfold flip3; rw [hexFlip_involutive]
theorem flip4_involutive (c : Cell256) : flip4 (flip4 c) = c := by
  rcases c with ⟨h, s⟩; unfold flip4; rw [hexFlip_involutive]
theorem flip5_involutive (c : Cell256) : flip5 (flip5 c) = c := by
  rcases c with ⟨h, s⟩; unfold flip5; rw [hexFlip_involutive]
theorem flip6_involutive (c : Cell256) : flip6 (flip6 c) = c := by
  rcases c with ⟨h, s⟩; unfold flip6; rw [hexFlip_involutive]

theorem flip1_shiCuo_comm (c : Cell256) :
    flip1 (shiCuo c) = shiCuo (flip1 c) := by
  rcases c with ⟨h, s⟩; rfl

/-! ## § 6 印/投 as XOR-with-mask forms -/

/-- 印 mask: only the YinBit (Shi.ji) is set. -/
def imprint_mask : Cell256 := (Hexagram.qianqian, Shi.ji)

/-- 投 mask: only the GuoBit (Shi.wei) is set. -/
def project_mask : Cell256 := (Hexagram.qianqian, Shi.wei)

/-- 印 (mask form): XOR with `imprint_mask`. -/
def imprint (c : Cell256) : Cell256 := xor c imprint_mask

/-- 投 (mask form): XOR with `project_mask`. -/
def project (c : Cell256) : Cell256 := xor c project_mask

/-- 印 is involutive (mask self-cancels). -/
theorem imprint_involutive (c : Cell256) : imprint (imprint c) = c := by
  unfold imprint
  rw [xor_assoc, xor_self, xor_origin]

/-- 投 is involutive. -/
theorem project_involutive (c : Cell256) : project (project c) = c := by
  unfold project
  rw [xor_assoc, xor_self, xor_origin]

/-- 印 and 投 commute. -/
theorem imprint_project_comm (c : Cell256) :
    imprint (project c) = project (imprint c) := by
  unfold imprint project
  rw [xor_assoc, xor_assoc, xor_comm project_mask imprint_mask]

/-! ## § 7 Projection: forget Shi component(s) -/

/-- Project down to `Cell128` by truncating Shi to its first bit (YinBit). -/
def project256to7 (c : Cell256) : Cell128 :=
  (c.1, c.2 ⟨0, by decide⟩)

/-- Project down to `Hexagram` by forgetting both Shi bits. -/
def project256to6 (c : Cell256) : Hexagram := c.1

@[simp] theorem project256to6_apply (h : Hexagram) (s : Shi) :
    project256to6 (h, s) = h := rfl

@[simp] theorem project256to6_origin :
    project256to6 origin = Hexagram.qianqian := rfl

@[simp] theorem project256to7_apply (h : Hexagram) (s : Shi) :
    project256to7 (h, s) = (h, s ⟨0, by decide⟩) := rfl

/-- The two projections compose: 7-then-6 = 6 directly. -/
theorem project_commutes (c : Cell256) :
    Cell128.project128to6 (project256to7 c) = project256to6 c := by
  rcases c with ⟨h, s⟩; rfl

/-- hex operators commute with the Shi-projection (since they don't touch Shi). -/
theorem project256to6_hexCuo (c : Cell256) :
    project256to6 (hexCuo c) = Hexagram.cuo (project256to6 c) := rfl

theorem project256to6_hexZong (c : Cell256) :
    project256to6 (hexZong c) = Hexagram.zong (project256to6 c) := rfl

theorem project256to6_shiCuo (c : Cell256) :
    project256to6 (shiCuo c) = project256to6 c := rfl

/-! ## § 8 Cayley regular representation (R₈ self-action) -/

instance : SMul Cell256 Cell256 := ⟨xor⟩

@[simp] theorem smul_def (c s : Cell256) : c • s = xor c s := rfl

/-- Cayley left-translation by `c` on `Cell256`. -/
def cayley (c : Cell256) : Cell256 → Cell256 := fun s => xor c s

/-- Evaluate any endo at the origin to recover its translation amount. -/
def epsAtOrigin (f : Cell256 → Cell256) : Cell256 := f origin

@[simp] theorem epsAtOrigin_cayley (c : Cell256) :
    epsAtOrigin (cayley c) = c := by
  unfold epsAtOrigin cayley
  exact xor_origin c

theorem cayley_inj : Function.Injective cayley := by
  intro c₁ c₂ h
  have := congrFun h origin
  unfold cayley at this
  rwa [xor_origin, xor_origin] at this

theorem cayley_hom (c₁ c₂ : Cell256) :
    cayley (xor c₁ c₂) = cayley c₁ ∘ cayley c₂ := by
  funext s
  unfold cayley
  rw [Function.comp_apply, xor_assoc]

/-! ## § 9 The V₄ group law on Shi-actions -/

/-- The 4 Shi V₄ actions on Cell256 are an involution group: identity,
    shiCuo, shiZong, shiCuoZong all of order ≤ 2. -/
theorem v4_shi_orders (c : Cell256) :
    c = c
  ∧ shiCuo (shiCuo c) = c
  ∧ shiZong (shiZong c) = c
  ∧ shiCuoZong (shiCuoZong c) = c :=
  ⟨rfl, shiCuo_involutive c, shiZong_involutive c, shiCuoZong_involutive c⟩

/-- The 4 hex V₄ actions on Cell256 are an involution group. -/
theorem v4_hex_orders (c : Cell256) :
    c = c
  ∧ hexCuo (hexCuo c) = c
  ∧ hexZong (hexZong c) = c
  ∧ hexCuoZong (hexCuoZong c) = c :=
  ⟨rfl, hexCuo_involutive c, hexZong_involutive c, hexCuoZong_involutive c⟩

/-! ## § 10 Public Phase-A summary -/

/-- R₈ Phase-A summary: (Z/2)⁸ group laws + Cayley fusion + 印/投 mask forms. -/
theorem cell256_phaseA_summary :
    (∀ c : Cell256, xor origin c = c)
    ∧ (∀ c : Cell256, xor c c = origin)
    ∧ (∀ a b : Cell256, xor a b = xor b a)
    ∧ (∀ a b c : Cell256, xor (xor a b) c = xor a (xor b c))
    ∧ Function.Injective cayley
    ∧ (∀ c : Cell256, epsAtOrigin (cayley c) = c)
    ∧ (∀ c : Cell256, imprint (imprint c) = c)
    ∧ (∀ c : Cell256, project (project c) = c)
    ∧ (∀ c : Cell256, imprint (project c) = project (imprint c)) :=
  ⟨origin_xor, xor_self, xor_comm, xor_assoc,
   cayley_inj, epsAtOrigin_cayley,
   imprint_involutive, project_involutive, imprint_project_comm⟩

end Cell256

end SSBX.Foundation.Atlas.Yi
