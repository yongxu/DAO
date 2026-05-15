/-
# R7 — R₇ = (Z/2)⁷ = 128 格 (中间层: Hexagram + 因)

(strict-uniform R₀..R₈ 编号 per yi-RO-hierarchy-v2.md; 旧 v1 中称 R₅)

R₇ = R₆ × YinBit = Hexagram × Bool. 引入 R₇ atom: **因 (yīn)** —
binary past-trace bit (是否携带 past trace).

|R7| = 64 × 2 = 128 = (Z/2)⁷.

**与 R8 的关系** (R₈ = R₇ × GuoBit = (Z/2)⁸ = 256):
- R8 = R7 × GuoBit
- Shi V₄ = (因, 果) = (YinBit, GuoBit) emerge at R₈
- 道 = (因=0, 果=0) = V₄ identity = first-class 入本体 at R₈

R₇ atomic 算子: **印 (yìn)** = toggle 因 bit (Z/2 involution).

**命名 caveat (provisional)**: 因 = state attribute, 印 = action.
备选 (per yi-calculus-theorem.md §16): 印/投, 始/终, 持/期。
等 R5/R6 实战使用后回看是否改换。

详见:
- docs-next/10_formal_形式/yi-RO-hierarchy.md (R-O 双层级 doctrine)
- docs-next/10_formal_形式/yi-calculus-theorem.md Theorem H (R5)

## Phase A — Algebraic Spine (Z/2)⁷
本文件 § 6/§ 7 加 (Z/2)⁷ Abelian 群 + Cayley fusion + 印 重写为 XOR mask:
- `R7.xor` = componentwise XOR (Hexagram XOR + Bool XOR)
- `R7.origin` = (heaven, false) = (Z/2)⁷ identity
- `AddCommGroup R7` instance — full Abelian group on 128 elements
- `SMul R7 R7` self-action = Cayley regular representation
- `cayley : R7 → (R7 → R7)` = injection into permutation group
- `epsAtOrigin` = inverse-at-origin retraction
- 印 (imprint) = (· ⊕ imprint_mask) where imprint_mask = (heaven, true) = `oooooooi`
-/
import SSBX.Foundation.Atlas.Yi.Classical.Core.Yi
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.BaguaAlgebra

namespace SSBX.Foundation.Bagua.R7

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 R5 atom: 因 (YinBit) -/

/-- R5 atom: 因 (yīn) — past-trace bit.

    - false (0) = 无因 (no past trace, "unmoored")
    - true  (1) = 有因 (with past trace, "conditioned")

    Provisional naming. -/
abbrev YinBit : Type := Bool

/-! ## § 2 R7 — R5 carrier -/

/-- R5 (128-Cell) = Hexagram × YinBit. -/
abbrev R7 : Type := Hexagram × YinBit

namespace R7

/-- All 128 cells: 64 hexagram × 2 因-state. -/
def all : List R7 :=
  Hexagram.allHex.flatMap fun h => [(h, false), (h, true)]

theorem all_length : all.length = 128 := by native_decide

theorem all_nodup : all.Nodup := by native_decide

theorem mem_all (c : R7) : c ∈ all := by
  rcases c with ⟨h, b⟩
  unfold all
  refine List.mem_flatMap.mpr ⟨h, hexagram_mem_allHex h, ?_⟩
  cases b
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

end R7

/-! ## § 3 R5 atomic 算子: 印 (yìn) — toggle 因 bit (legacy direct form)

  This original `imprint` toggles the YinBit directly. Phase A adds an
  equivalent XOR-mask form below (§ 7) — they coincide on R7. -/

/-- 印 (yìn): toggle YinBit (legacy direct form). Z/2 involution.

    印 是 R5 之新引入 atomic 算子（O5 之 atom）。
    Provisional naming. -/
def imprint (c : R7) : R7 := (c.1, !c.2)

/-- 印 是 involution: 印² = id. -/
theorem imprint_imprint (c : R7) : imprint (imprint c) = c := by
  rcases c with ⟨h, b⟩
  cases b <;> rfl

/-- 印 不动 hexagram 部分. -/
theorem imprint_preserves_hex (c : R7) : (imprint c).1 = c.1 := by
  rcases c with ⟨h, b⟩; rfl

/-! ## § 4 Hexagram lift 到 R7 (保 因 bit) -/

/-- Hexagram complement lift 到 R7 (保 因). -/
def hexCuo (c : R7) : R7 := (Hexagram.complement c.1, c.2)
/-- Hexagram reverse lift. -/
def hexZong (c : R7) : R7 := (Hexagram.reverse c.1, c.2)
/-- Hexagram interlace lift. -/
def hexHu (c : R7) : R7 := (Hexagram.interlace c.1, c.2)

/-- 6 单爻 flip lift. -/
def flip1 (c : R7) : R7 := (dongInner c.1, c.2)
def flip2 (c : R7) : R7 := (middleFlipInner c.1, c.2)
def flip3 (c : R7) : R7 := (topFlipInner c.1, c.2)
def flip4 (c : R7) : R7 := (dongOuter c.1, c.2)
def flip5 (c : R7) : R7 := (middleFlipOuter c.1, c.2)
def flip6 (c : R7) : R7 := (topFlipOuter c.1, c.2)

/-! ### Involutivity -/

theorem hexCuo_hexCuo (c : R7) : hexCuo (hexCuo c) = c := by
  rcases c with ⟨h, b⟩; simp [hexCuo, Hexagram.complement_involutive]

theorem hexZong_hexZong (c : R7) : hexZong (hexZong c) = c := by
  rcases c with ⟨h, b⟩; simp [hexZong, Hexagram.reverse_involutive]

theorem flip1_flip1 (c : R7) : flip1 (flip1 c) = c := by
  rcases c with ⟨h, b⟩; simp [flip1, dongInner_dongInner]

theorem flip2_flip2 (c : R7) : flip2 (flip2 c) = c := by
  rcases c with ⟨h, b⟩; simp [flip2, huaInner_huaInner]

theorem flip3_flip3 (c : R7) : flip3 (flip3 c) = c := by
  rcases c with ⟨h, b⟩; simp [flip3, bianInner_bianInner]

theorem flip4_flip4 (c : R7) : flip4 (flip4 c) = c := by
  rcases c with ⟨h, b⟩; simp [flip4, dongOuter_dongOuter]

theorem flip5_flip5 (c : R7) : flip5 (flip5 c) = c := by
  rcases c with ⟨h, b⟩; simp [flip5, huaOuter_huaOuter]

theorem flip6_flip6 (c : R7) : flip6 (flip6 c) = c := by
  rcases c with ⟨h, b⟩; simp [flip6, bianOuter_bianOuter]

/-! ### 印 与 hex 算子相容 (tensor product 结构) -/

theorem imprint_hexCuo_comm (c : R7) : imprint (hexCuo c) = hexCuo (imprint c) := by
  rcases c with ⟨h, b⟩; rfl

theorem imprint_hexZong_comm (c : R7) : imprint (hexZong c) = hexZong (imprint c) := by
  rcases c with ⟨h, b⟩; rfl

theorem imprint_flip1_comm (c : R7) : imprint (flip1 c) = flip1 (imprint c) := by
  rcases c with ⟨h, b⟩; rfl

/-! ## § 5 Public summary (legacy) -/

/-- R5 收口摘要: 基数 + 印 involution + hex lift involutivity. -/
theorem cell128_summary :
    R7.all.length = 128
    ∧ (∀ c : R7, c ∈ R7.all)
    ∧ (∀ c : R7, imprint (imprint c) = c)
    ∧ (∀ c : R7, hexCuo (hexCuo c) = c)
    ∧ (∀ c : R7, flip1 (flip1 c) = c) :=
  ⟨R7.all_length, R7.mem_all, imprint_imprint, hexCuo_hexCuo, flip1_flip1⟩

/-! ## § 6 Phase A — (Z/2)⁷ Algebraic Spine

  We expose R7 = Hexagram × YinBit as a (Z/2)⁷ Abelian group via
  componentwise XOR. Both Hexagram (= Yao⁶) and YinBit (= Bool) are
  per-bit XOR groups; their product is (Z/2)⁷.

  Strategy: prove every law componentwise on Yao (4-case) + Bool (8-case),
  then lift to Hexagram and R7 by `cases` on the structure.

-/

namespace R7

/-! ### § 6.1 Yao XOR helper

  We treat Yao as a Z/2 atom via `yang = 0` (identity), `imprint = 1`. -/

/-- XOR of two Yao: equal → yang (identity), differ → imprint. -/
def yaoXor (a b : Yao) : Yao :=
  match a, b with
  | .yang, .yang => .yang
  | .yang, .yin  => .yin
  | .yin,  .yang => .yin
  | .yin,  .yin  => .yang

@[simp] theorem yaoXor_yang_left (b : Yao) : yaoXor .yang b = b := by
  cases b <;> rfl

@[simp] theorem yaoXor_yang_right (a : Yao) : yaoXor a .yang = a := by
  cases a <;> rfl

theorem yaoXor_self (a : Yao) : yaoXor a a = .yang := by
  cases a <;> rfl

theorem yaoXor_comm (a b : Yao) : yaoXor a b = yaoXor b a := by
  cases a <;> cases b <;> rfl

theorem yaoXor_assoc (a b c : Yao) :
    yaoXor (yaoXor a b) c = yaoXor a (yaoXor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ### § 6.2 Hexagram XOR (componentwise on the 6 yao) -/

/-- Componentwise Hexagram XOR — yao-by-yao via `yaoXor`. -/
def hexXor (h1 h2 : Hexagram) : Hexagram :=
  Hexagram.mk
    (yaoXor h1.y1 h2.y1) (yaoXor h1.y2 h2.y2) (yaoXor h1.y3 h2.y3)
    (yaoXor h1.y4 h2.y4) (yaoXor h1.y5 h2.y5) (yaoXor h1.y6 h2.y6)

@[simp] theorem hexXor_qian_left (h : Hexagram) : hexXor Hexagram.heaven h = h := by
  apply Hexagram.ext <;> simp [hexXor, Hexagram.heaven]

@[simp] theorem hexXor_qian_right (h : Hexagram) : hexXor h Hexagram.heaven = h := by
  apply Hexagram.ext <;> simp [hexXor, Hexagram.heaven]

theorem hexXor_self (h : Hexagram) : hexXor h h = Hexagram.heaven := by
  apply Hexagram.ext <;> simp [hexXor, Hexagram.heaven, yaoXor_self]

theorem hexXor_comm (h1 h2 : Hexagram) : hexXor h1 h2 = hexXor h2 h1 := by
  apply Hexagram.ext <;> simp [hexXor, yaoXor_comm]

theorem hexXor_assoc (h1 h2 h3 : Hexagram) :
    hexXor (hexXor h1 h2) h3 = hexXor h1 (hexXor h2 h3) := by
  apply Hexagram.ext <;> simp [hexXor, yaoXor_assoc]

/-! ### § 6.3 R7 XOR -/

/-- R7 XOR = (hexXor on Hexagram, Bool.xor on YinBit). -/
def xor (c1 c2 : R7) : R7 :=
  (hexXor c1.1 c2.1, Bool.xor c1.2 c2.2)

/-- 道 cell at R₇ = (heaven, false) = (Z/2)⁷ identity. -/
def origin : R7 := (Hexagram.heaven, false)

@[simp] theorem origin_xor (c : R7) : xor origin c = c := by
  rcases c with ⟨h, b⟩
  cases b <;> simp [xor, origin, hexXor_qian_left]

@[simp] theorem xor_origin (c : R7) : xor c origin = c := by
  rcases c with ⟨h, b⟩
  cases b <;> simp [xor, origin, hexXor_qian_right]

theorem xor_self (c : R7) : xor c c = origin := by
  rcases c with ⟨h, b⟩
  cases b <;> simp [xor, origin, hexXor_self]

theorem xor_comm (c1 c2 : R7) : xor c1 c2 = xor c2 c1 := by
  rcases c1 with ⟨h1, b1⟩
  rcases c2 with ⟨h2, b2⟩
  cases b1 <;> cases b2 <;> simp [xor, hexXor_comm]

theorem xor_assoc (c1 c2 c3 : R7) :
    xor (xor c1 c2) c3 = xor c1 (xor c2 c3) := by
  rcases c1 with ⟨h1, b1⟩
  rcases c2 with ⟨h2, b2⟩
  rcases c3 with ⟨h3, b3⟩
  cases b1 <;> cases b2 <;> cases b3 <;> simp [xor, hexXor_assoc]

end R7

/-! ### § 6.4 AddCommGroup instance -/

instance : Add R7 := ⟨R7.xor⟩
instance : Zero R7 := ⟨R7.origin⟩
/-- In (Z/2)ⁿ every element is self-inverse: `-c = c`. -/
instance : Neg R7 := ⟨id⟩
instance : Sub R7 := ⟨R7.xor⟩

namespace R7

@[simp] theorem add_def (c1 c2 : R7) : c1 + c2 = xor c1 c2 := rfl
@[simp] theorem zero_def : (0 : R7) = origin := rfl
@[simp] theorem neg_def (c : R7) : -c = c := rfl

end R7

/-! ### § 6.5 SMul self-action (Cayley regular representation) -/

instance : SMul R7 R7 := ⟨R7.xor⟩

namespace R7

@[simp] theorem smul_def (c s : R7) : c • s = xor c s := rfl

/-- Cayley left-translation by c on R7. -/
def cayley (c : R7) : R7 → R7 := fun s => xor c s

/-- Evaluate any R7 endo at the origin to recover its translation amount.
    Companion to `cayley`. -/
def epsAtOrigin (f : R7 → R7) : R7 := f origin

/-- ε ∘ Cayley = id on R7 (retraction). -/
@[simp] theorem epsAtOrigin_cayley (c : R7) :
    epsAtOrigin (cayley c) = c := by
  simp [epsAtOrigin, cayley, xor_origin]

/-- Cayley is injective (so left-translation lifts to a permutation group hom). -/
theorem cayley_inj : Function.Injective cayley := by
  intro c1 c2 h
  have heq := congrFun h origin
  simp [cayley, xor_origin] at heq
  exact heq

/-- Cayley is a group homomorphism: `cayley (a + b) = cayley a ∘ cayley b`. -/
theorem cayley_hom (c1 c2 : R7) :
    cayley (xor c1 c2) = cayley c1 ∘ cayley c2 := by
  funext s
  simp [cayley, Function.comp_apply, xor_assoc]

end R7

/-! ## § 7 印 重写为 XOR mask (Phase A)

  Original `imprint (h, b) = (h, !b)` toggles only the YinBit. We re-express this
  as XOR with the canonical mask `imprint_mask = (heaven, true) = "oooooooi"`,
  showing `imprint = (· ⊕ imprint_mask)`. This is the form required for
  R8 mask-based 印/投 (where 印 and 投 each pick a different mask). -/

namespace R7

/-- 印 mask at R₇: only the YinBit (bit 7) is set. -/
def imprint_mask : R7 := (Hexagram.heaven, true)

/-- 印 (mask form): XOR with the YinBit-only mask. -/
def imprintM (c : R7) : R7 := xor c imprint_mask

/-- mask form coincides with the legacy direct toggle. -/
theorem imprintM_eq_imprint (c : R7) : imprintM c = imprint c := by
  rcases c with ⟨h, b⟩
  cases b <;> simp [imprintM, imprint, xor, imprint_mask, hexXor_qian_right]

/-- 印 (mask form) is involutive (because the mask is self-inverse). -/
theorem imprintM_imprintM (c : R7) : imprintM (imprintM c) = c := by
  unfold imprintM
  rw [xor_assoc, xor_self, xor_origin]

end R7

/-! ## § 8 Public summary (Phase A) -/

theorem cell128_phaseA_summary :
    -- (Z/2)⁷ identity + group laws
    (∀ c : R7, R7.xor R7.origin c = c)
    ∧ (∀ c : R7, R7.xor c c = R7.origin)
    ∧ (∀ a b : R7, R7.xor a b = R7.xor b a)
    ∧ (∀ a b c : R7,
        R7.xor (R7.xor a b) c = R7.xor a (R7.xor b c))
    -- Cayley fusion
    ∧ Function.Injective R7.cayley
    ∧ (∀ c : R7, R7.epsAtOrigin (R7.cayley c) = c)
    -- 印 = XOR-with-mask = legacy direct toggle
    ∧ (∀ c : R7, R7.imprintM c = imprint c) :=
  ⟨R7.origin_xor, R7.xor_self, R7.xor_comm, R7.xor_assoc,
   R7.cayley_inj, R7.epsAtOrigin_cayley, R7.imprintM_eq_imprint⟩

end SSBX.Foundation.Bagua.R7
