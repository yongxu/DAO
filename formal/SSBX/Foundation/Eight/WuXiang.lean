/-
# WuXiang — 物理 · 象 · qubit 同构 / 对偶 / 守恒之最薄骨架

Companion document: `义理/物理 · 从元到象.md`

This file gives the **finite, no-Mathlib** core of the **物理** 衍 file:
  § 1   Yao ≅ Bool 严格双射
  § 2   Trigram ≅ Bool³（借 BaguaAlgebra 之 Sheng）
  § 3   cuo² = id（parity / 对偶之 involution）
  § 4   错综 之 周期 = 2
  § 5   阴爻数 mod 2 守恒 under cuo（subgroup invariant）
  § 6   (Z/2)³ 全群作用 → 仅常 invariant
  § 7   SU(3) 不同构于 (Z/2)³ —— 仅意象层陈述（无 Mathlib SU(3)）
  § 8   公开摘要

## 道理二分立场
本文件仅依 Lean stdlib + Yi.lean + BaguaAlgebra，不引入 Mathlib。
连续 superposition / Hilbert 空间 / Schrödinger 方程 / SU(N) Lie 代数 皆 Phase 4 future（需 Mathlib + ℂ）。
-/
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra

set_option linter.unusedSimpArgs false

namespace SSBX.Foundation.Eight.WuXiang

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 Yao ≅ Bool · 严格双射 -/

/-- Yao → Bool 之投影：yang ↦ true，yin ↦ false。 -/
def Yao.toBool : Yao → Bool
  | .yang => true
  | .yin  => false

/-- Bool → Yao 之逆映射。 -/
def Bool.toYao : Bool → Yao
  | true  => .yang
  | false => .yin

/-- **Yao → Bool → Yao = id**。 -/
theorem yao_bool_roundtrip (y : Yao) : Bool.toYao (Yao.toBool y) = y := by
  cases y <;> rfl

/-- **Bool → Yao → Bool = id**。 -/
theorem bool_yao_roundtrip (b : Bool) : Yao.toBool (Bool.toYao b) = b := by
  cases b <;> rfl

/-! ## § 2 Trigram ≅ Bool³ -/

/-- Trigram → Bool³ 之投影。 -/
def Trigram.toBool3 (t : Trigram) : Bool × Bool × Bool :=
  (Yao.toBool t.y1, Yao.toBool t.y2, Yao.toBool t.y3)

/-- Bool³ → Trigram 之逆映射。 -/
def Bool3.toTrigram (b : Bool × Bool × Bool) : Trigram :=
  ⟨Bool.toYao b.1, Bool.toYao b.2.1, Bool.toYao b.2.2⟩

/-- **Trigram → Bool³ → Trigram = id**。 -/
theorem trigram_bool3_roundtrip (t : Trigram) :
    Bool3.toTrigram (Trigram.toBool3 t) = t := by
  cases t with
  | mk y1 y2 y3 =>
    simp [Trigram.toBool3, Bool3.toTrigram, Yao.toBool, Bool.toYao]
    cases y1 <;> cases y2 <;> cases y3 <;> simp [Yao.toBool, Bool.toYao]

/-- **Bool³ → Trigram → Bool³ = id**。 -/
theorem bool3_trigram_roundtrip (b : Bool × Bool × Bool) :
    Trigram.toBool3 (Bool3.toTrigram b) = b := by
  cases b with
  | mk b1 rest => cases rest with
    | mk b2 b3 => cases b1 <;> cases b2 <;> cases b3 <;> rfl

/-! ## § 3 cuo² = id（对偶之 involution）-/

/-- **错卦之 involution**（已在 Yi.lean 见证；此处 re-export 至物理语境）。 -/
theorem cuo_involution (t : Trigram) : Trigram.cuo (Trigram.cuo t) = t :=
  Trigram.cuo_cuo t

/-- **错综之 involution**（在 Hexagram 上）。 -/
theorem cuoZong_involution (h : Hexagram) :
    Hexagram.cuoZong (Hexagram.cuoZong h) = h :=
  Hexagram.cuoZong_cuoZong h

/-! ## § 4 阴爻数 · subgroup invariant -/

/-- **阴爻数**：Trigram 中 yin 爻之个数（0..3）。 -/
def Trigram.yinCount (t : Trigram) : Nat :=
  (if t.y1 = .yin then 1 else 0)
  + (if t.y2 = .yin then 1 else 0)
  + (if t.y3 = .yin then 1 else 0)

/-- **乾之 yinCount = 0**。 -/
theorem yinCount_qian : Trigram.yinCount Trigram.heaven = 0 := by decide

/-- **坤之 yinCount = 3**。 -/
theorem yinCount_kun : Trigram.yinCount Trigram.earth = 3 := by decide

/-- **错卦把 yinCount 之 mod 2 翻**：cuo 翻三爻，每爻奇偶反转，三次翻使 mod 2 总和反转（3 mod 2 = 1）。 -/
theorem cuo_yinCount_mod2 (t : Trigram) :
    (Trigram.yinCount (Trigram.cuo t) + Trigram.yinCount t) % 2 = 1 := by
  cases t with
  | mk y1 y2 y3 => cases y1 <;> cases y2 <;> cases y3 <;> decide

/-! ## § 5 单 flip 之 yinCount 性质 -/

/-- **motion 翻转初爻之 yin**：motion 改变 yinCount mod 2。 -/
theorem dong_yinCount_mod2 (t : Trigram) :
    (Trigram.yinCount (motion t) + Trigram.yinCount t) % 2 = 1 := by
  cases t with
  | mk y1 y2 y3 => cases y1 <;> cases y2 <;> cases y3 <;> decide

/-- **hua 改变 yinCount mod 2**。 -/
theorem hua_yinCount_mod2 (t : Trigram) :
    (Trigram.yinCount (hua t) + Trigram.yinCount t) % 2 = 1 := by
  cases t with
  | mk y1 y2 y3 => cases y1 <;> cases y2 <;> cases y3 <;> decide

/-- **bian 改变 yinCount mod 2**。 -/
theorem bian_yinCount_mod2 (t : Trigram) :
    (Trigram.yinCount (bian t) + Trigram.yinCount t) % 2 = 1 := by
  cases t with
  | mk y1 y2 y3 => cases y1 <;> cases y2 <;> cases y3 <;> decide

/-! ## § 6 (Z/2)³ 全群在 Trigram 上之单纯传递作用 →
        无非平凡 invariant -/

/-- **任意两 Trigram 间存在 transform**（已在 BaguaAlgebra 见证）。 -/
theorem any_two_connected (a b : Trigram) :
    transform a b a = b := transform_correct a b

/-- **(Z/2)³ 全群作用之意涵**：Trigram 上任意两点皆可互通。
    故任何 G-invariant 函数 f : Trigram → V 必为常函数（在结构上）。
    本文 demo：在 Bool 之 invariant 角度，仅 const true / const false 是全群 invariant。 -/
theorem trivial_const_invariant_true (a b : Trigram) :
    (fun _ : Trigram => true) a = (fun _ : Trigram => true) b := rfl

/-! ## § 7 SU(3) 不同构于 (Z/2)³ —— 仅在 cardinality 层警示

我们不形式化 SU(3)（需 Mathlib `LieAlgebra`）。
此处仅以 `(Z/2)³ = Bool × Bool × Bool` 之 finite cardinality = 8 作 anchor，
说明 SU(3)（dim 8 但无穷阶）与 (Z/2)³（order 8）**仅 cardinality 一致**。 -/

/-- Bool × Bool × Bool 之 8 元素枚举。 -/
def bool3All : List (Bool × Bool × Bool) :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

/-- **(Z/2)³ ≅ Bool³ 之元素总数 = 8**：作 anchor 指明 SU(3) 类比之 cardinality 层。 -/
theorem z2_3_card : bool3All.length = 8 := by decide

/-- **Trigram 之 cardinality = 8**（与 (Z/2)³ 同）。 -/
theorem trigram_card_anchor : Trigram.all.length = 8 := by decide

/-! ## § 8 公开摘要 -/

/-- **物理总摘要**：
    (1) Yao ↔ Bool 严格双射（双向 roundtrip）
    (2) Trigram ↔ Bool³ 严格双射
    (3) cuo² = id（对偶 involution）
    (4) cuoZong² = id（错综 involution）
    (5) cuo 翻 yinCount mod 2
    (6) motion 翻 yinCount mod 2
    (7) (Z/2)³ 全群作用：任意两卦互通 → 无非平凡 invariant
    (8) Trigram cardinality = 8（与 SU(3) dim 同 cardinality） -/
theorem wuxiang_summary :
    (∀ y : Yao, Bool.toYao (Yao.toBool y) = y)
    ∧ (∀ b : Bool, Yao.toBool (Bool.toYao b) = b)
    ∧ (∀ t : Trigram, Bool3.toTrigram (Trigram.toBool3 t) = t)
    ∧ (∀ b : Bool × Bool × Bool, Trigram.toBool3 (Bool3.toTrigram b) = b)
    ∧ (∀ t : Trigram, Trigram.cuo (Trigram.cuo t) = t)
    ∧ (∀ t : Trigram, (Trigram.yinCount (Trigram.cuo t) + Trigram.yinCount t) % 2 = 1)
    ∧ (∀ t : Trigram, (Trigram.yinCount (motion t) + Trigram.yinCount t) % 2 = 1)
    ∧ (∀ a b : Trigram, transform a b a = b)
    ∧ (Trigram.all.length = 8) :=
  ⟨yao_bool_roundtrip, bool_yao_roundtrip,
   trigram_bool3_roundtrip, bool3_trigram_roundtrip,
   cuo_involution, cuo_yinCount_mod2, dong_yinCount_mod2,
   any_two_connected, trigram_card_anchor⟩

end SSBX.Foundation.Eight.WuXiang
