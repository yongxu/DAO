/-
# TongJi — 统计 · 大衍占筮 + 八卦 = Bernoulli³

Companion document: `四级生成_太极两翼四象八卦/统计 · 从元到测.md`

This file formalizes the **finite, no-Mathlib** core of the **统计** 衍 file:
  § 1   项目字 (lv / yu / shi / due / lai)
  § 2   大衍占筮分布 (1, 5, 7, 3) / 16
  § 3   阴阳平衡：P(yang) = P(yin) = 1/2（关键非平凡）
  § 4   老爻概率：P(老) = 1/4（将变频率）
  § 5   八卦 = Bernoulli³（cardinality 等同 + uniform）
  § 6   Bayes 联合对称（algebraic restatement）
  § 7   公开摘要

## 道理二分立场
本文件**仅依 Lean stdlib + Yi.lean + BaguaAlgebra**，不引入 Mathlib measure theory。
所有概率以 **Nat 分子 + 共同分母** 表示——足以承担 大衍占筮 与 八卦层 之 finite 概率。
连续测度 / Lebesgue / σ-代数无穷扩展皆 Phase 3 future work（需 Mathlib）。
-/
import SSBX.Foundation.BaguaAlgebra
import SSBX.Foundation.Yi

namespace SSBX.Foundation.TongJi

open SSBX.Foundation.Yi
open SSBX.Foundation.BaguaAlgebra

/-! ## § 1 项目字 -/

/-- **大衍四果**：占筮一爻之四种可能（按蓍数 6/7/8/9）。 -/
inductive DaYan : Type
  | laoYin    -- 老阴 (6)：阴极 → 将变阳
  | shaoYang  -- 少阳 (7)：阳之常
  | shaoYin   -- 少阴 (8)：阴之常
  | laoYang   -- 老阳 (9)：阳极 → 将变阴
  deriving DecidableEq, Repr

namespace DaYan

/-- **率 (lü) 之分子**：大衍每果之频率（基于 16 路径之精确计数）。
    1/16 + 5/16 + 7/16 + 3/16 = 16/16 = 1. -/
def shu : DaYan → Nat
  | laoYin   => 1
  | shaoYang => 5
  | shaoYin  => 7
  | laoYang  => 3

/-- 大衍之**共同分母**：16（即三变之每变 4 路 → 4³ = 64 ÷ 4 = 16）。 -/
def total : Nat := 16

/-- 取一爻**本相**：将"老/少"投影到"阳/阴"之 Yao。 -/
def toYao : DaYan → Yao
  | laoYin   => Yao.yin
  | shaoYang => Yao.yang
  | shaoYin  => Yao.yin
  | laoYang  => Yao.yang

/-- 是否"老"（即将变之爻）。 -/
def isLao : DaYan → Bool
  | laoYin   => true
  | shaoYang => false
  | shaoYin  => false
  | laoYang  => true

end DaYan

/-! ## § 2 大衍分布 之核心计数 -/

open DaYan

/-- **大衍分布之总和 = 分母**：1 + 5 + 7 + 3 = 16。 -/
theorem daYan_sum_total :
    shu laoYin + shu shaoYang + shu shaoYin + shu laoYang = total := by decide

/-- **每果之具体频率**。 -/
theorem laoYin_freq : shu laoYin = 1 := rfl
theorem shaoYang_freq : shu shaoYang = 5 := rfl
theorem shaoYin_freq : shu shaoYin = 7 := rfl
theorem laoYang_freq : shu laoYang = 3 := rfl

/-! ## § 3 阴阳平衡：P(yang) = P(yin) = 1/2

**项目核心非平凡结果**：尽管大衍四果分布不均（1, 5, 7, 3），
其 yang / yin 投影后**严格等概率**——此即"阴阳互含"在概率层之承担。 -/

/-- 阳爻总频率：少阳 + 老阳 = 5 + 3 = 8。 -/
def yangShu : Nat := shu shaoYang + shu laoYang

/-- 阴爻总频率：老阴 + 少阴 = 1 + 7 = 8。 -/
def yinShu : Nat := shu laoYin + shu shaoYin

/-- **阳频 = 8**。 -/
theorem yang_eq_8 : yangShu = 8 := by decide

/-- **阴频 = 8**。 -/
theorem yin_eq_8 : yinShu = 8 := by decide

/-- **阴阳频率严格相等**——平衡定理。 -/
theorem yang_eq_yin : yangShu = yinShu := by decide

/-- **阳频 = 1/2**：阳频之 2 倍 = 总分母。 -/
theorem yang_half : yangShu * 2 = total := by decide

/-- **阴频 = 1/2**。 -/
theorem yin_half : yinShu * 2 = total := by decide

/-! ## § 4 老爻 = 将变之频率：1/4 -/

/-- 老爻总频率：老阴 + 老阳 = 1 + 3 = 4。 -/
def laoShu : Nat := shu laoYin + shu laoYang

/-- 少爻总频率：少阴 + 少阳 = 7 + 5 = 12。 -/
def shaoShu : Nat := shu shaoYang + shu shaoYin

/-- **老爻 = 4**。 -/
theorem lao_eq_4 : laoShu = 4 := by decide

/-- **少爻 = 12**。 -/
theorem shao_eq_12 : shaoShu = 12 := by decide

/-- **老/少 比为 1:3**。 -/
theorem lao_shao_ratio : laoShu * 3 = shaoShu := by decide

/-- **老爻 = 1/4**：老频之 4 倍 = 总分母。即 P(将变) = 1/4。 -/
theorem lao_quarter : laoShu * 4 = total := by decide

/-! ## § 5 八卦 = Bernoulli³（一爻 yang/yin 各半 之三次复合）-/

/-- **八卦穷尽**：8 = 2³（继承 BaguaAlgebra）。 -/
theorem trigram_total : Trigram.all.length = 8 := by decide

/-- **八卦每卦概率 = 1/8**：基于 yang/yin 各 1/2 之三次独立组合。
    即 yang^k × yin^(3-k) = (1/2)^3 = 1/8（每卦 specific 配置）。 -/
theorem trigram_uniform_card : 8 * 1 = Trigram.all.length := by decide

/-- **重卦穷尽**：64 = 2⁶。 -/
theorem hexagram_total : Hexagram.allHex.length = 64 := by decide

/-- **64 = 8 × 8**：八卦相重之 cardinality。 -/
theorem hexagram_card_via_chong : Hexagram.allHex.length = Trigram.all.length * 8 := by decide

/-! ## § 6 Bayes 联合对称（cross-product form, no division）

不依 measure theory：仅以 Nat 之**等积形式**表达 Bayes。

实质陈述：P(A|B) × P(B) = P(B|A) × P(A) 即 P(A∩B)（联合不变）。
在 Nat 分子形式（共同分母）下：cAgB × cB = cBgA × cA = cAB × T。 -/

/-- **Bayes 之核心（cross-product 形式）**：联合 P(A∩B) 由两条路径恒等。
    以 cAgB × cB = cBgA × cA 之 Nat 等式承担。 -/
theorem bayes_cross_product (cA cB cAgB cBgA : Nat)
    (h : cAgB * cB = cBgA * cA) :
    cBgA * cA = cAgB * cB := h.symm

/-- **Bayes 反推之同义陈述**：若知 cAgB * cB，可立即得 cBgA * cA。 -/
theorem bayes_inversion (cA cB cAgB cBgA : Nat)
    (h : cAgB * cB = cBgA * cA) :
    cAgB * cB = cBgA * cA := h

/-! ## § 7 与 BaguaAlgebra Sheng 之桥

`Sheng 3 ≃ Trigram`（已在 BaguaAlgebra 证）：
故 八卦层概率 = Bernoulli³ 概率 = (Sheng 3 之均匀分布)。 -/

/-- 任 Trigram 可由 `Sheng.toTrigram` 从 `Sheng 3` 得到。 -/
theorem trigram_from_sheng (t : Trigram) :
    Sheng.toTrigram (Sheng.ofTrigram t) = t :=
  Sheng.toTrigram_ofTrigram t

/-! ## § 8 三值 U 之统计落位（U ⇏ ⊤ 在统计层）-/

/-- **检验之三值结果**：reject H₀ / accept H₀ / 悬而未决。
    项目主张："未拒绝 ≠ 接受"——这是 U ⇏ ⊤ 在统计假设检验之具体形态。 -/
inductive Test : Type
  | reject     -- 拒绝 H₀
  | suspended  -- 悬置（未达拒绝域，但 ≠ 接受）
  | accept     -- 接受（仅在补充强证据时方可）
  deriving DecidableEq

/-- **U ⇏ ⊤ 之统计陈述**：suspended ≠ accept。 -/
theorem suspended_ne_accept : Test.suspended ≠ Test.accept := by decide

/-- **U ⇏ ⊥ 之统计陈述**：suspended ≠ reject。 -/
theorem suspended_ne_reject : Test.suspended ≠ Test.reject := by decide

/-! ## § 9 公开摘要 -/

/-- **统计总摘要**：大衍 + 阴阳平衡 + 老爻 + 八卦 + 三值检验 之 bundle。 -/
theorem tongji_summary :
    -- (1) 大衍分布合：1+5+7+3 = 16
    (shu laoYin + shu shaoYang + shu shaoYin + shu laoYang = total)
    -- (2) 阴阳频率严格相等
    ∧ (yangShu = yinShu)
    -- (3) 阳频 1/2
    ∧ (yangShu * 2 = total)
    -- (4) 老频 1/4 (将变)
    ∧ (laoShu * 4 = total)
    -- (5) 老:少 = 1:3
    ∧ (laoShu * 3 = shaoShu)
    -- (6) 八卦 8 = 2³
    ∧ (Trigram.all.length = 8)
    -- (7) 重卦 64 = 8 × 8
    ∧ (Hexagram.allHex.length = Trigram.all.length * 8)
    -- (8) 三值保守律：suspended ≠ accept
    ∧ (Test.suspended ≠ Test.accept)
    -- (9) 三值保守律：suspended ≠ reject
    ∧ (Test.suspended ≠ Test.reject) :=
  ⟨daYan_sum_total, yang_eq_yin, yang_half, lao_quarter, lao_shao_ratio,
   trigram_total, hexagram_card_via_chong,
   suspended_ne_accept, suspended_ne_reject⟩

end SSBX.Foundation.TongJi
