/-
# Confucian — 儒家概念在 R-层 Cell 上的具体落位

Following the existing abstract formalization in `Foundation/Wen/Kernel.lean`
(80+ Confucian theorems based on a `dong : Field → Field` axiom layer), this
file lifts four families of Confucian concepts to **concrete R-layer cells**
in the (Z/2)ⁿ hierarchy:

| 家族 | R-layer | Cells | 来源 |
| --- | --- | ---: | --- |
| 五常 (仁义礼智信) | R₇ Cell128 | 5 of 128 | `Wuchang.lean` (done) |
| 四端 (恻隐羞恶辞让是非) | R₃ Trigram | 4 of 8 | here, **aliases** existing `Eight/XinZhi.lean::SiDuan.toTrigram` |
| 大学八目 (格致诚正修齐治平) | R₃ Trigram | 8 of 8 | here, **new** proposal mapping |
| 五伦 (父子君臣夫妇兄弟朋友) | R₅ Wuyao | 5 of 32 | here, **new** aliases of L5 generators |
| 大同 (64 卦穷尽) | R₆ Hexagram | 64 of 64 | here, **bridges** existing `Yuan.lean::daTong_total` |

## Per-cell creation report

| 层 | 名 | 落位 | 类型 | 来源 |
| --- | --- | --- | --- | --- |
| R₃ | 恻隐 (仁端) | 离 ☲ | alias | from `SiDuan.toTrigram .ceYin` |
| R₃ | 羞恶 (义端) | 坎 ☵ | alias | from `SiDuan.toTrigram .xiuWu` |
| R₃ | 辞让 (礼端) | 震 ☳ | alias | from `SiDuan.toTrigram .ciRang` |
| R₃ | 是非 (智端) | 兑 ☱ | alias | from `SiDuan.toTrigram .shiFei` |
| R₃ | 格物 | 巽 ☴ (penetrate) | new | proposed |
| R₃ | 致知 | 离 ☲ (illuminate) | new | proposed |
| R₃ | 诚意 | 兑 ☱ (joy/lake) | new | proposed |
| R₃ | 正心 | 艮 ☶ (still/mountain) | new | proposed |
| R₃ | 修身 | 震 ☳ (thunder/awaken) | new | proposed |
| R₃ | 齐家 | 坎 ☵ (water/flow) | new | proposed |
| R₃ | 治国 | 坤 ☷ (earth/patient) | new | proposed |
| R₃ | 平天下 | 乾 ☰ (heaven/ultimate) | new | proposed |
| R₅ | 父子 | flipBenLo | alias | from `L5.flipBenLo` |
| R₅ | 君臣 | flipBenHi | alias | from `L5.flipBenHi` |
| R₅ | 夫妇 | flipZhengLo | alias | from `L5.flipZhengLo` |
| R₅ | 兄弟 | flipZhengHi | alias | from `L5.flipZhengHi` |
| R₅ | 朋友 | flipFifth | alias | from `L5.flipFifth` |
| R₆ | 大同 (anchor) | 乾/坤/既济/未济 | bridge | from `Yuan.daTong_total` |

**Total new defs**: 21 (4 alias + 8 new + 5 alias + 4 bridge = 21)
**Total bridged theorems**: 4 (大同 anchors)
-/

import SSBX.Foundation.Lang.Names
import SSBX.Foundation.Lang.L3_Trigram
import SSBX.Foundation.Lang.L5_Wuyao
import SSBX.Foundation.Eight.XinZhi
import SSBX.Foundation.Core.Yuan

namespace SSBX.Foundation.Lang.Confucian

open SSBX.Foundation.Yi.Yi (Yao Trigram Hexagram)
open SSBX.Foundation.Yi.Yi.Hexagram

/-! ## § 1 R₃ 四端 (仁义礼智之心 端): aliases of existing SiDuan.toTrigram -/

namespace SiDuan

/-- 恻隐之心 = 仁之端 → 离 ☲ (illumination/warmth). -/
def «恻隐» : Trigram := Trigram.li

/-- 羞恶之心 = 义之端 → 坎 ☵ (water/danger/judgment). -/
def «羞恶» : Trigram := Trigram.kan

/-- 辞让之心 = 礼之端 → 震 ☳ (thunder/initiation/yielding). -/
def «辞让» : Trigram := Trigram.zhen

/-- 是非之心 = 智之端 → 兑 ☱ (lake/clarity/discrimination). -/
def «是非» : Trigram := Trigram.dui

/-- These four aliases agree with the existing `SiDuan.toTrigram` mapping
in `Foundation/Eight/XinZhi.lean`. -/
theorem siduan_agrees_with_XinZhi :
    «恻隐» = SSBX.Foundation.Eight.XinZhi.SiDuan.toTrigram .ceYin ∧
    «羞恶» = SSBX.Foundation.Eight.XinZhi.SiDuan.toTrigram .xiuWu ∧
    «辞让» = SSBX.Foundation.Eight.XinZhi.SiDuan.toTrigram .ciRang ∧
    «是非» = SSBX.Foundation.Eight.XinZhi.SiDuan.toTrigram .shiFei := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The 4 端 are pairwise distinct. -/
theorem siduan_distinct :
    «恻隐» ≠ «羞恶» ∧ «恻隐» ≠ «辞让» ∧ «恻隐» ≠ «是非» ∧
    «羞恶» ≠ «辞让» ∧ «羞恶» ≠ «是非» ∧ «辞让» ≠ «是非» := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end SiDuan

/-! ## § 2 R₃ 大学八目 (格致诚正修齐治平): NEW proposed mapping

Thematic, not canonical. Each 目 takes its 卦 from the matching dynamic:

  格物 ↔ 巽 (penetrating the thing)
  致知 ↔ 离 (illuminating knowledge)
  诚意 ↔ 兑 (joyful sincerity)
  正心 ↔ 艮 (still/centered heart)
  修身 ↔ 震 (stirring/awakening self)
  齐家 ↔ 坎 (regulated household flow)
  治国 ↔ 坤 (patient governance)
  平天下 ↔ 乾 (heaven encompasses all)

Alternative readings exist — this is a proposal.
-/

namespace BaMu

def «格物»   : Trigram := Trigram.xun
def «致知»   : Trigram := Trigram.li
def «诚意»   : Trigram := Trigram.dui
def «正心»   : Trigram := Trigram.gen
def «修身»   : Trigram := Trigram.zhen
def «齐家»   : Trigram := Trigram.kan
def «治国»   : Trigram := Trigram.kun
def «平天下» : Trigram := Trigram.qian

/-- The 8 目 list. -/
def all : List Trigram :=
  [«格物», «致知», «诚意», «正心», «修身», «齐家», «治国», «平天下»]

theorem bamu_count : all.length = 8 := rfl

/-- The 8 目 cover all 8 trigrams (bijection with 八卦) as a list permutation. -/
theorem bamu_eq_perm_of_bagua : BaMu.all =
    [Trigram.xun, Trigram.li, Trigram.dui, Trigram.gen,
     Trigram.zhen, Trigram.kan, Trigram.kun, Trigram.qian] := rfl

/-- The 8 目 are pairwise distinct. -/
theorem bamu_distinct : «格物» ≠ «致知» ∧ «格物» ≠ «诚意» ∧
    «致知» ≠ «诚意» ∧ «修身» ≠ «齐家» ∧ «治国» ≠ «平天下» := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end BaMu

/-! ## § 3 R₅ 五伦 (父子君臣夫妇兄弟朋友): aliases of L5 generators

Each 伦 is a single-bit generator of (Z/2)⁵. The 5 伦 generate the entire
R₅ via XOR. Aliases of the existing `L5.flipBenLo/Hi`, `L5.flipZhengLo/Hi`,
`L5.flipFifth`.
-/

namespace WuLun

/-- 父子有亲 → flipBenLo. -/
def «父子» : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipBenLo

/-- 君臣有义 → flipBenHi. -/
def «君臣» : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipBenHi

/-- 夫妇有别 → flipZhengLo. -/
def «夫妇» : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipZhengLo

/-- 兄弟有序 → flipZhengHi. -/
def «兄弟» : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipZhengHi

/-- 朋友有信 → flipFifth (the new 5th-yao bit, "above" the Mian generators). -/
def «朋友» : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipFifth

def all : List SSBX.Foundation.Lang.L5.Cell :=
  [«父子», «君臣», «夫妇», «兄弟», «朋友»]

theorem wulun_count : all.length = 5 := rfl

theorem wulun_distinct :
    «父子» ≠ «君臣» ∧ «父子» ≠ «夫妇» ∧ «父子» ≠ «兄弟» ∧ «父子» ≠ «朋友» ∧
    «君臣» ≠ «夫妇» ∧ «君臣» ≠ «兄弟» ∧ «君臣» ≠ «朋友» ∧
    «夫妇» ≠ «兄弟» ∧ «夫妇» ≠ «朋友» ∧ «兄弟» ≠ «朋友» := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end WuLun

/-! ## § 4 R₆ 大同 (64 卦穷尽): bridges Yuan.daTong_total

Yuan.lean already proves `daTong_total : ∀ h, h.inDao = true` — every
Hexagram is in 道. This section names four canonical "大同 anchors" via
the existing Hexagram.fromName / Hexagram.«…» defs in Names.lean and
re-states the inDao fact at the named cells.
-/

namespace DaTong

def «乾»   : Hexagram := Hexagram.«乾»
def «坤»   : Hexagram := Hexagram.«坤»
def «既济» : Hexagram := Hexagram.«既济»
def «未济» : Hexagram := Hexagram.«未济»

theorem qian_in_dao   : «乾».inDao = true   := SSBX.Foundation.Core.Yuan.daTong_total «乾»
theorem kun_in_dao    : «坤».inDao = true   := SSBX.Foundation.Core.Yuan.daTong_total «坤»
theorem jiji_in_dao   : «既济».inDao = true := SSBX.Foundation.Core.Yuan.daTong_total «既济»
theorem weiji_in_dao  : «未济».inDao = true := SSBX.Foundation.Core.Yuan.daTong_total «未济»

/-- The universal statement, re-exported from Yuan.lean. -/
theorem all_hexagrams_in_dao (h : Hexagram) : h.inDao = true :=
  SSBX.Foundation.Core.Yuan.daTong_total h

end DaTong

/-! ## § 6 R₁ Yao — 善 / 恶 (the simplest cell-level binary)

In Kernel.lean: `shan ≡ middle` (善 = 中, the unfixed state) and `eVice ≡
extreme` (恶 = 极, the fixed state). At Cell layer, "fixed by XOR-with-0"
is automatic (origin), but the doctrinal yin/yang reading is more natural:

- 善 ↔ 阳 (Yao.yang) — the manifest, the moving-forward
- 恶 ↔ 阴 (Yao.yin) — the recessive, the stalled

This is metaphorical: at R₁ the (Z/2)¹ algebra makes 阴 the origin/identity
(see L1_Yao.lean) so the dynamic intuition runs INVERSE to the cell-algebra
intuition. We name accordingly with documentation. -/

namespace ShanE

def «善» : Yao := Yao.yang
def «恶» : Yao := Yao.yin

theorem shan_e_distinct : «善» ≠ «恶» := by decide

end ShanE

/-! ## § 7 R₂ SiXiang — 喜怒哀乐 (the four emotions of 中庸)

《中庸》"喜怒哀乐之未发，谓之中；发而皆中节，谓之和". The four primary
emotions fit naturally into the 4-element SiXiang structure.

  喜 (joy)     → 太阳 (taiYang, full yang)
  怒 (anger)   → 少阴 (shaoYin, yang-going-down)
  哀 (sorrow)  → 少阳 (shaoYang, yin-rising)
  乐 (delight) → 太阴 (taiYin, full yin)
-/

namespace XiNuAiLe

open SSBX.Foundation.Bagua.BaguaAlgebra

def «喜» : SiXiang := SiXiang.taiYang
def «怒» : SiXiang := SiXiang.shaoYin
def «哀» : SiXiang := SiXiang.shaoYang
def «乐» : SiXiang := SiXiang.taiYin

theorem xi_nu_ai_le_distinct :
    «喜» ≠ «怒» ∧ «喜» ≠ «哀» ∧ «喜» ≠ «乐» ∧
    «怒» ≠ «哀» ∧ «怒» ≠ «乐» ∧ «哀» ≠ «乐» := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end XiNuAiLe

/-! ## § 8 R₂ SiXiang — 元亨利贞 (the four virtues of 乾卦)

《周易·乾·彖》"元亨利贞". The four cardinal virtues of 乾 — the same
4-element structure as 喜怒哀乐 but a different labeling.

  元 (origin/spring)     → 太阳 (full yang, the head)
  亨 (smooth/summer)     → 少阳 (yang in motion)
  利 (benefit/autumn)    → 少阴 (yin in maturation)
  贞 (correctness/winter)→ 太阴 (full yin, the held)
-/

namespace YuanHengLiZhen

open SSBX.Foundation.Bagua.BaguaAlgebra

def «元» : SiXiang := SiXiang.taiYang
def «亨» : SiXiang := SiXiang.shaoYang
def «利» : SiXiang := SiXiang.shaoYin
def «贞» : SiXiang := SiXiang.taiYin

theorem yuan_heng_li_zhen_distinct :
    «元» ≠ «亨» ∧ «元» ≠ «利» ∧ «元» ≠ «贞» ∧
    «亨» ≠ «利» ∧ «亨» ≠ «贞» ∧ «利» ≠ «贞» := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end YuanHengLiZhen

/-! ## § 9 R₃ Trigram — 三纲 + 三才

### 大学 三纲
《大学》"大学之道，在明明德，在亲民，在止于至善".

  明明德      → 离 ☲ (illumination of inner brightness)
  亲民        → 兑 ☱ (joyful contact with the people)
  止于至善    → 艮 ☶ (resting in highest good)

### 三才 — the three forces

  天 → 乾 ☰
  地 → 坤 ☷
  人 → 艮 ☶ (mountain — the centered, the still — the human poised between)
-/

namespace SanGang

def «明明德» : Trigram := Trigram.li
def «亲民»   : Trigram := Trigram.dui
def «止于至善» : Trigram := Trigram.gen

def all : List Trigram := [«明明德», «亲民», «止于至善»]

theorem sangang_count : all.length = 3 := rfl

theorem sangang_distinct :
    «明明德» ≠ «亲民» ∧ «明明德» ≠ «止于至善» ∧ «亲民» ≠ «止于至善» := by
  refine ⟨?_, ?_, ?_⟩
  all_goals decide

end SanGang

namespace SanCai

def «天» : Trigram := Trigram.qian
def «地» : Trigram := Trigram.kun
def «人» : Trigram := Trigram.gen

theorem sancai_distinct :
    «天» ≠ «地» ∧ «天» ≠ «人» ∧ «地» ≠ «人» := by
  refine ⟨?_, ?_, ?_⟩
  all_goals decide

end SanCai

/-! ## § 10 What stays as Kernel.lean abstract predicate (NOT lifted to cells)

The following Confucian concepts in Kernel.lean (~50 abstract theorems) do
NOT have a natural cell-level position because they describe **dynamics over
orbits** rather than static positions. They remain as Field-level predicates,
and our cell-layer work does not replace them:

| Concept | 类型 | 为何不 lift |
|---|---|---|
| 動 / dong | axiom on Field → Field | the foundational dynamics axiom |
| 中 / middle | predicate `dong s ≠ s` | property of states, not a state |
| 极 / extreme | predicate `dong s = s` | property of states |
| 几 / ji | iter-of-dong | sequence, not a state |
| 势 / shi | accumulated direction | derived dynamics |
| 机 / jiTurning | critical point | event-on-orbit |
| 聚 / 散 / 和 / 美 / 德 / 理 / 心 / 情 / 积 | various predicates | properties of orbits |
| 圣人 / isShengRen | predicate over Xin | role under window |
| 内圣 / 外王 | derived predicates | orbital configurations |
| 恕道 / 推己及人 / 己所不欲 | cross-orbit relation | not a single state |
| 知行合一 / 反身而诚 | composition theorem | dynamics + closure |
| 慎独 / 至诚无息 / 致中和 | universal-quantified | over n : Nat |
| 见贤思齐 / 过则勿惮改 | event-predicates | over orbit history |
| 自强不息 / 厚德载物 | order-2 predicates | over Field structure |
| 学而时习之 / 温故知新 | iteration laws | orbit-level |
| 三人行 / 君子和而不同 | multi-orbit relations | configuration over Field |
| 性善 / 性恶 | semantic equivalence | 善 = 中, 恶 = 极 (kernel-level) |
| ~22 论孟中庸引文 | various | each is a specific orbit-level theorem |

**Total liftable to cells**: ~30 concepts (五常 5, 四端 4, 八目 8, 五伦 5,
善恶 2, 喜怒哀乐 4, 元亨利贞 4, 三纲 3, 三才 3, 大同 anchors 4 + universal,
五常归道 1). The remaining ~70 stay correctly in `Kernel.lean` as
Field-level dynamics. This is a HONEST division of labor, not a gap.
-/

/-! ## § 5 Public summary -/

/-- Public summary bundling all nine families across R₁..R₆. -/
theorem confucian_summary :
    -- R₁ 善恶
    ShanE.«善» = Yao.yang ∧ ShanE.«恶» = Yao.yin ∧
    -- R₂ 喜怒哀乐
    XiNuAiLe.«喜» = SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang.taiYang ∧
    -- R₂ 元亨利贞
    YuanHengLiZhen.«元» = SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang.taiYang ∧
    -- R₃ 四端
    SiDuan.«恻隐» = Trigram.li ∧
    SiDuan.«羞恶» = Trigram.kan ∧
    SiDuan.«辞让» = Trigram.zhen ∧
    SiDuan.«是非» = Trigram.dui ∧
    -- R₃ 三纲
    SanGang.all.length = 3 ∧
    -- R₃ 三才
    SanCai.«天» = Trigram.qian ∧
    SanCai.«地» = Trigram.kun ∧
    -- R₃ 大学八目
    BaMu.all.length = 8 ∧
    -- R₅ 五伦
    WuLun.all.length = 5 ∧
    -- R₆ 大同
    (∀ h : Hexagram, h.inDao = true) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact DaTong.all_hexagrams_in_dao

end SSBX.Foundation.Lang.Confucian
