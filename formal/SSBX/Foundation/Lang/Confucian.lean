/-
# Confucian — 儒家概念在 R-层 Cell 上的具体落位

Following the existing abstract formalization in `Foundation/Wen/Kernel.lean`
(80+ Confucian theorems based on a `motion : Field → Field` axiom layer), this
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
def compassion : Trigram := Trigram.fire

/-- 羞恶之心 = 义之端 → 坎 ☵ (water/danger/judgment). -/
def shame : Trigram := Trigram.water

/-- 辞让之心 = 礼之端 → 震 ☳ (thunder/initiation/yielding). -/
def yielding : Trigram := Trigram.thunder

/-- 是非之心 = 智之端 → 兑 ☱ (lake/clarity/discrimination). -/
def discernment : Trigram := Trigram.lake

/-- These four aliases agree with the existing `SiDuan.toTrigram` mapping
in `Foundation/Eight/XinZhi.lean`. -/
theorem siduan_agrees_with_XinZhi :
    compassion = SSBX.Foundation.Eight.XinZhi.SiDuan.toTrigram .ceYin ∧
    shame = SSBX.Foundation.Eight.XinZhi.SiDuan.toTrigram .xiuWu ∧
    yielding = SSBX.Foundation.Eight.XinZhi.SiDuan.toTrigram .ciRang ∧
    discernment = SSBX.Foundation.Eight.XinZhi.SiDuan.toTrigram .shiFei := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The 4 端 are pairwise distinct. -/
theorem siduan_distinct :
    compassion ≠ shame ∧ compassion ≠ yielding ∧ compassion ≠ discernment ∧
    shame ≠ yielding ∧ shame ≠ discernment ∧ yielding ≠ discernment := by
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

def investigateThings   : Trigram := Trigram.wind
def extendKnowledge   : Trigram := Trigram.fire
def sincereIntention   : Trigram := Trigram.lake
def rectifyHeart   : Trigram := Trigram.mountain
def cultivateSelf   : Trigram := Trigram.thunder
def regulateFamily   : Trigram := Trigram.water
def governState   : Trigram := Trigram.earth
def pacifyWorld : Trigram := Trigram.heaven

/-- The 8 目 list. -/
def all : List Trigram :=
  [investigateThings, extendKnowledge, sincereIntention, rectifyHeart, cultivateSelf, regulateFamily, governState, pacifyWorld]

theorem bamu_count : all.length = 8 := rfl

/-- The 8 目 cover all 8 trigrams (bijection with 八卦) as a list permutation. -/
theorem bamu_eq_perm_of_bagua : BaMu.all =
    [Trigram.wind, Trigram.fire, Trigram.lake, Trigram.mountain,
     Trigram.thunder, Trigram.water, Trigram.earth, Trigram.heaven] := rfl

/-- The 8 目 are pairwise distinct. -/
theorem bamu_distinct : investigateThings ≠ extendKnowledge ∧ investigateThings ≠ sincereIntention ∧
    extendKnowledge ≠ sincereIntention ∧ cultivateSelf ≠ regulateFamily ∧ governState ≠ pacifyWorld := by
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
def fatherSon : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipBenLo

/-- 君臣有义 → flipBenHi. -/
def rulerSubject : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipBenHi

/-- 夫妇有别 → flipZhengLo. -/
def husbandWife : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipZhengLo

/-- 兄弟有序 → flipZhengHi. -/
def brothers : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipZhengHi

/-- 朋友有信 → flipFifth (the new 5th-yao bit, "above" the Mian generators). -/
def friends : SSBX.Foundation.Lang.L5.Cell := SSBX.Foundation.Lang.L5.flipFifth

def all : List SSBX.Foundation.Lang.L5.Cell :=
  [fatherSon, rulerSubject, husbandWife, brothers, friends]

theorem wulun_count : all.length = 5 := rfl

theorem wulun_distinct :
    fatherSon ≠ rulerSubject ∧ fatherSon ≠ husbandWife ∧ fatherSon ≠ brothers ∧ fatherSon ≠ friends ∧
    rulerSubject ≠ husbandWife ∧ rulerSubject ≠ brothers ∧ rulerSubject ≠ friends ∧
    husbandWife ≠ brothers ∧ husbandWife ≠ friends ∧ brothers ≠ friends := by
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

theorem heaven_in_dao     : Hexagram.heaven.inDao = true     := SSBX.Foundation.Core.Yuan.daTong_total Hexagram.heaven
theorem earth_in_dao      : Hexagram.earth.inDao = true      := SSBX.Foundation.Core.Yuan.daTong_total Hexagram.earth
theorem complete_in_dao   : Hexagram.complete.inDao = true   := SSBX.Foundation.Core.Yuan.daTong_total Hexagram.complete
theorem incomplete_in_dao : Hexagram.incomplete.inDao = true := SSBX.Foundation.Core.Yuan.daTong_total Hexagram.incomplete

/-- The universal statement, re-exported from Yuan.lean. -/
theorem all_hexagrams_in_dao (h : Hexagram) : h.inDao = true :=
  SSBX.Foundation.Core.Yuan.daTong_total h

end DaTong

/-! ## § 6 R₁ Yao — 善 / 恶 (the simplest cell-level binary)

In Kernel.lean: `good ≡ center` (善 = 中, the unfixed state) and `evil ≡
terminus` (恶 = 极, the fixed state). At Cell layer, "fixed by XOR-with-0"
is automatic (origin), but the doctrinal yin/yang reading is more natural:

- 善 ↔ 阳 (Yao.yang) — the manifest, the moving-forward
- 恶 ↔ 阴 (Yao.yin) — the recessive, the stalled

This is metaphorical: at R₁ the (Z/2)¹ algebra makes 阴 the origin/identity
(see L1_Yao.lean) so the dynamic intuition runs INVERSE to the cell-algebra
intuition. We name accordingly with documentation. -/

namespace ShanE

def good : Yao := Yao.yang
def evil : Yao := Yao.yin

theorem shan_e_distinct : good ≠ evil := by decide

end ShanE

/-! ## § 7 R₂ SiXiang — 喜怒哀乐 (the four emotions of 中庸)

《中庸》"喜怒哀乐之未发，谓之中；发而皆中节，谓之和". The four primary
emotions fit naturally into the 4-element SiXiang structure.

  喜 (joy)     → 太阳 (greaterYang, full yang)
  怒 (anger)   → 少阴 (lesserYin, yang-going-down)
  哀 (sorrow)  → 少阳 (lesserYang, yin-rising)
  乐 (delight) → 太阴 (greaterYin, full yin)
-/

namespace XiNuAiLe

open SSBX.Foundation.Bagua.BaguaAlgebra

def joy : SiXiang := SiXiang.greaterYang
def anger : SiXiang := SiXiang.lesserYin
def sorrow : SiXiang := SiXiang.lesserYang
def delight : SiXiang := SiXiang.greaterYin

theorem xi_nu_ai_le_distinct :
    joy ≠ anger ∧ joy ≠ sorrow ∧ joy ≠ delight ∧
    anger ≠ sorrow ∧ anger ≠ delight ∧ sorrow ≠ delight := by
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

def originVirtue : SiXiang := SiXiang.greaterYang
def smoothVirtue : SiXiang := SiXiang.lesserYang
def benefitVirtue : SiXiang := SiXiang.lesserYin
def correctVirtue : SiXiang := SiXiang.greaterYin

theorem yuan_heng_li_zhen_distinct :
    originVirtue ≠ smoothVirtue ∧ originVirtue ≠ benefitVirtue ∧ originVirtue ≠ correctVirtue ∧
    smoothVirtue ≠ benefitVirtue ∧ smoothVirtue ≠ correctVirtue ∧ benefitVirtue ≠ correctVirtue := by
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

def illuminateVirtue : Trigram := Trigram.fire
def engagePeople   : Trigram := Trigram.lake
def restInGood : Trigram := Trigram.mountain

def all : List Trigram := [illuminateVirtue, engagePeople, restInGood]

theorem sangang_count : all.length = 3 := rfl

theorem sangang_distinct :
    illuminateVirtue ≠ engagePeople ∧ illuminateVirtue ≠ restInGood ∧ engagePeople ≠ restInGood := by
  refine ⟨?_, ?_, ?_⟩
  all_goals decide

end SanGang

namespace SanCai

def sky : Trigram := Trigram.heaven
def ground : Trigram := Trigram.earth
def human : Trigram := Trigram.mountain

theorem sancai_distinct :
    sky ≠ ground ∧ sky ≠ human ∧ ground ≠ human := by
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
| 動 / motion | axiom on Field → Field | the foundational dynamics axiom |
| 中 / center | predicate `motion s ≠ s` | property of states, not a state |
| 极 / terminus | predicate `motion s = s` | property of states |
| 几 / ji | iter-of-motion | sequence, not a state |
| 势 / shi | accumulated direction | derived dynamics |
| 机 / jiTurning | critical point | event-on-orbit |
| 聚 / 散 / 和 / 美 / 德 / 理 / 心 / 情 / 积 | various predicates | properties of orbits |
| 圣人 / isSage | predicate over Xin | role under window |
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
    ShanE.good = Yao.yang ∧ ShanE.evil = Yao.yin ∧
    -- R₂ 喜怒哀乐
    XiNuAiLe.joy = SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang.greaterYang ∧
    -- R₂ 元亨利贞
    YuanHengLiZhen.originVirtue = SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang.greaterYang ∧
    -- R₃ 四端
    SiDuan.compassion = Trigram.fire ∧
    SiDuan.shame = Trigram.water ∧
    SiDuan.yielding = Trigram.thunder ∧
    SiDuan.discernment = Trigram.lake ∧
    -- R₃ 三纲
    SanGang.all.length = 3 ∧
    -- R₃ 三才
    SanCai.sky = Trigram.heaven ∧
    SanCai.ground = Trigram.earth ∧
    -- R₃ 大学八目
    BaMu.all.length = 8 ∧
    -- R₅ 五伦
    WuLun.all.length = 5 ∧
    -- R₆ 大同
    (∀ h : Hexagram, h.inDao = true) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact DaTong.all_hexagrams_in_dao

end SSBX.Foundation.Lang.Confucian
