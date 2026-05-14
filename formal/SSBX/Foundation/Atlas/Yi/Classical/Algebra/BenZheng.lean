/-
# BenZheng — 4 本 / 4 征 / Mian / Quadrant

本文件是新本体核心。把 (Z/2)³ 群 reverse-orbit 的 4+4 划分作为 ontology basis。

## 结构

  4 本 (substrates, palindromic) ↔ {heaven, fire, water, earth}
    Ben.thing (物), Ben.motion (動), Ben.interval (間), Ben.event (事)

  4 征 (marks, directional) ↔ {wind, thunder, lake, mountain}
    Zheng.trace (幾), Zheng.momentum (勢), Zheng.pivot (機), Zheng.occasion (時)

  Mian := Ben × Zheng = 16 cells
    label: 動/行/化/流/萌/长/发/续/缘/通/会/系/兆/趋/变/史

  Quadrant := { benBen, benZheng, zhengBen, zhengZheng }
    Hexagram → Quadrant by inner/outer 本征性

## 算子 invariants (全部 native_decide 可证)

  complement  保 isZongFixed (Trigram-level) → 保 quadrant (Hexagram-level)
  middleFlip  保 isZongFixed                 → middleFlipInner / middleFlipOuter 保 quadrant
  motion / topFlip 翻 isZongFixed           → dongInner / topFlipInner / dongOuter / topFlipOuter 跨象限
  reverse: 本本/征征 自闭, 本征↔征本

  interlace fixed points: 1乾, 2坤; interlace 2-cycle: 63既济 ↔ 64未济

## 替代了什么

  - JianOntology.lean 之 OnticRoot / Manifestation / DynamicMark (3-元 placeholder)
  - Core.lean GammaProcess namespace
  - MonadRoot.lean Face 12-枚举（在 P5 改造时）
-/
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.BaguaAlgebra

namespace SSBX.Foundation.Bagua.BenZheng

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 Ben (本) — 4 substrates -/

/-- 4 本: 物 / 動 / 間 / 事. -/
inductive Ben : Type
  | thing     -- 物
  | motion   -- 動
  | interval   -- 間
  | event    -- 事
  deriving Repr, DecidableEq, BEq

namespace Ben

def all : List Ben := [.thing, .motion, .interval, .event]

/-- 本 → trigram 双射: 物→乾, 動→离, 間→坎, 事→坤. -/
def toTrigram : Ben → Trigram
  | .thing   => Trigram.heaven
  | .motion => Trigram.fire
  | .interval => Trigram.water
  | .event  => Trigram.earth

def char : Ben → String
  | .thing   => "物"
  | .motion => "动"
  | .interval => "间"
  | .event  => "事"

def fromChar (s : String) : Option Ben :=
  if s = "物" then some .thing
  else if s = "动" || s = "動" then some .motion
  else if s = "间" || s = "間" then some .interval
  else if s = "事" then some .event
  else none

theorem char_roundtrip (b : Ben) : fromChar b.char = some b := by
  cases b <;> rfl

end Ben

/-! ## § 2 Zheng (征) — 4 marks -/

/-- 4 征: 幾 / 勢 / 機 / 時.

    构造子用 trace / momentum / pivot / occasion 避免与 Ben.event 冲突
    (两个 namespace 都用裸 `event` / `ji` 会产生歧义)。 -/
inductive Zheng : Type
  | trace     -- 幾 (subtle trace)
  | momentum    -- 勢 (momentum)
  | pivot  -- 機 (occasion)
  | occasion     -- 時 (timing)
  deriving Repr, DecidableEq, BEq

namespace Zheng

def all : List Zheng := [.trace, .momentum, .pivot, .occasion]

/-- 征 → trigram 双射: 幾→巽, 勢→震, 機→兑, 時→艮. -/
def toTrigram : Zheng → Trigram
  | .trace    => Trigram.wind
  | .momentum   => Trigram.thunder
  | .pivot => Trigram.lake
  | .occasion    => Trigram.mountain

def char : Zheng → String
  | .trace    => "几"
  | .momentum   => "势"
  | .pivot => "机"
  | .occasion    => "时"

def fromChar (s : String) : Option Zheng :=
  if s = "几" || s = "幾" then some .trace
  else if s = "势" || s = "勢" then some .momentum
  else if s = "机" || s = "機" then some .pivot
  else if s = "时" || s = "時" then some .occasion
  else none

theorem char_roundtrip (z : Zheng) : fromChar z.char = some z := by
  cases z <;> rfl

end Zheng

/-! ## § 3 Trigram 谓词 + 双向映射 -/

end SSBX.Foundation.Bagua.BenZheng

namespace SSBX.Foundation.Yi.Yi.Trigram

open SSBX.Foundation.Yi.Yi

/-- palindromic / reverse-fixed: y1 = y3。这是 4 本组的判别. -/
def isZongFixed (t : Trigram) : Bool :=
  match t.y1, t.y3 with
  | .yang, .yang => true
  | .yin,  .yin  => true
  | _, _         => false

/-- non-palindromic / reverse-mobile: y1 ≠ y3。这是 4 征组的判别. -/
def isZongMobile (t : Trigram) : Bool := !t.isZongFixed

/-- Trigram → 本: 仅 4 个 reverse-fixed trigram 有 Ben. -/
def benOf? (t : Trigram) : Option SSBX.Foundation.Bagua.BenZheng.Ben :=
  if t = heaven then some .thing
  else if t = fire   then some .motion
  else if t = water  then some .interval
  else if t = earth  then some .event
  else none

/-- Trigram → 征: 仅 4 个 reverse-mobile trigram 有 Zheng. -/
def zhengOf? (t : Trigram) : Option SSBX.Foundation.Bagua.BenZheng.Zheng :=
  if t = wind  then some .trace
  else if t = thunder then some .momentum
  else if t = lake  then some .pivot
  else if t = mountain  then some .occasion
  else none

end SSBX.Foundation.Yi.Yi.Trigram

namespace SSBX.Foundation.Bagua.BenZheng

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 4 Trigram-level invariants -/

theorem ben_count :
    (Trigram.all.filter Trigram.isZongFixed).length = 4 := by native_decide

theorem zheng_count :
    (Trigram.all.filter Trigram.isZongMobile).length = 4 := by native_decide

theorem ben_zheng_complement (t : Trigram) :
    t.isZongFixed = !t.isZongMobile := by
  simp [Trigram.isZongMobile]

/-- complement 保 isZongFixed: 全反不破坏 palindrome. -/
theorem complement_preserves_isZongFixed (t : Trigram) :
    t.complement.isZongFixed = t.isZongFixed := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y3 <;> rfl

/-- middleFlip 保 isZongFixed: 翻中爻不动 y1/y3, palindrome 不变. -/
theorem middleFlip_preserves_isZongFixed (t : Trigram) :
    (middleFlip t).isZongFixed = t.isZongFixed := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y3 <;> rfl

/-- motion 翻 isZongFixed: 改 y1 而不动 y3, 翻 palindrome 状态. -/
theorem motion_flips_isZongFixed (t : Trigram) :
    (motion t).isZongFixed = !t.isZongFixed := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y3 <;> rfl

/-- topFlip 翻 isZongFixed: 改 y3 而不动 y1, 翻 palindrome 状态. -/
theorem topFlip_flips_isZongFixed (t : Trigram) :
    (topFlip t).isZongFixed = !t.isZongFixed := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y3 <;> rfl

/-- bijection round-trip: Ben → Trigram → Ben. -/
theorem benOf_toTrigram (b : Ben) :
    Trigram.benOf? b.toTrigram = some b := by
  cases b <;> rfl

/-- bijection round-trip: Zheng → Trigram → Zheng. -/
theorem zhengOf_toTrigram (z : Zheng) :
    Trigram.zhengOf? z.toTrigram = some z := by
  cases z <;> rfl

/-- Ben.toTrigram 总是 reverse-fixed. -/
theorem ben_toTrigram_isZongFixed (b : Ben) :
    b.toTrigram.isZongFixed = true := by
  cases b <;> rfl

/-- Zheng.toTrigram 总是 reverse-mobile. -/
theorem zheng_toTrigram_isZongMobile (z : Zheng) :
    z.toTrigram.isZongMobile = true := by
  cases z <;> rfl

/-! ## § 5 Mian = Ben × Zheng = 16 cells -/

/-- Mian (面)：本 × 征 = 16 cells，取代旧 12-Face 枚举.

    每 cell label 是 16 个单字之一 (動/行/化/流/萌/长/发/续/缘/通/会/系/兆/趋/变/史)，
    出自 docs-next/10_formal_形式/sanben-sijieduan-grid.md 的 16-grid. -/
abbrev Mian : Type := Ben × Zheng

namespace Mian

/-- 16 cells 全枚举. -/
def all : List Mian :=
  Ben.all.flatMap (fun b => Zheng.all.map (fun z => (b, z)))

theorem all_count : Mian.all.length = 16 := by native_decide

/-- 16-cell label: 本×征 = 派生单字. -/
def label : Mian → String
  | (.thing,   .trace)    => "动"  -- 物之微
  | (.thing,   .momentum)   => "行"  -- 物之进
  | (.thing,   .pivot) => "化"  -- 物之转
  | (.thing,   .occasion)    => "流"  -- 物之久
  | (.motion, .trace)    => "萌"  -- 動之微
  | (.motion, .momentum)   => "长"  -- 動之进
  | (.motion, .pivot) => "发"  -- 動之转
  | (.motion, .occasion)    => "续"  -- 動之久
  | (.interval, .trace)    => "缘"  -- 間之微
  | (.interval, .momentum)   => "通"  -- 間之进
  | (.interval, .pivot) => "会"  -- 間之转
  | (.interval, .occasion)    => "系"  -- 間之久
  | (.event,  .trace)    => "兆"  -- 事之微
  | (.event,  .momentum)   => "趋"  -- 事之进
  | (.event,  .pivot) => "变"  -- 事之转
  | (.event,  .occasion)    => "史"  -- 事之久

end Mian

/-! ## § 6 Quadrant — 64 卦 4 象限 -/

inductive Quadrant : Type
  | benBen       -- 本本: inner 本 + outer 本
  | benZheng     -- 本征: inner 本 + outer 征
  | zhengBen     -- 征本: inner 征 + outer 本
  | zhengZheng   -- 征征: inner 征 + outer 征
  deriving Repr, DecidableEq, BEq

namespace Quadrant

def all : List Quadrant := [.benBen, .benZheng, .zhengBen, .zhengZheng]

def label : Quadrant → String
  | .benBen     => "本本"
  | .benZheng   => "本征"
  | .zhengBen   => "征本"
  | .zhengZheng => "征征"

end Quadrant

/-! ## § 7 Hexagram inner/outer + quadrant -/

end SSBX.Foundation.Bagua.BenZheng

namespace SSBX.Foundation.Yi.Yi.Hexagram

open SSBX.Foundation.Yi.Yi

-- innerTrigram / outerTrigram 已在 Yi.lean 定义，此处复用

/-- 64 卦 4 象限: 由 inner/outer 各自 isZongFixed 决定. -/
def quadrant (h : Hexagram) : SSBX.Foundation.Bagua.BenZheng.Quadrant :=
  match h.innerTrigram.isZongFixed, h.outerTrigram.isZongFixed with
  | true,  true  => .benBen
  | true,  false => .benZheng
  | false, true  => .zhengBen
  | false, false => .zhengZheng

/-- 各象限下的卦 list. -/
def quadrantList (q : SSBX.Foundation.Bagua.BenZheng.Quadrant) : List Hexagram :=
  allHex.filter (fun h => h.quadrant = q)

end SSBX.Foundation.Yi.Yi.Hexagram

namespace SSBX.Foundation.Bagua.BenZheng

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 8 Cardinality: 4 象限各 16 -/

theorem benBen_count :
    (Hexagram.quadrantList .benBen).length = 16 := by native_decide

theorem benZheng_count :
    (Hexagram.quadrantList .benZheng).length = 16 := by native_decide

theorem zhengBen_count :
    (Hexagram.quadrantList .zhengBen).length = 16 := by native_decide

theorem zhengZheng_count :
    (Hexagram.quadrantList .zhengZheng).length = 16 := by native_decide

theorem quadrant_partition_complete :
    (Hexagram.quadrantList .benBen).length
      + (Hexagram.quadrantList .benZheng).length
      + (Hexagram.quadrantList .zhengBen).length
      + (Hexagram.quadrantList .zhengZheng).length
    = 64 := by native_decide

/-! ## § 9 Hexagram 算子 invariants -/

/-- complement 保象限 (六爻全反，inner 与 outer 各自 isZongFixed 不变). -/
theorem complement_preserves_quadrant (h : Hexagram) :
    h.complement.quadrant = h.quadrant := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> rfl

/-- reverse 在本本自闭. -/
theorem reverse_preserves_benBen (h : Hexagram) :
    h.quadrant = .benBen → h.reverse.quadrant = .benBen := by
  intro hq
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    revert hq
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> intro hq <;>
      first | rfl | (simp [Hexagram.quadrant, Hexagram.innerTrigram,
                            Hexagram.outerTrigram, Trigram.isZongFixed] at hq)

/-- reverse 把本征送到征本. -/
theorem reverse_swap_benZheng_to_zhengBen (h : Hexagram) :
    h.quadrant = .benZheng → h.reverse.quadrant = .zhengBen := by
  intro hq
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    revert hq
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> intro hq <;>
      first | rfl | (simp [Hexagram.quadrant, Hexagram.innerTrigram,
                            Hexagram.outerTrigram, Trigram.isZongFixed] at hq)

/-- reverse 把征本送到本征. -/
theorem reverse_swap_zhengBen_to_benZheng (h : Hexagram) :
    h.quadrant = .zhengBen → h.reverse.quadrant = .benZheng := by
  intro hq
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    revert hq
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> intro hq <;>
      first | rfl | (simp [Hexagram.quadrant, Hexagram.innerTrigram,
                            Hexagram.outerTrigram, Trigram.isZongFixed] at hq)

/-- reverse 在征征自闭. -/
theorem reverse_preserves_zhengZheng (h : Hexagram) :
    h.quadrant = .zhengZheng → h.reverse.quadrant = .zhengZheng := by
  intro hq
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    revert hq
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> intro hq <;>
      first | rfl | (simp [Hexagram.quadrant, Hexagram.innerTrigram,
                            Hexagram.outerTrigram, Trigram.isZongFixed] at hq)

/-! ## § 10 单爻 flip：中爻 (y2/y5) 保象限，其它跨 -/

/-- middleFlipInner (flip y2) 保象限. -/
theorem huaInner_preserves_quadrant (h : Hexagram) :
    (middleFlipInner h).quadrant = h.quadrant := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> rfl

/-- middleFlipOuter (flip y5) 保象限. -/
theorem huaOuter_preserves_quadrant (h : Hexagram) :
    (middleFlipOuter h).quadrant = h.quadrant := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> rfl

/-- dongInner (flip y1) 跨 inner 本/征. -/
theorem dongInner_flips_inner (h : Hexagram) :
    (dongInner h).innerTrigram.isZongFixed = !h.innerTrigram.isZongFixed := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> rfl

/-- topFlipInner (flip y3) 跨 inner 本/征. -/
theorem bianInner_flips_inner (h : Hexagram) :
    (topFlipInner h).innerTrigram.isZongFixed = !h.innerTrigram.isZongFixed := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> rfl

/-- dongOuter (flip y4) 跨 outer 本/征. -/
theorem dongOuter_flips_outer (h : Hexagram) :
    (dongOuter h).outerTrigram.isZongFixed = !h.outerTrigram.isZongFixed := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y4 <;> cases y6 <;> rfl

/-- topFlipOuter (flip y6) 跨 outer 本/征. -/
theorem bianOuter_flips_outer (h : Hexagram) :
    (topFlipOuter h).outerTrigram.isZongFixed = !h.outerTrigram.isZongFixed := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y4 <;> cases y6 <;> rfl

/-! ## § 11 interlace attractors: {1乾, 2坤, 63既济, 64未济} 全在本本 -/

/-- 乾 interlace-fixed (本本). -/
theorem qian_quadrant : Hexagram.heaven.quadrant = .benBen := by native_decide

/-- 坤 interlace-fixed (本本). -/
theorem kun_quadrant : Hexagram.earth.quadrant = .benBen := by native_decide

/-- 既济在本本. -/
theorem jiji_quadrant : Hexagram.complete.quadrant = .benBen := by native_decide

/-- 未济在本本. -/
theorem weiji_quadrant : Hexagram.incomplete.quadrant = .benBen := by native_decide

/-- 4 个 interlace attractor 都在本本 — 这是 64 卦最深的 substrate. -/
theorem interlace_attractors_in_benBen :
    Hexagram.heaven.quadrant = .benBen
    ∧ Hexagram.earth.quadrant = .benBen
    ∧ Hexagram.complete.quadrant = .benBen
    ∧ Hexagram.incomplete.quadrant = .benBen := by
  exact ⟨qian_quadrant, kun_quadrant, jiji_quadrant, weiji_quadrant⟩

/-- 既济 interlace→ 未济, 未济 interlace→ 既济: 2-cycle in 本本. -/
theorem jiji_hu_eq_weiji : Hexagram.complete.interlace = Hexagram.incomplete := by rfl

theorem weiji_hu_eq_jiji : Hexagram.incomplete.interlace = Hexagram.complete := by rfl

/-! ## § 12 Sanity tests (concrete) -/

-- complement / 错卦 在象限内
example : (Hexagram.complement Hexagram.heaven).quadrant = Hexagram.heaven.quadrant := by
  native_decide

-- 11泰 ↔ 12否 by complement, 都本本
example : (chong Trigram.heaven Trigram.earth).quadrant = .benBen := by native_decide
example : (chong Trigram.earth Trigram.heaven).quadrant = .benBen := by native_decide

-- 34大壮 (内乾外震) 是本征
example : (chong Trigram.heaven Trigram.thunder).quadrant = .benZheng := by native_decide

-- 25无妄 (内震外乾) 是征本
example : (chong Trigram.thunder Trigram.heaven).quadrant = .zhengBen := by native_decide

-- 51震 (内震外震) 是征征
example : (chong Trigram.thunder Trigram.thunder).quadrant = .zhengZheng := by native_decide

end SSBX.Foundation.Bagua.BenZheng
