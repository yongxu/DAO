/-
# BenZheng — 4 本 / 4 征 / Mian / Quadrant

本文件是新本体核心。把 (Z/2)³ 群 zong-orbit 的 4+4 划分作为 ontology basis。

## 结构

  4 本 (substrates, palindromic) ↔ {qian, li, kan, kun}
    Ben.wu (物), Ben.dong (動), Ben.jian (間), Ben.shi (事)

  4 征 (marks, directional) ↔ {xun, zhen, dui, gen}
    Zheng.jiFaint (幾), Zheng.shiForce (勢), Zheng.jiOccasion (機), Zheng.shiTime (時)

  Mian := Ben × Zheng = 16 cells
    label: 動/行/化/流/萌/长/发/续/缘/通/会/系/兆/趋/变/史

  Quadrant := { benBen, benZheng, zhengBen, zhengZheng }
    Hexagram → Quadrant by inner/outer 本征性

## 算子 invariants (全部 native_decide 可证)

  cuo  保 isZongFixed (Trigram-level) → 保 quadrant (Hexagram-level)
  hua  保 isZongFixed                 → huaInner / huaOuter 保 quadrant
  dong / bian 翻 isZongFixed           → dongInner / bianInner / dongOuter / bianOuter 跨象限
  zong: 本本/征征 自闭, 本征↔征本

  hu fixed points: 1乾, 2坤; hu 2-cycle: 63既济 ↔ 64未济
-/
import SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 Ben (本) — 4 substrates -/

namespace SSBX.Foundation.Bagua.BenZheng

/-- 4 本: 物 / 動 / 間 / 事. -/
inductive Ben : Type
  | wu     -- 物
  | dong   -- 動
  | jian   -- 間
  | shi    -- 事
  deriving Repr, DecidableEq, BEq

namespace Ben

open SSBX.Foundation.Yi.Yi

def all : List Ben := [.wu, .dong, .jian, .shi]

/-- 本 → trigram 双射: 物→乾, 動→离, 間→坎, 事→坤. -/
def toTrigram : Ben → Trigram
  | .wu   => Trigram.qian
  | .dong => Trigram.li
  | .jian => Trigram.kan
  | .shi  => Trigram.kun

def char : Ben → String
  | .wu   => "物"
  | .dong => "动"
  | .jian => "间"
  | .shi  => "事"

def fromChar (s : String) : Option Ben :=
  if s = "物" then some .wu
  else if s = "动" || s = "動" then some .dong
  else if s = "间" || s = "間" then some .jian
  else if s = "事" then some .shi
  else none

theorem char_roundtrip (b : Ben) : fromChar b.char = some b := by
  cases b <;> rfl

end Ben

/-! ## § 2 Zheng (征) — 4 marks -/

/-- 4 征: 幾 / 勢 / 機 / 時.

    构造子用 jiFaint / shiForce / jiOccasion / shiTime 避免与 Ben.shi 冲突. -/
inductive Zheng : Type
  | jiFaint     -- 幾 (subtle trace)
  | shiForce    -- 勢 (momentum)
  | jiOccasion  -- 機 (occasion)
  | shiTime     -- 時 (timing)
  deriving Repr, DecidableEq, BEq

namespace Zheng

open SSBX.Foundation.Yi.Yi

def all : List Zheng := [.jiFaint, .shiForce, .jiOccasion, .shiTime]

/-- 征 → trigram 双射: 幾→巽, 勢→震, 機→兑, 時→艮. -/
def toTrigram : Zheng → Trigram
  | .jiFaint    => Trigram.xun
  | .shiForce   => Trigram.zhen
  | .jiOccasion => Trigram.dui
  | .shiTime    => Trigram.gen

def char : Zheng → String
  | .jiFaint    => "几"
  | .shiForce   => "势"
  | .jiOccasion => "机"
  | .shiTime    => "时"

def fromChar (s : String) : Option Zheng :=
  if s = "几" || s = "幾" then some .jiFaint
  else if s = "势" || s = "勢" then some .shiForce
  else if s = "机" || s = "機" then some .jiOccasion
  else if s = "时" || s = "時" then some .shiTime
  else none

theorem char_roundtrip (z : Zheng) : fromChar z.char = some z := by
  cases z <;> rfl

end Zheng

/-! ## § 3 Mian = Ben × Zheng = 16 cells -/

/-- Mian (面)：本 × 征 = 16 cells，取代旧 12-Face 枚举. -/
abbrev Mian : Type := Ben × Zheng

namespace Mian

def all : List Mian :=
  Ben.all.flatMap (fun b => Zheng.all.map (fun z => (b, z)))

theorem all_count : all.length = 16 := by native_decide

/-- 16-cell label: 派生单字. -/
def label : Mian → String
  | (.wu,   .jiFaint)    => "动"  -- 物之微
  | (.wu,   .shiForce)   => "行"  -- 物之进
  | (.wu,   .jiOccasion) => "化"  -- 物之转
  | (.wu,   .shiTime)    => "流"  -- 物之久
  | (.dong, .jiFaint)    => "萌"  -- 動之微
  | (.dong, .shiForce)   => "长"  -- 動之进
  | (.dong, .jiOccasion) => "发"  -- 動之转
  | (.dong, .shiTime)    => "续"  -- 動之久
  | (.jian, .jiFaint)    => "缘"  -- 間之微
  | (.jian, .shiForce)   => "通"  -- 間之进
  | (.jian, .jiOccasion) => "会"  -- 間之转
  | (.jian, .shiTime)    => "系"  -- 間之久
  | (.shi,  .jiFaint)    => "兆"  -- 事之微
  | (.shi,  .shiForce)   => "趋"  -- 事之进
  | (.shi,  .jiOccasion) => "变"  -- 事之转
  | (.shi,  .shiTime)    => "史"  -- 事之久

end Mian

/-! ## § 4 Quadrant — 64 卦 4 象限 -/

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

end SSBX.Foundation.Bagua.BenZheng

/-! ## § 5 Trigram extensions: isZongFixed / benOf? / zhengOf? -/

namespace SSBX.Foundation.Yi.Yi.Trigram

open SSBX.Foundation.Bagua.BenZheng

/-- palindromic / zong-fixed: y1 = y3。这是 4 本组的判别. -/
def isZongFixed (t : Trigram) : Bool :=
  match t.y1, t.y3 with
  | .yang, .yang => true
  | .yin,  .yin  => true
  | _, _         => false

/-- non-palindromic / zong-mobile: y1 ≠ y3。这是 4 征组的判别. -/
def isZongMobile (t : Trigram) : Bool := !t.isZongFixed

/-- Trigram → 本: 仅 4 个 zong-fixed trigram 有 Ben. -/
def benOf? (t : Trigram) : Option Ben :=
  if t = qian then some .wu
  else if t = li   then some .dong
  else if t = kan  then some .jian
  else if t = kun  then some .shi
  else none

/-- Trigram → 征: 仅 4 个 zong-mobile trigram 有 Zheng. -/
def zhengOf? (t : Trigram) : Option Zheng :=
  if t = xun  then some .jiFaint
  else if t = zhen then some .shiForce
  else if t = dui  then some .jiOccasion
  else if t = gen  then some .shiTime
  else none

end SSBX.Foundation.Yi.Yi.Trigram

/-! ## § 6 Trigram-level invariants -/

namespace SSBX.Foundation.Bagua.BenZheng

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

theorem ben_count :
    (Trigram.all.filter Trigram.isZongFixed).length = 4 := by native_decide

theorem zheng_count :
    (Trigram.all.filter Trigram.isZongMobile).length = 4 := by native_decide

theorem ben_zheng_complement (t : Trigram) :
    t.isZongFixed = !t.isZongMobile := by
  simp [Trigram.isZongMobile]

/-- cuo 保 isZongFixed: 全反不破坏 palindrome. -/
theorem cuo_preserves_isZongFixed (t : Trigram) :
    t.cuo.isZongFixed = t.isZongFixed := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y3 <;> rfl

/-- hua 保 isZongFixed: 翻中爻不动 y1/y3, palindrome 不变. -/
theorem hua_preserves_isZongFixed (t : Trigram) :
    (hua t).isZongFixed = t.isZongFixed := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y3 <;> rfl

/-- dong 翻 isZongFixed: 改 y1 而不动 y3, 翻 palindrome 状态. -/
theorem dong_flips_isZongFixed (t : Trigram) :
    (dong t).isZongFixed = !t.isZongFixed := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y3 <;> rfl

/-- bian 翻 isZongFixed: 改 y3 而不动 y1, 翻 palindrome 状态. -/
theorem bian_flips_isZongFixed (t : Trigram) :
    (bian t).isZongFixed = !t.isZongFixed := by
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

/-- Ben.toTrigram 总是 zong-fixed. -/
theorem ben_toTrigram_isZongFixed (b : Ben) :
    b.toTrigram.isZongFixed = true := by
  cases b <;> rfl

/-- Zheng.toTrigram 总是 zong-mobile. -/
theorem zheng_toTrigram_isZongMobile (z : Zheng) :
    z.toTrigram.isZongMobile = true := by
  cases z <;> rfl

end SSBX.Foundation.Bagua.BenZheng

/-! ## § 7 Hexagram extensions: inner/outer + quadrant -/

namespace SSBX.Foundation.Yi.Yi.Hexagram

open SSBX.Foundation.Bagua.BenZheng

/-- 64 卦 4 象限。inner/outer trigram 已在 Yi.lean 定义. -/
def quadrant (h : Hexagram) : Quadrant :=
  match h.innerTrigram.isZongFixed, h.outerTrigram.isZongFixed with
  | true,  true  => .benBen
  | true,  false => .benZheng
  | false, true  => .zhengBen
  | false, false => .zhengZheng

/-- 各象限下的卦 list. -/
def quadrantList (q : Quadrant) : List Hexagram :=
  allHex.filter (fun h => h.quadrant = q)

end SSBX.Foundation.Yi.Yi.Hexagram

/-! ## § 8 Cardinality + Hexagram-level invariants -/

namespace SSBX.Foundation.Bagua.BenZheng

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

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

/-- cuo 保象限. -/
theorem cuo_preserves_quadrant (h : Hexagram) :
    h.cuo.quadrant = h.quadrant := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> rfl

/-! ### zong 象限行为：本本/征征 自闭，本征 ↔ 征本 -/

/-- 统一 zong 象限定理：四个 quadrant 的行为表. -/
theorem zong_quadrant (h : Hexagram) :
    h.zong.quadrant =
      match h.quadrant with
      | .benBen     => .benBen
      | .benZheng   => .zhengBen
      | .zhengBen   => .benZheng
      | .zhengZheng => .zhengZheng := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> rfl

theorem zong_preserves_benBen (h : Hexagram) :
    h.quadrant = .benBen → h.zong.quadrant = .benBen := by
  intro hq; rw [zong_quadrant, hq]

theorem zong_swap_benZheng_to_zhengBen (h : Hexagram) :
    h.quadrant = .benZheng → h.zong.quadrant = .zhengBen := by
  intro hq; rw [zong_quadrant, hq]

theorem zong_swap_zhengBen_to_benZheng (h : Hexagram) :
    h.quadrant = .zhengBen → h.zong.quadrant = .benZheng := by
  intro hq; rw [zong_quadrant, hq]

theorem zong_preserves_zhengZheng (h : Hexagram) :
    h.quadrant = .zhengZheng → h.zong.quadrant = .zhengZheng := by
  intro hq; rw [zong_quadrant, hq]

/-! ### 单爻 flip：中爻 (y2/y5) 保象限，其它跨 -/

/-- huaInner (flip y2) 保象限. -/
theorem huaInner_preserves_quadrant (h : Hexagram) :
    (huaInner h).quadrant = h.quadrant := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> rfl

/-- huaOuter (flip y5) 保象限. -/
theorem huaOuter_preserves_quadrant (h : Hexagram) :
    (huaOuter h).quadrant = h.quadrant := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> cases y4 <;> cases y6 <;> rfl

/-- dongInner (flip y1) 跨 inner 本/征. -/
theorem dongInner_flips_inner (h : Hexagram) :
    (dongInner h).innerTrigram.isZongFixed = !h.innerTrigram.isZongFixed := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> rfl

/-- bianInner (flip y3) 跨 inner 本/征. -/
theorem bianInner_flips_inner (h : Hexagram) :
    (bianInner h).innerTrigram.isZongFixed = !h.innerTrigram.isZongFixed := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y3 <;> rfl

/-- dongOuter (flip y4) 跨 outer 本/征. -/
theorem dongOuter_flips_outer (h : Hexagram) :
    (dongOuter h).outerTrigram.isZongFixed = !h.outerTrigram.isZongFixed := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y4 <;> cases y6 <;> rfl

/-- bianOuter (flip y6) 跨 outer 本/征. -/
theorem bianOuter_flips_outer (h : Hexagram) :
    (bianOuter h).outerTrigram.isZongFixed = !h.outerTrigram.isZongFixed := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y4 <;> cases y6 <;> rfl

/-! ## § 9 hu attractors: {1乾, 2坤, 63既济, 64未济} 全在本本 -/

theorem qian_quadrant : Hexagram.qian.quadrant = .benBen := by native_decide

theorem kun_quadrant : Hexagram.kun.quadrant = .benBen := by native_decide

theorem jiji_quadrant : Hexagram.jiji.quadrant = .benBen := by native_decide

theorem weiji_quadrant : Hexagram.weiji.quadrant = .benBen := by native_decide

/-- 4 个 hu attractor 都在本本. -/
theorem hu_attractors_in_benBen :
    Hexagram.qian.quadrant = .benBen
    ∧ Hexagram.kun.quadrant = .benBen
    ∧ Hexagram.jiji.quadrant = .benBen
    ∧ Hexagram.weiji.quadrant = .benBen :=
  ⟨qian_quadrant, kun_quadrant, jiji_quadrant, weiji_quadrant⟩

/-- 既济 hu→ 未济, 2-cycle in 本本. -/
theorem jiji_hu_eq_weiji : Hexagram.jiji.hu = Hexagram.weiji := by rfl

theorem weiji_hu_eq_jiji : Hexagram.weiji.hu = Hexagram.jiji := by rfl

/-! ## § 10 Sanity tests (concrete 64 卦 抽样) -/

example : Hexagram.qian.cuo.quadrant = Hexagram.qian.quadrant := by native_decide

-- 11泰 (内乾外坤): 本本
example : (Hexagram.oplus Trigram.qian Trigram.kun).quadrant = .benBen := by native_decide

-- 12否 (内坤外乾): 本本
example : (Hexagram.oplus Trigram.kun Trigram.qian).quadrant = .benBen := by native_decide

-- 34大壮 (内乾外震): 本征
example : (Hexagram.oplus Trigram.qian Trigram.zhen).quadrant = .benZheng := by native_decide

-- 25无妄 (内震外乾): 征本
example : (Hexagram.oplus Trigram.zhen Trigram.qian).quadrant = .zhengBen := by native_decide

-- 51震 (内震外震): 征征
example : (Hexagram.oplus Trigram.zhen Trigram.zhen).quadrant = .zhengZheng := by native_decide

end SSBX.Foundation.Bagua.BenZheng
