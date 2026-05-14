/-
# HexagramPosition — 六十四卦之位结构续 (Phase 4 · 0-Mathlib finitary)

Companion document: `义理/几何位 · 从元到形.md`

承 `Eight/XingWei.lean`（Trigram 上之 metric/topology）与 `Yi/Yi.lean`
（`atPos`, `isYangPos`, `wellPos`, `isZhongPos`, `yingResponds`, `biAdj`）之上，
本文展开 **六十四卦之位结构** —— 中 / 应 / 比 / 当位 + 承 / 乘 ——
之全 finitary 普查 (survey) 与 几何字元 anchors。

  § 1   wellPosCount: 六位之中"当位"个数普查
  § 2   centralYaos: 中爻之 (二爻, 五爻) 模式分类
  § 3   respondsCount: 应位三对之"应"数普查
  § 4   biCount: 比位五对之"同"数普查
  § 5   承 (chenLi) / 乘 (chengLi): 阴在阳下/阳在阴下 之 local pattern
  § 6   位 之 complement / reverse 不变性
  § 7   几何字元 anchors: 点 / 线 / 面 / 体 之 cardinality
  § 8   posClass: 位 之 partition (non-injective fingerprint)
  § 9   公开摘要

## 道理二分立场
本文全程 0-Mathlib：六十四卦是 finite type，所有"位结构"皆 decidable。
所证之 enumeration/count 命题用 `native_decide` 高效证明。
位 之 几何字元 anchors（点/线/面/体 = 2^k）是 finitary cardinalities，
对应 `XingWei.lean` 之 metric 度量层之离散基底。
-/
import SSBX.Foundation.Eight.XingWei
import SSBX.Foundation.Atlas.Yi.Classical.Core.Yi

namespace SSBX.Foundation.Modern.HexagramPosition

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.Yi.Hexagram

/-! ## § 1 当位 (wellPos) 之普查

  `wellPosCount h` = 六位中"当位"之爻个数（0..6）。
  既济 (complete) 是唯一 wellPosCount = 6 之卦，
  未济 (incomplete) 是唯一 wellPosCount = 0 之卦。
  其余 62 卦分布于 1..5 之间（0/6 极值唯一性是位结构之顶/底）。 -/

/-- 六位之"当位"个数。 -/
def wellPosCount (h : Hexagram) : Nat :=
  (if wellPos h ⟨0, by omega⟩ then 1 else 0)
  + (if wellPos h ⟨1, by omega⟩ then 1 else 0)
  + (if wellPos h ⟨2, by omega⟩ then 1 else 0)
  + (if wellPos h ⟨3, by omega⟩ then 1 else 0)
  + (if wellPos h ⟨4, by omega⟩ then 1 else 0)
  + (if wellPos h ⟨5, by omega⟩ then 1 else 0)

/-- **既济**全当位 → wellPosCount = 6. -/
theorem wellPosCount_jiji : wellPosCount complete = 6 := by native_decide

/-- **未济**全不当位 → wellPosCount = 0. -/
theorem wellPosCount_weiji : wellPosCount incomplete = 0 := by native_decide

/-- **乾**: 三阳位当位（0,2,4）→ count = 3. -/
theorem wellPosCount_qian : wellPosCount heaven = 3 := by native_decide

/-- **坤**: 三阴位当位（1,3,5）→ count = 3. -/
theorem wellPosCount_kun : wellPosCount earth = 3 := by native_decide

/-- 六十四卦中存在 wellPosCount = 4 之卦。 -/
theorem exists_wellPosCount_4 : ∃ h ∈ Hexagram.allHex, wellPosCount h = 4 := by
  native_decide

/-- 六十四卦中存在 wellPosCount = 5 之卦。 -/
theorem exists_wellPosCount_5 : ∃ h ∈ Hexagram.allHex, wellPosCount h = 5 := by
  native_decide

/-- 六十四卦中存在 wellPosCount = 1 之卦。 -/
theorem exists_wellPosCount_1 : ∃ h ∈ Hexagram.allHex, wellPosCount h = 1 := by
  native_decide

/-- 六十四卦中存在 wellPosCount = 2 之卦。 -/
theorem exists_wellPosCount_2 : ∃ h ∈ Hexagram.allHex, wellPosCount h = 2 := by
  native_decide

/-- **count = 6 唯一**：仅既济。
    （在 allHex 列表上对所有 h ≠ complete 验证 wellPosCount h ≠ 6。） -/
theorem wellPosCount_6_unique :
    ∀ h ∈ Hexagram.allHex, wellPosCount h = 6 → h = complete := by
  native_decide

/-- **count = 0 唯一**：仅未济。 -/
theorem wellPosCount_0_unique :
    ∀ h ∈ Hexagram.allHex, wellPosCount h = 0 → h = incomplete := by
  native_decide

/-- 六十四卦中按 wellPosCount 分类，count k 之卦数（k = 0..6）。
    使用 List.countP 之 Bool decidable 形式。 -/
def wellPosCountAt (k : Nat) : Nat :=
  Hexagram.allHex.countP (fun h => decide (wellPosCount h = k))

/-- count = 0 之卦数 = 1（未济唯一）。 -/
theorem wellPosCountAt_0 : wellPosCountAt 0 = 1 := by native_decide

/-- count = 6 之卦数 = 1（既济唯一）。 -/
theorem wellPosCountAt_6 : wellPosCountAt 6 = 1 := by native_decide

/-- count k (k=1..5) 之卦数皆 ≥ 1。 -/
theorem wellPosCountAt_1_pos : wellPosCountAt 1 ≥ 1 := by native_decide
theorem wellPosCountAt_2_pos : wellPosCountAt 2 ≥ 1 := by native_decide
theorem wellPosCountAt_3_pos : wellPosCountAt 3 ≥ 1 := by native_decide
theorem wellPosCountAt_4_pos : wellPosCountAt 4 ≥ 1 := by native_decide
theorem wellPosCountAt_5_pos : wellPosCountAt 5 ≥ 1 := by native_decide

/-- **总和守恒**：Σ_{k=0..6} wellPosCountAt k = 64. -/
theorem wellPosCountAt_total :
    wellPosCountAt 0 + wellPosCountAt 1 + wellPosCountAt 2 + wellPosCountAt 3
    + wellPosCountAt 4 + wellPosCountAt 5 + wellPosCountAt 6 = 64 := by
  native_decide

/-! ## § 2 中爻 (centralYaos) 之模式

  中爻 = (第二爻, 第五爻) — 0-indexed 是 (1, 4)。
  四种可能模式: (yang,yang) / (yang,yin) / (yin,yang) / (yin,yin)。
  既济之中爻 = (yin, yang)，对应"中正而和": 阴在二、阳在五。 -/

/-- 中爻：取出 (二爻, 五爻) — 0-indexed (1, 4)。 -/
def centralYaos (h : Hexagram) : Yao × Yao :=
  (atPos h ⟨1, by omega⟩, atPos h ⟨4, by omega⟩)

/-- **既济**之中爻 = (yin, yang)，恰中正。 -/
theorem centralYaos_jiji : centralYaos complete = (.yin, .yang) := by native_decide

/-- **未济**之中爻 = (yang, yin)，反中正。 -/
theorem centralYaos_weiji : centralYaos incomplete = (.yang, .yin) := by native_decide

/-- **乾**之中爻 = (yang, yang)。 -/
theorem centralYaos_qian : centralYaos heaven = (.yang, .yang) := by native_decide

/-- **坤**之中爻 = (yin, yin)。 -/
theorem centralYaos_kun : centralYaos earth = (.yin, .yin) := by native_decide

/-- 中爻同正（二、五皆当其位）= 二阴五阳: 既济之模式。
    定义为 `centralYaos h = (yin, yang)` 之 Bool 见证。 -/
def centralAligned (h : Hexagram) : Bool :=
  decide (centralYaos h = (Yao.yin, Yao.yang))

/-- 既济中爻对齐。 -/
theorem centralAligned_jiji : centralAligned complete = true := by native_decide

/-- 未济中爻不对齐。 -/
theorem centralAligned_weiji : centralAligned incomplete = false := by native_decide

/-- 中爻按四模式分类之卦数总和 = 64. -/
theorem centralYaos_partition_total :
    Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yang, Yao.yang)))
    + Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yang, Yao.yin)))
    + Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yin, Yao.yang)))
    + Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yin, Yao.yin)))
    = 64 := by native_decide

/-- 每个中爻模式之卦数皆为 16（中爻固定后，其余 4 爻自由 → 2^4）。 -/
theorem centralYaos_each_16_yy :
    Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yang, Yao.yang))) = 16 := by
  native_decide

theorem centralYaos_each_16_yYin :
    Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yang, Yao.yin))) = 16 := by
  native_decide

theorem centralYaos_each_16_YinY :
    Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yin, Yao.yang))) = 16 := by
  native_decide

theorem centralYaos_each_16_YinYin :
    Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yin, Yao.yin))) = 16 := by
  native_decide

/-! ## § 3 应 (yingResponds) 三对之普查

  应位三对：1↔4, 2↔5, 3↔6 (1-indexed)；0-indexed: 0↔3, 1↔4, 2↔5。
  `respondsCount h ∈ {0,1,2,3}` = 三对中"相应"（即两爻不同）之个数。
  既济三对皆应；乾/坤三对皆敌（同性）。 -/

/-- 三对应位中"相应"之个数 (0..3)。 -/
def respondsCount (h : Hexagram) : Nat :=
  (if yingResponds h ⟨0, by omega⟩ then 1 else 0)
  + (if yingResponds h ⟨1, by omega⟩ then 1 else 0)
  + (if yingResponds h ⟨2, by omega⟩ then 1 else 0)

/-- **既济** 三对皆应。 -/
theorem respondsCount_jiji : respondsCount complete = 3 := by native_decide

/-- **未济** 三对皆应（与既济同 — 因二者皆 perfectly alternating）。 -/
theorem respondsCount_weiji : respondsCount incomplete = 3 := by native_decide

/-- **乾** 三对皆敌（六阳 → 各对皆同性 → 不应）。 -/
theorem respondsCount_qian : respondsCount heaven = 0 := by native_decide

/-- **坤** 三对皆敌。 -/
theorem respondsCount_kun : respondsCount earth = 0 := by native_decide

/-- 否 (blocking) 之 respondsCount: 内坤外乾，三对皆相对（阴对阳）→ 全应。 -/
theorem respondsCount_pi : respondsCount blocking = 3 := by native_decide

/-- 泰 (peace) 之 respondsCount = 3（同否，反相）。 -/
theorem respondsCount_tai : respondsCount peace = 3 := by native_decide

/-- 卦数按 respondsCount 分类。 -/
def respondsCountAt (k : Nat) : Nat :=
  Hexagram.allHex.countP (fun h => decide (respondsCount h = k))

/-- 各 k=0..3 之卦数：cardinalities (8, 24, 24, 8)。
    （组合：3 对独立，"应"对数服从二项分布 Bin(3,1/2)，
    乘以剩余对之 2 自由度 = 2^3 / 8 = 1，
    故卦数 = C(3,k) · 2^3 = (8, 24, 24, 8)。） -/
theorem respondsCountAt_0 : respondsCountAt 0 = 8 := by native_decide
theorem respondsCountAt_1 : respondsCountAt 1 = 24 := by native_decide
theorem respondsCountAt_2 : respondsCountAt 2 = 24 := by native_decide
theorem respondsCountAt_3 : respondsCountAt 3 = 8 := by native_decide

/-- **总和守恒**：8 + 24 + 24 + 8 = 64. -/
theorem respondsCountAt_total :
    respondsCountAt 0 + respondsCountAt 1 + respondsCountAt 2 + respondsCountAt 3 = 64 := by
  native_decide

/-! ## § 4 比 (biAdj) 五对之普查

  比位五对：(初, 二), (二, 三), (三, 四), (四, 五), (五, 六)。
  `biCount h ∈ {0,..,5}` = 五对中"同性"（"亲比"）之对数。
  乾/坤皆 5（六爻同性）；既济/未济皆 0（完美交替）。 -/

/-- 邻位之"同性"判定：两爻同 → true。 -/
def biAdjSame (h : Hexagram) (i : Fin 5) : Bool :=
  let p := biAdj h i
  decide (p.1 = p.2)

/-- 邻位"同性"对数 (0..5)。 -/
def biCount (h : Hexagram) : Nat :=
  (if biAdjSame h ⟨0, by omega⟩ then 1 else 0)
  + (if biAdjSame h ⟨1, by omega⟩ then 1 else 0)
  + (if biAdjSame h ⟨2, by omega⟩ then 1 else 0)
  + (if biAdjSame h ⟨3, by omega⟩ then 1 else 0)
  + (if biAdjSame h ⟨4, by omega⟩ then 1 else 0)

/-- **乾** 五对皆同（六阳）。 -/
theorem biCount_qian : biCount heaven = 5 := by native_decide

/-- **坤** 五对皆同（六阴）。 -/
theorem biCount_kun : biCount earth = 5 := by native_decide

/-- **既济** 五对皆异 = 0（完美交替）。 -/
theorem biCount_jiji : biCount complete = 0 := by native_decide

/-- **未济** 五对皆异 = 0. -/
theorem biCount_weiji : biCount incomplete = 0 := by native_decide

/-- 否 (blocking): 内坤 + 外乾，五对中前两对同(yin,yin)、(yin,yin), 中一对异, 后两对同(yang,yang)
    → biCount = 4. -/
theorem biCount_pi : biCount blocking = 4 := by native_decide

/-- 卦数按 biCount 分类。 -/
def biCountAt (k : Nat) : Nat :=
  Hexagram.allHex.countP (fun h => decide (biCount h = k))

/-- biCount = 5 卦数 = 2 (heaven, earth)。 -/
theorem biCountAt_5 : biCountAt 5 = 2 := by native_decide

/-- biCount = 0 卦数 = 2 (complete, incomplete — 完美交替之两种)。 -/
theorem biCountAt_0 : biCountAt 0 = 2 := by native_decide

/-- 总和守恒：Σ_{k=0..5} biCountAt k = 64. -/
theorem biCountAt_total :
    biCountAt 0 + biCountAt 1 + biCountAt 2 + biCountAt 3
    + biCountAt 4 + biCountAt 5 = 64 := by
  native_decide

/-- **biCount = 5 唯一者** 仅 heaven 与 earth。 -/
theorem biCount_5_iff_qian_kun (h : Hexagram) :
    biCount h = 5 ↔ h = heaven ∨ h = earth := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-- **biCount = 0 唯一者** 仅 complete 与 incomplete。 -/
theorem biCount_0_iff_jiji_weiji (h : Hexagram) :
    biCount h = 0 ↔ h = complete ∨ h = incomplete := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-! ## § 5 承 (chenLi) / 乘 (chengLi) 关系

  - 承 (chenLi) at i: i 位是阴, i+1 位是阳 — "阴承阳" (柔承刚于上)
  - 乘 (chengLi) at i: i 位是阳, i+1 位是阴 — "阳被乘" / "阴乘阳"
  这两关系是 yi-jing 之 local "上下亲合" 之 finer 切分（皆 biAdj 异性之子情形）。 -/

/-- 承位（阴在阳之下）。 -/
def chenLi (h : Hexagram) (i : Fin 5) : Bool :=
  let p := biAdj h i
  decide (p.1 = Yao.yin ∧ p.2 = Yao.yang)

/-- 乘位（阳在阴之下，即阴在阳之上"乘"）。 -/
def chengLi (h : Hexagram) (i : Fin 5) : Bool :=
  let p := biAdj h i
  decide (p.1 = Yao.yang ∧ p.2 = Yao.yin)

/-- 承之总数。 -/
def chenCount (h : Hexagram) : Nat :=
  (if chenLi h ⟨0, by omega⟩ then 1 else 0)
  + (if chenLi h ⟨1, by omega⟩ then 1 else 0)
  + (if chenLi h ⟨2, by omega⟩ then 1 else 0)
  + (if chenLi h ⟨3, by omega⟩ then 1 else 0)
  + (if chenLi h ⟨4, by omega⟩ then 1 else 0)

/-- 乘之总数。 -/
def chengCount (h : Hexagram) : Nat :=
  (if chengLi h ⟨0, by omega⟩ then 1 else 0)
  + (if chengLi h ⟨1, by omega⟩ then 1 else 0)
  + (if chengLi h ⟨2, by omega⟩ then 1 else 0)
  + (if chengLi h ⟨3, by omega⟩ then 1 else 0)
  + (if chengLi h ⟨4, by omega⟩ then 1 else 0)

/-- **乾**: 无阴爻 → 无承无乘。 -/
theorem chenCount_qian : chenCount heaven = 0 := by native_decide
theorem chengCount_qian : chengCount heaven = 0 := by native_decide

/-- **坤**: 无阳爻 → 无承无乘。 -/
theorem chenCount_kun : chenCount earth = 0 := by native_decide
theorem chengCount_kun : chengCount earth = 0 := by native_decide

/-- **既济**: ⟨阳,阴,阳,阴,阳,阴⟩；五邻位交替 (yang,yin)/(yin,yang)，
    其中 (yang,yin) 对计 cheng (3 对：位 0,2,4)，
    其中 (yin,yang) 对计 chen (2 对：位 1,3)。 -/
theorem chenCount_jiji : chenCount complete = 2 := by native_decide
theorem chengCount_jiji : chengCount complete = 3 := by native_decide

/-- **未济**: ⟨阴,阳,阴,阳,阴,阳⟩；与既济对偶 (chen=3, cheng=2)。 -/
theorem chenCount_weiji : chenCount incomplete = 3 := by native_decide
theorem chengCount_weiji : chengCount incomplete = 2 := by native_decide

/-- 承 + 乘 = 异性邻位之总数 = 5 - biCount。 -/
theorem chen_cheng_complement (h : Hexagram) :
    chenCount h + chengCount h + biCount h = 5 := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-! ## § 6 位 之 complement / reverse 不变性

  - complement (yao-wise neg): wellPos pattern bit-flip — 阳位之 yang yao → yang 阴位之 yin yao.
    具体：complement 把 wellPos 之 true/false 与每 i 之奇偶按 yao 翻 → wellPosCount 互补：
    `wellPosCount h + wellPosCount h.complement = 6`。
  - reverse (reverse): 位 i ↔ 5-i, isYangPos i ≠ isYangPos (5-i)（因 5-i 之奇偶反），
    所以 reverse 也 flip wellPos pattern at each (reversed) position 之 sense。
  - biCount 不变 under complement (因为"同性"之邻位关系 complement 后仍同性).
  - biCount 不变 under reverse (邻位关系 reversed 但仍邻位)。 -/

/-- **complement flips wellPos**: ∀ i, wellPos h.complement i ≠ wellPos h i. -/
theorem cuo_flips_wellPos (h : Hexagram) (i : Fin 6) :
    wellPos h.complement i = !(wellPos h i) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      (match i with
       | ⟨0, h⟩ => decide +revert
       | ⟨1, h⟩ => decide +revert
       | ⟨2, h⟩ => decide +revert
       | ⟨3, h⟩ => decide +revert
       | ⟨4, h⟩ => decide +revert
       | ⟨5, h⟩ => decide +revert)

/-- **wellPosCount 与 complement 互补**: count h + count (complement h) = 6. -/
theorem wellPosCount_cuo_complement (h : Hexagram) :
    wellPosCount h + wellPosCount h.complement = 6 := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-- **biCount 在 complement 下不变**。 -/
theorem biCount_cuo_invariant (h : Hexagram) :
    biCount h.complement = biCount h := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-- **biCount 在 reverse 下不变**。 -/
theorem biCount_zong_invariant (h : Hexagram) :
    biCount h.reverse = biCount h := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-- **respondsCount 在 complement 下不变**：complement 翻每爻 → 应位每对皆同步翻 → 应/敌不变。 -/
theorem respondsCount_cuo_invariant (h : Hexagram) :
    respondsCount h.complement = respondsCount h := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-- **respondsCount 在 reverse 下不变**：reverse 反位 → 应位三对皆 (i, 5-i) 之配对反置 → 三对集合不变。 -/
theorem respondsCount_zong_invariant (h : Hexagram) :
    respondsCount h.reverse = respondsCount h := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-- **承 / 乘 在 complement 下交换**：complement 把每爻 yang ↔ yin，故 (yin,yang) ↔ (yang,yin)。 -/
theorem chen_cuo_eq_cheng (h : Hexagram) :
    chenCount h.complement = chengCount h := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-- 对偶：cheng complement = chen。 -/
theorem cheng_cuo_eq_chen (h : Hexagram) :
    chengCount h.complement = chenCount h := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
      decide

/-! ## § 7 几何字元 anchors: 点 / 线 / 面 / 体

  对应 `几何位 · 从元到形.md` 之四元字:
  - 点 (dian)  = 单爻 (Yao)         — cardinality 2 = 2^1
  - 线 (xian) = 一段二爻邻接          — cardinality 4 = 2^2
  - 面 (mian) = 三爻 (Trigram)      — cardinality 8 = 2^3
  - 体 (ti)   = 六爻 (Hexagram)    — cardinality 64 = 2^6 -/

/-- **点 之 cardinality = 2**。 -/
theorem dian_card : ([Yao.yang, Yao.yin]).length = 2 := rfl

/-- **线 之 cardinality = 4**：四种二爻配对。 -/
theorem xian_card :
    ([(Yao.yang, Yao.yang), (Yao.yang, Yao.yin),
      (Yao.yin, Yao.yang), (Yao.yin, Yao.yin)] : List (Yao × Yao)).length = 4 := rfl

/-- **面 之 cardinality = 8**：八卦数。 -/
theorem mian_card : Trigram.all.length = 8 := rfl

/-- **体 之 cardinality = 64**：六十四卦。 -/
theorem ti_card : Hexagram.allHex.length = 64 := Hexagram.allHex_count

/-- 几何字元四级 cardinalities = 2^k for k=1,2,3,6。 -/
theorem geom_cardinalities :
    ([Yao.yang, Yao.yin]).length = 2 ^ 1
    ∧ ([(Yao.yang, Yao.yang), (Yao.yang, Yao.yin),
        (Yao.yin, Yao.yang), (Yao.yin, Yao.yin)] : List (Yao × Yao)).length = 2 ^ 2
    ∧ Trigram.all.length = 2 ^ 3
    ∧ Hexagram.allHex.length = 2 ^ 6 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show Hexagram.allHex.length = 64
  exact Hexagram.allHex_count

/-! ## § 8 位 之 partition: posClass fingerprint

  `posClass h := (centralYaos h, respondsCount h, biCount h)`
  此 fingerprint 是 hexagram 之 *non-injective* 之位指纹：
  - 64 卦投影到 fingerprint 空间 ⊆ 4 × 4 × 6 = 96 单元；
  - 但许多卦共享同一 fingerprint（远小于 64 个不同 fingerprint）；
  - 给一对 explicit collision 之见证。 -/

/-- 位之 fingerprint：(中爻模式, 应位数, 比同数)。 -/
def posClass (h : Hexagram) : (Yao × Yao) × Nat × Nat :=
  (centralYaos h, respondsCount h, biCount h)

/-- complete 之 posClass。 -/
theorem posClass_jiji : posClass complete = ((.yin, .yang), 3, 0) := by native_decide

/-- incomplete 之 posClass。 -/
theorem posClass_weiji : posClass incomplete = ((.yang, .yin), 3, 0) := by native_decide

/-- heaven 之 posClass。 -/
theorem posClass_qian : posClass heaven = ((.yang, .yang), 0, 5) := by native_decide

/-- earth 之 posClass。 -/
theorem posClass_kun : posClass earth = ((.yin, .yin), 0, 5) := by native_decide

/-- blocking 之 posClass。 -/
theorem posClass_pi : posClass blocking = ((.yin, .yang), 3, 4) := by native_decide

/-- peace 之 posClass。 -/
theorem posClass_tai : posClass peace = ((.yang, .yin), 3, 4) := by native_decide

/-- 显式构造：两 hexagram 共享同一 posClass.
    取 h1 = ⟨yang, yang, yin, yin, yang, yin⟩，h2 = h1.reverse.
    h1.reverse 与 h1 在 biCount/respondsCount 下不变（§ 6 之 reverse 不变性），
    且 h1 之中爻 = (yang, yang) (二、五皆 yang) 之 reverse 后仍 (yang, yang)，
    故两者 posClass 一致。 -/
def collA : Hexagram := ⟨.yang, .yang, .yin, .yin, .yang, .yin⟩
def collB : Hexagram := ⟨.yin, .yang, .yin, .yin, .yang, .yang⟩

/-- A ≠ B 但 posClass 相等：见证 fingerprint non-injectivity. -/
theorem posClass_collision : collA ≠ collB ∧ posClass collA = posClass collB := by
  refine ⟨?_, ?_⟩
  · intro h; injection h with h1; cases h1
  · native_decide

/-- 位 之 posClass 之像 (image) 之 cardinality 严格小于 64. -/
theorem posClass_not_injective :
    ∃ h₁ h₂ : Hexagram, h₁ ≠ h₂ ∧ posClass h₁ = posClass h₂ :=
  ⟨collA, collB, posClass_collision.1, posClass_collision.2⟩

/-! ## § 9 公开摘要 -/

/-- **HexagramPosition 总摘要**：
    (1) wellPosCount 之 64 卦 enumeration（既济 = 6 唯一/未济 = 0 唯一）
    (2) 中爻四模式各 16 卦
    (3) respondsCount 分布 (8, 24, 24, 8)
    (4) biCount = 5 唯一为 heaven/earth；biCount = 0 唯一为 complete/incomplete
    (5) chenCount + chengCount + biCount = 5
    (6) complement flips wellPos；complement / reverse 保 biCount, respondsCount
    (7) 几何字元 cardinalities = 2^k (k=1,2,3,6)
    (8) posClass non-injective。 -/
theorem hexagram_position_summary :
    -- (1) wellPosCount 极值唯一性
    wellPosCount complete = 6
    ∧ wellPosCount incomplete = 0
    ∧ wellPosCountAt 0 = 1 ∧ wellPosCountAt 6 = 1
    ∧ wellPosCountAt 0 + wellPosCountAt 1 + wellPosCountAt 2 + wellPosCountAt 3
        + wellPosCountAt 4 + wellPosCountAt 5 + wellPosCountAt 6 = 64
    -- (2) 中爻 four modes each 16
    ∧ Hexagram.allHex.countP
        (fun h => decide (centralYaos h = (Yao.yin, Yao.yang))) = 16
    -- (3) respondsCount 分布
    ∧ respondsCountAt 0 = 8 ∧ respondsCountAt 3 = 8
    ∧ respondsCountAt 0 + respondsCountAt 1 + respondsCountAt 2 + respondsCountAt 3 = 64
    -- (4) biCount 极值
    ∧ biCountAt 5 = 2 ∧ biCountAt 0 = 2
    -- (5) chen/cheng + bi = 5
    ∧ (∀ h : Hexagram, chenCount h + chengCount h + biCount h = 5)
    -- (6) complement flips wellPos
    ∧ (∀ h : Hexagram, ∀ i : Fin 6, wellPos h.complement i = !(wellPos h i))
    ∧ (∀ h : Hexagram, biCount h.complement = biCount h)
    ∧ (∀ h : Hexagram, biCount h.reverse = biCount h)
    -- (7) 几何字元 cardinalities
    ∧ Trigram.all.length = 2 ^ 3
    ∧ Hexagram.allHex.length = 2 ^ 6
    -- (8) posClass collision
    ∧ (∃ h₁ h₂ : Hexagram, h₁ ≠ h₂ ∧ posClass h₁ = posClass h₂) :=
  ⟨wellPosCount_jiji, wellPosCount_weiji,
   wellPosCountAt_0, wellPosCountAt_6, wellPosCountAt_total,
   centralYaos_each_16_YinY,
   respondsCountAt_0, respondsCountAt_3, respondsCountAt_total,
   biCountAt_5, biCountAt_0,
   chen_cheng_complement,
   cuo_flips_wellPos, biCount_cuo_invariant, biCount_zong_invariant,
   geom_cardinalities.2.2.1, geom_cardinalities.2.2.2,
   posClass_not_injective⟩

end SSBX.Foundation.Modern.HexagramPosition
