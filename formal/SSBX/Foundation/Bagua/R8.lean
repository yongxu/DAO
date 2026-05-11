/-
# R8 — R₈ = (Z/2)⁸ = 256 格 + V₄ Shi + 序卦

(strict-uniform R₀..R₈ 编号 per yi-RO-hierarchy-v2.md; 旧 v1 中称 R₆)

R₈ = R₆ × Shi = (Z/2)⁶ × V₄ = 256 cells.

Shi 是 V₄ Klein 四群 = {道, 已, 今, 未}（**绝非 Z/3 cyclic**）：
  - 道 = (0, 0) = V₄ 单位元 = 跨时空永真 anchor
  - 已 = (1, 0) = parity-like (P)：过去固定，无未来
  - 未 = (0, 1) = time-reversal-like (T)：未来开放，无过去
  - 今 = (1, 1) = PT 复合：过去与未来交汇 = 现在

详见 docs-next/10_formal_形式/yi-calculus-theorem.md Theorems H–J。

之前版本 (Cell192.lean) 把 Shi 编为 Z/3 cyclic 是结构错误，破坏了 R-hierarchy
的 (Z/2)ⁿ 自相似闭合。本文件是 R5 真闭合版。

Builds on Yi.lean and BaguaAlgebra.lean.

## Phases
  § 1   Shi (时态) inductive + V₄ Klein 群结构 (complement / reverse / complementReverse involution)
  § 2   R8 = Hexagram × Shi + cardinality 256
  § 3   R8 lateral operators (合 hex flips with 时态)
  § 4   xuGua (序卦传 King Wen order) as List Hexagram of length 64
  § 5   xuGua next / index / completeness theorems
-/
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Bagua.R7

namespace SSBX.Foundation.Bagua.R8

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.Yi.Trigram
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R7 (YinBit)

/-! ## § 1 Shi (时态) — V₄ Klein 四群 = {道, 已, 今, 未}

  Shi 由 R5/R6 双 axis 之 (因, 果) ∈ Bool² emerge（详 yi-RO-hierarchy.md 第六部分）：
  - YinBit (因, R5 atom) = past trace bit
  - GuoBit (果, R6 atom) = future projection bit
  - Shi = YinBit × GuoBit ≅ V₄

  **命名 caveats (provisional)**: 因/果 / 印/投 暂用，备选 印/投 (Husserl) /
  始/终 (Yi-native) / 持/期 (现象学) — 详 yi-calculus-theorem.md §16. -/

/-- R6 atom: 果 (guǒ) — future-projection bit. Provisional naming.

    `YinBit` is imported from `SSBX.Foundation.Bagua.R7` (R₇ origin):
    R7 introduces 因 first, then R8 = R7 × GuoBit pairs it
    with 果 to form Shi V₄. -/
abbrev GuoBit : Type := Bool

/-- 时态: V₄ 四态 道 / 已 / 今 / 未. 同构于 (YinBit, GuoBit) ∈ Bool².

    - 道 = (0, 0) — 永真，跨时空，V₄ 单位元
    - 已 = (1, 0) — 过去封闭 (有因, 无果)
    - 未 = (0, 1) — 未来开放 (无因, 有果)
    - 今 = (1, 1) — PT 交汇 (因果俱在)

    Now an `abbrev` of `YinBit × GuoBit` = `Bool × Bool`. The 4 named tags
    `dao / ji / jin / wei` are `@[match_pattern]` defs so existing
    pattern-matches `| .dao => ...` continue to work. -/
abbrev Shi : Type := YinBit × GuoBit

namespace Shi

@[match_pattern] def dao : Shi := (false, false)
@[match_pattern] def ji  : Shi := (true,  false)
@[match_pattern] def jin : Shi := (true,  true)
@[match_pattern] def wei : Shi := (false, true)

/-- 全部 4 个时态. -/
def all : List Shi := [dao, ji, jin, wei]

theorem all_length : all.length = 4 := rfl

/-- V₄ complement (P-like, 翻 past-trace 轴): 道↔已, 未↔今. -/
def complement : Shi → Shi
  | .dao => .ji
  | .ji  => .dao
  | .jin => .wei
  | .wei => .jin

/-- V₄ reverse (T-like, 翻 future-projection 轴): 道↔未, 已↔今. -/
def reverse : Shi → Shi
  | .dao => .wei
  | .ji  => .jin
  | .jin => .ji
  | .wei => .dao

/-- V₄ complementReverse (= PT, 双轴翻): 道↔今, 已↔未. -/
def complementReverse : Shi → Shi
  | .dao => .jin
  | .ji  => .wei
  | .jin => .dao
  | .wei => .ji

theorem complement_involutive (s : Shi) : complement (complement s) = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl
theorem reverse_involutive (s : Shi) : reverse (reverse s) = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl
theorem cuoZong_cuoZong (s : Shi) : complementReverse (complementReverse s) = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

/-- complement 与 reverse 交换（V₄ Abelian）. -/
theorem complement_reverse_comm (s : Shi) : complement (reverse s) = reverse (complement s) := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

/-- complementReverse = complement ∘ reverse （V₄ 复合）. -/
theorem cuoZong_eq_compose (s : Shi) : complementReverse s = complement (reverse s) := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

/-! ### Shi ↔ (YinBit × GuoBit) ≅ V₄ Klein 双射

  Shi 之 V₄ 结构通过 (因, 果) bit 显式暴露，对应 yi-RO-hierarchy.md 第六部分:
  Shi V₄ = R5⊗R6 emergence。 -/

/-- Shi → (因, 果) ∈ Bool² 双射. Identity since `Shi := YinBit × GuoBit`. -/
def toYinGuo (s : Shi) : YinBit × GuoBit := s

/-- (因, 果) ∈ Bool² → Shi 反向双射. Identity. -/
def ofYinGuo (yg : YinBit × GuoBit) : Shi := yg

/-- 双射 left: Shi → (因,果) → Shi = id. -/
theorem ofYinGuo_toYinGuo (s : Shi) : ofYinGuo (toYinGuo s) = s := rfl

/-- 双射 right: (因,果) → Shi → (因,果) = id. -/
theorem toYinGuo_ofYinGuo (yg : YinBit × GuoBit) : toYinGuo (ofYinGuo yg) = yg := rfl

/-! ### 印 (yìn) / 投 (tóu) — O5/O6 atomic 算子

  印 = toggle YinBit (R5 atom 算子)，投 = toggle GuoBit (R6 atom 算子)。
  二者皆为 Z/2 involution. 详 yi-RO-hierarchy.md §5/§6.

  **命名 provisional**: 印/投 vs 因/果（state attributes）的二元对偶；
  备选 印/望、持/期等 — 详 yi-calculus-theorem.md §16. -/

/-- 印 (yìn): toggle YinBit (因 axis). 等价于 Shi.complement. -/
def imprint (s : Shi) : Shi := s.complement

/-- 投 (tóu): toggle GuoBit (果 axis). 等价于 Shi.reverse. -/
def project (s : Shi) : Shi := s.reverse

theorem imprint_imprint (s : Shi) : imprint (imprint s) = s := complement_involutive s
theorem project_project (s : Shi) : project (project s) = s := reverse_involutive s
theorem imprint_project_comm (s : Shi) : imprint (project s) = project (imprint s) := complement_reverse_comm s

/-- 印 ∘ 投 = complementReverse = V₄ central element. -/
theorem imprint_project_eq_complementReverse (s : Shi) : imprint (project s) = complementReverse s := by
  unfold imprint project
  exact (cuoZong_eq_compose s).symm

end Shi

/-! ## § 2 R8 — 256 格 -/

/-- 256 格 = 64 卦 × 4 时态 = (Z/2)⁸. -/
abbrev R8 : Type := Hexagram × Shi

namespace R8

/-- All 256 cells. -/
def all : List R8 :=
  Hexagram.allHex.flatMap fun h => Shi.all.map fun s => (h, s)

/-- |R8| = 256 strictly. -/
theorem all_length : all.length = 256 := by native_decide

/-- The 256-cell enumeration has no duplicate cells. -/
theorem all_nodup : all.Nodup := by native_decide

/-- Every R8 is in `all` (exhaustion). -/
theorem mem_all (c : R8) : c ∈ all := by
  rcases c with ⟨h, s⟩
  unfold all
  refine List.mem_flatMap.mpr ⟨h, hexagram_mem_allHex h, ?_⟩
  exact List.mem_map.mpr ⟨s, by
    rcases s with ⟨y, g⟩; cases y <;> cases g <;> simp [Shi.all, Shi.dao, Shi.ji, Shi.jin, Shi.wei], rfl⟩

/-- Node counts for the root-to-256 prefix tree:
    root → 6 yao bit levels → 8th bit (Shi past) → 9th bit (Shi future) = 256.
    Pure (Z/2)⁸ binary tree, 9 levels. -/
def rootTo256TreeLevelCounts : List Nat :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256]

theorem rootTo256TreeLevelCounts_sum :
    rootTo256TreeLevelCounts.sum = 511 := by
  native_decide

theorem rootTo256TreeEdgeCount :
    2 + 4 + 8 + 16 + 32 + 64 + 128 + 256 = 510 := by
  native_decide

end R8

/-! ## § 3 R8 lateral operators — combined hex flips + 时态 V₄ -/

namespace R8

/-- 时态 complement on R8 (P-like, 保 hex). -/
def shiCuo (c : R8) : R8 := (c.1, c.2.complement)
/-- 时态 reverse on R8 (T-like, 保 hex). -/
def shiZong (c : R8) : R8 := (c.1, c.2.reverse)
/-- 时态 complementReverse on R8 (PT, 保 hex). -/
def shiCuoZong (c : R8) : R8 := (c.1, c.2.complementReverse)

theorem shiCuo_shiCuo (c : R8) : shiCuo (shiCuo c) = c := by
  rcases c with ⟨h, s⟩; simp [shiCuo, Shi.complement_involutive]

theorem shiZong_shiZong (c : R8) : shiZong (shiZong c) = c := by
  rcases c with ⟨h, s⟩; simp [shiZong, Shi.reverse_involutive]

theorem shiCuoZong_shiCuoZong (c : R8) : shiCuoZong (shiCuoZong c) = c := by
  rcases c with ⟨h, s⟩; simp [shiCuoZong, Shi.cuoZong_cuoZong]

/-- Hexagram 错 lifted to R8 (preserves 时态). -/
def hexCuo (c : R8) : R8 := (Hexagram.complement c.1, c.2)
/-- Hexagram 综 lifted. -/
def hexZong (c : R8) : R8 := (Hexagram.reverse c.1, c.2)
/-- Hexagram 互 lifted. -/
def hexHu (c : R8) : R8 := (Hexagram.interlace c.1, c.2)

/-- 6 single yao flips lifted. -/
def flip1 (c : R8) : R8 := (dongInner c.1, c.2)
def flip2 (c : R8) : R8 := (middleFlipInner c.1, c.2)
def flip3 (c : R8) : R8 := (topFlipInner c.1, c.2)
def flip4 (c : R8) : R8 := (dongOuter c.1, c.2)
def flip5 (c : R8) : R8 := (middleFlipOuter c.1, c.2)
def flip6 (c : R8) : R8 := (topFlipOuter c.1, c.2)

theorem hexCuo_hexCuo (c : R8) : hexCuo (hexCuo c) = c := by
  rcases c with ⟨h, s⟩
  simp [hexCuo, Hexagram.complement_involutive]

theorem hexZong_hexZong (c : R8) : hexZong (hexZong c) = c := by
  rcases c with ⟨h, s⟩
  simp [hexZong, Hexagram.reverse_involutive]

theorem hexCuo_hexZong_comm (c : R8) :
    hexCuo (hexZong c) = hexZong (hexCuo c) := by
  rcases c with ⟨h, s⟩
  simp [hexCuo, hexZong, Hexagram.complement_reverse_comm]

theorem hexCuoZong_hexCuoZong (c : R8) :
    hexCuo (hexZong (hexCuo (hexZong c))) = c := by
  rw [hexCuo_hexZong_comm, hexCuo_hexCuo, hexZong_hexZong]

theorem flip1_flip1 (c : R8) : flip1 (flip1 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip1, dongInner_dongInner]

theorem flip2_flip2 (c : R8) : flip2 (flip2 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip2, huaInner_huaInner]

theorem flip3_flip3 (c : R8) : flip3 (flip3 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip3, bianInner_bianInner]

theorem flip4_flip4 (c : R8) : flip4 (flip4 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip4, dongOuter_dongOuter]

theorem flip5_flip5 (c : R8) : flip5 (flip5 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip5, huaOuter_huaOuter]

theorem flip6_flip6 (c : R8) : flip6 (flip6 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip6, bianOuter_bianOuter]

/-- hex 与 shi V₄ 算子之间互相交换（tensor product 结构）. -/
theorem hexCuo_shiCuo_comm (c : R8) : hexCuo (shiCuo c) = shiCuo (hexCuo c) := by
  rcases c with ⟨h, s⟩; rfl

theorem hexZong_shiZong_comm (c : R8) : hexZong (shiZong c) = shiZong (hexZong c) := by
  rcases c with ⟨h, s⟩; rfl

end R8

/-! ## § 4 序卦 (King Wen Order) — 64 hexagrams in canonical sequence -/

/-- The 64 hexagrams in the canonical 序卦传 (King Wen) order. -/
def xuGua : List Hexagram := [
  ⟨.yang, .yang, .yang, .yang, .yang, .yang⟩,  --  1. 乾    ䷀
  ⟨.yin,  .yin,  .yin,  .yin,  .yin,  .yin⟩,   --  2. 坤    ䷁
  ⟨.yang, .yin,  .yin,  .yin,  .yang, .yin⟩,   --  3. 屯    ䷂
  ⟨.yin,  .yang, .yin,  .yin,  .yin,  .yang⟩,  --  4. 蒙    ䷃
  ⟨.yang, .yang, .yang, .yin,  .yang, .yin⟩,   --  5. 需    ䷄
  ⟨.yin,  .yang, .yin,  .yang, .yang, .yang⟩,  --  6. 讼    ䷅
  ⟨.yin,  .yang, .yin,  .yin,  .yin,  .yin⟩,   --  7. 师    ䷆
  ⟨.yin,  .yin,  .yin,  .yin,  .yang, .yin⟩,   --  8. 比    ䷇
  ⟨.yang, .yang, .yang, .yin,  .yang, .yang⟩,  --  9. 小畜  ䷈
  ⟨.yang, .yang, .yin,  .yang, .yang, .yang⟩,  -- 10. 履    ䷉
  ⟨.yang, .yang, .yang, .yin,  .yin,  .yin⟩,   -- 11. 泰    ䷊
  ⟨.yin,  .yin,  .yin,  .yang, .yang, .yang⟩,  -- 12. 否    ䷋
  ⟨.yang, .yin,  .yang, .yang, .yang, .yang⟩,  -- 13. 同人  ䷌
  ⟨.yang, .yang, .yang, .yang, .yin,  .yang⟩,  -- 14. 大有  ䷍
  ⟨.yin,  .yin,  .yang, .yin,  .yin,  .yin⟩,   -- 15. 谦    ䷎
  ⟨.yin,  .yin,  .yin,  .yang, .yin,  .yin⟩,   -- 16. 豫    ䷏
  ⟨.yang, .yin,  .yin,  .yang, .yang, .yin⟩,   -- 17. 随    ䷐
  ⟨.yin,  .yang, .yang, .yin,  .yin,  .yang⟩,  -- 18. 蛊    ䷑
  ⟨.yang, .yang, .yin,  .yin,  .yin,  .yin⟩,   -- 19. 临    ䷒
  ⟨.yin,  .yin,  .yin,  .yin,  .yang, .yang⟩,  -- 20. 观    ䷓
  ⟨.yang, .yin,  .yin,  .yang, .yin,  .yang⟩,  -- 21. 噬嗑  ䷔
  ⟨.yang, .yin,  .yang, .yin,  .yin,  .yang⟩,  -- 22. 贲    ䷕
  ⟨.yin,  .yin,  .yin,  .yin,  .yin,  .yang⟩,  -- 23. 剥    ䷖
  ⟨.yang, .yin,  .yin,  .yin,  .yin,  .yin⟩,   -- 24. 复    ䷗
  ⟨.yang, .yin,  .yin,  .yang, .yang, .yang⟩,  -- 25. 无妄  ䷘
  ⟨.yang, .yang, .yang, .yin,  .yin,  .yang⟩,  -- 26. 大畜  ䷙
  ⟨.yang, .yin,  .yin,  .yin,  .yin,  .yang⟩,  -- 27. 颐    ䷚
  ⟨.yin,  .yang, .yang, .yang, .yang, .yin⟩,   -- 28. 大过  ䷛
  ⟨.yin,  .yang, .yin,  .yin,  .yang, .yin⟩,   -- 29. 坎    ䷜
  ⟨.yang, .yin,  .yang, .yang, .yin,  .yang⟩,  -- 30. 离    ䷝
  ⟨.yin,  .yin,  .yang, .yang, .yang, .yin⟩,   -- 31. 咸    ䷞
  ⟨.yin,  .yang, .yang, .yang, .yin,  .yin⟩,   -- 32. 恒    ䷟
  ⟨.yin,  .yin,  .yang, .yang, .yang, .yang⟩,  -- 33. 遁    ䷠
  ⟨.yang, .yang, .yang, .yang, .yin,  .yin⟩,   -- 34. 大壮  ䷡
  ⟨.yin,  .yin,  .yin,  .yang, .yin,  .yang⟩,  -- 35. 晋    ䷢
  ⟨.yang, .yin,  .yang, .yin,  .yin,  .yin⟩,   -- 36. 明夷  ䷣
  ⟨.yang, .yin,  .yang, .yin,  .yang, .yang⟩,  -- 37. 家人  ䷤
  ⟨.yang, .yang, .yin,  .yang, .yin,  .yang⟩,  -- 38. 睽    ䷥
  ⟨.yin,  .yin,  .yang, .yin,  .yang, .yin⟩,   -- 39. 蹇    ䷦
  ⟨.yin,  .yang, .yin,  .yang, .yin,  .yin⟩,   -- 40. 解    ䷧
  ⟨.yang, .yang, .yin,  .yin,  .yin,  .yang⟩,  -- 41. 损    ䷨
  ⟨.yang, .yin,  .yin,  .yin,  .yang, .yang⟩,  -- 42. 益    ䷩
  ⟨.yang, .yang, .yang, .yang, .yang, .yin⟩,   -- 43. 夬    ䷪
  ⟨.yin,  .yang, .yang, .yang, .yang, .yang⟩,  -- 44. 姤    ䷫
  ⟨.yin,  .yin,  .yin,  .yang, .yang, .yin⟩,   -- 45. 萃    ䷬
  ⟨.yin,  .yang, .yang, .yin,  .yin,  .yin⟩,   -- 46. 升    ䷭
  ⟨.yin,  .yang, .yin,  .yang, .yang, .yin⟩,   -- 47. 困    ䷮
  ⟨.yin,  .yang, .yang, .yin,  .yang, .yin⟩,   -- 48. 井    ䷯
  ⟨.yang, .yin,  .yang, .yang, .yang, .yin⟩,   -- 49. 革    ䷰
  ⟨.yin,  .yang, .yang, .yang, .yin,  .yang⟩,  -- 50. 鼎    ䷱
  ⟨.yang, .yin,  .yin,  .yang, .yin,  .yin⟩,   -- 51. 震    ䷲
  ⟨.yin,  .yin,  .yang, .yin,  .yin,  .yang⟩,  -- 52. 艮    ䷳
  ⟨.yin,  .yin,  .yang, .yin,  .yang, .yang⟩,  -- 53. 渐    ䷴
  ⟨.yang, .yang, .yin,  .yang, .yin,  .yin⟩,   -- 54. 归妹  ䷵
  ⟨.yang, .yin,  .yang, .yang, .yin,  .yin⟩,   -- 55. 丰    ䷶
  ⟨.yin,  .yin,  .yang, .yang, .yin,  .yang⟩,  -- 56. 旅    ䷷
  ⟨.yin,  .yang, .yang, .yin,  .yang, .yang⟩,  -- 57. 巽    ䷸
  ⟨.yang, .yang, .yin,  .yang, .yang, .yin⟩,   -- 58. 兑    ䷹
  ⟨.yin,  .yang, .yin,  .yin,  .yang, .yang⟩,  -- 59. 涣    ䷺
  ⟨.yang, .yang, .yin,  .yin,  .yang, .yin⟩,   -- 60. 节    ䷻
  ⟨.yang, .yang, .yin,  .yin,  .yang, .yang⟩,  -- 61. 中孚  ䷼
  ⟨.yin,  .yin,  .yang, .yang, .yin,  .yin⟩,   -- 62. 小过  ䷽
  ⟨.yang, .yin,  .yang, .yin,  .yang, .yin⟩,   -- 63. 既济  ䷾
  ⟨.yin,  .yang, .yin,  .yang, .yin,  .yang⟩   -- 64. 未济  ䷿
]

/-! ## § 5 序卦 properties -/

theorem xuGua_length : xuGua.length = 64 := by native_decide

/-- The first hexagram in 序卦 is 乾. -/
theorem xuGua_head : xuGua.head? = some Hexagram.heaven := rfl

/-- The last hexagram in 序卦 is 未济. -/
theorem xuGua_last :
    xuGua.getLast? = some ⟨.yin, .yang, .yin, .yang, .yin, .yang⟩ := rfl

/-- 序卦 successor: the next hexagram in King Wen order, if any. -/
def xuGuaNext (h : Hexagram) : Option Hexagram :=
  let rec loop : List Hexagram → Option Hexagram
    | [] => none
    | [_] => none
    | a :: b :: rest =>
        if a = h then some b else loop (b :: rest)
  loop xuGua

/-! ## § 6 Public summary (legacy) -/

/-- R8 cardinality + 序卦 length facts. -/
theorem cell256_summary :
    R8.all.length = 256
    ∧ (∀ c : R8, c ∈ R8.all)
    ∧ xuGua.length = 64 :=
  ⟨R8.all_length, R8.mem_all, xuGua_length⟩

/-! ## § 7 Phase A — (Z/2)⁸ Algebraic Spine

  Expose R8 = Hexagram × Shi as a (Z/2)⁸ Abelian group via
  componentwise XOR. The Shi V₄ part is XOR'd in (因, 果) ∈ Bool²
  coordinates via `Shi.toYinGuo` / `Shi.ofYinGuo`.

  Components: (Hexagram = Yao⁶) gives (Z/2)⁶; Shi = (YinBit, GuoBit) gives
  (Z/2)². Total: (Z/2)⁸ = 256 cells with `origin = (heaven, dao)` as identity.

  Strategy: prove every law componentwise on Yao (4-case) + Bool (8-case),
  lift to Hexagram and Shi, then to R8 by `cases`.
-/

namespace R8

/-! ### § 7.1 Yao XOR helper -/

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

/-! ### § 7.2 Hexagram XOR -/

/-- Componentwise Hexagram XOR — yao-by-yao via `yaoXor`. -/
def hexXor (h1 h2 : Hexagram) : Hexagram :=
  ⟨yaoXor h1.y1 h2.y1, yaoXor h1.y2 h2.y2, yaoXor h1.y3 h2.y3,
   yaoXor h1.y4 h2.y4, yaoXor h1.y5 h2.y5, yaoXor h1.y6 h2.y6⟩

@[simp] theorem hexXor_qian_left (h : Hexagram) : hexXor Hexagram.heaven h = h := by
  rcases h with ⟨_, _, _, _, _, _⟩
  simp [hexXor, Hexagram.heaven]

@[simp] theorem hexXor_qian_right (h : Hexagram) : hexXor h Hexagram.heaven = h := by
  rcases h with ⟨_, _, _, _, _, _⟩
  simp [hexXor, Hexagram.heaven]

theorem hexXor_self (h : Hexagram) : hexXor h h = Hexagram.heaven := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  simp [hexXor, Hexagram.heaven, yaoXor_self]

theorem hexXor_comm (h1 h2 : Hexagram) : hexXor h1 h2 = hexXor h2 h1 := by
  rcases h1 with ⟨_, _, _, _, _, _⟩
  rcases h2 with ⟨_, _, _, _, _, _⟩
  simp [hexXor, yaoXor_comm]

theorem hexXor_assoc (h1 h2 h3 : Hexagram) :
    hexXor (hexXor h1 h2) h3 = hexXor h1 (hexXor h2 h3) := by
  rcases h1 with ⟨_, _, _, _, _, _⟩
  rcases h2 with ⟨_, _, _, _, _, _⟩
  rcases h3 with ⟨_, _, _, _, _, _⟩
  simp [hexXor, yaoXor_assoc]

/-! ### § 7.3 Shi XOR

  Shi = V₄ Klein four-group. We define XOR via the (因, 果) ∈ Bool² bijection. -/

/-- Shi XOR via componentwise Bool XOR on (因, 果). -/
def shiXor (s1 s2 : Shi) : Shi :=
  let (y1, g1) := Shi.toYinGuo s1
  let (y2, g2) := Shi.toYinGuo s2
  Shi.ofYinGuo (Bool.xor y1 y2, Bool.xor g1 g2)

@[simp] theorem shiXor_dao_left (s : Shi) : shiXor Shi.dao s = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

@[simp] theorem shiXor_dao_right (s : Shi) : shiXor s Shi.dao = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

theorem shiXor_self (s : Shi) : shiXor s s = Shi.dao := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

theorem shiXor_comm (s1 s2 : Shi) : shiXor s1 s2 = shiXor s2 s1 := by
  rcases s1 with ⟨y1, g1⟩; rcases s2 with ⟨y2, g2⟩
  cases y1 <;> cases g1 <;> cases y2 <;> cases g2 <;> rfl

theorem shiXor_assoc (s1 s2 s3 : Shi) :
    shiXor (shiXor s1 s2) s3 = shiXor s1 (shiXor s2 s3) := by
  rcases s1 with ⟨y1, g1⟩; rcases s2 with ⟨y2, g2⟩; rcases s3 with ⟨y3, g3⟩
  cases y1 <;> cases g1 <;> cases y2 <;> cases g2 <;> cases y3 <;> cases g3 <;> rfl

/-! ### § 7.4 R8 XOR -/

/-- R8 XOR = (hexXor on Hexagram, shiXor on Shi). -/
def xor (c1 c2 : R8) : R8 :=
  (hexXor c1.1 c2.1, shiXor c1.2 c2.2)

/-- 道 cell at R₈ = (heaven, dao) = (Z/2)⁸ identity. -/
def origin : R8 := (Hexagram.heaven, Shi.dao)

@[simp] theorem origin_xor (c : R8) : xor origin c = c := by
  rcases c with ⟨h, s⟩
  simp [xor, origin, hexXor_qian_left, shiXor_dao_left]

@[simp] theorem xor_origin (c : R8) : xor c origin = c := by
  rcases c with ⟨h, s⟩
  simp [xor, origin, hexXor_qian_right, shiXor_dao_right]

theorem xor_self (c : R8) : xor c c = origin := by
  rcases c with ⟨h, s⟩
  simp [xor, origin, hexXor_self, shiXor_self]

theorem xor_comm (c1 c2 : R8) : xor c1 c2 = xor c2 c1 := by
  rcases c1 with ⟨h1, s1⟩
  rcases c2 with ⟨h2, s2⟩
  simp [xor, hexXor_comm, shiXor_comm]

theorem xor_assoc (c1 c2 c3 : R8) :
    xor (xor c1 c2) c3 = xor c1 (xor c2 c3) := by
  rcases c1 with ⟨h1, s1⟩
  rcases c2 with ⟨h2, s2⟩
  rcases c3 with ⟨h3, s3⟩
  simp [xor, hexXor_assoc, shiXor_assoc]

end R8

/-! ### § 7.5 AddCommGroup-flavoured instance binding

  We bind `Add` / `Zero` / `Neg` / `Sub` so R8 can use `+ / 0 / -`
  notation. We do not import Mathlib here (kept as Foundation-pure), but
  every law required by `AddCommGroup` is proven explicitly above. -/

instance : Add R8 := ⟨R8.xor⟩
instance : Zero R8 := ⟨R8.origin⟩
/-- In (Z/2)ⁿ every element is self-inverse: `-c = c`. -/
instance : Neg R8 := ⟨id⟩
instance : Sub R8 := ⟨R8.xor⟩

namespace R8

@[simp] theorem add_def (c1 c2 : R8) : c1 + c2 = xor c1 c2 := rfl
@[simp] theorem zero_def : (0 : R8) = origin := rfl
@[simp] theorem neg_def (c : R8) : -c = c := rfl
@[simp] theorem sub_def (c1 c2 : R8) : c1 - c2 = xor c1 c2 := rfl

end R8

/-! ### § 7.6 SMul self-action (Cayley regular representation) -/

instance : SMul R8 R8 := ⟨R8.xor⟩

namespace R8

@[simp] theorem smul_def (c s : R8) : c • s = xor c s := rfl

/-- Cayley left-translation by c on R8. -/
def cayley (c : R8) : R8 → R8 := fun s => xor c s

/-- Evaluate a R8 endo at the origin to recover its translation. -/
def epsAtOrigin (f : R8 → R8) : R8 := f origin

/-- ε ∘ Cayley = id (retraction). -/
@[simp] theorem epsAtOrigin_cayley (c : R8) :
    epsAtOrigin (cayley c) = c := by
  simp [epsAtOrigin, cayley, xor_origin]

/-- Cayley is injective: distinct shifts are distinct functions. -/
theorem cayley_inj : Function.Injective cayley := by
  intro c1 c2 h
  have heq := congrFun h origin
  simp [cayley, xor_origin] at heq
  exact heq

/-- Cayley is a group homomorphism: `cayley (a + b) = cayley a ∘ cayley b`. -/
theorem cayley_hom (c1 c2 : R8) :
    cayley (xor c1 c2) = cayley c1 ∘ cayley c2 := by
  funext s
  simp [cayley, Function.comp_apply, xor_assoc]

end R8

/-! ## § 8 印/投 重写为 XOR mask (Phase A)

  The legacy `Shi.yin / Shi.project` (= `Shi.complement / Shi.reverse`) are V₄ wraps.
  Phase A re-expresses 印/投 at the **R8 level** as XOR with two
  canonical masks:

    imprint_mask = (heaven, ji)  = `oooooooi`o  (only YinBit / 因 axis)
    project_mask = (heaven, wei) = `oooooooo`i  (only GuoBit / 果 axis)

  Then `imprint = (· ⊕ imprint_mask)` and `project = (· ⊕ project_mask)` are mask-XOR
  involutions. The two masks XOR to `(heaven, jin) = "ooooooon"`, the V₄
  central element. -/

namespace R8

/-- 印 mask: only the YinBit (因 axis, R5 atom) is set.
    `(heaven, ji) = (heaven, (1, 0)) = "oooooooi"`. -/
def imprint_mask : R8 := (Hexagram.heaven, Shi.ji)

/-- 投 mask: only the GuoBit (果 axis, R6 atom) is set.
    `(heaven, wei) = (heaven, (0, 1)) = "ooooooox"`. -/
def project_mask : R8 := (Hexagram.heaven, Shi.wei)

/-- 印 (yìn) at R8: XOR with the YinBit-only mask. -/
def imprint (c : R8) : R8 := xor c imprint_mask

/-- 投 (tóu) at R8: XOR with the GuoBit-only mask. -/
def project (c : R8) : R8 := xor c project_mask

/-- 印 is involutive (mask is self-inverse). -/
theorem imprint_imprint (c : R8) : imprint (imprint c) = c := by
  unfold imprint
  rw [xor_assoc, xor_self, xor_origin]

/-- 投 is involutive. -/
theorem project_project (c : R8) : project (project c) = c := by
  unfold project
  rw [xor_assoc, xor_self, xor_origin]

/-- 印 and 投 commute (both are XOR-with-fixed-mask, and XOR is commutative
    + associative). -/
theorem imprint_project_comm (c : R8) : imprint (project c) = project (imprint c) := by
  unfold imprint project
  rw [xor_assoc, xor_assoc, xor_comm project_mask imprint_mask]

/-- 印 ∘ 投 = XOR with `(heaven, jin)` = the V₄ central mask. -/
theorem imprint_project_eq_central (c : R8) :
    imprint (project c) = xor c (Hexagram.heaven, Shi.jin) := by
  unfold imprint project
  rw [xor_assoc]
  congr 1

/-- The two masks together generate the V₄ central element. -/
theorem imprint_mask_xor_project_mask :
    xor imprint_mask project_mask = (Hexagram.heaven, Shi.jin) := by
  rfl

end R8

/-! ## § 9 Public summary (Phase A) -/

theorem cell256_phaseA_summary :
    -- (Z/2)⁸ identity + group laws
    (∀ c : R8, R8.xor R8.origin c = c)
    ∧ (∀ c : R8, R8.xor c c = R8.origin)
    ∧ (∀ a b : R8, R8.xor a b = R8.xor b a)
    ∧ (∀ a b c : R8,
        R8.xor (R8.xor a b) c = R8.xor a (R8.xor b c))
    -- Cayley fusion
    ∧ Function.Injective R8.cayley
    ∧ (∀ c : R8, R8.epsAtOrigin (R8.cayley c) = c)
    -- 印 / 投 mask involutions + commute
    ∧ (∀ c : R8, R8.imprint (R8.imprint c) = c)
    ∧ (∀ c : R8, R8.project (R8.project c) = c)
    ∧ (∀ c : R8, R8.imprint (R8.project c) = R8.project (R8.imprint c)) :=
  ⟨R8.origin_xor, R8.xor_self, R8.xor_comm, R8.xor_assoc,
   R8.cayley_inj, R8.epsAtOrigin_cayley,
   R8.imprint_imprint, R8.project_project, R8.imprint_project_comm⟩

end SSBX.Foundation.Bagua.R8
