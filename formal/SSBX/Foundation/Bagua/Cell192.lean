/-
# Cell192 — 192 格 + 时态 + 序卦

192 = 64 卦 × 3 时态 (已 / 今 / 未).

Builds on Yi.lean and BaguaAlgebra.lean.

## Phases
  § 1   Shi (时态) inductive + cyclic Z/3 group
  § 2   Cell192 = Hexagram × Shi + cardinality 192
  § 3   Cell192 lateral operators (合 hex flips with 时态)
  § 4   xuGua (序卦传 King Wen order) as List Hexagram of length 64
  § 5   xuGua next / index / completeness theorems
-/
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra

namespace SSBX.Foundation.Bagua.Cell192

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.Yi.Trigram
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 Shi (时态) — Z/3 cyclic group -/

/-- 时态: 三时态 已 / 今 / 未. -/
inductive Shi : Type
  | ji   -- 已 (past)
  | jin  -- 今 (present)
  | wei  -- 未 (future)
  deriving Repr, DecidableEq, BEq

namespace Shi

/-- All three 时态. -/
def all : List Shi := [ji, jin, wei]

theorem all_length : all.length = 3 := rfl

/-- 时态前进: 已 → 今 → 未 → 已. -/
def next : Shi → Shi
  | ji  => jin
  | jin => wei
  | wei => ji

/-- 时态后退: 已 ← 今 ← 未 ← 已. -/
def prev : Shi → Shi
  | ji  => wei
  | jin => ji
  | wei => jin

theorem next_prev (s : Shi) : prev (next s) = s := by cases s <;> rfl
theorem prev_next (s : Shi) : next (prev s) = s := by cases s <;> rfl

/-- next is order 3 (cyclic Z/3). -/
theorem next_three (s : Shi) : next (next (next s)) = s := by cases s <;> rfl

end Shi

/-! ## § 2 Cell192 — 192 格 -/

/-- 192 格 = 64 卦 × 3 时态. -/
abbrev Cell192 : Type := Hexagram × Shi

namespace Cell192

/-- All 192 cells. -/
def all : List Cell192 :=
  Hexagram.allHex.flatMap fun h => Shi.all.map fun s => (h, s)

/-- |Cell192| = 192 strictly. -/
theorem all_length : all.length = 192 := by native_decide

/-- The 192-cell enumeration has no duplicate cells. -/
theorem all_nodup : all.Nodup := by native_decide

/-- Every Cell192 is in `all` (exhaustion). -/
theorem mem_all (c : Cell192) : c ∈ all := by
  rcases c with ⟨h, s⟩
  unfold all
  refine List.mem_flatMap.mpr ⟨h, hexagram_mem_allHex h, ?_⟩
  exact List.mem_map.mpr ⟨s, by cases s <;> simp [Shi.all], rfl⟩

end Cell192

/-! ## § 3 Cell192 lateral operators — combined hex flips + 时态 -/

namespace Cell192

/-- 时态前进 on Cell192. -/
def shiNext (c : Cell192) : Cell192 := (c.1, c.2.next)
/-- 时态后退 on Cell192. -/
def shiPrev (c : Cell192) : Cell192 := (c.1, c.2.prev)

theorem shiNext_prev (c : Cell192) : shiPrev (shiNext c) = c := by
  rcases c with ⟨h, s⟩
  simp [shiNext, shiPrev, Shi.next_prev]

theorem shiPrev_next (c : Cell192) : shiNext (shiPrev c) = c := by
  rcases c with ⟨h, s⟩
  simp [shiNext, shiPrev, Shi.prev_next]

theorem shiNext_three (c : Cell192) : shiNext (shiNext (shiNext c)) = c := by
  rcases c with ⟨h, s⟩
  simp [shiNext, Shi.next_three]

/-- Hexagram 错 lifted to Cell192 (preserves 时态). -/
def hexCuo (c : Cell192) : Cell192 := (Hexagram.cuo c.1, c.2)
/-- Hexagram 综 lifted. -/
def hexZong (c : Cell192) : Cell192 := (Hexagram.zong c.1, c.2)
/-- Hexagram 互 lifted. -/
def hexHu (c : Cell192) : Cell192 := (Hexagram.hu c.1, c.2)

/-- 6 single yao flips lifted. -/
def flip1 (c : Cell192) : Cell192 := (dongInner c.1, c.2)
def flip2 (c : Cell192) : Cell192 := (huaInner c.1, c.2)
def flip3 (c : Cell192) : Cell192 := (bianInner c.1, c.2)
def flip4 (c : Cell192) : Cell192 := (dongOuter c.1, c.2)
def flip5 (c : Cell192) : Cell192 := (huaOuter c.1, c.2)
def flip6 (c : Cell192) : Cell192 := (bianOuter c.1, c.2)

theorem hexCuo_hexCuo (c : Cell192) : hexCuo (hexCuo c) = c := by
  rcases c with ⟨h, s⟩
  simp [hexCuo, Hexagram.cuo_cuo]

theorem hexZong_hexZong (c : Cell192) : hexZong (hexZong c) = c := by
  rcases c with ⟨h, s⟩
  simp [hexZong, Hexagram.zong_zong]

theorem hexCuo_hexZong_comm (c : Cell192) :
    hexCuo (hexZong c) = hexZong (hexCuo c) := by
  rcases c with ⟨h, s⟩
  simp [hexCuo, hexZong, Hexagram.cuo_zong_comm]

theorem hexCuoZong_hexCuoZong (c : Cell192) :
    hexCuo (hexZong (hexCuo (hexZong c))) = c := by
  rw [hexCuo_hexZong_comm, hexCuo_hexCuo, hexZong_hexZong]

theorem flip1_flip1 (c : Cell192) : flip1 (flip1 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip1, dongInner_dongInner]

theorem flip2_flip2 (c : Cell192) : flip2 (flip2 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip2, huaInner_huaInner]

theorem flip3_flip3 (c : Cell192) : flip3 (flip3 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip3, bianInner_bianInner]

theorem flip4_flip4 (c : Cell192) : flip4 (flip4 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip4, dongOuter_dongOuter]

theorem flip5_flip5 (c : Cell192) : flip5 (flip5 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip5, huaOuter_huaOuter]

theorem flip6_flip6 (c : Cell192) : flip6 (flip6 c) = c := by
  rcases c with ⟨h, s⟩; simp [flip6, bianOuter_bianOuter]

end Cell192

/-! ## § 4 序卦 (King Wen Order) — 64 hexagrams in canonical sequence -/

/-- The 64 hexagrams in the canonical 序卦传 (King Wen) order.

  Each entry is the explicit Hexagram literal `⟨y1, y2, y3, y4, y5, y6⟩`,
  where (y1,y2,y3) is the inner (下) trigram and (y4,y5,y6) is the outer (上).
  Pattern reference: e.g., 屯 = 水雷屯 = inner 雷(zhen), outer 水(kan)
  = (yang, yin, yin, yin, yang, yin).

  We use explicit Hexagram literals (rather than `chong t1 t2`) to allow
  `native_decide` to evaluate list membership at the kernel/native level. -/
def xuGua : List Hexagram := [
  ⟨.yang, .yang, .yang, .yang, .yang, .yang⟩,  --  1. 乾    ䷀
  ⟨.yin,  .yin,  .yin,  .yin,  .yin,  .yin⟩,   --  2. 坤    ䷁
  ⟨.yang, .yin,  .yin,  .yin,  .yang, .yin⟩,   --  3. 屯    ䷂  水雷屯
  ⟨.yin,  .yang, .yin,  .yin,  .yin,  .yang⟩,  --  4. 蒙    ䷃  山水蒙
  ⟨.yang, .yang, .yang, .yin,  .yang, .yin⟩,   --  5. 需    ䷄  水天需
  ⟨.yin,  .yang, .yin,  .yang, .yang, .yang⟩,  --  6. 讼    ䷅  天水讼
  ⟨.yin,  .yang, .yin,  .yin,  .yin,  .yin⟩,   --  7. 师    ䷆  地水师
  ⟨.yin,  .yin,  .yin,  .yin,  .yang, .yin⟩,   --  8. 比    ䷇  水地比
  ⟨.yang, .yang, .yang, .yin,  .yang, .yang⟩,  --  9. 小畜  ䷈  风天小畜
  ⟨.yang, .yang, .yin,  .yang, .yang, .yang⟩,  -- 10. 履    ䷉  天泽履
  ⟨.yang, .yang, .yang, .yin,  .yin,  .yin⟩,   -- 11. 泰    ䷊  地天泰
  ⟨.yin,  .yin,  .yin,  .yang, .yang, .yang⟩,  -- 12. 否    ䷋  天地否
  ⟨.yang, .yin,  .yang, .yang, .yang, .yang⟩,  -- 13. 同人  ䷌  天火同人
  ⟨.yang, .yang, .yang, .yang, .yin,  .yang⟩,  -- 14. 大有  ䷍  火天大有
  ⟨.yin,  .yin,  .yang, .yin,  .yin,  .yin⟩,   -- 15. 谦    ䷎  地山谦
  ⟨.yin,  .yin,  .yin,  .yang, .yin,  .yin⟩,   -- 16. 豫    ䷏  雷地豫
  ⟨.yang, .yin,  .yin,  .yang, .yang, .yin⟩,   -- 17. 随    ䷐  泽雷随
  ⟨.yin,  .yang, .yang, .yin,  .yin,  .yang⟩,  -- 18. 蛊    ䷑  山风蛊
  ⟨.yang, .yang, .yin,  .yin,  .yin,  .yin⟩,   -- 19. 临    ䷒  地泽临
  ⟨.yin,  .yin,  .yin,  .yin,  .yang, .yang⟩,  -- 20. 观    ䷓  风地观
  ⟨.yang, .yin,  .yin,  .yang, .yin,  .yang⟩,  -- 21. 噬嗑  ䷔  火雷噬嗑
  ⟨.yang, .yin,  .yang, .yin,  .yin,  .yang⟩,  -- 22. 贲    ䷕  山火贲
  ⟨.yin,  .yin,  .yin,  .yin,  .yin,  .yang⟩,  -- 23. 剥    ䷖  山地剥
  ⟨.yang, .yin,  .yin,  .yin,  .yin,  .yin⟩,   -- 24. 复    ䷗  地雷复
  ⟨.yang, .yin,  .yin,  .yang, .yang, .yang⟩,  -- 25. 无妄  ䷘  天雷无妄
  ⟨.yang, .yang, .yang, .yin,  .yin,  .yang⟩,  -- 26. 大畜  ䷙  山天大畜
  ⟨.yang, .yin,  .yin,  .yin,  .yin,  .yang⟩,  -- 27. 颐    ䷚  山雷颐
  ⟨.yin,  .yang, .yang, .yang, .yang, .yin⟩,   -- 28. 大过  ䷛  泽风大过
  ⟨.yin,  .yang, .yin,  .yin,  .yang, .yin⟩,   -- 29. 坎    ䷜
  ⟨.yang, .yin,  .yang, .yang, .yin,  .yang⟩,  -- 30. 离    ䷝
  ⟨.yin,  .yin,  .yang, .yang, .yang, .yin⟩,   -- 31. 咸    ䷞  泽山咸
  ⟨.yin,  .yang, .yang, .yang, .yin,  .yin⟩,   -- 32. 恒    ䷟  雷风恒
  ⟨.yin,  .yin,  .yang, .yang, .yang, .yang⟩,  -- 33. 遁    ䷠  天山遁
  ⟨.yang, .yang, .yang, .yang, .yin,  .yin⟩,   -- 34. 大壮  ䷡  雷天大壮
  ⟨.yin,  .yin,  .yin,  .yang, .yin,  .yang⟩,  -- 35. 晋    ䷢  火地晋
  ⟨.yang, .yin,  .yang, .yin,  .yin,  .yin⟩,   -- 36. 明夷  ䷣  地火明夷
  ⟨.yang, .yin,  .yang, .yin,  .yang, .yang⟩,  -- 37. 家人  ䷤  风火家人
  ⟨.yang, .yang, .yin,  .yang, .yin,  .yang⟩,  -- 38. 睽    ䷥  火泽睽
  ⟨.yin,  .yin,  .yang, .yin,  .yang, .yin⟩,   -- 39. 蹇    ䷦  水山蹇
  ⟨.yin,  .yang, .yin,  .yang, .yin,  .yin⟩,   -- 40. 解    ䷧  雷水解
  ⟨.yang, .yang, .yin,  .yin,  .yin,  .yang⟩,  -- 41. 损    ䷨  山泽损
  ⟨.yang, .yin,  .yin,  .yin,  .yang, .yang⟩,  -- 42. 益    ䷩  风雷益
  ⟨.yang, .yang, .yang, .yang, .yang, .yin⟩,   -- 43. 夬    ䷪  泽天夬
  ⟨.yin,  .yang, .yang, .yang, .yang, .yang⟩,  -- 44. 姤    ䷫  天风姤
  ⟨.yin,  .yin,  .yin,  .yang, .yang, .yin⟩,   -- 45. 萃    ䷬  泽地萃
  ⟨.yin,  .yang, .yang, .yin,  .yin,  .yin⟩,   -- 46. 升    ䷭  地风升
  ⟨.yin,  .yang, .yin,  .yang, .yang, .yin⟩,   -- 47. 困    ䷮  泽水困
  ⟨.yin,  .yang, .yang, .yin,  .yang, .yin⟩,   -- 48. 井    ䷯  水风井
  ⟨.yang, .yin,  .yang, .yang, .yang, .yin⟩,   -- 49. 革    ䷰  泽火革
  ⟨.yin,  .yang, .yang, .yang, .yin,  .yang⟩,  -- 50. 鼎    ䷱  火风鼎
  ⟨.yang, .yin,  .yin,  .yang, .yin,  .yin⟩,   -- 51. 震    ䷲
  ⟨.yin,  .yin,  .yang, .yin,  .yin,  .yang⟩,  -- 52. 艮    ䷳
  ⟨.yin,  .yin,  .yang, .yin,  .yang, .yang⟩,  -- 53. 渐    ䷴  风山渐
  ⟨.yang, .yang, .yin,  .yang, .yin,  .yin⟩,   -- 54. 归妹  ䷵  雷泽归妹
  ⟨.yang, .yin,  .yang, .yang, .yin,  .yin⟩,   -- 55. 丰    ䷶  雷火丰
  ⟨.yin,  .yin,  .yang, .yang, .yin,  .yang⟩,  -- 56. 旅    ䷷  火山旅
  ⟨.yin,  .yang, .yang, .yin,  .yang, .yang⟩,  -- 57. 巽    ䷸
  ⟨.yang, .yang, .yin,  .yang, .yang, .yin⟩,   -- 58. 兑    ䷹
  ⟨.yin,  .yang, .yin,  .yin,  .yang, .yang⟩,  -- 59. 涣    ䷺  风水涣
  ⟨.yang, .yang, .yin,  .yin,  .yang, .yin⟩,   -- 60. 节    ䷻  水泽节
  ⟨.yang, .yang, .yin,  .yin,  .yang, .yang⟩,  -- 61. 中孚  ䷼  风泽中孚
  ⟨.yin,  .yin,  .yang, .yang, .yin,  .yin⟩,   -- 62. 小过  ䷽  雷山小过
  ⟨.yang, .yin,  .yang, .yin,  .yang, .yin⟩,   -- 63. 既济  ䷾  水火既济
  ⟨.yin,  .yang, .yin,  .yang, .yin,  .yang⟩   -- 64. 未济  ䷿  火水未济
]

/-! ## § 5 序卦 properties -/

theorem xuGua_length : xuGua.length = 64 := by native_decide

/-- The first hexagram in 序卦 is 乾. -/
theorem xuGua_head : xuGua.head? = some Hexagram.qian := rfl

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

/-! ## § 6 Public summary -/

/-- Cell192 cardinality + 序卦 length facts. -/
theorem cell192_summary :
    Cell192.all.length = 192
    ∧ (∀ c : Cell192, c ∈ Cell192.all)
    ∧ xuGua.length = 64 :=
  ⟨Cell192.all_length, Cell192.mem_all, xuGua_length⟩

end SSBX.Foundation.Bagua.Cell192
