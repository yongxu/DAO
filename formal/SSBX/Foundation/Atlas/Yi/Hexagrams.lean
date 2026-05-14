/-
# Foundation.Atlas.Yi.Hexagrams — 64 hexagram names on R 6

Per `wen-algebra` v0.6 §9 and `v4-foundation` v0.5 §15:

    六十四卦 : 64 named elements of `R 6 = Fin 6 → Bool`

This module gives:

* The 4 distinguished hexagrams that are 互-related fixed points or a
  2-cycle: `qianqian` (☰☰), `kunkun` (☷☷), `jiji` (☵☲), `weiji` (☲☵).
* The 64-hexagram King Wen ordering `xuGua : List Hexagram` (transcribed
  from `Foundation/Bagua/R8.lean`'s `xuGua`, the canonical King Wen
  序卦传 order).
* Helpers `Hexagram.toIdx : Hexagram → Fin 64` and
  `Hexagram.fromIdx : Fin 64 → Hexagram` that round-trip through the
  King Wen ordering.

The 60 hexagrams not named individually are accessible by King-Wen
index (e.g. `Hexagram.fromIdx ⟨2, _⟩` is 屯, "Difficulty at Birth").

## Bit-pattern convention

`o = false = yang`, `x = true = yin`.  The hexagram constructor `mk`
takes `y1 ... y6` in bottom-to-top order.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §1.6 (R 6 readings).
* `v4-foundation.md` v0.5 §15.6 (Hexagram binding).
-/

import SSBX.Foundation.Atlas.Yi.Names

namespace SSBX.Foundation.Atlas.Yi

open SSBX.Foundation.R
open Yao (yang yin)

namespace Hexagram

/-! ## § 1 The four distinguished hexagrams

These four are the simultaneous fixed-points / orbit of `hu` (mutual
hexagram) and `cuo` (complement):

    cuo qianqian = kunkun,    cuo kunkun = qianqian
    cuo jiji     = weiji,     cuo weiji  = jiji
    hu  qianqian = qianqian,  hu  kunkun = kunkun     (the 2 fixed pts)
    hu  jiji     = weiji,     hu  weiji  = jiji       (the 2-cycle)

-/

/-- 乾為天 (☰☰): all yang.  King Wen #1. -/
@[match_pattern] def qianqian : Hexagram := mk yang yang yang yang yang yang

/-- 坤為地 (☷☷): all yin.  King Wen #2. -/
@[match_pattern] def kunkun : Hexagram := mk yin yin yin yin yin yin

/-- 既濟 (☲☵, fire over water): "Already crossed".  King Wen #63.
    Bit pattern `(yang, yin, yang, yin, yang, yin)` — inner = 離, outer = 坎. -/
@[match_pattern] def jiji : Hexagram := mk yang yin yang yin yang yin

/-- 未濟 (☵☲, water over fire): "Not yet crossed".  King Wen #64.
    Bit pattern `(yin, yang, yin, yang, yin, yang)` — inner = 坎, outer = 離. -/
@[match_pattern] def weiji : Hexagram := mk yin yang yin yang yin yang

/-! ## § 2 King Wen Order (序卦傳)

The 64 hexagrams in the canonical 序卦傳 (King Wen) order.  Numbered
1–64 (0-indexed in `xuGua`).  -/

/-- The 64 hexagrams in the canonical 序卦傳 order. -/
def xuGua : List Hexagram := [
  mk yang yang yang yang yang yang,  --  1. 乾    ䷀
  mk yin  yin  yin  yin  yin  yin,   --  2. 坤    ䷁
  mk yang yin  yin  yin  yang yin,   --  3. 屯    ䷂
  mk yin  yang yin  yin  yin  yang,  --  4. 蒙    ䷃
  mk yang yang yang yin  yang yin,   --  5. 需    ䷄
  mk yin  yang yin  yang yang yang,  --  6. 訟    ䷅
  mk yin  yang yin  yin  yin  yin,   --  7. 師    ䷆
  mk yin  yin  yin  yin  yang yin,   --  8. 比    ䷇
  mk yang yang yang yin  yang yang,  --  9. 小畜  ䷈
  mk yang yang yin  yang yang yang,  -- 10. 履    ䷉
  mk yang yang yang yin  yin  yin,   -- 11. 泰    ䷊
  mk yin  yin  yin  yang yang yang,  -- 12. 否    ䷋
  mk yang yin  yang yang yang yang,  -- 13. 同人  ䷌
  mk yang yang yang yang yin  yang,  -- 14. 大有  ䷍
  mk yin  yin  yang yin  yin  yin,   -- 15. 謙    ䷎
  mk yin  yin  yin  yang yin  yin,   -- 16. 豫    ䷏
  mk yang yin  yin  yang yang yin,   -- 17. 隨    ䷐
  mk yin  yang yang yin  yin  yang,  -- 18. 蠱    ䷑
  mk yang yang yin  yin  yin  yin,   -- 19. 臨    ䷒
  mk yin  yin  yin  yin  yang yang,  -- 20. 觀    ䷓
  mk yang yin  yin  yang yin  yang,  -- 21. 噬嗑  ䷔
  mk yang yin  yang yin  yin  yang,  -- 22. 賁    ䷕
  mk yin  yin  yin  yin  yin  yang,  -- 23. 剝    ䷖
  mk yang yin  yin  yin  yin  yin,   -- 24. 復    ䷗
  mk yang yin  yin  yang yang yang,  -- 25. 無妄  ䷘
  mk yang yang yang yin  yin  yang,  -- 26. 大畜  ䷙
  mk yang yin  yin  yin  yin  yang,  -- 27. 頤    ䷚
  mk yin  yang yang yang yang yin,   -- 28. 大過  ䷛
  mk yin  yang yin  yin  yang yin,   -- 29. 坎    ䷜
  mk yang yin  yang yang yin  yang,  -- 30. 離    ䷝
  mk yin  yin  yang yang yang yin,   -- 31. 咸    ䷞
  mk yin  yang yang yang yin  yin,   -- 32. 恆    ䷟
  mk yin  yin  yang yang yang yang,  -- 33. 遯    ䷠
  mk yang yang yang yang yin  yin,   -- 34. 大壯  ䷡
  mk yin  yin  yin  yang yin  yang,  -- 35. 晉    ䷢
  mk yang yin  yang yin  yin  yin,   -- 36. 明夷  ䷣
  mk yang yin  yang yin  yang yang,  -- 37. 家人  ䷤
  mk yang yang yin  yang yin  yang,  -- 38. 睽    ䷥
  mk yin  yin  yang yin  yang yin,   -- 39. 蹇    ䷦
  mk yin  yang yin  yang yin  yin,   -- 40. 解    ䷧
  mk yang yang yin  yin  yin  yang,  -- 41. 損    ䷨
  mk yang yin  yin  yin  yang yang,  -- 42. 益    ䷩
  mk yang yang yang yang yang yin,   -- 43. 夬    ䷪
  mk yin  yang yang yang yang yang,  -- 44. 姤    ䷫
  mk yin  yin  yin  yang yang yin,   -- 45. 萃    ䷬
  mk yin  yang yang yin  yin  yin,   -- 46. 升    ䷭
  mk yin  yang yin  yang yang yin,   -- 47. 困    ䷮
  mk yin  yang yang yin  yang yin,   -- 48. 井    ䷯
  mk yang yin  yang yang yang yin,   -- 49. 革    ䷰
  mk yin  yang yang yang yin  yang,  -- 50. 鼎    ䷱
  mk yang yin  yin  yang yin  yin,   -- 51. 震    ䷲
  mk yin  yin  yang yin  yin  yang,  -- 52. 艮    ䷳
  mk yin  yin  yang yin  yang yang,  -- 53. 漸    ䷴
  mk yang yang yin  yang yin  yin,   -- 54. 歸妹  ䷵
  mk yang yin  yang yang yin  yin,   -- 55. 豐    ䷶
  mk yin  yin  yang yang yin  yang,  -- 56. 旅    ䷷
  mk yin  yang yang yin  yang yang,  -- 57. 巽    ䷸
  mk yang yang yin  yang yang yin,   -- 58. 兌    ䷹
  mk yin  yang yin  yin  yang yang,  -- 59. 渙    ䷺
  mk yang yang yin  yin  yang yin,   -- 60. 節    ䷻
  mk yang yang yin  yin  yang yang,  -- 61. 中孚  ䷼
  mk yin  yin  yang yang yin  yin,   -- 62. 小過  ䷽
  mk yang yin  yang yin  yang yin,   -- 63. 既濟  ䷾
  mk yin  yang yin  yang yin  yang   -- 64. 未濟  ䷿
]

/-- |序卦| = 64. -/
theorem xuGua_length : xuGua.length = 64 := rfl

/-- First hexagram in 序卦 is 乾為天. -/
theorem xuGua_head : xuGua.head? = some qianqian := rfl

/-- Last hexagram in 序卦 is 未濟. -/
theorem xuGua_last : xuGua.getLast? = some weiji := rfl

/-! ## § 3 King-Wen index helpers -/

/-- Encode a hexagram as a 6-bit `Nat` (0..63) by the bit pattern
    `(y1 << 5) | (y2 << 4) | (y3 << 3) | (y4 << 2) | (y5 << 1) | y6`. -/
def toBitNat (h : Hexagram) : Nat :=
  (if h.y1 then 32 else 0)
  + (if h.y2 then 16 else 0)
  + (if h.y3 then 8 else 0)
  + (if h.y4 then 4 else 0)
  + (if h.y5 then 2 else 0)
  + (if h.y6 then 1 else 0)

/-- `toBitNat` of every hexagram is < 64. -/
theorem toBitNat_lt (h : Hexagram) : toBitNat h < 64 := by
  unfold toBitNat
  rcases h.y1 with _ | _ <;> rcases h.y2 with _ | _ <;>
  rcases h.y3 with _ | _ <;> rcases h.y4 with _ | _ <;>
  rcases h.y5 with _ | _ <;> rcases h.y6 with _ | _ <;> decide

/-- King-Wen index lookup: find the position of `h` in `xuGua`.
    Returns the 0-based King Wen index (1-based King Wen number minus 1).
    If for some reason `h` is not in the list (impossible), returns 0. -/
def kingWenIdx (h : Hexagram) : Nat :=
  (xuGua.idxOf h)

/-- Get the hexagram at King-Wen index `i` (0-based; i = 0 returns 乾,
    i = 63 returns 未濟). -/
def fromIdx (i : Fin 64) : Hexagram :=
  xuGua[i.val]'(by rw [xuGua_length]; exact i.isLt)

@[simp] theorem fromIdx_zero : fromIdx ⟨0, by decide⟩ = qianqian := rfl
@[simp] theorem fromIdx_one  : fromIdx ⟨1, by decide⟩ = kunkun   := rfl

/-- King Wen #63 is 既濟. -/
theorem fromIdx_62 : fromIdx ⟨62, by decide⟩ = jiji := rfl

/-- King Wen #64 is 未濟. -/
theorem fromIdx_63 : fromIdx ⟨63, by decide⟩ = weiji := rfl

/-! ## § 4 Distinctness of the 4 named anchors -/

theorem qianqian_ne_kunkun : (qianqian : Hexagram) ≠ kunkun := by
  intro h; have := congrFun h ⟨0, by decide⟩; cases this

theorem jiji_ne_weiji : (jiji : Hexagram) ≠ weiji := by
  intro h; have := congrFun h ⟨0, by decide⟩; cases this

theorem qianqian_ne_jiji : (qianqian : Hexagram) ≠ jiji := by
  intro h; have := congrFun h ⟨1, by decide⟩; cases this

/-! ## § 5 Legacy English / pinyin aliases

Pinyin entries for two further King-Wen anchors and English aliases for
the six most commonly used hexagrams.  Each alias is a `def`-level
synonym so existing pattern-matches against the canonical name continue
to typecheck. -/

/-- 泰 (☷☰, earth over heaven, King Wen #11): "peace".  Inner 乾, outer 坤. -/
@[match_pattern] def tai : Hexagram := mk yang yang yang yin yin yin

/-- 否 (☰☷, heaven over earth, King Wen #12): "blocking" / "obstruction".
    Inner 坤, outer 乾. -/
@[match_pattern] def pi : Hexagram := mk yin yin yin yang yang yang

/-- ☰☰ 乾為天 — "heaven" alias of `qianqian`. -/
def heaven : Hexagram := qianqian

/-- ☷☷ 坤為地 — "earth" alias of `kunkun`. -/
def earth : Hexagram := kunkun

/-- ☵☲ 既濟 — "complete" alias of `jiji`. -/
def complete : Hexagram := jiji

/-- ☲☵ 未濟 — "incomplete" alias of `weiji`. -/
def incomplete : Hexagram := weiji

/-- ☰☷ 否 — "blocking" alias of `pi`. -/
def blocking : Hexagram := pi

/-- ☷☰ 泰 — "peace" alias of `tai`. -/
def peace : Hexagram := tai

end Hexagram

end SSBX.Foundation.Atlas.Yi
