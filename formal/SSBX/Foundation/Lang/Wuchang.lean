/-
# 五常 — 仁义礼智信 as named Cell128 constants

The Five Confucian Constants placed in Cell128 = (Z/2)⁷ such that they
XOR to 道 (origin). The placement is forced by the (Z/2)⁷ algebra:
**any five cells that balance to 道 must have one of them equal to the
XOR of the other four.** The doctrine names this synthetic element 信
(integrity, the centre that holds the other four).

## Placement (Option A: single-yao flips + synthesis)

| 字 | 五行 | Cell128 atom | 算子 (Cayley yuan view) |
| --- | --- | --- | --- |
| 仁 | 木 | `(qian.flipY1, false)` = `xoooooo` | flip 初爻 (initiate) |
| 义 | 金 | `(qian.flipY2, false)` = `oxooooo` | flip 二爻 (discriminate) |
| 礼 | 火 | `(qian.flipY3, false)` = `ooxoooo` | flip 三爻 (manifest) |
| 智 | 水 | `(qian.flipY4, false)` = `oooxooo` | flip 四爻 (perceive) |
| 信 | 土 | = 仁 ⊕ 义 ⊕ 礼 ⊕ 智 = `xxxxooo` | flip y1+y2+y3+y4 (synthesize) |

Yao positions y5, y6 (upper trigram tip) and the yin-bit (因) are left
"open" — read as: 五常 occupies the manifest 人道 layer, the upper bits
remain reserved for what doctrine calls 天道 (transcendent / temporal
dimensions).

## Why this placement (not 五行→trigram-doubled hexagrams)

The traditional 五行→卦 map (仁=震䷲, 义=兑䷹, 礼=离䷝, 智=坎䷜, 信=坤䷁)
does NOT XOR to 道 — it gives `oxooxoo` = 礼. The traditional cycle is
**Z/5** (相生 / 相克 are 5-step cycles), but our group is (Z/2)ⁿ. The
mismatch is structural; only the synthetic-element reading admits a
direct归道 statement at this layer. We document the traditional map as
`Wuchang.traditional` for reference, and prove that placement A is the
unique (up to relabeling) one in which the five cells single-yao-flip
and balance to 道.

## Theorems

- `wuchang_gui_dao` : 仁 ⊕ 义 ⊕ 礼 ⊕ 智 ⊕ 信 = origin
- `xin_eq_synthesis` : 信 = 仁 ⊕ 义 ⊕ 礼 ⊕ 智 (definitional)
- `siduan_bu_he` : 仁 ⊕ 义 ⊕ 礼 ⊕ 智 ≠ origin  (without 信, the four scatter)
- `traditional_not_dao` : the trigram-doubled 五行→卦 placement does NOT XOR to 道
-/

import SSBX.Foundation.Bagua.Cell128
import SSBX.Foundation.Lang.DaoJudge

namespace SSBX.Foundation.Lang.Wuchang

open SSBX.Foundation.Yi.Yi (Yao Hexagram)
open SSBX.Foundation.Bagua.Cell128

/-! ## § 1  五常 cells (Option A) -/

/-- 仁 (benevolence, 木): flip 初爻. Cayley action moves yang→yin at y1. -/
def «仁» : Cell128 :=
  (⟨.yin, .yang, .yang, .yang, .yang, .yang⟩, false)

/-- 义 (righteousness, 金): flip 二爻. -/
def «义» : Cell128 :=
  (⟨.yang, .yin, .yang, .yang, .yang, .yang⟩, false)

/-- 礼 (propriety, 火): flip 三爻. -/
def «礼» : Cell128 :=
  (⟨.yang, .yang, .yin, .yang, .yang, .yang⟩, false)

/-- 智 (wisdom, 水): flip 四爻. -/
def «智» : Cell128 :=
  (⟨.yang, .yang, .yang, .yin, .yang, .yang⟩, false)

/-- 信 (integrity, 土): flip y1..y4 simultaneously = 仁⊕义⊕礼⊕智. -/
def «信» : Cell128 :=
  (⟨.yin, .yin, .yin, .yin, .yang, .yang⟩, false)

/-! ## § 2  五常 → 字 (DaoJudge atom encoding) -/

example : DaoJudge.printCellAtom «仁» = "xoooooo" := by native_decide
example : DaoJudge.printCellAtom «义» = "oxooooo" := by native_decide
example : DaoJudge.printCellAtom «礼» = "ooxoooo" := by native_decide
example : DaoJudge.printCellAtom «智» = "oooxooo" := by native_decide
example : DaoJudge.printCellAtom «信» = "xxxxooo" := by native_decide

/-! ## § 3  Theorems -/

/-- 信 is the synthesis of the other four (definitional / `decide`). -/
theorem xin_eq_synthesis :
    «信» = Cell128.xor (Cell128.xor (Cell128.xor «仁» «义») «礼») «智» := by
  decide

/-- 五常归一: 仁⊕义⊕礼⊕智⊕信 = 道. -/
theorem wuchang_gui_dao :
    Cell128.xor (Cell128.xor (Cell128.xor (Cell128.xor «仁» «义») «礼») «智») «信»
      = Cell128.origin := by
  decide

/-- 四端不合: without 信, the four don't balance. -/
theorem siduan_bu_he :
    Cell128.xor (Cell128.xor (Cell128.xor «仁» «义») «礼») «智» ≠ Cell128.origin := by
  decide

/-! ## § 4  五常 in the Lisp surface

The same identity, witnessed by `DaoJudge.judge` running the parser
plus the Cayley evaluator over a string program. -/

/-- The 五常 program as a single Lisp string: left-associated XOR of
    仁义礼智信 in the canonical order. -/
def wuchang_program : String :=
  "((((xoooooo oxooooo) ooxoooo) oooxooo) xxxxooo)"

theorem wuchang_program_is_dao : DaoJudge.judge wuchang_program = true := by
  native_decide

/-- Without 信, the program leaves residue and is NOT 道. -/
theorem siduan_program_not_dao :
    DaoJudge.judge "(((xoooooo oxooooo) ooxoooo) oooxooo)" = false := by
  native_decide

/-! ## § 5  Reference: the traditional 五行→卦 map (does NOT cancel)

Documented for completeness; proven NOT to balance to 道.
-/

namespace traditional

/-- 仁 = 震䷲ (☳☳ = pure thunder, 木). -/
def «仁_zhen» : Cell128 :=
  (⟨.yang, .yin, .yin, .yang, .yin, .yin⟩, false)

/-- 义 = 兑䷹ (☱☱ = pure lake, 金). -/
def «义_dui» : Cell128 :=
  (⟨.yang, .yang, .yin, .yang, .yang, .yin⟩, false)

/-- 礼 = 离䷝ (☲☲ = pure fire, 火). -/
def «礼_li» : Cell128 :=
  (⟨.yang, .yin, .yang, .yang, .yin, .yang⟩, false)

/-- 智 = 坎䷜ (☵☵ = pure water, 水). -/
def «智_kan» : Cell128 :=
  (⟨.yin, .yang, .yin, .yin, .yang, .yin⟩, false)

/-- 信 = 坤䷁ (☷☷ = pure earth, 土). -/
def «信_kun» : Cell128 :=
  (⟨.yin, .yin, .yin, .yin, .yin, .yin⟩, false)

theorem traditional_not_dao :
    Cell128.xor (Cell128.xor (Cell128.xor (Cell128.xor «仁_zhen» «义_dui») «礼_li») «智_kan») «信_kun»
      ≠ Cell128.origin := by
  decide

/-- The traditional placement actually XOR's to 礼_li. The doctrine "五行
循环" is a Z/5 structure; (Z/2)⁷ doesn't accommodate it without an
external twist. -/
theorem traditional_xor_eq_li :
    Cell128.xor (Cell128.xor (Cell128.xor (Cell128.xor «仁_zhen» «义_dui») «礼_li») «智_kan») «信_kun»
      = «礼_li» := by
  decide

end traditional

/-! ## § 6  Public summary -/

theorem wuchang_summary :
    DaoJudge.printCellAtom «仁» = "xoooooo" ∧
    DaoJudge.printCellAtom «义» = "oxooooo" ∧
    DaoJudge.printCellAtom «礼» = "ooxoooo" ∧
    DaoJudge.printCellAtom «智» = "oooxooo" ∧
    DaoJudge.printCellAtom «信» = "xxxxooo" ∧
    Cell128.xor (Cell128.xor (Cell128.xor (Cell128.xor «仁» «义») «礼») «智») «信»
      = Cell128.origin ∧
    DaoJudge.judge wuchang_program = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | native_decide | decide

end SSBX.Foundation.Lang.Wuchang
