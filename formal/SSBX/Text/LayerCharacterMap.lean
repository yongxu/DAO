/-
# LayerCharacterMap — 层级单字映射 (R1 → L0)

This file is the code-level source of truth for the recommended single-character
readings of each element and operator across the generation line (R1 → R5),
plus the L0 BaguaWen VM instructions.

It is a companion to:
- docs-next/10_formal_形式/layer-character-map.md (full analysis with备选 reasons)
- docs-next/10_formal_形式/layer-axis-graph.md (visual map, three-axis convergence)
- docs-next/10_formal_形式/root-layer-map.md (structural layer map)

## Principle

"字恰当高于冲突" — appropriate character beats conflict-avoidance. Where a
truly authoritative reading conflicts with another use, prefer the authoritative
reading and resolve via type/context.

## Coverage

* `Yao.essenceChar`            — R1 阳/阴 → 实/虚 (邵雍《观物外篇》)
* `SiXiang.seasonChar`         — R2 四象 → 春/夏/秋/冬 (邵雍先天图)
* `Trigram.virtueChar`         — R3 八卦 → 健/悦/显/起/入/险/止/顺 (说卦回归)
* `Trigram.literalChar`        — R3 八卦 → 乾/兑/离/震/巽/坎/艮/坤 (canonical)
* `flipPositionChar`           — R4 6 爻 flip → 改/化/变/临/主/极
* `ShiTransition.char`         — R5 shi 转换 → 迁/溯
* `YiInstrKind.modernAlias`    — L0 12 instructions → 静/置/翻/...

## Status

These are *recommended aliases*. The parser/Lex layer should accept them on top
of existing primary tokens (e.g., `不动` for `.nop`). Existing token paths in
`SSBX.Text.OperatorAnchors` are unchanged for backward compatibility.

The `allLayerChars` table at the bottom is a unified inspection point for the
interpreter — any future surface-alias parser should consult it as ground truth.
-/

import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Bagua.R8
import SSBX.Text.OperatorAnchors

/-! ## R1 — Yao essence (阳/阴 → 实/虚)

   邵雍《观物外篇》"阳为实，阴为虚"。
   这是 R1 (一处差异之两端) 的义理读法。 -/

namespace SSBX.Foundation.Yi.Yi.Yao

def essenceChar : Yao → String
  | .yang => "实"
  | .yin  => "虚"

def fromEssenceChar (s : String) : Option Yao :=
  if s = "实" then some .yang
  else if s = "虚" then some .yin
  else none

theorem essence_roundtrip (y : Yao) :
    fromEssenceChar y.essenceChar = some y := by
  cases y <;> rfl

end SSBX.Foundation.Yi.Yi.Yao

/-! ## R2 — SiXiang seasons (邵雍先天图四象配四时)

   邵雍《皇极经世》：
   - 太阳之时为夏
   - 少阴之时为秋
   - 少阳之时为春
   - 太阴之时为冬 -/

namespace SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang

open SSBX.Foundation.Yi.Yi

def seasonChar (s : SiXiang) : String :=
  if s = SiXiang.greaterYang then "夏"
  else if s = SiXiang.lesserYin then "秋"
  else if s = SiXiang.lesserYang then "春"
  else "冬"  -- greaterYin

def fromSeasonChar (s : String) : Option SiXiang :=
  if s = "夏" then some SiXiang.greaterYang
  else if s = "秋" then some SiXiang.lesserYin
  else if s = "春" then some SiXiang.lesserYang
  else if s = "冬" then some SiXiang.greaterYin
  else none

end SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang

/-! ## R3 — Trigram virtue (说卦传性德, conflict-aware substitutions)

   《说卦传》原文：乾健、坤顺、震动、巽入、坎陷、离丽、艮止、兑说也。

   本表对原文做三处替换以避免系统内冲突：
   - 震：动 → 起 (因 `motion` 已是 R3 flip y1 算子；《说卦》"震起"为次义)
   - 离：丽 → 显 (因 `丽` 与 30 卦撞名；`显` 与 Sheng.toTrigram manifest 同向)
   - 兑：说 → 悦 (现代汉字写法) -/

namespace SSBX.Foundation.Yi.Yi.Trigram

def virtueChar (t : Trigram) : String :=
  if t = heaven then "健"
  else if t = lake then "悦"
  else if t = fire then "显"
  else if t = thunder then "起"
  else if t = wind then "入"
  else if t = water then "险"
  else if t = mountain then "止"
  else "顺"  -- earth

def fromVirtueChar (s : String) : Option Trigram :=
  if s = "健" then some heaven
  else if s = "悦" then some lake
  else if s = "显" then some fire
  else if s = "起" then some thunder
  else if s = "入" then some wind
  else if s = "险" then some water
  else if s = "止" then some mountain
  else if s = "顺" then some earth
  else none

/-- Each trigram's canonical literal character (the trigram name itself). -/
def literalChar (t : Trigram) : String :=
  if t = heaven then "乾"
  else if t = lake then "兑"
  else if t = fire then "离"
  else if t = thunder then "震"
  else if t = wind then "巽"
  else if t = water then "坎"
  else if t = mountain then "艮"
  else "坤"

theorem virtue_roundtrip (t : Trigram) :
    fromVirtueChar t.virtueChar = some t := by
  rcases t with ⟨y1, y2, y3⟩
  cases y1 <;> cases y2 <;> cases y3 <;> rfl

end SSBX.Foundation.Yi.Yi.Trigram

/-! ## R4 — Hexagram 6-yao flip position chars

   六爻位翻转字: 改/化/变/临/主/极 (Fin 6, 0-indexed)

   - flip[0] (改) — 初爻 (与 R3 motion 一致)
   - flip[1] (化) — 二爻 (与 R3 middleFlip 一致)
   - flip[2] (变) — 三爻 (与 R3 topFlip 一致)
   - flip[3] (临) — 四爻 (近君位 / 临察；19 临卦同字)
   - flip[4] (主) — 五爻 (君位 / 主导；九五之尊)
   - flip[5] (极) — 上爻 (亢龙有悔之极位) -/

namespace SSBX.Text.LayerCharacterMap

def flipPositionChar : Fin 6 → String
  | ⟨0, _⟩ => "改"
  | ⟨1, _⟩ => "化"
  | ⟨2, _⟩ => "变"
  | ⟨3, _⟩ => "临"
  | ⟨4, _⟩ => "主"
  | ⟨5, _⟩ => "极"
  | ⟨n+6, h⟩ => absurd h (by omega)

def fromFlipPositionChar (s : String) : Option (Fin 6) :=
  if s = "改" then some ⟨0, by decide⟩
  else if s = "化" then some ⟨1, by decide⟩
  else if s = "变" then some ⟨2, by decide⟩
  else if s = "临" then some ⟨3, by decide⟩
  else if s = "主" then some ⟨4, by decide⟩
  else if s = "极" then some ⟨5, by decide⟩
  else none

theorem flipPosition_roundtrip (n : Fin 6) :
    fromFlipPositionChar (flipPositionChar n) = some n := by
  match n with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

end SSBX.Text.LayerCharacterMap

/-! ## R5 — Shi transition chars (迁 / 溯) -/

namespace SSBX.Text.LayerCharacterMap

inductive ShiTransition : Type
  | next  -- 迁: 已 → 今 → 未 → 已
  | prev  -- 溯: 已 ← 今 ← 未 ← 已
  deriving Repr, DecidableEq, BEq

namespace ShiTransition

open SSBX.Foundation.Bagua.R8

def char : ShiTransition → String
  | .next => "迁"
  | .prev => "溯"

def fromChar (s : String) : Option ShiTransition :=
  if s = "迁" then some .next
  else if s = "溯" then some .prev
  else none

/-- Apply a shi transition to a Shi value. Under V₄, both `.next` and `.prev`
    collapse to `Shi.complement` (V₄ involution = self-inverse). The legacy Z/3
    cycle (next^[3]=id) was replaced by complement^[2]=id. -/
def apply (t : ShiTransition) (s : Shi) : Shi :=
  match t with
  | .next => s.complement
  | .prev => s.complement

theorem char_roundtrip (t : ShiTransition) :
    fromChar t.char = some t := by
  cases t <;> rfl

end ShiTransition

end SSBX.Text.LayerCharacterMap

/-! ## L0 — Modern instruction aliases (静/置/翻/...)

   These are aliases on top of the existing `YiInstrKind.token` tokens
   (`不动 / 设时 / 翻爻 / 比爻 / 比时`), which remain unchanged. -/

namespace SSBX.Text.OperatorAnchors.YiInstrKind

def modernAlias : YiInstrKind → String
  | .nop          => "静"
  | .setShi       => "置"
  | .flipYao      => "翻"
  | .interlace           => "互"
  | .complement          => "错"
  | .reverse         => "综"
  | .branchYaoEq  => "侔"
  | .branchShiEq  => "会"
  | .jump         => "跳"
  | .push         => "推"
  | .pop          => "取"
  | .halt         => "终"

def fromModernAlias (s : String) : Option YiInstrKind :=
  if s = "静"      then some .nop
  else if s = "置" then some .setShi
  else if s = "翻" then some .flipYao
  else if s = "互" then some .interlace
  else if s = "错" then some .complement
  else if s = "综" then some .reverse
  else if s = "侔" then some .branchYaoEq
  else if s = "会" then some .branchShiEq
  else if s = "跳" then some .jump
  else if s = "推" then some .push
  else if s = "取" then some .pop
  else if s = "终" then some .halt
  else none

theorem modernAlias_roundtrip (k : YiInstrKind) :
    fromModernAlias k.modernAlias = some k := by
  cases k <;> rfl

end SSBX.Text.OperatorAnchors.YiInstrKind

namespace SSBX.Text.LayerCharacterMap

open SSBX.Text.OperatorAnchors

theorem allKinds_modernAliases_distinct :
    (yiInstrKinds.map YiInstrKind.modernAlias).Nodup := by
  native_decide

theorem allKinds_modernAliases_length_12 :
    (yiInstrKinds.map YiInstrKind.modernAlias).length = 12 := by
  native_decide

/-! ## Aggregate inspection table

   `allLayerChars` is the single ground-truth list for any future
   surface-alias parser. -/

structure LayerChar where
  layer  : String
  role   : String
  source : String
  char   : String
  deriving Repr

def allLayerChars : List LayerChar :=
  -- R1: yao essence (2)
  [ ⟨"R1", "essence", "Yao.yang",  "实"⟩
  , ⟨"R1", "essence", "Yao.yin",   "虚"⟩
  -- R2: sixiang seasons (4)
  , ⟨"R2", "season",  "SiXiang.greaterYang",  "夏"⟩
  , ⟨"R2", "season",  "SiXiang.lesserYin",  "秋"⟩
  , ⟨"R2", "season",  "SiXiang.lesserYang", "春"⟩
  , ⟨"R2", "season",  "SiXiang.greaterYin",   "冬"⟩
  -- R3: trigram virtues (8)
  , ⟨"R3", "virtue",  "Trigram.heaven", "健"⟩
  , ⟨"R3", "virtue",  "Trigram.lake",  "悦"⟩
  , ⟨"R3", "virtue",  "Trigram.fire",   "显"⟩
  , ⟨"R3", "virtue",  "Trigram.thunder", "起"⟩
  , ⟨"R3", "virtue",  "Trigram.wind",  "入"⟩
  , ⟨"R3", "virtue",  "Trigram.water",  "险"⟩
  , ⟨"R3", "virtue",  "Trigram.mountain",  "止"⟩
  , ⟨"R3", "virtue",  "Trigram.earth",  "顺"⟩
  -- R3: trigram literals (8)
  , ⟨"R3", "literal", "Trigram.heaven", "乾"⟩
  , ⟨"R3", "literal", "Trigram.lake",  "兑"⟩
  , ⟨"R3", "literal", "Trigram.fire",   "离"⟩
  , ⟨"R3", "literal", "Trigram.thunder", "震"⟩
  , ⟨"R3", "literal", "Trigram.wind",  "巽"⟩
  , ⟨"R3", "literal", "Trigram.water",  "坎"⟩
  , ⟨"R3", "literal", "Trigram.mountain",  "艮"⟩
  , ⟨"R3", "literal", "Trigram.earth",  "坤"⟩
  -- R4: 6-yao flip positions (6)
  , ⟨"R4", "flip", "flip[0]初爻", "改"⟩
  , ⟨"R4", "flip", "flip[1]二爻", "化"⟩
  , ⟨"R4", "flip", "flip[2]三爻", "变"⟩
  , ⟨"R4", "flip", "flip[3]四爻", "临"⟩
  , ⟨"R4", "flip", "flip[4]五爻", "主"⟩
  , ⟨"R4", "flip", "flip[5]上爻", "极"⟩
  -- R5: shi transitions (2)
  , ⟨"R5", "shi-transition", "ShiTransition.next", "迁"⟩
  , ⟨"R5", "shi-transition", "ShiTransition.prev", "溯"⟩
  -- L0: VM instruction aliases (12)
  , ⟨"L0", "instr", "YiInstrKind.nop",          "静"⟩
  , ⟨"L0", "instr", "YiInstrKind.setShi",       "置"⟩
  , ⟨"L0", "instr", "YiInstrKind.flipYao",      "翻"⟩
  , ⟨"L0", "instr", "YiInstrKind.interlace",           "互"⟩
  , ⟨"L0", "instr", "YiInstrKind.complement",          "错"⟩
  , ⟨"L0", "instr", "YiInstrKind.reverse",         "综"⟩
  , ⟨"L0", "instr", "YiInstrKind.branchYaoEq",  "侔"⟩
  , ⟨"L0", "instr", "YiInstrKind.branchShiEq",  "会"⟩
  , ⟨"L0", "instr", "YiInstrKind.jump",         "跳"⟩
  , ⟨"L0", "instr", "YiInstrKind.push",         "推"⟩
  , ⟨"L0", "instr", "YiInstrKind.pop",          "取"⟩
  , ⟨"L0", "instr", "YiInstrKind.halt",         "终"⟩
  ]

theorem allLayerChars_length : allLayerChars.length = 42 := by native_decide

/-- Filter by layer for inspection. -/
def charsForLayer (layer : String) : List LayerChar :=
  allLayerChars.filter (fun c => c.layer = layer)

theorem r1_chars_count : (charsForLayer "R1").length = 2  := by native_decide
theorem r2_chars_count : (charsForLayer "R2").length = 4  := by native_decide
theorem r3_chars_count : (charsForLayer "R3").length = 16 := by native_decide
theorem r4_chars_count : (charsForLayer "R4").length = 6  := by native_decide
theorem r5_chars_count : (charsForLayer "R5").length = 2  := by native_decide
theorem l0_chars_count : (charsForLayer "L0").length = 12 := by native_decide

end SSBX.Text.LayerCharacterMap
