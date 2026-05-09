/-
# LayerCharacterMap — 层级单字映射 (R1 → L0 + Rh 16-grid)

Code-level ground truth for character readings across all generation/structure
layers. Companion to:
- docs-next/10_formal_形式/layer-character-map.md
- docs-next/10_formal_形式/sanben-sijieduan-grid.md
- docs-next/10_formal_形式/64-hexagram-grid.md

## Coverage

* R1 — Yao essence (实/虚)
* R2 — SiXiang seasons (春/夏/秋/冬)
* R3 — Trigram virtue (健/悦/显/起/入/险/止/顺) via Virtue.displayChar
* R3 — Trigram literal (乾/兑/离/震/巽/坎/艮/坤)
* R4 — 6-yao flip (改/化/变/临/主/极)
* R5 — Shi transitions (迁/溯)
* L0 — VM instruction aliases (静/置/翻/互/错/综/侔/会/跳/推/取/终)
* Rh — Ben/Zheng/Mian (4+4+16 = 24 chars from BenZheng.lean)

Total: 2 + 4 + 8 + 8 + 6 + 2 + 12 + 4 + 4 + 16 = 66 entries
-/
import SSBX.Foundation.Bagua.BenZheng
import SSBX.Foundation.Bagua.Cell192
import SSBX.Text.OperatorAnchors

-- All Trigram/Yao/Hexagram extensions are at top-level (NOT inside LayerCharacterMap).
-- LayerCharacterMap namespace is reserved for the inspection table at the end.

/-! ## R1 — Yao essence (阳/阴 → 实/虚) -/

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

/-! ## R2 — SiXiang seasons (邵雍先天图四时) -/

namespace SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang

def seasonChar (s : SiXiang) : String :=
  if s = SiXiang.taiYang then "夏"
  else if s = SiXiang.shaoYin then "秋"
  else if s = SiXiang.shaoYang then "春"
  else "冬"

def fromSeasonChar (s : String) : Option SiXiang :=
  if s = "夏" then some SiXiang.taiYang
  else if s = "秋" then some SiXiang.shaoYin
  else if s = "春" then some SiXiang.shaoYang
  else if s = "冬" then some SiXiang.taiYin
  else none

end SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang

/-! ## R3 — Trigram literal char (8 canonical names) -/

namespace SSBX.Foundation.Yi.Yi.Trigram

def literalChar (t : Trigram) : String :=
  if t = qian then "乾"
  else if t = dui then "兑"
  else if t = li then "离"
  else if t = zhen then "震"
  else if t = xun then "巽"
  else if t = kan then "坎"
  else if t = gen then "艮"
  else "坤"

def fromLiteralChar (s : String) : Option Trigram :=
  if s = "乾" then some qian
  else if s = "兑" || s = "兌" then some dui
  else if s = "离" || s = "離" then some li
  else if s = "震" then some zhen
  else if s = "巽" then some xun
  else if s = "坎" then some kan
  else if s = "艮" then some gen
  else if s = "坤" then some kun
  else none

end SSBX.Foundation.Yi.Yi.Trigram

/-! ## R3 — Trigram virtue (via Virtue.displayChar)

   Note: Trigram → Virtue → displayChar 链路。
   `Trigram.virtue` 在 Yi.lean 已定义；`Virtue.displayChar` 也在 Yi.lean. -/

namespace SSBX.Foundation.Yi.Yi.Trigram

/-- Convenience: trigram virtue char in one step. -/
def virtueChar (t : Trigram) : String := t.virtue.displayChar

def fromVirtueChar (s : String) : Option Trigram :=
  if s = "健" then some qian
  else if s = "悦" then some dui
  else if s = "显" then some li
  else if s = "起" then some zhen
  else if s = "入" then some xun
  else if s = "险" then some kan
  else if s = "止" then some gen
  else if s = "顺" then some kun
  else none

theorem virtue_roundtrip (t : Trigram) :
    fromVirtueChar t.virtueChar = some t := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;> rfl

end SSBX.Foundation.Yi.Yi.Trigram

/-! ## R4 — 6-yao flip position chars (改/化/变/临/主/极)

   These live in the LayerCharacterMap namespace as standalone helpers. -/

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
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl

end SSBX.Text.LayerCharacterMap

/-! ## R5 — Shi transitions (迁/溯) -/

namespace SSBX.Text.LayerCharacterMap

open SSBX.Foundation.Bagua.Cell192

inductive ShiTransition : Type
  | next  -- 迁
  | prev  -- 溯
  deriving Repr, DecidableEq, BEq

namespace ShiTransition

def char : ShiTransition → String
  | .next => "迁"
  | .prev => "溯"

def fromChar (s : String) : Option ShiTransition :=
  if s = "迁" then some .next
  else if s = "溯" then some .prev
  else none

def apply (t : ShiTransition) (s : Shi) : Shi :=
  match t with
  | .next => s.next
  | .prev => s.prev

theorem char_roundtrip (t : ShiTransition) :
    fromChar t.char = some t := by
  cases t <;> rfl

end ShiTransition

end SSBX.Text.LayerCharacterMap

/-! ## L0 — VM instruction modern aliases (静/置/翻/互/错/综/侔/会/跳/推/取/终) -/

namespace SSBX.Text.OperatorAnchors.YiInstrKind

def modernAlias : YiInstrKind → String
  | .nop          => "静"
  | .setShi       => "置"
  | .flipYao      => "翻"
  | .hu           => "互"
  | .cuo          => "错"
  | .zong         => "综"
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
  else if s = "互" then some .hu
  else if s = "错" then some .cuo
  else if s = "综" then some .zong
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

/-! ## Rh — Ben/Zheng/Mian fromChar (chars 与 char 已在 BenZheng.lean 定义) -/

-- Ben.fromChar、Zheng.fromChar、Mian.label 已在 BenZheng.lean 定义。
-- 此处不重复，仅引入到 LayerCharacterMap 的 inspection table。

/-! ## Aggregate inspection table -/

namespace SSBX.Text.LayerCharacterMap

structure LayerChar where
  layer  : String
  role   : String
  source : String
  char   : String
  deriving Repr

def allLayerChars : List LayerChar :=
  -- R1 (2)
  [ ⟨"R1", "essence", "Yao.yang",  "实"⟩
  , ⟨"R1", "essence", "Yao.yin",   "虚"⟩
  -- R2 (4)
  , ⟨"R2", "season",  "SiXiang.taiYang",  "夏"⟩
  , ⟨"R2", "season",  "SiXiang.shaoYin",  "秋"⟩
  , ⟨"R2", "season",  "SiXiang.shaoYang", "春"⟩
  , ⟨"R2", "season",  "SiXiang.taiYin",   "冬"⟩
  -- R3 virtue (8)
  , ⟨"R3", "virtue",  "Trigram.qian", "健"⟩
  , ⟨"R3", "virtue",  "Trigram.dui",  "悦"⟩
  , ⟨"R3", "virtue",  "Trigram.li",   "显"⟩
  , ⟨"R3", "virtue",  "Trigram.zhen", "起"⟩
  , ⟨"R3", "virtue",  "Trigram.xun",  "入"⟩
  , ⟨"R3", "virtue",  "Trigram.kan",  "险"⟩
  , ⟨"R3", "virtue",  "Trigram.gen",  "止"⟩
  , ⟨"R3", "virtue",  "Trigram.kun",  "顺"⟩
  -- R3 literal (8)
  , ⟨"R3", "literal", "Trigram.qian", "乾"⟩
  , ⟨"R3", "literal", "Trigram.dui",  "兑"⟩
  , ⟨"R3", "literal", "Trigram.li",   "离"⟩
  , ⟨"R3", "literal", "Trigram.zhen", "震"⟩
  , ⟨"R3", "literal", "Trigram.xun",  "巽"⟩
  , ⟨"R3", "literal", "Trigram.kan",  "坎"⟩
  , ⟨"R3", "literal", "Trigram.gen",  "艮"⟩
  , ⟨"R3", "literal", "Trigram.kun",  "坤"⟩
  -- R4 flip (6)
  , ⟨"R4", "flip", "flip[0]初爻", "改"⟩
  , ⟨"R4", "flip", "flip[1]二爻", "化"⟩
  , ⟨"R4", "flip", "flip[2]三爻", "变"⟩
  , ⟨"R4", "flip", "flip[3]四爻", "临"⟩
  , ⟨"R4", "flip", "flip[4]五爻", "主"⟩
  , ⟨"R4", "flip", "flip[5]上爻", "极"⟩
  -- R5 (2)
  , ⟨"R5", "shi-transition", "ShiTransition.next", "迁"⟩
  , ⟨"R5", "shi-transition", "ShiTransition.prev", "溯"⟩
  -- L0 (12)
  , ⟨"L0", "instr", "YiInstrKind.nop",          "静"⟩
  , ⟨"L0", "instr", "YiInstrKind.setShi",       "置"⟩
  , ⟨"L0", "instr", "YiInstrKind.flipYao",      "翻"⟩
  , ⟨"L0", "instr", "YiInstrKind.hu",           "互"⟩
  , ⟨"L0", "instr", "YiInstrKind.cuo",          "错"⟩
  , ⟨"L0", "instr", "YiInstrKind.zong",         "综"⟩
  , ⟨"L0", "instr", "YiInstrKind.branchYaoEq",  "侔"⟩
  , ⟨"L0", "instr", "YiInstrKind.branchShiEq",  "会"⟩
  , ⟨"L0", "instr", "YiInstrKind.jump",         "跳"⟩
  , ⟨"L0", "instr", "YiInstrKind.push",         "推"⟩
  , ⟨"L0", "instr", "YiInstrKind.pop",          "取"⟩
  , ⟨"L0", "instr", "YiInstrKind.halt",         "终"⟩
  -- Rh: Ben (4)
  , ⟨"Rh", "ben", "Ben.wu",   "物"⟩
  , ⟨"Rh", "ben", "Ben.dong", "动"⟩
  , ⟨"Rh", "ben", "Ben.jian", "间"⟩
  , ⟨"Rh", "ben", "Ben.shi",  "事"⟩
  -- Rh: Zheng (4)
  , ⟨"Rh", "zheng", "Zheng.jiFaint",    "几"⟩
  , ⟨"Rh", "zheng", "Zheng.shiForce",   "势"⟩
  , ⟨"Rh", "zheng", "Zheng.jiOccasion", "机"⟩
  , ⟨"Rh", "zheng", "Zheng.shiTime",    "时"⟩
  -- Rh: Mian 16-grid (16)
  , ⟨"Rh", "mian", "(物,几)", "动"⟩
  , ⟨"Rh", "mian", "(物,势)", "行"⟩
  , ⟨"Rh", "mian", "(物,机)", "化"⟩
  , ⟨"Rh", "mian", "(物,时)", "流"⟩
  , ⟨"Rh", "mian", "(动,几)", "萌"⟩
  , ⟨"Rh", "mian", "(动,势)", "长"⟩
  , ⟨"Rh", "mian", "(动,机)", "发"⟩
  , ⟨"Rh", "mian", "(动,时)", "续"⟩
  , ⟨"Rh", "mian", "(间,几)", "缘"⟩
  , ⟨"Rh", "mian", "(间,势)", "通"⟩
  , ⟨"Rh", "mian", "(间,机)", "会"⟩
  , ⟨"Rh", "mian", "(间,时)", "系"⟩
  , ⟨"Rh", "mian", "(事,几)", "兆"⟩
  , ⟨"Rh", "mian", "(事,势)", "趋"⟩
  , ⟨"Rh", "mian", "(事,机)", "变"⟩
  , ⟨"Rh", "mian", "(事,时)", "史"⟩
  ]

theorem allLayerChars_length : allLayerChars.length = 66 := by native_decide

def charsForLayer (layer : String) : List LayerChar :=
  allLayerChars.filter (fun c => c.layer = layer)

theorem r1_chars_count : (charsForLayer "R1").length = 2  := by native_decide
theorem r2_chars_count : (charsForLayer "R2").length = 4  := by native_decide
theorem r3_chars_count : (charsForLayer "R3").length = 16 := by native_decide
theorem r4_chars_count : (charsForLayer "R4").length = 6  := by native_decide
theorem r5_chars_count : (charsForLayer "R5").length = 2  := by native_decide
theorem l0_chars_count : (charsForLayer "L0").length = 12 := by native_decide
theorem rh_chars_count : (charsForLayer "Rh").length = 24 := by native_decide

end SSBX.Text.LayerCharacterMap
