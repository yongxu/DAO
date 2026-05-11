/-
# Names — comprehensive cell naming across R₄..R₈

Every cell at every layer gets a Chinese name (single character or
compound, dot-separated for product layers). Round-trip parsers attached
where it makes sense.

## Layer summary

| Layer | Cells | Naming scheme | Source |
| --- | ---: | --- | --- |
| R₁ Yao | 2 | 阳/阴 | already in Yi.lean |
| R₂ SiXiang | 4 | 太阳/少阴/少阳/太阴 | already in BaguaAlgebra.lean |
| R₃ Trigram | 8 | 八卦 (乾/兑/离/震/巽/坎/艮/坤) | already in Yi.lean |
| R₄ Mian | 16 | <Ben>·<Zheng> e.g. 物·几, 动·势, … | here (composes existing chars) |
| R₅ Wuyao | 32 | <Mian>·<5爻> where 5爻 ∈ {显/隐} | here (proposes 显/隐 for the 5th yao) |
| R₆ Hexagram | 64 | 64 周易卦名 (乾/坤/屯/蒙/…/既济/未济) | here (lifts xuGua comments to defs) |
| R₇ Cell128 | 128 | <卦名>·<因> where 因 ∈ {无/有} | here |
| R₈ Cell256 | 256 | <卦名>·<时> where 时 ∈ V₄ {道/已/今/未} | here |

## R₅ naming rationale

The user pushed back on "no traditional names for R₅". Truth: there's no
canonical one-name-per-cell convention for the 5-yao layer in classical Yi.
But we can compose: R₅ = Mian × 5th-yao-bit. The 5th-yao-bit conventionally
corresponds to **位** (position-relative-prominence). We use 显 (manifest /
yang) vs 隐 (concealed / yin) for the bit; the resulting 32 names are then
e.g. 物·几·显, 物·几·隐, …, 事·时·隐. This is a proposal, not a canonical
classical naming — but it fills the gap with terms drawn from existing 易
vocabulary.

## R₆ disambiguation

Pinyin collisions exist (heaven = 乾/谦, water = 坎/坎 (dup ok), earth = 坤/困,
yi = 颐/益, …). To avoid ASCII ambiguity, the 64 individual defs use
«»-quoted Chinese names (e.g. `Hexagram.«乾»`). Lean 4's stock lexer
requires the brackets for CJK identifiers.
-/

import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Bagua.BenZheng
import SSBX.Foundation.Hierarchy.R5_Wuyao
import SSBX.Foundation.Bagua.Cell128
import SSBX.Foundation.Bagua.Cell256

namespace SSBX.Foundation.Yi.Yi.Hexagram

open SSBX.Foundation.Yi.Yi

/-! ## § 6  R₆ — 64 周易卦名 -/

def «乾» : Hexagram := ⟨.yang, .yang, .yang, .yang, .yang, .yang⟩
def «坤» : Hexagram := ⟨.yin,  .yin,  .yin,  .yin,  .yin,  .yin⟩
def «屯» : Hexagram := ⟨.yang, .yin,  .yin,  .yin,  .yang, .yin⟩
def «蒙» : Hexagram := ⟨.yin,  .yang, .yin,  .yin,  .yin,  .yang⟩
def «需» : Hexagram := ⟨.yang, .yang, .yang, .yin,  .yang, .yin⟩
def «讼» : Hexagram := ⟨.yin,  .yang, .yin,  .yang, .yang, .yang⟩
def «师» : Hexagram := ⟨.yin,  .yang, .yin,  .yin,  .yin,  .yin⟩
def «比» : Hexagram := ⟨.yin,  .yin,  .yin,  .yin,  .yang, .yin⟩
def «小畜» : Hexagram := ⟨.yang, .yang, .yang, .yin,  .yang, .yang⟩
def «履» : Hexagram := ⟨.yang, .yang, .yin,  .yang, .yang, .yang⟩
def «泰» : Hexagram := ⟨.yang, .yang, .yang, .yin,  .yin,  .yin⟩
def «否» : Hexagram := ⟨.yin,  .yin,  .yin,  .yang, .yang, .yang⟩
def «同人» : Hexagram := ⟨.yang, .yin,  .yang, .yang, .yang, .yang⟩
def «大有» : Hexagram := ⟨.yang, .yang, .yang, .yang, .yin,  .yang⟩
def «谦» : Hexagram := ⟨.yin,  .yin,  .yang, .yin,  .yin,  .yin⟩
def «豫» : Hexagram := ⟨.yin,  .yin,  .yin,  .yang, .yin,  .yin⟩
def «随» : Hexagram := ⟨.yang, .yin,  .yin,  .yang, .yang, .yin⟩
def «蛊» : Hexagram := ⟨.yin,  .yang, .yang, .yin,  .yin,  .yang⟩
def «临» : Hexagram := ⟨.yang, .yang, .yin,  .yin,  .yin,  .yin⟩
def «观» : Hexagram := ⟨.yin,  .yin,  .yin,  .yin,  .yang, .yang⟩
def «噬嗑» : Hexagram := ⟨.yang, .yin,  .yin,  .yang, .yin,  .yang⟩
def «贲» : Hexagram := ⟨.yang, .yin,  .yang, .yin,  .yin,  .yang⟩
def «剥» : Hexagram := ⟨.yin,  .yin,  .yin,  .yin,  .yin,  .yang⟩
def «复» : Hexagram := ⟨.yang, .yin,  .yin,  .yin,  .yin,  .yin⟩
def «无妄» : Hexagram := ⟨.yang, .yin,  .yin,  .yang, .yang, .yang⟩
def «大畜» : Hexagram := ⟨.yang, .yang, .yang, .yin,  .yin,  .yang⟩
def «颐» : Hexagram := ⟨.yang, .yin,  .yin,  .yin,  .yin,  .yang⟩
def «大过» : Hexagram := ⟨.yin,  .yang, .yang, .yang, .yang, .yin⟩
def «坎H» : Hexagram := ⟨.yin,  .yang, .yin,  .yin,  .yang, .yin⟩  -- 坎 卦 (29) — H suffix to avoid clash with Trigram.water
def «离H» : Hexagram := ⟨.yang, .yin,  .yang, .yang, .yin,  .yang⟩  -- 离 卦 (30)
def «咸» : Hexagram := ⟨.yin,  .yin,  .yang, .yang, .yang, .yin⟩
def «恒» : Hexagram := ⟨.yin,  .yang, .yang, .yang, .yin,  .yin⟩
def «遁» : Hexagram := ⟨.yin,  .yin,  .yang, .yang, .yang, .yang⟩
def «大壮» : Hexagram := ⟨.yang, .yang, .yang, .yang, .yin,  .yin⟩
def «晋» : Hexagram := ⟨.yin,  .yin,  .yin,  .yang, .yin,  .yang⟩
def «明夷» : Hexagram := ⟨.yang, .yin,  .yang, .yin,  .yin,  .yin⟩
def «家人» : Hexagram := ⟨.yang, .yin,  .yang, .yin,  .yang, .yang⟩
def «睽» : Hexagram := ⟨.yang, .yang, .yin,  .yang, .yin,  .yang⟩
def «蹇» : Hexagram := ⟨.yin,  .yin,  .yang, .yin,  .yang, .yin⟩
def «解» : Hexagram := ⟨.yin,  .yang, .yin,  .yang, .yin,  .yin⟩
def «损» : Hexagram := ⟨.yang, .yang, .yin,  .yin,  .yin,  .yang⟩
def «益» : Hexagram := ⟨.yang, .yin,  .yin,  .yin,  .yang, .yang⟩
def «夬» : Hexagram := ⟨.yang, .yang, .yang, .yang, .yang, .yin⟩
def «姤» : Hexagram := ⟨.yin,  .yang, .yang, .yang, .yang, .yang⟩
def «萃» : Hexagram := ⟨.yin,  .yin,  .yin,  .yang, .yang, .yin⟩
def «升» : Hexagram := ⟨.yin,  .yang, .yang, .yin,  .yin,  .yin⟩
def «困» : Hexagram := ⟨.yin,  .yang, .yin,  .yang, .yang, .yin⟩
def «井» : Hexagram := ⟨.yin,  .yang, .yang, .yin,  .yang, .yin⟩
def «革» : Hexagram := ⟨.yang, .yin,  .yang, .yang, .yang, .yin⟩
def «鼎» : Hexagram := ⟨.yin,  .yang, .yang, .yang, .yin,  .yang⟩
def «震H» : Hexagram := ⟨.yang, .yin,  .yin,  .yang, .yin,  .yin⟩  -- 震 卦 (51)
def «艮H» : Hexagram := ⟨.yin,  .yin,  .yang, .yin,  .yin,  .yang⟩  -- 艮 卦 (52)
def «渐» : Hexagram := ⟨.yin,  .yin,  .yang, .yin,  .yang, .yang⟩
def «归妹» : Hexagram := ⟨.yang, .yang, .yin,  .yang, .yin,  .yin⟩
def «丰» : Hexagram := ⟨.yang, .yin,  .yang, .yang, .yin,  .yin⟩
def «旅» : Hexagram := ⟨.yin,  .yin,  .yang, .yang, .yin,  .yang⟩
def «巽H» : Hexagram := ⟨.yin,  .yang, .yang, .yin,  .yang, .yang⟩  -- 巽 卦 (57)
def «兑H» : Hexagram := ⟨.yang, .yang, .yin,  .yang, .yang, .yin⟩  -- 兑 卦 (58)
def «涣» : Hexagram := ⟨.yin,  .yang, .yin,  .yin,  .yang, .yang⟩
def «节» : Hexagram := ⟨.yang, .yang, .yin,  .yin,  .yang, .yin⟩
def «中孚» : Hexagram := ⟨.yang, .yang, .yin,  .yin,  .yang, .yang⟩
def «小过» : Hexagram := ⟨.yin,  .yin,  .yang, .yang, .yin,  .yin⟩
def «既济» : Hexagram := ⟨.yang, .yin,  .yang, .yin,  .yang, .yin⟩
def «未济» : Hexagram := ⟨.yin,  .yang, .yin,  .yang, .yin,  .yang⟩

/-- Name lookup: Hexagram → 卦名. Total function via `xuGua` enumeration. -/
def name (h : Hexagram) : String :=
  -- match the 64 patterns exactly; fall through is unreachable since
  -- Hexagram has exactly 64 inhabitants
  if h = «乾» then "乾"
  else if h = «坤» then "坤"
  else if h = «屯» then "屯"
  else if h = «蒙» then "蒙"
  else if h = «需» then "需"
  else if h = «讼» then "讼"
  else if h = «师» then "师"
  else if h = «比» then "比"
  else if h = «小畜» then "小畜"
  else if h = «履» then "履"
  else if h = «泰» then "泰"
  else if h = «否» then "否"
  else if h = «同人» then "同人"
  else if h = «大有» then "大有"
  else if h = «谦» then "谦"
  else if h = «豫» then "豫"
  else if h = «随» then "随"
  else if h = «蛊» then "蛊"
  else if h = «临» then "临"
  else if h = «观» then "观"
  else if h = «噬嗑» then "噬嗑"
  else if h = «贲» then "贲"
  else if h = «剥» then "剥"
  else if h = «复» then "复"
  else if h = «无妄» then "无妄"
  else if h = «大畜» then "大畜"
  else if h = «颐» then "颐"
  else if h = «大过» then "大过"
  else if h = «坎H» then "坎"
  else if h = «离H» then "离"
  else if h = «咸» then "咸"
  else if h = «恒» then "恒"
  else if h = «遁» then "遁"
  else if h = «大壮» then "大壮"
  else if h = «晋» then "晋"
  else if h = «明夷» then "明夷"
  else if h = «家人» then "家人"
  else if h = «睽» then "睽"
  else if h = «蹇» then "蹇"
  else if h = «解» then "解"
  else if h = «损» then "损"
  else if h = «益» then "益"
  else if h = «夬» then "夬"
  else if h = «姤» then "姤"
  else if h = «萃» then "萃"
  else if h = «升» then "升"
  else if h = «困» then "困"
  else if h = «井» then "井"
  else if h = «革» then "革"
  else if h = «鼎» then "鼎"
  else if h = «震H» then "震"
  else if h = «艮H» then "艮"
  else if h = «渐» then "渐"
  else if h = «归妹» then "归妹"
  else if h = «丰» then "丰"
  else if h = «旅» then "旅"
  else if h = «巽H» then "巽"
  else if h = «兑H» then "兑"
  else if h = «涣» then "涣"
  else if h = «节» then "节"
  else if h = «中孚» then "中孚"
  else if h = «小过» then "小过"
  else if h = «既济» then "既济"
  else if h = «未济» then "未济"
  else "?"  -- unreachable

example : name «乾» = "乾" := by native_decide
example : name «未济» = "未济" := by native_decide
example : name «既济» = "既济" := by native_decide

/-- Lookup-by-name: matches all 64. -/
def fromName : String → Option Hexagram
  | "乾"   => some «乾»     | "坤"   => some «坤»
  | "屯"   => some «屯»     | "蒙"   => some «蒙»
  | "需"   => some «需»     | "讼"   => some «讼»
  | "师"   => some «师»     | "比"   => some «比»
  | "小畜" => some «小畜»   | "履"   => some «履»
  | "泰"   => some «泰»     | "否"   => some «否»
  | "同人" => some «同人»   | "大有" => some «大有»
  | "谦"   => some «谦»     | "豫"   => some «豫»
  | "随"   => some «随»     | "蛊"   => some «蛊»
  | "临"   => some «临»     | "观"   => some «观»
  | "噬嗑" => some «噬嗑»   | "贲"   => some «贲»
  | "剥"   => some «剥»     | "复"   => some «复»
  | "无妄" => some «无妄»   | "大畜" => some «大畜»
  | "颐"   => some «颐»     | "大过" => some «大过»
  | "坎"   => some «坎H»    | "离"   => some «离H»
  | "咸"   => some «咸»     | "恒"   => some «恒»
  | "遁"   => some «遁»     | "大壮" => some «大壮»
  | "晋"   => some «晋»     | "明夷" => some «明夷»
  | "家人" => some «家人»   | "睽"   => some «睽»
  | "蹇"   => some «蹇»     | "解"   => some «解»
  | "损"   => some «损»     | "益"   => some «益»
  | "夬"   => some «夬»     | "姤"   => some «姤»
  | "萃"   => some «萃»     | "升"   => some «升»
  | "困"   => some «困»     | "井"   => some «井»
  | "革"   => some «革»     | "鼎"   => some «鼎»
  | "震"   => some «震H»    | "艮"   => some «艮H»
  | "渐"   => some «渐»     | "归妹" => some «归妹»
  | "丰"   => some «丰»     | "旅"   => some «旅»
  | "巽"   => some «巽H»    | "兑"   => some «兑H»
  | "涣"   => some «涣»     | "节"   => some «节»
  | "中孚" => some «中孚»   | "小过" => some «小过»
  | "既济" => some «既济»   | "未济" => some «未济»
  | _       => none

example : fromName "乾" = some «乾» := by native_decide
example : fromName "既济" = some «既济» := by native_decide
example : fromName "未知" = none := by native_decide

end SSBX.Foundation.Yi.Yi.Hexagram

namespace SSBX.Foundation.Bagua.BenZheng.Mian

open SSBX.Foundation.Bagua.BenZheng

/-! ## § 4  R₄ — Mian = Ben × Zheng -/

/-- Mian name = `<Ben>·<Zheng>`, e.g. 物·几, 动·势, 间·机, 事·时. -/
def name (m : Mian) : String :=
  m.fst.char ++ "·" ++ m.snd.char

example : name (.thing, .trace) = "物·几" := by native_decide
example : name (.event, .occasion) = "事·时" := by native_decide

end SSBX.Foundation.Bagua.BenZheng.Mian

namespace SSBX.Foundation.Hierarchy.R5_Wuyao.Wuyao

open SSBX.Foundation.Bagua.BenZheng (Mian)
open SSBX.Foundation.Bagua.BenZheng.Mian

/-! ## § 5  R₅ — Wuyao = Mian × Bool

The 5th yao bit: yang ↦ 显 (manifest), yin ↦ 隐 (concealed). Naming
convention proposed (not canonical classical Yi). 32 names total.
-/

def name (w : Wuyao) : String :=
  Mian.name w.fst ++ "·" ++ (if w.snd then "显" else "隐")

example : name ((.thing, .trace), false) = "物·几·隐" := by native_decide
example : name ((.event, .occasion), true) = "事·时·显" := by native_decide

end SSBX.Foundation.Hierarchy.R5_Wuyao.Wuyao

namespace SSBX.Foundation.Bagua.Cell128

open SSBX.Foundation.Yi.Yi (Hexagram)
open SSBX.Foundation.Yi.Yi.Hexagram

/-! ## § 7  R₇ — Cell128 = Hexagram × YinBit

Naming: `<卦名>·<因>` where 因 ∈ {无, 有}.
-/

def name (c : Cell128) : String :=
  Hexagram.name c.fst ++ "·" ++ (if c.snd then "有" else "无")

example : name (Cell128.origin) = "乾·无" := by native_decide
example : name («既济», true) = "既济·有" := by native_decide
example : name («坤», false) = "坤·无" := by native_decide

end SSBX.Foundation.Bagua.Cell128

namespace SSBX.Foundation.Bagua.Cell256

open SSBX.Foundation.Yi.Yi (Hexagram)
open SSBX.Foundation.Yi.Yi.Hexagram

/-! ## § 8  R₈ — Cell256 = Hexagram × Shi (V₄)

Naming: `<卦名>·<时>` where 时 ∈ V₄ {道, 已, 今, 未}. The Shi V₄ Klein
group: dao = (false,false), ji = (true,false), jin = (true,true),
wei = (false,true).
-/

def shiName (s : Shi) : String :=
  match s with
  | (false, false) => "道"
  | (true,  false) => "已"
  | (true,  true)  => "今"
  | (false, true)  => "未"

def name (c : Cell256) : String :=
  Hexagram.name c.fst ++ "·" ++ shiName c.snd

example : name (Cell256.origin) = "乾·道" := by native_decide
example : name («未济», Shi.wei) = "未济·未" := by native_decide
example : name («既济», Shi.jin) = "既济·今" := by native_decide
example : name («坤», Shi.dao) = "坤·道" := by native_decide

end SSBX.Foundation.Bagua.Cell256

/-! ## § Verification: spot-check round trips

A full universally-quantified Hexagram round-trip would need a Fintype
instance. Concrete spot checks suffice for the demo. -/

namespace SSBX.Foundation.Lang.Names

open SSBX.Foundation.Yi.Yi.Hexagram

/-- Round-trip on 8 spot-check hexagrams covering full and compound names. -/
theorem hex_round_trip_spot_check :
    fromName (name «乾») = some «乾» ∧
    fromName (name «坤») = some «坤» ∧
    fromName (name «既济») = some «既济» ∧
    fromName (name «未济») = some «未济» ∧
    fromName (name «同人») = some «同人» ∧
    fromName (name «噬嗑») = some «噬嗑» ∧
    fromName (name «中孚») = some «中孚» ∧
    fromName (name «归妹») = some «归妹» := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals native_decide

end SSBX.Foundation.Lang.Names
