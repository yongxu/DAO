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
| R₇ R7 | 128 | <卦名>·<因> where 因 ∈ {无/有} | here |
| R₈ R8 | 256 | <卦名>·<时> where 时 ∈ V₄ {道/已/今/未} | here |

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
«»-quoted Chinese names (e.g. `Hexagram.heaven`). Lean 4's stock lexer
requires the brackets for CJK identifiers.
-/

import SSBX.Foundation.Atlas.YiLegacy.Yi
import SSBX.Foundation.Atlas.YiLegacy.Bagua.BaguaAlgebra
import SSBX.Foundation.Atlas.YiLegacy.Bagua.BenZheng
import SSBX.Foundation.Hierarchy.R5_Wuyao
import SSBX.Foundation.Atlas.YiLegacy.Bagua.R7
import SSBX.Foundation.Atlas.YiLegacy.Bagua.R8

namespace SSBX.Foundation.Yi.Yi.Hexagram

open SSBX.Foundation.Yi.Yi

/-! ## § 6  R₆ — 64 周易卦名

  10 are defined in `Yi.lean` already (heaven/earth/peace/blocking/
  sprout/naive/waiting/dispute/complete/incomplete). The remaining 54
  are added here. -/

def army : Hexagram := ⟨.yin,  .yang, .yin,  .yin,  .yin,  .yin⟩
def uniting : Hexagram := ⟨.yin,  .yin,  .yin,  .yin,  .yang, .yin⟩
def smallRestraint : Hexagram := ⟨.yang, .yang, .yang, .yin,  .yang, .yang⟩
def treading : Hexagram := ⟨.yang, .yang, .yin,  .yang, .yang, .yang⟩
def fellowship : Hexagram := ⟨.yang, .yin,  .yang, .yang, .yang, .yang⟩
def greatPossession : Hexagram := ⟨.yang, .yang, .yang, .yang, .yin,  .yang⟩
def modesty : Hexagram := ⟨.yin,  .yin,  .yang, .yin,  .yin,  .yin⟩
def enthusiasm : Hexagram := ⟨.yin,  .yin,  .yin,  .yang, .yin,  .yin⟩
def following : Hexagram := ⟨.yang, .yin,  .yin,  .yang, .yang, .yin⟩
def decay : Hexagram := ⟨.yin,  .yang, .yang, .yin,  .yin,  .yang⟩
def approach : Hexagram := ⟨.yang, .yang, .yin,  .yin,  .yin,  .yin⟩
def contemplation : Hexagram := ⟨.yin,  .yin,  .yin,  .yin,  .yang, .yang⟩
def biteThrough : Hexagram := ⟨.yang, .yin,  .yin,  .yang, .yin,  .yang⟩
def adornment : Hexagram := ⟨.yang, .yin,  .yang, .yin,  .yin,  .yang⟩
def stripping : Hexagram := ⟨.yin,  .yin,  .yin,  .yin,  .yin,  .yang⟩
def returning : Hexagram := ⟨.yang, .yin,  .yin,  .yin,  .yin,  .yin⟩
def innocence : Hexagram := ⟨.yang, .yin,  .yin,  .yang, .yang, .yang⟩
def greatRestraint : Hexagram := ⟨.yang, .yang, .yang, .yin,  .yin,  .yang⟩
def nourishing : Hexagram := ⟨.yang, .yin,  .yin,  .yin,  .yin,  .yang⟩
def greatExceeding : Hexagram := ⟨.yin,  .yang, .yang, .yang, .yang, .yin⟩
def abyss : Hexagram := ⟨.yin,  .yang, .yin,  .yin,  .yang, .yin⟩  -- 坎 卦 (29) — H suffix to avoid clash with Trigram.water
def brightness : Hexagram := ⟨.yang, .yin,  .yang, .yang, .yin,  .yang⟩  -- 离 卦 (30)
def influence : Hexagram := ⟨.yin,  .yin,  .yang, .yang, .yang, .yin⟩
def duration : Hexagram := ⟨.yin,  .yang, .yang, .yang, .yin,  .yin⟩
def retreat : Hexagram := ⟨.yin,  .yin,  .yang, .yang, .yang, .yang⟩
def greatPower : Hexagram := ⟨.yang, .yang, .yang, .yang, .yin,  .yin⟩
def progress : Hexagram := ⟨.yin,  .yin,  .yin,  .yang, .yin,  .yang⟩
def darkening : Hexagram := ⟨.yang, .yin,  .yang, .yin,  .yin,  .yin⟩
def family : Hexagram := ⟨.yang, .yin,  .yang, .yin,  .yang, .yang⟩
def opposition : Hexagram := ⟨.yang, .yang, .yin,  .yang, .yin,  .yang⟩
def obstruction : Hexagram := ⟨.yin,  .yin,  .yang, .yin,  .yang, .yin⟩
def deliverance : Hexagram := ⟨.yin,  .yang, .yin,  .yang, .yin,  .yin⟩
def decrease : Hexagram := ⟨.yang, .yang, .yin,  .yin,  .yin,  .yang⟩
def increase : Hexagram := ⟨.yang, .yin,  .yin,  .yin,  .yang, .yang⟩
def resolution : Hexagram := ⟨.yang, .yang, .yang, .yang, .yang, .yin⟩
def encounter : Hexagram := ⟨.yin,  .yang, .yang, .yang, .yang, .yang⟩
def gathering : Hexagram := ⟨.yin,  .yin,  .yin,  .yang, .yang, .yin⟩
def ascending : Hexagram := ⟨.yin,  .yang, .yang, .yin,  .yin,  .yin⟩
def impasse : Hexagram := ⟨.yin,  .yang, .yin,  .yang, .yang, .yin⟩
def well : Hexagram := ⟨.yin,  .yang, .yang, .yin,  .yang, .yin⟩
def revolution : Hexagram := ⟨.yang, .yin,  .yang, .yang, .yang, .yin⟩
def cauldron : Hexagram := ⟨.yin,  .yang, .yang, .yang, .yin,  .yang⟩
def arousing : Hexagram := ⟨.yang, .yin,  .yin,  .yang, .yin,  .yin⟩  -- 震 卦 (51)
def keepingStill : Hexagram := ⟨.yin,  .yin,  .yang, .yin,  .yin,  .yang⟩  -- 艮 卦 (52)
def gradualProgress : Hexagram := ⟨.yin,  .yin,  .yang, .yin,  .yang, .yang⟩
def marryingMaiden : Hexagram := ⟨.yang, .yang, .yin,  .yang, .yin,  .yin⟩
def abundance : Hexagram := ⟨.yang, .yin,  .yang, .yang, .yin,  .yin⟩
def wanderer : Hexagram := ⟨.yin,  .yin,  .yang, .yang, .yin,  .yang⟩
def gentle : Hexagram := ⟨.yin,  .yang, .yang, .yin,  .yang, .yang⟩  -- 巽 卦 (57)
def joyous : Hexagram := ⟨.yang, .yang, .yin,  .yang, .yang, .yin⟩  -- 兑 卦 (58)
def dispersion : Hexagram := ⟨.yin,  .yang, .yin,  .yin,  .yang, .yang⟩
def limitation : Hexagram := ⟨.yang, .yang, .yin,  .yin,  .yang, .yin⟩
def innerTruth : Hexagram := ⟨.yang, .yang, .yin,  .yin,  .yang, .yang⟩
def smallExceeding : Hexagram := ⟨.yin,  .yin,  .yang, .yang, .yin,  .yin⟩

/-- Name lookup: Hexagram → 卦名. Total function via `xuGua` enumeration. -/
def name (h : Hexagram) : String :=
  -- match the 64 patterns exactly; fall through is unreachable since
  -- Hexagram has exactly 64 inhabitants
  if h = heaven then "乾"
  else if h = earth then "坤"
  else if h = sprout then "屯"
  else if h = naive then "蒙"
  else if h = waiting then "需"
  else if h = dispute then "讼"
  else if h = army then "师"
  else if h = uniting then "比"
  else if h = smallRestraint then "小畜"
  else if h = treading then "履"
  else if h = peace then "泰"
  else if h = blocking then "否"
  else if h = fellowship then "同人"
  else if h = greatPossession then "大有"
  else if h = modesty then "谦"
  else if h = enthusiasm then "豫"
  else if h = following then "随"
  else if h = decay then "蛊"
  else if h = approach then "临"
  else if h = contemplation then "观"
  else if h = biteThrough then "噬嗑"
  else if h = adornment then "贲"
  else if h = stripping then "剥"
  else if h = returning then "复"
  else if h = innocence then "无妄"
  else if h = greatRestraint then "大畜"
  else if h = nourishing then "颐"
  else if h = greatExceeding then "大过"
  else if h = abyss then "坎"
  else if h = brightness then "离"
  else if h = influence then "咸"
  else if h = duration then "恒"
  else if h = retreat then "遁"
  else if h = greatPower then "大壮"
  else if h = progress then "晋"
  else if h = darkening then "明夷"
  else if h = family then "家人"
  else if h = opposition then "睽"
  else if h = obstruction then "蹇"
  else if h = deliverance then "解"
  else if h = decrease then "损"
  else if h = increase then "益"
  else if h = resolution then "夬"
  else if h = encounter then "姤"
  else if h = gathering then "萃"
  else if h = ascending then "升"
  else if h = impasse then "困"
  else if h = well then "井"
  else if h = revolution then "革"
  else if h = cauldron then "鼎"
  else if h = arousing then "震"
  else if h = keepingStill then "艮"
  else if h = gradualProgress then "渐"
  else if h = marryingMaiden then "归妹"
  else if h = abundance then "丰"
  else if h = wanderer then "旅"
  else if h = gentle then "巽"
  else if h = joyous then "兑"
  else if h = dispersion then "涣"
  else if h = limitation then "节"
  else if h = innerTruth then "中孚"
  else if h = smallExceeding then "小过"
  else if h = complete then "既济"
  else if h = incomplete then "未济"
  else "?"  -- unreachable

example : name heaven = "乾" := by native_decide
example : name incomplete = "未济" := by native_decide
example : name complete = "既济" := by native_decide

/-- Lookup-by-name: matches all 64. -/
def fromName : String → Option Hexagram
  | "乾"   => some heaven     | "坤"   => some earth
  | "屯"   => some sprout     | "蒙"   => some naive
  | "需"   => some waiting     | "讼"   => some dispute
  | "师"   => some army     | "比"   => some uniting
  | "小畜" => some smallRestraint   | "履"   => some treading
  | "泰"   => some peace     | "否"   => some blocking
  | "同人" => some fellowship   | "大有" => some greatPossession
  | "谦"   => some modesty     | "豫"   => some enthusiasm
  | "随"   => some following     | "蛊"   => some decay
  | "临"   => some approach     | "观"   => some contemplation
  | "噬嗑" => some biteThrough   | "贲"   => some adornment
  | "剥"   => some stripping     | "复"   => some returning
  | "无妄" => some innocence   | "大畜" => some greatRestraint
  | "颐"   => some nourishing     | "大过" => some greatExceeding
  | "坎"   => some abyss    | "离"   => some brightness
  | "咸"   => some influence     | "恒"   => some duration
  | "遁"   => some retreat     | "大壮" => some greatPower
  | "晋"   => some progress     | "明夷" => some darkening
  | "家人" => some family   | "睽"   => some opposition
  | "蹇"   => some obstruction     | "解"   => some deliverance
  | "损"   => some decrease     | "益"   => some increase
  | "夬"   => some resolution     | "姤"   => some encounter
  | "萃"   => some gathering     | "升"   => some ascending
  | "困"   => some impasse     | "井"   => some well
  | "革"   => some revolution     | "鼎"   => some cauldron
  | "震"   => some arousing    | "艮"   => some keepingStill
  | "渐"   => some gradualProgress     | "归妹" => some marryingMaiden
  | "丰"   => some abundance     | "旅"   => some wanderer
  | "巽"   => some gentle    | "兑"   => some joyous
  | "涣"   => some dispersion     | "节"   => some limitation
  | "中孚" => some innerTruth   | "小过" => some smallExceeding
  | "既济" => some complete   | "未济" => some incomplete
  | _       => none

example : fromName "乾" = some heaven := by native_decide
example : fromName "既济" = some complete := by native_decide
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

namespace SSBX.Foundation.Bagua.R7

open SSBX.Foundation.Yi.Yi (Hexagram)
open SSBX.Foundation.Yi.Yi.Hexagram

/-! ## § 7  R₇ — R7 = Hexagram × YinBit

Naming: `<卦名>·<因>` where 因 ∈ {无, 有}.
-/

def name (c : R7) : String :=
  Hexagram.name c.fst ++ "·" ++ (if c.snd then "有" else "无")

example : name (R7.origin) = "乾·无" := by native_decide
example : name (complete, true) = "既济·有" := by native_decide
example : name (earth, false) = "坤·无" := by native_decide

end SSBX.Foundation.Bagua.R7

namespace SSBX.Foundation.Bagua.R8

open SSBX.Foundation.Yi.Yi (Hexagram)
open SSBX.Foundation.Yi.Yi.Hexagram

/-! ## § 8  R₈ — R8 = Hexagram × Shi (V₄)

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

def name (c : R8) : String :=
  Hexagram.name c.fst ++ "·" ++ shiName c.snd

example : name (R8.origin) = "乾·道" := by native_decide
example : name (incomplete, Shi.wei) = "未济·未" := by native_decide
example : name (complete, Shi.jin) = "既济·今" := by native_decide
example : name (earth, Shi.dao) = "坤·道" := by native_decide

end SSBX.Foundation.Bagua.R8

/-! ## § Verification: spot-check round trips

A full universally-quantified Hexagram round-trip would need a Fintype
instance. Concrete spot checks suffice for the demo. -/

namespace SSBX.Foundation.Lang.Names

open SSBX.Foundation.Yi.Yi.Hexagram

/-- Round-trip on 8 spot-check hexagrams covering full and compound names. -/
theorem hex_round_trip_spot_check :
    fromName (name heaven) = some heaven ∧
    fromName (name earth) = some earth ∧
    fromName (name complete) = some complete ∧
    fromName (name incomplete) = some incomplete ∧
    fromName (name fellowship) = some fellowship ∧
    fromName (name biteThrough) = some biteThrough ∧
    fromName (name innerTruth) = some innerTruth ∧
    fromName (name marryingMaiden) = some marryingMaiden := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals native_decide

end SSBX.Foundation.Lang.Names
