/-
# Lexicon — canonical Chinese ↔ English ↔ bit-string mapping

Single source of truth. Every doctrinal identifier in the codebase resolves
through this table. Three faces per concept:

1. **chinese**: the canonical Chinese form (used in docstrings, Sexp atoms,
   user-facing prose). Never used as a Lean identifier.
2. **english**: the canonical Lean identifier (descriptive English; math
   vocabulary when precise; `R<n>_<bits>` fallback for obscure cells).
3. **bits**: the layer-indexed bit-string form `<n-char o/x>` where `o`=yang
   (false) and `x`=yin (true). Layer is inferred from string length.

## Translation policy (per user mandate)

- Use **precise descriptive English** when it maps exactly to the position
  (e.g., 中 → `center`, 极 → `terminus`).
- Use **formal/math/logic vocabulary** when there's an exact mathematical
  correspondent (e.g., 一 → `one`, 极 → `fixedPoint`).
- Use **bit-string fallback** `R<n>_<bits>` when no precise descriptive
  English exists (e.g., obscure hexagrams).

## Namespace collisions

Several Chinese characters denote BOTH a trigram and a hexagram (坎/离/震/
艮/巽/兑). The English forms differ:

| Chinese | Trigram (R₃) | Hexagram (R₆) |
|---|---|---|
| 坎 | `water` | `abyss` |
| 离 | `fire` | `brightness` |
| 震 | `thunder` | `arousing` |
| 艮 | `mountain` | `keepingStill` |
| 巽 | `wind` | `gentle` |
| 兑 | `lake` | `joyous` |
| 乾 | `heaven` | `heaven` (the trigram is contained in the hexagram) |
| 坤 | `earth` | `earth` (same) |

For 乾/坤 the trigram and hexagram English names coincide (no namespace
collision because their `bits` strings differ in length: 3 vs 6).

## Confucian-doctrine cells lifted from `Wuchang.lean` + `Confucian.lean`

The 五常 (Wuchang) are SPECIFIC Cell128 cells, not aliases of hexagrams.
Their bit-string is 7 chars (R₇ = R₆ × YinBit). See `confucian` table § 6.
-/

namespace SSBX.Foundation.Lang.Lexicon

/-- A lexicon entry: one doctrinal concept with three canonical forms. -/
structure Entry where
  chinese : String           -- canonical Chinese form
  english : String           -- canonical Lean identifier
  bits    : String           -- bit-string (length = R-layer)
  aka     : List String := []  -- legacy / alternative names (pinyin, etc.)
  notes   : String := ""     -- Wilhelm-canonical or doctrinal commentary
  deriving Repr, Inhabited

/-- The R-layer of an entry (inferred from `bits.length`). -/
def Entry.layer (e : Entry) : Nat := e.bits.length

/-! ## § 1 R₁ Yao (2 atoms) -/

def yao : List Entry := [
  ⟨"阳", "yang", "o", [], "active / manifest / +"⟩,
  ⟨"阴", "yin",  "x", [], "receptive / latent / -"⟩
]

/-! ## § 2 R₂ SiXiang (4 atoms) -/

def sixiang : List Entry := [
  ⟨"太阳", "greaterYang", "oo", ["taiYang"], "full yang"⟩,
  ⟨"少阴", "lesserYin",   "ox", ["shaoYin"],  "yang descending"⟩,
  ⟨"少阳", "lesserYang",  "xo", ["shaoYang"], "yin rising"⟩,
  ⟨"太阴", "greaterYin",  "xx", ["taiYin"],   "full yin"⟩
]

/-! ## § 3 R₃ Trigram (八卦, 8 atoms) -/

def trigram : List Entry := [
  ⟨"乾", "heaven",   "ooo", ["qian"], "☰ heaven / father"⟩,
  ⟨"兑", "lake",     "oox", ["dui"],  "☱ lake / youngest daughter"⟩,
  ⟨"离", "fire",     "oxo", ["li"],   "☲ fire / middle daughter"⟩,
  ⟨"震", "thunder",  "oxx", ["zhen"], "☳ thunder / eldest son"⟩,
  ⟨"巽", "wind",     "xoo", ["xun"],  "☴ wind / eldest daughter"⟩,
  ⟨"坎", "water",    "xox", ["kan"],  "☵ water / middle son"⟩,
  ⟨"艮", "mountain", "xxo", ["gen"],  "☶ mountain / youngest son"⟩,
  ⟨"坤", "earth",    "xxx", ["kun"],  "☷ earth / mother"⟩
]

/-! ## § 4 R₄ Mian = Ben × Zheng (16 cells)

  Ben (4): 物/动/间/事 = thing/motion/interval/event
  Zheng (4): 几/势/机/时 = trace/momentum/pivot/occasion

  16 combined names follow `<ben>·<zheng>` composition.
-/

def ben : List Entry := [
  ⟨"物", "thing",    "oo", ["wu"],   "Ben atom: substance / matter"⟩,
  ⟨"动", "motion",   "xo", ["dong"], "Ben atom: dynamic-becoming"⟩,
  ⟨"间", "interval", "ox", ["jian"], "Ben atom: spatial between-ness"⟩,
  ⟨"事", "event",    "xx", ["shi"],  "Ben atom: happening / occurrence"⟩
]

def zheng : List Entry := [
  ⟨"几", "trace",     "oo", ["jiFaint"],    "Zheng atom: subtle stir / micro-genesis"⟩,
  ⟨"势", "momentum",  "xo", ["shiForce"],   "Zheng atom: directional pressure"⟩,
  ⟨"机", "pivot",     "ox", ["jiOccasion"], "Zheng atom: critical opportunity"⟩,
  ⟨"时", "occasion",  "xx", ["shiTime"],    "Zheng atom: temporal kairos"⟩
]

/-! ## § 5 R₆ Hexagram (64 周易卦)

  Each entry: `bits` is 6 chars y1..y6 (inner-to-outer, bottom-to-top).
  English chosen descriptive-first; Wilhelm-canonical in notes.
-/

def hexagram : List Entry := [
  -- 1-8
  ⟨"乾",   "heaven",         "oooooo", ["qian"], "01. The Creative"⟩,
  ⟨"坤",   "earth",          "xxxxxx", ["kun"],  "02. The Receptive"⟩,
  ⟨"屯",   "sprout",         "oxxxox", ["zhun"], "03. Difficulty at Beginning"⟩,
  ⟨"蒙",   "naive",          "xoxxxo", ["meng"], "04. Youthful Folly"⟩,
  ⟨"需",   "waiting",        "oooxox", ["xu"],   "05. Waiting"⟩,
  ⟨"讼",   "dispute",        "xoxooo", ["song"], "06. Conflict"⟩,
  ⟨"师",   "army",           "xoxxxx", ["shiArmy"], "07. The Army"⟩,
  ⟨"比",   "uniting",        "xxxxox", ["biUnion"], "08. Holding Together"⟩,
  -- 9-16
  ⟨"小畜", "smallRestraint", "oooxoo", ["xiaoXu"],  "09. Small Taming"⟩,
  ⟨"履",   "treading",       "ooxooo", ["lvTread"], "10. Treading"⟩,
  ⟨"泰",   "peace",          "oooxxx", ["tai"],     "11. Peace"⟩,
  ⟨"否",   "blocking",       "xxxooo", ["pi"],      "12. Standstill"⟩,
  ⟨"同人", "fellowship",     "oxoooo", ["tongRen"], "13. Fellowship"⟩,
  ⟨"大有", "greatPossession","ooooxo", ["daYou"],   "14. Great Possession"⟩,
  ⟨"谦",   "modesty",        "xxoxxx", ["qianModesty"], "15. Modesty"⟩,
  ⟨"豫",   "enthusiasm",     "xxxoxx", ["yu"],      "16. Enthusiasm"⟩,
  -- 17-24
  ⟨"随",   "following",      "oxxoox", ["sui"],     "17. Following"⟩,
  ⟨"蛊",   "decay",          "xooxxo", ["gu"],      "18. Work on the Decayed"⟩,
  ⟨"临",   "approach",       "ooxxxx", ["lin"],     "19. Approach"⟩,
  ⟨"观",   "contemplation",  "xxxxoo", ["guan"],    "20. Contemplation"⟩,
  ⟨"噬嗑", "biteThrough",    "oxxoxo", ["shiHe"],   "21. Biting Through"⟩,
  ⟨"贲",   "adornment",      "oxoxox", ["bi"],      "22. Grace / Adornment"⟩,
  ⟨"剥",   "stripping",      "xxxxxo", ["bo"],      "23. Splitting Apart"⟩,
  ⟨"复",   "returning",      "oxxxxx", ["fu"],      "24. Return"⟩,
  -- 25-32
  ⟨"无妄", "innocence",      "oxxooo", ["wuWang"],  "25. Innocence"⟩,
  ⟨"大畜", "greatRestraint", "oooxxo", ["daXu"],    "26. Great Taming"⟩,
  ⟨"颐",   "nourishing",     "oxxxxo", ["yiNourish"], "27. Mouth Corners"⟩,
  ⟨"大过", "greatExceeding", "xoooox", ["daGuo"], "28. Preponderance of Great"⟩,
  ⟨"坎",   "abyss",          "xoxxox", ["kanHex"],  "29. The Abysmal (Water)"⟩,
  ⟨"离",   "brightness",     "oxooxo", ["liHex"],   "30. The Clinging (Fire)"⟩,
  ⟨"咸",   "influence",      "xxooox", ["xian"],    "31. Influence"⟩,
  ⟨"恒",   "duration",       "xoooxx", ["heng"],    "32. Duration"⟩,
  -- 33-40
  ⟨"遁",   "retreat",        "xxoooo", ["dun"],     "33. Retreat"⟩,
  ⟨"大壮", "greatPower",     "ooooxx", ["daZhuang"], "34. Great Power"⟩,
  ⟨"晋",   "progress",       "xxxoxo", ["jin"],     "35. Progress"⟩,
  ⟨"明夷", "darkening",      "oxoxxx", ["mingYi"],  "36. Darkening of the Light"⟩,
  ⟨"家人", "family",         "oxoxoo", ["jiaRen"],  "37. The Family"⟩,
  ⟨"睽",   "opposition",     "ooxoxo", ["kui"],     "38. Opposition"⟩,
  ⟨"蹇",   "obstruction",    "xxoxox", ["jianObst"], "39. Obstruction"⟩,
  ⟨"解",   "deliverance",    "xoxoxx", ["xie"],     "40. Deliverance"⟩,
  -- 41-48
  ⟨"损",   "decrease",       "ooxxxo", ["sun"],     "41. Decrease"⟩,
  ⟨"益",   "increase",       "oxxxoo", ["yiIncr"],  "42. Increase"⟩,
  ⟨"夬",   "resolution",     "ooooox", ["guai"],    "43. Breakthrough"⟩,
  ⟨"姤",   "encounter",      "xooooo", ["gou"],     "44. Coming to Meet"⟩,
  ⟨"萃",   "gathering",      "xxxoox", ["cui"],     "45. Gathering Together"⟩,
  ⟨"升",   "ascending",      "xooxxx", ["sheng"],   "46. Pushing Upward"⟩,
  ⟨"困",   "impasse",        "xoxoox", ["kunImp"],  "47. Oppression"⟩,
  ⟨"井",   "well",           "xooxox", ["jing"],    "48. The Well"⟩,
  -- 49-56
  ⟨"革",   "revolution",     "oxooox", ["ge"],      "49. Revolution"⟩,
  ⟨"鼎",   "cauldron",       "xoooxo", ["ding"],    "50. The Cauldron"⟩,
  ⟨"震",   "arousing",       "oxxoxx", ["zhenHex"], "51. The Arousing (Thunder)"⟩,
  ⟨"艮",   "keepingStill",   "xxoxxo", ["genHex"],  "52. Keeping Still (Mountain)"⟩,
  ⟨"渐",   "gradualProgress","xxoxoo", ["jianGrad"], "53. Development / Gradual"⟩,
  ⟨"归妹", "marryingMaiden", "ooxoxx", ["guiMei"],  "54. The Marrying Maiden"⟩,
  ⟨"丰",   "abundance",      "oxooxx", ["feng"],    "55. Abundance / Fullness"⟩,
  ⟨"旅",   "wanderer",       "xxooxo", ["lvTrav"],  "56. The Wanderer"⟩,
  -- 57-64
  ⟨"巽",   "gentle",         "xooxoo", ["xunHex"],  "57. The Gentle (Wind)"⟩,
  ⟨"兑",   "joyous",         "ooxoox", ["duiHex"],  "58. The Joyous (Lake)"⟩,
  ⟨"涣",   "dispersion",     "xoxxoo", ["huan"],    "59. Dispersion"⟩,
  ⟨"节",   "limitation",     "ooxxox", ["jie"],     "60. Limitation"⟩,
  ⟨"中孚", "innerTruth",     "ooxxoo", ["zhongFu"], "61. Inner Truth"⟩,
  ⟨"小过", "smallExceeding", "xxooxx", ["xiaoGuo"], "62. Preponderance of the Small"⟩,
  ⟨"既济", "complete",       "oxoxox", ["jiJi"],    "63. After Completion"⟩,
  ⟨"未济", "incomplete",     "xoxoxo", ["weiJi"],   "64. Before Completion"⟩
]

theorem hexagram_count : hexagram.length = 64 := by native_decide

/-! ## § 6 Confucian doctrinal terms

  Includes the 五常 placed at R₇ Cell128 (yin-bit suffix `o` = 无),
  the 四端 as R₃ trigrams, plus other doctrinal vocabulary.
-/

def confucian : List Entry := [
  -- 五常 (5 cells at R₇ Cell128)
  ⟨"仁", "benevolence",   "xoooooo", ["ren"], "first stir; cell = 姤·无"⟩,
  ⟨"义", "righteousness", "oxooooo", ["yiV"], "fellowship; cell = 同人·无"⟩,
  ⟨"礼", "propriety",     "ooxoooo", ["liV"], "treading; cell = 履·无"⟩,
  ⟨"智", "wisdom",        "oooxooo", ["zhiV"], "restraint; cell = 小畜·无"⟩,
  ⟨"信", "integrity",     "xxxxooo", ["xinV"], "observation; cell = 观·无 (信 = 仁⊕义⊕礼⊕智)"⟩,
  -- 善恶 at R₁
  ⟨"善", "good",          "o", ["shan"], "good = yang (active align)"⟩,
  ⟨"恶", "evil",          "x", ["eVice"], "evil = yin (passive misalign)"⟩,
  -- 四端 (4 of 8 trigrams)
  ⟨"恻隐", "compassion",  "oxo", ["ceYin"],   "仁端; 离 ☲"⟩,
  ⟨"羞恶", "shame",       "xox", ["xiuWu"],   "义端; 坎 ☵"⟩,
  ⟨"辞让", "yielding",    "oxx", ["ciRang"],  "礼端; 震 ☳"⟩,
  ⟨"是非", "discernment", "oox", ["shiFei"],  "智端; 兑 ☱"⟩,
  -- 三才 (3 of 8 trigrams)
  ⟨"天", "sky",     "ooo", ["tianSky"],    "三才 heaven aspect (= 乾)"⟩,
  ⟨"地", "ground",  "xxx", ["diGround"],   "三才 earth aspect (= 坤)"⟩,
  ⟨"人", "human",   "xxo", ["renHuman"],   "三才 human aspect (= 艮 mountain)"⟩,
  -- 大学三纲 (3 of 8 trigrams)
  ⟨"明明德",   "illuminateVirtue", "oxo", ["mingMingDe"], "三纲 1; 离 ☲"⟩,
  ⟨"亲民",     "engagePeople",     "oox", ["qinMin"],     "三纲 2; 兑 ☱"⟩,
  ⟨"止于至善", "restInGood",       "xxo", ["zhiYuZhiShan"], "三纲 3; 艮 ☶"⟩,
  -- 大学八目 (8 trigrams)
  ⟨"格物",   "investigateThings",   "xoo", ["geWu"],     "八目 1; 巽 ☴"⟩,
  ⟨"致知",   "extendKnowledge",     "oxo", ["zhiZhi"],   "八目 2; 离 ☲"⟩,
  ⟨"诚意",   "sincereIntention",    "oox", ["chengYi"],  "八目 3; 兑 ☱"⟩,
  ⟨"正心",   "rectifyHeart",        "xxo", ["zhengXin"], "八目 4; 艮 ☶"⟩,
  ⟨"修身",   "cultivateSelf",       "oxx", ["xiuShen"],  "八目 5; 震 ☳"⟩,
  ⟨"齐家",   "regulateFamily",      "xox", ["qiJia"],    "八目 6; 坎 ☵"⟩,
  ⟨"治国",   "governState",         "xxx", ["zhiGuo"],   "八目 7; 坤 ☷"⟩,
  ⟨"平天下", "pacifyWorld",         "ooo", ["pingTianXia"], "八目 8; 乾 ☰"⟩,
  -- 喜怒哀乐 (4 of SiXiang)
  ⟨"喜", "joy",      "oo", ["xi"],     "中庸 emotion: full yang"⟩,
  ⟨"怒", "anger",    "ox", ["nu"],     "中庸 emotion: yang descending"⟩,
  ⟨"哀", "sorrow",   "xo", ["ai"],     "中庸 emotion: yin rising"⟩,
  ⟨"乐", "delight",  "xx", ["le"],     "中庸 emotion: full yin"⟩,
  -- 元亨利贞 (4 of SiXiang)
  ⟨"元", "origin",  "oo", ["yuan"], "乾·彖: spring / source"⟩,
  ⟨"亨", "smooth",  "xo", ["heng"], "乾·彖: summer / passage"⟩,
  ⟨"利", "benefit", "ox", ["liYHL"], "乾·彖: autumn / yield"⟩,
  ⟨"贞", "correct", "xx", ["zhen"], "乾·彖: winter / fidelity"⟩,
  -- 高级 doctrinal terms
  ⟨"道",    "dao",         "ooooooo", ["dao"], "proper noun; R₇ origin"⟩,
  ⟨"圣人",  "sage",        "ooooooo", ["shengRen"], "perfected being"⟩,
  ⟨"内圣",  "innerSage",   "", ["neiSheng"], "inner perfection (predicate)"⟩,
  ⟨"外王",  "outerKing",   "", ["waiWang"], "outer ruling (predicate)"⟩,
  ⟨"恕",    "reciprocity", "", ["shu"], "cross-orbit relation"⟩,
  ⟨"中庸",  "middleWay",   "", ["zhongYong"], "the doctrine of mean"⟩,
  ⟨"大学",  "greatLearning","", ["daXue"], "Confucian classic"⟩,
  ⟨"论语",  "analects",    "", ["lunYu"], "Confucian classic"⟩,
  ⟨"孟子",  "mencius",     "", ["mengZi"], "Confucian classic"⟩,
  ⟨"易",    "yiBook",      "", ["yiBook"], "the Yi Jing (proper noun)"⟩,
  ⟨"太极",  "taiji",       "", ["taiJi"], "supreme ultimate (proper noun)"⟩
]

/-! ## § 7 Operators (Cayley actions / V₄ ops / predicate primitives) -/

def operators : List Entry := [
  ⟨"印", "imprint",        "", ["yinOp"],   "R₇ atomic: toggle YinBit (因)"⟩,
  ⟨"投", "project",        "", ["touOp"],   "R₈ atomic: toggle GuoBit (果)"⟩,
  ⟨"错", "complement",     "", ["cuoOp"],   "XOR with all-yang = NOT (Hexagram)"⟩,
  ⟨"综", "reverse",        "", ["zongOp"],  "yao-order reversal (Hexagram)"⟩,
  ⟨"互", "interlace",      "", ["huOp"],    "inner-trigram extraction"⟩,
  ⟨"错综", "complementReverse", "", ["cuoZongOp"], "V₄ central element"⟩,
  ⟨"動", "motion",         "", ["dongOp"],  "Kernel primitive: XOR-with-c_motion"⟩,
  ⟨"中", "center",         "", ["centerP"], "predicate: cell ≠ motion-fixed-point"⟩,
  ⟨"极", "terminus",       "", ["terminusP"], "predicate: cell = motion-fixed-point = origin"⟩,
  ⟨"几", "trace",          "", ["traceP"],  "iterated motion: motion^[n]"⟩,
  ⟨"势", "momentum",       "", ["momentumP"], "cumulative XOR of motion masks"⟩,
  ⟨"机", "pivot",          "", ["pivotP"],  "critical transition point"⟩,
  ⟨"聚", "gather",         "", ["gatherP"], "convergent dynamics predicate"⟩,
  ⟨"散", "scatter",        "", ["scatterP"], "divergent dynamics predicate"⟩,
  ⟨"和", "harmony",        "", ["harmonyP"], "multi-orbit diversity-with-flow"⟩,
  ⟨"美", "beauty",         "", ["beautyP"], "heart-event encounter in center"⟩,
  ⟨"德", "virtue",         "", ["virtueP"], "orbit predicate: hasDe"⟩,
  ⟨"理", "principle",      "", ["principleP"], "orbit unfolding as structure"⟩,
  ⟨"心", "heart",          "", ["heartP"], "self-referential focus structure"⟩,
  ⟨"情", "feeling",        "", ["feelingP"], "heart-in-relation"⟩,
  ⟨"积", "accumulation",   "", ["accumP"], "scale-stabilization predicate"⟩,
  ⟨"生", "birth",          "", ["birthP"], "= motion (生成 face)"⟩,
  ⟨"息", "rest",           "", ["restP"],  "= terminus (停息 face)"⟩,
  ⟨"行", "action",         "", ["actionP"], "= motion (actor face)"⟩,
  ⟨"一", "one",            "", ["oneP"],   "the foundational unity (Field root)"⟩,
  ⟨"意", "intention",      "", ["intentionP"], "heart's projection / pre-cognition"⟩,
  ⟨"诚", "sincerity",      "", ["sincerityP"], "heart-self-consistency"⟩
]

/-! ## § 8 五伦 (R₅ aliases) — these are R₅ generators, not "cells with names" -/

def wuLun : List Entry := [
  ⟨"父子", "fatherSon",      "", ["fuZi"],     "五伦 1: vertical generation"⟩,
  ⟨"君臣", "rulerSubject",   "", ["junChen"],  "五伦 2: vertical role"⟩,
  ⟨"夫妇", "husbandWife",    "", ["fuFu"],     "五伦 3: paired union"⟩,
  ⟨"兄弟", "brothers",       "", ["xiongDi"],  "五伦 4: ordered siblings"⟩,
  ⟨"朋友", "friends",        "", ["pengYou"],  "五伦 5: equal companions"⟩
]

/-! ## § 9 Lookup functions

  Bidirectional resolution: Chinese ↔ English (canonical or legacy alias)
  ↔ bit-string. All work on String inputs.
-/

namespace Lookup

/-- All tables, flattened (without layer-classification). -/
def allEntries : List Entry :=
  yao ++ sixiang ++ trigram ++ ben ++ zheng ++ hexagram ++ confucian ++ operators ++ wuLun

/-- Find an entry by its canonical Chinese name. -/
def byChinese (zh : String) : Option Entry :=
  allEntries.find? fun e => e.chinese == zh

/-- Find an entry by its canonical English name OR any legacy `aka` alias. -/
def byEnglish (en : String) : Option Entry :=
  allEntries.find? fun e => e.english == en || e.aka.contains en

/-- Find an entry by its bit-string. Returns the FIRST match across all tables;
    if multiple tables share a bit-string (e.g., a trigram and a hexagram), the
    earlier table wins. -/
def byBits (bs : String) : Option Entry :=
  allEntries.find? fun e => e.bits == bs

/-- Lookup the canonical English name for a Chinese string. -/
def englishOf (zh : String) : Option String :=
  (byChinese zh).map (·.english)

/-- Lookup the canonical Chinese name for an English string. -/
def chineseOf (en : String) : Option String :=
  (byEnglish en).map (·.chinese)

/-- Lookup the bit-string + R-layer for a Chinese string. -/
def bitsOf (zh : String) : Option (Nat × String) :=
  (byChinese zh).map fun e => (e.layer, e.bits)

end Lookup

/-! ## § 10 Smoke tests + round-trip checks -/

#eval Lookup.englishOf "乾"    -- some "heaven"
#eval Lookup.chineseOf "heaven" -- some "乾"
#eval Lookup.englishOf "仁"    -- some "benevolence"
#eval Lookup.bitsOf "未济"      -- some (6, "xoxoxo")
#eval Lookup.byBits "xxxxxx"   -- some «坤»

example : Lookup.englishOf "乾" = some "heaven" := by native_decide
example : Lookup.chineseOf "heaven" = some "乾" := by native_decide
example : Lookup.englishOf "仁" = some "benevolence" := by native_decide
example : Lookup.englishOf "未济" = some "incomplete" := by native_decide
example : Lookup.englishOf "中庸" = some "middleWay" := by native_decide

/-! ## § 11 Public summary -/

theorem lexicon_summary :
    Lookup.englishOf "乾" = some "heaven" ∧
    Lookup.englishOf "仁" = some "benevolence" ∧
    Lookup.englishOf "既济" = some "complete" ∧
    Lookup.englishOf "印" = some "imprint" ∧
    Lookup.chineseOf "wisdom" = some "智" ∧
    hexagram.length = 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals native_decide

end SSBX.Foundation.Lang.Lexicon
