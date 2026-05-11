/-
# WenyanText — 文言之程，可执之文

文言不止是描述，亦可为程。
本模块以 Lean 之 `«»` 引号给 `YiInstr` 之十二构造子起文言别名，
则文之程序即真程序，可由同一 `runFuel` 解释器执行——与道判机同。

注：Lean 4.29 之 lexer 不收 CJK 字为标识符之首，故须以 `«名»` 包之。
-/
import SSBX.Foundation.Bagua.BaguaTuring

namespace SSBX.Foundation.Wen.WenyanText

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring

/-! ## § 1  文之十二字 — YiInstr 之文言别名 -/

/-- 不动：守而不易。 -/
abbrev «不动» : YiInstr := YiInstr.nop
/-- 互：内外相照。 -/
abbrev «互» : YiInstr := YiInstr.interlace
/-- 错：阴阳全反。 -/
abbrev «错» : YiInstr := YiInstr.complement
/-- 综：上下颠倒。 -/
abbrev «综» : YiInstr := YiInstr.reverse
/-- 推：现入于带。 -/
abbrev «推» : YiInstr := YiInstr.push
/-- 取：自带回现。 -/
abbrev «取» : YiInstr := YiInstr.pop
/-- 终：行止。 -/
abbrev «终» : YiInstr := YiInstr.halt

/-- 设时：定其已今未。 -/
abbrev «设时» (s : Shi) : YiInstr := YiInstr.setShi s
/-- 翻爻：择爻而反。 -/
abbrev «翻爻» (i : Fin 6) : YiInstr := YiInstr.flipYao i
/-- 比爻：观二爻之同否。 -/
abbrev «比爻» (i j : Fin 6) (n : Nat) : YiInstr := YiInstr.branchYaoEq i j n
/-- 比时：观时态之同否。 -/
abbrev «比时» (s : Shi) (n : Nat) : YiInstr := YiInstr.branchShiEq s n
/-- 跳：行至所指。 -/
abbrev «跳» (n : Nat) : YiInstr := YiInstr.jump n

/-! ## § 2  时态之三 -/

abbrev «已» : Shi := Shi.ji
abbrev «今» : Shi := Shi.jin
abbrev «未» : Shi := Shi.wei

/-! ## § 3  爻位之六 -/

abbrev «初爻» : Fin 6 := ⟨0, by omega⟩
abbrev «二爻» : Fin 6 := ⟨1, by omega⟩
abbrev «三爻» : Fin 6 := ⟨2, by omega⟩
abbrev «四爻» : Fin 6 := ⟨3, by omega⟩
abbrev «五爻» : Fin 6 := ⟨4, by omega⟩
abbrev «上爻» : Fin 6 := ⟨5, by omega⟩

/-! ## § 4  道判之程 — 以文言写之

经曰：「比第三爻于第四爻；
        若同，则跳天道之处；
        若异，则置时为未——心道也；
        既到天道之处，则置时为已——天道也。」 -/

/-- 道判之程，凡五字。 -/
def «道判之程» : List YiInstr :=
  [ «比爻» «三爻» «四爻» 3
  , «设时» «未»
  , «终»
  , «设时» «已»
  , «终» ]

/-- 文之道判之程，与 BaguaTuring 中之 daoJudgeProg，字面一致。 -/
theorem «道判同源» : «道判之程» = daoJudgeProg := rfl

/-- 施：以某程施于卦，取其时态结果。fuel 与 daoJudge 同。 -/
def «施» (prog : List YiInstr) (h : Hexagram) : Shi :=
  ((YiState.init h prog).runFuel 10).cur.2

/-- 文之施道判，与 daoJudge 全等。 -/
theorem «施判等同» (h : Hexagram) : «施» «道判之程» h = daoJudge h := rfl

/-! ## § 5  验证 — 经卦皆可执 -/

/-- 乾☰☰：天道。 -/
theorem «乾天道» : «施» «道判之程» Hexagram.heaven = «已» := by native_decide

/-- 坤☷☷：天道。 -/
theorem «坤天道» : «施» «道判之程» Hexagram.earth = «已» := by native_decide

/-- 否☰☷：心道。 -/
theorem «否心道» :
    «施» «道判之程» ⟨.yin, .yin, .yin, .yang, .yang, .yang⟩ = «未» := by native_decide

/-- 泰☷☰：心道。 -/
theorem «泰心道» :
    «施» «道判之程» ⟨.yang, .yang, .yang, .yin, .yin, .yin⟩ = «未» := by native_decide

/-! ## § 6  文之他程 — 文言之中能造万程 -/

/-- 互而后判：先施互于卦，再判其道。 -/
def «互而后判» : List YiInstr :=
  [ «互»
  , «比爻» «三爻» «四爻» 4
  , «设时» «未»
  , «终»
  , «设时» «已»
  , «终» ]

/-- 错而后判：先施错于卦，再判其道。 -/
def «错而后判» : List YiInstr :=
  [ «错»
  , «比爻» «三爻» «四爻» 4
  , «设时» «未»
  , «终»
  , «设时» «已»
  , «终» ]

/-- 综而后判：先施综于卦，再判其道。 -/
def «综而后判» : List YiInstr :=
  [ «综»
  , «比爻» «三爻» «四爻» 4
  , «设时» «未»
  , «终»
  , «设时» «已»
  , «终» ]

/-- 互而后判：保道。互不变 y3=y4 之关系。 -/
theorem «互判保道» (h : Hexagram) :
    «施» «互而后判» h = «施» «道判之程» h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-- 错而后判：保道。错颠倒所有爻，y3、y4 之同否不变。 -/
theorem «错判保道» (h : Hexagram) :
    «施» «错而后判» h = «施» «道判之程» h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-- 综而后判：保道。综倒上下，y3 与 y4 互换，故同否不变。 -/
theorem «综判保道» (h : Hexagram) :
    «施» «综而后判» h = «施» «道判之程» h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-! ## § 7  翻爻之程 — 一爻反则道未必同 -/

/-- 翻三而后判：先翻第三爻，再判其道。 -/
def «翻三而后判» : List YiInstr :=
  [ «翻爻» «三爻»
  , «比爻» «三爻» «四爻» 4
  , «设时» «未»
  , «终»
  , «设时» «已»
  , «终» ]

/-- 翻第三爻则道反：天变心，心变天。 -/
theorem «翻三反道» (h : Hexagram) :
    «施» «翻三而后判» h = (if «施» «道判之程» h = «已» then «未» else «已») := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-! ## § 8  推取之程 — 带之用 -/

/-- 推而再取：状态不变。 -/
def «推取» : List YiInstr :=
  [ «推»
  , «取»
  , «终» ]

theorem «推取归原» (h : Hexagram) :
    ((YiState.init h «推取»).runFuel 10).cur = (h, «今») := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-! ## § 9  公示 -/

/-- 文之至：文言写就之程，与 daoJudgeProg 字面同体；
    其执行结果，与 daoJudge 全等。 -/
theorem «文道一也» :
    («道判之程» = daoJudgeProg)
    ∧ (∀ h : Hexagram, «施» «道判之程» h = daoJudge h)
    ∧ (∀ h : Hexagram, «施» «道判之程» h = (if h.isTian then «已» else «未»)) := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro h
  show daoJudge h = _
  exact daoJudge_correct h

end SSBX.Foundation.Wen.WenyanText
