/-
# WenyanReflect — 文核同源：判型良 / 判停 / 验程

Path 丙 § M3-甲 之反射层（reflection layer）。

把「程序合度」与「有界停机」二事，皆铸为 *Bool-valued reflective functions*，
并以「文核同源」公示之名声明：文（wenyan-named function）与核（kernel-side
`runFuel` / `validProg`）字面同体，由 `rfl` 见证。

## 三函

  · `判型良 : List YiInstr → Bool`
        — 结构合度判定（target 须 1..64，与 `BaguaWenSpec.maxNumeral = 64` 一致）
  · `判停   : List YiInstr → Hexagram → Nat → Bool`
        — 有界停机判定（n 步后是否 halted）
  · `验程   : List YiInstr → Hexagram → Nat → YiState`
        — 文言名义之 runFuel 别名（程之验形即末态）

## 三公示

  · `文核同源`        — 验程 = runFuel ∘ init                 (rfl)
  · `判停_eq`         — 判停 = halted ∘ runFuel ∘ init        (rfl)
  · `validProg_iff_判型良`
                       — M1 之 validProg 与本层 判型良 extensional 同 (rfl)

## 状态

0 sorry / 0 axiom / 全 def 总函数。
具体程序之反射结论由 `native_decide` 见证（道判机停 / loopProg 不停 / 末态 = 已）。
-/
import SSBX.Foundation.Bagua.BaguaTuring
import SSBX.Foundation.Bagua.BaguaWenSpec
import SSBX.Foundation.Wen.WenyanParser

namespace SSBX.Foundation.Wen.WenyanReflect

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.BaguaWenSpec
open SSBX.Foundation.Wen.WenyanParser

/-! ## § 1  判型良 — 结构合度反射 -/

/-- 单条指令之合度：跳转目标须 1 ≤ t ≤ 64（与 `maxNumeral` 一致）。
    结构上与 `WenyanParser.validInstr` 字面同体。 -/
def «判型良一» : YiInstr → Bool
  | .branchYaoEq _ _ t => decide (1 ≤ t ∧ t ≤ 64)
  | .branchShiEq _ t   => decide (1 ≤ t ∧ t ≤ 64)
  | .jump t            => decide (1 ≤ t ∧ t ≤ 64)
  | _ => true

/-- 整程合度反射：每条指令皆合度。 -/
def «判型良» (p : List YiInstr) : Bool := p.all «判型良一»

/-! ## § 2  判停 — 有界停机反射 -/

/-- 有界停机判定：从 hexagram h 之 init 出发，跑 n 步后是否 halted。 -/
def «判停» (prog : List YiInstr) (h : Hexagram) (n : Nat) : Bool :=
  ((YiState.init h prog).runFuel n).halted

/-! ## § 3  验程 — 文言名义之 runFuel 别名 -/

/-- 验程：从 hexagram h 之 init 出发，跑 n 步后之末态。 -/
def «验程» (prog : List YiInstr) (h : Hexagram) (n : Nat) : YiState :=
  (YiState.init h prog).runFuel n

/-! ## § 4  文核同源 — 反射层与核层之恒等 -/

/-- **文核同源**：验程（文）= runFuel ∘ init（核）。文之名与核之实字面同体。 -/
theorem «文核同源» (prog : List YiInstr) (h : Hexagram) (n : Nat) :
    «验程» prog h n = (YiState.init h prog).runFuel n := rfl

/-- 判停之展开：reflective predicate 字面等于核层 halted-after-runFuel。 -/
theorem «判停_eq» (prog : List YiInstr) (h : Hexagram) (n : Nat) :
    «判停» prog h n = ((YiState.init h prog).runFuel n).halted := rfl

/-! ## § 5  validProg ↔ 判型良 之 extensional 同体 -/

/-- 单条指令层：validInstr 与 判型良一 字面同体. -/
theorem «validInstr_eq_判型良一» (i : YiInstr) :
    validInstr i = «判型良一» i := by
  cases i <;> rfl

/-- 程层：M1 之 validProg 与本层 判型良 extensional 同体. -/
theorem «validProg_iff_判型良» (p : List YiInstr) :
    validProg p = «判型良» p := by
  unfold validProg «判型良»
  induction p with
  | nil => rfl
  | cons i rest ih =>
      simp [List.all_cons, «validInstr_eq_判型良一», ih]

/-! ## § 6  Sanity 检查 — native_decide 见证 -/

/-- 道判机程序合度（target=3 ∈ 1..64）。 -/
theorem «道判_判型良» : «判型良» daoJudgeProg = true := by native_decide

/-- 道判机于乾卦 10 步内停机。 -/
theorem «道判_判停_乾» : «判停» daoJudgeProg Hexagram.qian 10 = true := by native_decide

/-- loopProg 于乾卦任 10 步内不停机（loopProg 永循环）。 -/
theorem «环程_不停» : «判停» loopProg Hexagram.qian 10 = false := by native_decide

/-- 验程之末态：道判机于乾卦 10 步后 cur.2 = 已（天道）。 -/
theorem «验程_乾_末时» :
    («验程» daoJudgeProg Hexagram.qian 10).cur.2 = Shi.ji := by native_decide

/-! ## § 7  附加见证 — 三角公示

  反射层之三事一气：合度 (判型良) → 停机 (判停) → 末态 (验程.cur).
  每一事皆 Bool / YiState 反射，由 native_decide 在 daoJudgeProg 上见证。
-/

/-- 道判机三反射齐整：合度 ∧ 停 ∧ 末时 = 已. -/
theorem «道判_三反射» :
    «判型良» daoJudgeProg = true
    ∧ «判停» daoJudgeProg Hexagram.qian 10 = true
    ∧ («验程» daoJudgeProg Hexagram.qian 10).cur.2 = Shi.ji :=
  ⟨«道判_判型良», «道判_判停_乾», «验程_乾_末时»⟩

end SSBX.Foundation.Wen.WenyanReflect
