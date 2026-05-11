/-
# WenyanSyntax — M3-甲 ：Lean 内 wenyan 块语法

Path 丙 § M3 之甲路：以 Lean 之 `notation` / `syntax` / `macro_rules` 把 baguaWen
22 token 直接铸入 Lean 解析器，使 wenyan 之文可在 Lean 文件中直写为 `term`。

## 为何用「裸 CJK」而非 «»-quoted

Lean 4 之 `«...»` 是 *identifier 引号*（用以容纳含特殊字符之标识符）.
若以 `«已»` 作为 `notation` 之 atom，Lean 解析器先把 `«已»` 识别为 ident
而非 string atom，故得 "invalid atom" 之错。

故此模块用 *裸 CJK*：`notation "已" => Shi.ji`. 所有 22 reservedToken 之
原字面（即去 «» 之 内容部分）皆 declare 为 keyword. 因 reservedTokens 已
冻结于 `BaguaWenSpec.lean`，且其内字本不作 identifier 用，无 token 流失。

## 设计

  · `notation`         — 11 atomic instr / 3 shi / 6 yao 位（直接铸 token → 值）
  · `syntax + macro`   — 比爻 / 比时 / 跳 三 至-特例（带 Nat 参数）
  · `程` 块            — sepBy(term, "；") → List YiInstr

  i.e.
  ```
  程 { 比爻 三爻 四爻 至 3 ；
        设时 未  ；  终  ；
        设时 已  ；  终 }
  ```
  在 Lean 解析阶段即生成 `daoJudgeProg : List YiInstr`，无须 string parser。

## 与 String 端 (M1 WenyanParser) 之关系

M1 之 `«解程»` 处理 *运行时 String*；M3 之 `程` 块处理 *编译时 Lean term*。
两者在 daoJudgeProg 上 commute（由 `WenyanParser.daoJudgeProg_print` 与
本文件之 `daoJudgeBlock_eq_daoJudgeProg` 共同见证）。

## 状态

0 sorry / 0 axiom. 全 native_decide / rfl 见证.
-/
import SSBX.Foundation.Bagua.BaguaTuring

namespace SSBX.Foundation.Wen.WenyanSyntax

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring

/-! ## § 1  时态四字 (V₄ Klein) -/

notation "道" => Shi.dao
notation "已" => Shi.ji
notation "今" => Shi.jin
notation "未" => Shi.wei

/-! ## § 2  爻位六字 — Fin 6 -/

notation "初爻" => (⟨0, by omega⟩ : Fin 6)
notation "二爻" => (⟨1, by omega⟩ : Fin 6)
notation "三爻" => (⟨2, by omega⟩ : Fin 6)
notation "四爻" => (⟨3, by omega⟩ : Fin 6)
notation "五爻" => (⟨4, by omega⟩ : Fin 6)
notation "上爻" => (⟨5, by omega⟩ : Fin 6)

/-! ## § 3  指令字 — atomic 7 -/

notation "不动" => YiInstr.nop
notation "互"   => YiInstr.interlace
notation "错"   => YiInstr.complement
notation "综"   => YiInstr.reverse
notation "推"   => YiInstr.push
notation "取"   => YiInstr.pop
notation "终"   => YiInstr.halt

/-! ## § 4  指令字 — 1-arg parameterized 2 -/

syntax:max "设时" term:max : term
syntax:max "翻爻" term:max : term

macro_rules
  | `(设时 $s) => `(YiInstr.setShi $s)
  | `(翻爻 $i) => `(YiInstr.flipYao $i)

/-! ## § 5  指令字 — 至-3-arg 3 -/

syntax:max "比爻" term:max term:max "至" term:max : term
syntax:max "比时" term:max "至" term:max : term
syntax:max "跳"   "至" term:max : term

macro_rules
  | `(比爻 $a $b 至 $t) => `(YiInstr.branchYaoEq $a $b $t)
  | `(比时 $s 至 $t)    => `(YiInstr.branchShiEq $s $t)
  | `(跳 至 $t)         => `(YiInstr.jump $t)

/-! ## § 6  程 块：sepBy(term, "；") → List YiInstr -/

syntax "程" "{" sepBy(term, "；") "}" : term

macro_rules
  | `(程 { $[$is]；* }) => `(([$[$is],*] : List YiInstr))

/-! ## § 7  Sanity 测试：原子 -/

example : (YiInstr.nop  : YiInstr) = 不动 := rfl
example : (YiInstr.halt : YiInstr) = 终   := rfl
example : (YiInstr.interlace   : YiInstr) = 互   := rfl
example : (YiInstr.complement  : YiInstr) = 错   := rfl
example : (YiInstr.reverse : YiInstr) = 综   := rfl
example : (YiInstr.push : YiInstr) = 推   := rfl
example : (YiInstr.pop  : YiInstr) = 取   := rfl

/-! ## § 8  Sanity 测试：参数化 -/

example : 设时 已 = YiInstr.setShi Shi.ji := rfl
example : 设时 今 = YiInstr.setShi Shi.jin := rfl
example : 设时 未 = YiInstr.setShi Shi.wei := rfl

example : 翻爻 初爻 = YiInstr.flipYao ⟨0, by omega⟩ := rfl
example : 翻爻 上爻 = YiInstr.flipYao ⟨5, by omega⟩ := rfl

/-! ## § 9  Sanity 测试：至-specials -/

example : 比爻 三爻 四爻 至 3
        = YiInstr.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ 3 := rfl

example : 比时 未 至 7
        = YiInstr.branchShiEq Shi.wei 7 := rfl

example : 跳 至 5 = YiInstr.jump 5 := rfl

/-! ## § 10  Sanity 测试：程 块 -/

example : 程 { 终 } = [YiInstr.halt] := rfl

example : 程 { 不动 ； 终 } = [YiInstr.nop, YiInstr.halt] := rfl

example : 程 { 设时 未 ； 终 }
        = [YiInstr.setShi Shi.wei, YiInstr.halt] := rfl

/-! ## § 11  端到端：daoJudgeProg via Lean 块语法

  M3-甲 之 first light：原本由 String parser 处理之文言文，
  现于 Lean 编译期由本模块解析为 daoJudgeProg。
  与 `Bagua.BaguaTuring.daoJudgeProg` 字面同体，由 rfl 见证。
-/

/-- 道判机 之 Lean 块语法直写形式。 -/
def daoJudgeBlock : List YiInstr :=
  程 { 比爻 三爻 四爻 至 3 ；
       设时 未  ；  终  ；
       设时 已  ；  终 }

/-- M3-甲 之 first light：Lean 块语法直写 = daoJudgeProg。 -/
theorem daoJudgeBlock_eq_daoJudgeProg :
    daoJudgeBlock = daoJudgeProg := rfl

/-! ## § 12  与 M1 String parser 之 commute

  M1 之 `«解程» «道判源»`（运行时 String → List YiInstr）
  与 M3-甲 之 `daoJudgeBlock`（编译时 Lean → List YiInstr）字面同体.
  由 `Foundation.Wen.Demo.daojudge_parse` 与 本文件之 daoJudgeBlock_eq_daoJudgeProg
  共同见证：
    · String → daoJudgeProg                   (M1 native_decide)
    · Lean block → daoJudgeProg               (M3-甲 rfl)
    · ∴ String → daoJudgeProg = Lean block    （传递）
-/

/-! ## § 13  长程序范例 -/

/-- 一段 8-instr 程序，展示组合用法。 -/
def sampleProg : List YiInstr :=
  程 { 不动 ；
       翻爻 初爻 ；
       互 ；
       错 ；
       综 ；
       设时 今 ；
       跳 至 7 ；
       终 }

theorem sampleProg_length : sampleProg.length = 8 := rfl

theorem sampleProg_explicit :
    sampleProg = [YiInstr.nop, YiInstr.flipYao ⟨0, by omega⟩,
                  YiInstr.interlace, YiInstr.complement, YiInstr.reverse,
                  YiInstr.setShi Shi.jin, YiInstr.jump 7, YiInstr.halt] := rfl

end SSBX.Foundation.Wen.WenyanSyntax
