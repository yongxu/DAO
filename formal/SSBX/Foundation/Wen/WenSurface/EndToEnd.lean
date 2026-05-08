/-
# WenSurface.EndToEnd — 文表层端到端管线

把 lex / resolve / parse / elab / typecheck / denote 拼成单一入口：
  · `wenyanCompile : String → Except WenSurfaceErr TypedTm`
  · `wenyanInterp : String → Except WenSurfaceErr Hexagram`
  · `wenyanInterpBool : String → Except WenSurfaceErr Bool`
  · `wenyanInterpHexPair` / `wenyanInterpHexList` for exact carrier values

求值复用既有 [WenDefEval.denoteHex / denoteBool / denoteHexPair / denoteHexList](../WenDefEval.lean)，
不走 baguaWen IL（保留 [WenDefCompile.lean](../WenDefCompile.lean) 的
cuo-equivariant 子集 commute 作 future work）。

## 当前范围

- cue-aware resolver + explicit `SurfaceExpr` AST
- 64 卦名 / aliases + Bool literals + Hex-only binders
- executable registry 覆盖全部 371 个 OperatorId
- 371 个 exact/theorem-backed operator 可求 Hex/Bool/Pair/List；structural catalogue fallback 不再覆盖 catalogue row
- unpromoted gap form 只诊断，不伪造 denotation

## 状态

0 sorry / 0 axiom / 总函数. 端到端例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Elaborate

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Text.OperatorSignatures

/-! ## § 1  统一错误类型 -/

/-- WenSurface pipeline 之统一错误。 -/
inductive WenSurfaceErr where
  | lex     (e : LexErr)
  | resolve (e : ResolveErr)
  | parse   (e : ParseErr)
  | elab    (e : ElabErr)
  | denoteFailed (expected actual : Ty)
deriving DecidableEq, Repr

/-! ## § 2  端到端管线 -/

/-- String → typed Tm 之完整管线（lex + cue-aware resolve + parse + elab + typecheck）. -/
def wenyanCompile (s : String) : Except WenSurfaceErr TypedTm :=
  match lexWen s with
  | .error e => .error (.lex e)
  | .ok toks =>
    match resolveWithCues toks with
    | .error e => .error (.resolve e)
    | .ok rs =>
      match parseSurfaceResolved rs with
      | .error e => .error (.parse e)
      | .ok expr =>
        match elabSurfaceTyped expr with
        | .error e => .error (.elab e)
        | .ok t    => .ok t

/-- Backward-compatible untyped projection for code that only needs the Tm. -/
def wenyanCompileTm (s : String) : Except WenSurfaceErr Tm :=
  (wenyanCompile s).map (fun typed => typed.tm)

/-- 闭项 hex 求值：String → Hexagram. -/
def wenyanInterp (s : String) : Except WenSurfaceErr Hexagram :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok typed =>
    match denoteHex typed.tm with
    | some h => .ok h
    | none   => .error (.denoteFailed .hex typed.ty)

/-- 闭项 bool 求值：String → Bool. -/
def wenyanInterpBool (s : String) : Except WenSurfaceErr Bool :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok typed =>
    match denoteBool typed.tm with
    | some b => .ok b
    | none   => .error (.denoteFailed .bool typed.ty)

def wenyanInterpHexPair (s : String) : Except WenSurfaceErr (Hexagram × Hexagram) :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok typed =>
    match denoteHexPair typed.tm with
    | some p => .ok p
    | none   => .error (.denoteFailed (.prod .hex .hex) typed.ty)

def wenyanInterpHexList (s : String) : Except WenSurfaceErr (List Hexagram) :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok typed =>
    match denoteHexList typed.tm with
    | some xs => .ok xs
    | none    => .error (.denoteFailed (.list .hex) typed.ty)

/-! ## § 3  端到端 sanity 例子 -/

/-- 「一」 → «一». -/
example : (wenyanInterp "一").toOption = some «一» := by native_decide

/-- 「推 一」 → «生» «一»（即 hex idx 2）. -/
example : (wenyanInterp "推 一").toOption = some («生» «一») := by native_decide

/-- 「推 推 一」 → «生生» 2 «一». -/
example : (wenyanInterp "推 推 一").toOption = some («生生» 2 «一») := by native_decide

/-- 「推 推 推 一」 → «生生» 3 «一». -/
example :
    (wenyanInterp "推 推 推 一").toOption = some («生生» 3 «一») :=
  by native_decide

/-- 「推 推 推 推 一」 → «生生» 4 «一». -/
example :
    (wenyanInterp "推 推 推 推 一").toOption = some («生生» 4 «一») :=
  by native_decide

/-- 64 次「推」打回原点（«生生» 64 «一» = «一»）. -/
example :
    let chain := String.intercalate " " (List.replicate 64 "推") ++ " 一"
    (wenyanInterp chain).toOption = some «一» :=
  by native_decide

/-- 「乾」→ Hexagram.qian (idx 0). -/
example : (wenyanInterp "乾").toOption = some Hexagram.qian := by native_decide

/-- 「坤」→ Hexagram.kun (idx 63). -/
example : (wenyanInterp "坤").toOption = some Hexagram.kun := by native_decide

/-- 「推 乾」→ «生» «乾» = «一»（idx 0 + 1 mod 64 = 1）. -/
example : (wenyanInterp "推 乾").toOption = some «一» := by native_decide

/-- 「推 坤」→ «生» «坤» = «乾»（idx 63 + 1 mod 64 = 0，周而复始）. -/
example :
    (wenyanInterp "推 坤").toOption = some Hexagram.qian :=
  by native_decide

/-! ### 「之」 应用标记测试（显式 AST marker，elab 时透明） -/

/-- 「推 之 一」≡「推 一」，「之」elab 时被过滤. -/
example :
    (wenyanInterp "推 之 一").toOption = (wenyanInterp "推 一").toOption :=
  by native_decide

/-- 「推 之 推 之 一」 ≡ 「推 推 一」 = «生生» 2 «一». -/
example :
    (wenyanInterp "推 之 推 之 一").toOption = some («生生» 2 «一») :=
  by native_decide

/-- 尾随「之」不再被静默吞掉。 -/
example :
    (wenyanInterp "推 乾 之").toOption = none :=
  by native_decide

/-! ### 二元谓词测试（arity-driven 解析） -/

/-- 「同 一 一」 → true（恒等成立）. -/
example : (wenyanInterpBool "同 一 一").toOption = some true := by native_decide

/-- 「同 一 乾」 → false（«一» ≠ «乾»）. -/
example : (wenyanInterpBool "同 一 乾").toOption = some false := by native_decide

/-- 「同 乾 乾」 → true. -/
example : (wenyanInterpBool "同 乾 乾").toOption = some true := by native_decide

/-- 「比 一 一」 → true（v1 比 = 同）. -/
example : (wenyanInterpBool "比 一 一").toOption = some true := by native_decide

/-- 「比 乾 坤」 → false. -/
example : (wenyanInterpBool "比 乾 坤").toOption = some false := by native_decide

/-! ### Hex/operator surface collision tests

  「比」「益」「损/損」既可作已执行算子，也可作卦名。parser 在 prefix
  表达式中可用作算子；在裸值或需给后续参数预留 token 的位置回退为卦名。
-/

example : (wenyanInterp "比").toOption = resolveHexConst "比" := by native_decide

example :
    (wenyanInterpBool "同 比 比").toOption = some true :=
  by native_decide

example :
    (wenyanInterpBool "比 乾 坤").toOption = some false :=
  by native_decide

example :
    (wenyanInterp "益 乾").toOption = some («生» Hexagram.qian) :=
  by native_decide

example :
    (wenyanInterpBool "同 益 乾").toOption = some false :=
  by native_decide

example :
    (wenyanInterpBool "同 损 损").toOption = some true :=
  by native_decide

example : (wenyanInterp "大壯").toOption = (wenyanInterp "大壮").toOption := by native_decide

example : (wenyanInterp "鼎").toOption = resolveHexConst "鼎" := by native_decide

example : (wenyanInterp "鼎 乾").toOption = none := by native_decide

example :
    (match wenyanCompile "鼎 乾" with
     | .error (.parse (.unpromotedHexagramGap "鼎" 0)) => true
     | _ => false) = true :=
  by native_decide

example : (wenyanInterp "丽").toOption = none := by native_decide

example :
    (match wenyanCompile "丽" with
     | .error (.resolve (.unpromotedHexagramGap "丽" 0)) => true
     | _ => false) = true :=
  by native_decide

example :
    (match wenyanCompile "大" with
     | .error (.resolve (.unpromotedHexagramGap "大" 0)) => true
     | _ => false) = true :=
  by native_decide

example :
    (match wenyanCompile "在 乾 坤" with
     | .ok typed => typed.ty = .bool
     | _ => false) = true :=
  by native_decide

example : (wenyanInterpBool "在 乾 乾").toOption = some true := by native_decide
example : (wenyanInterpBool "在 乾 坤").toOption = some false := by native_decide
example : (wenyanInterpBool "含 乾 坤").toOption = some false := by native_decide
example : (wenyanInterpBool "識 乾").toOption = some true := by native_decide
example : (wenyanInterpBool "大一 乾").toOption = some true := by native_decide

example :
    (match wenyanCompile "五行 乾" with
     | .ok typed => typed.ty = .list .hex
     | _ => false) = true :=
  by native_decide

example :
    (wenyanInterpHexList "五行 乾").toOption = some [Hexagram.qian] :=
  by native_decide

example :
    (match wenyanCompile "或 乾" with
     | .error (.resolve (.ambiguous "或" 0 candidates)) => candidates.length == 2
     | _ => false) = true :=
  by native_decide

example :
    (match wenyanCompile "名分 乾" with
     | .error (.resolve (.ambiguous "名分" 0 candidates)) => candidates.length == 2
     | _ => false) = true :=
  by native_decide

example : (parseSurface "乾 之 坤").toOption.isSome = true := by native_decide

example : (wenyanCompile "乾 之 坤").toOption = none := by native_decide

/-! ### promoted logic / identity catalogue operators -/

example :
    (wenyanInterpBool "則 真 假").toOption = some false :=
  by native_decide

example :
    (match wenyanCompile "故 假 假" with
     | .error (.resolve (.ambiguous "故" 0 candidates)) => candidates.length == 3
     | _ => false) = true :=
  by native_decide

example :
    (wenyanInterpBool "且 真 假").toOption = some false :=
  by native_decide

example :
    (wenyanInterpBool "弗 真").toOption = some false :=
  by native_decide

example :
    (wenyanInterpBool "勿 假").toOption = some true :=
  by native_decide

example :
    (wenyanInterpBool "是 乾 乾").toOption = some true :=
  by native_decide

example :
    (wenyanInterpBool "非 乾 坤").toOption = some true :=
  by native_decide

example :
    (wenyanInterpBool "異 乾 乾").toOption = some false :=
  by native_decide

example :
    (wenyanInterpBool "皆 者 甲 同 甲 甲").toOption = some true :=
  by native_decide

example :
    (match wenyanCompile "或 者 甲 同 甲 一" with
     | .error (.resolve (.ambiguous "或" 0 candidates)) => candidates.length == 2
     | _ => false) = true :=
  by native_decide

example :
    (wenyanInterpBool "莫 者 甲 同 甲 一").toOption = some false :=
  by native_decide

theorem canonicalHexNames_interpret_to_xuGua :
    canonicalHexNameRows.all
        (fun row => decide ((wenyanInterp row.fst).toOption = some row.snd)) = true := by
  native_decide

theorem hexNameAliases_interpret_to_canonical :
    hexNameAliases.all
        (fun row => decide ((wenyanInterp row.fst).toOption = (wenyanInterp row.snd).toOption)) = true := by
  native_decide

/-- 嵌套：「同 推 一 推 一」 → 「same 一+1 一+1」 = true. -/
example :
    (wenyanInterpBool "同 推 一 推 一").toOption = some true :=
  by native_decide

/-- 「同 推 乾 一」 → 「«生» «乾» = «一»」 = true（旋转闭合）. -/
example :
    (wenyanInterpBool "同 推 乾 一").toOption = some true :=
  by native_decide

/-- 「同 推 坤 乾」 → 「«生» «坤» = «乾»」 = true（cyclic closure）. -/
example :
    (wenyanInterpBool "同 推 坤 乾").toOption = some true :=
  by native_decide

/-- 「不 同 一 一」 → ¬true = false. -/
example :
    (wenyanInterpBool "不 同 一 一").toOption = some false :=
  by native_decide

/-- 「不 同 一 乾」 → ¬false = true. -/
example :
    (wenyanInterpBool "不 同 一 乾").toOption = some true :=
  by native_decide

/-! ### Bool 字面值测试 -/

/-- 「真」 → true. -/
example : (wenyanInterpBool "真").toOption = some true := by native_decide

/-- 「假」 → false. -/
example : (wenyanInterpBool "假").toOption = some false := by native_decide

/-- 「不 真」 → false. -/
example : (wenyanInterpBool "不 真").toOption = some false := by native_decide

/-- 「不 假」 → true. -/
example : (wenyanInterpBool "不 假").toOption = some true := by native_decide

/-- 「不 不 真」 → ¬¬true = true. -/
example : (wenyanInterpBool "不 不 真").toOption = some true := by native_decide

/-- 「不 不 不 真」 → false. -/
example :
    (wenyanInterpBool "不 不 不 真").toOption = some false :=
  by native_decide

/-! ## § 4  错误路径 sanity -/

/-- 未知 surface「瓜」走 resolve 错误. -/
example : (wenyanInterp "瓜").toOption = none := by native_decide

/-- ASCII 走 lex 错误. -/
example : (wenyanInterp "abc").toOption = none := by native_decide

/-- 空串：empty elab. -/
example : (wenyanInterp "").toOption = none := by native_decide

/-! ## § 5  与 stdlib 既有定理之桥 -/

/-- 「推 一」之 elab Tm 等于 `.app Stdlib.tuiBody .yi`. -/
example :
    (wenyanCompileTm "推 一").toOption = some (.app Stdlib.tuiBody .yi) :=
  by native_decide

/-! ### Grouping punctuation -/

example :
    (wenyanInterp "（推 一）").toOption = (wenyanInterp "推 一").toOption :=
  by native_decide

example :
    (wenyanInterp "(推 一)").toOption = (wenyanInterp "推 一").toOption :=
  by native_decide

example :
    (wenyanInterpBool "同 （推 一） （推 一）").toOption = some true :=
  by native_decide

example : (wenyanInterp "（推 一").toOption = none := by native_decide

example : (wenyanInterp "推 一）").toOption = none := by native_decide

/-- 与 `tui_eq_sheng` 桥 — 用 wenyan 表层走 stdlib 算子等价于 YiCore.«生». -/
theorem wenyan_tui_yi_eq_sheng :
    (wenyanInterp "推 一").toOption = some («生» «一») := by
  native_decide

/-! ## § 6  損/益 端到端 -/

/-- 「益 一」 → «生» «一»（即 hex idx 2）；与「推 一」等价. -/
example : (wenyanInterp "益 一").toOption = some («生» «一») := by native_decide

/-- 「損 一」 → «一» − 1 = idx 0 = «乾». -/
example : (wenyanInterp "損 一").toOption = some Hexagram.qian := by native_decide

/-- 「損 乾」 → «乾» − 1 = idx -1 mod 64 = idx 63 = «坤». -/
example : (wenyanInterp "損 乾").toOption = some Hexagram.kun := by native_decide

/-- 简体「损」也认得. -/
example : (wenyanInterp "损 一").toOption = some Hexagram.qian := by native_decide

/-- 「益 损 一」 → ((一 − 1) + 1) = 一. -/
example : (wenyanInterp "益 损 一").toOption = some «一» := by native_decide

/-- 「损 益 乾」 → ((乾 + 1) − 1) = 乾. -/
example : (wenyanInterp "损 益 乾").toOption = some Hexagram.qian := by native_decide

/-! ## § 6.25 exact Hex transforms -/

example : (wenyanInterp "错 乾").toOption = some Hexagram.kun := by native_decide
example : (wenyanInterp "錯 乾").toOption = some Hexagram.kun := by native_decide
example : (wenyanInterp "综 乾").toOption = some Hexagram.qian := by native_decide
example : (wenyanInterp "互 坤").toOption = some Hexagram.kun := by native_decide
example : (wenyanInterp "改 乾").toOption = some (dongInner Hexagram.qian) := by native_decide
example : (wenyanInterp "轉 乾").toOption = some Hexagram.qian.zong := by native_decide
example : (wenyanInterp "伸 乾").toOption = some («生» Hexagram.qian) := by native_decide
example : (wenyanInterp "屈 乾").toOption = some («加» Hexagram.kun Hexagram.qian) := by native_decide
example : (wenyanInterp "起 乾").toOption = some («生» Hexagram.qian) := by native_decide
example : (wenyanInterp "止 乾").toOption = some Hexagram.qian := by native_decide
example : (wenyanInterp "進 乾").toOption = some («生» Hexagram.qian) := by native_decide
example : (wenyanInterp "退 乾").toOption = some («加» Hexagram.kun Hexagram.qian) := by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.F_1).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.F_2).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.F_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.F_8).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.F_11).isSome = true :=
  by native_decide
example : (wenyanInterp "藏 乾").toOption = some («加» Hexagram.kun Hexagram.qian) := by native_decide
example : (wenyanInterp "露 乾").toOption = some («生» Hexagram.qian) := by native_decide
example : (wenyanInterp "明 乾").toOption = some («生» Hexagram.qian) := by native_decide
example : (wenyanInterp "蔽 乾").toOption = some («加» Hexagram.kun Hexagram.qian) := by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.M_5).isSome = true :=
  by native_decide
example : (wenyanInterp "使 推 乾").toOption = some («生» Hexagram.qian) := by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.K_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.L_7).isSome = true :=
  by native_decide
example : (wenyanInterpBool "若 真").toOption = some true := by native_decide
example : (wenyanInterp "再 推 乾").toOption = some («生» («生» Hexagram.qian)) := by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_6).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Q_3).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.D_9).isSome = true :=
  by native_decide
example : (wenyanInterpBool "宜 真 假").toOption = some false := by native_decide
example : (wenyanInterpBool "能 假 真").toOption = some true := by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.M_7).isSome = true :=
  by native_decide
example :
    (wenyanCompile "偶 乾 坤").toOption.map (·.ty) =
      some (.prod .hex .hex) :=
  by native_decide
example :
    (wenyanInterpHexPair "偶 乾 坤").toOption =
      some (Hexagram.qian, Hexagram.kun) :=
  by native_decide
example :
    (wenyanInterpHexPair "偕 乾 坤").toOption =
      some (Hexagram.qian, Hexagram.kun) :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.R_14).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.T_3).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.T_11).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.K_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.N_8).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.I_7).isSome = true :=
  by native_decide
example :
    structuralCatalogueOperatorIds.length = 0 :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.E_2).isSome = true :=
  by native_decide
example :
    (wenyanCompile "曰 乾 坤").toOption.map (·.ty) =
      some (.prod .hex .hex) :=
  by native_decide
example :
    (wenyanInterpHexPair "曰 乾 坤").toOption =
      some (Hexagram.qian, Hexagram.kun) :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.CHU_2).isSome = true :=
  by native_decide
example :
    (wenyanCompile "上下 乾 坤 一").toOption.map (·.ty) =
      some (.list .hex) :=
  by native_decide
example :
    (wenyanInterpHexList "上下 乾 坤 一").toOption =
      some [Hexagram.qian, Hexagram.kun, «一»] :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_11).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_13).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_22).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.D_8).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.L_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.X_4).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_21).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.X_14).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_19).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.CHU_9).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.H_8).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_1).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_6).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_8).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_10).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_11).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_12).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_13).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_14).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_15).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_21).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_22).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_23).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_24).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_25).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_26).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Y_27).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_26).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_27).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_34).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_35).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.G_2).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.G_4).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_23).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.X_1).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.ZHU_10).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.SUN_1).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.SUN_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.ZA_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.LIJ_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.ZA_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.ZA_3).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.ZA_11).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.C_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.C_6).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.B_1).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.B_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.R_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.C_4).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.C_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.C_8).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.B_2).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_10).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_12).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.G_8).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_3).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.L_13).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.G_9).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.H_1).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.H_2).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.H_3).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.H_4).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.H_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.H_6).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_2).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_6).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_18).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_24).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.G_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.L_3).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.L_12).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.L_15).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_24).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.ZHU_9).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.SUN_2).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.SUN_3).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.SUN_4).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.SUN_14).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.CHU_4).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.CHU_5).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.LIJ_4).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.LIJ_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.LIJ_11).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.ZA_6).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.S_9).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.S_10).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.S_11).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.S_12).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.S_17).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.S_18).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.S_19).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.P_23).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_1).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_2).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_3).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_8).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_9).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_10).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_15).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_16).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_17).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_18).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_19).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.A_20).isSome = true :=
  by native_decide
example :
    (wenyanInterpHexPair "兩 乾").toOption =
      some (Hexagram.qian, Hexagram.qian) :=
  by native_decide
example :
    (wenyanInterpHexList "聚 乾").toOption = some [Hexagram.qian] :=
  by native_decide
example :
    (wenyanInterp "散 聚 乾").toOption = some Hexagram.qian :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_17).isSome = true :=
  by native_decide
example :
    (wenyanCompile "改").toOption.map (·.ty) = some (.arr .hex .hex) :=
  by native_decide
example :
    (match wenyanCompile "化 乾" with
     | .error (.resolve (.ambiguous "化" 0 candidates)) => candidates.length == 2
     | _ => false) = true :=
  by native_decide
example :
    (match wenyanCompile "反 乾" with
     | .error (.resolve (.ambiguous "反" 0 candidates)) => candidates.length == 3
     | _ => false) = true :=
  by native_decide

/-! ## § 6.26 exact Bool / finite quantifier promotions -/

example : (wenyanInterpBool "遂 真 假").toOption = some false := by native_decide
example : (wenyanInterpBool "但 真 假").toOption = some false := by native_decide
example : (wenyanInterpBool "過半 者 甲 真").toOption = some true := by native_decide

example :
    (wenyanCompile "三").toOption.map (·.ty) =
      some (.arr (.arr .hex .bool) .bool) :=
  by native_decide

example :
    (theoremBackedSemanticsFor? OperatorId.Q_8).isSome = true := by native_decide

example :
    (theoremBackedSemanticsFor? OperatorId.D_10).isSome = true := by native_decide

example :
    (wenyanInterp "（而 者 甲 推 甲 者 甲 損 甲） 之 一").toOption = some «一» :=
  by native_decide

example : (wenyanInterp "而 推 損 一").toOption = some «一» := by native_decide

example : (wenyanInterp "而 损 推 一").toOption = some «一» := by native_decide

example :
    (wenyanCompile "而 推 損").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example :
    (wenyanCompile "推").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example :
    (wenyanCompile "不").toOption.map (·.ty)
      = some (.arr .bool .bool) :=
  by native_decide

example :
    (wenyanCompile "同 乾").toOption.map (·.ty)
      = some (.arr .hex .bool) :=
  by native_decide

example :
    (wenyanCompile "（推）").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example :
    (wenyanCompile "（同 乾）").toOption.map (·.ty)
      = some (.arr .hex .bool) :=
  by native_decide

example : (wenyanInterpBool "（同 乾） 乾").toOption = some true := by native_decide

example : (wenyanInterp "者 甲 推 甲 乾").toOption = some «一» := by native_decide

example :
    (match wenyanCompile "而 不 不 真" with
     | .error (.parse (.typeMismatch (.arr .hex .hex) (.arr .bool .bool) "不" 2)) => true
     | _ => false) = true :=
  by native_decide

example :
    (match wenyanCompile "在 乾" with
     | .ok typed => typed.ty = .arr .hex .bool
     | _ => false) = true :=
  by native_decide

/-! ## § 6.3 prefix binder / let forms -/

example :
    (wenyanInterpBool "凡 甲 同 甲 甲").toOption = some true :=
  by native_decide

example :
    (wenyanInterpBool "令 甲 乾 同 甲 乾").toOption = some true :=
  by native_decide

example :
    (wenyanInterp "令 甲 乾 推 甲").toOption = some «一» :=
  by native_decide

/-! ## § 6.5  之又 iteration construction (Phase D)

  「之又 F X」 = F (F X)。语义上等价于 «生生» 2 X 当 F = «生»（即 surface 推）。
  与 stdlib 一元算子组合：之又 推 / 之又 不 各为 hex / bool 之双重应用。
-/

/-- 「之又 推 一」 = 推 (推 一) = «生生» 2 «一». -/
example :
    (wenyanInterp "之又 推 一").toOption = some («生生» 2 «一») := by native_decide

/-- 「之又 推 乾」 = 推 (推 乾) = «生生» 2 «乾» = idx 2. -/
example :
    (wenyanInterp "之又 推 乾").toOption = some («生生» 2 Hexagram.qian) :=
  by native_decide

/-- 之又 + 不 + 真 — 双重否定 = 真. -/
example :
    (wenyanInterpBool "之又 不 真").toOption = some true := by native_decide

/-- 之又 + 不 + 假 — 双重否定 假 = 假. -/
example :
    (wenyanInterpBool "之又 不 假").toOption = some false := by native_decide

/-! ## § 7  公示总结 -/

/-- 基础公示：早期 stdlib 算子 + 「一」的端到端可达性。
    `推`/`一` 的合成结果与 YiCore.«生»/«生生» 一致。 -/
theorem v1_endToEnd_summary :
    (wenyanInterp "一").toOption = some «一»
    ∧ (wenyanInterp "推 一").toOption = some («生» «一»)
    ∧ (wenyanInterp "推 推 一").toOption = some («生生» 2 «一»)
    ∧ (wenyanInterp "推 推 推 一").toOption = some («生生» 3 «一»)
    := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## § 7  Phase C cue resolution 端到端 sanity

  cue-aware resolver (`resolveWithCues`) 与 simple resolver (`resolveSimple`)
  在不含「之」的 stdlib 流上完全等价 —— 这里给一组 atom 序列见证.

  含「之」时，cue 路径将「之」消歧为 S_1 catalogue（v1 路径里是 appMarker），
  parser 将其保留成 explicit marker，elab 时透明处理。本节 verify
  resolveWithCues 之 atom 序列正确性，与 cue → unique reading 桥定理. -/

/-- 不含「之」的程序：cue-aware resolve 之 atom 序列与 simple resolve 一致.
    通过这一 bridge，「推 一」之意义不依赖路径选择. -/
example :
    let toks : List GlyphTok :=
      [⟨"推", 0, 1, false⟩, ⟨"一", 2, 1, false⟩]
    ((resolveWithCues toks).toOption.map (fun rs => rs.map (·.atom)))
      = ((resolveSimple toks).toOption.map (fun rs => rs.map (·.atom))) :=
  by native_decide

/-- 「推 一」之 cue resolve 序列同 v1 resolve 序列（atom 等价）. -/
example :
    let toks : List GlyphTok :=
      [⟨"推", 0, 1, false⟩, ⟨"比", 2, 1, false⟩, ⟨"不", 4, 1, false⟩,
       ⟨"必", 6, 1, false⟩, ⟨"同", 8, 1, false⟩, ⟨"凡", 10, 1, false⟩,
       ⟨"一", 12, 1, false⟩]
    ((resolveWithCues toks).toOption.map (fun rs => rs.map (·.atom)))
      = ((resolveSimple toks).toOption.map (fun rs => rs.map (·.atom))) :=
  by native_decide

/-- 「推 之 一」cue resolve 比 v1 resolve 多识：「之」拿到 S_1 catalogue.
    具体地：v1 给 [T_10-cat, appMarker, hex«一»]；cue 给 [T_10-cat, S_1-cat, hex«一»]. -/
example :
    let toks : List GlyphTok :=
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩]
    ((resolveWithCues toks).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?)))
      = some [some OperatorId.T_10, some OperatorId.S_1, none] :=
  by native_decide

/-- simple 路径仍把同一程序之「之」识为 appMarker（无 OperatorId）—— 与 cue 路径成对.
    note: opId? 在 catalogueOp 时返 reading.operator?；appMarker 时返 none. -/
example :
    let toks : List GlyphTok :=
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩]
    ((resolveSimple toks).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?)))
      = some [some OperatorId.T_10, none, none] :=
  by native_decide

/-- 桥定理：cue 路径 + uniqueCatalogueReading 同 OperatorReadings.
    `zhi_between_nominals_unique` (line 749-751) 桥. -/
theorem wensurface_zhi_between_nominals_S1 :
    (uniqueCatalogueReading "之" [.betweenNominals]).bind (·.operator?)
      = some OperatorId.S_1 :=
  zhi_between_nominals_unique_catalogue

/-- 端到端 cue → unique reading：「推 之 一」之 i=1 处 cues 为
    [.betweenNominals]，从而「之」唯一对应 S_1 catalogue. -/
theorem zhi_in_tui_zhi_yi_resolves_S1 :
    let toks : List GlyphTok :=
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩]
    (uniqueCatalogueReading "之" (computeCues toks 1)).bind (·.operator?)
      = some OperatorId.S_1 :=
  by native_decide

/-- 当前 wenyanInterp 走 cue-aware resolver：
    「推 之 一」 = «生» «一»，显式 marker 透明. -/
example :
    (wenyanInterp "推 之 一").toOption = some («生» «一») :=
  by native_decide

end SSBX.Foundation.Wen.WenSurface
