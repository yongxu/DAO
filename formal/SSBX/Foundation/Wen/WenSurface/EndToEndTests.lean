/-
# WenSurface.EndToEndTests — sanity examples + theorems via native_decide

Phase γ note: split out of `EndToEnd.lean` (commit efd892a, 2026-05-15) because
after `Hexagram` became `Fin 6 → Bool` (function type, not inductive struct),
`native_decide` per-example compilation overhead is dramatic — full build of
the 318 examples here exceeds 1 hour wall-clock on a laptop.

The pipeline definitions (`wenyanInterp`, `wenyanInterpBool`, etc.) live in
`EndToEnd.lean` and are imported by `SSBX.lean`.  This module imports them
but is **NOT** in `SSBX.lean`'s import chain — it builds on demand via
`lake build SSBX.Foundation.Wen.WenSurface.EndToEndTests`.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Text.OperatorSignatures

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

/-- 「乾」→ Hexagram.heaven (idx 0). -/
example : (wenyanInterp "乾").toOption = some Hexagram.heaven := by native_decide

/-- 「坤」→ Hexagram.earth (idx 63). -/
example : (wenyanInterp "坤").toOption = some Hexagram.earth := by native_decide

/-- 「推 乾」→ «生» «乾» = «一»（idx 0 + 1 mod 64 = 1）. -/
example : (wenyanInterp "推 乾").toOption = some «一» := by native_decide

/-- 「推 坤」→ «生» «坤» = «乾»（idx 63 + 1 mod 64 = 0，周而复始）. -/
example :
    (wenyanInterp "推 坤").toOption = some Hexagram.heaven :=
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

/-! ### Relation infix forms -/

example : (wenyanInterpBool "一 同 一").toOption = some true := by native_decide

example : (wenyanInterpBool "推 乾 同 一").toOption = some true := by native_decide

example : (wenyanInterpBool "（推 乾） 同 一").toOption = some true := by native_decide

example : (wenyanInterpBool "乾 比 坤").toOption = some false := by native_decide

example :
    (match wenyanCompile "一 同 一 同 一" with
     | .error (.parse (.nonassocInfix "同" 6)) => true
     | _ => false) = true :=
  by native_decide

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
    (wenyanInterp "益 乾").toOption = some («生» Hexagram.heaven) :=
  by native_decide

example :
    (wenyanInterpBool "同 益 乾").toOption = some false :=
  by native_decide

example :
    (wenyanInterpBool "同 损 损").toOption = some true :=
  by native_decide

example : (wenyanInterp "大壯").toOption = (wenyanInterp "大壮").toOption := by native_decide

example : (wenyanInterp "器").toOption = resolveHexConst "鼎" := by native_decide

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
    (wenyanInterpHexList "五行 乾").toOption = some [Hexagram.heaven] :=
  by native_decide

example :
    (match wenyanCompile "曰 乾 乾" with
     | .ok typed => typed.ty = .prod .hex .hex
     | _ => false) = true :=
  by native_decide

example :
    (wenyanInterpHexPair "曰 乾 乾").toOption =
      some (Hexagram.heaven, Hexagram.heaven) :=
  by native_decide

example :
    (match wenyanCompile "教 乾 坤 一" with
     | .ok typed => typed.ty = .list .hex
     | _ => false) = true :=
  by native_decide

example :
    (wenyanInterpHexList "教 乾 坤 一").toOption =
      some [Hexagram.heaven, Hexagram.earth, «一»] :=
  by native_decide

example :
    (match wenyanCompile "曰 真 真" with
     | .error (.elab (.typeMismatch (.argumentMismatch .hex .bool))) => true
     | _ => false) = true :=
  by native_decide

/-- B-5: `或` now resolves to `Tm.orB : Bool → Bool → Bool` builtin
    (priority above catalogue), so `或 乾` is no longer an ambiguous
    catalogue resolve.  It still fails to compile — `或` is arity-2
    and only one argument follows. -/
example :
    (wenyanCompile "或 乾").toOption.isNone = true :=
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

/-- B-5: `或 者 ...` previously routed to the `Q_5` existential
    quantifier via the catalogue + 「者」 cue.  After B-5, `或` resolves
    directly to the `Tm.orB : Bool → Bool → Bool` builtin (priority
    above the catalogue), so this construction is no longer reachable
    via `或`.  The existential surface is intentionally left without a
    direct test here — the `Tm.orB` semantics is covered by the B-5
    builtin tests in `Reading.lean`. -/
example :
    (wenyanInterpBool "或 真 假").toOption = some true :=
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

example :
    (wenyanInterpBool "于 同 乾 乾").toOption = some true :=
  by native_decide

example :
    (wenyanInterpBool "地 同 乾 坤").toOption = some false :=
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
example : (wenyanInterp "損 一").toOption = some Hexagram.heaven := by native_decide

/-- 「損 乾」 → «乾» − 1 = idx -1 mod 64 = idx 63 = «坤». -/
example : (wenyanInterp "損 乾").toOption = some Hexagram.earth := by native_decide

/-- 简体「损」也认得. -/
example : (wenyanInterp "损 一").toOption = some Hexagram.heaven := by native_decide

/-- 「益 损 一」 → ((一 − 1) + 1) = 一. -/
example : (wenyanInterp "益 损 一").toOption = some «一» := by native_decide

/-- 「损 益 乾」 → ((乾 + 1) − 1) = 乾. -/
example : (wenyanInterp "损 益 乾").toOption = some Hexagram.heaven := by native_decide

/-! ## § 6.25 exact Hex transforms -/

example : (wenyanInterp "错 乾").toOption = some Hexagram.earth := by native_decide
example : (wenyanInterp "錯 乾").toOption = some Hexagram.earth := by native_decide
example : (wenyanInterp "综 乾").toOption = some Hexagram.heaven := by native_decide
example : (wenyanInterp "互 坤").toOption = some Hexagram.earth := by native_decide
example : (wenyanInterp "改 乾").toOption = some (dongInner Hexagram.heaven) := by native_decide
example : (wenyanInterp "轉 乾").toOption = some Hexagram.heaven.reverse := by native_decide
example : (wenyanInterp "伸 乾").toOption = some («生» Hexagram.heaven) := by native_decide
example : (wenyanInterp "屈 乾").toOption = some («加» Hexagram.earth Hexagram.heaven) := by native_decide
example : (wenyanInterp "起 乾").toOption = some («生» Hexagram.heaven) := by native_decide
example : (wenyanInterp "止 乾").toOption = some Hexagram.heaven := by native_decide
example : (wenyanInterp "進 乾").toOption = some («生» Hexagram.heaven) := by native_decide
example : (wenyanInterp "退 乾").toOption = some («加» Hexagram.earth Hexagram.heaven) := by native_decide
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
example : (wenyanInterp "藏 乾").toOption = some («加» Hexagram.earth Hexagram.heaven) := by native_decide
example : (wenyanInterp "露 乾").toOption = some («生» Hexagram.heaven) := by native_decide
example : (wenyanInterp "明 乾").toOption = some («生» Hexagram.heaven) := by native_decide
example : (wenyanInterp "蔽 乾").toOption = some («加» Hexagram.earth Hexagram.heaven) := by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.M_5).isSome = true :=
  by native_decide
example : (wenyanInterp "使 推 乾").toOption = some («生» Hexagram.heaven) := by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.K_7).isSome = true :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.L_7).isSome = true :=
  by native_decide
example : (wenyanInterpBool "若 真").toOption = some true := by native_decide
example : (wenyanInterp "再 推 乾").toOption = some («生» («生» Hexagram.heaven)) := by native_decide
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
      some (Hexagram.heaven, Hexagram.earth) :=
  by native_decide
example :
    (wenyanInterpHexPair "偕 乾 坤").toOption =
      some (Hexagram.heaven, Hexagram.earth) :=
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
      some (Hexagram.heaven, Hexagram.heaven) :=
  by native_decide
example :
    (wenyanInterpHexList "聚 乾").toOption = some [Hexagram.heaven] :=
  by native_decide
example :
    (wenyanInterp "散 聚 乾").toOption = some Hexagram.heaven :=
  by native_decide
example :
    (theoremBackedSemanticsFor? OperatorId.Z_17).isSome = true :=
  by native_decide
example : (wenyanInterp "静 乾").toOption = some Hexagram.heaven := by native_decide
example : (wenyanInterp "恒 乾").toOption = some Hexagram.heaven := by native_decide
example : (wenyanInterp "不动 乾").toOption = some Hexagram.heaven := by native_decide
example : (wenyanInterp "錯綜 乾").toOption = some Hexagram.heaven.complementReverse := by native_decide
example : (wenyanInterp "交错 乾").toOption = some Hexagram.heaven.complementReverse := by native_decide
example : (wenyanInterp "复 乾").toOption = some Hexagram.heaven := by native_decide
example : (wenyanInterp "归一 乾").toOption = some Hexagram.heaven := by native_decide
example : (wenyanInterp "展 乾").toOption = some («生» Hexagram.heaven) := by native_decide
example : (wenyanInterp "初动 乾").toOption = some (dongInner Hexagram.heaven) := by native_decide
example : (wenyanInterp "承变 乾").toOption = some (middleFlipInner Hexagram.heaven) := by native_decide
example : (wenyanInterp "际变 乾").toOption = some (topFlipInner Hexagram.heaven) := by native_decide
example :
    (wenyanCompile "改").toOption.map (·.ty) = some (.arr .hex .hex) :=
  by native_decide
example :
    (wenyanInterp "化 乾").toOption = some (middleFlipInner Hexagram.heaven) :=
  by native_decide
example :
    (wenyanInterp "反 乾").toOption = some Hexagram.heaven.complement :=
  by native_decide
example :
    (wenyanInterpBool "反 真").toOption = some false :=
  by native_decide

example :
    (wenyanCompile "反").toOption = none :=
  by native_decide

example :
    (match wenyanCompile "反" with
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
    (wenyanCompile "而 反 推").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example :
    (wenyanCompile "而 推 反").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example :
    (wenyanCompile "再 反").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example : (wenyanInterp "而 反 综 一").toOption = some «一».reverse.complement := by native_decide

example : (wenyanInterp "再 反 一").toOption = some «一».complement.complement := by native_decide

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
    (wenyanCompile "者 甲 甲").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example :
    (wenyanCompile "者 甲 不 甲").toOption.map (·.ty)
      = some (.arr .bool .bool) :=
  by native_decide

example :
    (wenyanCompile "者 甲 甲 之 乾").toOption.map (·.ty)
      = some (.arr (.arr .hex .hex) .hex) :=
  by native_decide

example :
    (wenyanCompile "者 甲 甲 之 真").toOption.map (·.ty)
      = some (.arr (.arr .bool .bool) .bool) :=
  by native_decide

example :
    (wenyanCompile "者 甲 同 甲 甲").toOption.map (·.ty)
      = some (.arr .hex .bool) :=
  by native_decide

example :
    (wenyanInterpBool "者 甲 甲 真").toOption = some true :=
  by native_decide

example :
    (wenyanInterpBool "者 甲 不 甲 真").toOption = some false :=
  by native_decide

example :
    (wenyanCompile "者 甲 甲 推").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example :
    (wenyanInterpBool "（者 甲 不 甲） 之 真").toOption = some false :=
  by native_decide

example :
    (wenyanInterp "（者 甲 甲 之 乾） 之 推").toOption = some «一» :=
  by native_decide

example :
    (wenyanInterp "（者 甲 甲 之 一） 之 推").toOption = some («生» «一») :=
  by native_decide

example :
    (wenyanInterpBool "（者 甲 甲 之 真） 之 不").toOption = some false :=
  by native_decide

example :
    (wenyanCompile "而 者 甲 甲 者 甲 推 甲").toOption.map (·.ty)
      = some (.arr .hex .hex) :=
  by native_decide

example :
    (wenyanInterpBool "各 者 甲 真 者 甲 同 甲 甲").toOption = some true :=
  by native_decide

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

example :
    (wenyanInterpBool "令 甲 真 不 甲").toOption = some false :=
  by native_decide

example :
    (wenyanInterp "令 甲 （推） （甲 之 乾）").toOption = some «一» :=
  by native_decide

example :
    (wenyanInterpBool "令 甲 （不） （甲 之 真）").toOption = some false :=
  by native_decide

example :
    (match wenyanCompile "凡 甲 不 甲" with
     | .error (.elab (.typeMismatch (.argumentMismatch .bool .hex))) => true
     | _ => false) = true :=
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
    (wenyanInterp "之又 推 乾").toOption = some («生生» 2 Hexagram.heaven) :=
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

  cue-aware resolver (`resolveWithCues`) 在明显 argument 起点处会比
  simple resolver 选择更精确的同字 reading；因此这里固定 operator-id
  序列，而不要求 atom constructor 与 simple 路径逐字相同。

  含「之」时，cue 路径将「之」消歧为 S_1 catalogue（v1 路径里是 appMarker），
  parser 将其保留成 explicit marker，elab 时透明处理。本节 verify
  resolveWithCues 之 atom 序列正确性，与 cue → unique reading 桥定理. -/

/-- 不含「之」的程序：cue-aware resolve 仍选中 `推` 的 T_10 reading. -/
example :
    let toks : List GlyphTok :=
      [⟨"推", 0, 1, false⟩, ⟨"一", 2, 1, false⟩]
    ((resolveWithCues toks).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?)))
      = some [some OperatorId.T_10, none] :=
  by native_decide

/-- 基础 stdlib token 仍按原 OperatorId 序列解析. -/
example :
    let toks : List GlyphTok :=
      [⟨"推", 0, 1, false⟩, ⟨"比", 2, 1, false⟩, ⟨"不", 4, 1, false⟩,
       ⟨"必", 6, 1, false⟩, ⟨"同", 8, 1, false⟩, ⟨"凡", 10, 1, false⟩,
       ⟨"一", 12, 1, false⟩]
    ((resolveWithCues toks).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?)))
      = some [some OperatorId.T_10, some OperatorId.R_8, some OperatorId.N_1,
          some OperatorId.M_1, some OperatorId.I_1, some OperatorId.Q_1, none] :=
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

/-! ### 「也」 postfix marker (wen-restructure 05)

`S_14 也` carries two surface forms:
* prefix (arity 1, from `operatorForms`) — `也 乾` still parses as the prefix
  application of the identity-anchor `hexIdBody`
* postfix (prec 10, from `postfixSurfaceSyntaxEntries`) — `推 一 也` parses
  the trailing `也` as a postfix marker re-shaping `acc` into `(也) acc`

Since `S_14 = hexIdBody` is the identity on `Hex`, postfix and prefix both
preserve the underlying Hex value but record the surface form distinctly. -/

/-- Postfix demo: `推 一 也` compiles successfully (postfix applies to result). -/
example : (wenyanCompile "推 一 也").toOption.isSome = true := by native_decide

/-- Back-compat: `推 一` still compiles (regression check). -/
example : (wenyanCompile "推 一").toOption.isSome = true := by native_decide

/-- Postfix `也` over `推 一` is the identity on `Hex`, so the denoted value
    matches the bare `推 一`. -/
example : (wenyanInterp "推 一 也").toOption = some («生» «一») := by native_decide

/-- Back-compat: `也 乾` still parses as the prefix application of S_14. -/
example : (wenyanCompile "也 乾").toOption.isSome = true := by native_decide

/-- Mixed postfix + relation infix: `一 同 一 也` compiles (postfix is
    greedy and fires before the infix dispatch chain). -/
example : (wenyanCompile "一 同 一 也").toOption.isSome = true := by native_decide

/-! ### Multi-statement programs (wen-1.5 sub-plan 03)

Statement separators: 「；」 「。」 ASCII `;`. -/

/-- Empty input → empty program. -/
example : (wenyanCompileProgram "").toOption.map List.length = some 0 := by native_decide

/-- Whitespace-only input → empty program. -/
example : (wenyanCompileProgram "   ").toOption.map List.length = some 0 := by native_decide

/-- Single statement, no separator → one element. -/
example : (wenyanCompileProgram "推 一").toOption.map List.length = some 1 := by native_decide

/-- Two statements separated by ideographic 「；」. -/
example : (wenyanCompileProgram "推 一；推 推 一").toOption.map List.length = some 2 := by native_decide

/-- Three statements separated by 「。」. -/
example : (wenyanCompileProgram "推 一。推 推 一。推 推 推 一").toOption.map List.length = some 3 := by native_decide

/-- Mixed separators: 「；」 and 「。」 both recognised. -/
example : (wenyanCompileProgram "推 一；推 推 一。推 推 推 一").toOption.map List.length = some 3 := by native_decide

/-- ASCII semicolon also works. -/
example : (wenyanCompileProgram "推 一;推 推 一").toOption.map List.length = some 2 := by native_decide

/-- Each statement gets its own type from the elaborator. -/
example :
    (wenyanCompileProgram "推 一；凡 甲 同 甲 甲").toOption.map
        (fun ts => ts.map (·.ty))
      = some [.hex, .bool] := by
  native_decide

/-- Error in a chunk propagates. -/
example :
    (wenyanCompileProgram "推 一 二").toOption = none := by native_decide

/-- Trailing separator is tolerated (empty chunks filtered). -/
example : (wenyanCompileProgram "推 一；").toOption.map List.length = some 1 := by native_decide

/-! ### User-defined `def` declarations (wen-1.5 sub-plan 05)

Surface form: `定 NAME 为 BODY`.  Sequential definitions accumulate into
a `DefEnv`; subsequent statements rewrite references to declared names
by textual substitution of the body source (wrapped in 「（…）」) BEFORE
lexing.  v1: no recursion; re-definition rejected; catalogue glyphs
rejected as names. -/

/-- (1) Single def + single use: `定 倍推 为 而 推 推；倍推 一`.
    Result: list of 2 stmts.  The defStmt body has type `Hex → Hex`
    (S_2 = endoCompBody composes the two T_10 endomaps); the exprStmt
    applies it to `一` and has type `Hex`. -/
example :
    (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；倍推 一").toOption.map
        (·.map (·.body.ty))
      = some [.arr .hex .hex, .hex] := by
  native_decide

/-- (2) `倍推 一` after `定 倍推 为 而 推 推` has the SAME denotation as
    `推 推 一` (S_2 ≡ composition; substitution preserves semantics). -/
example :
    let lhs := (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；倍推 一").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    let rhs := (wenyanCompile "推 推 一").toOption
    (lhs.bind (denoteHex ·.tm)) = (rhs.bind (denoteHex ·.tm)) := by
  native_decide

/-- (3) Chained defs: `定 F 为 推 一；定 G 为 F；G` ≡ `推 一`. -/
example :
    let chained := (wenyanCompileProgramWithDefs "定 甴 为 推 一；定 乸 为 甴；乸").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    let direct := (wenyanCompile "推 一").toOption
    (chained.bind (denoteHex ·.tm)) = (direct.bind (denoteHex ·.tm)) := by
  native_decide

/-- (4) Redefinition rejected: `定 甴 为 推 一；定 甴 为 推 推 一` errors. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴 为 推 一；定 甴 为 推 推 一" with
     | .error (.defError 1 (.redefinition "甴")) => true
     | _ => false) = true := by native_decide

/-- (5) Catalogue collision rejected: `定 推 为 推 一` cannot shadow the
    catalogue glyph `推`. -/
example :
    (match wenyanCompileProgramWithDefs "定 推 为 推 一" with
     | .error (.defError 0 (.conflictWithCatalogue "推")) => true
     | _ => false) = true := by native_decide

/-- (6) Missing `为` separator → defError. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴" with
     | .error (.defError 0 _) => true
     | _ => false) = true := by native_decide

/-- (7) Empty body after `为` → defError. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴 为 " with
     | .error (.defError 0 _) => true
     | _ => false) = true := by native_decide

/-- (8) Def-body compile failure surfaces as a `.base` (not `.defError`).
    The body `推 真` is a type error: `推` expects `Hex` but `真` is `Bool`. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴 为 推 真" with
     | .error (.base 0 _) => true
     | _ => false) = true := by native_decide

/-- (9) Multi-token name «倍推» is accepted (not in `multiCharSurfaces`).
    Body `推 一` has type `Hex`; `倍推` resolves to it. -/
example :
    (wenyanCompileProgramWithDefs "定 倍推 为 推 一；倍推").toOption.map List.length
      = some 2 := by
  native_decide

/-- (10) Recursion rejected (body compile errors): `定 甴 为 甴`.
    Inner `甴` is an unbound glyph in the body's own compile context. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴 为 甴" with
     | .error (.base 0 _) => true
     | _ => false) = true := by native_decide

/-- (11) Plain expression chunks unaffected by an empty env. -/
example :
    (wenyanCompileProgramWithDefs "推 一").toOption.map List.length = some 1 := by
  native_decide

/-- (12) End-to-end value check: `定 倍推 为 而 推 推；倍推 一` denotes
    «生生» 2 «一» (compose-then-apply ≡ apply-twice). -/
example :
    let lastExpr := (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；倍推 一").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    lastExpr.bind (denoteHex ·.tm) = some («生生» 2 «一») := by
  native_decide

/-- (13) Nested def references: `定 三推 为 而 倍推 推；三推 一` ≡ apply 推 thrice. -/
example :
    let lastExpr :=
      (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；定 三推 为 而 倍推 推；三推 一").toOption
        |>.bind (·.getLast?) |>.map Stmt.body
    lastExpr.bind (denoteHex ·.tm) = some («生生» 3 «一») := by
  native_decide

/-! ## § 9  wen-2.0 ⑥ 曰 direct speech + ⑩ 引语括号「」/『』

  Pair feature (Phase β depends on α-⑩ lex extension):

  · ⑩ 引语括号 — lex 新支持 `「」` 与 `『』`. 内部 body 按一般规则解析为
    `SurfaceExpr`, 在 elab 阶段被识为 quote 之 group (openTok.surface ∈ {「,『})
    并 wrap 为 `Tm.quote body`. 类型一律为 `Ty.quoted`. 体内任意类型 / 自由
    变量在 typecheck 时不被强制（quote 之 body 是 *data*, 不是 *expression*).

  · ⑥ 曰 direct speech (E_2) — `曰 X Y` 之第二参数 Y 若为 quoted group 即
    被 elaborate 为 `.catalogue2 .E_2 X (.quote ...)`. textAct 之 `arity-1` 位
    被 `catalogueArgTypeOk` 放宽允许 `.quoted` 类型；Hex/Hex 之 back-compat
    形式 (e.g. `曰 乾 坤`) 仍合法.

  公示数字 **375 不变** — 不引入新 OperatorId. 仅 `Tm.quote` 构造子 + `Ty.quoted`
  类型 + lex/elab extension. 与 ⑪ unquote/eval 之未来接入预留接口.
-/

/-- ⑩ (1) Bare quote「一」 compiles to `Tm.quote .yi` with type `.quoted`. -/
example :
    let typed := wenyanCompile "「一」"
    typed.toOption.map TypedTm.tm = some (.quote .yi)
      ∧ typed.toOption.map TypedTm.ty = some .quoted := by native_decide

/-- ⑩ (2) Bare quote「乾」 → quoted hex literal Hexagram.heaven. -/
example :
    let typed := wenyanCompile "「乾」"
    typed.toOption.map TypedTm.tm = some (.quote (.hexLit Hexagram.heaven))
      ∧ typed.toOption.map TypedTm.ty = some .quoted := by native_decide

/-- ⑩ (3) Secondary quote bracket『一』 has identical semantics to「一」. -/
example :
    (wenyanCompile "「一」").toOption.map TypedTm.tm
      = (wenyanCompile "『一』").toOption.map TypedTm.tm := by native_decide

/-- ⑩ (4) Quote of composite expression — body is fully elaborated but never
    evaluated.  「推 一」 → `.quote (.app tuiBody .yi)`. -/
example :
    let typed := wenyanCompile "「推 一」"
    typed.toOption.map TypedTm.ty = some .quoted
      ∧ typed.toOption.map TypedTm.tm
          = some (.quote (.app Stdlib.tuiBody .yi)) := by native_decide

/-- ⑩ (5) Deferment witness: 「不」 (notB primitive, .arr .bool .bool) quotes
    without forcing scalar evaluation.  The body is a function — bare 「不」
    body is well-formed Tm; quoted wrapper accepts any well-elaborated body. -/
example :
    let typed := wenyanCompile "「不」"
    typed.toOption.map TypedTm.tm = some (.quote .notB)
      ∧ typed.toOption.map TypedTm.ty = some .quoted := by native_decide

/-- ⑩ (6) Nested quote: 「『一』」 → `.quote (.quote .yi)`. -/
example :
    let typed := wenyanCompile "「『一』」"
    typed.toOption.map TypedTm.tm = some (.quote (.quote .yi))
      ∧ typed.toOption.map TypedTm.ty = some .quoted := by native_decide

/-- ⑩ (7) `「一」 同 「一」` — `.quoted` is not `.hex`, so an infix `同` over
    quotes is a type mismatch (not silently coerced).  Confirms `.quoted` is
    a *distinct* type, not a hex-alias. -/
example : (wenyanCompile "「一」 同 「一」").toOption.isNone = true := by native_decide

/-- ⑥ (1) 曰 + Hex speaker + quoted body: `曰 乾 「一」` →
    `.catalogue2 .E_2 (.hexLit Hexagram.heaven) (.quote .yi)`. -/
example :
    let typed := wenyanCompile "曰 乾 「一」"
    typed.toOption.map TypedTm.tm
        = some (.catalogue2 .E_2 (.hexLit Hexagram.heaven) (.quote .yi))
      ∧ typed.toOption.map TypedTm.ty = some (.catalogue .textAct) := by
  native_decide

/-- ⑥ (2) Back-compat: `曰 乾 坤` (both args Hex, no quote) keeps the
    pre-existing `pairHBody`-based elaboration (Hex × Hex carrier), exactly
    matching the legacy E_2 test fixture in `EndToEndTests` § 6. ⑥ only
    fires the `.catalogue2 .E_2 …` form when 2nd arg is a quoted group. -/
example :
    (match wenyanCompile "曰 乾 坤" with
     | .ok typed => typed.ty = .prod .hex .hex
     | _ => false) = true := by native_decide

/-- ⑥ (3) 曰 + hex speaker + quoted COMPOSITE body: `曰 乾 「推 一」`.
    Body is `.app tuiBody .yi` inside a quote — body not evaluated. -/
example :
    let typed := wenyanCompile "曰 乾 「推 一」"
    typed.toOption.map TypedTm.tm
        = some (.catalogue2 .E_2 (.hexLit Hexagram.heaven)
                  (.quote (.app Stdlib.tuiBody .yi)))
      ∧ typed.toOption.map TypedTm.ty = some (.catalogue .textAct) := by
  native_decide

/-- ⑥ (4) Quote of a stand-alone non-scalar (`.notB`) is accepted as 曰 body —
    confirms deferment: the body need not denote a Hex/Bool value.  Equivalent
    to the spec example "子曰：「不」 doesn't error even though 不 alone is a
    function". -/
example :
    let typed := wenyanCompile "曰 乾 「不」"
    typed.toOption.map TypedTm.tm
        = some (.catalogue2 .E_2 (.hexLit Hexagram.heaven) (.quote .notB))
      ∧ typed.toOption.map TypedTm.ty = some (.catalogue .textAct) := by
  native_decide

/-- ⑩ (8) Unclosed quote bracket → parse error.  Confirms `「` is a real open
    bracket that must be paired. -/
example : (wenyanCompile "「一").toOption.isNone = true := by native_decide

/-- ⑩ (9) Mismatched close: `「一)` reports an expectedCloseBracket-shaped
    parse error (or similar bracket-mismatch).  The pipeline rejects rather
    than silently accepting. -/
example : (wenyanCompile "「一)").toOption.isNone = true := by native_decide

/-- ⑩ (10) Quotes inside value-grouping parens still work: `（「一」）`.
    Outer `（...）` is a no-op group; inner `「一」` quotes the Hex literal. -/
example :
    let typed := wenyanCompile "（「一」）"
    typed.toOption.map TypedTm.tm = some (.quote .yi)
      ∧ typed.toOption.map TypedTm.ty = some .quoted := by native_decide

/-- ⑩ (11) Empty quote `「」` is an error (parser rejects empty grouped body).
    Quotes must wrap a non-empty expression — matches value-grouping
    behavior for `（）`. -/
example : (wenyanCompile "「」").toOption.isNone = true := by native_decide

end SSBX.Foundation.Wen.WenSurface
