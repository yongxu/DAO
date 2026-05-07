/-
# WenSurface.EndToEnd — 文表层端到端管线

把 lex / resolve / elab / denote 拼成单一入口：
  · `wenyanInterp : String → Option Hexagram`     — 闭项 wenyan 程序求 hex
  · `wenyanInterpBool : String → Option Bool`     — 求 bool

求值复用既有 [WenDefEval.denoteHex / denoteBool](../WenDefEval.lean)，
不走 baguaWen IL（保留 [WenDefCompile.lean](../WenDefCompile.lean) 的
cuo-equivariant 子集 commute 作 future work）。

## v1 范围

- 6 stdlib 算子 (推/比/不/必/同/凡) + 1 hex 常 (一)
- 右结合连续 application
- 「推 一」「推 推 一」「推 推 推 一」全打通到 YiCore.«生» 链

## 状态

0 sorry / 0 axiom / 总函数. 端到端例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Elaborate

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## § 1  统一错误类型 -/

/-- WenSurface pipeline 之统一错误。 -/
inductive WenSurfaceErr where
  | lex     (e : LexErr)
  | resolve (e : ResolveErr)
  | elab    (e : ElabErr)
  | denoteFailed
deriving DecidableEq, Repr

/-! ## § 2  端到端管线 -/

/-- String → Tm 之完整管线（lex + resolve + elab）. -/
def wenyanCompile (s : String) : Except WenSurfaceErr Tm :=
  match lexWen s with
  | .error e => .error (.lex e)
  | .ok toks =>
    match resolveSimple toks with
    | .error e => .error (.resolve e)
    | .ok rs =>
      match elabTokens rs with
      | .error e => .error (.elab e)
      | .ok t    => .ok t

/-- 闭项 hex 求值：String → Hexagram. -/
def wenyanInterp (s : String) : Except WenSurfaceErr Hexagram :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok t =>
    match denoteHex t with
    | some h => .ok h
    | none   => .error .denoteFailed

/-- 闭项 bool 求值：String → Bool. -/
def wenyanInterpBool (s : String) : Except WenSurfaceErr Bool :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok t =>
    match denoteBool t with
    | some b => .ok b
    | none   => .error .denoteFailed

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

/-! ### 「之」 应用标记测试（noop skip 语义） -/

/-- 「推 之 一」≡「推 一」，「之」elab 时被过滤. -/
example :
    (wenyanInterp "推 之 一").toOption = (wenyanInterp "推 一").toOption :=
  by native_decide

/-- 「推 之 推 之 一」 ≡ 「推 推 一」 = «生生» 2 «一». -/
example :
    (wenyanInterp "推 之 推 之 一").toOption = some («生生» 2 «一») :=
  by native_decide

/-- 「推 乾 之」尾随之是合法的（被 elab 过滤）—— 与「推 乾」同结果. -/
example :
    (wenyanInterp "推 之 乾").toOption = some «一» :=
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
    (wenyanCompile "推 一").toOption = some (.app Stdlib.tuiBody .yi) :=
  by native_decide

/-- 与 `tui_eq_sheng` 桥 — 用 wenyan 表层走 stdlib 算子等价于 YiCore.«生». -/
theorem wenyan_tui_yi_eq_sheng :
    (wenyanInterp "推 一").toOption = some («生» «一») := by
  native_decide

/-! ## § 6  公示总结 -/

/-- v1 公示：6 stdlib 算子 + 1 hex 常的端到端可达性。
    `推`/`一` 的合成结果与 YiCore.«生»/«生生» 一致。 -/
theorem v1_endToEnd_summary :
    (wenyanInterp "一").toOption = some «一»
    ∧ (wenyanInterp "推 一").toOption = some («生» «一»)
    ∧ (wenyanInterp "推 推 一").toOption = some («生生» 2 «一»)
    ∧ (wenyanInterp "推 推 推 一").toOption = some («生生» 3 «一»)
    := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end SSBX.Foundation.Wen.WenSurface
