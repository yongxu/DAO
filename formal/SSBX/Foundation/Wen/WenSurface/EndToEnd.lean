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
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings

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
    (wenyanCompile "推 一").toOption = some (.app Stdlib.tuiBody .yi) :=
  by native_decide

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

/-! ## § 7  公示总结 -/

/-- v1 公示：6 stdlib 算子 + 1 hex 常的端到端可达性。
    `推`/`一` 的合成结果与 YiCore.«生»/«生生» 一致。 -/
theorem v1_endToEnd_summary :
    (wenyanInterp "一").toOption = some «一»
    ∧ (wenyanInterp "推 一").toOption = some («生» «一»)
    ∧ (wenyanInterp "推 推 一").toOption = some («生生» 2 «一»)
    ∧ (wenyanInterp "推 推 推 一").toOption = some («生生» 3 «一»)
    := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## § 7  Phase C cue resolution 端到端 sanity

  cue-aware resolver (`resolveWithCues`) 与 v1 (`resolveSimple`) 在不含
  「之」的 stdlib 流上完全等价 —— 这里给一组端到端等价见证.

  含「之」时，cue 路径将「之」消歧为 S_1 catalogue（v1 路径里是 appMarker），
  但 elab 阶段 S_1 暂未支持，故端到端 wenyanInterp 现仍走 v1 路径
  (resolveSimple) 以保留 noop appMarker 行为。本节只 verify
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

/-- v1 路径仍把同一程序之「之」识为 appMarker（无 OperatorId）—— 与 cue 路径成对.
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

/-- v1 wenyanInterp（仍走 resolveSimple）不被新增模块影响：
    「推 之 一」 = «生» «一»，与 Phase B 表现一致. -/
example :
    (wenyanInterp "推 之 一").toOption = some («生» «一») :=
  by native_decide

end SSBX.Foundation.Wen.WenSurface
