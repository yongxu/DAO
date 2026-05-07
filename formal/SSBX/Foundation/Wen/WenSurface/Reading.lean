/-
# WenSurface.Reading — 单读 resolver (v1)

把 GlyphTok 流映到 ResolvedTok 流。每个 ResolvedTok 携带：
  · 原 GlyphTok（位置 / surface）
  · ResolvedAtom：要么是 hex 常值，要么是 catalogue 算子读法

## v1 范围（最小闭环）

直接 surface map，硬编码：
  · **6 stdlib 算子**: 推/比/不/必/同/凡 → T_10/R_8/N_1/M_1/I_1/Q_1
    与 [WenDef.lean](../WenDef.lean) `Stdlib.{tui,bi,bu,biModal,tong,fan}Def` 一一对应。
  · **1 hex 常**: 一 → YiCore.«一»
  · 其他 surface → `.noReading`

Phase C（cue-aware）将取代此层；Phase B 仅为打通 lex→elab 管线。

## 状态

0 sorry / 0 axiom / 总函数. 关键例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Lex
import SSBX.Text.OperatorReadings
import SSBX.Foundation.Yi.YiCore

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore

/-! ## § 1  Resolved 类型 -/

/-- 已消歧的原子：要么是卦字面值，要么是 catalogue 算子读法. -/
inductive ResolvedAtom where
  | hexConst    (h : Hexagram)
  | catalogueOp (reading : OperatorReading)
deriving DecidableEq, Repr

/-- 已消歧的 token：保留 GlyphTok 与解析结果. -/
structure ResolvedTok where
  tok  : GlyphTok
  atom : ResolvedAtom
deriving DecidableEq, Repr

/-- Resolver 错误。 -/
inductive ResolveErr where
  | noReading (surface : String) (col : Nat) : ResolveErr
deriving DecidableEq, Repr

/-! ## § 2  v1 surface map -/

/-- 6 个 stdlib 算子的 surface → catalogue reading. 每条 reading
    通过 `catalogueReading` factory 构造，与 [Stdlib WenDef](../WenDef.lean#L171)
    之 def 一一对应. -/
def resolveStdlibOp : Glyph → Option OperatorReading
  | "推" => some (catalogueReading "推" "T-10" "对象推进 / 生" (some .T_10)
                    .prefix [.expectedObject])
  | "比" => some (catalogueReading "比" "R-8"  "邻接对应"     (some .R_8)
                    .prefix [.expectedObject])
  | "不" => some (catalogueReading "不" "N-1"  "命题否定"     (some .N_1)
                    .prefix [.expectedProp])
  | "必" => some (catalogueReading "必" "M-1"  "必然 / □"     (some .M_1)
                    .prefix [.modalFrame])
  | "同" => some (catalogueReading "同" "I-1"  "恒等谓词"     (some .I_1)
                    .prefix [.expectedObject])
  | "凡" => some (catalogueReading "凡" "Q-1"  "凡量"         (some .Q_1)
                    .prefix [.quantifierDomain])
  | _   => none

/-- v1 hex 常值 surface → Hexagram. -/
def resolveHexConst : Glyph → Option Hexagram
  | "一" => some «一»
  | _   => none

/-! ## § 3  Resolver -/

/-- 单 token resolver. 先尝试 hex 常值，再 stdlib 算子；失败则 `.noReading`. -/
def resolveOne (t : GlyphTok) : Except ResolveErr ResolvedTok :=
  match resolveHexConst t.surface with
  | some h => .ok ⟨t, .hexConst h⟩
  | none =>
    match resolveStdlibOp t.surface with
    | some r => .ok ⟨t, .catalogueOp r⟩
    | none   => .error (.noReading t.surface t.startCol)

/-- 全 token 列表 resolver。结构递归，总函数. -/
def resolveSimple : List GlyphTok → Except ResolveErr (List ResolvedTok)
  | []       => .ok []
  | t :: ts  =>
    match resolveOne t with
    | .error e => .error e
    | .ok r =>
      match resolveSimple ts with
      | .error e  => .error e
      | .ok rs    => .ok (r :: rs)

/-- 顶层 entry：String → ResolvedTok 流，串接 lex 与 resolve. -/
def lexAndResolve (s : String)
    : Except (LexErr ⊕ ResolveErr) (List ResolvedTok) :=
  match lexWen s with
  | .error e => .error (.inl e)
  | .ok toks =>
    match resolveSimple toks with
    | .error e => .error (.inr e)
    | .ok rs   => .ok rs

/-! ## § 4  Helper：从 ResolvedTok 抽 atom 列表 -/

/-- 从 resolve 结果抽 atom 序列（丢弃位置信息）. -/
def atomsOf : List ResolvedTok → List ResolvedAtom :=
  List.map (·.atom)

/-- 从 ResolvedAtom 抽 OperatorId（仅对 catalogueOp 有效）. -/
def ResolvedAtom.opId? : ResolvedAtom → Option OperatorId
  | .hexConst _    => none
  | .catalogueOp r => r.operator?

/-! ## § 5  Sanity 例子 (native_decide) -/

/-- Helper: 提取 atom 的 OperatorId（hexConst → none）. -/
private def opIdsOf (s : String) : Option (List (Option OperatorId)) :=
  (lexAndResolve s).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?))

/-- 「推」单独 → catalogueOp T_10. -/
example : opIdsOf "推" = some [some OperatorId.T_10] := by native_decide

/-- 「一」单独 → hexConst «一». -/
example : opIdsOf "一" = some [none] := by native_decide

/-- 6 个 stdlib 算子 + 「一」全打通. -/
example :
    opIdsOf "推 比 不 必 同 凡 一"
      = some [some OperatorId.T_10, some OperatorId.R_8, some OperatorId.N_1,
              some OperatorId.M_1,  some OperatorId.I_1, some OperatorId.Q_1,
              none] :=
  by native_decide

/-- 「推 一」流：T_10 + hex const «一». -/
example :
    opIdsOf "推 一" = some [some OperatorId.T_10, none] :=
  by native_decide

/-- 未知 surface → ResolveErr. -/
example : opIdsOf "瓜" = none := by native_decide

/-- 空串 → 空 list. -/
example : opIdsOf "" = some [] := by native_decide

/-! ## § 6  结构性断言 -/

/-- v1 stdlib map 之全部 6 个 surface 都解析成 some. -/
example : (["推", "比", "不", "必", "同", "凡"].all
            (resolveStdlibOp · |>.isSome)) = true := by native_decide

/-- v1 hex 常值 map 唯一项「一」. -/
example : resolveHexConst "一" = some «一» := by native_decide
example : resolveHexConst "推" = none := by native_decide

/-- 6 stdlib 算子的 OperatorId 互不相同（按定义顺序展开）. -/
example :
    (["推", "比", "不", "必", "同", "凡"].filterMap
       (fun s => (resolveStdlibOp s).bind (·.operator?)))
      = [OperatorId.T_10, OperatorId.R_8, OperatorId.N_1,
         OperatorId.M_1,  OperatorId.I_1, OperatorId.Q_1] :=
  by native_decide

end SSBX.Foundation.Wen.WenSurface
