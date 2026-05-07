/-
# WenSurface.Elaborate — ResolvedTok → WenDef.Tm

把 ResolvedTok 流 elaborate 为 WenDef.Tm（typed-λ over Hex+Bool+Arr）。
求值仍由既有 [WenDefEval.evalFuel](../WenDefEval.lean) 完成。

## v1 范围

- **算子**：6 个 stdlib (推/比/不/必/同/凡) → 直接复用 [Stdlib bodies](../WenDef.lean#L171)
  · T_10 → `Stdlib.tuiBody`     (Hex → Hex)
  · R_8  → `Stdlib.biBody`      (Hex → Hex → Bool)
  · N_1  → `Stdlib.buBody`      (Bool → Bool)
  · M_1  → `Stdlib.biModalBody` ((Hex → Bool) → Bool)
  · I_1  → `Stdlib.tongBody`    (Hex → Hex → Bool)
  · Q_1  → `Stdlib.fanBody`     ((Hex → Bool) → Bool)
- **常值**：「一」 → `.yi` (primitive)；其他 hex 字面值 → `.hexLit h`
- **组合**：右结合 application — `[f, g, x]` → `.app f (.app g x)`
- **未知 OperatorId**（含反/错/损/益等）→ `.unsupported`

## 状态

0 sorry / 0 axiom / 总函数. 关键例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Reading
import SSBX.Foundation.Wen.WenDef
import SSBX.Foundation.Wen.WenDefEval

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings

/-! ## § 1  Elab error 类型 -/

inductive ElabErr where
  | unsupportedOp (id : OperatorId)
  | empty
deriving DecidableEq, Repr

/-! ## § 2  Atom → Tm -/

/-- 单个 ResolvedAtom 之 Tm 解释。
    · hexConst «一» 走 `.yi` primitive（与 `tui_eq_sheng` 等定理对齐）
    · 其他 hexConst h 走 `.hexLit h`
    · catalogueOp 按 OperatorId 派发到 stdlib body. -/
def atomToTm : ResolvedAtom → Except ElabErr Tm
  | .hexConst h =>
      if h = «一» then .ok .yi else .ok (.hexLit h)
  | .catalogueOp r =>
      match r.operator? with
      | some .T_10 => .ok Stdlib.tuiBody
      | some .R_8  => .ok Stdlib.biBody
      | some .N_1  => .ok Stdlib.buBody
      | some .M_1  => .ok Stdlib.biModalBody
      | some .I_1  => .ok Stdlib.tongBody
      | some .Q_1  => .ok Stdlib.fanBody
      | some id    => .error (.unsupportedOp id)
      | none       => .error .empty

/-! ## § 3  右结合组合 -/

/-- 右结合的连续 application：
    · `[a]` → atom 的 Tm
    · `[f, ..rest]` → `.app f (elabRightAssoc rest)` -/
def elabRightAssoc : List ResolvedAtom → Except ElabErr Tm
  | [] => .error .empty
  | [a] => atomToTm a
  | a :: rest =>
    match atomToTm a with
    | .error e => .error e
    | .ok f =>
      match elabRightAssoc rest with
      | .error e => .error e
      | .ok arg  => .ok (.app f arg)

/-- 顶层 elaborator：ResolvedTok 流 → Tm. -/
def elabTokens (rs : List ResolvedTok) : Except ElabErr Tm :=
  elabRightAssoc (rs.map (·.atom))

/-! ## § 4  Sanity 例子 (native_decide via toOption) -/

/-- 「一」 elab 成 `.yi` primitive. -/
example :
    (elabTokens [⟨⟨"一", 0, 1, false⟩, .hexConst «一»⟩]).toOption
      = some Tm.yi :=
  by native_decide

/-- 「推」 elab 成 `Stdlib.tuiBody`. -/
example :
    (elabTokens [⟨⟨"推", 0, 1, false⟩,
                  .catalogueOp (catalogueReading "推" "T-10" "对象推进 / 生"
                                   (some OperatorId.T_10) .prefix
                                   [.expectedObject])⟩]).toOption
      = some Stdlib.tuiBody :=
  by native_decide

/-! ## § 5  端到端 atomToTm 类型核校 -/

/-- 6 stdlib body 之 typecheck（来自 WenDef.Stdlib 既有定理）. -/
example : typeCheck [] Stdlib.tuiBody     = some (.arr .hex .hex)            := by native_decide
example : typeCheck [] Stdlib.biBody      = some (.arr .hex (.arr .hex .bool)) := by native_decide
example : typeCheck [] Stdlib.buBody      = some (.arr .bool .bool)          := by native_decide
example : typeCheck [] Stdlib.biModalBody = some (.arr (.arr .hex .bool) .bool) := by native_decide
example : typeCheck [] Stdlib.tongBody    = some (.arr .hex (.arr .hex .bool)) := by native_decide
example : typeCheck [] Stdlib.fanBody     = some (.arr (.arr .hex .bool) .bool) := by native_decide

/-- `.yi` primitive 之类型. -/
example : typeCheck [] Tm.yi = some .hex := by native_decide

end SSBX.Foundation.Wen.WenSurface
