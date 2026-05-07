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
  | leftoverAtoms (count : Nat)
  | fuelExhausted
deriving DecidableEq, Repr

/-! ## § 2  Atom → Tm -/

/-- 单个 ResolvedAtom 之 Tm 解释。
    · hexConst «一» 走 `.yi` primitive（与 `tui_eq_sheng` 等定理对齐）
    · 其他 hexConst h 走 `.hexLit h`
    · boolConst b 走 `.boolLit b`
    · catalogueOp 按 OperatorId 派发到 stdlib body
    · appMarker 不应进 atomToTm（应在 list 层被过滤）—— 防御性返 `empty`. -/
def atomToTm : ResolvedAtom → Except ElabErr Tm
  | .hexConst h =>
      if h = «一» then .ok .yi else .ok (.hexLit h)
  | .boolConst b => .ok (.boolLit b)
  | .catalogueOp r =>
      match r.operator? with
      | some .T_10 => .ok Stdlib.tuiBody
      | some .R_8  => .ok Stdlib.biBody
      | some .N_1  => .ok Stdlib.buBody
      | some .M_1  => .ok Stdlib.biModalBody
      | some .I_1  => .ok Stdlib.tongBody
      | some .Q_1  => .ok Stdlib.fanBody
      | some .T_12 => .ok Stdlib.sunBody
      | some .T_13 => .ok Stdlib.yiBenefitBody
      | some id    => .error (.unsupportedOp id)
      | none       => .error .empty
  | .appMarker  => .error .empty

/-! ## § 3  Arity 表 -/

/-- Stdlib 算子的 arity（参数个数）.
    其他 OperatorId → 0（不在 v1 范围）. -/
def opArity : OperatorId → Nat
  | .T_10 => 1   -- 推 : Hex → Hex
  | .R_8  => 2   -- 比 : Hex → Hex → Bool
  | .N_1  => 1   -- 不 : Bool → Bool
  | .M_1  => 1   -- 必 : (Hex → Bool) → Bool
  | .I_1  => 2   -- 同 : Hex → Hex → Bool
  | .Q_1  => 1   -- 凡 : (Hex → Bool) → Bool
  | .T_12 => 1   -- 損 : Hex → Hex
  | .T_13 => 1   -- 益 : Hex → Hex
  | _     => 0

/-! ## § 4  Arity-driven 递归下降 (fuel-bounded total)

  从 atom 列表解析一个表达式，返回 (Tm, 余下 atoms)。
  Arity 驱动：算子按其声明 arity 消耗后续子表达式；appMarker 被透明跳过.
-/

mutual
  def parseExpr : Nat → List ResolvedAtom → Except ElabErr (Tm × List ResolvedAtom)
    | 0,    _                                  => .error .fuelExhausted
    | _+1,  []                                 => .error .empty
    | n+1,  .appMarker :: rest                 => parseExpr n rest
    | _+1,  .hexConst h :: rest                =>
      .ok ((if h = «一» then .yi else .hexLit h), rest)
    | _+1,  .boolConst b :: rest               =>
      .ok (.boolLit b, rest)
    | n+1,  .catalogueOp r :: rest             =>
      match r.operator? with
      | none    => .error .empty
      | some id =>
        match atomToTm (.catalogueOp r) with
        | .error e => .error e
        | .ok body => collectArgs n body (opArity id) rest

  /-- 消费 `k` 个子表达式作为 `acc` 的参数（左结合：`((acc a1) a2) ...`). -/
  def collectArgs : Nat → Tm → Nat → List ResolvedAtom → Except ElabErr (Tm × List ResolvedAtom)
    | _,    acc, 0,   rest => .ok (acc, rest)
    | 0,    _,   _+1, _    => .error .fuelExhausted
    | n+1,  acc, k+1, rest =>
      match parseExpr n rest with
      | .error e          => .error e
      | .ok (arg, rest')  => collectArgs n (.app acc arg) k rest'
end -- mutual

/-- 顶层 elaborator：所有 atom 必须被一个 expression 完整消费。
    Fuel = 2·n + 1：每个 atom 至多触发 1 次 parseExpr + 1 次 collectArgs. -/
def elabTokens (rs : List ResolvedTok) : Except ElabErr Tm :=
  let atoms := rs.map (·.atom)
  let fuel  := atoms.length * 2 + 1
  match parseExpr fuel atoms with
  | .error e         => .error e
  | .ok (tm, [])     => .ok tm
  | .ok (_, leftover) => .error (.leftoverAtoms leftover.length)

/-! ## § 5  Sanity 例子 (native_decide via toOption) -/

/-- 「一」 elab 成 `.yi` primitive. -/
example :
    (elabTokens [⟨⟨"一", 0, 1, false⟩, .hexConst «一»⟩]).toOption
      = some Tm.yi :=
  by native_decide

/-- 「推」 单独 elab 报 empty（arity 1 但无参） -/
example :
    let toks : List ResolvedTok :=
      [⟨⟨"推", 0, 1, false⟩,
        .catalogueOp (catalogueReading "推" "T-10" "对象推进 / 生"
                         (some OperatorId.T_10) .prefix [.expectedObject])⟩]
    (elabTokens toks).toOption = none :=
  by native_decide

/-! ## § 6  端到端 atomToTm 类型核校 -/

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
