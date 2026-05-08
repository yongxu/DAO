/-
# WenSurface.Elaborate — SurfaceExpr → WenDef.Tm

把 ResolvedTok 流 elaborate 为 WenDef.Tm（typed-λ over Hex+Bool+Arr）。
求值仍由既有 [WenDefEval.evalFuel](../WenDefEval.lean) 完成。

## 当前范围

- **算子**：141 个 exact operator 进入 theorem-backed / Bool package bodies；
  其余 catalogue operator elaborates to structural catalogue normal forms。
- **常值**：「一」 → `.yi` primitive；64 卦名 / aliases → `.hexLit h`。
- **组合**：显式 `SurfaceExpr.app` 左结合到 `Tm.app`。
- **绑定**：Hex-only `者` lambda、`凡` forall、`令` let。
- **同字冲突**：`hexOrOp` 在 parser 已消歧；elab fallback 只把它当 hex literal。

## 状态

0 sorry / 0 axiom / 总函数. 关键例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Syntax
import SSBX.Foundation.Wen.WenDef
import SSBX.Foundation.Wen.WenDefEval

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorSignatures
open SSBX.Text.OperatorReadings

/-! ## § 1  Elab error 类型 -/

inductive TypeDiag where
  | unknownVar (name : String)
  | expectedFunction (actual : Ty)
  | argumentMismatch (expected actual : Ty)
deriving DecidableEq, Repr

inductive ElabErr where
  | unsupportedOp (id : OperatorId) (surface : String) (col : Nat)
  | unsupportedConstruction (name : String)
  | empty
  | leftoverAtoms (count : Nat)
  | fuelExhausted
  | typeMismatch (diag : TypeDiag)
deriving DecidableEq, Repr

/-- A closed elaborated term plus its checked type. -/
structure TypedTm where
  tm : Tm
  ty : Ty
deriving DecidableEq, Repr

/-! ## § 2  Atom → Tm -/

/-- 单个 ResolvedAtom 之 Tm 解释。
    · hexConst «一» 走 `.yi` primitive（与 `tui_eq_sheng` 等定理对齐）
    · 其他 hexConst h 走 `.hexLit h`
    · boolConst b 走 `.boolLit b`
    · catalogueOp 按 OperatorId 派发到 stdlib body
    · appMarker 不应进 atomToTm（应在 list 层被过滤）—— 防御性返 `empty`
    · iterate 由 parseExpr 直接处理，atomToTm 仅作防御性 `empty`. -/
def atomToTm : ResolvedAtom → Except ElabErr Tm
  | .hexConst h =>
      if h = «一» then .ok .yi else .ok (.hexLit h)
  | .boolConst b => .ok (.boolLit b)
  | .varName name => .ok (.var name)
  | .catalogueOp r =>
      match r.operator? with
      | some id =>
          match theoremBackedSemanticsFor? id with
          | some sem => .ok sem.body
          | none     => .error (.unsupportedOp id "" 0)
      | none => .error .empty
  | .hexOrOp h _ =>
      if h = «一» then .ok .yi else .ok (.hexLit h)
  | .syntax _    => .error .empty
  | .appMarker  => .error .empty
  | .iterate    => .error .empty
  | .openBracket => .error .empty
  | .closeBracket => .error .empty

def symbolicCatalogueTm? (id : OperatorId) : List Tm → Option Tm
  | [a] => some (.catalogue1 id a)
  | [a, b] => some (.catalogue2 id a b)
  | [a, b, c] => some (.catalogue3 id a b c)
  | _ => none

/-! ## § 3  Arity 表 -/

/-- Surface parser 使用的 operator arity：executable registry 优先，
    catalogue signature fallback. -/
def opArity : OperatorId → Nat
  | id => parseArityFor id

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
    | _+1,  .varName name :: rest              =>
      .ok (.var name, rest)
    | _+1,  .hexOrOp h _ :: rest               =>
      .ok ((if h = «一» then .yi else .hexLit h), rest)
    | _+1,  .syntax _ :: _                     =>
      .error .empty
    | _+1,  .openBracket :: _                  =>
      .error .empty
    | _+1,  .closeBracket :: _                 =>
      .error .empty
    | n+1,  .iterate :: rest                   =>
      -- 「之又 F X」 → F (F X)：递归解析 `F X` 子表达式（消耗 op + arg），
      -- 然后将其内部 application 复制为 F (F X)。
      match parseExpr n rest with
      | .error e         => .error e
      | .ok (innerTm, rest') =>
        match innerTm with
        | .app f x => .ok (.app f (.app f x), rest')
        | _        => .error .empty   -- 之又 后必须紧跟 arity≥1 的 op + 实参
    | n+1,  .catalogueOp r :: rest             =>
      match r.operator? with
      | none    => .error .empty
      | some id =>
        match theoremBackedSemanticsFor? id with
        | some sem => collectArgs n sem.body (opArity id) rest
        | none =>
            match collectArgTerms n (opArity id) rest with
            | .error e => .error e
            | .ok (args, rest') =>
                match symbolicCatalogueTm? id args with
                | some tm => .ok (tm, rest')
                | none => .error .empty

  /-- 消费 `k` 个子表达式作为 `acc` 的参数（左结合：`((acc a1) a2) ...`). -/
  def collectArgs : Nat → Tm → Nat → List ResolvedAtom → Except ElabErr (Tm × List ResolvedAtom)
    | _,    acc, 0,   rest => .ok (acc, rest)
    | 0,    _,   _+1, _    => .error .fuelExhausted
    | n+1,  acc, k+1, rest =>
      match parseExpr n rest with
      | .error e          => .error e
      | .ok (arg, rest')  => collectArgs n (.app acc arg) k rest'

  def collectArgTerms : Nat → Nat → List ResolvedAtom → Except ElabErr (List Tm × List ResolvedAtom)
    | _,    0,   rest => .ok ([], rest)
    | 0,    _+1, _    => .error .fuelExhausted
    | n+1,  k+1, rest =>
      match parseExpr n rest with
      | .error e => .error e
      | .ok (arg, rest') =>
          match collectArgTerms n k rest' with
          | .error e => .error e
          | .ok (args, rest'') => .ok (arg :: args, rest'')
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

/-! ## § 4.5 SurfaceExpr elaboration -/

def atomToTmAt (tok : ResolvedTok) : Except ElabErr Tm :=
  match tok.atom with
  | .catalogueOp r =>
      match r.operator? with
      | some id =>
          match theoremBackedSemanticsFor? id with
          | some sem => .ok sem.body
          | none     => .error (.unsupportedOp id tok.surface tok.col)
      | none => .error .empty
  | _ => atomToTm tok.atom

def symbolicCatalogueHead? (tok : ResolvedTok) (arity : Nat) : Option OperatorId :=
  match tok.atom with
  | .catalogueOp r =>
      match r.operator? with
      | some id =>
          if (theoremBackedSemanticsFor? id).isNone && (fullSignatureFor id).arity = arity then
            some id
          else
            none
      | none => none
  | _ => none

def elabSurfaceExpr : SurfaceExpr → Except ElabErr Tm
  | .atom tok => atomToTmAt tok
  | .app (.atom tok) a =>
      match symbolicCatalogueHead? tok 1 with
      | some id =>
          match elabSurfaceExpr a with
          | .ok ta => .ok (.catalogue1 id ta)
          | .error e => .error e
      | none =>
          match atomToTmAt tok, elabSurfaceExpr a with
          | .ok tf, .ok ta => .ok (.app tf ta)
          | .error e, _ => .error e
          | _, .error e => .error e
  | .app (.app (.atom tok) a) b =>
      match symbolicCatalogueHead? tok 2 with
      | some id =>
          match elabSurfaceExpr a, elabSurfaceExpr b with
          | .ok ta, .ok tb => .ok (.catalogue2 id ta tb)
          | .error e, _ => .error e
          | _, .error e => .error e
      | none =>
          match elabSurfaceExpr (.app (.atom tok) a), elabSurfaceExpr b with
          | .ok tf, .ok tb => .ok (.app tf tb)
          | .error e, _ => .error e
          | _, .error e => .error e
  | .app (.app (.app (.atom tok) a) b) c =>
      match symbolicCatalogueHead? tok 3 with
      | some id =>
          match elabSurfaceExpr a, elabSurfaceExpr b, elabSurfaceExpr c with
          | .ok ta, .ok tb, .ok tc => .ok (.catalogue3 id ta tb tc)
          | .error e, _, _ => .error e
          | _, .error e, _ => .error e
          | _, _, .error e => .error e
      | none =>
          match elabSurfaceExpr (.app (.app (.atom tok) a) b), elabSurfaceExpr c with
          | .ok tf, .ok tc => .ok (.app tf tc)
          | .error e, _ => .error e
          | _, .error e => .error e
  | .app f x =>
      match elabSurfaceExpr f, elabSurfaceExpr x with
      | .ok tf, .ok tx => .ok (.app tf tx)
      | .error e, _ => .error e
      | _, .error e => .error e
  | .seq [x] => elabSurfaceExpr x
  | .seq _ => .error (.unsupportedConstruction "seq")
  | .marker _ body => elabSurfaceExpr body
  | .binder .lambda name body =>
      match elabSurfaceExpr body with
      | .ok t => .ok (.abs name .hex t)
      | .error e => .error e
  | .binder .forallHex name body =>
      match elabSurfaceExpr body with
      | .ok t => .ok (.app .forallH (.abs name .hex t))
      | .error e => .error e
  | .letBind name value body =>
      match elabSurfaceExpr value, elabSurfaceExpr body with
      | .ok tv, .ok tb => .ok (.app (.abs name .hex tb) tv)
      | .error e, _ => .error e
      | _, .error e => .error e
  | .construction "之又" [inner] =>
      match elabSurfaceExpr inner with
      | .error e => .error e
      | .ok (.app f x) => .ok (.app f (.app f x))
      | .ok _ => .error .empty
  | .grouped _ _ body => elabSurfaceExpr body
  | .construction name _ => .error (.unsupportedConstruction name)

/-- Diagnostic type inference used only by WenSurface errors.
    `WenDef.typeCheck` remains the kernel checker; this mirrors it while
    preserving the first actionable mismatch for CLI/JSON output. -/
def inferTypeDetailed : Ctx → Tm → Except TypeDiag Ty
  | ctx, .var n =>
      match ctx.lookup n with
      | some ty => .ok ty
      | none => .error (.unknownVar n)
  | ctx, .abs n t body =>
      match inferTypeDetailed ((n, t) :: ctx) body with
      | .ok t' => .ok (.arr t t')
      | .error e => .error e
  | ctx, .app f x =>
      match inferTypeDetailed ctx f with
      | .error e => .error e
      | .ok (.arr a b) =>
          match inferTypeDetailed ctx x with
          | .error e => .error e
          | .ok a' =>
              if a = a' then .ok b else .error (.argumentMismatch a a')
      | .ok actual => .error (.expectedFunction actual)
  | _, .hexLit _  => .ok .hex
  | _, .boolLit _ => .ok .bool
  | _, .jia       => .ok (.arr .hex (.arr .hex .hex))
  | _, .yi        => .ok .hex
  | _, .notB      => .ok (.arr .bool .bool)
  | _, .andB      => .ok (.arr .bool (.arr .bool .bool))
  | _, .orB       => .ok (.arr .bool (.arr .bool .bool))
  | _, .eqHex     => .ok (.arr .hex (.arr .hex .bool))
  | _, .forallH   => .ok (.arr (.arr .hex .bool) .bool)
  | _, .uniqueH   => .ok (.arr (.arr .hex .bool) .bool)
  | _, .exactly3H => .ok (.arr (.arr .hex .bool) .bool)
  | _, .majorityH => .ok (.arr (.arr .hex .bool) .bool)
  | _, .cuoH      => .ok (.arr .hex .hex)
  | _, .zongH     => .ok (.arr .hex .hex)
  | _, .huH       => .ok (.arr .hex .hex)
  | _, .cuoZongH  => .ok (.arr .hex .hex)
  | _, .flip1H    => .ok (.arr .hex .hex)
  | _, .flip2H    => .ok (.arr .hex .hex)
  | _, .flip3H    => .ok (.arr .hex .hex)
  | ctx, .catalogue1 id a =>
      match inferTypeDetailed ctx a with
      | .error e => .error e
      | .ok _ =>
          let sig := fullSignatureFor id
          if sig.arity = 1 then .ok (.catalogue sig.kind) else .error (.expectedFunction (.catalogue sig.kind))
  | ctx, .catalogue2 id a b =>
      match inferTypeDetailed ctx a, inferTypeDetailed ctx b with
      | .ok _, .ok _ =>
          let sig := fullSignatureFor id
          if sig.arity = 2 then .ok (.catalogue sig.kind) else .error (.expectedFunction (.catalogue sig.kind))
      | .error e, _ => .error e
      | _, .error e => .error e
  | ctx, .catalogue3 id a b c =>
      match inferTypeDetailed ctx a, inferTypeDetailed ctx b, inferTypeDetailed ctx c with
      | .ok _, .ok _, .ok _ =>
          let sig := fullSignatureFor id
          if sig.arity = 3 then .ok (.catalogue sig.kind) else .error (.expectedFunction (.catalogue sig.kind))
      | .error e, _, _ => .error e
      | _, .error e, _ => .error e
      | _, _, .error e => .error e

def elabSurfaceTyped (expr : SurfaceExpr) : Except ElabErr TypedTm :=
  match elabSurfaceExpr expr with
  | .error e => .error e
  | .ok t =>
      match inferTypeDetailed [] t with
      | .ok ty => .ok ⟨t, ty⟩
      | .error diag => .error (.typeMismatch diag)

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

/-- 基础 stdlib body 之 typecheck（来自 WenDef.Stdlib 既有定理）. -/
example : typeCheck [] Stdlib.tuiBody     = some (.arr .hex .hex)            := by native_decide
example : typeCheck [] Stdlib.biBody      = some (.arr .hex (.arr .hex .bool)) := by native_decide
example : typeCheck [] Stdlib.buBody      = some (.arr .bool .bool)          := by native_decide
example : typeCheck [] Stdlib.biModalBody = some (.arr (.arr .hex .bool) .bool) := by native_decide
example : typeCheck [] Stdlib.tongBody    = some (.arr .hex (.arr .hex .bool)) := by native_decide
example : typeCheck [] Stdlib.fanBody     = some (.arr (.arr .hex .bool) .bool) := by native_decide

/-- `.yi` primitive 之类型. -/
example : typeCheck [] Tm.yi = some .hex := by native_decide

example :
    (match inferTypeDetailed [] (.app .notB (.hexLit Hexagram.qian)) with
     | .error (.argumentMismatch .bool .hex) => true
     | _ => false) = true :=
  by native_decide

example :
    (match inferTypeDetailed [] (.app (.hexLit Hexagram.qian) (.hexLit Hexagram.kun)) with
     | .error (.expectedFunction .hex) => true
     | _ => false) = true :=
  by native_decide

end SSBX.Foundation.Wen.WenSurface
