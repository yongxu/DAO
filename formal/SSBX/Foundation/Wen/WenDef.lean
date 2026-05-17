/-
# WenDef — 文之定义机制（typed lambda over 64-hexagram universe）

Path 丙 § 风险 3 之完全缓解：
  baguaWen 22 内核 + WenDef 扩展 = wenyan-operators 281 字之全体表达力。

## 论证

由 64 元有限论域 + Church-Turing 之退化形式：
  ∀ wenyan-op : Hexagram^k → (Hexagram | Bool)^m,
    ∃ baguaWen 程序 + 用户 def, 其 denotation = 该 op

故 wenyan-ops 之全体可由 baguaWen 22 + 算子组合 + 用户 def 表达。
不可计算的「∀」「□」在 64 论域上退化为有限合取，全 `Decidable`，全可 `native_decide`。

## 设计

类型 (Ty):   Hex | Bool | Arr a b

项 (Tm):     var | abs | app | hexLit | boolLit
            + 10 内核 primitives:
              jia (加) :  Hex → Hex → Hex
              yi  (一) :  Hex
              notB (不):  Bool → Bool
              andB (並):  Bool → Bool → Bool
              orB  (或):  Bool → Bool → Bool
              eqHex (同): Hex → Hex → Bool
              forallH (凡): (Hex → Bool) → Bool      -- 64-fold ∀，有限可决
              uniqueH / exactly3H / majorityH: finite Hex counters
              cuoH (错): Hex → Hex
              zongH (综): Hex → Hex
              huH (互): Hex → Hex
              cuoZongH: Hex → Hex
              flip1H/flip2H/flip3H/flip4H/flip5H/flip6H: Hex → Hex

命名约定:
  · 天干 10 字（甲乙丙丁戊己庚辛壬癸）— 中性变量名
  · ASCII 标识符（[a-zA-Z][a-zA-Z0-9_]*）
  · 不在 `Bagua.BaguaWenSpec.reservedTokens` 内（即 baguaWen 22 之外）

## 复用

`Jian.JianSTLC` 之 untyped Lam β-reduction 已 0 sorry 完毕（subst_preserves_enc + simulation）.
`Tm` 之 operational semantics 经类型擦除可映入 `Lam`，由 `JianSTLC.simulation` 见证.
该映射定于 M2 之 `WenEval.lean`，本文件仅给类型层 + WenDef 结构.

## 状态

0 sorry / 0 axiom. 仅类型层；operational semantics 见 M2.

## Phase F.2 migration note (Cell192 → R8)

Was: `cellLit : Cell192 → Tm` (192 cells, Z/3 `Shi`).
Now: `cellLit : R8 → Tm` (256 cells, R 2 Klein-four `Shi`).

The cell-endo builtin tags `.shiNextC` / `.shiPrevC` keep their syntactic
identity here (this is the typed-λ surface; only types change). Their
operational semantics are defined elsewhere (`WenDefEval`); under V₄ both
collapse to the `Shi.complement` involution because V₄ involutions are self-inverse.
-/
import SSBX.Foundation.Atlas.Yi.Classical.Core.Yi
import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8
import SSBX.Foundation.Atlas.Yi.Classical.Computation.BaguaWenSpec
import SSBX.Text.OperatorSignatures

namespace SSBX.Foundation.Wen.WenDef

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaWenSpec
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorSignatures

/-! ## § 1  简单类型 -/

/-- 简单类型：Hex（卦，64 元）、Bool、函数。

    `quoted` 是 wen-2.0 ⑥/⑩ 之 quoted Tm 之类型：`「Y」` (引语括号) 内之
    内容作为不立即求值之数据，载入 `Tm.quote` 之 payload；其类型一律为
    `.quoted`，使 doxastic / 言说 / meta-programming 构造可在 STLC 上类
    型一致地承载。语义层不对 quoted body 求值（只作 syntactic carrier），
    亦不要求 body 类型上确切（quoted body 可为任意 Tm，包括含自由变量者）. -/
inductive Ty : Type
  | hex
  | bool
  | cell
  | catalogue (kind : SignatureKind)
  | prod (fst snd : Ty)
  | list (elem : Ty)
  | arr (dom cod : Ty)
  | quoted
  /-- wen-2.0 ④ user inductive type, nominal-by-name.  `name` is the
      type-level identifier declared by `类 NAME = CTOR₁ | … | CTORₙ`.
      Two `.user` types are equal iff their names match (decidable). -/
  | user (name : String)
deriving DecidableEq, Repr

/-! ## § 2  项 -/

/-- wen-2.0 ⑤ a pattern that can appear in one arm of a `析 X 为 …` match.

    - `.lit h`     — match a specific hexagram literal (only against `.hex`)
    - `.boolP b`   — match a specific boolean literal (only against `.bool`)
    - `.userP typeName ctorName` — match a user-defined constructor
                                   (only against `.user typeName`)
    - `.wildcard`  — match anything, no binding
    - `.varP n`    — match anything, bind to name `n` with the scrutinee's type

    Patterns are flat (no nesting) in v1.  Linearity is NOT enforced at
    the AST level — `varP` with duplicate names would shadow within the
    arm body, which is benign. -/
inductive MatchPat : Type
  | lit      (h : Hexagram)                : MatchPat
  | boolP    (b : Bool)                    : MatchPat
  | userP    (typeName ctorName : String)  : MatchPat
  | wildcard                                : MatchPat
  | varP     (n : String)                  : MatchPat
deriving DecidableEq, Repr

/-- 文之项：λ + app + var + 字面值 + core primitives。 -/
inductive Tm : Type
  | var     (n : String)               : Tm
  | abs     (n : String) (t : Ty) (body : Tm) : Tm
  | app     (f x : Tm)                 : Tm
  | hexLit  (h : Hexagram)             : Tm
  | boolLit (b : Bool)                 : Tm
  | cellLit (c : R8)              : Tm
  | jia                                : Tm  -- 加 :  Hex → Hex → Hex
  | yi                                 : Tm  -- 一 :  Hex
  | notB                               : Tm  -- 不 :  Bool → Bool
  | andB                               : Tm  -- 並 :  Bool → Bool → Bool
  | orB                                : Tm  -- 或 :  Bool → Bool → Bool
  | eqHex                              : Tm  -- 同 :  Hex → Hex → Bool
  | forallH                            : Tm  -- 凡 :  (Hex → Bool) → Bool
  | uniqueH                            : Tm  -- 唯 :  (Hex → Bool) → Bool
  | exactly3H                          : Tm  -- 三 :  (Hex → Bool) → Bool
  | majorityH                          : Tm  -- 過半 : (Hex → Bool) → Bool
  | cuoH                               : Tm  -- 错 :  Hex → Hex
  | zongH                              : Tm  -- 综 :  Hex → Hex
  | huH                                : Tm  -- 互 :  Hex → Hex
  | cuoZongH                           : Tm  -- 错综 : Hex → Hex
  | flip1H                             : Tm  -- 初爻 flip : Hex → Hex
  | flip2H                             : Tm  -- 二爻 flip : Hex → Hex
  | flip3H                             : Tm  -- 三爻 flip : Hex → Hex
  | flip4H                             : Tm  -- 四爻 flip : Hex → Hex
  | flip5H                             : Tm  -- 五爻 flip : Hex → Hex
  | flip6H                             : Tm  -- 上爻 flip : Hex → Hex
  | pairH                              : Tm  -- pair : Hex → Hex → Hex×Hex
  | dupH                               : Tm  -- dup : Hex → Hex×Hex
  | list1H                             : Tm  -- singleton : Hex → List Hex
  | list2H                             : Tm  -- pair-list : Hex → Hex → List Hex
  | list3H                             : Tm  -- triple-list : Hex → Hex → Hex → List Hex
  | headH                              : Tm  -- head : List Hex → Hex
  | eqCell                             : Tm  -- Cell → Cell → Bool
  | cuoC                               : Tm  -- Cell → Cell, preserve 时
  | zongC                              : Tm  -- Cell → Cell, preserve 时
  | huC                                : Tm  -- Cell → Cell, preserve 时
  | shiNextC                           : Tm  -- Cell → Cell, 时态单步 (V₄ Shi.complement)
  | shiPrevC                           : Tm  -- Cell → Cell, 时态单步 (V₄ Shi.complement, self-inverse)
  | flip1C                             : Tm  -- Cell → Cell, y1 flip
  | flip2C                             : Tm  -- Cell → Cell, y2 flip
  | flip3C                             : Tm  -- Cell → Cell, y3 flip
  | flip4C                             : Tm  -- Cell → Cell, y4 flip
  | flip5C                             : Tm  -- Cell → Cell, y5 flip
  | flip6C                             : Tm  -- Cell → Cell, y6 flip
  | catalogue1 (id : OperatorId) (a : Tm) : Tm
  | catalogue2 (id : OperatorId) (a b : Tm) : Tm
  | catalogue3 (id : OperatorId) (a b c : Tm) : Tm
  /-- `quote body`: wen-2.0 ⑥/⑩ 之引语 (引语括号 `「Y」` 内之 Tm).
      Body 本身可为任意 Tm（含自由变量、ill-typed 子项不在此处校验）；
      整体类型为 `.quoted`，载入 doxastic / 言说 / meta-prog 之 deferred Tm 数据.
      `WenDefEval` 仅以 builtin tag 标记此 Value，不对 body 作 β-reduction. -/
  | quote (body : Tm) : Tm
  /-- `unquote q`: wen-2.0 ⑪ quote-eval (`执 「X」`).  Evaluates `q` (which must
      reduce to a `.quoteV inner`) and then re-evaluates `inner` under the
      *empty* environment.  Fuel-bounded — divergent quoted bodies exhaust
      fuel cleanly (return `none`).

      Typecheck rule (v1): `unquote q` is `.hex`.  Justified by the doctrine
      "every Wen term reduces to a Hex value at the top of the R-tower"; the
      kernel cannot peer inside the opaque `.quoted` type so this is the only
      sound universal answer.  Future work (with HM on `.quoted`) could
      refine to the inner body's type.

      Argument typecheck: `q` must have type `.quoted` (so applying `执` to a
      non-quoted argument is rejected by `typeCheck`). -/
  | unquote (q : Tm) : Tm
  /-- `fix n t body`: wen-2.0 ② μ-fixpoint (`定递 n 为 body`).
      Models `μ n : t. body` — the body is closed over a self-reference to
      `n` of type `t`; operationally unrolled on-demand by the fuel-bounded
      evaluator (`WenDefEval.evalFuel`).  Each unrolling consumes one fuel
      tick, so divergent recursion exhausts fuel cleanly rather than crashing.
      Typecheck rule:  `body` typechecks to `t` in `(n,t) :: ctx`. -/
  | fix (n : String) (t : Ty) (body : Tm) : Tm
  /-- wen-2.0 ④ user inductive constructor.  `typeName` is the surface
      declaration name (e.g. `"五行"`), `ctorName` is the constructor head
      (e.g. `"木"`).  Typechecks to `.user typeName` unconditionally —
      the constructor table is enforced at the surface parsing layer
      (`WenSurface.EndToEnd` rejects bare ctor names without a `类` decl
      in scope and rejects ctor clashes with existing 定/catalogue
      names).  Operationally the value is opaque to evaluation (see
      `WenDefEval.userCtorV`); reduction relations from the cells/Hex
      sublanguage do not interpret it. -/
  | userCtor (typeName ctorName : String) : Tm
  /-- wen-2.0 ⑤ pattern-matching scrutinee + arm list.  `scrut` is the
      term being decomposed; each `(pat, body)` arm pairs a pattern with
      its result expression.  Arms are tried top-down at runtime; if
      none match, evaluation yields `none` (clean error — v1 has no
      exhaustiveness check).  Type checking requires every arm body to
      synthesize the SAME type, and patterns must be compatible with
      the scrutinee's type (see `patternBindings`). -/
  | «match» (scrut : Tm) (arms : List (MatchPat × Tm)) : Tm
deriving Repr, DecidableEq

/-! ## § 3  类型检查 -/

/-- 上下文：变量名 → 类型。 -/
abbrev Ctx := List (String × Ty)

/--
Conservative argument type expected by structural catalogue normal forms.

This is not a domain semantics claim. It only prevents catalogue wrappers from
accepting arguments outside their coarse signature shape.
-/
def catalogueExpectedArgTy (kind : SignatureKind) (pos : Nat) : Ty :=
  match kind with
  | .propUnary => .bool
  | .propImp
  | .propConnective
  | .binaryModal => .bool
  | .quantifier => .arr .hex .bool
  | .app => if pos = 0 then .arr .hex .hex else .hex
  | .endoComp => .arr .hex .hex
  | _ => .hex

/--
An argument's actual type is acceptable for a catalogue position if it matches
the structural expectation, or — for `textAct` operators (wen-2.0 ⑥ 曰 direct
speech) — the last positional argument is allowed to be `.quoted` instead of
`.hex`.  The "speech content" of `X 曰 Y` carries `Y` as `.quoted` data when
it is wrapped in 引语括号 「」/『』; bare Hex remains valid for back-compat.
-/
def catalogueArgTypeOk (sig : CoveredOperatorSignature) (pos : Nat) (ty : Ty) : Bool :=
  let expected := catalogueExpectedArgTy sig.kind pos
  decide (ty = expected)
    || (sig.kind = .textAct && pos + 1 = sig.arity && ty = .quoted)

def catalogueArgTypesOk (sig : CoveredOperatorSignature) : List Ty → Bool
  | [a] =>
      decide (sig.arity = 1) && catalogueArgTypeOk sig 0 a
  | [a, b] =>
      decide (sig.arity = 2)
        && catalogueArgTypeOk sig 0 a
        && catalogueArgTypeOk sig 1 b
  | [a, b, c] =>
      decide (sig.arity = 3)
        && catalogueArgTypeOk sig 0 a
        && catalogueArgTypeOk sig 1 b
        && catalogueArgTypeOk sig 2 c
  | _ => false

/-- 在上下文中查找变量类型。 -/
def Ctx.lookup : Ctx → String → Option Ty
  | [], _ => none
  | (n, t) :: rest, name => if n = name then some t else rest.lookup name

/-- wen-2.0 ⑤ pattern compatibility + binding extraction.

    Given a `pat` and the inferred type `scrutTy` of the scrutinee, decide
    whether the pattern is type-compatible.  On success returns the list of
    `(name, ty)` bindings the pattern introduces (used to extend the arm
    body's typing context).

    Rules:
    · `.lit h`             ↔ `scrutTy = .hex`,  no bindings
    · `.boolP b`           ↔ `scrutTy = .bool`, no bindings
    · `.userP tn _`        ↔ `scrutTy = .user tn`, no bindings
                            (ctor-name validity enforced at the surface
                             layer by the user-ctor table)
    · `.wildcard`          ↔ any `scrutTy`, no bindings
    · `.varP n`            ↔ any `scrutTy`, binds `n` to `scrutTy`

    Returns `none` if the pattern is type-incompatible. -/
def patternBindings : MatchPat → Ty → Option (List (String × Ty))
  | .lit _,        .hex      => some []
  | .boolP _,      .bool     => some []
  | .userP tn _,   .user tn' => if tn = tn' then some [] else none
  | .wildcard,     _         => some []
  | .varP n,       t         => some [(n, t)]
  | _,             _         => none

/-- 类型检查：返回项的类型 (well-typed) 或 none (ill-typed)。
    总函数（结构递归 on Tm）。 -/
def typeCheck : Ctx → Tm → Option Ty
  | ctx, .var n => ctx.lookup n
  | ctx, .abs n t body =>
      match typeCheck ((n, t) :: ctx) body with
      | some t' => some (.arr t t')
      | none    => none
  | ctx, .app f x =>
      match typeCheck ctx f, typeCheck ctx x with
      | some (.arr a b), some a' => if a = a' then some b else none
      | _, _ => none
  | _, .hexLit _  => some .hex
  | _, .boolLit _ => some .bool
  | _, .cellLit _ => some .cell
  | _, .jia       => some (.arr .hex (.arr .hex .hex))
  | _, .yi        => some .hex
  | _, .notB      => some (.arr .bool .bool)
  | _, .andB      => some (.arr .bool (.arr .bool .bool))
  | _, .orB       => some (.arr .bool (.arr .bool .bool))
  | _, .eqHex     => some (.arr .hex (.arr .hex .bool))
  | _, .forallH   => some (.arr (.arr .hex .bool) .bool)
  | _, .uniqueH   => some (.arr (.arr .hex .bool) .bool)
  | _, .exactly3H => some (.arr (.arr .hex .bool) .bool)
  | _, .majorityH => some (.arr (.arr .hex .bool) .bool)
  | _, .cuoH      => some (.arr .hex .hex)
  | _, .zongH     => some (.arr .hex .hex)
  | _, .huH       => some (.arr .hex .hex)
  | _, .cuoZongH  => some (.arr .hex .hex)
  | _, .flip1H    => some (.arr .hex .hex)
  | _, .flip2H    => some (.arr .hex .hex)
  | _, .flip3H    => some (.arr .hex .hex)
  | _, .flip4H    => some (.arr .hex .hex)
  | _, .flip5H    => some (.arr .hex .hex)
  | _, .flip6H    => some (.arr .hex .hex)
  | _, .pairH     => some (.arr .hex (.arr .hex (.prod .hex .hex)))
  | _, .dupH      => some (.arr .hex (.prod .hex .hex))
  | _, .list1H    => some (.arr .hex (.list .hex))
  | _, .list2H    => some (.arr .hex (.arr .hex (.list .hex)))
  | _, .list3H    => some (.arr .hex (.arr .hex (.arr .hex (.list .hex))))
  | _, .headH     => some (.arr (.list .hex) .hex)
  | _, .eqCell    => some (.arr .cell (.arr .cell .bool))
  | _, .cuoC      => some (.arr .cell .cell)
  | _, .zongC     => some (.arr .cell .cell)
  | _, .huC       => some (.arr .cell .cell)
  | _, .shiNextC  => some (.arr .cell .cell)
  | _, .shiPrevC  => some (.arr .cell .cell)
  | _, .flip1C    => some (.arr .cell .cell)
  | _, .flip2C    => some (.arr .cell .cell)
  | _, .flip3C    => some (.arr .cell .cell)
  | _, .flip4C    => some (.arr .cell .cell)
  | _, .flip5C    => some (.arr .cell .cell)
  | _, .flip6C    => some (.arr .cell .cell)
  | ctx, .catalogue1 id a =>
      let sig := fullSignatureFor id
      match typeCheck ctx a with
      | some ta =>
          if catalogueArgTypesOk sig [ta] then
            some (.catalogue sig.kind)
          else
            none
      | none => none
  | ctx, .catalogue2 id a b =>
      let sig := fullSignatureFor id
      match typeCheck ctx a, typeCheck ctx b with
      | some ta, some tb =>
          if catalogueArgTypesOk sig [ta, tb] then
            some (.catalogue sig.kind)
          else
            none
      | _, _ => none
  | ctx, .catalogue3 id a b c =>
      let sig := fullSignatureFor id
      match typeCheck ctx a, typeCheck ctx b, typeCheck ctx c with
      | some ta, some tb, some tc =>
          if catalogueArgTypesOk sig [ta, tb, tc] then
            some (.catalogue sig.kind)
          else
            none
      | _, _, _ => none
  | _, .quote _ => some .quoted
  | ctx, .unquote q =>
      match typeCheck ctx q with
      | some .quoted => some .hex
      | _ => none
  | ctx, .fix n t body =>
      match typeCheck ((n, t) :: ctx) body with
      | some t' => if t = t' then some t else none
      | none => none
  -- wen-2.0 ④ user inductive constructor: typechecks to `.user typeName`.
  -- The ctor-table validity is enforced at the surface layer, not here.
  | _, .userCtor typeName _ => some (.user typeName)
  -- wen-2.0 ⑤ pattern-match expression: 析 X 为 P₁ → E₁；P₂ → E₂…
  -- Strategy: typecheck the scrutinee first; then walk each arm checking
  -- (i) pattern compatibility with scrutinee type, (ii) the arm body
  -- typechecks under the extended ctx, (iii) every arm body shares one
  -- common type (the result type).  An empty arm list rejects.  The
  -- inner `checkArms` loop is structural-recursive on `arms : List …`
  -- and never re-enters `typeCheck` recursively on the scrutinee.
  | ctx, .«match» scrut arms =>
      match typeCheck ctx scrut with
      | none => none
      | some scrutTy =>
          let rec checkArms : List (MatchPat × Tm) → Option Ty → Option Ty
            | [], acc => acc
            | (pat, body) :: rest, acc =>
                match patternBindings pat scrutTy with
                | none => none
                | some binds =>
                    let ctx' := binds ++ ctx
                    match typeCheck ctx' body with
                    | none => none
                    | some bodyTy =>
                        match acc with
                        | none      => checkArms rest (some bodyTy)
                        | some prev =>
                            if prev = bodyTy then checkArms rest (some bodyTy)
                            else none
          checkArms arms none

example :
    typeCheck [] (.catalogue2 .E_2 (.hexLit Hexagram.heaven) (.hexLit Hexagram.heaven))
      = some (.catalogue .textAct) := by native_decide

/-! ### wen-2.0 ⑥ 曰 / ⑩ 引语括号 typecheck examples -/

/-- 「子曰：「学」」 — 第二参数 `.quote .yi` 之类型 `.quoted`，textAct 接受. -/
example :
    typeCheck [] (.catalogue2 .E_2 (.hexLit Hexagram.heaven) (.quote .yi))
      = some (.catalogue .textAct) := by native_decide

/-- Quote a non-trivially typed body (.notB : Bool → Bool) is fine; `.quoted`
    erases inner type. -/
example :
    typeCheck [] (.quote .notB) = some .quoted := by native_decide

/-- Quote of `.var` (free variable) still typechecks — quote 不强求 body
    well-typed，符合 wen-2.0 ⑥ "不立即 eval / deferred Tm 数据" 之语义. -/
example :
    typeCheck [] (.quote (.var "x")) = some .quoted := by native_decide

/-- Back-compat：曰 之两 Hex 参数仍为合法 textAct 应用. -/
example :
    typeCheck [] (.catalogue2 .E_2 (.hexLit Hexagram.heaven) (.hexLit Hexagram.earth))
      = some (.catalogue .textAct) := by native_decide

example :
    typeCheck [] (.catalogue2 .E_2 (.boolLit true) (.boolLit true)) = none := by
  native_decide

example :
    typeCheck [] (.catalogue2 .P_23 (.boolLit true) (.boolLit false))
      = some (.catalogue .propConnective) := by native_decide

example :
    typeCheck [] (.catalogue2 .P_23 (.hexLit Hexagram.heaven) (.hexLit Hexagram.earth))
      = none := by native_decide

/-! ### wen-2.0 ⑪ `.unquote` typecheck examples -/

/-- `执 「一」` typechecks to `.hex`. -/
example :
    typeCheck [] (.unquote (.quote .yi)) = some .hex := by native_decide

/-- `执 「乾」` typechecks to `.hex`. -/
example :
    typeCheck [] (.unquote (.quote (.hexLit Hexagram.heaven))) = some .hex := by
  native_decide

/-- Quoted lambda — still typechecks (unquote returns `.hex`, evaluation will
    decide at runtime). -/
example :
    typeCheck [] (.unquote (.quote .notB)) = some .hex := by native_decide

/-- Type error: applying `执` to a non-`.quoted` arg (`一 : .hex`) is rejected. -/
example :
    typeCheck [] (.unquote .yi) = none := by native_decide

/-- Type error: applying `执` to a `.bool` is rejected. -/
example :
    typeCheck [] (.unquote (.boolLit true)) = none := by native_decide

/-- Type error: applying `执` to a function is rejected. -/
example :
    typeCheck [] (.unquote .cuoH) = none := by native_decide

/-! ### wen-2.0 ② `.fix` typecheck examples -/

/-- A trivial fixpoint at type `.hex` (body just returns self-reference) is
    typeable as `.hex` — operationally diverges but typechecks. -/
example :
    typeCheck [] (.fix "f" .hex (.var "f")) = some .hex := by native_decide

/-- `μ f : Hex → Hex. λ x. f x` typechecks to `Hex → Hex`. -/
example :
    typeCheck []
        (.fix "f" (.arr .hex .hex)
          (.abs "x" .hex (.app (.var "f") (.var "x"))))
      = some (.arr .hex .hex) := by native_decide

/-- Mismatched annotation: body typechecks to a different type → none. -/
example :
    typeCheck []
        (.fix "f" .hex (.abs "x" .hex (.var "x")))
      = none := by native_decide

/-- An ill-typed body propagates as none. -/
example :
    typeCheck []
        (.fix "f" .hex (.app .notB .yi))
      = none := by native_decide

/-! ### wen-2.0 ⑤ `.match` typecheck examples -/

/-- Match a Bool literal against two boolean arms, both producing Hex. -/
example :
    typeCheck []
        (.«match» (.boolLit true)
          [(.boolP true, .yi),
           (.boolP false, .hexLit Hexagram.heaven)])
      = some .hex := by native_decide

/-- Match on a Hex scrutinee with a literal arm + a wildcard fallback. -/
example :
    typeCheck []
        (.«match» .yi
          [(.lit Hexagram.heaven, .boolLit true),
           (.wildcard, .boolLit false)])
      = some .bool := by native_decide

/-- Match with a `varP` binder: arm body uses the bound name. -/
example :
    typeCheck []
        (.«match» .yi
          [(.varP "x", .var "x")])
      = some .hex := by native_decide

/-- Type error: two arms produce different result types. -/
example :
    typeCheck []
        (.«match» (.boolLit true)
          [(.boolP true, .yi),
           (.boolP false, .boolLit true)])
      = none := by native_decide

/-- Type error: pattern type doesn't match scrutinee (Bool pattern on Hex
    scrutinee). -/
example :
    typeCheck []
        (.«match» .yi
          [(.boolP true, .yi)])
      = none := by native_decide

/-- Empty arm list rejects (no result type). -/
example :
    typeCheck [] (.«match» .yi []) = none := by native_decide

/-- User-ctor pattern matches against `.user` scrutinee. -/
example :
    typeCheck []
        (.«match» (.userCtor "甴甴" "甲")
          [(.userP "甴甴" "甲", .yi),
           (.wildcard, .yi)])
      = some .hex := by native_decide

/-- Type error: user-ctor pattern with wrong type name. -/
example :
    typeCheck []
        (.«match» (.userCtor "甴甴" "甲")
          [(.userP "真假" "甲", .yi)])
      = none := by native_decide

/-! ### wen-2.0 ④ `.userCtor` typecheck examples -/

/-- A bare user-ctor typechecks to its nominal `.user` type. -/
example :
    typeCheck [] (.userCtor "五行" "木") = some (.user "五行") := by native_decide

/-- Two ctors of the same user type unify (same `.user` head). -/
example :
    typeCheck [] (.userCtor "真假" "真") = some (.user "真假") := by native_decide

/-- Distinct user types are distinct (decidable). -/
example :
    Ty.user "五行" ≠ Ty.user "真假" := by native_decide

/-! ## § 3b  Free-variable substitution (used by wen-2.0 ② 定递)

  `substTmFree name replacement t` substitutes every **free** occurrence of
  `Tm.var name` in `t` with `replacement`.  Binders (`abs`, `fix`) that
  re-bind `name` shadow the substitution within their body.  Note:
  `replacement` is inserted verbatim (no α-renaming), so this is safe only
  when `replacement` is a closed term — which is the use case here
  (recursive defs produce closed `.fix` terms).
-/
def substTmFree (name : String) (replacement : Tm) : Tm → Tm
  | .var n => if n = name then replacement else .var n
  | .abs n t body =>
      if n = name then .abs n t body
      else .abs n t (substTmFree name replacement body)
  | .app f x => .app (substTmFree name replacement f) (substTmFree name replacement x)
  | .catalogue1 id a => .catalogue1 id (substTmFree name replacement a)
  | .catalogue2 id a b =>
      .catalogue2 id (substTmFree name replacement a) (substTmFree name replacement b)
  | .catalogue3 id a b c =>
      .catalogue3 id (substTmFree name replacement a)
        (substTmFree name replacement b) (substTmFree name replacement c)
  | .quote body => .quote body  -- quote body is data; not subject to subst
  | .unquote q => .unquote (substTmFree name replacement q)
  | .fix n t body =>
      if n = name then .fix n t body
      else .fix n t (substTmFree name replacement body)
  -- wen-2.0 ⑤: subst into scrutinee and each arm body; varP / userP-bound
  -- names within a pattern shadow the outer substitution.
  | .«match» scrut arms =>
      let scrut' := substTmFree name replacement scrut
      let arms' := arms.map (fun (p, b) =>
        match p with
        | .varP n => if n = name then (p, b) else (p, substTmFree name replacement b)
        | _ => (p, substTmFree name replacement b))
      .«match» scrut' arms'
  | t => t  -- literals + primitives are leaves

/-! ## § 3c  wen-2.0 ④ user inductive constructor table

  A `UserCtor` is one row of a `类 TYPENAME = CTOR₁ | … | CTORₙ` decl.
  `name` is the constructor head glyph (e.g. `"木"`), `typeName` is the
  enclosing user type (e.g. `"五行"`).  A list of `UserCtor`s is
  threaded through the WenSurface compile pipeline so the elaborator can
  resolve bare ctor names against the in-scope user-decl table.

  We do NOT bake this table into `Tm.userCtor` itself — the Tm only
  carries `typeName` + `ctorName`, both as bare strings.  Type-checking
  succeeds for any `.userCtor t c` regardless of the table (the table's
  role is *resolution* + decl-time *clash detection*, not kernel typing).
-/

/-- One constructor row of a `类 TYPENAME = CTOR₁ | … | CTORₙ` decl. -/
structure UserCtor where
  /-- Constructor head glyph (e.g. `"木"`). -/
  name     : String
  /-- Enclosing user type name (e.g. `"五行"`). -/
  typeName : String
deriving DecidableEq, Repr

/-- Lookup a ctor in a table by its bare name.  Returns the typeName of the
    enclosing user inductive, or `none` if no decl in scope binds this glyph. -/
def UserCtor.lookupType (table : List UserCtor) (name : String) : Option String :=
  match table.find? (fun c => c.name = name) with
  | some c => some c.typeName
  | none   => none

/-! ## § 4  命名空间 -/

/-- 天干 10 字：中性变量名空间。 -/
def heavenlyStems : List String :=
  ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"]

/-- ASCII 标识符判定：开头字母，余下字母/数字/下划线。 -/
def isAsciiIdent (s : String) : Bool :=
  match s.toList with
  | []        => false
  | c :: rest => c.isAlpha && rest.all (fun c => c.isAlpha || c.isDigit || c = '_')

/-- 合法 def 名：天干 ∪ ASCII，不在 baguaWen 22 reservedTokens 内。 -/
def isValidName (s : String) : Bool :=
  (heavenlyStems.contains s || isAsciiIdent s) &&
  !reservedTokens.contains s

/-! ## § 5  WenDef 结构 -/

/-- 一个 wenyan 定义：name + body + 类型签名 + 名合度凭据 + 类型一致凭据。 -/
structure WenDef where
  name           : String
  body           : Tm
  bodyType       : Ty
  validName      : isValidName name = true
  bodyTypechecks : typeCheck [] body = some bodyType

/-! ## § 6  命名空间 sanity -/

theorem heavenlyStems_length : heavenlyStems.length = 10 := by native_decide

theorem heavenlyStems_all_valid :
    heavenlyStems.all isValidName = true := by native_decide

theorem heavenlyStems_disjoint_reserved :
    heavenlyStems.all (fun s => !reservedTokens.contains s) = true := by native_decide

/-- ASCII 标识符之范例皆为合度名。 -/
example : isValidName "tui"     = true := by native_decide
example : isValidName "bi"      = true := by native_decide
example : isValidName "biModal" = true := by native_decide

/-- 与 baguaWen 22 重之 CJK token 不合度（保命名空间分离）。 -/
example : isValidName "推"  = false := by native_decide
example : isValidName "终"  = false := by native_decide
example : isValidName "比爻" = false := by native_decide

/-- 数字开头之 ASCII 不合度。 -/
example : isValidName "1tui"   = false := by native_decide

/-- 空串不合度。 -/
example : isValidName ""       = false := by native_decide

/-! ## § 7  Stdlib 示例：wenyan-operators 之 def

  每条用拼音 / ASCII 作 WenDef.name（避免与 baguaWen 22 之 CJK 冲突）；
  CJK 名仅作 Lean-level navigation 与文档参考。
-/

namespace Stdlib

/-! ### T-10 推（推动 — 沿轴推进；孟子「推恩足以保四海」）

  实现：λx:Hex. 加 一 x  （即 YiCore.«生»，64-cyclic group action）.
  类型：Hex → Hex.
-/

def tuiBody : Tm :=
  .abs "x" .hex (.app (.app .jia .yi) (.var "x"))

theorem tuiBody_typed :
    typeCheck [] tuiBody = some (.arr .hex .hex) := by native_decide

def tuiDef : WenDef where
  name           := "tui"
  body           := tuiBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### R-8 比（邻接 — 易·彖「比，辅也」）

  第一近似实现：λa b:Hex. 同 a b （恒等谓词）.
  Refined 版（限于「相邻爻位」）留待 stdlib v2.
  类型：Hex → Hex → Bool.
-/

def biBody : Tm :=
  .abs "a" .hex (.abs "b" .hex (.app (.app .eqHex (.var "a")) (.var "b")))

theorem biBody_typed :
    typeCheck [] biBody = some (.arr .hex (.arr .hex .bool)) := by native_decide

def biDef : WenDef where
  name           := "bi"
  body           := biBody
  bodyType       := .arr .hex (.arr .hex .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### N-1 不（否定）

  实现：直接是 .notB primitive.
  类型：Bool → Bool.
-/

def buBody : Tm := .notB

theorem buBody_typed :
    typeCheck [] buBody = some (.arr .bool .bool) := by native_decide

def buDef : WenDef where
  name           := "bu"
  body           := buBody
  bodyType       := .arr .bool .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### M-1 必（必然 — modal □）

  在 64 元有限论域上，∀h ≡ □（固定可达关系）.
  实现：直接是 .forallH primitive.
  类型：(Hex → Bool) → Bool.
-/

def biModalBody : Tm := .forallH

theorem biModalBody_typed :
    typeCheck [] biModalBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def biModalDef : WenDef where
  name           := "biModal"
  body           := biModalBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### I-1 同（恒等关系）

  实现：直接是 .eqHex primitive.
  类型：Hex → Hex → Bool.
-/

def tongBody : Tm := .eqHex

theorem tongBody_typed :
    typeCheck [] tongBody = some (.arr .hex (.arr .hex .bool)) := by native_decide

def tongDef : WenDef where
  name           := "tong"
  body           := tongBody
  bodyType       := .arr .hex (.arr .hex .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Q-1 凡（universal 量化）

  实现：直接是 .forallH primitive (有限 ∀ over 64).
  类型：(Hex → Bool) → Bool.
-/

def fanBody : Tm := .forallH

theorem fanBody_typed :
    typeCheck [] fanBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def fanDef : WenDef where
  name           := "fan"
  body           := fanBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### T-12 損（减一 / 反生）

  实现：λx:Hex. 加 «坤» x.
  «坤» 之索引为 63，故 (x + 63) mod 64 = (x − 1) mod 64，即 mod-64 减一.
  与 T-13 益 互逆；与 T-10 推 一加一减.
  类型：Hex → Hex.
-/

def sunBody : Tm :=
  .abs "x" .hex (.app (.app .jia (.hexLit Hexagram.earth)) (.var "x"))

theorem sunBody_typed :
    typeCheck [] sunBody = some (.arr .hex .hex) := by native_decide

def sunDef : WenDef where
  name           := "sun"
  body           := sunBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### T-13 益（加一 / 同推）

  实现：λx:Hex. 加 一 x  （即 YiCore.«生»，与 T-10 推 共体）.
  以独立 WenDef 收录，明示 catalogue 中「益 = 推」之同义.
  类型：Hex → Hex.
-/

def yiBenefitBody : Tm :=
  .abs "x" .hex (.app (.app .jia .yi) (.var "x"))

theorem yiBenefitBody_typed :
    typeCheck [] yiBenefitBody = some (.arr .hex .hex) := by native_decide

def yiBenefitDef : WenDef where
  name           := "yiBenefit"
  body           := yiBenefitBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Z-5 / Z-6 / Z-3 / T-6 exact Hex transforms

  这些对应 `Yi.Hexagram` 已证明的结构算子，不从 catalogue 文义临时解释。
-/

def cuoBody : Tm := .cuoH

theorem cuoBody_typed :
    typeCheck [] cuoBody = some (.arr .hex .hex) := by native_decide

def cuoDef : WenDef where
  name           := "complement"
  body           := cuoBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def zongBody : Tm := .zongH

theorem zongBody_typed :
    typeCheck [] zongBody = some (.arr .hex .hex) := by native_decide

def zongDef : WenDef where
  name           := "reverse"
  body           := zongBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def huBody : Tm := .huH

theorem huBody_typed :
    typeCheck [] huBody = some (.arr .hex .hex) := by native_decide

def huDef : WenDef where
  name           := "interlace"
  body           := huBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def fanReverseBody : Tm := .cuoH

theorem fanReverseBody_typed :
    typeCheck [] fanReverseBody = some (.arr .hex .hex) := by native_decide

def fanReverseDef : WenDef where
  name           := "fanReverse"
  body           := fanReverseBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def hexIdBody : Tm :=
  .abs "x" .hex (.var "x")

theorem hexIdBody_typed :
    typeCheck [] hexIdBody = some (.arr .hex .hex) := by native_decide

def hexIdDef : WenDef where
  name           := "hexId"
  body           := hexIdBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def cuoZongBody : Tm := .cuoZongH

theorem cuoZongBody_typed :
    typeCheck [] cuoZongBody = some (.arr .hex .hex) := by native_decide

def cuoZongDef : WenDef where
  name           := "complementReverse"
  body           := cuoZongBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip1Body : Tm := .flip1H

theorem flip1Body_typed :
    typeCheck [] flip1Body = some (.arr .hex .hex) := by native_decide

def flip1Def : WenDef where
  name           := "flip1"
  body           := flip1Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip2Body : Tm := .flip2H

theorem flip2Body_typed :
    typeCheck [] flip2Body = some (.arr .hex .hex) := by native_decide

def flip2Def : WenDef where
  name           := "flip2"
  body           := flip2Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip3Body : Tm := .flip3H

theorem flip3Body_typed :
    typeCheck [] flip3Body = some (.arr .hex .hex) := by native_decide

def flip3Def : WenDef where
  name           := "flip3"
  body           := flip3Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip4Body : Tm := .flip4H

theorem flip4Body_typed :
    typeCheck [] flip4Body = some (.arr .hex .hex) := by native_decide

def flip4Def : WenDef where
  name           := "flip4"
  body           := flip4Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip5Body : Tm := .flip5H

theorem flip5Body_typed :
    typeCheck [] flip5Body = some (.arr .hex .hex) := by native_decide

def flip5Def : WenDef where
  name           := "flip5"
  body           := flip5Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip6Body : Tm := .flip6H

theorem flip6Body_typed :
    typeCheck [] flip6Body = some (.arr .hex .hex) := by native_decide

def flip6Def : WenDef where
  name           := "flip6"
  body           := flip6Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Logic and identity aliases promoted from catalogue-only rows

  These bodies reuse the existing `Bool`, `Hex`, and finite `forallH` core.
  They deliberately avoid catalogue rows that require new carriers such as
  `R8` (was `Cell192` pre-Phase F.2), paths, text acts, modal frames,
  or domain-specific state.
-/

def impBody : Tm :=
  .abs "p" .bool
    (.abs "q" .bool
      (.app (.app .orB (.app .notB (.var "p"))) (.var "q")))

theorem impBody_typed :
    typeCheck [] impBody = some (.arr .bool (.arr .bool .bool)) := by native_decide

def impDef : WenDef where
  name           := "imp"
  body           := impBody
  bodyType       := .arr .bool (.arr .bool .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def xorBBody : Tm :=
  .abs "p" .bool
    (.abs "q" .bool
      (.app
        (.app .orB
          (.app (.app .andB (.var "p")) (.app .notB (.var "q"))))
        (.app (.app .andB (.app .notB (.var "p"))) (.var "q"))))

theorem xorBBody_typed :
    typeCheck [] xorBBody = some (.arr .bool (.arr .bool .bool)) := by native_decide

def xorBDef : WenDef where
  name           := "xorB"
  body           := xorBBody
  bodyType       := .arr .bool (.arr .bool .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def neqHexBody : Tm :=
  .abs "a" .hex
    (.abs "b" .hex
      (.app .notB (.app (.app .eqHex (.var "a")) (.var "b"))))

theorem neqHexBody_typed :
    typeCheck [] neqHexBody = some (.arr .hex (.arr .hex .bool)) := by native_decide

def neqHexDef : WenDef where
  name           := "neqHex"
  body           := neqHexBody
  bodyType       := .arr .hex (.arr .hex .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def existsHBody : Tm :=
  .abs "p" (.arr .hex .bool)
    (.app .notB
      (.app .forallH
        (.abs "x" .hex
          (.app .notB (.app (.var "p") (.var "x"))))))

theorem existsHBody_typed :
    typeCheck [] existsHBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def existsHDef : WenDef where
  name           := "existsH"
  body           := existsHBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def noneHBody : Tm :=
  .abs "p" (.arr .hex .bool)
    (.app .forallH
      (.abs "x" .hex
        (.app .notB (.app (.var "p") (.var "x")))))

theorem noneHBody_typed :
    typeCheck [] noneHBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def noneHDef : WenDef where
  name           := "noneH"
  body           := noneHBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def uniqueHBody : Tm := .uniqueH

theorem uniqueHBody_typed :
    typeCheck [] uniqueHBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def uniqueHDef : WenDef where
  name           := "uniqueH"
  body           := uniqueHBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def exactly3HBody : Tm := .exactly3H

theorem exactly3HBody_typed :
    typeCheck [] exactly3HBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def exactly3HDef : WenDef where
  name           := "exactly3H"
  body           := exactly3HBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def majorityHBody : Tm := .majorityH

theorem majorityHBody_typed :
    typeCheck [] majorityHBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def majorityHDef : WenDef where
  name           := "majorityH"
  body           := majorityHBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def endoCompBody : Tm :=
  .abs "f" (.arr .hex .hex)
    (.abs "g" (.arr .hex .hex)
      (.abs "x" .hex
        (.app (.var "f") (.app (.var "g") (.var "x")))))

theorem endoCompBody_typed :
    typeCheck [] endoCompBody =
      some (.arr (.arr .hex .hex) (.arr (.arr .hex .hex) (.arr .hex .hex))) := by
  native_decide

def endoCompDef : WenDef where
  name           := "endoComp"
  body           := endoCompBody
  bodyType       := .arr (.arr .hex .hex) (.arr (.arr .hex .hex) (.arr .hex .hex))
  validName      := by native_decide
  bodyTypechecks := by native_decide

def hexApplyBody : Tm :=
  .abs "f" (.arr .hex .hex)
    (.abs "x" .hex
      (.app (.var "f") (.var "x")))

theorem hexApplyBody_typed :
    typeCheck [] hexApplyBody =
      some (.arr (.arr .hex .hex) (.arr .hex .hex)) := by
  native_decide

def hexApplyDef : WenDef where
  name           := "hexApply"
  body           := hexApplyBody
  bodyType       := .arr (.arr .hex .hex) (.arr .hex .hex)
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Structural truth/motion helpers -/

def boolMarkerBody : Tm :=
  .abs "p" .bool (.var "p")

theorem boolMarkerBody_typed :
    typeCheck [] boolMarkerBody = some (.arr .bool .bool) := by native_decide

def boolMarkerDef : WenDef where
  name           := "boolMarker"
  body           := boolMarkerBody
  bodyType       := .arr .bool .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def repeatOnceBody : Tm :=
  .abs "f" (.arr .hex .hex)
    (.abs "x" .hex (.app (.var "f") (.app (.var "f") (.var "x"))))

theorem repeatOnceBody_typed :
    typeCheck [] repeatOnceBody =
      some (.arr (.arr .hex .hex) (.arr .hex .hex)) := by native_decide

def repeatOnceDef : WenDef where
  name           := "repeatOnce"
  body           := repeatOnceBody
  bodyType       := .arr (.arr .hex .hex) (.arr .hex .hex)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def eachHBody : Tm :=
  .abs "dom" (.arr .hex .bool)
    (.abs "p" (.arr .hex .bool)
      (.app .forallH
        (.abs "x" .hex
          (.app
            (.app impBody (.app (.var "dom") (.var "x")))
            (.app (.var "p") (.var "x"))))))

theorem eachHBody_typed :
    typeCheck [] eachHBody =
      some (.arr (.arr .hex .bool) (.arr (.arr .hex .bool) .bool)) := by
  native_decide

def eachHDef : WenDef where
  name           := "eachH"
  body           := eachHBody
  bodyType       := .arr (.arr .hex .bool) (.arr (.arr .hex .bool) .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def hexPredApplyBody : Tm :=
  .abs "p" (.arr .hex .bool)
    (.abs "x" .hex (.app (.var "p") (.var "x")))

theorem hexPredApplyBody_typed :
    typeCheck [] hexPredApplyBody =
      some (.arr (.arr .hex .bool) (.arr .hex .bool)) := by
  native_decide

def hexPredApplyDef : WenDef where
  name           := "hexPredApply"
  body           := hexPredApplyBody
  bodyType       := .arr (.arr .hex .bool) (.arr .hex .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Hex pair/list carrier helpers -/

def pairHBody : Tm := .pairH

theorem pairHBody_typed :
    typeCheck [] pairHBody = some (.arr .hex (.arr .hex (.prod .hex .hex))) := by
  native_decide

def pairHDef : WenDef where
  name           := "pairH"
  body           := pairHBody
  bodyType       := .arr .hex (.arr .hex (.prod .hex .hex))
  validName      := by native_decide
  bodyTypechecks := by native_decide

def dupHBody : Tm := .dupH

theorem dupHBody_typed :
    typeCheck [] dupHBody = some (.arr .hex (.prod .hex .hex)) := by native_decide

def dupHDef : WenDef where
  name           := "dupH"
  body           := dupHBody
  bodyType       := .arr .hex (.prod .hex .hex)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def list1HBody : Tm := .list1H

theorem list1HBody_typed :
    typeCheck [] list1HBody = some (.arr .hex (.list .hex)) := by native_decide

def list1HDef : WenDef where
  name           := "list1H"
  body           := list1HBody
  bodyType       := .arr .hex (.list .hex)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def list2HBody : Tm := .list2H

theorem list2HBody_typed :
    typeCheck [] list2HBody = some (.arr .hex (.arr .hex (.list .hex))) := by
  native_decide

def list2HDef : WenDef where
  name           := "list2H"
  body           := list2HBody
  bodyType       := .arr .hex (.arr .hex (.list .hex))
  validName      := by native_decide
  bodyTypechecks := by native_decide

def list3HBody : Tm := .list3H

theorem list3HBody_typed :
    typeCheck [] list3HBody =
      some (.arr .hex (.arr .hex (.arr .hex (.list .hex)))) := by
  native_decide

def list3HDef : WenDef where
  name           := "list3H"
  body           := list3HBody
  bodyType       := .arr .hex (.arr .hex (.arr .hex (.list .hex)))
  validName      := by native_decide
  bodyTypechecks := by native_decide

def headHBody : Tm := .headH

theorem headHBody_typed :
    typeCheck [] headHBody = some (.arr (.list .hex) .hex) := by native_decide

def headHDef : WenDef where
  name           := "headH"
  body           := headHBody
  bodyType       := .arr (.list .hex) .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### R8 carrier helpers (post Phase F.2 migration; was `Cell192`) -/

def eqCellBody : Tm := .eqCell

theorem eqCellBody_typed :
    typeCheck [] eqCellBody = some (.arr .cell (.arr .cell .bool)) := by
  native_decide

def eqCellDef : WenDef where
  name           := "eqCell"
  body           := eqCellBody
  bodyType       := .arr .cell (.arr .cell .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def cuoCBody : Tm := .cuoC
def zongCBody : Tm := .zongC
def huCBody : Tm := .huC
def shiNextCBody : Tm := .shiNextC
def shiPrevCBody : Tm := .shiPrevC
def flip1CBody : Tm := .flip1C
def flip2CBody : Tm := .flip2C
def flip3CBody : Tm := .flip3C
def flip4CBody : Tm := .flip4C
def flip5CBody : Tm := .flip5C
def flip6CBody : Tm := .flip6C

theorem cuoCBody_typed : typeCheck [] cuoCBody = some (.arr .cell .cell) := by native_decide
theorem zongCBody_typed : typeCheck [] zongCBody = some (.arr .cell .cell) := by native_decide
theorem huCBody_typed : typeCheck [] huCBody = some (.arr .cell .cell) := by native_decide
theorem shiNextCBody_typed : typeCheck [] shiNextCBody = some (.arr .cell .cell) := by native_decide
theorem shiPrevCBody_typed : typeCheck [] shiPrevCBody = some (.arr .cell .cell) := by native_decide
theorem flip1CBody_typed : typeCheck [] flip1CBody = some (.arr .cell .cell) := by native_decide
theorem flip2CBody_typed : typeCheck [] flip2CBody = some (.arr .cell .cell) := by native_decide
theorem flip3CBody_typed : typeCheck [] flip3CBody = some (.arr .cell .cell) := by native_decide
theorem flip4CBody_typed : typeCheck [] flip4CBody = some (.arr .cell .cell) := by native_decide
theorem flip5CBody_typed : typeCheck [] flip5CBody = some (.arr .cell .cell) := by native_decide
theorem flip6CBody_typed : typeCheck [] flip6CBody = some (.arr .cell .cell) := by native_decide

def cellEndoDef (name : String) (body : Tm)
    (validName : isValidName name = true)
    (bodyTypechecks : typeCheck [] body = some (.arr .cell .cell)) : WenDef where
  name := name
  body := body
  bodyType := .arr .cell .cell
  validName := validName
  bodyTypechecks := by simpa using bodyTypechecks

def cuoCDef : WenDef := cellEndoDef "cuoC" cuoCBody (by native_decide) cuoCBody_typed
def zongCDef : WenDef := cellEndoDef "zongC" zongCBody (by native_decide) zongCBody_typed
def huCDef : WenDef := cellEndoDef "huC" huCBody (by native_decide) huCBody_typed
def shiNextCDef : WenDef := cellEndoDef "shiNextC" shiNextCBody (by native_decide) shiNextCBody_typed
def shiPrevCDef : WenDef := cellEndoDef "shiPrevC" shiPrevCBody (by native_decide) shiPrevCBody_typed
def flip1CDef : WenDef := cellEndoDef "flip1C" flip1CBody (by native_decide) flip1CBody_typed
def flip2CDef : WenDef := cellEndoDef "flip2C" flip2CBody (by native_decide) flip2CBody_typed
def flip3CDef : WenDef := cellEndoDef "flip3C" flip3CBody (by native_decide) flip3CBody_typed
def flip4CDef : WenDef := cellEndoDef "flip4C" flip4CBody (by native_decide) flip4CBody_typed
def flip5CDef : WenDef := cellEndoDef "flip5C" flip5CBody (by native_decide) flip5CBody_typed
def flip6CDef : WenDef := cellEndoDef "flip6C" flip6CBody (by native_decide) flip6CBody_typed

/-! ### Stdlib 总表 -/

/-- 当前 stdlib 中已合度且类型化之 wenyan-ops 定义。 -/
def all : List WenDef :=
  [ tuiDef, biDef, buDef, biModalDef, tongDef, fanDef, sunDef, yiBenefitDef
  , cuoDef, zongDef, huDef, fanReverseDef
  , hexIdDef, cuoZongDef, flip1Def, flip2Def, flip3Def, flip4Def, flip5Def, flip6Def
  , impDef, xorBDef, neqHexDef, existsHDef, noneHDef
  , uniqueHDef, exactly3HDef, majorityHDef, endoCompDef, hexApplyDef
  , boolMarkerDef, repeatOnceDef, eachHDef, hexPredApplyDef
  , pairHDef, dupHDef, list1HDef, list2HDef, list3HDef, headHDef
  , eqCellDef, cuoCDef, zongCDef, huCDef, shiNextCDef, shiPrevCDef
  , flip1CDef, flip2CDef, flip3CDef, flip4CDef, flip5CDef, flip6CDef ]

theorem all_length : all.length = 52 := by native_decide

theorem all_names :
    all.map WenDef.name =
      [ "tui", "bi", "bu", "biModal", "tong", "fan", "sun", "yiBenefit"
      , "complement", "reverse", "interlace", "fanReverse"
      , "hexId", "complementReverse", "flip1", "flip2", "flip3", "flip4", "flip5", "flip6"
      , "imp", "xorB", "neqHex", "existsH", "noneH"
      , "uniqueH", "exactly3H", "majorityH", "endoComp", "hexApply"
      , "boolMarker", "repeatOnce", "eachH", "hexPredApply"
      , "pairH", "dupH", "list1H", "list2H", "list3H", "headH"
      , "eqCell", "cuoC", "zongC", "huC", "shiNextC", "shiPrevC"
      , "flip1C", "flip2C", "flip3C", "flip4C", "flip5C", "flip6C" ] := by
  native_decide

theorem all_distinct_names : (all.map WenDef.name).Nodup := by native_decide

end Stdlib

/-! ## § 8  组合范例：wenyan-ops 之 64-fold 合取

  展示「凡 (λh. 同 h h)」 — i.e. ∀h:H, h = h — 是一个 well-typed Tm.
  其类型为 Bool. 此例展示 forallH 之高阶用法.
-/

/-- 凡 (λh. 同 h h)：恒等之 universal 闭合，类型 Bool。 -/
def selfEqAll : Tm :=
  .app .forallH (.abs "h" .hex (.app (.app .eqHex (.var "h")) (.var "h")))

theorem selfEqAll_typed : typeCheck [] selfEqAll = some .bool := by native_decide

/-- 反例：«凡 不» 类型不通（不 之类型 Bool→Bool ≠ Hex→Bool）。 -/
example : typeCheck [] (.app .forallH .notB) = none := by native_decide

end SSBX.Foundation.Wen.WenDef
