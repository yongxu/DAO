/-
# WenSurface.Syntax — resolved tokens to explicit surface AST

This layer keeps application markers and binder forms visible before
elaboration.  It replaces the older direct `List ResolvedAtom → Tm` path for
the default interpreter pipeline.
-/
import SSBX.Foundation.Wen.WenSurface.Semantics
import SSBX.Foundation.Wen.WenSurface.Reading

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Wen.WenDef
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings

/-! ## § 1 AST -/

inductive BinderKind where
  | lambda
  | forallHex
deriving DecidableEq, Repr

inductive SurfaceExpr where
  | atom (tok : ResolvedTok)
  | app (f x : SurfaceExpr)
  | seq (items : List SurfaceExpr)
  | marker (tok : ResolvedTok) (body : SurfaceExpr)
  | binder (kind : BinderKind) (name : String) (body : SurfaceExpr)
  | letBind (name : String) (value body : SurfaceExpr)
  | construction (name : String) (items : List SurfaceExpr)
  | grouped (openTok closeTok : ResolvedTok) (body : SurfaceExpr)
deriving Repr

inductive SurfaceAssoc where
  | left
  | right
  | nonassoc
deriving DecidableEq, Repr

inductive PatternPart where
  | lit (surface : String)
  | hole (name : String) (minPrec : Nat)
deriving DecidableEq, Repr

inductive SurfaceForm where
  | prefix (prec : Nat)
  | infix (prec : Nat) (assoc : SurfaceAssoc)
  | postfix (prec : Nat)
  | mixfix (pattern : List PatternPart) (prec : Nat)
deriving DecidableEq, Repr

structure SurfaceSyntaxEntry where
  id : OperatorId
  surface : String
  form : SurfaceForm
  note : String
deriving DecidableEq, Repr

inductive ParseErr where
  | empty
  | expectedExpression (col : Nat)
  | fuelExhausted
  | unmatchedOpenBracket (surface : String) (col : Nat)
  | unmatchedCloseBracket (surface : String) (col : Nat)
  | expectedCloseBracket (openSurface expected : String) (openCol col : Nat)
  | expectedVariable (surface : String) (col : Nat)
  | unexpectedApplicationMarker (surface : String) (col : Nat)
  | unpromotedHexagramGap (surface : String) (col : Nat)
  | nonassocInfix (surface : String) (col : Nat)
  | typeMismatch (expected actual : Ty) (surface : String) (col : Nat)
  | leftoverAtoms (count : Nat) (firstSurface : String) (firstCol : Nat)
deriving DecidableEq, Repr

/-! ## § 2 Helpers -/

def ResolvedTok.col (t : ResolvedTok) : Nat := t.tok.startCol
def ResolvedTok.surface (t : ResolvedTok) : String := t.tok.surface

def ResolvedAtom.operatorId? : ResolvedAtom → Option OperatorId
  | .catalogueOp r => r.operator?
  | .hexOrOp _ r => r.operator?
  | _ => none

/-- True iff this atom is a B-2/B-3/B-6 builtin Tm primitive. -/
def ResolvedAtom.isBuiltinTm : ResolvedAtom → Bool
  | .builtinTm _ _ => true
  | _              => false

/-- Extract `(body, arity)` for a `.builtinTm` atom (none otherwise). -/
def ResolvedAtom.builtinTm? : ResolvedAtom → Option (Tm × Nat)
  | .builtinTm body arity => some (body, arity)
  | _                     => none

def isApplicationOperator : OperatorId → Bool
  | .S_1 => true
  | _ => false

def isApplicationMarkerTok (t : ResolvedTok) : Bool :=
  match t.atom with
  | .appMarker => true
  | .catalogueOp r =>
      match r.operator? with
      | some id => isApplicationOperator id
      | none => false
  | _ => false

def isRelationInfixOperator : OperatorId → Bool
  | .I_1 => true
  | .R_8 => true
  | _ => false

def SurfaceForm.precedence : SurfaceForm → Nat
  | .prefix prec => prec
  | .infix prec _ => prec
  | .postfix prec => prec
  | .mixfix _ prec => prec

def SurfaceForm.fixityLabel : SurfaceForm → String
  | .prefix _ => "prefix"
  | .infix _ _ => "infix"
  | .postfix _ => "postfix"
  | .mixfix _ _ => "mixfix"

def SurfaceAssoc.label : SurfaceAssoc → String
  | .left => "left"
  | .right => "right"
  | .nonassoc => "nonassoc"

def prefixSurfaceSyntaxEntriesForOperator (id : OperatorId) : List SurfaceSyntaxEntry :=
  (operatorForms id).map (fun sense =>
    { id := id
    , surface := sense.glyph
    , form := .prefix 80
    , note := "registered prefix surface form from operatorForms" })

def allPrefixSurfaceSyntaxEntriesFrom : List OperatorId → List SurfaceSyntaxEntry
  | [] => []
  | id :: rest =>
      prefixSurfaceSyntaxEntriesForOperator id ++ allPrefixSurfaceSyntaxEntriesFrom rest

def allPrefixSurfaceSyntaxEntries : List SurfaceSyntaxEntry :=
  allPrefixSurfaceSyntaxEntriesFrom allOperatorIds

def relationInfixSurfaceSyntaxEntries : List SurfaceSyntaxEntry :=
  [ { id := .I_1
    , surface := "同"
    , form := .infix 40 .nonassoc
    , note := "relation equality infix; parser currently desugars to curried application" }
  , { id := .R_8
    , surface := "比"
    , form := .infix 40 .nonassoc
    , note := "relation comparison infix; expression-start 比 remains hex/operator disambiguated" }
  ]

/--
Postfix surface entries.  A postfix entry fires inside
[`parsePostfixApplications`](#parsePostfixApplications) **after** a complete
left-side expression `acc` has been parsed and **before** any infix dispatch.
Postfix consumes one token and re-shapes `acc` into `(opTok) acc`.

Currently demos `S_14 也` (predication/finality particle) with precedence `10`
so that postfix binds tightly to the immediately preceding expression.  The
existing `S_14` prefix entry from `operatorForms` is preserved unchanged, so
`也 乾` still parses as the prefix application; `推 一 也` now elaborates the
trailing `也` as a postfix marker over `推 一`.
-/
def postfixSurfaceSyntaxEntries : List SurfaceSyntaxEntry :=
  [ { id := .S_14
    , surface := "也"
    , form := .postfix 10
    , note := "predication/finality particle; postfix demo (parser dispatches via postfixSyntaxEntry?)" }
  , { id := .S_21
    , surface := "乎"
    , form := .postfix 10
    , note := "interrogative final particle (modal axis: M_5 可); postfix boolMarker on Bool" }
  , { id := .S_22
    , surface := "矣"
    , form := .postfix 10
    , note := "perfective final particle (与 S_18 已 关联); postfix boolMarker on Bool" }
  , { id := .S_23
    , surface := "哉"
    , form := .postfix 10
    , note := "exclamatory final particle (modal axis: M_1 必); postfix boolMarker on Bool" }
  , { id := .S_24
    , surface := "兮"
    , form := .postfix 10
    , note := "lyrical final particle (aesthetic/韵律 marker); postfix boolMarker on Bool" }
  ]

def surfaceSyntaxEntries : List SurfaceSyntaxEntry :=
  relationInfixSurfaceSyntaxEntries ++ postfixSurfaceSyntaxEntries ++ allPrefixSurfaceSyntaxEntries

def surfaceSyntaxEntriesForOperator (id : OperatorId) : List SurfaceSyntaxEntry :=
  surfaceSyntaxEntries.filter (fun entry => decide (entry.id = id))

theorem relationInfixSurfaceSyntaxEntries_length :
    relationInfixSurfaceSyntaxEntries.length = 2 := by native_decide

theorem postfixSurfaceSyntaxEntries_length :
    postfixSurfaceSyntaxEntries.length = 5 := by native_decide

theorem prefixSurfaceSyntaxEntries_cover_all_operators :
    allOperatorIds.all (fun id => !(prefixSurfaceSyntaxEntriesForOperator id).isEmpty) = true := by
  native_decide

theorem surfaceSyntaxEntries_relation_examples :
    (surfaceSyntaxEntriesForOperator .I_1).length = 2
      ∧ (surfaceSyntaxEntriesForOperator .R_8).length = 2 := by
  native_decide

/-- `S_14 也` now has 1 prefix entry (from `operatorForms`) + 1 postfix entry. -/
theorem surfaceSyntaxEntries_S_14_has_postfix :
    (surfaceSyntaxEntriesForOperator .S_14).length = 2 := by native_decide

def relationInfixTok? (t : ResolvedTok) : Option ResolvedTok :=
  match t.atom with
  | .catalogueOp r =>
      match r.operator? with
      | some id => if isRelationInfixOperator id then some t else none
      | none => none
  | .hexOrOp _ r =>
      match r.operator? with
      | some id =>
          if isRelationInfixOperator id then some { t with atom := .catalogueOp r } else none
      | none => none
  | _ => none

/--
Postfix surface-entry lookup for a `ResolvedTok`.  Returns the operator id
and its postfix precedence, plus a `ResolvedTok` normalised to `.catalogueOp`
so downstream `SurfaceExpr.atom` construction sees a clean dispatch atom.

Resolution walks `postfixSurfaceSyntaxEntries`; the parser consults this
**before** infix dispatch (postfix is 1-token, infix is 2-token).
-/
def postfixSyntaxEntry? (t : ResolvedTok) : Option (ResolvedTok × Nat) :=
  let lookup (id : OperatorId) (tok : ResolvedTok) : Option (ResolvedTok × Nat) :=
    match postfixSurfaceSyntaxEntries.find? (fun entry => decide (entry.id = id)) with
    | some entry =>
        match entry.form with
        | .postfix prec => some (tok, prec)
        | _ => none
    | none => none
  match t.atom with
  | .catalogueOp r =>
      match r.operator? with
      | some id => lookup id t
      | none => none
  | .hexOrOp _ r =>
      match r.operator? with
      | some id => lookup id { t with atom := .catalogueOp r }
      | none => none
  | _ => none

def isCloseBracketTok (t : ResolvedTok) : Bool :=
  match t.atom with
  | .closeBracket => true
  | _ => false

/-- wen-2.0 ⑦: `者` syntax marker test.  Distinguishing this lets the
    postfix-dispatch branch of `parsePostfixApplications` fire the
    nominalizer rule when `者` follows a complete predicate expression. -/
def isZheSyntaxTok (t : ResolvedTok) : Bool :=
  match t.atom with
  | .syntax .zhe => true
  | _ => false

/-- wen-2.0 ⑦: `属` (member-of) syntax marker test.  Used by the
    postfix-application dispatch to fold `X 属 S` into a `.construction "属"
    [X, S]`, which the elaborator lowers to `Tm.memberOf`. -/
def isShuSyntaxTok (t : ResolvedTok) : Bool :=
  match t.atom with
  | .syntax .shu => true
  | _ => false

def exactOperatorType? (id : OperatorId) : Option Ty :=
  match theoremBackedSemanticsFor? id with
  | some sem => typeCheck [] sem.body
  | none => none

def Ty.argTypesFor : Ty → Nat → Option (List Ty)
  | _, 0 => some []
  | .arr a b, n+1 =>
      match Ty.argTypesFor b n with
      | some args => some (a :: args)
      | none => none
  | _, _+1 => none

def Ty.argsNeededToReachFuel (target : Ty) : Nat → Ty → Option Nat
  | 0, _ => none
  | fuel+1, ty =>
      if ty = target then
        some 0
      else
        match ty with
        | .arr _ b =>
            match Ty.argsNeededToReachFuel target fuel b with
            | some n => some (n + 1)
            | none => none
        | _ => none

def Ty.argsNeededToReach (target ty : Ty) : Option Nat :=
  Ty.argsNeededToReachFuel target 32 ty

def exactTokWithType? (t : ResolvedTok) : Option (ResolvedTok × OperatorId × Ty) :=
  match t.atom with
  | .catalogueOp r =>
      match r.operator? with
      | some id =>
          match exactOperatorType? id with
          | some ty => some (t, id, ty)
          | none => none
      | none => none
  | .hexOrOp _ r =>
      match r.operator? with
      | some id =>
          match exactOperatorType? id with
          | some ty => some ({ t with atom := .catalogueOp r }, id, ty)
          | none => none
      | none => none
  | _ => none

/-- Finite binder domains inferred when the surface grammar has no explicit
    annotation.  Hex stays first to preserve legacy `者 甲 甲`. -/
def binderDomainCandidates : List Ty :=
  [ .hex
  , .bool
  , .arr .hex .hex
  , .arr .hex .bool
  , .arr .bool .bool
  , .arr .bool .hex ]

def binderDomainCandidatesWith (primary? : Option Ty) : List Ty :=
  match primary? with
  | none => binderDomainCandidates
  | some primary =>
      primary :: binderDomainCandidates.filter (fun ty => decide (ty ≠ primary))

def atomSurfaceTypeWithCtx? (ctx : Ctx) : ResolvedAtom → Option Ty
  | .hexConst _ => some .hex
  | .boolConst _ => some .bool
  | .varName name => ctx.lookup name
  | .catalogueOp r =>
      match r.operator? with
      | some id => exactOperatorType? id
      | none => none
  | .hexOrOp _ _ => some .hex
  | .builtinTm body _ => typeCheck [] body
  | _ => none

def atomSurfaceType? (atom : ResolvedAtom) : Option Ty :=
  atomSurfaceTypeWithCtx? [] atom

mutual
  def surfaceExprTypeWithCtx? : Ctx → SurfaceExpr → Option Ty
    | ctx, .atom tok => atomSurfaceTypeWithCtx? ctx tok.atom
    | ctx, .app f x =>
        match surfaceExprTypeWithCtx? ctx f, surfaceExprTypeWithCtx? ctx x with
        | some (.arr a b), some a' => if a = a' then some b else none
        | _, _ => none
    | ctx, .seq [x] => surfaceExprTypeWithCtx? ctx x
    | _, .seq _ => none
    | ctx, .marker _ body => surfaceExprTypeWithCtx? ctx body
    | ctx, .binder .lambda name body =>
        lambdaTypeWithCtx? ctx name body binderDomainCandidates
    | ctx, .binder .forallHex name body =>
        match surfaceExprTypeWithCtx? ((name, .hex) :: ctx) body with
        | some .bool => some .bool
        | _ => none
    | ctx, .letBind name value body =>
        match surfaceExprTypeWithCtx? ctx value with
        | some ty => surfaceExprTypeWithCtx? ((name, ty) :: ctx) body
        | none => none
    | ctx, .construction "之又" [inner] => surfaceExprTypeWithCtx? ctx inner
    -- wen-2.0 ⑪: 执 X — the inner expression must surface-type to `.quoted`
    -- (typically a 引语括号 group); the construction itself is `.hex` (the
    -- kernel `typeCheck` returns `.hex` for `Tm.unquote q` whenever
    -- `q : .quoted`).
    | ctx, .construction "执" [inner] =>
        match surfaceExprTypeWithCtx? ctx inner with
        | some .quoted => some .hex
        | _ => none
    -- wen-2.0 ⑦: 者 nominalizer — inner must be `arr T .bool`; result `.set T`.
    | ctx, .construction "者" [inner] =>
        match surfaceExprTypeWithCtx? ctx inner with
        | some (.arr t .bool) => some (.set t)
        | _ => none
    -- wen-2.0 ⑦: `X 属 S` — S : .set T, X : T, result .bool.
    | ctx, .construction "属" [x, s] =>
        match surfaceExprTypeWithCtx? ctx s with
        | some (.set elem) =>
            match surfaceExprTypeWithCtx? ctx x with
            | some tx => if tx = elem then some .bool else none
            | none => none
        | _ => none
    | _, .construction _ _ => none
    | ctx, .grouped openTok _ body =>
        -- wen-2.0 ⑩: quote brackets 「」/『』 give the surface group type `.quoted`,
        -- regardless of body type — matches `Tm.quote` elaboration.  Value
        -- grouping `（…）`/`(…)` is unchanged (delegates to body).
        if isQuoteOpenBracketSurface openTok.surface then some .quoted
        else surfaceExprTypeWithCtx? ctx body

  def lambdaTypeWithCtx? : Ctx → String → SurfaceExpr → List Ty → Option Ty
    | _, _, _, [] => none
    | ctx, name, body, dom :: rest =>
        match surfaceExprTypeWithCtx? ((name, dom) :: ctx) body with
        | some cod => some (.arr dom cod)
        | none => lambdaTypeWithCtx? ctx name body rest
end

def surfaceExprType? (expr : SurfaceExpr) : Option Ty :=
  surfaceExprTypeWithCtx? [] expr

def surfaceExprMatchesTypeWithCtx (ctx : Ctx) (expected : Ty) (expr : SurfaceExpr) : Bool :=
  match surfaceExprTypeWithCtx? ctx expr with
  | some actual => actual = expected
  | none => false

def typedExprMatches (expected : Ty) (expr : SurfaceExpr) : Bool :=
  surfaceExprMatchesTypeWithCtx [] expected expr

def expectedTypeErrWithCtx (ctx : Ctx) (expected : Ty) (head : ResolvedTok)
    (expr : SurfaceExpr) : ParseErr :=
  match surfaceExprTypeWithCtx? ctx expr with
  | some actual => .typeMismatch expected actual head.surface head.col
  | none =>
      match exactTokWithType? head with
      | some (_, _, actual) => .typeMismatch expected actual head.surface head.col
      | none => .empty

def expectedTypeErr (expected : Ty) (head : ResolvedTok) (expr : SurfaceExpr) : ParseErr :=
  expectedTypeErrWithCtx [] expected head expr

def lambdaParts? : SurfaceExpr → Option (String × SurfaceExpr)
  | .binder .lambda name body => some (name, body)
  | .grouped _ _ body => lambdaParts? body
  | _ => none

def exactArgsForArity? (ty : Ty) (arity : Nat) : Option (List Ty) :=
  Ty.argTypesFor ty arity

def exactArgsToReach? (target ty : Ty) (arity : Nat) : Option (List Ty) :=
  match Ty.argsNeededToReach target ty with
  | some n =>
      if decide (n <= arity) then Ty.argTypesFor ty n else none
  | none => none

def exactNormalStart? (head : ResolvedTok) : Option (ResolvedTok × List Ty) :=
  match exactTokWithType? head with
  | some (tok, id, ty) =>
      match exactArgsForArity? ty (parseArityFor id) with
      | some args => some (tok, args)
      | none => none
  | none => none

def exactExpectedStart? (expected : Ty) (head : ResolvedTok)
    : Option (ResolvedTok × List Ty) :=
  match exactTokWithType? head with
  | some (tok, id, ty) =>
      match exactArgsToReach? expected ty (parseArityFor id) with
      | some args => some (tok, args)
      | none => none
  | none => none

def expectedFunctionCue? : Ty → Option ContextCue
  | .arr .hex .hex => some .expectedObject
  | .arr .bool .bool => some .expectedProp
  | _ => none

def readingHasExactExpectedType (expected : Ty) (r : OperatorReading) : Bool :=
  match r.operator? with
  | some id =>
      match exactOperatorType? id with
      | some ty => decide (ty = expected)
      | none => false
  | none => false

def readingMatchesExpectedFunction (expected : Ty) (r : OperatorReading) : Bool :=
  let cueMatches :=
    match expectedFunctionCue? expected with
    | some cue => readingSatisfiesCue r cue
    | none => true
  readingHasExactExpectedType expected r && cueMatches

def expectedFunctionResolvedTok? (expected : Ty) (head : ResolvedTok)
    : Option ResolvedTok :=
  match head.atom with
  | .ambiguousOp candidates =>
      match candidates.filter (readingMatchesExpectedFunction expected) with
      | [r] => some { head with atom := .catalogueOp r }
      | _ => none
  | _ => none

def asVarName? (t : ResolvedTok) : Option String :=
  match t.atom with
  | .varName n => some n
  | _ => none

/-- wen-2.0 ⑧ helper: split `toks` at the first **terminal** `者` —— i.e., a
    `.syntax .zhe` token that is **not** followed by a varName (such a `者`
    would otherwise be the head of a lambda binder `者 甲 BODY`).  Returns
    `some (before, after)` where `before` is the prefix tokens consumed up to
    (but not including) the terminal `者`, and `after` is everything after
    the `者`.  Returns `none` if no terminal `者` is found.

    Used by `所 PRED 者` to isolate `PRED` from trailing context: the `者`
    here is **not** a binder (it has no var name afterward), it merely closes
    the relativization. -/
def splitAtTerminalZhe : List ResolvedTok → Option (List ResolvedTok × List ResolvedTok)
  | [] => none
  | t :: rest =>
      match t.atom with
      | .syntax .zhe =>
          -- Check if this `者` is followed by a varName (= lambda binder).
          match rest with
          | v :: _ =>
              match asVarName? v with
              | some _ =>
                  -- Lambda-binder 者: skip past it (consume `者` + var as part of prefix).
                  match splitAtTerminalZhe rest with
                  | some (before, after) => some (t :: before, after)
                  | none => none
              | none =>
                  -- Terminal 者: split here.
                  some ([], rest)
          | [] =>
              -- 者 at end of stream with no var → terminal.
              some ([], [])
      | _ =>
          match splitAtTerminalZhe rest with
          | some (before, after) => some (t :: before, after)
          | none => none

def expectedVariableErr (head : ResolvedTok) : ParseErr :=
  .expectedVariable head.surface head.col

def expectedCloseBracketErr (openTok : ResolvedTok) (rest : List ResolvedTok) : ParseErr :=
  let expected := (matchingCloseBracket? openTok.surface).getD "）"
  match rest with
  | closeTok :: _ => .expectedCloseBracket openTok.surface expected openTok.col closeTok.col
  | [] => .unmatchedOpenBracket openTok.surface openTok.col

/-! ## § 3 Prefix parser -/

mutual
  def parseSurfaceExprAux : Ctx → Bool → Nat → Nat → List ResolvedTok →
      Except ParseErr (SurfaceExpr × List ResolvedTok)
    | _, _, 0, _, _ => .error .fuelExhausted
    | _, _, _+1, _, [] => .error .empty
    | ctx, allowInfix, n+1, reserve, head :: rest =>
      match head.atom with
      | .syntax .zhe =>
          match rest with
          | v :: rest' =>
              match asVarName? v with
              | some name =>
                  let tryBody (dom : Ty) :=
                    parseSurfaceExprAux ((name, dom) :: ctx) allowInfix n reserve rest'
                  match tryBody .hex with
                  | .ok (body, rest'') =>
                      parsePostfixApplications ctx allowInfix n reserve (.binder .lambda name body) rest''
                  | .error _ =>
                      match tryBody .bool with
                      | .ok (body, rest'') =>
                          parsePostfixApplications ctx allowInfix n reserve (.binder .lambda name body) rest''
                      | .error _ =>
                          match tryBody (.arr .hex .hex) with
                          | .ok (body, rest'') =>
                              parsePostfixApplications ctx allowInfix n reserve (.binder .lambda name body) rest''
                          | .error _ =>
                              match tryBody (.arr .hex .bool) with
                              | .ok (body, rest'') =>
                                  parsePostfixApplications ctx allowInfix n reserve (.binder .lambda name body) rest''
                              | .error _ =>
                                  match tryBody (.arr .bool .bool) with
                                  | .ok (body, rest'') =>
                                      parsePostfixApplications ctx allowInfix n reserve (.binder .lambda name body) rest''
                                  | .error _ =>
                                      match tryBody (.arr .bool .hex) with
                                      | .ok (body, rest'') =>
                                          parsePostfixApplications ctx allowInfix n reserve (.binder .lambda name body) rest''
                                      | .error e => .error e
              | none => .error (expectedVariableErr head)
          | [] => .error (expectedVariableErr head)
      | .syntax .ling =>
          match rest with
          | v :: rest' =>
              match asVarName? v with
              | some name =>
                  match parseSurfaceExprAux ctx false n 1 rest' with
                  | .error e => .error e
                  | .ok (value, rest'') =>
                      let bodyCtx :=
                        match surfaceExprTypeWithCtx? ctx value with
                        | some ty => (name, ty) :: ctx
                        | none => (name, .hex) :: ctx
                      match parseSurfaceExprAux bodyCtx allowInfix n reserve rest'' with
                      | .ok (body, rest''') =>
                          parsePostfixApplications ctx allowInfix n reserve (.letBind name value body) rest'''
                      | .error e => .error e
              | none => .error (expectedVariableErr head)
          | [] => .error (expectedVariableErr head)
      | .syntax .zhi =>
          -- wen-2.0 ⑪ `执 X`: consume one SurfaceExpr argument as the quoted
          -- payload.  Reserve 1 so trailing tokens aren't starved.  The
          -- elaborator turns the resulting `.construction "执" [body]` into
          -- `Tm.unquote body'`.  Body must elaborate to a `.quoted` (typically
          -- a 引语括号-grouped expression `「Y」`).
          match rest with
          | [] => .error (.expectedExpression (head.col + head.surface.toList.length))
          | _ =>
              match parseSurfaceExprAux ctx false n reserve rest with
              | .ok (body, rest') =>
                  parsePostfixApplications ctx allowInfix n reserve
                    (.construction "执" [body]) rest'
              | .error e => .error e
      | .syntax .shu =>
          -- wen-2.0 ⑦ `属` 是 infix-only; 出现在 expression start 是语法错误。
          .error (.unexpectedApplicationMarker head.surface head.col)
      | .syntax .suo =>
          -- wen-2.0 ⑧ `所 PRED 者`: object relativization.  Split `rest` at
          -- the first **terminal** `者` (i.e., a `者` not followed by a
          -- varName, so it's not a nested lambda binder).  Parse the prefix
          -- as `pred`, then desugar to `λ甲. pred 甲` — a Hex-input lambda
          -- whose body applies the predicate to an implicit `甲` variable.
          -- The legacy `S_16` (所: Hex→Hex identity) catalogue reading is
          -- shadowed: `所` is no longer reachable as an operator surface.
          match splitAtTerminalZhe rest with
          | none =>
              .error (.expectedExpression (head.col + head.surface.toList.length))
          | some (predToks, restAfterZhe) =>
              match predToks with
              | [] => .error (.expectedExpression (head.col + head.surface.toList.length))
              | _ =>
                  -- Parse `predToks` as a complete sub-expression.  Use fuel
                  -- `n` and reserve `0` (the predToks list is self-contained).
                  match parseSurfaceExprAux ctx false n 0 predToks with
                  | .error e => .error e
                  | .ok (pred, leftover) =>
                      match leftover with
                      | [] =>
                          -- Synthesize an implicit binder `甲` and body
                          -- `pred 甲`.  The varName tok is dummy (col=0);
                          -- only `name` is consulted by the elaborator.
                          let varTok : ResolvedTok :=
                            ⟨⟨"甲", 0, 1, false⟩, .varName "甲"⟩
                          let varExpr : SurfaceExpr := .atom varTok
                          let body : SurfaceExpr := .app pred varExpr
                          parsePostfixApplications ctx allowInfix n reserve
                            (.binder .lambda "甲" body) restAfterZhe
                      | first :: _ =>
                          -- Inner `pred` did not consume all predToks —
                          -- the surplus tokens are between `所` and `者`
                          -- but couldn't fold into the predicate.
                          .error (.leftoverAtoms leftover.length first.surface first.col)
      | .syntax .zhiSuoYi =>
          -- wen-2.0 ⑧: `之所以` at expression-start has no subject (acc).
          -- This is the bare form `之所以 X` which is grammatically
          -- ill-formed (the reason-extractor needs a preceding subject).
          -- Surface this as a parse error so the user fixes it.
          .error (.expectedExpression head.col)
      | .appMarker =>
          match rest with
          | [] => .error (.expectedExpression (head.col + head.surface.toList.length))
          | _ =>
              match parseSurfaceExprAux ctx allowInfix n reserve rest with
              | .ok (body, rest') => parsePostfixApplications ctx allowInfix n reserve (.marker head body) rest'
              | .error e => .error e
      | .iterate =>
          match rest with
          | [] => .error (.expectedExpression (head.col + head.surface.toList.length))
          | _ =>
              match parseSurfaceExprAux ctx allowInfix n reserve rest with
              | .ok (body, rest') =>
                  parsePostfixApplications ctx allowInfix n reserve (.construction "之又" [body]) rest'
              | .error e => .error e
      | .openBracket =>
          match rest with
          | closeTok :: _ =>
              if isCloseBracketTok closeTok then
                .error (.expectedExpression closeTok.col)
              else
                match parseSurfaceExprAux ctx allowInfix n reserve rest with
                | .error e => .error e
                | .ok (body, closeTok :: rest') =>
                    match closeTok.atom with
                    | .closeBracket =>
                        match matchingCloseBracket? head.surface with
                        | some expected =>
                            if closeTok.surface = expected then
                              parsePostfixApplications ctx allowInfix n reserve (.grouped head closeTok body) rest'
                            else
                              .error (.expectedCloseBracket head.surface expected head.col closeTok.col)
                        | none => .error (.unmatchedOpenBracket head.surface head.col)
                    | _ => .error (expectedCloseBracketErr head (closeTok :: rest'))
                | .ok (_, []) => .error (expectedCloseBracketErr head [])
          | [] => .error (expectedCloseBracketErr head [])
      | .closeBracket =>
          .error (.unmatchedCloseBracket head.surface head.col)
      | .hexOrOp h r =>
          match r.operator? with
          | none => parsePostfixApplications ctx allowInfix n reserve (.atom { head with atom := .hexConst h }) rest
          | some id =>
              let hexFallback :=
                parsePostfixApplications ctx allowInfix n reserve (.atom { head with atom := .hexConst h }) rest
              if isApplicationOperator id then
                hexFallback
              else
                match exactNormalStart? head with
                | some (tok, args) =>
                    match collectExactArgsPartial ctx allowInfix n reserve (.atom tok) args rest with
                    | .ok (expr, rest') =>
                        if rest'.length < rest.length then
                          parsePostfixApplications ctx allowInfix n reserve expr rest'
                        else
                          hexFallback
                    | .error _ => hexFallback
                | none =>
                    match collectSurfaceArgs ctx allowInfix n (.atom { head with atom := .catalogueOp r }) (parseArityFor id) rest with
                    | .ok (expr, rest') =>
                        if decide (reserve <= rest'.length) then
                          parsePostfixApplications ctx allowInfix n reserve expr rest'
                        else hexFallback
                    | .error _ => hexFallback
      | .catalogueOp r =>
          match r.operator? with
          | none => .error (.unexpectedApplicationMarker head.surface head.col)
          | some id =>
              if isApplicationOperator id then
                match parseSurfaceExprAux ctx allowInfix n reserve rest with
                | .ok (body, rest') => parsePostfixApplications ctx allowInfix n reserve (.marker head body) rest'
                | .error e => .error e
              else if id = .Q_1 then
                match rest with
                | v :: rest' =>
                    match asVarName? v with
                    | some name =>
                        match parseSurfaceExprAux ((name, .hex) :: ctx) allowInfix n reserve rest' with
                        | .ok (body, rest'') =>
                            parsePostfixApplications ctx allowInfix n reserve (.binder .forallHex name body) rest''
                        | .error e => .error e
                      | none =>
                        match exactNormalStart? head with
                        | some (tok, args) =>
                            match collectExactArgsPartial ctx allowInfix n reserve (.atom tok) args rest with
                            | .ok (expr, rest') => parsePostfixApplications ctx allowInfix n reserve expr rest'
                            | .error e => .error e
                        | none =>
                            match collectSurfaceArgs ctx allowInfix n (.atom head) (parseArityFor id) rest with
                            | .ok (expr, rest') => parsePostfixApplications ctx allowInfix n reserve expr rest'
                            | .error e => .error e
                  | [] =>
                      match exactNormalStart? head with
                      | some (tok, args) =>
                          match collectExactArgsPartial ctx allowInfix n reserve (.atom tok) args rest with
                          | .ok (expr, rest') => parsePostfixApplications ctx allowInfix n reserve expr rest'
                          | .error e => .error e
                      | none =>
                          match collectSurfaceArgs ctx allowInfix n (.atom head) (parseArityFor id) rest with
                          | .ok (expr, rest') => parsePostfixApplications ctx allowInfix n reserve expr rest'
                          | .error e => .error e
                else
                  match exactNormalStart? head with
                  | some (tok, args) =>
                      match collectExactArgsPartial ctx allowInfix n reserve (.atom tok) args rest with
                      | .ok (expr, rest') => parsePostfixApplications ctx allowInfix n reserve expr rest'
                      | .error e => .error e
                  | none =>
                      match collectSurfaceArgs ctx allowInfix n (.atom head) (parseArityFor id) rest with
                      | .ok (expr, rest') => parsePostfixApplications ctx allowInfix n reserve expr rest'
                      | .error e => .error e
      | .ambiguousOp _ => .error .empty
      | .builtinTm _ arity =>
          -- B-2/B-3/B-6: builtin Tm primitive head.  Same dispatch shape as a
          -- catalogue prefix op: collect `arity` sub-expressions as
          -- left-associative args (e.g. `加 一 一` → `((加 一) 一)`), then
          -- continue with postfix applications.
          match collectSurfaceArgs ctx allowInfix n (.atom head) arity rest with
          | .ok (expr, rest') => parsePostfixApplications ctx allowInfix n reserve expr rest'
          | .error e => .error e
      | .hexConst _ => parsePostfixApplications ctx allowInfix n reserve (.atom head) rest
      | .boolConst _ => parsePostfixApplications ctx allowInfix n reserve (.atom head) rest
      | .varName _ => parsePostfixApplications ctx allowInfix n reserve (.atom head) rest

    def collectSurfaceArgs : Ctx → Bool → Nat → SurfaceExpr → Nat → List ResolvedTok →
        Except ParseErr (SurfaceExpr × List ResolvedTok)
    | _, _, _, acc, 0, rest => .ok (acc, rest)
    | _, _, 0, _, _+1, _ => .error .fuelExhausted
    | ctx, allowInfix, n+1, acc, k+1, rest =>
          match parseSurfaceExprAux ctx false n k rest with
          | .error e => .error e
          | .ok (arg, rest') => collectSurfaceArgs ctx allowInfix n (.app acc arg) k rest'

    def collectExactArgsPartial : Ctx → Bool → Nat → Nat → SurfaceExpr → List Ty → List ResolvedTok →
        Except ParseErr (SurfaceExpr × List ResolvedTok)
      | _, _, _, _, acc, [], rest => .ok (acc, rest)
      | _, _, 0, _, _, _ :: _, _ => .error .fuelExhausted
      | ctx, allowInfix, n+1, reserve, acc, expected :: expectedRest, rest =>
          match rest with
          | head :: _ =>
              if isCloseBracketTok head then
                .ok (acc, rest)
              else if decide (rest.length <= reserve) then
                .ok (acc, rest)
              else
                let argReserve := reserve + expectedRest.length
                let parsed :=
                  match expected with
                  | .arr _ _ => parseSurfaceExprExpected ctx allowInfix n argReserve expected rest
                  | _ => parseSurfaceExprAux ctx false n argReserve rest
                match parsed with
                | .error e => .error e
                | .ok (arg, rest') =>
                    collectExactArgsPartial ctx allowInfix n reserve (.app acc arg) expectedRest rest'
          | [] => .ok (acc, [])

    def collectExactArgsExact : Ctx → Bool → Nat → Nat → SurfaceExpr → List Ty → List ResolvedTok →
        Except ParseErr (SurfaceExpr × List ResolvedTok)
      | _, _, _, _, acc, [], rest => .ok (acc, rest)
      | _, _, 0, _, _, _ :: _, _ => .error .fuelExhausted
      | _, _, _+1, _, _, _ :: _, [] => .error .empty
      | ctx, allowInfix, n+1, reserve, acc, expected :: expectedRest, rest =>
          if decide (rest.length <= reserve) then
            .error .empty
          else
            let argReserve := reserve + expectedRest.length
            let parsed :=
              match expected with
              | .arr _ _ => parseSurfaceExprExpected ctx allowInfix n argReserve expected rest
              | _ => parseSurfaceExprAux ctx false n argReserve rest
            match parsed with
            | .error e => .error e
            | .ok (arg, rest') =>
                collectExactArgsExact ctx allowInfix n reserve (.app acc arg) expectedRest rest'

    def parseSurfaceExprExpected : Ctx → Bool → Nat → Nat → Ty → List ResolvedTok →
        Except ParseErr (SurfaceExpr × List ResolvedTok)
      | _, _, 0, _, _, _ => .error .fuelExhausted
      | _, _, _+1, _, _, [] => .error .empty
      | ctx, allowInfix, n+1, reserve, expected, head :: rest =>
          let expectedHead := (expectedFunctionResolvedTok? expected head).getD head
          match expected, expectedHead.atom with
          | .arr dom cod, .syntax .zhe =>
              match rest with
              | v :: rest' =>
                  match asVarName? v with
                  | some name =>
                      match parseSurfaceExprExpected ((name, dom) :: ctx) allowInfix n reserve cod rest' with
                      | .ok (body, rest'') => .ok (.binder .lambda name body, rest'')
                      | .error e => .error e
                  | none => .error (expectedVariableErr head)
              | [] => .error (expectedVariableErr head)
          | _, _ =>
          match exactExpectedStart? expected expectedHead with
          | some (tok, args) =>
              match collectExactArgsExact ctx allowInfix n reserve (.atom tok) args rest with
              | .ok result => .ok result
              | .error _ =>
                  match parseSurfaceExprAux ctx allowInfix n reserve (expectedHead :: rest) with
                  | .ok result =>
                      if surfaceExprMatchesTypeWithCtx ctx expected result.1 then
                        .ok result
                      else
                        .error (expectedTypeErrWithCtx ctx expected expectedHead result.1)
                  | .error e => .error e
          | none =>
              match parseSurfaceExprAux ctx allowInfix n reserve (expectedHead :: rest) with
              | .ok result =>
                  if surfaceExprMatchesTypeWithCtx ctx expected result.1 then
                    .ok result
                  else
                    .error (expectedTypeErrWithCtx ctx expected expectedHead result.1)
              | .error e => .error e

  def parsePostfixApplications : Ctx → Bool → Nat → Nat → SurfaceExpr → List ResolvedTok →
      Except ParseErr (SurfaceExpr × List ResolvedTok)
    | _, _, 0, _, _, _ => .error .fuelExhausted
    | _, _, _+1, _, acc, [] => .ok (acc, [])
    | ctx, allowInfix, n+1, reserve, acc, head :: rest =>
        if isCloseBracketTok head then
          .ok (acc, head :: rest)
        -- wen-2.0 ⑦ 真名词化器: `PRED 者` (者 in noun position).  When `acc`
        -- surface-types to an `arr T .bool` (a predicate) and `head` is the
        -- syntax marker `者`, fold `acc` into `.construction "者" [acc]`.
        -- This fires *before* the head-position binder case picks it up
        -- (binder requires a variable name *after* `者`; here there's no
        -- such requirement because we're nominalizing the predicate to its
        -- left).  Honour `reserve` so outer contexts aren't starved.
        else if isZheSyntaxTok head then
          match surfaceExprTypeWithCtx? ctx acc with
          | some (.arr _ .bool) =>
              if decide (reserve <= rest.length) then
                parsePostfixApplications ctx allowInfix n reserve
                  (.construction "者" [acc]) rest
              else
                .ok (acc, head :: rest)
          | _ => .ok (acc, head :: rest)
        -- wen-2.0 ⑦ `X 属 S` set-membership infix.  `属` is a binary postfix-
        -- positioned operator: `acc` is the element being tested; the next
        -- sub-expression is the Set argument.  Result: `.construction "属"
        -- [acc, rhs]` ⇒ elaborator emits `Tm.memberOf acc rhs`.
        else if isShuSyntaxTok head then
          if allowInfix && decide (reserve < rest.length) then
            match parseSurfaceExprAux ctx false n reserve rest with
            | .ok (rhs, rest') =>
                parsePostfixApplications ctx allowInfix n reserve
                  (.construction "属" [acc, rhs]) rest'
            | .error e => .error e
          else
            .ok (acc, head :: rest)
        else if isApplicationMarkerTok head then
          -- B-7: only fold `之 ARG` into `(acc ARG)` when `acc` is a function
          -- (or a lambda).  Otherwise `(NON-FN) 之 X 之 Y` would inner-recurse
          -- on `[X, 之, Y]` and greedily produce `(X Y)`, which the outer
          -- marker then mis-applies to `acc` as a *single* arg.  Surrendering
          -- the `之` here lets the outer caller resume the chain so curried
          -- lambdas (`（λ甲 λ乙 BODY）之 X 之 Y`) parse without inner parens.
          let accIsFunctional : Bool :=
            match surfaceExprTypeWithCtx? ctx acc with
            | some (.arr _ _) => true
            | _ =>
                match lambdaParts? acc with
                | some _ => true
                | none => false
          if !accIsFunctional then
            .ok (acc, head :: rest)
          else
            match parseSurfaceExprAux ctx allowInfix n reserve rest with
            | .ok (arg, rest') =>
                if decide (reserve <= rest'.length) then
                  parsePostfixApplications ctx allowInfix n reserve (.marker head (.app acc arg)) rest'
                else
                  .ok (acc, head :: rest)
            | .error _ => .ok (acc, head :: rest)
          else
            -- Postfix dispatch fires before infix.  A postfix entry consumes
            -- exactly one token (`head`) and re-shapes `acc` into
            -- `(opTok) acc`.  Honour `reserve` so outer contexts that need
            -- trailing tokens are not starved.  The `prec` field is currently
            -- treated as a tie-breaker only (entries are disjoint by surface
            -- glyph from infix entries — see `postfixSurfaceSyntaxEntries`).
            match postfixSyntaxEntry? head with
            | some (opTok, _prec) =>
                if decide (reserve <= rest.length) then
                  parsePostfixApplications ctx allowInfix n reserve (.app (.atom opTok) acc) rest
                else
                  .ok (acc, head :: rest)
            | none =>
              -- wen-2.0 ⑧ `Y 之所以 X`: reason-extraction infix.  When the
              -- preceding `acc = Y` is a complete expression and the next
              -- token is `之所以`, consume the marker and parse the rhs `X`
              -- (the "reason" predicate / verb).  Reshape to `.app X Y`
              -- (reason-as-application — the kernel treats this as ordinary
              -- function application; the rhetorical "causes Y to X"
              -- framing lives only at the surface).
              --
              -- Honour `reserve` so outer contexts that need trailing
              -- tokens still get them.  Disallow infix inside `X` to keep
              -- chained relation parsing predictable.
              match head.atom with
              | .syntax .zhiSuoYi =>
                  if decide ((head :: rest).length <= reserve) then
                    .ok (acc, head :: rest)
                  else
                    match parseSurfaceExprAux ctx false n reserve rest with
                    | .ok (rhs, rest') =>
                        parsePostfixApplications ctx allowInfix n reserve
                          (.app rhs acc) rest'
                    | .error e => .error e
              | _ =>
              match relationInfixTok? head with
              | some opTok =>
                  if allowInfix then
                    if decide ((head :: rest).length <= reserve) then
                      .ok (acc, head :: rest)
                    else
                      match surfaceExprTypeWithCtx? ctx acc with
                      | some .hex =>
                          match parseSurfaceExprExpected ctx false n reserve .hex rest with
                          | .ok (rhs, rest') =>
                              match rest' with
                              | next :: _ =>
                                  match relationInfixTok? next with
                                  | some _ => .error (.nonassocInfix next.surface next.col)
                                  | none =>
                                      parsePostfixApplications ctx allowInfix n reserve
                                        (.app (.app (.atom opTok) acc) rhs) rest'
                              | [] =>
                                  parsePostfixApplications ctx allowInfix n reserve
                                    (.app (.app (.atom opTok) acc) rhs) []
                          | .error e => .error e
                      | some actual => .error (.typeMismatch .hex actual head.surface head.col)
                      | none => .ok (acc, head :: rest)
                  else
                    .ok (acc, head :: rest)
              | none =>
                  let parseBareLambdaArg :=
                    if decide ((head :: rest).length <= reserve) then
                      .ok (acc, head :: rest)
                    else
                      match parseSurfaceExprAux ctx allowInfix n reserve (head :: rest) with
                      | .ok (arg, rest') =>
                          parsePostfixApplications ctx allowInfix n reserve (.app acc arg) rest'
                      | .error _ => .ok (acc, head :: rest)
                  match surfaceExprTypeWithCtx? ctx acc with
                  | some (.arr expected _) =>
                      if decide ((head :: rest).length <= reserve) then
                        .ok (acc, head :: rest)
                      else
                        match parseSurfaceExprExpected ctx allowInfix n reserve expected (head :: rest) with
                        | .ok (arg, rest') =>
                            parsePostfixApplications ctx allowInfix n reserve (.app acc arg) rest'
                        | .error _ =>
                            match lambdaParts? acc with
                            | some _ => parseBareLambdaArg
                            | none => .ok (acc, head :: rest)
                  | _ =>
                      match lambdaParts? acc with
                      | some _ => parseBareLambdaArg
                      | none => .ok (acc, head :: rest)
  end

def leftoverAtomsErr : List ResolvedTok → ParseErr
  | [] => .leftoverAtoms 0 "" 0
  | first :: rest =>
      match first.atom with
      | .closeBracket => .unmatchedCloseBracket first.surface first.col
      | _ => .leftoverAtoms (rest.length + 1) first.surface first.col

/-- Context-aware variant of `parseSurfaceResolved` — used by wen-2.0 ②
    `定递` so subsequent statements can reference recursive defs by their
    Heavenly-Stem var name with the correct function type pre-bound in ctx.
    The parser's `surfaceExprTypeWithCtx?` consults this ctx for varName
    typing, which drives application-arity inference. -/
def parseSurfaceResolvedInCtx (ctx : Ctx) (rs : List ResolvedTok) : Except ParseErr SurfaceExpr :=
  match rs with
  | [] => .error (.expectedExpression 0)
  | _ =>
      let fuel := rs.length * 2 + 1
      match parseSurfaceExprAux ctx true fuel 0 rs with
      | .error e => .error e
      | .ok (expr, []) => .ok expr
      | .ok (.atom tok, leftover@(_ :: _)) =>
          if isUnpromotedHexagramGap tok.surface then
            .error (.unpromotedHexagramGap tok.surface tok.col)
          else
            .error (leftoverAtomsErr leftover)
      | .ok (_, leftover) => .error (leftoverAtomsErr leftover)

def parseSurfaceResolved (rs : List ResolvedTok) : Except ParseErr SurfaceExpr :=
  parseSurfaceResolvedInCtx [] rs

def firstAmbiguousResolved? : List ResolvedTok → Option (GlyphTok × List OperatorReading)
  | [] => none
  | t :: rest =>
      match t.atom with
      | .ambiguousOp candidates => some (t.tok, candidates)
      | _ => firstAmbiguousResolved? rest

def parseSurfaceResolvedOrResolveErr (rs : List ResolvedTok)
    : Except (ResolveErr ⊕ ParseErr) SurfaceExpr :=
  match parseSurfaceResolved rs with
  | .ok expr => .ok expr
  | .error e =>
      match firstAmbiguousResolved? rs with
      | some (tok, candidates) =>
          .error (.inl (.ambiguous tok.surface tok.startCol candidates))
      | none => .error (.inr e)

/-- Context-aware variant of `parseSurfaceResolvedOrResolveErr`.  See
    `parseSurfaceResolvedInCtx`. -/
def parseSurfaceResolvedOrResolveErrInCtx (ctx : Ctx) (rs : List ResolvedTok)
    : Except (ResolveErr ⊕ ParseErr) SurfaceExpr :=
  match parseSurfaceResolvedInCtx ctx rs with
  | .ok expr => .ok expr
  | .error e =>
      match firstAmbiguousResolved? rs with
      | some (tok, candidates) =>
          .error (.inl (.ambiguous tok.surface tok.startCol candidates))
      | none => .error (.inr e)

def parseSurface (s : String) : Except (LexErr ⊕ ResolveErr ⊕ ParseErr) SurfaceExpr :=
  match lexWen s with
  | .error e => .error (.inl e)
  | .ok toks =>
      match resolveWithCuesAllowAmbiguous toks with
      | .error e => .error (.inr (.inl e))
      | .ok rs =>
          match parseSurfaceResolvedOrResolveErr rs with
          | .error (.inl e) => .error (.inr (.inl e))
          | .error (.inr e) => .error (.inr (.inr e))
          | .ok expr => .ok expr

/-! ## § 4 Sanity -/

example : (parseSurface "推 一").toOption.isSome = true := by native_decide

example : (parseSurface "推 之 一").toOption.isSome = true := by native_decide

example : (parseSurface "推 乾 之").toOption.isNone = true := by native_decide

example : (parseSurface "凡 甲 同 甲 甲").toOption.isSome = true := by native_decide

example : (parseSurface "令 甲 乾 同 甲 乾").toOption.isSome = true := by native_decide

example : (parseSurface "者 甲 甲 之 乾").toOption.isSome = true := by native_decide

example : (parseSurface "同 乾 之 坤").toOption.isSome = true := by native_decide

example : (parseSurface "（推 一）").toOption.isSome = true := by native_decide

example : (parseSurface "(推 一)").toOption.isSome = true := by native_decide

example : (parseSurface "同 （推 一） （推 一）").toOption.isSome = true := by native_decide
example : (parseSurface "一 同 一").toOption.isSome = true := by native_decide
example : (parseSurface "推 乾 同 一").toOption.isSome = true := by native_decide
example : (parseSurface "（推 乾） 同 一").toOption.isSome = true := by native_decide
example : (parseSurface "乾 比 坤").toOption.isSome = true := by native_decide
example : (parseSurface "一 同 一 同 一").toOption.isNone = true := by native_decide

example : (parseSurface "而 推 損 一").toOption.isSome = true := by native_decide
example : (parseSurface "而 損 推").toOption.isSome = true := by native_decide
example : (parseSurface "而 反 推").toOption.isSome = true := by native_decide
example : (parseSurface "而 推 反").toOption.isSome = true := by native_decide
example : (parseSurface "再 反").toOption.isSome = true := by native_decide
example : (parseSurface "推").toOption.isSome = true := by native_decide
example : (parseSurface "不").toOption.isSome = true := by native_decide
example : (parseSurface "同 乾").toOption.isSome = true := by native_decide
example : (parseSurface "（推）").toOption.isSome = true := by native_decide
example : (parseSurface "（同 乾）").toOption.isSome = true := by native_decide
example : (parseSurface "（同 乾） 乾").toOption.isSome = true := by native_decide
example : (parseSurface "者 甲 推 甲 乾").toOption.isSome = true := by native_decide
example : (parseSurface "在 乾").toOption.isSome = true := by native_decide

example : (parseSurface "（推 一").toOption.isNone = true := by native_decide

example : (parseSurface "推 一）").toOption.isNone = true := by native_decide

example : (parseSurface "（）").toOption.isNone = true := by native_decide
example :
    (match parseSurfaceResolved [] with
    | .error (.expectedExpression 0) => true
    | _ => false) = true := by native_decide
example :
    (match parseSurface "（）" with
    | .error (.inr (.inr (.expectedExpression 1))) => true
    | _ => false) = true := by native_decide
example :
    (match parseSurface "之" with
    | .error (.inr (.inr (.expectedExpression 1))) => true
    | _ => false) = true := by native_decide

example :
    (match parseSurface "反" with
     | .error (.inr (.inl (.ambiguous "反" 0 candidates))) => candidates.length == 3
     | _ => false) = true := by native_decide

example :
    (match parseSurface "或 乾" with
     | .error (.inr (.inl (.ambiguous "或" 0 candidates))) => candidates.length == 2
     | _ => false) = true := by native_decide

/-! ## § 5 Postfix marker parsing

The `也` glyph carries two surface forms after wen-restructure 05:

* prefix `S_14` (arity 1, from `operatorForms`) — `也 乾` still parses as
  the prefix application
* postfix `S_14` (prec 10) — `推 一 也` parses `也` as a postfix marker
  over the already-built `推 一`

Postfix dispatch runs **before** infix in `parsePostfixApplications`, so the
choice between prefix-start and postfix-tail is decided by the *position* of
the token (expression-start = prefix, after a complete `acc` = postfix).
-/

/-- Postfix demo: `也` after a complete expression. -/
example : (parseSurface "推 一 也").toOption.isSome = true := by native_decide

/-- Back-compat: `推 一` still parses without any postfix. -/
example : (parseSurface "推 一").toOption.isSome = true := by native_decide

/-- Back-compat: `也 乾` still parses as the prefix application of `S_14`. -/
example : (parseSurface "也 乾").toOption.isSome = true := by native_decide

/-- Postfix consumes one token; chained postfix is left-associative. -/
example : (parseSurface "推 一 也 也").toOption.isSome = true := by native_decide

/-- Mixed postfix + relation infix: `一 同 一 也` succeeds. The postfix
    binds tighter than the infix, so `也` applies after the relation rhs. -/
example : (parseSurface "一 同 一 也").toOption.isSome = true := by native_decide

end SSBX.Foundation.Wen.WenSurface
