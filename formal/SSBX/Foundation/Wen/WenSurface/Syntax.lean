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

inductive ParseErr where
  | empty
  | fuelExhausted
  | unmatchedOpenBracket (surface : String) (col : Nat)
  | unmatchedCloseBracket (surface : String) (col : Nat)
  | expectedCloseBracket (openSurface expected : String) (openCol col : Nat)
  | expectedVariable (surface : String) (col : Nat)
  | unexpectedApplicationMarker (surface : String) (col : Nat)
  | unpromotedHexagramGap (surface : String) (col : Nat)
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

def isCloseBracketTok (t : ResolvedTok) : Bool :=
  match t.atom with
  | .closeBracket => true
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

def atomSurfaceType? : ResolvedAtom → Option Ty
  | .hexConst _ => some .hex
  | .boolConst _ => some .bool
  | .varName _ => some .hex
  | .catalogueOp r =>
      match r.operator? with
      | some id => exactOperatorType? id
      | none => none
  | .hexOrOp _ _ => some .hex
  | _ => none

def surfaceExprType? : SurfaceExpr → Option Ty
  | .atom tok => atomSurfaceType? tok.atom
  | .app f x =>
      match surfaceExprType? f, surfaceExprType? x with
      | some (.arr a b), some a' => if a = a' then some b else none
      | _, _ => none
  | .seq [x] => surfaceExprType? x
  | .seq _ => none
  | .marker _ body => surfaceExprType? body
  | .binder .lambda _ body =>
      match surfaceExprType? body with
      | some ty => some (.arr .hex ty)
      | none => none
  | .binder .forallHex _ body =>
      match surfaceExprType? body with
      | some .bool => some .bool
      | _ => none
  | .letBind _ value body =>
      match surfaceExprType? value with
      | some .hex => surfaceExprType? body
      | _ => none
  | .construction "之又" [inner] => surfaceExprType? inner
  | .construction _ _ => none
  | .grouped _ _ body => surfaceExprType? body

def typedExprMatches (expected : Ty) (expr : SurfaceExpr) : Bool :=
  match surfaceExprType? expr with
  | some actual => actual = expected
  | none => false

def expectedTypeErr (expected : Ty) (head : ResolvedTok) (expr : SurfaceExpr) : ParseErr :=
  match surfaceExprType? expr with
  | some actual => .typeMismatch expected actual head.surface head.col
  | none =>
      match exactTokWithType? head with
      | some (_, _, actual) => .typeMismatch expected actual head.surface head.col
      | none => .empty

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

def asVarName? (t : ResolvedTok) : Option String :=
  match t.atom with
  | .varName n => some n
  | _ => none

def expectedVariableErr (head : ResolvedTok) : ParseErr :=
  .expectedVariable head.surface head.col

def expectedCloseBracketErr (openTok : ResolvedTok) (rest : List ResolvedTok) : ParseErr :=
  let expected := (matchingCloseBracket? openTok.surface).getD "）"
  match rest with
  | closeTok :: _ => .expectedCloseBracket openTok.surface expected openTok.col closeTok.col
  | [] => .unmatchedOpenBracket openTok.surface openTok.col

/-! ## § 3 Prefix parser -/

mutual
  def parseSurfaceExprAux : Nat → Nat → List ResolvedTok → Except ParseErr (SurfaceExpr × List ResolvedTok)
    | 0, _, _ => .error .fuelExhausted
    | _+1, _, [] => .error .empty
    | n+1, reserve, head :: rest =>
      match head.atom with
      | .syntax .zhe =>
          match rest with
          | v :: rest' =>
              match asVarName? v with
              | some name =>
                  match parseSurfaceExprAux n reserve rest' with
                  | .ok (body, rest'') =>
                      parsePostfixApplications n reserve (.binder .lambda name body) rest''
                  | .error e => .error e
              | none => .error (expectedVariableErr head)
          | [] => .error (expectedVariableErr head)
      | .syntax .ling =>
          match rest with
          | v :: rest' =>
              match asVarName? v with
              | some name =>
                  match parseSurfaceExprAux n 1 rest' with
                  | .error e => .error e
                  | .ok (value, rest'') =>
                      match parseSurfaceExprAux n reserve rest'' with
                      | .ok (body, rest''') =>
                          parsePostfixApplications n reserve (.letBind name value body) rest'''
                      | .error e => .error e
              | none => .error (expectedVariableErr head)
          | [] => .error (expectedVariableErr head)
      | .appMarker =>
          match parseSurfaceExprAux n reserve rest with
          | .ok (body, rest') => parsePostfixApplications n reserve (.marker head body) rest'
          | .error e => .error e
      | .iterate =>
          match parseSurfaceExprAux n reserve rest with
          | .ok (body, rest') =>
              parsePostfixApplications n reserve (.construction "之又" [body]) rest'
          | .error e => .error e
      | .openBracket =>
          match parseSurfaceExprAux n reserve rest with
          | .error e => .error e
          | .ok (body, closeTok :: rest') =>
              match closeTok.atom with
              | .closeBracket =>
                  match matchingCloseBracket? head.surface with
                  | some expected =>
                      if closeTok.surface = expected then
                        parsePostfixApplications n reserve (.grouped head closeTok body) rest'
                      else
                        .error (.expectedCloseBracket head.surface expected head.col closeTok.col)
                  | none => .error (.unmatchedOpenBracket head.surface head.col)
              | _ => .error (expectedCloseBracketErr head (closeTok :: rest'))
          | .ok (_, []) => .error (expectedCloseBracketErr head [])
      | .closeBracket =>
          .error (.unmatchedCloseBracket head.surface head.col)
      | .hexOrOp h r =>
          match r.operator? with
          | none => parsePostfixApplications n reserve (.atom { head with atom := .hexConst h }) rest
          | some id =>
              let hexFallback :=
                parsePostfixApplications n reserve (.atom { head with atom := .hexConst h }) rest
              if isApplicationOperator id then
                hexFallback
              else
                match exactNormalStart? head with
                | some (tok, args) =>
                    match collectExactArgsPartial n reserve (.atom tok) args rest with
                    | .ok (expr, rest') =>
                        if rest'.length < rest.length then
                          parsePostfixApplications n reserve expr rest'
                        else
                          hexFallback
                    | .error _ => hexFallback
                | none =>
                    match collectSurfaceArgs n (.atom { head with atom := .catalogueOp r }) (parseArityFor id) rest with
                    | .ok (expr, rest') =>
                        if decide (reserve <= rest'.length) then
                          parsePostfixApplications n reserve expr rest'
                        else hexFallback
                    | .error _ => hexFallback
      | .catalogueOp r =>
          match r.operator? with
          | none => .error (.unexpectedApplicationMarker head.surface head.col)
          | some id =>
              if isApplicationOperator id then
                match parseSurfaceExprAux n reserve rest with
                | .ok (body, rest') => parsePostfixApplications n reserve (.marker head body) rest'
                | .error e => .error e
              else if id = .Q_1 then
                match rest with
                | v :: rest' =>
                    match asVarName? v with
                    | some name =>
                        match parseSurfaceExprAux n reserve rest' with
                        | .ok (body, rest'') =>
                            parsePostfixApplications n reserve (.binder .forallHex name body) rest''
                        | .error e => .error e
                      | none =>
                        match exactNormalStart? head with
                        | some (tok, args) =>
                            match collectExactArgsPartial n reserve (.atom tok) args rest with
                            | .ok (expr, rest') => parsePostfixApplications n reserve expr rest'
                            | .error e => .error e
                        | none =>
                            match collectSurfaceArgs n (.atom head) (parseArityFor id) rest with
                            | .ok (expr, rest') => parsePostfixApplications n reserve expr rest'
                            | .error e => .error e
                  | [] =>
                      match exactNormalStart? head with
                      | some (tok, args) =>
                          match collectExactArgsPartial n reserve (.atom tok) args rest with
                          | .ok (expr, rest') => parsePostfixApplications n reserve expr rest'
                          | .error e => .error e
                      | none =>
                          match collectSurfaceArgs n (.atom head) (parseArityFor id) rest with
                          | .ok (expr, rest') => parsePostfixApplications n reserve expr rest'
                          | .error e => .error e
                else
                  match exactNormalStart? head with
                  | some (tok, args) =>
                      match collectExactArgsPartial n reserve (.atom tok) args rest with
                      | .ok (expr, rest') => parsePostfixApplications n reserve expr rest'
                      | .error e => .error e
                  | none =>
                      match collectSurfaceArgs n (.atom head) (parseArityFor id) rest with
                      | .ok (expr, rest') => parsePostfixApplications n reserve expr rest'
                      | .error e => .error e
      | .hexConst _ => parsePostfixApplications n reserve (.atom head) rest
      | .boolConst _ => parsePostfixApplications n reserve (.atom head) rest
      | .varName _ => parsePostfixApplications n reserve (.atom head) rest

    def collectSurfaceArgs : Nat → SurfaceExpr → Nat → List ResolvedTok →
        Except ParseErr (SurfaceExpr × List ResolvedTok)
    | _, acc, 0, rest => .ok (acc, rest)
    | 0, _, _+1, _ => .error .fuelExhausted
    | n+1, acc, k+1, rest =>
          match parseSurfaceExprAux n k rest with
          | .error e => .error e
          | .ok (arg, rest') => collectSurfaceArgs n (.app acc arg) k rest'

    def collectExactArgsPartial : Nat → Nat → SurfaceExpr → List Ty → List ResolvedTok →
        Except ParseErr (SurfaceExpr × List ResolvedTok)
      | _, _, acc, [], rest => .ok (acc, rest)
      | 0, _, _, _ :: _, _ => .error .fuelExhausted
      | n+1, reserve, acc, expected :: expectedRest, rest =>
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
                  | .arr _ _ => parseSurfaceExprExpected n argReserve expected rest
                  | _ => parseSurfaceExprAux n argReserve rest
                match parsed with
                | .error e => .error e
                | .ok (arg, rest') =>
                    collectExactArgsPartial n reserve (.app acc arg) expectedRest rest'
          | [] => .ok (acc, [])

    def collectExactArgsExact : Nat → Nat → SurfaceExpr → List Ty → List ResolvedTok →
        Except ParseErr (SurfaceExpr × List ResolvedTok)
      | _, _, acc, [], rest => .ok (acc, rest)
      | 0, _, _, _ :: _, _ => .error .fuelExhausted
      | _+1, _, _, _ :: _, [] => .error .empty
      | n+1, reserve, acc, expected :: expectedRest, rest =>
          if decide (rest.length <= reserve) then
            .error .empty
          else
            let argReserve := reserve + expectedRest.length
            let parsed :=
              match expected with
              | .arr _ _ => parseSurfaceExprExpected n argReserve expected rest
              | _ => parseSurfaceExprAux n argReserve rest
            match parsed with
            | .error e => .error e
            | .ok (arg, rest') =>
                collectExactArgsExact n reserve (.app acc arg) expectedRest rest'

    def parseSurfaceExprExpected : Nat → Nat → Ty → List ResolvedTok →
        Except ParseErr (SurfaceExpr × List ResolvedTok)
      | 0, _, _, _ => .error .fuelExhausted
      | _+1, _, _, [] => .error .empty
      | n+1, reserve, expected, head :: rest =>
          match exactExpectedStart? expected head with
          | some (tok, args) =>
              match collectExactArgsExact n reserve (.atom tok) args rest with
              | .ok result => .ok result
              | .error _ =>
                  match parseSurfaceExprAux n reserve (head :: rest) with
                  | .ok result =>
                      if typedExprMatches expected result.1 then
                        .ok result
                      else
                        .error (expectedTypeErr expected head result.1)
                  | .error e => .error e
          | none =>
              match parseSurfaceExprAux n reserve (head :: rest) with
              | .ok result =>
                  if typedExprMatches expected result.1 then
                    .ok result
                  else
                    .error (expectedTypeErr expected head result.1)
              | .error e => .error e

  def parsePostfixApplications : Nat → Nat → SurfaceExpr → List ResolvedTok →
      Except ParseErr (SurfaceExpr × List ResolvedTok)
    | 0, _, _, _ => .error .fuelExhausted
    | _+1, _, acc, [] => .ok (acc, [])
    | n+1, reserve, acc, head :: rest =>
        if isCloseBracketTok head then
          .ok (acc, head :: rest)
        else if isApplicationMarkerTok head then
          match parseSurfaceExprAux n reserve rest with
          | .ok (arg, rest') =>
              if decide (reserve <= rest'.length) then
                parsePostfixApplications n reserve (.marker head (.app acc arg)) rest'
              else
                .ok (acc, head :: rest)
          | .error _ => .ok (acc, head :: rest)
          else
            match surfaceExprType? acc with
            | some (.arr expected _) =>
                if decide ((head :: rest).length <= reserve) then
                  .ok (acc, head :: rest)
                else
                  match parseSurfaceExprExpected n reserve expected (head :: rest) with
                  | .ok (arg, rest') => parsePostfixApplications n reserve (.app acc arg) rest'
                  | .error _ => .ok (acc, head :: rest)
            | _ => .ok (acc, head :: rest)
  end

def leftoverAtomsErr : List ResolvedTok → ParseErr
  | [] => .leftoverAtoms 0 "" 0
  | first :: rest =>
      match first.atom with
      | .closeBracket => .unmatchedCloseBracket first.surface first.col
      | _ => .leftoverAtoms (rest.length + 1) first.surface first.col

def parseSurfaceResolved (rs : List ResolvedTok) : Except ParseErr SurfaceExpr :=
  let fuel := rs.length * 2 + 1
  match parseSurfaceExprAux fuel 0 rs with
  | .error e => .error e
  | .ok (expr, []) => .ok expr
  | .ok (.atom tok, leftover@(_ :: _)) =>
      if isUnpromotedHexagramGap tok.surface then
        .error (.unpromotedHexagramGap tok.surface tok.col)
      else
        .error (leftoverAtomsErr leftover)
  | .ok (_, leftover) => .error (leftoverAtomsErr leftover)

def parseSurface (s : String) : Except (LexErr ⊕ ResolveErr ⊕ ParseErr) SurfaceExpr :=
  match lexWen s with
  | .error e => .error (.inl e)
  | .ok toks =>
      match resolveWithCues toks with
      | .error e => .error (.inr (.inl e))
      | .ok rs =>
          match parseSurfaceResolved rs with
          | .error e => .error (.inr (.inr e))
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

example : (parseSurface "而 推 損 一").toOption.isSome = true := by native_decide
example : (parseSurface "而 損 推").toOption.isSome = true := by native_decide
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

end SSBX.Foundation.Wen.WenSurface
