/-
# WenSurface.Syntax — resolved tokens to explicit surface AST

This layer keeps application markers and binder forms visible before
elaboration.  It replaces the older direct `List ResolvedAtom → Tm` path for
the default interpreter pipeline.
-/
import SSBX.Foundation.Wen.WenSurface.Semantics
import SSBX.Foundation.Wen.WenSurface.Reading

namespace SSBX.Foundation.Wen.WenSurface

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
deriving Repr

inductive ParseErr where
  | empty
  | fuelExhausted
  | expectedVariable (surface : String) (col : Nat)
  | unexpectedApplicationMarker (surface : String) (col : Nat)
  | unpromotedHexagramGap (surface : String) (col : Nat)
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

def asVarName? (t : ResolvedTok) : Option String :=
  match t.atom with
  | .varName n => some n
  | _ => none

def expectedVariableErr (head : ResolvedTok) : ParseErr :=
  .expectedVariable head.surface head.col

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
      | .hexOrOp h r =>
          match r.operator? with
          | none => parsePostfixApplications n reserve (.atom { head with atom := .hexConst h }) rest
          | some id =>
              let hexFallback :=
                parsePostfixApplications n reserve (.atom { head with atom := .hexConst h }) rest
              if isApplicationOperator id then
                hexFallback
              else
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
                      match collectSurfaceArgs n (.atom head) (parseArityFor id) rest with
                      | .ok (expr, rest') => parsePostfixApplications n reserve expr rest'
                      | .error e => .error e
                | [] =>
                    match collectSurfaceArgs n (.atom head) (parseArityFor id) rest with
                    | .ok (expr, rest') => parsePostfixApplications n reserve expr rest'
                    | .error e => .error e
              else
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

  def parsePostfixApplications : Nat → Nat → SurfaceExpr → List ResolvedTok →
      Except ParseErr (SurfaceExpr × List ResolvedTok)
    | 0, _, _, _ => .error .fuelExhausted
    | _+1, _, acc, [] => .ok (acc, [])
    | n+1, reserve, acc, head :: rest =>
        if isApplicationMarkerTok head then
          match parseSurfaceExprAux n reserve rest with
          | .ok (arg, rest') =>
              if decide (reserve <= rest'.length) then
                parsePostfixApplications n reserve (.marker head (.app acc arg)) rest'
              else
                .ok (acc, head :: rest)
          | .error _ => .ok (acc, head :: rest)
        else
          .ok (acc, head :: rest)
end

def leftoverAtomsErr : List ResolvedTok → ParseErr
  | [] => .leftoverAtoms 0 "" 0
  | first :: rest => .leftoverAtoms (rest.length + 1) first.surface first.col

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

end SSBX.Foundation.Wen.WenSurface
