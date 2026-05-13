/-
# Wen.V4Kernel.LispReader -- S-expression reader for 64-word Wen Lisp

This is a boundary module: it imports the R6/Lexicon bridge and the existing
S-expression parser.  The core syntax/evaluator modules stay V4-only.
-/

import SSBX.Foundation.Lang.Sexp
import SSBX.Foundation.Wen.WenyanParser
import SSBX.Foundation.Wen.V4Kernel.LispSurface
import SSBX.Foundation.Wen.Layered.Bridges.Word64

namespace SSBX.Foundation.Wen.V4Kernel

namespace LispReader

def digitVal : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

def parseAsciiNatAux : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: rest, acc => do
      let d ← digitVal c
      parseAsciiNatAux rest (acc * 10 + d)

def parseAsciiNat (token : String) : Option Nat :=
  match token.toList with
  | [] => none
  | chars => parseAsciiNatAux chars 0

def parseNatToken (token : String) : Option Nat :=
  match SSBX.Foundation.Wen.WenyanParser.parseNumeral token with
  | some n => some n
  | none => parseAsciiNat token

def primOfToken : String → Option Prim
  | "compose" | "v4Compose" | "v4-compose" => some .v4Compose
  | "v4Eq" | "v4-eq" => some .v4Eq
  | "wordCompose" | "word-compose" => some .wordCompose
  | "wordEq" | "word-eq" => some .wordEq
  | "numEq" | "num-eq" => some .numEq
  | "succ" => some .succ
  | "pred" => some .pred
  | "add" | "+" => some .add
  | "cons" => some .cons
  | "car" => some .car
  | "cdr" => some .cdr
  | "null" | "null?" => some .null
  | "atom" | "atom?" => some .atom
  | "symbol?" => some .isSymbol
  | "number?" => some .isNumber
  | "eval" => some .eval
  | "r5?" | "r5Is" | "r5-is" => some .r5Is
  | "r5ToR4" | "r5-to-r4" => some .r5ToR4
  | "r5Compose" | "r5-compose" => some .r5Compose
  | "r5Coords" | "r5-coords" => some .r5Coords
  | _ => none

def v4OfToken : String → Option SSBX.Foundation.Hierarchy.Operators.V4
  | "道" | "dao" => some .dao
  | "错" | "錯" | "cuo" => some .cuo
  | "综" | "綜" | "zong" => some .zong
  | "错综" | "錯綜" | "cuoZong" | "cuozong" => some .cuoZong
  | _ => none

def wordOfToken (token : String) : Option Word64 :=
  SSBX.Foundation.Wen.Layered.Bridges.Word64.wordOfToken token

def readWordName (token : String) : Option Word64 :=
  wordOfToken token

def readAtom (token : String) : Option SurfaceExpr :=
  if token == "nil" then some .nil
  else
    match v4OfToken token with
    | some g => some (.atom g)
    | none =>
        match primOfToken token with
        | some p => some (.prim p)
        | none =>
            match parseNatToken token with
            | some n => some (.num n)
            | none =>
                match wordOfToken token with
                | some word => some (.ref word)
                | none => none

mutual

def readExprList : List SSBX.Foundation.Lang.Sexp → Option (List SurfaceExpr)
  | [] => some []
  | head :: tail => do
      let h ← readExpr head
      let t ← readExprList tail
      some (h :: t)

def readLambdaParam : SSBX.Foundation.Lang.Sexp → Option Word64
  | .atom token => readWordName token
  | .list [.atom token] => readWordName token
  | _ => none

def readExpr : SSBX.Foundation.Lang.Sexp → Option SurfaceExpr
  | .atom token => readAtom token
  | .named _ _ => none
  | .list [] => some .nil
  | .list [.atom "quote", body] => do
      let b ← readExpr body
      some (.quote b)
  | .list [.atom "lambda", param, body] => do
      let p ← readLambdaParam param
      let b ← readExpr body
      some (.lambda p b)
  | .list [.atom "if", test, thenBranch, elseBranch] => do
      let c ← readExpr test
      let t ← readExpr thenBranch
      let e ← readExpr elseBranch
      some (.if0 c t e)
  | .list (fn :: args) => do
      let f ← readExpr fn
      let as ← readExprList args
      some (.app f as)

end

def readTop : SSBX.Foundation.Lang.Sexp → Option SurfaceTopForm
  | .list [.atom "define", .atom name, body] => do
      let word ← readWordName name
      let expr ← readExpr body
      some (.define word expr)
  | sexp => do
      let expr ← readExpr sexp
      some (.expr expr)

def readTopString (source : String) : Option SurfaceTopForm :=
  match SSBX.Foundation.Lang.Sexp.parse source with
  | .ok sexp => readTop sexp
  | .error _ => none

def readEvalTopString (fuel : Nat) (global : GlobalEnv) (source : String) :
    Option (GlobalEnv × Value) := do
  let form ← readTopString source
  SurfaceTopForm.evalFuel fuel global form

def readEvalTwoTopStrings (fuel : Nat) (global : GlobalEnv) (first second : String) :
    Option (GlobalEnv × Value) := do
  let (global', _) ← readEvalTopString fuel global first
  readEvalTopString fuel global' second

#eval readEvalTwoTopStrings 4 [] "(define 乾 (quote 坤))" "乾"
#eval readEvalTopString 8 [] "((lambda (乾) 乾) (quote 坤))"
#eval readEvalTopString 8 [] "(add 三 四)"

theorem reader_summary :
    wordOfToken "乾" = some Word64.qian
    ∧ parseNatToken "三" = some 3
    ∧ primOfToken "add" = some .add
    ∧ v4OfToken "错综" = some .cuoZong
    ∧ primOfToken "r5?" = some .r5Is :=
  ⟨SSBX.Foundation.Wen.Layered.Bridges.Word64.qian_token, rfl, rfl, rfl, rfl⟩

end LispReader

end SSBX.Foundation.Wen.V4Kernel
