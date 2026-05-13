/-
# Wen.Native.Reader -- S-expression boundary for native Wen

The reader is a boundary module over the generic native surface.  It parses
ASCII S-expressions into `SurfaceTopForm n` without importing YiInstr or the
old V4 interpreter spine.
-/

import SSBX.Foundation.Lang.Sexp
import SSBX.Foundation.Wen.Native.Surface

namespace SSBX.Foundation.Wen.Native

open SSBX.Foundation.Wen.Layered

namespace Reader

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

def bitVal : Char → Option Bool
  | 'o' => some false
  | '0' => some false
  | 'x' => some true
  | '1' => some true
  | _ => none

def parseBits : List Char → Option (List Bool)
  | [] => some []
  | c :: rest => do
      let bit ← bitVal c
      let bits ← parseBits rest
      some (bit :: bits)

def cellOfBits {n : Nat} (bits : List Bool) : Cell n :=
  fun i => bits.getD i.val false

def cellOfToken {n : Nat} (token : String) : Option (Cell n) := do
  let bits ← parseBits token.toList
  if bits.length = n then
    some (cellOfBits bits)
  else
    none

def stripPrefix (mark : Char) (token : String) : Option String :=
  match token.toList with
  | [] => none
  | c :: rest =>
      if c = mark then some (String.ofList rest) else none

def readName {n : Nat} (token : String) : Option (Cell n) :=
  match stripPrefix '@' token with
  | some rest => cellOfToken rest
  | none =>
      match stripPrefix '#' token with
      | some rest => cellOfToken rest
      | none => cellOfToken token

def readCellLiteral {n : Nat} (token : String) : Option (Cell n) :=
  match stripPrefix '#' token with
  | some rest => cellOfToken rest
  | none => cellOfToken token

def primOfToken {n : Nat} : String → Option (Prim n)
  | "zero" => some .zero
  | "xor" => some .xor
  | "act" => some .act
  | "eq" | "cell-eq" => some .eq
  | "cons" => some .cons
  | "car" => some .car
  | "cdr" => some .cdr
  | "null" | "null?" => some .null
  | "atom" | "atom?" => some .atom
  | "bool?" => some .isBool
  | "number?" | "num?" => some .isNumber
  | "numEq" | "num-eq" => some .numEq
  | "succ" => some .succ
  | "pred" => some .pred
  | "add" | "+" => some .add
  | "eval" => some .eval
  | _ => none

def slotOfNat? {n : Nat} (index : Nat) : Option (Slot n) :=
  if h : index < n then some ⟨index, h⟩ else none

def readAtom {n : Nat} (token : String) : Option (SurfaceExpr n) :=
  if token == "nil" then some .nil
  else if token == "true" then some (.bool true)
  else if token == "false" then some (.bool false)
  else
    match primOfToken token with
    | some prim => some (.prim prim)
    | none =>
        match parseAsciiNat token with
        | some value => some (.num value)
        | none =>
            match stripPrefix '#' token with
            | some rest => do
                let value ← cellOfToken rest
                some (.cell value)
            | none =>
                match readName token with
                | some name => some (.ref name)
                | none => none

mutual

def readExprList {n : Nat} : List SSBX.Foundation.Lang.Sexp → Option (List (SurfaceExpr n))
  | [] => some []
  | head :: tail => do
      let h ← readExpr head
      let t ← readExprList tail
      some (h :: t)

def readLambdaParam {n : Nat} : SSBX.Foundation.Lang.Sexp → Option (Cell n)
  | .atom token => readName token
  | .list [.atom token] => readName token
  | _ => none

def readExpr {n : Nat} : SSBX.Foundation.Lang.Sexp → Option (SurfaceExpr n)
  | .atom token => readAtom token
  | .named _ _ => none
  | .list [] => some .nil
  | .list [.atom "cell", .atom token] => do
      let value ← readCellLiteral token
      some (.cell value)
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
  | .list [.atom "flip", .atom indexToken, arg] => do
      let index ← parseAsciiNat indexToken
      let slot ← slotOfNat? index
      let a ← readExpr arg
      some (.app (.prim (.flip slot)) [a])
  | .list (fn :: args) => do
      let f ← readExpr fn
      let as ← readExprList args
      some (.app f as)

end

def readTop {n : Nat} : SSBX.Foundation.Lang.Sexp → Option (SurfaceTopForm n)
  | .list [.atom "define", .atom name, body] => do
      let cell ← readName name
      let expr ← readExpr body
      some (.define cell expr)
  | sexp => do
      let expr ← readExpr sexp
      some (.expr expr)

def readTopString {n : Nat} (source : String) : Option (SurfaceTopForm n) :=
  match SSBX.Foundation.Lang.Sexp.parse source with
  | .ok sexp => readTop sexp
  | .error _ => none

def readEvalTopString {n : Nat}
    (fuel : Nat) (global : GlobalEnv n) (source : String) :
    Option (GlobalEnv n × Value n) := do
  let form ← readTopString source
  SurfaceTopForm.evalFuel fuel global form

def readEvalTwoTopStrings {n : Nat}
    (fuel : Nat) (global : GlobalEnv n) (first second : String) :
    Option (GlobalEnv n × Value n) := do
  let (global', _) ← readEvalTopString fuel global first
  readEvalTopString fuel global' second

theorem reader_summary :
    parseAsciiNat "42" = some 42
    ∧ (primOfToken (n := 4) "xor" = some .xor)
    ∧ (slotOfNat? (n := 4) 2).isSome = true
    ∧ (slotOfNat? (n := 0) 0).isSome = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Reader

end SSBX.Foundation.Wen.Native
