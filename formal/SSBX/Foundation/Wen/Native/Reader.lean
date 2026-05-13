/-
# Wen.Native.Reader -- S-expression boundary for native Wen

The reader is the concrete text boundary over the generic native surface.  It
parses one ASCII S-expression into `SurfaceTopForm n` without importing YiInstr
or the old V4 interpreter spine.

Accepted native grammar:

```text
top     ::= (define name expr) | expr
expr    ::= atom
          | ()
          | (cell bits)
          | (quote expr)          -- Sexp also expands 'expr to this form
          | (lambda param expr)
          | (if expr expr expr)
          | (flip nat expr)
          | (expr expr*)
atom    ::= nil | 空 | true | false | nat | prim | name | #bits
name    ::= @bits | bits
param   ::= name | (name)
bits    ::= exactly n chars, each one of o x 0 1
prim    ::= zero | xor | act | eq | cell-eq | cons | car | cdr
          | null | null? | atom | atom? | bool? | number? | num?
          | numEq | num-eq | num-le | <= | 不大于 | num-lt | < | 大于
          | succ | pred | add | + | eval
```

`#bits` is reserved for cell literals; `@bits` is the explicit spelling for a
surface name.  Bare `bits` remains accepted as a compact name form.

Chinese aliases are accepted only at the reader/surface boundary.  They lower to
the same native core constructors and primitives:

```text
函=lambda, 施=application, 结=cons, 空=nil, 首=car, 余=cdr,
若=if, 空乎/判空=null, 引=quote, 解=eval, 定=define.
```
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
  | "cons" | "结" => some .cons
  | "car" | "首" => some .car
  | "cdr" | "余" => some .cdr
  | "null" | "null?" | "空乎" | "判空" => some .null
  | "atom" | "atom?" => some .atom
  | "bool?" => some .isBool
  | "number?" | "num?" => some .isNumber
  | "numEq" | "num-eq" => some .numEq
  | "numLe" | "num-le" | "<=" | "不大于" => some .numLe
  | "numLt" | "num-lt" | "<" | "大于" => some .numLt
  | "succ" => some .succ
  | "pred" => some .pred
  | "add" | "+" => some .add
  | "eval" | "解" => some .eval
  | _ => none

def slotOfNat? {n : Nat} (index : Nat) : Option (Slot n) :=
  if h : index < n then some ⟨index, h⟩ else none

def readAtom {n : Nat} (token : String) : Option (SurfaceExpr n) :=
  if token == "nil" || token == "空" then some .nil
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
  | .list [.atom "元", .atom token] => do
      let value ← readCellLiteral token
      some (.cell value)
  | .list [.atom "quote", body] => do
      let b ← readExpr body
      some (.quote b)
  | .list [.atom "引", body] => do
      let b ← readExpr body
      some (.quote b)
  | .list [.atom "lambda", param, body] => do
      let p ← readLambdaParam param
      let b ← readExpr body
      some (.lambda p b)
  | .list [.atom "函", param, body] => do
      let p ← readLambdaParam param
      let b ← readExpr body
      some (.lambda p b)
  | .list [.atom "if", test, thenBranch, elseBranch] => do
      let c ← readExpr test
      let t ← readExpr thenBranch
      let e ← readExpr elseBranch
      some (.if0 c t e)
  | .list [.atom "若", test, thenBranch, elseBranch] => do
      let c ← readExpr test
      let t ← readExpr thenBranch
      let e ← readExpr elseBranch
      some (.if0 c t e)
  | .list [.atom "flip", .atom indexToken, arg] => do
      let index ← parseAsciiNat indexToken
      let slot ← slotOfNat? index
      let a ← readExpr arg
      some (.app (.prim (.flip slot)) [a])
  | .list (.atom "施" :: fn :: args) => do
      let f ← readExpr fn
      let as ← readExprList args
      some (.app f as)
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
  | .list [.atom "定", .atom name, body] => do
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

theorem cellOfBits_oooo_eq_origin_r4 :
    cellOfBits (n := 4) [false, false, false, false] = originCell := by
  funext i
  fin_cases i <;> rfl

theorem readName_explicit_origin_r4 :
    readName (n := 4) "@oooo" = some originCell := by
  simp [readName, stripPrefix, cellOfToken, parseBits, bitVal,
    cellOfBits_oooo_eq_origin_r4]

theorem readName_hash_reserved_r4 :
    readName (n := 4) "#oooo" = none := rfl

theorem readAtom_cell_literal_origin_r4 :
    readAtom (n := 4) "#oooo" = some (.cell originCell) := by
  simp [readAtom, primOfToken, parseAsciiNat, parseAsciiNatAux, digitVal,
    stripPrefix, cellOfToken, parseBits, bitVal, cellOfBits_oooo_eq_origin_r4]

theorem cellOfBits_oooooooo_eq_origin_r8 :
    cellOfBits (n := 8)
      [false, false, false, false, false, false, false, false] = originCell := by
  funext i
  fin_cases i <;> rfl

theorem readAtom_chinese_nil_r8 :
    readAtom (n := 8) "空" = some .nil := rfl

theorem primOfToken_chinese_cons_r8 :
    primOfToken (n := 8) "结" = some .cons := rfl

theorem primOfToken_chinese_numLe_r8 :
    primOfToken (n := 8) "不大于" = some .numLe := rfl

theorem primOfToken_chinese_numLt_r8 :
    primOfToken (n := 8) "大于" = some .numLt := rfl

theorem readAtom_cell_literal_origin_r8 :
    readAtom (n := 8) "#oooooooo" = some (.cell originCell) := by
  simp [readAtom, primOfToken, parseAsciiNat, parseAsciiNatAux, digitVal,
    stripPrefix, cellOfToken, parseBits, bitVal, cellOfBits_oooooooo_eq_origin_r8]

def isOriginCellR8 (cell : Cell 8) : Bool :=
  cell ⟨0, by decide⟩ == false &&
  cell ⟨1, by decide⟩ == false &&
  cell ⟨2, by decide⟩ == false &&
  cell ⟨3, by decide⟩ == false &&
  cell ⟨4, by decide⟩ == false &&
  cell ⟨5, by decide⟩ == false &&
  cell ⟨6, by decide⟩ == false &&
  cell ⟨7, by decide⟩ == false

def readEvalChineseConsOriginR8 : Bool :=
  match readEvalTopString (n := 8) 16 [] "(结 #oooooooo 空)" with
  | some ([], .cons (.cell cell) .nil) => isOriginCellR8 cell
  | _ => false

def readEvalChineseCarOriginR8 : Bool :=
  match readEvalTopString (n := 8) 16 [] "(首 (结 #oooooooo 空))" with
  | some ([], .cell cell) => isOriginCellR8 cell
  | _ => false

def readEvalChineseIfNullR8 : Bool :=
  match readEvalTopString (n := 8) 16 [] "(若 (空乎 空) 1 2)" with
  | some ([], .num 1) => true
  | _ => false

theorem readEval_chinese_cons_origin_r8 :
    readEvalChineseConsOriginR8 = true := by
  native_decide

theorem readEval_chinese_car_origin_r8 :
    readEvalChineseCarOriginR8 = true := by
  native_decide

theorem readEval_chinese_if_null_r8 :
    readEvalChineseIfNullR8 = true := by
  native_decide

theorem reader_grammar_laws :
    parseAsciiNat "42" = some 42
    ∧ (primOfToken (n := 4) "xor" = some .xor)
    ∧ (slotOfNat? (n := 4) 2).isSome = true
    ∧ (slotOfNat? (n := 0) 0).isSome = false
    ∧ readName (n := 4) "@oooo" = some originCell
    ∧ readName (n := 4) "#oooo" = none
    ∧ readAtom (n := 4) "#oooo" = some (.cell originCell)
    ∧ readAtom (n := 8) "空" = some .nil
    ∧ primOfToken (n := 8) "结" = some .cons
    ∧ primOfToken (n := 8) "不大于" = some .numLe
    ∧ primOfToken (n := 8) "大于" = some .numLt
    ∧ readAtom (n := 8) "#oooooooo" = some (.cell originCell)
    ∧ readEvalChineseConsOriginR8 = true
    ∧ readEvalChineseCarOriginR8 = true
    ∧ readEvalChineseIfNullR8 = true :=
  ⟨rfl, rfl, rfl, rfl, readName_explicit_origin_r4,
    readName_hash_reserved_r4, readAtom_cell_literal_origin_r4,
    readAtom_chinese_nil_r8, primOfToken_chinese_cons_r8,
    primOfToken_chinese_numLe_r8, primOfToken_chinese_numLt_r8,
    readAtom_cell_literal_origin_r8, readEval_chinese_cons_origin_r8,
    readEval_chinese_car_origin_r8, readEval_chinese_if_null_r8⟩

end Reader

end SSBX.Foundation.Wen.Native
