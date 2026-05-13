/-
# WenyanAlgorithms -- pure-wenyan program parser with executable witnesses

This module records algorithm examples in the intended pure wenyan style,
without S-expression/Lisp surface syntax.  The wenyan source blocks are parsed
into a small AST, lowered to `Wen.Native` top forms, and run by the native
evaluator; the Lean definitions beside them are executable witnesses for the
same algorithms.

Current boundary: this is a small dedicated parser for the pure-wenyan
algorithm files, not yet the general `WenSurface` reader.
-/

import SSBX.Foundation.Wen.Native.Program

namespace SSBX.Foundation.Wen.WenyanAlgorithms

universe u v

abbrev NativeCell8 := SSBX.Foundation.Wen.Native.Cell 8
abbrev NativeSurfaceExpr8 := SSBX.Foundation.Wen.Native.SurfaceExpr 8
abbrev NativeSurfaceTopForm8 := SSBX.Foundation.Wen.Native.SurfaceTopForm 8
abbrev NativeTopForm8 := SSBX.Foundation.Wen.Native.TopForm 8
abbrev NativeValue8 := SSBX.Foundation.Wen.Native.Value 8

/-!
文言源：

```text
法曰映。
受函，受列。
若列空，归空。
取列之首，名曰甲。
取列之余，名曰乙。
归结施函于甲于映函乙。
```
-/
def «映» (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: «映» f xs

/-!
文言源：

```text
法曰择。
受判，受列。
若列空，归空。
取列之首，名曰甲。
取列之余，名曰乙。
若判施于甲，归结甲于择判乙。
否则归择判乙。
```
-/
def «择» (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
      if p x then
        x :: «择» p xs
      else
        «择» p xs

/-!
文言源：

```text
法曰折。
受并，受始，受列。
若列空，归始。
取列之首，名曰甲。
取列之余，名曰乙。
归折并（并始甲）乙。
```
-/
def «折» (f : β → α → β) : β → List α → β
  | acc, [] => acc
  | acc, x :: xs => «折» f (f acc x) xs

def «和» : List Nat → Nat :=
  «折» (fun acc x => acc + x) 0

def «不大于» (pivot x : Nat) : Bool :=
  decide (x ≤ pivot)

def «大于» (pivot x : Nat) : Bool :=
  decide (pivot < x)

def «小等列» (pivot : Nat) (xs : List Nat) : List Nat :=
  «择» («不大于» pivot) xs

def «大列» (pivot : Nat) (xs : List Nat) : List Nat :=
  «择» («大于» pivot) xs

/-!
文言源：

```text
法曰速排。
受列。
若列空，归空。
取列之首，名曰枢。
取列之余，名曰余。
令小者为择（不大于枢）余。
令大者为择（大于枢）余。
归并速排小者、结枢空、速排大者。
```

Lean witness notes:

* `速排燃` is fuel-bounded so the definition is total.
* `速排 xs` gives fuel `xs.length`, enough for these structural partitions.
* This is algorithmic semantics, not yet a claim that the text block above is
  parsed by the current reader.
-/
def «速排燃» : Nat → List Nat → List Nat
  | 0, xs => xs
  | _ + 1, [] => []
  | fuel + 1, pivot :: rest =>
      «速排燃» fuel («小等列» pivot rest) ++ [pivot] ++
        «速排燃» fuel («大列» pivot rest)

def «速排» (xs : List Nat) : List Nat :=
  «速排燃» xs.length xs

/-! ## Checked examples -/

theorem «映_例» :
    «映» (fun x : Nat => x + 1) [1, 2, 3] = [2, 3, 4] := by
  native_decide

theorem «择_例» :
    «择» (fun x : Nat => decide (x ≤ 2)) [3, 1, 2, 4] = [1, 2] := by
  native_decide

theorem «和_例» :
    «和» [3, 1, 2] = 6 := by
  native_decide

theorem «速排_空» :
    «速排» [] = [] := by
  native_decide

theorem «速排_三一二» :
    «速排» [3, 1, 2] = [1, 2, 3] := by
  native_decide

theorem «速排_有重复» :
    «速排» [3, 1, 2, 1] = [1, 1, 2, 3] := by
  native_decide

theorem «速排_已排» :
    «速排» [1, 2, 3, 4] = [1, 2, 3, 4] := by
  native_decide

theorem «文言算法例汇总» :
    «映» (fun x : Nat => x + 1) [1, 2, 3] = [2, 3, 4]
    ∧ «择» (fun x : Nat => decide (x ≤ 2)) [3, 1, 2, 4] = [1, 2]
    ∧ «和» [3, 1, 2] = 6
    ∧ «速排» [3, 1, 2, 1] = [1, 1, 2, 3] :=
  ⟨«映_例», «择_例», «和_例», «速排_有重复»⟩

/-! ## Pure-wenyan algorithm parser and runner -/

inductive Predicate where
  | lePivot (pivot : String)
  | gtPivot (pivot : String)

inductive Expr where
  | nil
  | var (name : String)
  | singleton (headName : String)
  | filter (predicate : Predicate) (sourceName : String)
  | call (functionName argName : String)
  | append (items : List Expr)

inductive Stmt where
  | ifEmptyReturn (sourceName : String) (body : Expr)
  | letHead (sourceName targetName : String)
  | letTail (sourceName targetName : String)
  | letValue (name : String) (body : Expr)
  | ret (body : Expr)

structure Function where
  name : String
  params : List String
  body : List Stmt

structure ParsedSource where
  main : Function
  sample? : Option (List Nat)

inductive Value where
  | nat (value : Nat)
  | list (items : List Nat)

abbrev Env := List (String × Value)

structure RunResult where
  functionName : String
  input : List Nat
  output : List Nat
deriving DecidableEq, Repr

def cleanLine (line : String) : String :=
  line.trimAscii.toString

def sourceLines (source : String) : List String :=
  (source.splitOn "\n").map cleanLine |>.filter (fun line => line != "")

def parseDigit1to9 : String → Option Nat
  | "一" => some 1
  | "二" => some 2
  | "三" => some 3
  | "四" => some 4
  | "五" => some 5
  | "六" => some 6
  | "七" => some 7
  | "八" => some 8
  | "九" => some 9
  | _ => none

def parseWenNat (token : String) : Option Nat :=
  match token.toNat? with
  | some n => some n
  | none =>
      match token with
      | "零" => some 0
      | "十" => some 10
      | _ =>
          match token.splitOn "十" with
          | [left, right] =>
              let tens? :=
                if left = "" then some 1 else parseDigit1to9 left
              let ones? :=
                if right = "" then some 0 else parseDigit1to9 right
              match tens?, ones? with
              | some tens, some ones => some (tens * 10 + ones)
              | _, _ => none
          | _ => parseDigit1to9 token

def parseWenNatList (source : String) : Option (List Nat) :=
  let parts := (source.splitOn "、").map cleanLine |>.filter (fun token => token != "")
  parts.mapM parseWenNat

def parseSampleLine? (line : String) : Option (List Nat) :=
  let line := cleanLine line
  let body? :=
    match line.splitOn "试以" with
    | ["", rest] => some rest
    | _ =>
        match line.splitOn "試以" with
        | ["", rest] => some rest
        | _ => none
  match body? with
  | none => none
  | some body =>
      match body.splitOn "。" with
      | [items, ""] => parseWenNatList items
      | [items] => parseWenNatList items
      | _ => none

def sampleInput? (source : String) : Option (List Nat) :=
  (sourceLines source).findSome? parseSampleLine?

def splitOnToken? (token source : String) : Option (String × String) :=
  match source.splitOn token with
  | [left, right] => some (left, right)
  | _ => none

def dropPrefix? (pre source : String) : Option String :=
  match splitOnToken? pre source with
  | some ("", rest) => some rest
  | _ => none

def stripFullStop (line : String) : String :=
  match line.splitOn "。" with
  | [body, ""] => body
  | _ => line

def parsePredicate? : String → Option Predicate
  | text =>
      match dropPrefix? "不大于" text with
      | some pivot => some (.lePivot pivot)
      | none =>
          match dropPrefix? "大于" text with
          | some pivot => some (.gtPivot pivot)
          | none => none

def parseCallExpr? (callNames : List String) (text : String) : Option Expr :=
  callNames.findSome? fun functionName =>
    match dropPrefix? functionName text with
    | some argName =>
        if argName == "" then
          none
        else
          some (.call functionName argName)
    | none => none

def parseExprFuel : Nat → List String → String → Option Expr
  | 0, _, _ => none
  | fuel + 1, callNames, raw =>
      let text := cleanLine raw
      if text = "空" then
        some .nil
      else
        match dropPrefix? "并" text with
        | some rest => do
            let items ←
              (rest.splitOn "、").mapM (fun item => parseExprFuel fuel callNames item)
            some (.append items)
        | none =>
            match dropPrefix? "择（" text with
            | some rest => do
                let (predicateText, sourceName) ← splitOnToken? "）" rest
                let predicate ← parsePredicate? predicateText
                some (.filter predicate sourceName)
            | none =>
                match dropPrefix? "结" text with
                | some rest =>
                    match splitOnToken? "空" rest with
                    | some (headName, "") => some (.singleton headName)
                    | _ => none
                | none =>
                    match parseCallExpr? callNames text with
                    | some call => some call
                    | none => some (.var text)

def parseExpr? (callNames : List String) (raw : String) : Option Expr :=
  parseExprFuel (raw.toList.length + 1) callNames raw

inductive ParsedLine where
  | param (name : String)
  | stmt (body : Stmt)

def parseLine? (callNames : List String) (raw : String) : Option ParsedLine :=
  let line := stripFullStop (cleanLine raw)
  match dropPrefix? "受" line with
  | some name => some (.param name)
  | none =>
      match dropPrefix? "若" line with
      | some rest => do
          let (sourceName, bodyText) ← splitOnToken? "空，归" rest
          let body ← parseExpr? callNames bodyText
          some (.stmt (.ifEmptyReturn sourceName body))
      | none =>
          match dropPrefix? "取" line with
          | some rest =>
              match splitOnToken? "之首，名曰" rest with
              | some (sourceName, targetName) =>
                  some (.stmt (.letHead sourceName targetName))
              | none =>
                  match splitOnToken? "之余，名曰" rest with
                  | some (sourceName, targetName) =>
                      some (.stmt (.letTail sourceName targetName))
                  | none => none
          | none =>
              match dropPrefix? "令" line with
              | some rest => do
                  let (name, bodyText) ← splitOnToken? "为" rest
                  let body ← parseExpr? callNames bodyText
                  some (.stmt (.letValue name body))
              | none =>
                  match dropPrefix? "归" line with
                  | some bodyText => do
                      let body ← parseExpr? callNames bodyText
                      some (.stmt (.ret body))
                  | none => none

def isSampleLine (line : String) : Bool :=
  (parseSampleLine? line).isSome

def functionStart? (line : String) : Option String :=
  dropPrefix? "法曰" (stripFullStop (cleanLine line))

def parseFunctionBody :
    List String → List String → List Stmt → Option Function
  | [], _, _ => none
  | first :: rest, params, body =>
      match functionStart? first with
      | none => none
      | some name =>
          let rec go : List String → List String → List Stmt → Option Function
            | [], params, body =>
                some { name := name, params := params.reverse, body := body.reverse }
            | line :: rest, params, body =>
                if isSampleLine line then
                  some { name := name, params := params.reverse, body := body.reverse }
                else if (functionStart? line).isSome then
                  some { name := name, params := params.reverse, body := body.reverse }
                else
                  match parseLine? [name] line with
                  | some (.param param) => go rest (param :: params) body
                  | some (.stmt stmt) => go rest params (stmt :: body)
                  | none => none
          go rest params body

def parseSource? (source : String) : Option ParsedSource := do
  let lines := sourceLines source
  let main ← parseFunctionBody lines [] []
  some { main := main, sample? := sampleInput? source }

def Env.lookup (name : String) : Env → Option Value
  | [] => none
  | (key, value) :: rest =>
      if key = name then some value else lookup name rest

def expectNat : Value → Option Nat
  | .nat value => some value
  | _ => none

def expectList : Value → Option (List Nat)
  | .list items => some items
  | _ => none

def evalPredicate (env : Env) : Predicate → Nat → Option Bool
  | .lePivot pivotName, value => do
      let pivot ← Env.lookup pivotName env >>= expectNat
      some (value ≤ pivot)
  | .gtPivot pivotName, value => do
      let pivot ← Env.lookup pivotName env >>= expectNat
      some (pivot < value)

mutual
  def evalFunction : Nat → List Function → String → List Value → Option Value
    | 0, _, _, _ => none
    | fuel + 1, functions, name, args => do
        let function ← functions.find? (fun candidate => candidate.name = name)
        if function.params.length = args.length then
          let env := function.params.zip args
          evalStmts fuel functions env function.body
        else
          none

  def evalExpr : Nat → List Function → Env → Expr → Option Value
    | 0, _, _, _ => none
    | fuel + 1, functions, env, expr =>
        match expr with
        | .nil => some (.list [])
        | .var name => Env.lookup name env
        | .singleton headName => do
            let head ← Env.lookup headName env >>= expectNat
            some (.list [head])
        | .filter predicate sourceName => do
            let source ← Env.lookup sourceName env >>= expectList
            let kept ← source.mapM (fun value => do
              let keep ← evalPredicate env predicate value
              some (if keep then some value else none))
            some (.list (kept.filterMap id))
        | .call functionName argName => do
            let arg ← Env.lookup argName env >>= expectList
            evalFunction fuel functions functionName [.list arg]
        | .append items => do
            let rec evalAppend : List Expr → Option (List Nat)
              | [] => some []
              | item :: rest => do
                  let xs ← evalExpr fuel functions env item >>= expectList
                  let ys ← evalAppend rest
                  some (xs ++ ys)
            let output ← evalAppend items
            some (.list output)

  def evalStmts : Nat → List Function → Env → List Stmt → Option Value
    | 0, _, _, _ => none
    | _ + 1, _, _, [] => none
    | fuel + 1, functions, env, stmt :: rest =>
        match stmt with
        | .ifEmptyReturn sourceName body => do
            let source ← Env.lookup sourceName env >>= expectList
            if source.isEmpty then
              evalExpr fuel functions env body
            else
              evalStmts fuel functions env rest
        | .letHead sourceName targetName => do
            let source ← Env.lookup sourceName env >>= expectList
            match source with
            | [] => none
            | head :: _ =>
                evalStmts fuel functions ((targetName, .nat head) :: env) rest
        | .letTail sourceName targetName => do
            let source ← Env.lookup sourceName env >>= expectList
            match source with
            | [] => none
            | _ :: tail =>
                evalStmts fuel functions ((targetName, .list tail) :: env) rest
        | .letValue name body => do
            let value ← evalExpr fuel functions env body
            evalStmts fuel functions ((name, value) :: env) rest
        | .ret body =>
            evalExpr fuel functions env body
end

/-! ## Lowering to native Wen -/

def natBit (value index : Nat) : Bool :=
  decide (((value / (2 ^ index)) % 2) = 1)

def cell8OfNat (value : Nat) : NativeCell8 :=
  SSBX.Foundation.Wen.Native.Reader.cellOfBits (n := 8)
    [ natBit value 0
    , natBit value 1
    , natBit value 2
    , natBit value 3
    , natBit value 4
    , natBit value 5
    , natBit value 6
    , natBit value 7
    ]

def cell8OfIndex? (index : Nat) : Option NativeCell8 :=
  if index = 0 then
    none
  else if index < 256 then
    some (cell8OfNat index)
  else
    none

structure NameTable where
  next : Nat
  entries : List (String × NativeCell8)

namespace NameTable

def empty : NameTable :=
  { next := 1, entries := [] }

def lookup (name : String) : NameTable → Option NativeCell8
  | { entries := [], .. } => none
  | { entries := (key, value) :: rest, next := next } =>
      if key = name then
        some value
      else
        lookup name { next := next, entries := rest }

def intern (name : String) (table : NameTable) : Option (NativeCell8 × NameTable) :=
  match lookup name table with
  | some cell => some (cell, table)
  | none => do
      let cell ← cell8OfIndex? table.next
      some (cell, { table with
        next := table.next + 1
        entries := (name, cell) :: table.entries })

def internMany : List String → NameTable → Option (List NativeCell8 × NameTable)
  | [], table => some ([], table)
  | name :: rest, table => do
      let (cell, table) ← intern name table
      let (cells, table) ← internMany rest table
      some (cell :: cells, table)

end NameTable

def helperAppendName : String := "__文言_append"
def helperFilterLeName : String := "__文言_filterLe"
def helperFilterGtName : String := "__文言_filterGt"
def helperXsName : String := "__文言_xs"
def helperYsName : String := "__文言_ys"
def helperPivotName : String := "__文言_pivot"

def sRef (name : NativeCell8) : NativeSurfaceExpr8 :=
  .ref name

def sPrimApp (prim : SSBX.Foundation.Wen.Native.Prim 8)
    (args : List NativeSurfaceExpr8) : NativeSurfaceExpr8 :=
  .app (.prim prim) args

def sCall (fn : NativeCell8) (args : List NativeSurfaceExpr8) : NativeSurfaceExpr8 :=
  .app (.ref fn) args

def sLet (name : NativeCell8) (value body : NativeSurfaceExpr8) : NativeSurfaceExpr8 :=
  .app (.lambda name body) [value]

def sLambdaMany : List NativeCell8 → NativeSurfaceExpr8 → NativeSurfaceExpr8
  | [], body => body
  | param :: rest, body => .lambda param (sLambdaMany rest body)

def sNatList : List Nat → NativeSurfaceExpr8
  | xs => .list (xs.map (fun value => (.num value : NativeSurfaceExpr8)))

def sAppendChain (appendName : NativeCell8) : List NativeSurfaceExpr8 → NativeSurfaceExpr8
  | [] => .nil
  | [item] => item
  | item :: rest => sCall appendName [item, sAppendChain appendName rest]

def exprSize : Expr → Nat
  | .nil => 1
  | .var _ => 1
  | .singleton _ => 1
  | .filter _ _ => 1
  | .call _ _ => 1
  | .append items => exprListSize items + 1
where
  exprListSize : List Expr → Nat
    | [] => 0
    | item :: rest => exprSize item + exprListSize rest

mutual

def compileExprFuel? :
    Nat → NameTable → Expr → Option (NativeSurfaceExpr8 × NameTable)
  | 0, _, _ => none
  | fuel + 1, table, expr =>
      match expr with
      | .nil => some (.nil, table)
      | .var name => do
          let (cell, table) ← NameTable.intern name table
          some (sRef cell, table)
      | .singleton headName => do
          let (head, table) ← NameTable.intern headName table
          some (sPrimApp .cons [sRef head, .nil], table)
      | .filter predicate sourceName =>
          match predicate with
          | .lePivot pivotName => do
              let (helper, table) ← NameTable.intern helperFilterLeName table
              let (pivot, table) ← NameTable.intern pivotName table
              let (source, table) ← NameTable.intern sourceName table
              some (sCall helper [sRef pivot, sRef source], table)
          | .gtPivot pivotName => do
              let (helper, table) ← NameTable.intern helperFilterGtName table
              let (pivot, table) ← NameTable.intern pivotName table
              let (source, table) ← NameTable.intern sourceName table
              some (sCall helper [sRef pivot, sRef source], table)
      | .call functionName argName => do
          let (functionCell, table) ← NameTable.intern functionName table
          let (argCell, table) ← NameTable.intern argName table
          some (sCall functionCell [sRef argCell], table)
      | .append items => do
          let (appendName, table) ← NameTable.intern helperAppendName table
          let (compiledItems, table) ← compileExprListFuel? fuel table items
          some (sAppendChain appendName compiledItems, table)

def compileExprListFuel? :
    Nat → NameTable → List Expr → Option (List NativeSurfaceExpr8 × NameTable)
  | 0, _, _ => none
  | _ + 1, table, [] => some ([], table)
  | fuel + 1, table, item :: rest => do
      let (compiledItem, table) ← compileExprFuel? fuel table item
      let (compiledRest, table) ← compileExprListFuel? fuel table rest
      some (compiledItem :: compiledRest, table)

end

def compileExpr? (table : NameTable) (expr : Expr) :
    Option (NativeSurfaceExpr8 × NameTable) :=
  compileExprFuel? (exprSize expr + 8) table expr

def compileStmts? :
    NameTable → List Stmt → Option (NativeSurfaceExpr8 × NameTable)
  | _, [] => none
  | table, stmt :: rest =>
      match stmt with
      | .ifEmptyReturn sourceName body => do
          let (source, table) ← NameTable.intern sourceName table
          let (thenExpr, table) ← compileExpr? table body
          let (elseExpr, table) ← compileStmts? table rest
          some (SSBX.Foundation.Wen.Native.SurfaceExpr.if0
            (sPrimApp .null [sRef source]) thenExpr elseExpr, table)
      | .letHead sourceName targetName => do
          let (source, table) ← NameTable.intern sourceName table
          let (target, table) ← NameTable.intern targetName table
          let (body, table) ← compileStmts? table rest
          some (sLet target (sPrimApp .car [sRef source]) body, table)
      | .letTail sourceName targetName => do
          let (source, table) ← NameTable.intern sourceName table
          let (target, table) ← NameTable.intern targetName table
          let (body, table) ← compileStmts? table rest
          some (sLet target (sPrimApp .cdr [sRef source]) body, table)
      | .letValue name valueExpr => do
          let (nameCell, table) ← NameTable.intern name table
          let (value, table) ← compileExpr? table valueExpr
          let (body, table) ← compileStmts? table rest
          some (sLet nameCell value body, table)
      | .ret body =>
          compileExpr? table body

def compileFunction? (table : NameTable) (function : Function) :
    Option (NativeSurfaceTopForm8 × NativeCell8 × NameTable) := do
  let (functionCell, table) ← NameTable.intern function.name table
  let (params, table) ← NameTable.internMany function.params table
  let (body, table) ← compileStmts? table function.body
  some (.define functionCell (sLambdaMany params body), functionCell, table)

def compileAppendHelper? (table : NameTable) :
    Option (NativeSurfaceTopForm8 × NameTable) := do
  let (appendName, table) ← NameTable.intern helperAppendName table
  let (xs, table) ← NameTable.intern helperXsName table
  let (ys, table) ← NameTable.intern helperYsName table
  let xsRef := sRef xs
  let ysRef := sRef ys
  let tail := sPrimApp .cdr [xsRef]
  let body :=
    SSBX.Foundation.Wen.Native.SurfaceExpr.if0
      (sPrimApp .null [xsRef])
      ysRef
      (sPrimApp .cons [sPrimApp .car [xsRef], sCall appendName [tail, ysRef]])
  some (.define appendName (sLambdaMany [xs, ys] body), table)

def compileFilterHelper? (helperName : String) (testPrim : SSBX.Foundation.Wen.Native.Prim 8)
    (pivotFirst : Bool) (table : NameTable) :
    Option (NativeSurfaceTopForm8 × NameTable) := do
  let (filterName, table) ← NameTable.intern helperName table
  let (pivot, table) ← NameTable.intern helperPivotName table
  let (xs, table) ← NameTable.intern helperXsName table
  let xsRef := sRef xs
  let pivotRef := sRef pivot
  let head := sPrimApp .car [xsRef]
  let tail := sPrimApp .cdr [xsRef]
  let recursive := sCall filterName [pivotRef, tail]
  let test :=
    if pivotFirst then
      sPrimApp testPrim [pivotRef, head]
    else
      sPrimApp testPrim [head, pivotRef]
  let body :=
    SSBX.Foundation.Wen.Native.SurfaceExpr.if0
      (sPrimApp .null [xsRef])
      .nil
      (SSBX.Foundation.Wen.Native.SurfaceExpr.if0
        test
        (sPrimApp .cons [head, recursive])
        recursive)
  some (.define filterName (sLambdaMany [pivot, xs] body), table)

def compileHelperForms? (table : NameTable) :
    Option (List NativeSurfaceTopForm8 × NameTable) := do
  let (appendForm, table) ← compileAppendHelper? table
  let (filterLeForm, table) ← compileFilterHelper?
    helperFilterLeName (.numLe : SSBX.Foundation.Wen.Native.Prim 8) false table
  let (filterGtForm, table) ← compileFilterHelper?
    helperFilterGtName (.numLt : SSBX.Foundation.Wen.Native.Prim 8) true table
  some ([appendForm, filterLeForm, filterGtForm], table)

def compileParsedSourceToSurfaceTopForms? (parsed : ParsedSource) (input : List Nat) :
    Option (List NativeSurfaceTopForm8) := do
  let (helpers, table) ← compileHelperForms? NameTable.empty
  let (mainForm, mainName, _) ← compileFunction? table parsed.main
  let runForm : NativeSurfaceTopForm8 :=
    .expr (sCall mainName [sNatList input])
  some (helpers ++ [mainForm, runForm])

def compileParsedSourceToTopForms? (parsed : ParsedSource) (input : List Nat) :
    Option (List NativeTopForm8) := do
  let forms ← compileParsedSourceToSurfaceTopForms? parsed input
  forms.mapM SSBX.Foundation.Wen.Native.SurfaceTopForm.elaborate

def chooseInput? (parsed : ParsedSource) (overrideInput? : Option (List Nat)) :
    Option (List Nat) :=
  match overrideInput? with
  | some input => some input
  | none => parsed.sample?

def compileSourceToTopForms? (source : String) (overrideInput? : Option (List Nat) := none) :
    Option (List NativeTopForm8) := do
  let parsed ← parseSource? source
  let input ← chooseInput? parsed overrideInput?
  compileParsedSourceToTopForms? parsed input

def decodeNativeNatList? : NativeValue8 → Option (List Nat)
  | .nil => some []
  | .cons (.num value) rest => do
      let values ← decodeNativeNatList? rest
      some (value :: values)
  | _ => none

def runFuelForInput (input : List Nat) : Nat :=
  input.length * input.length * 128 + 512

def runParsedSource? (parsed : ParsedSource) (input : List Nat) : Option RunResult := do
  let forms ← compileParsedSourceToTopForms? parsed input
  let (_, value) ←
    SSBX.Foundation.Wen.Native.Program.evalTopFormsFinalFuel
      (n := 8) (runFuelForInput input) [] forms
  let output ← decodeNativeNatList? value
  some { functionName := parsed.main.name, input := input, output := output }

def runSource? (source : String) (overrideInput? : Option (List Nat) := none) :
    Option RunResult := do
  let parsed ← parseSource? source
  let input ← chooseInput? parsed overrideInput?
  runParsedSource? parsed input

def natListShow (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

def runResultShow (result : RunResult) : String :=
  String.intercalate "\n"
    [ "algorithm=" ++ result.functionName
    , "input=" ++ natListShow result.input
    , "=> " ++ natListShow result.output
    ]

def quicksortSourceExample : String :=
  String.intercalate "\n"
    [ "法曰速排。"
    , "受列。"
    , "若列空，归空。"
    , "取列之首，名曰枢。"
    , "取列之余，名曰余。"
    , "令小者为择（不大于枢）余。"
    , "令大者为择（大于枢）余。"
    , "归并速排小者、结枢空、速排大者。"
    , "试以三、一、二、一。"
    ]

def parserSmoke : Bool :=
  match parseSource? quicksortSourceExample with
  | some parsed =>
      parsed.main.name == "速排"
        && parsed.main.params == ["列"]
        && parsed.main.body.length == 6
        && parsed.sample? == some [3, 1, 2, 1]
  | none => false

theorem parser_smoke :
    parserSmoke = true := by
  native_decide

def compileQuicksortToTopFormsOk : Bool :=
  match compileSourceToTopForms? quicksortSourceExample with
  | some _ => true
  | none => false

theorem compile_quicksort_to_topforms :
    compileQuicksortToTopFormsOk = true := by
  native_decide

theorem runSource_quicksort_example :
    runSource? quicksortSourceExample = some
      { functionName := "速排", input := [3, 1, 2, 1], output := [1, 1, 2, 3] } := by
  native_decide

theorem runSource_quicksort_override :
    runSource? quicksortSourceExample (some [5, 4, 6]) = some
      { functionName := "速排", input := [5, 4, 6], output := [4, 5, 6] } := by
  native_decide

end SSBX.Foundation.Wen.WenyanAlgorithms
