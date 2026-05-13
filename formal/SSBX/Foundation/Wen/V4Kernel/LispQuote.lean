/-
# Wen.V4Kernel.LispQuote -- homoiconic expression encoding

This file makes program-as-data explicit for the V4-native Lisp kernel.
-/

import SSBX.Foundation.Wen.V4Kernel.LispEval

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-! ## V4Tree expression encoding -/

def pairTree (left right : V4Tree) : V4Tree :=
  .node .dao left right

def encodeNat : Nat → V4Tree
  | 0 => .atom .dao
  | n + 1 => .node .cuo (encodeNat n) V4Tree.unit

def decodeNat : V4Tree → Option Nat
  | .atom .dao => some 0
  | .node .cuo rest (.atom .dao) => do
      let n ← decodeNat rest
      some (n + 1)
  | _ => none

@[simp] theorem decodeNat_encodeNat (n : Nat) :
    decodeNat (encodeNat n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change decodeNat (.node .cuo (encodeNat n) (.atom .dao)) = some (n + 1)
      simp [decodeNat, ih]

def encodePrim : Prim → V4Tree
  | .v4Compose => .atom .dao
  | .v4Eq => .atom .cuo
  | .wordCompose => .atom .zong
  | .wordEq => .atom .cuoZong
  | .numEq => .node .dao V4Tree.unit V4Tree.unit
  | .succ => .node .cuo V4Tree.unit V4Tree.unit
  | .pred => .node .zong V4Tree.unit V4Tree.unit
  | .add => .node .cuoZong V4Tree.unit V4Tree.unit
  | .cons => .node .dao (.atom .cuo) V4Tree.unit
  | .car => .node .cuo (.atom .cuo) V4Tree.unit
  | .cdr => .node .zong (.atom .cuo) V4Tree.unit
  | .null => .node .cuoZong (.atom .cuo) V4Tree.unit
  | .atom => .node .dao (.atom .zong) V4Tree.unit
  | .isSymbol => .node .cuo (.atom .zong) V4Tree.unit
  | .isNumber => .node .zong (.atom .zong) V4Tree.unit
  | .eval => .node .cuoZong (.atom .zong) V4Tree.unit
  | .r5Is => .node .dao (.atom .cuoZong) V4Tree.unit
  | .r5ToR4 => .node .cuo (.atom .cuoZong) V4Tree.unit
  | .r5Compose => .node .zong (.atom .cuoZong) V4Tree.unit
  | .r5Coords => .node .cuoZong (.atom .cuoZong) V4Tree.unit

def decodePrim : V4Tree → Option Prim
  | .atom .dao => some .v4Compose
  | .atom .cuo => some .v4Eq
  | .atom .zong => some .wordCompose
  | .atom .cuoZong => some .wordEq
  | .node .dao (.atom .dao) (.atom .dao) => some .numEq
  | .node .cuo (.atom .dao) (.atom .dao) => some .succ
  | .node .zong (.atom .dao) (.atom .dao) => some .pred
  | .node .cuoZong (.atom .dao) (.atom .dao) => some .add
  | .node .dao (.atom .cuo) (.atom .dao) => some .cons
  | .node .cuo (.atom .cuo) (.atom .dao) => some .car
  | .node .zong (.atom .cuo) (.atom .dao) => some .cdr
  | .node .cuoZong (.atom .cuo) (.atom .dao) => some .null
  | .node .dao (.atom .zong) (.atom .dao) => some .atom
  | .node .cuo (.atom .zong) (.atom .dao) => some .isSymbol
  | .node .zong (.atom .zong) (.atom .dao) => some .isNumber
  | .node .cuoZong (.atom .zong) (.atom .dao) => some .eval
  | .node .dao (.atom .cuoZong) (.atom .dao) => some .r5Is
  | .node .cuo (.atom .cuoZong) (.atom .dao) => some .r5ToR4
  | .node .zong (.atom .cuoZong) (.atom .dao) => some .r5Compose
  | .node .cuoZong (.atom .cuoZong) (.atom .dao) => some .r5Coords
  | _ => none

@[simp] theorem decodePrim_encodePrim (p : Prim) :
    decodePrim (encodePrim p) = some p := by
  cases p <;> rfl

def encodeWord64 (word : Word64) : V4Tree :=
  .node .dao (.atom word.first) (.node .dao (.atom word.second) (.atom word.third))

def decodeWord64 : V4Tree → Option Word64
  | .node .dao (.atom first) (.node .dao (.atom second) (.atom third)) =>
      some ⟨first, second, third⟩
  | _ => none

@[simp] theorem decodeWord64_encodeWord64 (word : Word64) :
    decodeWord64 (encodeWord64 word) = some word := by
  cases word
  rfl

/-- Encode an expression as a V4-labelled tree. -/
def encodeExpr : Expr → V4Tree
  | .atom g => .node .cuoZong (.atom .dao) (.atom g)
  | .symbol name => .node .cuoZong (.node .dao (.atom .zong) (.atom .cuo)) (encodeWord64 name)
  | .num n => .node .cuoZong (.node .dao (.atom .zong) (.atom .zong)) (encodeNat n)
  | .nil => .node .cuoZong (.atom .cuo) V4Tree.unit
  | .cons head tail =>
      .node .cuoZong (.atom .zong) (pairTree (encodeExpr head) (encodeExpr tail))
  | .quote body => .node .cuoZong (.atom .cuoZong) (encodeExpr body)
  | .var index => .node .cuoZong (pairTree V4Tree.unit V4Tree.unit) (encodeNat index)
  | .ref name => .node .cuoZong (.node .dao (.atom .zong) (.atom .cuoZong)) (encodeWord64 name)
  | .lam body => .node .cuoZong (.node .cuo V4Tree.unit V4Tree.unit) (encodeExpr body)
  | .app fn arg =>
      .node .cuoZong (.node .zong V4Tree.unit V4Tree.unit)
        (pairTree (encodeExpr fn) (encodeExpr arg))
  | .if0 test thenBranch elseBranch =>
      .node .cuoZong (.node .cuoZong V4Tree.unit V4Tree.unit)
        (pairTree (encodeExpr test) (pairTree (encodeExpr thenBranch) (encodeExpr elseBranch)))
  | .prim p => .node .cuoZong (pairTree (.atom .cuo) V4Tree.unit) (encodePrim p)

/-- Decode an expression from the V4-labelled tree format above. -/
def decodeExpr : V4Tree → Option Expr
  | .node .cuoZong (.atom .dao) (.atom g) => some (.atom g)
  | .node .cuoZong (.node .dao (.atom .zong) (.atom .cuo)) wordCode => do
      let word ← decodeWord64 wordCode
      some (.symbol word)
  | .node .cuoZong (.node .dao (.atom .zong) (.atom .zong)) natCode => do
      let n ← decodeNat natCode
      some (.num n)
  | .node .cuoZong (.atom .cuo) (.atom .dao) => some .nil
  | .node .cuoZong (.atom .zong) (.node .dao head tail) => do
      let h ← decodeExpr head
      let t ← decodeExpr tail
      some (.cons h t)
  | .node .cuoZong (.atom .cuoZong) body => do
      let b ← decodeExpr body
      some (.quote b)
  | .node .cuoZong (.node .dao (.atom .dao) (.atom .dao)) index => do
      let n ← decodeNat index
      some (.var n)
  | .node .cuoZong (.node .dao (.atom .zong) (.atom .cuoZong)) wordCode => do
      let word ← decodeWord64 wordCode
      some (.ref word)
  | .node .cuoZong (.node .cuo (.atom .dao) (.atom .dao)) body => do
      let b ← decodeExpr body
      some (.lam b)
  | .node .cuoZong (.node .zong (.atom .dao) (.atom .dao)) (.node .dao fn arg) => do
      let f ← decodeExpr fn
      let a ← decodeExpr arg
      some (.app f a)
  | .node .cuoZong (.node .cuoZong (.atom .dao) (.atom .dao))
      (.node .dao test (.node .dao thenBranch elseBranch)) => do
      let c ← decodeExpr test
      let t ← decodeExpr thenBranch
      let e ← decodeExpr elseBranch
      some (.if0 c t e)
  | .node .cuoZong (.node .dao (.atom .cuo) (.atom .dao)) primCode => do
      let p ← decodePrim primCode
      some (.prim p)
  | _ => none

@[simp] theorem decodeExpr_encodeExpr (expr : Expr) :
    decodeExpr (encodeExpr expr) = some expr := by
  exact
    Expr.rec
      (motive_1 := fun e => decodeExpr (encodeExpr e) = some e)
      (motive_2 := fun _ => True)
      (motive_3 := fun _ => True)
      (motive_4 := fun _ => True)
      (motive_5 := fun _ => True)
      (fun _ => rfl)
      (fun name => by simp [encodeExpr, decodeExpr])
      (fun n => by simp [encodeExpr, decodeExpr])
      rfl
      (fun head tail ihHead ihTail => by
        simp [encodeExpr, decodeExpr, pairTree, ihHead, ihTail])
      (fun body ih => by
        simp [encodeExpr, decodeExpr, ih])
      (fun index => by
        simp [encodeExpr, decodeExpr, pairTree, V4Tree.unit])
      (fun name => by simp [encodeExpr, decodeExpr])
      (fun body ih => by
        simp [encodeExpr, decodeExpr, V4Tree.unit, ih])
      (fun fn arg ihFn ihArg => by
        simp [encodeExpr, decodeExpr, pairTree, V4Tree.unit, ihFn, ihArg])
      (fun test thenBranch elseBranch ihTest ihThen ihElse => by
        simp [encodeExpr, decodeExpr, pairTree, V4Tree.unit, ihTest, ihThen, ihElse])
      (fun p => by
        simp [encodeExpr, decodeExpr, pairTree, V4Tree.unit])
      (fun _ => True.intro)
      (fun _ => True.intro)
      (fun _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      (fun _ _ _ _ _ _ => True.intro)
      (fun _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      (fun _ _ _ => True.intro)
      expr

def encodeTopForm : TopForm → V4Tree
  | .expr body => .node .dao (encodeExpr body) V4Tree.unit
  | .define name body => .node .cuo (encodeWord64 name) (encodeExpr body)

def decodeTopForm : V4Tree → Option TopForm
  | .node .dao body (.atom .dao) => do
      let expr ← decodeExpr body
      some (.expr expr)
  | .node .cuo nameCode body => do
      let name ← decodeWord64 nameCode
      let expr ← decodeExpr body
      some (.define name expr)
  | _ => none

@[simp] theorem decodeTopForm_encodeTopForm (form : TopForm) :
    decodeTopForm (encodeTopForm form) = some form := by
  cases form with
  | expr body =>
      simp [encodeTopForm, decodeTopForm, V4Tree.unit]
  | define name body =>
      simp [encodeTopForm, decodeTopForm]

/-! ## Quoted values back to expressions -/

def exprAsValue (expr : Expr) : Value :=
  quoteValue expr

@[simp] theorem valueAsExpr_exprAsValue (expr : Expr) :
    valueAsExpr (exprAsValue expr) = some expr := by
  exact
    Expr.rec
      (motive_1 := fun e => valueAsExpr (exprAsValue e) = some e)
      (motive_2 := fun _ => True)
      (motive_3 := fun _ => True)
      (motive_4 := fun _ => True)
      (motive_5 := fun _ => True)
      (fun _ => rfl)
      (fun _ => rfl)
      (fun _ => rfl)
      rfl
      (fun head tail ihHead ihTail => by
        change valueAsExpr (quoteValue head) = some head at ihHead
        change valueAsExpr (quoteValue tail) = some tail at ihTail
        simp [exprAsValue, quoteValue, taggedQuote, quoteTag, valueAsExpr, ihHead, ihTail])
      (fun body ih => by
        change valueAsExpr (quoteValue body) = some body at ih
        simp [exprAsValue, quoteValue, taggedQuote, quoteTag, valueAsExpr, ih])
      (fun index => by
        simp [exprAsValue, quoteValue, taggedQuote, quoteTag, valueAsExpr])
      (fun name => by
        simp [exprAsValue, quoteValue, taggedQuote, quoteTag, valueAsExpr])
      (fun body ih => by
        change valueAsExpr (quoteValue body) = some body at ih
        simp [exprAsValue, quoteValue, taggedQuote, quoteTag, valueAsExpr, ih])
      (fun fn arg ihFn ihArg => by
        change valueAsExpr (quoteValue fn) = some fn at ihFn
        change valueAsExpr (quoteValue arg) = some arg at ihArg
        simp [exprAsValue, quoteValue, taggedQuote, quoteTag, valueAsExpr, ihFn, ihArg])
      (fun test thenBranch elseBranch ihTest ihThen ihElse => by
        change valueAsExpr (quoteValue test) = some test at ihTest
        change valueAsExpr (quoteValue thenBranch) = some thenBranch at ihThen
        change valueAsExpr (quoteValue elseBranch) = some elseBranch at ihElse
        simp [exprAsValue, quoteValue, taggedQuote, quoteTag, valueAsExpr, ihTest, ihThen, ihElse])
      (fun _ => rfl)
      (fun _ => True.intro)
      (fun _ => True.intro)
      (fun _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      (fun _ _ _ _ _ _ => True.intro)
      (fun _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      (fun _ _ _ => True.intro)
      expr

theorem evalFuel_quote_exprAsValue (fuel : Nat) (env : Env) (expr : Expr) :
    evalFuel (fuel + 1) env (.quote expr) = some (exprAsValue expr) := rfl

theorem lisp_quote_summary :
    (∀ expr : Expr, decodeExpr (encodeExpr expr) = some expr)
    ∧ (∀ expr : Expr, valueAsExpr (exprAsValue expr) = some expr)
    ∧ (∀ fuel : Nat, ∀ env : Env, ∀ expr : Expr,
        evalFuel (fuel + 1) env (.quote expr) = some (exprAsValue expr)) :=
  ⟨decodeExpr_encodeExpr, valueAsExpr_exprAsValue, evalFuel_quote_exprAsValue⟩

end SSBX.Foundation.Wen.V4Kernel
