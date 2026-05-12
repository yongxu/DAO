/-
# Wen.V4Kernel.LispTrace -- 64-word path tracing

Path tracing is intentionally outside the evaluator core.  It is a diagnostic
view over `Word64.compose`, with an expression generator that runs the same
path inside the Lisp interpreter.
-/

import SSBX.Foundation.Wen.V4Kernel.LispProgram

namespace SSBX.Foundation.Wen.V4Kernel

namespace LispTrace

structure WordPathStep where
  before : Word64
  op : Word64
  after : Word64
  deriving DecidableEq, Repr

def traceWordPathAux : Word64 → List Word64 → List WordPathStep × Word64
  | current, [] => ([], current)
  | current, op :: rest =>
      let next := Word64.compose current op
      let (steps, final) := traceWordPathAux next rest
      ({ before := current, op := op, after := next } :: steps, final)

def traceWordPath (start : Word64) (ops : List Word64) : List WordPathStep :=
  (traceWordPathAux start ops).1

def traceWordFinal (start : Word64) (ops : List Word64) : Word64 :=
  (traceWordPathAux start ops).2

def traceWordStates (start : Word64) (ops : List Word64) : List Word64 :=
  start :: (traceWordPath start ops).map (fun step => step.after)

def readWordTokens : List String → Option (List Word64)
  | [] => some []
  | token :: rest => do
      let word ← Word64Bridge.wordOfToken token
      let words ← readWordTokens rest
      some (word :: words)

def readWordPathStates (startToken : String) (opTokens : List String) :
    Option (List Word64) := do
  let start ← Word64Bridge.wordOfToken startToken
  let ops ← readWordTokens opTokens
  some (traceWordStates start ops)

def wordPathExpr (start : Word64) : List Word64 → Expr
  | [] => .quote (.symbol start)
  | op :: rest =>
      .app (.prim .wordCompose)
        (Expr.list [wordPathExpr start rest, .quote (.symbol op)])

def wordPathExprLeft (start : Word64) (ops : List Word64) : Expr :=
  ops.foldl
    (fun acc op =>
      .app (.prim .wordCompose) (Expr.list [acc, .quote (.symbol op)]))
    (.quote (.symbol start))

def qianLoopOps : List Word64 :=
  [.kun, .complete, .incomplete]

def qianLoopTrace : List Word64 :=
  traceWordStates .qian qianLoopOps

theorem qianLoopTrace_ok :
    qianLoopTrace = [.qian, .kun, .incomplete, .qian] :=
  rfl

theorem qianLoopFinal_ok :
    traceWordFinal .qian qianLoopOps = .qian :=
  rfl

theorem read_qianLoopTrace_ok :
    readWordPathStates "乾" ["坤", "既济", "未济"] =
      some [.qian, .kun, .incomplete, .qian] := by
  native_decide

theorem eval_wordPathExprLeft_qianLoop :
    evalFuel 32 [] (wordPathExprLeft .qian qianLoopOps) = some (.symbol .qian) :=
  rfl

#eval readWordPathStates "乾" ["坤", "既济", "未济"]
#eval evalFuel 32 [] (wordPathExprLeft .qian qianLoopOps)

theorem lisp_trace_summary :
    traceWordStates .qian qianLoopOps = [.qian, .kun, .incomplete, .qian]
    ∧ traceWordFinal .qian qianLoopOps = .qian
    ∧ readWordPathStates "乾" ["坤", "既济", "未济"] =
      some [.qian, .kun, .incomplete, .qian]
    ∧ evalFuel 32 [] (wordPathExprLeft .qian qianLoopOps) = some (.symbol .qian) :=
  ⟨qianLoopTrace_ok, qianLoopFinal_ok, read_qianLoopTrace_ok,
   eval_wordPathExprLeft_qianLoop⟩

end LispTrace

end SSBX.Foundation.Wen.V4Kernel

