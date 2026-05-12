/-
# Wen.V4Kernel.LispAlgorithms -- verified nontrivial interpreter workloads

These examples exercise the launch-boundary interpreter: top-level programs,
lambda, lexical shadowing, conditionals, lists, quote/eval, arithmetic, and
64-word path execution.
-/

import SSBX.Foundation.Wen.V4Kernel.LispTrace

namespace SSBX.Foundation.Wen.V4Kernel

namespace LispAlgorithms

/-! ## Higher-order and homoiconic algorithms -/

def evalQuotedLambdaAdd : Expr :=
  .app (.prim .eval)
    (.quote
      (.app
        (.lam (.app (.prim .add) (Expr.list [.var 0, .num 5])))
        (.num 37)))

theorem evalQuotedLambdaAdd_ok :
    evalFuel 40 [] evalQuotedLambdaAdd = some (.num 42) :=
  rfl

def conditionalWordReturn : Expr :=
  .app
    (.lam
      (.if0
        (.app (.prim .numEq) (Expr.list [.var 0, .num 0]))
        (.quote (.symbol .kun))
        (.app (.prim .wordCompose) (Expr.list [.quote (.symbol .kun), .quote (.symbol .kun)]))))
    (.num 3)

theorem conditionalWordReturn_ok :
    evalFuel 40 [] conditionalWordReturn = some (.symbol .qian) :=
  rfl

/-! ## List algorithms -/

def listTailAlgorithm : Expr :=
  .app (.prim .cdr)
    (Expr.list
      [ .app (.prim .cons)
          (Expr.list
            [ .num 1
            , .app (.prim .cons) (Expr.list [.num 2, .nil])
            ])
      ])

theorem listTailAlgorithm_ok :
    evalFuel 40 [] listTailAlgorithm = some (.cons (.num 2) .nil) :=
  rfl

def listHeadAfterTailAlgorithm : Expr :=
  .app (.prim .car) (Expr.list [listTailAlgorithm])

theorem listHeadAfterTailAlgorithm_ok :
    evalFuel 80 [] listHeadAfterTailAlgorithm = some (.num 2) :=
  rfl

/-! ## Program-level and reader-backed workloads -/

def readerFunctionProgram : List String :=
  ["(define 乾 (lambda (坤) (add 坤 5)))", "(乾 37)"]

#eval LispProgram.readEvalProgramFinal 40 [] readerFunctionProgram

def surfaceFunctionProgram : List SurfaceTopForm :=
  [ .define .qian
      (.lambda .kun (.app (.prim .add) [.ref .kun, .num 5]))
  , .expr (.app (.ref .qian) [.num 37])
  ]

theorem surfaceFunctionProgram_ok :
    LispProgram.evalSurfaceFormsFuel 40 [] surfaceFunctionProgram =
      some
        ( [ (.qian, .closure [] []
              (.app (.prim .add) (Expr.list [.var 0, .num 5])))
          ]
        , [ .closure [] [] (.app (.prim .add) (Expr.list [.var 0, .num 5]))
          , .num 42
          ]
        ) :=
  rfl

/-! ## 64-word path workload -/

def pathAlgorithm : Expr :=
  LispTrace.wordPathExprLeft .qian LispTrace.qianLoopOps

theorem pathAlgorithm_ok :
    evalFuel 32 [] pathAlgorithm = some (.symbol .qian) :=
  LispTrace.eval_wordPathExprLeft_qianLoop

theorem algorithms_summary :
    evalFuel 40 [] evalQuotedLambdaAdd = some (.num 42)
    ∧ evalFuel 40 [] conditionalWordReturn = some (.symbol .qian)
    ∧ evalFuel 40 [] listTailAlgorithm = some (.cons (.num 2) .nil)
    ∧ evalFuel 80 [] listHeadAfterTailAlgorithm = some (.num 2)
    ∧ evalFuel 32 [] pathAlgorithm = some (.symbol .qian) :=
  ⟨evalQuotedLambdaAdd_ok, conditionalWordReturn_ok, listTailAlgorithm_ok,
   listHeadAfterTailAlgorithm_ok, pathAlgorithm_ok⟩

end LispAlgorithms

end SSBX.Foundation.Wen.V4Kernel

