/-
# Wen.V4Kernel.LispProgram -- program-level runner

The evaluator in `LispEval` runs one expression or one top-level form.  This
module adds the launch boundary for the V4-native Lisp interpreter: immutable
top-level programs, surface programs, and reader-backed string programs.
-/

import SSBX.Foundation.Wen.V4Kernel.LispReader

namespace SSBX.Foundation.Wen.V4Kernel

namespace LispProgram

/-! ## Core top-level programs -/

def evalTopFormsFuel :
    Nat → GlobalEnv → List TopForm → Option (GlobalEnv × List Value)
  | _, global, [] => some (global, [])
  | fuel, global, form :: rest => do
      let (global', value) ← evalTopFuel fuel global form
      let (global'', values) ← evalTopFormsFuel fuel global' rest
      some (global'', value :: values)

def evalTopFormsFinalFuel
    (fuel : Nat) (global : GlobalEnv) (forms : List TopForm) :
    Option (GlobalEnv × Value) := do
  let (global', values) ← evalTopFormsFuel fuel global forms
  match values.reverse with
  | [] => some (global', .nil)
  | final :: _ => some (global', final)

/-! ## Surface and reader programs -/

def evalSurfaceFormsFuel :
    Nat → GlobalEnv → List SurfaceTopForm → Option (GlobalEnv × List Value)
  | _, global, [] => some (global, [])
  | fuel, global, form :: rest => do
      let (global', value) ← SurfaceTopForm.evalFuel fuel global form
      let (global'', values) ← evalSurfaceFormsFuel fuel global' rest
      some (global'', value :: values)

def readTopStrings : List String → Option (List SurfaceTopForm)
  | [] => some []
  | source :: rest => do
      let form ← LispReader.readTopString source
      let forms ← readTopStrings rest
      some (form :: forms)

def readEvalProgramStrings
    (fuel : Nat) (global : GlobalEnv) (sources : List String) :
    Option (GlobalEnv × List Value) := do
  let forms ← readTopStrings sources
  evalSurfaceFormsFuel fuel global forms

def readEvalProgramFinal
    (fuel : Nat) (global : GlobalEnv) (sources : List String) :
    Option (GlobalEnv × Value) := do
  let (global', values) ← readEvalProgramStrings fuel global sources
  match values.reverse with
  | [] => some (global', .nil)
  | final :: _ => some (global', final)

/-! ## Smoke programs -/

def defineChainProgram : List TopForm :=
  [ .define .qian (.num 10)
  , .define .kun (.app (.prim .add) (Expr.list [.ref .qian, .num 32]))
  , .expr (.ref .kun)
  ]

theorem eval_defineChainProgram :
    evalTopFormsFuel 8 [] defineChainProgram =
      some ([(.kun, .num 42), (.qian, .num 10)], [.num 10, .num 42, .num 42]) :=
  rfl

theorem eval_defineChainProgram_final :
    evalTopFormsFinalFuel 8 [] defineChainProgram =
      some ([(.kun, .num 42), (.qian, .num 10)], .num 42) :=
  rfl

def readerDefineChain : List String :=
  ["(define 乾 10)", "(define 坤 (add 乾 32))", "坤"]

#eval readEvalProgramFinal 8 [] readerDefineChain

theorem lisp_program_summary :
    evalTopFormsFuel 8 [] defineChainProgram =
      some ([(.kun, .num 42), (.qian, .num 10)], [.num 10, .num 42, .num 42])
    ∧ evalTopFormsFinalFuel 8 [] defineChainProgram =
      some ([(.kun, .num 42), (.qian, .num 10)], .num 42) :=
  ⟨eval_defineChainProgram, eval_defineChainProgram_final⟩

end LispProgram

end SSBX.Foundation.Wen.V4Kernel

