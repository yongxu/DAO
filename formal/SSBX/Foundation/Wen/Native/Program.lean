/-
# Wen.Native.Program -- native top-level program runner

Program evaluation is deliberately small: each top form receives the same fuel
budget, `define` extends the immutable global environment, and the final-value
entrypoint returns the last produced value or `nil` for an empty program.
-/

import SSBX.Foundation.Wen.Native.Reader

namespace SSBX.Foundation.Wen.Native

open SSBX.Foundation.Wen.Layered

namespace Program

/-! ## Core top-level programs -/

def evalTopFormsFuel {n : Nat} :
    Nat → GlobalEnv n → List (TopForm n) → Option (GlobalEnv n × List (Value n))
  | _, global, [] => some (global, [])
  | fuel, global, form :: rest => do
      let (global', value) ← evalTopFuel fuel global form
      let (global'', values) ← evalTopFormsFuel fuel global' rest
      some (global'', value :: values)

def evalTopFormsFinalFuel {n : Nat}
    (fuel : Nat) (global : GlobalEnv n) (forms : List (TopForm n)) :
    Option (GlobalEnv n × Value n) := do
  let (global', values) ← evalTopFormsFuel fuel global forms
  match values.reverse with
  | [] => some (global', .nil)
  | final :: _ => some (global', final)

/-! ## Surface and reader programs -/

def evalSurfaceFormsFuel {n : Nat} :
    Nat → GlobalEnv n → List (SurfaceTopForm n) → Option (GlobalEnv n × List (Value n))
  | _, global, [] => some (global, [])
  | fuel, global, form :: rest => do
      let (global', value) ← SurfaceTopForm.evalFuel fuel global form
      let (global'', values) ← evalSurfaceFormsFuel fuel global' rest
      some (global'', value :: values)

def readTopStrings {n : Nat} : List String → Option (List (SurfaceTopForm n))
  | [] => some []
  | source :: rest => do
      let form ← Reader.readTopString source
      let forms ← readTopStrings rest
      some (form :: forms)

def readEvalProgramStrings {n : Nat}
    (fuel : Nat) (global : GlobalEnv n) (sources : List String) :
    Option (GlobalEnv n × List (Value n)) := do
  let forms ← readTopStrings sources
  evalSurfaceFormsFuel fuel global forms

def readEvalProgramFinal {n : Nat}
    (fuel : Nat) (global : GlobalEnv n) (sources : List String) :
    Option (GlobalEnv n × Value n) := do
  let (global', values) ← readEvalProgramStrings fuel global sources
  match values.reverse with
  | [] => some (global', .nil)
  | final :: _ => some (global', final)

/-! ## Reference programs -/

def defineChain {n : Nat} : List (TopForm n) :=
  [ .define originCell (.num 10)
  , .define (Vn.xor originCell originCell) (.app (.prim .add) (Expr.list [.ref originCell, .num 32]))
  , .expr (.ref (Vn.xor originCell originCell))
  ]

theorem eval_defineChain {n : Nat} :
    evalTopFormsFuel 8 [] (defineChain : List (TopForm n)) =
      some ([(Vn.xor originCell originCell, .num 42), (originCell, .num 10)],
        [.num 10, .num 42, .num 42]) :=
  by
    simp [defineChain, evalTopFormsFuel, evalTopFuel, evalFuelG,
      evalListFuelG, valueList?, applyPrim, Expr.list, GlobalEnv.lookup]

theorem eval_defineChain_final {n : Nat} :
    evalTopFormsFinalFuel 8 [] (defineChain : List (TopForm n)) =
      some ([(Vn.xor originCell originCell, .num 42), (originCell, .num 10)], .num 42) :=
  by
    simp [evalTopFormsFinalFuel, eval_defineChain]

theorem program_runner_laws {n : Nat} :
    evalTopFormsFuel 8 [] (defineChain : List (TopForm n)) =
      some ([(Vn.xor originCell originCell, .num 42), (originCell, .num 10)],
        [.num 10, .num 42, .num 42])
    ∧ evalTopFormsFinalFuel 8 [] (defineChain : List (TopForm n)) =
      some ([(Vn.xor originCell originCell, .num 42), (originCell, .num 10)], .num 42) :=
  ⟨eval_defineChain, eval_defineChain_final⟩

end Program

end SSBX.Foundation.Wen.Native
