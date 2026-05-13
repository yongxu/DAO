/-
# Wen.Native.Program -- native top-level program runner
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

/-! ## Smoke programs -/

def defineChainProgram {n : Nat} : List (TopForm n) :=
  [ .define sampleCell (.num 10)
  , .define (Vn.xor sampleCell sampleCell) (.app (.prim .add) (Expr.list [.ref sampleCell, .num 32]))
  , .expr (.ref (Vn.xor sampleCell sampleCell))
  ]

theorem eval_defineChainProgram {n : Nat} :
    evalTopFormsFuel 8 [] (defineChainProgram : List (TopForm n)) =
      some ([(Vn.xor sampleCell sampleCell, .num 42), (sampleCell, .num 10)],
        [.num 10, .num 42, .num 42]) :=
  by
    simp [defineChainProgram, evalTopFormsFuel, evalTopFuel, evalFuelG,
      evalListFuelG, valueList?, applyPrim, Expr.list, GlobalEnv.lookup]

theorem eval_defineChainProgram_final {n : Nat} :
    evalTopFormsFinalFuel 8 [] (defineChainProgram : List (TopForm n)) =
      some ([(Vn.xor sampleCell sampleCell, .num 42), (sampleCell, .num 10)], .num 42) :=
  by
    simp [evalTopFormsFinalFuel, eval_defineChainProgram]

theorem native_program_summary {n : Nat} :
    evalTopFormsFuel 8 [] (defineChainProgram : List (TopForm n)) =
      some ([(Vn.xor sampleCell sampleCell, .num 42), (sampleCell, .num 10)],
        [.num 10, .num 42, .num 42])
    ∧ evalTopFormsFinalFuel 8 [] (defineChainProgram : List (TopForm n)) =
      some ([(Vn.xor sampleCell sampleCell, .num 42), (sampleCell, .num 10)], .num 42) :=
  ⟨eval_defineChainProgram, eval_defineChainProgram_final⟩

end Program

end SSBX.Foundation.Wen.Native
