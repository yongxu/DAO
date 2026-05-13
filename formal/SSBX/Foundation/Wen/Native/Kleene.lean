/-
# Wen.Native.Kleene -- native recursion-theorem target interfaces

This file states the native Wen targets needed to replace external recursion
axioms later.  It proves only the target assembly theorem: once fixed points
and Boolean inversion compilers are supplied, the native Kleene inverter follows.
-/

import SSBX.Foundation.Wen.Native.Program

namespace SSBX.Foundation.Wen.Native

namespace Kleene

/-- Native one-cell input convention. -/
def runOn {n : Nat} (program : Expr n) (input : Cell n) : Expr n :=
  .app program (.cell input)

/-- Pair an object program with its one-cell input as native data. -/
def programInputExpr {n : Nat} (program : Expr n) (input : Cell n) : Expr n :=
  .cons (.quote program) (.cell input)

/-- Run a meta-program on `(program, input)` encoded as native data. -/
def runWithProgramInput {n : Nat}
    (runner program : Expr n) (input : Cell n) : Expr n :=
  .app runner (programInputExpr program input)

/-- A native program halts on one input when fuelled evaluation returns a value. -/
def Halts {n : Nat} (program : Expr n) (input : Cell n) : Prop :=
  ∃ fuel value, evalFuel fuel [] (runOn program input) = some value

/-- A native meta-program halts on an encoded `(program, input)` pair. -/
def HaltsWithProgramInput {n : Nat}
    (runner program : Expr n) (input : Cell n) : Prop :=
  ∃ fuel value, evalFuel fuel [] (runWithProgramInput runner program input) = some value

def BoolFromValue? {n : Nat} : Value n → Option Bool
  | .bool value => some value
  | _ => none

def BoolOutputDefined {n : Nat} (value : Value n) : Prop :=
  ∃ b, BoolFromValue? value = some b

/-- A native decider program computes the supplied Lean Boolean predicate. -/
def Decides {n : Nat}
    (decider : Expr n) (decide : Expr n → Cell n → Bool) : Prop :=
  ∀ (program : Expr n) (input : Cell n),
    ∃ fuel,
      evalFuel fuel [] (runWithProgramInput decider program input) =
        some (.bool (decide program input))

/-- A Lean Boolean predicate is native-computable when some native program decides it. -/
def Computable {n : Nat} (decide : Expr n → Cell n → Bool) : Prop :=
  ∃ decider : Expr n, Decides decider decide

/-- Computable-restricted native Kleene inverter target. -/
def NativeKleeneInverter (n : Nat) : Prop :=
  ∀ (decide : Expr n → Cell n → Bool),
    Computable decide →
    ∃ program : Expr n, ∀ input : Cell n,
      Halts program input ↔ decide program input = false

/-- Universal interpreter target for native program/input pairs. -/
def UniversalSpec {n : Nat} (universal : Expr n) : Prop :=
  ∀ (program : Expr n) (input : Cell n),
    Halts program input ↔ HaltsWithProgramInput universal program input

def UniversalExists (n : Nat) : Prop :=
  ∃ universal : Expr n, UniversalSpec universal

/-- s-m-n target: specialize a native meta-program to an object program. -/
def SmnSpec {n : Nat} (subst : Expr n → Expr n → Expr n) : Prop :=
  ∀ (runner program : Expr n) (input : Cell n),
    Halts (subst runner program) input ↔ HaltsWithProgramInput runner program input

def SmnExists (n : Nat) : Prop :=
  ∃ subst : Expr n → Expr n → Expr n, SmnSpec subst

/-- A fixed point for a native program transformer. -/
def FixedPointSpec {n : Nat} (transform program : Expr n) : Prop :=
  ∀ input : Cell n,
    Halts program input ↔ HaltsWithProgramInput transform program input

def FixedPointExists (n : Nat) : Prop :=
  ∀ transform : Expr n, ∃ program : Expr n, FixedPointSpec transform program

/-- Compiler target for inverting a computable Boolean decider into halting. -/
def BoolInverterCompilerExists (n : Nat) : Prop :=
  ∀ (decide : Expr n → Cell n → Bool),
    Computable decide →
    ∃ inverter : Expr n, ∀ (program : Expr n) (input : Cell n),
      HaltsWithProgramInput inverter program input ↔ decide program input = false

theorem native_kleene_from_fixedpoint_and_inverter {n : Nat}
    (hFixed : FixedPointExists n)
    (hInvert : BoolInverterCompilerExists n) :
    NativeKleeneInverter n := by
  intro decide hComp
  rcases hInvert decide hComp with ⟨inverter, hInverter⟩
  rcases hFixed inverter with ⟨program, hProgram⟩
  refine ⟨program, ?_⟩
  intro input
  exact (hProgram input).trans (hInverter program input)

def FixedPointFromPrimitives (n : Nat) : Prop :=
  UniversalExists n → SmnExists n → FixedPointExists n

def BoolInverterFromUniversal (n : Nat) : Prop :=
  UniversalExists n → BoolInverterCompilerExists n

def KleeneFromPrimitives (n : Nat) : Prop :=
  UniversalExists n → SmnExists n → NativeKleeneInverter n

theorem native_kleene_from_primitives {n : Nat}
    (hFixed : FixedPointFromPrimitives n)
    (hInvert : BoolInverterFromUniversal n) :
    KleeneFromPrimitives n := by
  intro hUniversal hSmn
  exact native_kleene_from_fixedpoint_and_inverter
    (hFixed hUniversal hSmn) (hInvert hUniversal)

theorem halts_identity_cell {n : Nat} :
    Halts (.lam (.var 0) : Expr n) sampleCell := by
  exact ⟨3, .cell sampleCell, rfl⟩

theorem native_kleene_target_summary (n : Nat) :
    (FixedPointExists n → BoolInverterCompilerExists n → NativeKleeneInverter n)
    ∧ (FixedPointFromPrimitives n → BoolInverterFromUniversal n → KleeneFromPrimitives n)
    ∧ Halts (.lam (.var 0) : Expr n) sampleCell :=
  ⟨native_kleene_from_fixedpoint_and_inverter, native_kleene_from_primitives,
    halts_identity_cell⟩

end Kleene

end SSBX.Foundation.Wen.Native
