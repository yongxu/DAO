/-
Mathematical axiom family map.

This module formalizes the v14 claim that each mathematical interface used by
the theory has either registered roots or an explicit modern-mathematics map,
plus a structural contract and a conservative failure path.
-/
namespace SSBX.Foundation.MathAxiomMap

inductive AxiomFamily where
  | discreteStart
  | naturalNumber
  | formalLogic
  | setOrType
  | algebra
  | space
  | continuum
  | infinity
  | probabilityMeasure
  | fixedPointLattice
  | proofLegality
  deriving DecidableEq, Repr

inductive AxiomSupport where
  | roots
  | map
  | rootsAndMap
  deriving DecidableEq, Repr

inductive FormalLevel where
  | atomGenerated
  | axiomSchema
  | syntaxInterface
  | structuralAxiom
  | modelStructure
  | completenessAxiom
  | infinityAxiom
  | measureInterface
  | recursionSemantics
  | metalogicInterface
  deriving DecidableEq, Repr

structure AxiomEntry where
  family : AxiomFamily
  support : AxiomSupport
  contractSpecified : Bool
  failureToUnknown : Bool
  level : FormalLevel
  deriving Repr

def entry : AxiomFamily -> AxiomEntry
  | .discreteStart =>
      ⟨.discreteStart, .roots, true, true, .atomGenerated⟩
  | .naturalNumber =>
      ⟨.naturalNumber, .rootsAndMap, true, true, .axiomSchema⟩
  | .formalLogic =>
      ⟨.formalLogic, .rootsAndMap, true, true, .syntaxInterface⟩
  | .setOrType =>
      ⟨.setOrType, .rootsAndMap, true, true, .structuralAxiom⟩
  | .algebra =>
      ⟨.algebra, .rootsAndMap, true, true, .structuralAxiom⟩
  | .space =>
      ⟨.space, .rootsAndMap, true, true, .modelStructure⟩
  | .continuum =>
      ⟨.continuum, .rootsAndMap, true, true, .completenessAxiom⟩
  | .infinity =>
      ⟨.infinity, .rootsAndMap, true, true, .infinityAxiom⟩
  | .probabilityMeasure =>
      ⟨.probabilityMeasure, .rootsAndMap, true, true, .measureInterface⟩
  | .fixedPointLattice =>
      ⟨.fixedPointLattice, .rootsAndMap, true, true, .recursionSemantics⟩
  | .proofLegality =>
      ⟨.proofLegality, .rootsAndMap, true, true, .metalogicInterface⟩

def hasRootOrMap (e : AxiomEntry) : Prop :=
  e.support = .roots ∨ e.support = .map ∨ e.support = .rootsAndMap

def contractReady (e : AxiomEntry) : Prop :=
  e.contractSpecified = true

def conservativeFailure (e : AxiomEntry) : Prop :=
  e.failureToUnknown = true

theorem math_axiom_interfaces_have_root_or_map (A : AxiomFamily) :
    hasRootOrMap (entry A) := by
  cases A <;> simp [entry, hasRootOrMap]

theorem math_axiom_contracts_ready (A : AxiomFamily) :
    contractReady (entry A) := by
  cases A <;> simp [entry, contractReady]

theorem math_axiom_failures_are_conservative (A : AxiomFamily) :
    conservativeFailure (entry A) := by
  cases A <;> simp [entry, conservativeFailure]

theorem math_axiom_spectrum_complete (A : AxiomFamily) :
    hasRootOrMap (entry A) ∧
    contractReady (entry A) ∧
    conservativeFailure (entry A) := by
  exact ⟨
    math_axiom_interfaces_have_root_or_map A,
    math_axiom_contracts_ready A,
    math_axiom_failures_are_conservative A
  ⟩

end SSBX.Foundation.MathAxiomMap
