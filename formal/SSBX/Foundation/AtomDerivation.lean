/-
Atom derivation layer.

This module records the compression from the full registered single-glyph
roster to a smaller core-glyph layer.  It does not delete the full lexical
registry; it proves every registered atom has a core atom and reaches the
single root through that core atom.
-/
import SSBX.Foundation.MonadRoot

namespace SSBX.Foundation.AtomDerivation

open SSBX.Roster
open SSBX.Foundation.MonadRoot

inductive AtomIntegrationClass where
  | core
  | derived
  | needsSenseSplit
  deriving DecidableEq, Repr

namespace AtomIntegrationClass

def label : AtomIntegrationClass -> String
  | .core => "核心单字"
  | .derived => "可派生单字"
  | .needsSenseSplit => "需义项拆分"

end AtomIntegrationClass

/-- These glyphs are semantically overloaded enough that compression must keep
explicit sense numbers before stronger semantic claims are made. -/
def needsSenseSplitAtoms : List AtomName :=
  [.«生», .«开», .«闭», .«正», .«邪», .«真», .«道», .«人», .«天», .«子», .«之»,
   .«意», .«识», .«心», .«焦», .«聚», .«模», .«理», .«法», .«面», .«气», .«神»,
   .«精», .«性», .«礼», .«信»]

def isCoreGlyph (a : AtomName) : Bool :=
  CoreAtom.glyph (atomCore a) == a

def atomIntegrationClass (a : AtomName) : AtomIntegrationClass :=
  if a ∈ needsSenseSplitAtoms then
    .needsSenseSplit
  else if isCoreGlyph a then
    .core
  else
    .derived

theorem needs_sense_split_atoms_registered {a : AtomName} :
    a ∈ needsSenseSplitAtoms -> a ∈ allAtoms := by
  intro _
  cases a <;> decide

theorem atom_derivation_total (a : AtomName) :
    ∃ c,
      CoreDerives c a ∧
      Reachable «一元» (.core c) ∧
      DirectEdge (.core c) (.atom a) ∧
      Reachable «一元» (.atom a) := by
  exact ⟨atomCore a, rfl, coreRootPath (atomCore a), by simp [DirectEdge], atomRootPath a⟩

theorem atom_integration_class_total (a : AtomName) :
    atomIntegrationClass a = .core ∨
    atomIntegrationClass a = .derived ∨
    atomIntegrationClass a = .needsSenseSplit := by
  cases h1 : atomIntegrationClass a <;> simp

theorem all_atoms_pass_through_core (a : AtomName) :
    Reachable «一元» (.core (atomCore a)) ∧
    DirectEdge (.core (atomCore a)) (.atom a) ∧
    Reachable «一元» (.atom a) :=
  all_atoms_return_through_core a

end SSBX.Foundation.AtomDerivation
