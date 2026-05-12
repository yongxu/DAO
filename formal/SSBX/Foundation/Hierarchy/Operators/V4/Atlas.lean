/-
# Operators · V4.Atlas -- typed registry entries

This is a typed registry for cross-domain readings of the canonical V4
positions.  Entries are data, not proofs that an external domain has been
fully formalized here.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Hexagram
import SSBX.Foundation.Hierarchy.Operators.V4.Preservation
import SSBX.Foundation.Hierarchy.Operators.V4.Turing

namespace SSBX.Foundation.Hierarchy.Operators

namespace V4

inductive AtlasDomain where
  | wen
  | logic
  | category
  | turing
  | pauli
  | galois
  | semiotics
  deriving DecidableEq, Repr

structure AtlasEntry where
  position : V4
  domain : AtlasDomain
  label : String
  reading : String
  preservation : List PreservationLevel
  deriving Repr

/-- Registry markers attached to an atlas row.

These are internal preservation classifications only; they are not proofs that
the named external domain has been fully formalized here. -/
def atlasPreservation (position : V4) (domain : AtlasDomain) : List PreservationLevel :=
  match domain with
  | .wen | .turing | .pauli | .galois | .semiotics => [.setBijection]
  | .category => [.setBijection, .categoricalFunctor]
  | .logic =>
      if preservesAt position .implicationTruth then
        [.setBijection, .implicationTruth]
      else
        [.setBijection]

def coreAtlas : List AtlasEntry :=
  [ ⟨.dao, .wen, "Way", "identity", atlasPreservation .dao .wen⟩
  , ⟨.cuo, .wen, "content duality", "value flip", atlasPreservation .cuo .wen⟩
  , ⟨.zong, .wen, "frame duality", "order flip", atlasPreservation .zong .wen⟩
  , ⟨.cuoZong, .wen, "compound duality", "content and frame flip",
      atlasPreservation .cuoZong .wen⟩
  , ⟨.dao, .logic, "id", "identity", atlasPreservation .dao .logic⟩
  , ⟨.cuo, .logic, "negation", "content duality", atlasPreservation .cuo .logic⟩
  , ⟨.zong, .logic, "implication reversal", "frame duality",
      atlasPreservation .zong .logic⟩
  , ⟨.cuoZong, .logic, "contrapositive", "compound duality",
      atlasPreservation .cuoZong .logic⟩
  , ⟨.dao, .category, "identity functor", "object and arrow identity",
      atlasPreservation .dao .category⟩
  , ⟨.cuo, .category, "opposite content", "object-level dual reading",
      atlasPreservation .cuo .category⟩
  , ⟨.zong, .category, "opposite arrows", "arrow-order dual reading",
      atlasPreservation .zong .category⟩
  , ⟨.cuoZong, .category, "dual opposite", "content and arrow-order dual reading",
      atlasPreservation .cuoZong .category⟩
  , ⟨.dao, .turing, "nop", "no local flip", atlasPreservation .dao .turing⟩
  , ⟨.cuo, .turing, "flip-bit", "tape-symbol flip", atlasPreservation .cuo .turing⟩
  , ⟨.zong, .turing, "flip-dir", "head-direction flip", atlasPreservation .zong .turing⟩
  , ⟨.cuoZong, .turing, "flip-both", "symbol and direction flip",
      atlasPreservation .cuoZong .turing⟩
  , ⟨.dao, .pauli, "I", "identity reading", atlasPreservation .dao .pauli⟩
  , ⟨.cuo, .pauli, "X", "value-flip reading", atlasPreservation .cuo .pauli⟩
  , ⟨.zong, .pauli, "Z", "phase/frame-flip reading", atlasPreservation .zong .pauli⟩
  , ⟨.cuoZong, .pauli, "XZ", "paired value-frame flip reading",
      atlasPreservation .cuoZong .pauli⟩
  , ⟨.dao, .galois, "identity automorphism", "fixed coordinate reading",
      atlasPreservation .dao .galois⟩
  , ⟨.cuo, .galois, "content conjugation", "value-axis conjugate reading",
      atlasPreservation .cuo .galois⟩
  , ⟨.zong, .galois, "frame conjugation", "order-axis conjugate reading",
      atlasPreservation .zong .galois⟩
  , ⟨.cuoZong, .galois, "bi-conjugation", "content and frame conjugate reading",
      atlasPreservation .cuoZong .galois⟩
  , ⟨.dao, .semiotics, "sign", "mark as itself", atlasPreservation .dao .semiotics⟩
  , ⟨.cuo, .semiotics, "counter-sign", "marked content dual",
      atlasPreservation .cuo .semiotics⟩
  , ⟨.zong, .semiotics, "reframed sign", "context/order dual",
      atlasPreservation .zong .semiotics⟩
  , ⟨.cuoZong, .semiotics, "contrary reframed sign", "content and context dual",
      atlasPreservation .cuoZong .semiotics⟩
  ]

theorem coreAtlas_nonempty : coreAtlas ≠ [] := by
  decide

theorem coreAtlas_length : coreAtlas.length = 28 := rfl

theorem atlas_summary :
    coreAtlas.length = 28
    ∧ coreAtlas ≠ [] :=
  ⟨coreAtlas_length, coreAtlas_nonempty⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
