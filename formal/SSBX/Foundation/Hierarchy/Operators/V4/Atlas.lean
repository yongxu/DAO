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
  deriving Repr

def coreAtlas : List AtlasEntry :=
  [ ⟨.dao, .wen, "Way", "identity"⟩
  , ⟨.cuo, .wen, "content duality", "value flip"⟩
  , ⟨.zong, .wen, "frame duality", "order flip"⟩
  , ⟨.cuoZong, .wen, "compound duality", "content and frame flip"⟩
  , ⟨.dao, .turing, "nop", "no local flip"⟩
  , ⟨.cuo, .turing, "flip-bit", "tape-symbol flip"⟩
  , ⟨.zong, .turing, "flip-dir", "head-direction flip"⟩
  , ⟨.cuoZong, .turing, "flip-both", "symbol and direction flip"⟩
  , ⟨.dao, .logic, "id", "identity"⟩
  , ⟨.cuo, .logic, "negation", "content duality"⟩
  , ⟨.zong, .logic, "implication reversal", "frame duality"⟩
  , ⟨.cuoZong, .logic, "contrapositive", "compound duality"⟩
  ]

theorem coreAtlas_nonempty : coreAtlas ≠ [] := by
  decide

theorem coreAtlas_length : coreAtlas.length = 12 := rfl

theorem atlas_summary :
    coreAtlas.length = 12
    ∧ coreAtlas ≠ [] :=
  ⟨coreAtlas_length, coreAtlas_nonempty⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
