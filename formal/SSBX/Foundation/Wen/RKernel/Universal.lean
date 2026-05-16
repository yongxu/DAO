/-
# Wen.RKernel.Universal -- universal evaluator for quoted V4 terms

This is the suspended-R5/R8 universal-compose nucleus: a single evaluator
accepts V4-coded syntax and simulates that term's direct V4 semantics.
-/

import SSBX.Foundation.Wen.RKernel.Encode

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

/-- Universal evaluator for the current V4 term fragment. -/
def universalEval (code : V4Tree) : Option V4 :=
  match decodeTerm code with
  | some term => some term.eval
  | none => none

@[simp] theorem universalEval_encodeTerm (t : Term) :
    universalEval (encodeTerm t) = some t.eval := by
  simp [universalEval]

def sampleCode : V4Tree :=
  encodeTerm sampleCuoZong

example : universalEval sampleCode = some .cuoZong := rfl

/-- Universal-compose theorem for the V4 kernel fragment. -/
theorem universal_compose_v4_kernel :
    ∀ term : Term, universalEval (encodeTerm term) = some term.eval :=
  universalEval_encodeTerm

theorem universal_summary :
    universalEval sampleCode = some .cuoZong
    ∧ (∀ term : Term, universalEval (encodeTerm term) = some term.eval) :=
  ⟨rfl, universal_compose_v4_kernel⟩

end SSBX.Foundation.Wen.RKernel
