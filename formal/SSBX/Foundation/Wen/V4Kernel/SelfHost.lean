/-
# Wen.V4Kernel.SelfHost -- quote/eval surface for the V4 kernel

This file gives the first self-hosting surface: programs are quotable as V4
trees, and the universal evaluator consumes that quoted form.  It deliberately
does not compile into Cell256 or depend on R5-R8.
-/

import SSBX.Foundation.Wen.V4Kernel.Universal

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-- Quoting is just the canonical V4-tree encoding. -/
def quote (term : Term) : V4Tree :=
  encodeTerm term

/-- Evaluate a quoted term through the universal evaluator. -/
def evalQuoted (term : Term) : Option V4 :=
  universalEval (quote term)

theorem evalQuoted_correct (term : Term) :
    evalQuoted term = some term.eval := by
  simp [evalQuoted, quote]

/-- Minimal interpreter package for the V4 kernel. -/
structure InterpreterKernel where
  quote : Term → V4Tree
  evalCode : V4Tree → Option V4
  quote_correct : ∀ term, evalCode (quote term) = some term.eval

def interpreterKernel : InterpreterKernel where
  quote := quote
  evalCode := universalEval
  quote_correct := evalQuoted_correct

/-- R5-R8/Cell256 backend construction is intentionally outside this kernel. -/
def BackendEmbeddingConstructedHere : Prop := False

theorem backend_embedding_not_claimed :
    ¬ BackendEmbeddingConstructedHere := by
  intro h
  exact h

theorem self_host_summary :
    (∀ term : Term, evalQuoted term = some term.eval)
    ∧ interpreterKernel.evalCode (interpreterKernel.quote sampleCuoZong) =
      some .cuoZong
    ∧ ¬ BackendEmbeddingConstructedHere :=
  ⟨evalQuoted_correct, rfl, backend_embedding_not_claimed⟩

end SSBX.Foundation.Wen.V4Kernel
