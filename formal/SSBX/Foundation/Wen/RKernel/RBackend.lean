/-
# Wen.RKernel.RBackend -- abstract representation backend contract

This module records the R-space boundary without importing a concrete R layer.
Future R0..R8 encodings instantiate this contract by proving tree roundtrip.
-/

import SSBX.Foundation.Wen.RKernel.Binding
import SSBX.Foundation.Wen.RKernel.Universal

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

/--
Representation backend for quoted V4 programs.

`Code` may later be an R-space stream, a Cell256 layout, or another audited
carrier.  The kernel only requires a V4Tree roundtrip.
-/
structure RBackend where
  Code : Type
  encodeTree : V4Tree → Code
  decodeTree : Code → Option V4Tree
  decode_encodeTree : ∀ tree, decodeTree (encodeTree tree) = some tree

namespace RBackend

def evalCode (backend : RBackend) (code : backend.Code) : Option V4 := do
  let tree ← backend.decodeTree code
  universalEval tree

def encodeTermCode (backend : RBackend) (term : Term) : backend.Code :=
  backend.encodeTree (encodeTerm term)

@[simp] theorem evalCode_encodeTree (backend : RBackend) (tree : V4Tree) :
    backend.evalCode (backend.encodeTree tree) = universalEval tree := by
  simp [evalCode, backend.decode_encodeTree tree]

theorem evalCode_encodeTerm (backend : RBackend) (term : Term) :
    backend.evalCode (backend.encodeTermCode term) = some term.eval := by
  simp [encodeTermCode, evalCode_encodeTree, universalEval_encodeTerm]

end RBackend

/-- The identity backend is the reference instance for the contract itself. -/
def treeBackend : RBackend where
  Code := V4Tree
  encodeTree := id
  decodeTree := some
  decode_encodeTree := by
    intro tree
    rfl

example : treeBackend.evalCode (treeBackend.encodeTermCode sampleCuoZong) =
    some .cuoZong := rfl

theorem rbackend_summary :
    (∀ backend : RBackend, ∀ term : Term,
      backend.evalCode (backend.encodeTermCode term) = some term.eval)
    ∧ treeBackend.evalCode (treeBackend.encodeTermCode sampleCuoZong) =
      some .cuoZong :=
  ⟨RBackend.evalCode_encodeTerm, rfl⟩

end SSBX.Foundation.Wen.RKernel
