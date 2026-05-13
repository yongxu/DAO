/-
# Wen.Native -- public native Wen API

This module is the public entrypoint for the native interpreter.  It exports
the rank-polymorphic core syntax, evaluator, quote/code-tree round trips,
backend contract, cell-named surface language, S-expression reader, program
runner, concrete-carrier bridges, and Kleene target interfaces.

The carrier is always `Layered.Rn n` with `Layered.Vn n` actions.  V4,
Word64/R6, and R8/Cell256 enter through bridges over this API; YiInstr and
restored meta-interpreter modules remain separate proof/backend lines and are
intentionally not imported here.
-/

import SSBX.Foundation.Wen.Native.Syntax
import SSBX.Foundation.Wen.Native.Eval
import SSBX.Foundation.Wen.Native.Quote
import SSBX.Foundation.Wen.Native.Universal
import SSBX.Foundation.Wen.Native.Backend
import SSBX.Foundation.Wen.Native.Surface
import SSBX.Foundation.Wen.Native.Reader
import SSBX.Foundation.Wen.Native.Program
import SSBX.Foundation.Wen.Native.Kleene
import SSBX.Foundation.Wen.Native.Bridges

namespace SSBX.Foundation.Wen.Native

theorem public_api_laws (n : Nat) :
    Nonempty (Expr n)
    ∧ Nonempty (Value n)
    ∧ Nonempty (Backend n)
    ∧ Nonempty Bridges.R8.Carrier
    ∧ Kleene.Halts (.lam (.var 0) : Expr n) originCell :=
  ⟨⟨.nil⟩, ⟨.nil⟩, ⟨treeBackend n⟩,
    ⟨SSBX.Foundation.Bagua.R8.R8.origin⟩, Kleene.halts_id_on_origin⟩

end SSBX.Foundation.Wen.Native
