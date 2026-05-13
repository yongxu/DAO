/-
# Wen.Native -- public native Wen interpreter kernel

This is the active native interpreter spine.  It is built over
`Wen.Layered.VnRn`; YiInstr and restored meta-interpreter modules remain
separate research/proof lines and are not imported here.
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

namespace SSBX.Foundation.Wen.Native

theorem native_public_summary (n : Nat) :
    Nonempty (Expr n)
    ∧ Nonempty (Value n)
    ∧ Nonempty (Backend n)
    ∧ Kleene.Halts (.lam (.var 0) : Expr n) sampleCell :=
  ⟨⟨.nil⟩, ⟨.nil⟩, ⟨treeBackend n⟩, Kleene.halts_identity_cell⟩

end SSBX.Foundation.Wen.Native
