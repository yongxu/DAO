/-
# WenyanQuineSpec — raw quine target specification

This file is intentionally only a specification layer.  It records the literal
history-equals-program-encoding target for a Wenyan quine run, without claiming
a general fixed-point or diagonal theorem.
-/
import SSBX.Foundation.Wen.WenyanSelfInterp

namespace SSBX.Foundation.Wen.WenyanQuineSpec

open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Wen.WenyanSelfInterp

/-- Raw quine-run target: running `init` for `fuel` leaves exactly the encoded
program `P` in the execution history. -/
def QuineRunSpec (P : List YiInstr) (init : YiState) (fuel : Nat) : Prop :=
  (init.runFuel fuel).history = ProgEnc.encProg P

/-- The raw target theorem shape expected of a concrete quine witness. -/
def RawTargetTheoremStatement
    (P : List YiInstr) (init : YiState) (fuel : Nat) : Prop :=
  QuineRunSpec P init fuel

/-- Conservative gate: this file records only the literal run specification.
It deliberately does not assert a general diagonal/fixed-point theorem; such a
theorem would require a separate construction and proof tying program synthesis
to `ProgEnc.encProg`. -/
theorem literal_diagonal_gate : True := trivial

end SSBX.Foundation.Wen.WenyanQuineSpec
