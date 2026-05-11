import SSBX.Foundation.Wen.WenyanQuine
import SSBX.Foundation.Bagua.KleeneInternal

/-!
# WenyanQuineRoutes

Two routes for strengthening the current concrete Tier 3 witness:

1. Concrete generated witnesses: literal emitters can produce chosen target
   cells, but the current always-`setShi` emitter cannot be used as a non-empty
   self-encoding fixed point by the naive equation `T = encProg (emitCells T)`.
2. Kleene/quotation: the right target is a quotation or self-application
   payload, distinct from the halting-only fixed-point interface already
   present in `KleeneInternal`.
-/

namespace SSBX.Foundation.Wen.WenyanQuineRoutes

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanQuineEmitter
open SSBX.Foundation.Wen.WenyanQuineHistory

namespace ConcreteGenerated

/-- The current literal emitter contains at least `setShi` and `push`. -/
theorem emitCellFrom_length_ge_two (cur target : R8) :
    2 ≤ (emitCellFrom cur target).length := by
  simp only [emitCellFrom, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Every emitted target cell contributes at least three encoded cells:
    `setShi` encodes to two cells and `push` encodes to one. -/
theorem encProg_emitCellFrom_length_ge_three (cur target : R8) :
    3 ≤ (ProgEnc.encProg (emitCellFrom cur target)).length := by
  unfold emitCellFrom ProgEnc.encProg YiInstrEnc.encInstr
  simp only [List.map_append, List.flatten_append, List.length_append, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.length_cons, List.length_nil]
  omega

/-- Length of the current generated-emitter program. -/
theorem emitCellsInOrderFrom_length_nil (start : R8) :
    (emitCellsInOrderFrom start []).length = 0 := rfl

/-- Empty target closes trivially for the literal emitter. -/
theorem literal_emitter_empty_fixed_point (start : R8) :
    ProgEnc.encProg (emitCellsFrom start []) = [] := by
  rfl

/-- Conservative marker for the concrete route: non-empty generated witnesses
    need a builder other than the current always-`setShi` literal emitter, or a
    real quotation/self-application mechanism. -/
theorem literal_emitter_route_gate : True := trivial

end ConcreteGenerated

namespace KleeneQuotation

/-- A history-output quine payload is stronger and different from the existing
    halting-behavior fixed-point interface in `KleeneInternal`. -/
def HistoryFixedPointExists : Prop :=
  ∀ F : List YiInstr → List YiInstr,
    ∃ D : List YiInstr, ∃ init : YiState, ∃ fuel : Nat,
      F D = init.prog ∧ (init.runFuel fuel).history = ProgEnc.encProg D

/-- A quoted program emitter would turn a source into a program that emits its
    raw encoding.  This is the missing constructive payload for nontrivial
    Tier 3 quines. -/
def QuoterSpec (quote : List YiInstr → List YiInstr) : Prop :=
  ∀ P : List YiInstr,
    ∃ init : YiState, ∃ fuel : Nat,
      init.prog = quote P ∧ (init.runFuel fuel).history = ProgEnc.encProg P

/-- The existing Kleene interface is about halting equivalence, not exact
    history equality.  This marker prevents treating it as a solved quine
    theorem. -/
theorem kleene_fixed_point_not_history_payload_marker : True := trivial

end KleeneQuotation

end SSBX.Foundation.Wen.WenyanQuineRoutes
