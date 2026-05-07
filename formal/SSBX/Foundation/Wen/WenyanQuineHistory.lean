import SSBX.Foundation.Wen.WenyanQuineEmitter

/-!
# WenyanQuineHistory

Batch emitter wiring.  The general builder runs target cells in reverse order
because `push` writes to the front of `history`.
-/

namespace SSBX.Foundation.Wen.WenyanQuineHistory

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanQuineEmitter

/-- Emit `targets` in the given execution order, threading the known current cell. -/
def emitCellsInOrderFrom : Cell192 → List Cell192 → List YiInstr
  | _, [] => []
  | cur, target :: rest =>
      emitCellFrom cur target ++ emitCellsInOrderFrom target rest

/-- Emit a target list so the final `history` has the same order as `targets`. -/
def emitCellsFrom (start : Cell192) (targets : List Cell192) : List YiInstr :=
  emitCellsInOrderFrom start targets.reverse

def emitCellsInit (start : Cell192) (targets oldHistory : List Cell192) : YiState :=
  { cur := start
  , history := oldHistory
  , pc := 0
  , prog := emitCellsFrom start targets
  , halted := false }

def c0 : Cell192 := (Hexagram.qian, Shi.ji)
def c1 : Cell192 := ({ Hexagram.qian with y1 := Yao.yin }, Shi.jin)
def c2 : Cell192 := (Hexagram.kun, Shi.wei)

/-- Concrete ordering check: final history is `[c0, c1, c2]`, not reversed. -/
theorem emitCellsFrom_history_three :
    let start : Cell192 := (Hexagram.qian, Shi.jin)
    let targets : List Cell192 := [c0, c1, c2]
    ((emitCellsInit start targets []).runFuel (emitCellsFrom start targets).length).history = targets := by
  native_decide

end SSBX.Foundation.Wen.WenyanQuineHistory
