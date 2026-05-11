import SSBX.Foundation.Wen.WenyanQuineEmitter

/-!
# WenyanQuineHistory

Batch emitter wiring.  The general builder runs target cells in reverse order
because `push` writes to the front of `history`.
-/

namespace SSBX.Foundation.Wen.WenyanQuineHistory

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanQuineEmitter

/-- Emit `targets` in the given execution order, threading the known current cell. -/
def emitCellsInOrderFrom : R8 → List R8 → List YiInstr
  | _, [] => []
  | cur, target :: rest =>
      emitCellFrom cur target ++ emitCellsInOrderFrom target rest

/-- Emit a target list so the final `history` has the same order as `targets`. -/
def emitCellsFrom (start : R8) (targets : List R8) : List YiInstr :=
  emitCellsInOrderFrom start targets.reverse

def emitCellsInit (start : R8) (targets oldHistory : List R8) : YiState :=
  { cur := start
  , history := oldHistory
  , pc := 0
  , prog := emitCellsFrom start targets
  , halted := false }

def c0 : R8 := (Hexagram.heaven, Shi.ji)
def c1 : R8 := ({ Hexagram.heaven with y1 := Yao.yin }, Shi.jin)
def c2 : R8 := (Hexagram.earth, Shi.wei)

/-- Concrete ordering check: final history is `[c0, c1, c2]`, not reversed. -/
theorem emitCellsFrom_history_three :
    let start : R8 := (Hexagram.heaven, Shi.jin)
    let targets : List R8 := [c0, c1, c2]
    ((emitCellsInit start targets []).runFuel (emitCellsFrom start targets).length).history = targets := by
  native_decide

end SSBX.Foundation.Wen.WenyanQuineHistory
