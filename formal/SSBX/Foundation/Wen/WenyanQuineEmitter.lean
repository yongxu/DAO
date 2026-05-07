import SSBX.Foundation.Wen.WenyanSelfInterp

/-!
# WenyanQuineEmitter

Small literal emitters used by the Tier 3 quine lane.

The important runtime convention is that `push` conses onto `history`, so
multi-cell builders must emit the desired cells in reverse execution order.
-/

namespace SSBX.Foundation.Wen.WenyanQuineEmitter

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp

private def yao0 : Fin 6 := ⟨0, by omega⟩
private def yao1 : Fin 6 := ⟨1, by omega⟩
private def yao2 : Fin 6 := ⟨2, by omega⟩
private def yao3 : Fin 6 := ⟨3, by omega⟩
private def yao4 : Fin 6 := ⟨4, by omega⟩
private def yao5 : Fin 6 := ⟨5, by omega⟩

/-- Emit a single flip iff the selected yao differs between source and target. -/
def flipIfDiff (src target : Hexagram) (i : Fin 6) : List YiInstr :=
  if src.yaoAt i = target.yaoAt i then [] else [YiInstr.flipYao i]

theorem flipIfDiff_length_le (src target : Hexagram) (i : Fin 6) :
    (flipIfDiff src target i).length ≤ 1 := by
  unfold flipIfDiff
  split <;> simp

/-- Program fragment which sets `cur` from a known cell to `target`, then pushes. -/
def emitCellFrom (cur target : Cell192) : List YiInstr :=
  flipIfDiff cur.1 target.1 yao0 ++
  flipIfDiff cur.1 target.1 yao1 ++
  flipIfDiff cur.1 target.1 yao2 ++
  flipIfDiff cur.1 target.1 yao3 ++
  flipIfDiff cur.1 target.1 yao4 ++
  flipIfDiff cur.1 target.1 yao5 ++
  [YiInstr.setShi target.2, YiInstr.push]

theorem emitCellFrom_length_le (cur target : Cell192) :
    (emitCellFrom cur target).length ≤ 8 := by
  have h0 := flipIfDiff_length_le cur.1 target.1 yao0
  have h1 := flipIfDiff_length_le cur.1 target.1 yao1
  have h2 := flipIfDiff_length_le cur.1 target.1 yao2
  have h3 := flipIfDiff_length_le cur.1 target.1 yao3
  have h4 := flipIfDiff_length_le cur.1 target.1 yao4
  have h5 := flipIfDiff_length_le cur.1 target.1 yao5
  simp only [emitCellFrom, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Execution state for checking a single-cell emitter fragment. -/
def emitCellInit (cur target : Cell192) (oldHistory : List Cell192) : YiState :=
  { cur := cur
  , history := oldHistory
  , pc := 0
  , prog := emitCellFrom cur target
  , halted := false }

/-- A zero-flip concrete check. -/
theorem emitCellFrom_correct_zero_flip :
    let cur : Cell192 := (Hexagram.qian, Shi.jin)
    let target : Cell192 := (Hexagram.qian, Shi.ji)
    ((emitCellInit cur target []).runFuel (emitCellFrom cur target).length).cur = target
      ∧ ((emitCellInit cur target []).runFuel (emitCellFrom cur target).length).history = [target] := by
  native_decide

/-- A one-flip concrete check. -/
theorem emitCellFrom_correct_one_flip :
    let cur : Cell192 := (Hexagram.qian, Shi.jin)
    let target : Cell192 :=
      ({ Hexagram.qian with y1 := Yao.yin }, Shi.wei)
    ((emitCellInit cur target []).runFuel (emitCellFrom cur target).length).cur = target
      ∧ ((emitCellInit cur target []).runFuel (emitCellFrom cur target).length).history = [target] := by
  native_decide

/-- A six-flip concrete check. -/
theorem emitCellFrom_correct_six_flips :
    let cur : Cell192 := (Hexagram.qian, Shi.jin)
    let target : Cell192 := (Hexagram.kun, Shi.wei)
    ((emitCellInit cur target []).runFuel (emitCellFrom cur target).length).cur = target
      ∧ ((emitCellInit cur target []).runFuel (emitCellFrom cur target).length).history = [target] := by
  native_decide

end SSBX.Foundation.Wen.WenyanQuineEmitter
