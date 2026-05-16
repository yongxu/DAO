/-
# Foundation.Wen.CorePartial.State — interpreter state on `PartialCell 8`

The PartialCell-native state.  Carries:

* `pc`      — program counter (next instruction index)
* `cur`     — current partial-cell state (the carrier)
* `history` — stack of saved cells (for future push/pop in Phase E.2)
* `halted`  — termination flag

Initial state: pc = 0, cur = 道 (`PartialCell.dao`), history = [], halted = false.
The choice of 道 as initial state is doctrinally aligned: a program begins
in the maximally-undetermined state (the full 8-cube), and instructions
progressively specify or unspecify positions.

## Why `cur : PartialCell 8` and not `R 8`?

This is the key shift from `Foundation/Wen/Core/State.lean`.  In the
legacy core, the state is a fully-specified bit vector; an "unknown bit"
cannot be expressed.  Here, partial states are first-class: the
interpreter can carry under-specified knowledge through computation,
and conflict (不通) is a primary failure mode (not an exception).
-/

import SSBX.Foundation.Wen.CorePartial.Instruction

namespace SSBX.Foundation.Wen.CorePartial

open SSBX.Foundation.R

/-- Interpreter state on `PartialCell 8`.

    * `pc`      : program counter
    * `cur`     : current partial-cell state
    * `history` : LIFO stack of saved cells (reserved for Phase E.2)
    * `halted`  : true once the machine has halted -/
structure State : Type where
  pc      : Nat
  cur     : PartialCell 8
  history : List (PartialCell 8)
  halted  : Bool

namespace State

/-- The initial state: pc = 0, cur = 道 (the maximally-undetermined
    cell), empty history, not halted. -/
def initial : State :=
  { pc := 0, cur := PartialCell.dao, history := [], halted := false }

/-- Initial state with input `inp : R 8` lifted into a fully-specified
    PartialCell.  Bridge for porting `Wen.Core` programs (where the
    input is a total bit vector).  -/
def init (inp : R 8) : State :=
  { pc := 0, cur := PartialCell.ofFull inp, history := [], halted := false }

@[simp] theorem initial_pc : initial.pc = 0 := rfl
@[simp] theorem initial_cur : initial.cur = (PartialCell.dao : PartialCell 8) := rfl
@[simp] theorem initial_history : initial.history = ([] : List (PartialCell 8)) := rfl
@[simp] theorem initial_halted : initial.halted = false := rfl

@[simp] theorem init_pc (inp : R 8) : (init inp).pc = 0 := rfl
@[simp] theorem init_cur (inp : R 8) : (init inp).cur = PartialCell.ofFull inp := rfl
@[simp] theorem init_history (inp : R 8) :
    (init inp).history = ([] : List (PartialCell 8)) := rfl
@[simp] theorem init_halted (inp : R 8) : (init inp).halted = false := rfl

end State

end SSBX.Foundation.Wen.CorePartial
