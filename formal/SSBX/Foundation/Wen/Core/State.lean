/-
# Foundation.Wen.Core.State — execution state of the R 8 bit-machine

The state of the language-independent `R 8` interpreter is a 4-tuple:

```
State = { cur : R 8, history : List (R 8), pc : Nat, halted : Bool }
```

* `cur`     — the current cell value, an element of `R 8 = Fin 8 → Bool`.
* `history` — an *unbounded* list of prior `R 8` values, populated by
  `push` and consumed by `pop`.  This is the linear-tape boundary that
  gives the machine universal computation power.
* `pc`      — the program counter, indexing into a `List Instr` program.
* `halted`  — when `true`, the machine has terminated and `runFuel`
  becomes idempotent.

Per `wen-algebra` v0.6 doctrine, the state is **language-independent**:
there are no Yi/Pauli/Bagua-flavoured fields.  Semantic overlays live
in `Foundation/Atlas/`.

## Doctrinal anchor

* `r8.md` v0.2 §15.10 (interpreter primitives, basic state shape).
* `wen-algebra.md` v0.6 §10.7 (`RPhantom`-typed interpreter state — we
  use the simpler untyped `R 8` form here for the core machine; the
  `RPhantom` mode-tagged form is an Atlas-level refinement).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Wen.Core

open SSBX.Foundation.R
open SSBX.Foundation.R.R (basis add_apply)

/-! ## § 1 The execution state -/

/-- Execution state of the language-independent `R 8` interpreter.

    `cur` is the current cell value (`R 8`); `history` is an unbounded
    list of prior values (the linear-tape memory); `pc` is the program
    counter; `halted` is the termination flag. -/
structure State : Type where
  /-- The current cell value, an element of `R 8 = Fin 8 → Bool`. -/
  cur : R 8
  /-- The history stack: unbounded list of prior `R 8` values pushed
      via `Instr.push` and popped via `Instr.pop`. -/
  history : List (R 8)
  /-- Program counter: index into the program's instruction list. -/
  pc : Nat
  /-- Halt flag: when `true`, the machine has terminated. -/
  halted : Bool := false

namespace State

/-! ## § 2 Initial state constructor -/

/-- The initial state with cell `input`, empty history, pc = 0,
    and `halted = false`. -/
def init (input : R 8) : State :=
  { cur := input, history := [], pc := 0, halted := false }

@[simp] theorem init_cur (input : R 8) : (init input).cur = input := rfl

@[simp] theorem init_history (input : R 8) : (init input).history = [] := rfl

@[simp] theorem init_pc (input : R 8) : (init input).pc = 0 := rfl

@[simp] theorem init_halted (input : R 8) : (init input).halted = false := rfl

/-! ## § 3 Distinguished states

`zeroState` is the unique "origin" state: cell is the zero vector,
history is empty, pc = 0, not halted.  This is the `0`-of-state in
the obvious sense (zero in carrier and clean trace).
-/

/-- The zero state: zero cell, empty history, pc = 0, not halted. -/
def zeroState : State := init (0 : R 8)

@[simp] theorem zeroState_cur : zeroState.cur = (0 : R 8) := rfl

@[simp] theorem zeroState_pc : zeroState.pc = 0 := rfl

@[simp] theorem zeroState_history : zeroState.history = [] := rfl

@[simp] theorem zeroState_halted : zeroState.halted = false := rfl

/-! ## § 4 Halt accessor and basic predicates

These lightweight predicates are used downstream by `Machine.lean` to
characterise terminating runs.
-/

/-- A state is *running* iff it is not halted. -/
@[reducible] def isRunning (s : State) : Prop := s.halted = false

/-- A state is *terminated* iff it is halted. -/
@[reducible] def isTerminated (s : State) : Prop := s.halted = true

theorem isRunning_or_isTerminated (s : State) :
    s.isRunning ∨ s.isTerminated := by
  unfold isRunning isTerminated
  cases h : s.halted
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem isRunning_iff (s : State) :
    s.isRunning ↔ ¬ s.isTerminated := by
  unfold isRunning isTerminated
  cases h : s.halted
  · simp
  · simp

end State

/-! ## § 5 Cell update helpers (pure functions on R 8)

The single-bit update operations correspond to `Instr.flipBit` and
`Instr.writeBit` at the carrier level.  They are isolated here so the
`Machine.lean` step semantics can refer to them by name, and so they
admit independent algebraic lemmas (`flipBit_involutive`,
`writeBit_idempotent`).
-/

/-- Toggle bit `i` of `v : R 8`. -/
def flipBitR8 (i : Fin 8) (v : R 8) : R 8 :=
  fun j => if j = i then !v j else v j

/-- Set bit `i` of `v : R 8` to `b`. -/
def writeBitR8 (i : Fin 8) (b : Bool) (v : R 8) : R 8 :=
  fun j => if j = i then b else v j

/-! ## § 6 Carrier-level theorems -/

/-- `flipBitR8` toggles only the targeted bit. -/
@[simp] theorem flipBitR8_apply_eq (i : Fin 8) (v : R 8) :
    flipBitR8 i v i = !v i := by
  unfold flipBitR8; simp

theorem flipBitR8_apply_ne (i j : Fin 8) (v : R 8) (h : j ≠ i) :
    flipBitR8 i v j = v j := by
  unfold flipBitR8; simp [h]

/-- `flipBitR8 i` is an involution on `R 8`. -/
theorem flipBitR8_involutive (i : Fin 8) (v : R 8) :
    flipBitR8 i (flipBitR8 i v) = v := by
  funext j
  unfold flipBitR8
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- `writeBitR8 i b` writes `b` at position `i`. -/
@[simp] theorem writeBitR8_apply_eq (i : Fin 8) (b : Bool) (v : R 8) :
    writeBitR8 i b v i = b := by
  unfold writeBitR8; simp

theorem writeBitR8_apply_ne (i j : Fin 8) (b : Bool) (v : R 8) (h : j ≠ i) :
    writeBitR8 i b v j = v j := by
  unfold writeBitR8; simp [h]

/-- `writeBitR8 i b` is idempotent. -/
theorem writeBitR8_idempotent (i : Fin 8) (b : Bool) (v : R 8) :
    writeBitR8 i b (writeBitR8 i b v) = writeBitR8 i b v := by
  funext j
  unfold writeBitR8
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- `writeBitR8` applied twice in sequence keeps only the second value. -/
theorem writeBitR8_writeBitR8 (i : Fin 8) (b₁ b₂ : Bool) (v : R 8) :
    writeBitR8 i b₂ (writeBitR8 i b₁ v) = writeBitR8 i b₂ v := by
  funext j
  unfold writeBitR8
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- `flipBitR8 i` agrees with XOR with the canonical basis vector
    `basis i` (under coordinate-wise XOR / `R 8`-add).  This is the
    bridge between the single-bit primitive and the `R 8`-group
    structure. -/
theorem flipBitR8_eq_xor_basis (i : Fin 8) (v : R 8) :
    flipBitR8 i v = v + basis i := by
  funext j
  unfold flipBitR8 basis
  by_cases h : j = i
  · subst h
    simp [add_apply]
  · have h' : ¬ (i = j) := fun hh => h hh.symm
    simp [h, h', add_apply]

end SSBX.Foundation.Wen.Core
