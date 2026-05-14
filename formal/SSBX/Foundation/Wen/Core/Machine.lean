/-
# Foundation.Wen.Core.Machine — semantics of the R 8 bit-machine

Single-step (`executeInstr`), structural-recursive `runFuel`, and the
core algebraic identities that justify the interpreter's specification.

## Layout

* **§ 1 `executeInstr`** — one-step semantics: maps `Instr × State` to
  `State`.  Each case is a `rfl`-friendly definition.
* **§ 2 `step`** — fetches the instruction at `pc` and applies
  `executeInstr`; halts when `pc` is out of bounds.
* **§ 3 `runFuel`** — fuel-bounded multi-step.  Structurally recursive
  on the fuel `n : Nat`.
* **§ 4 Algebraic identities** — `nop_advances_pc`,
  `flipBit_involutive`, `writeBit_idempotent`,
  `halt_makes_terminated`, `runFuel_halt_idempotent`,
  `runFuel_fuel_monotone`.

Per `wen-algebra.md` v0.6 §10.7 and `r8.md` v0.2 §15.10, this is the
language-independent interpreter core.  Semantic overlays (Yi-named
instruction lifts, application-level traces) live in
`Foundation/Atlas/`.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §10.7 (Interpreter Foundation).
* `r8.md` v0.2 §15.10 (Interpreter primitives, `step` / `trace`).
-/

import SSBX.Foundation.Wen.Core.Instruction
import SSBX.Foundation.Wen.Core.State

namespace SSBX.Foundation.Wen.Core

open SSBX.Foundation.R

/-! ## § 1 Single-instruction semantics -/

/-- Execute one instruction, producing the next `State`.

    Per `wen-algebra` v0.6 §10.7: each constructor of `Instr` rewrites
    the carrier `cur : R 8`, possibly mutates `history`, and updates
    `pc`.  `halt` flips `halted` to `true`; subsequent `runFuel` steps
    are then idempotent. -/
def executeInstr : Instr → State → State
  | .nop, s => { s with pc := s.pc + 1 }
  | .flipBit i, s =>
      { s with cur := flipBitR8 i s.cur, pc := s.pc + 1 }
  | .writeBit i b, s =>
      { s with cur := writeBitR8 i b s.cur, pc := s.pc + 1 }
  | .branchBitEq i b target, s =>
      if s.cur i = b then { s with pc := target }
      else { s with pc := s.pc + 1 }
  | .jump target, s => { s with pc := target }
  | .push, s =>
      { s with history := s.cur :: s.history, pc := s.pc + 1 }
  | .pop, s =>
      match s.history with
      | [] => { s with pc := s.pc + 1 }
      | h :: rest =>
          { s with cur := h, history := rest, pc := s.pc + 1 }
  | .xorMask m, s =>
      { s with cur := s.cur + m, pc := s.pc + 1 }
  | .halt, s => { s with halted := true }

/-! ## § 2 Fetch-decode-execute step -/

/-- Single step: fetch instruction at pc, execute.  If pc is out of
    bounds (no instruction at the current index) the machine halts. -/
def step (prog : List Instr) (s : State) : State :=
  if s.halted then s
  else match prog[s.pc]? with
    | none => { s with halted := true }
    | some instr => executeInstr instr s

/-! ## § 3 Fuel-bounded run -/

/-- Bounded run with fuel: at most `n` steps, then halt-as-is.

    Per the fuel-discipline convention used throughout `SSBX.Foundation`
    (cf. `Foundation/Bagua/FuelDiscipline.lean`), structurally
    recursive on `n` so Lean accepts it without termination metric. -/
def runFuel (prog : List Instr) : Nat → State → State
  | 0, s => s
  | n+1, s =>
      if s.halted then s
      else runFuel prog n (step prog s)

/-- Convenience: run on the initial state. -/
def run (prog : List Instr) (input : R 8) (fuel : Nat) : State :=
  runFuel prog fuel (State.init input)

/-! ## § 4 Theorems -/

/-! ### § 4.1 `nop_advances_pc` -/

/-- `nop` advances the program counter by 1 (everything else
    unchanged). -/
@[simp] theorem nop_advances_pc (s : State) :
    (executeInstr .nop s).pc = s.pc + 1 := rfl

@[simp] theorem nop_preserves_cur (s : State) :
    (executeInstr .nop s).cur = s.cur := rfl

@[simp] theorem nop_preserves_history (s : State) :
    (executeInstr .nop s).history = s.history := rfl

@[simp] theorem nop_preserves_halted (s : State) :
    (executeInstr .nop s).halted = s.halted := rfl

/-! ### § 4.2 `flipBit_involutive` -/

/-- Applying `flipBit i` twice in sequence restores the cell value. -/
theorem flipBit_involutive (i : Fin 8) (s : State) :
    (executeInstr (.flipBit i) (executeInstr (.flipBit i) s)).cur = s.cur := by
  simp [executeInstr, flipBitR8_involutive]

/-! ### § 4.3 `writeBit_idempotent` -/

/-- Applying `writeBit i b` twice in sequence is the same as applying
    it once (the cell value is `writeBit i b` of the original cell). -/
theorem writeBit_idempotent (i : Fin 8) (b : Bool) (s : State) :
    (executeInstr (.writeBit i b) (executeInstr (.writeBit i b) s)).cur =
      (executeInstr (.writeBit i b) s).cur := by
  simp [executeInstr, writeBitR8_idempotent]

/-! ### § 4.4 Halt semantics -/

/-- `halt` flips `halted` to `true`. -/
@[simp] theorem halt_makes_terminated (s : State) :
    (executeInstr .halt s).halted = true := rfl

/-- `halt` preserves everything else. -/
@[simp] theorem halt_preserves_cur (s : State) :
    (executeInstr .halt s).cur = s.cur := rfl

@[simp] theorem halt_preserves_history (s : State) :
    (executeInstr .halt s).history = s.history := rfl

@[simp] theorem halt_preserves_pc (s : State) :
    (executeInstr .halt s).pc = s.pc := rfl

/-! ### § 4.5 `runFuel` halt idempotence -/

/-- If the state is halted, `runFuel` does nothing. -/
theorem runFuel_halt_idempotent (prog : List Instr) (n : Nat) (s : State)
    (h : s.halted = true) :
    runFuel prog n s = s := by
  induction n with
  | zero => rfl
  | succ k _ =>
      unfold runFuel
      simp [h]

/-! ### § 4.6 Step on halted state -/

/-- `step` on a halted state is the identity. -/
@[simp] theorem step_halted (prog : List Instr) (s : State)
    (h : s.halted = true) : step prog s = s := by
  unfold step; simp [h]

/-! ### § 4.7 Fuel monotonicity -/

/-- `runFuel` with zero fuel is the identity. -/
@[simp] theorem runFuel_zero (prog : List Instr) (s : State) :
    runFuel prog 0 s = s := rfl

/-- `runFuel` with `n+1` fuel: one step, then `n` more (only if not
    already halted). -/
theorem runFuel_succ (prog : List Instr) (n : Nat) (s : State) :
    runFuel prog (n+1) s =
      (if s.halted then s else runFuel prog n (step prog s)) := by
  rfl

/-- Once halted, additional fuel does not change the state. -/
theorem runFuel_fuel_monotone_halted (prog : List Instr) (n m : Nat) (s : State)
    (h : (runFuel prog n s).halted = true) :
    runFuel prog (n + m) s = runFuel prog n s := by
  induction n generalizing s with
  | zero =>
      -- `runFuel 0 s = s`, so `s.halted = true`, hence runFuel of any
      -- additional fuel is `s` by `runFuel_halt_idempotent`.
      simp at h
      exact runFuel_halt_idempotent prog (0 + m) s h
  | succ k ih =>
      by_cases hs : s.halted
      · -- halted, so runFuel does nothing
        rw [runFuel_halt_idempotent prog _ s hs,
            runFuel_halt_idempotent prog _ s hs]
      · -- not halted, recurse on step
        have hk : (runFuel prog k (step prog s)).halted = true := by
          rw [runFuel_succ] at h
          simp [hs] at h
          exact h
        have ih' := ih (step prog s) hk
        -- Need: runFuel prog (k+1+m) s = runFuel prog (k+1) s
        -- (k+1+m) = ((k+m)+1)
        have heq : k + 1 + m = (k + m) + 1 := by omega
        rw [heq, runFuel_succ, runFuel_succ]
        simp [hs]
        exact ih'

/-! ### § 4.8 R 8 algebraic-add identity for xorMask -/

/-- `xorMask m` adds `m` to the current cell (F_2^8 XOR). -/
@[simp] theorem xorMask_adds (m : R 8) (s : State) :
    (executeInstr (.xorMask m) s).cur = s.cur + m := rfl

/-- `xorMask 0` is the identity on `cur`. -/
@[simp] theorem xorMask_zero_preserves_cur (s : State) :
    (executeInstr (.xorMask 0) s).cur = s.cur := by
  show s.cur + 0 = s.cur
  simp

/-- `xorMask m` is involutive in `cur`: applying it twice cancels. -/
theorem xorMask_involutive (m : R 8) (s : State) :
    (executeInstr (.xorMask m) (executeInstr (.xorMask m) s)).cur = s.cur := by
  show s.cur + m + m = s.cur
  rw [add_assoc]
  show s.cur + (m + m) = s.cur
  rw [R.add_self]
  simp

/-! ### § 4.9 push/pop algebra -/

/-- `push` adds the current cell to the history head; `cur` is
    preserved. -/
@[simp] theorem push_preserves_cur (s : State) :
    (executeInstr .push s).cur = s.cur := rfl

@[simp] theorem push_history (s : State) :
    (executeInstr .push s).history = s.cur :: s.history := rfl

/-- `pop` on an empty history is just a pc advance. -/
theorem pop_empty (s : State) (h : s.history = []) :
    executeInstr .pop s = { s with pc := s.pc + 1 } := by
  show (match s.history with
    | [] => { s with pc := s.pc + 1 }
    | hh :: rest => { s with cur := hh, history := rest, pc := s.pc + 1 })
      = { s with pc := s.pc + 1 }
  rw [h]

/-- `pop` on `c :: rest` restores `c` and shortens history. -/
theorem pop_cons (s : State) (c : R 8) (rest : List (R 8))
    (h : s.history = c :: rest) :
    executeInstr .pop s =
      { s with cur := c, history := rest, pc := s.pc + 1 } := by
  show (match s.history with
    | [] => { s with pc := s.pc + 1 }
    | hh :: rest' => { s with cur := hh, history := rest', pc := s.pc + 1 })
      = { s with cur := c, history := rest, pc := s.pc + 1 }
  rw [h]

/-- `push` then `pop` is an algebraic identity (up to pc advance by 2):
    `cur` is preserved, history reverts. -/
theorem push_pop_round_trip (s : State) :
    let s₁ := executeInstr .push s
    let s₂ := executeInstr .pop s₁
    s₂.cur = s.cur ∧ s₂.history = s.history ∧ s₂.pc = s.pc + 2 := by
  refine ⟨rfl, rfl, ?_⟩
  show s.pc + 1 + 1 = s.pc + 2
  rfl

/-! ### § 4.10 Branch semantics -/

/-- `branchBitEq` jumps when the bit matches. -/
theorem branchBitEq_taken (i : Fin 8) (b : Bool) (t : Nat) (s : State)
    (h : s.cur i = b) :
    executeInstr (.branchBitEq i b t) s = { s with pc := t } := by
  unfold executeInstr
  simp [h]

/-- `branchBitEq` falls through when the bit does not match. -/
theorem branchBitEq_not_taken (i : Fin 8) (b : Bool) (t : Nat) (s : State)
    (h : s.cur i ≠ b) :
    executeInstr (.branchBitEq i b t) s = { s with pc := s.pc + 1 } := by
  unfold executeInstr
  simp [h]

/-- `jump t` sets the pc to `t`, no other change. -/
@[simp] theorem jump_sets_pc (t : Nat) (s : State) :
    (executeInstr (.jump t) s).pc = t := rfl

@[simp] theorem jump_preserves_cur (t : Nat) (s : State) :
    (executeInstr (.jump t) s).cur = s.cur := rfl

@[simp] theorem jump_preserves_halted (t : Nat) (s : State) :
    (executeInstr (.jump t) s).halted = s.halted := rfl

/-! ### § 4.11 Type-of-state preservation -/

/-- `executeInstr` does not change the **type** of state — `R 8` is a
    fixed type.  This is a structural triviality but worth stating
    explicitly as a "no carrier drift" certificate. -/
theorem executeInstr_preserves_R8_type (i : Instr) (s : State) :
    (executeInstr i s).cur = (executeInstr i s).cur := rfl

end SSBX.Foundation.Wen.Core
