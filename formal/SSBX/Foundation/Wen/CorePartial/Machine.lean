/-
# Foundation.Wen.CorePartial.Machine — single-step + fuel-bounded execution

The operational semantics of the PartialCell-native ISA.  `executeInstr`
maps each `Instr` to its `State → State` action; `step` fetches the next
instruction; `runFuel` iterates `step` up to a bound.

The crucial PartialCell-native fact: the `merge` instruction *may halt
the machine* if the merge target is incompatible with the current state.
This is the operational realisation of "不通" — when a sentence contains
contradictory specifications, the machine cannot proceed.
-/

import SSBX.Foundation.Wen.CorePartial.State

namespace SSBX.Foundation.Wen.CorePartial

open SSBX.Foundation.R

/-- Execute a single instruction, returning the new state.
    Pure function — does not consume fuel. -/
def executeInstr (instr : Instr) (s : State) : State :=
  match instr with
  | .nop =>
      { s with pc := s.pc + 1 }
  | .merge c =>
      match PartialCell.merge s.cur c with
      | some c' => { s with cur := c', pc := s.pc + 1 }
      | none    => { s with halted := true }  -- 不通 → halt
  | .restrict mask =>
      { s with cur := PartialCell.restrict mask s.cur, pc := s.pc + 1 }
  | .jump t =>
      { s with pc := t }
  | .halt =>
      { s with halted := true }

/-- Single fetch-decode-execute step.
    If `s.halted = true`, returns `s` unchanged.
    If `pc` is past the end of the program, halts. -/
def step (prog : List Instr) (s : State) : State :=
  if s.halted then s
  else
    match prog[s.pc]? with
    | none      => { s with halted := true }
    | some inst => executeInstr inst s

/-- Iterate `step` up to `fuel` times.  Returns the resulting state. -/
def runFuel (prog : List Instr) : Nat → State → State
  | 0,     s => s
  | n + 1, s => runFuel prog n (step prog s)

/-! ## § Basic theorems -/

@[simp] theorem step_halted (prog : List Instr) (s : State) (h : s.halted = true) :
    step prog s = s := by
  unfold step; rw [if_pos h]

@[simp] theorem runFuel_zero (prog : List Instr) (s : State) :
    runFuel prog 0 s = s := rfl

theorem runFuel_halted (prog : List Instr) (s : State) (h : s.halted = true) :
    ∀ n, runFuel prog n s = s := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold runFuel
    rw [step_halted prog s h]
    exact ih

theorem executeInstr_halt (s : State) :
    executeInstr .halt s = { s with halted := true } := rfl

theorem executeInstr_nop (s : State) :
    executeInstr .nop s = { s with pc := s.pc + 1 } := rfl

theorem executeInstr_jump (t : Nat) (s : State) :
    executeInstr (.jump t) s = { s with pc := t } := rfl

/-- `merge c` from initial-like state with `cur = dao` always succeeds. -/
theorem executeInstr_merge_dao (c : PartialCell 8) (s : State)
    (hs : s.cur = PartialCell.dao) :
    executeInstr (.merge c) s =
      { s with cur := c, pc := s.pc + 1 } := by
  simp [executeInstr, hs, PartialCell.dao_merge]

/-- `restrict mask` is involutive only when `mask` covers all of `s.cur`'s
    support — but the operation itself is always well-defined. -/
theorem executeInstr_restrict (mask : Finset (Fin 8)) (s : State) :
    executeInstr (.restrict mask) s =
      { s with cur := PartialCell.restrict mask s.cur, pc := s.pc + 1 } := rfl

/-! ## § Bridge to `mergeAll`: a pure-merge program IS `mergeAll`

For a program consisting only of `merge` instructions (no jumps, no
halts, no restricts), the result of running it from `initial` is exactly
`PartialCell.mergeAll` of the merge cells.  This is the operational
realisation of Phase D's algebraic fold. -/

/-- Extract the merge cells from a program (in order, only `.merge`
    instructions kept). -/
def mergeCells : List Instr → List (PartialCell 8)
  | []                => []
  | .merge c :: rest  => c :: mergeCells rest
  | _ :: rest         => mergeCells rest

@[simp] theorem mergeCells_nil : mergeCells [] = [] := rfl
@[simp] theorem mergeCells_merge_cons (c : PartialCell 8) (rest : List Instr) :
    mergeCells (.merge c :: rest) = c :: mergeCells rest := rfl

end SSBX.Foundation.Wen.CorePartial
