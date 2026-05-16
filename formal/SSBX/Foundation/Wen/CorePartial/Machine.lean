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
  | .branchBitEq i b t =>
      if s.cur i = some b then
        { s with pc := t }
      else
        { s with pc := s.pc + 1 }
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

/-! ### Field-projection lemmas (idiomatic — record-equality forms are
     brittle under match reduction with branchBitEq's nested if). -/

@[simp] theorem halt_halted (s : State) : (executeInstr .halt s).halted = true := rfl
@[simp] theorem halt_pc (s : State) : (executeInstr .halt s).pc = s.pc := rfl
@[simp] theorem halt_cur (s : State) : (executeInstr .halt s).cur = s.cur := rfl

@[simp] theorem nop_pc (s : State) : (executeInstr .nop s).pc = s.pc + 1 := rfl
@[simp] theorem nop_cur (s : State) : (executeInstr .nop s).cur = s.cur := rfl
@[simp] theorem nop_halted (s : State) : (executeInstr .nop s).halted = s.halted := rfl

@[simp] theorem jump_pc (t : Nat) (s : State) : (executeInstr (.jump t) s).pc = t := rfl
@[simp] theorem jump_cur (t : Nat) (s : State) : (executeInstr (.jump t) s).cur = s.cur := rfl
@[simp] theorem jump_halted (t : Nat) (s : State) :
    (executeInstr (.jump t) s).halted = s.halted := rfl

/-- `merge c` from initial-like state with `cur = dao` always succeeds.
    Stated as field-projection on `cur` to dodge record-equality brittleness. -/
@[simp] theorem merge_cur_of_dao (c : PartialCell 8) (s : State)
    (hs : s.cur = PartialCell.dao) :
    (executeInstr (.merge c) s).cur = c := by
  show ((match PartialCell.merge s.cur c with
         | some c' => ({ s with cur := c', pc := s.pc + 1 } : State)
         | none    => { s with halted := true }).cur) = c
  rw [hs, PartialCell.dao_merge]

@[simp] theorem restrict_cur (mask : Finset (Fin 8)) (s : State) :
    (executeInstr (.restrict mask) s).cur = PartialCell.restrict mask s.cur := rfl

@[simp] theorem restrict_pc (mask : Finset (Fin 8)) (s : State) :
    (executeInstr (.restrict mask) s).pc = s.pc + 1 := rfl

@[simp] theorem restrict_halted (mask : Finset (Fin 8)) (s : State) :
    (executeInstr (.restrict mask) s).halted = s.halted := rfl

/-- `branchBitEq i b t` fires when bit `i` is *explicitly* specified to `b`. -/
theorem branchBitEq_pc_taken (i : Fin 8) (b : Bool) (t : Nat) (s : State)
    (h : s.cur i = some b) :
    (executeInstr (.branchBitEq i b t) s).pc = t := by
  show (if s.cur i = some b then ({ s with pc := t } : State)
        else { s with pc := s.pc + 1 }).pc = t
  rw [if_pos h]

/-- `branchBitEq i b t` falls through when bit `i` is *not* explicitly `b`,
    including the `none` (unspecified) case — partial states do not commit. -/
theorem branchBitEq_pc_skip (i : Fin 8) (b : Bool) (t : Nat) (s : State)
    (h : s.cur i ≠ some b) :
    (executeInstr (.branchBitEq i b t) s).pc = s.pc + 1 := by
  show (if s.cur i = some b then ({ s with pc := t } : State)
        else { s with pc := s.pc + 1 }).pc = s.pc + 1
  rw [if_neg h]

/-- Specialisation: `branchBitEq` on an *unspecified* bit always falls through. -/
theorem branchBitEq_pc_unspec (i : Fin 8) (b : Bool) (t : Nat) (s : State)
    (h : s.cur i = none) :
    (executeInstr (.branchBitEq i b t) s).pc = s.pc + 1 := by
  apply branchBitEq_pc_skip
  rw [h]; intro h'; cases h'

@[simp] theorem branchBitEq_cur (i : Fin 8) (b : Bool) (t : Nat) (s : State) :
    (executeInstr (.branchBitEq i b t) s).cur = s.cur := by
  show (if s.cur i = some b then ({ s with pc := t } : State)
        else { s with pc := s.pc + 1 }).cur = s.cur
  by_cases h : s.cur i = some b
  · rw [if_pos h]
  · rw [if_neg h]

@[simp] theorem branchBitEq_halted (i : Fin 8) (b : Bool) (t : Nat) (s : State) :
    (executeInstr (.branchBitEq i b t) s).halted = s.halted := by
  show (if s.cur i = some b then ({ s with pc := t } : State)
        else { s with pc := s.pc + 1 }).halted = s.halted
  by_cases h : s.cur i = some b
  · rw [if_pos h]
  · rw [if_neg h]

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
