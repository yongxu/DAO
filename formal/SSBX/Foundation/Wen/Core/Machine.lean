/-
# Foundation.Wen.Core.Machine — single-step + fuel-bounded execution

The operational semantics of the PartialCell-native ISA.  `executeInstr`
maps each `Instr` to its `State → State` action; `step` fetches the next
instruction; `runFuel` iterates `step` up to a bound.

The crucial PartialCell-native fact: the `merge` instruction *may halt
the machine* if the merge target is incompatible with the current state.
This is the operational realisation of "不通" — when a sentence contains
contradictory specifications, the machine cannot proceed.
-/

import SSBX.Foundation.Wen.Core.State

namespace SSBX.Foundation.Wen.Core

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
  | .push =>
      { s with history := s.cur :: s.history, pc := s.pc + 1 }
  | .pop =>
      match s.history with
      | []      => { s with pc := s.pc + 1 }
      | c :: rs => { s with cur := c, history := rs, pc := s.pc + 1 }
  | .flipBit i =>
      { s with
        cur := fun j => if j = i then (s.cur j).map (!·) else s.cur j,
        pc := s.pc + 1 }
  | .writeBit i b =>
      { s with
        cur := fun j => if j = i then some b else s.cur j,
        pc := s.pc + 1 }
  | .xorMask m =>
      { s with
        cur := fun j => (s.cur j).map (· != m j),
        pc := s.pc + 1 }
  | .branchBitEq i b t =>
      if s.cur i = some b then
        { s with pc := t }
      else
        { s with pc := s.pc + 1 }
  | .jump t =>
      { s with pc := t }
  | .halt =>
      { s with halted := true }
  | .mergePrior =>
      match s.history with
      | []      => { s with pc := s.pc + 1 }
      | h :: _  =>
        match PartialCell.merge s.cur h with
        | some c' => { s with cur := c', pc := s.pc + 1 }
        | none    => { s with halted := true }  -- 不通 → halt

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

/-! ### Phase E.3 — push / pop / flipBit / writeBit / xorMask -/

@[simp] theorem push_pc (s : State) : (executeInstr .push s).pc = s.pc + 1 := rfl
@[simp] theorem push_cur (s : State) : (executeInstr .push s).cur = s.cur := rfl
@[simp] theorem push_history (s : State) :
    (executeInstr .push s).history = s.cur :: s.history := rfl
@[simp] theorem push_halted (s : State) :
    (executeInstr .push s).halted = s.halted := rfl

@[simp] theorem pop_pc (s : State) : (executeInstr .pop s).pc = s.pc + 1 := by
  show (match s.history with
        | []      => ({ s with pc := s.pc + 1 } : State)
        | c :: rs => { s with cur := c, history := rs, pc := s.pc + 1 }).pc
       = s.pc + 1
  cases s.history <;> rfl

@[simp] theorem pop_halted (s : State) : (executeInstr .pop s).halted = s.halted := by
  show (match s.history with
        | []      => ({ s with pc := s.pc + 1 } : State)
        | c :: rs => { s with cur := c, history := rs, pc := s.pc + 1 }).halted
       = s.halted
  cases s.history <;> rfl

theorem pop_cur_empty (s : State) (h : s.history = []) :
    (executeInstr .pop s).cur = s.cur := by
  show (match s.history with
        | []      => ({ s with pc := s.pc + 1 } : State)
        | c :: rs => { s with cur := c, history := rs, pc := s.pc + 1 }).cur
       = s.cur
  rw [h]

theorem pop_cur_cons (c : PartialCell 8) (rs : List (PartialCell 8)) (s : State)
    (h : s.history = c :: rs) :
    (executeInstr .pop s).cur = c := by
  show (match s.history with
        | []      => ({ s with pc := s.pc + 1 } : State)
        | c' :: rs' => { s with cur := c', history := rs', pc := s.pc + 1 }).cur
       = c
  rw [h]

@[simp] theorem flipBit_pc (i : Fin 8) (s : State) :
    (executeInstr (.flipBit i) s).pc = s.pc + 1 := rfl
@[simp] theorem flipBit_halted (i : Fin 8) (s : State) :
    (executeInstr (.flipBit i) s).halted = s.halted := rfl
@[simp] theorem flipBit_cur_at (i : Fin 8) (s : State) :
    (executeInstr (.flipBit i) s).cur i = (s.cur i).map (!·) := by
  show (if i = i then (s.cur i).map (!·) else s.cur i)
       = (s.cur i).map (!·)
  rw [if_pos rfl]
@[simp] theorem flipBit_cur_other (i j : Fin 8) (s : State) (h : j ≠ i) :
    (executeInstr (.flipBit i) s).cur j = s.cur j := by
  show (if j = i then (s.cur j).map (!·) else s.cur j) = s.cur j
  rw [if_neg h]

@[simp] theorem writeBit_pc (i : Fin 8) (b : Bool) (s : State) :
    (executeInstr (.writeBit i b) s).pc = s.pc + 1 := rfl
@[simp] theorem writeBit_halted (i : Fin 8) (b : Bool) (s : State) :
    (executeInstr (.writeBit i b) s).halted = s.halted := rfl
@[simp] theorem writeBit_cur_at (i : Fin 8) (b : Bool) (s : State) :
    (executeInstr (.writeBit i b) s).cur i = some b := by
  show (if i = i then some b else s.cur i) = some b
  rw [if_pos rfl]
@[simp] theorem writeBit_cur_other (i j : Fin 8) (b : Bool) (s : State) (h : j ≠ i) :
    (executeInstr (.writeBit i b) s).cur j = s.cur j := by
  show (if j = i then some b else s.cur j) = s.cur j
  rw [if_neg h]

@[simp] theorem xorMask_pc (m : R 8) (s : State) :
    (executeInstr (.xorMask m) s).pc = s.pc + 1 := rfl
@[simp] theorem xorMask_halted (m : R 8) (s : State) :
    (executeInstr (.xorMask m) s).halted = s.halted := rfl
@[simp] theorem xorMask_cur (m : R 8) (s : State) (j : Fin 8) :
    (executeInstr (.xorMask m) s).cur j = (s.cur j).map (· != m j) := rfl

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

/-! ### Phase E.4 — `mergePrior` (cross-substrate: history × merge) -/

/-- `mergePrior` always advances pc by 1 — both in the empty-history
    branch, the successful-merge branch, and the halt branch (since we
    don't move pc on halt either, but the *pre-halt* pc is unchanged;
    we state it as pc+1 only when no halt occurs).  Here we cover the
    no-history case where the instruction is a pure pc-advance. -/
theorem mergePrior_pc_empty (s : State) (h : s.history = []) :
    (executeInstr .mergePrior s).pc = s.pc + 1 := by
  show (match s.history with
        | []      => ({ s with pc := s.pc + 1 } : State)
        | hd :: _ =>
          match PartialCell.merge s.cur hd with
          | some c' => { s with cur := c', pc := s.pc + 1 }
          | none    => { s with halted := true }).pc
       = s.pc + 1
  rw [h]

/-- `mergePrior` is a no-op on `cur` when history is empty. -/
theorem mergePrior_cur_empty (s : State) (h : s.history = []) :
    (executeInstr .mergePrior s).cur = s.cur := by
  show (match s.history with
        | []      => ({ s with pc := s.pc + 1 } : State)
        | hd :: _ =>
          match PartialCell.merge s.cur hd with
          | some c' => { s with cur := c', pc := s.pc + 1 }
          | none    => { s with halted := true }).cur
       = s.cur
  rw [h]

/-- When history has a head `hd` and the merge succeeds, `cur` becomes
    `mergeFn s.cur hd` and pc advances. -/
theorem mergePrior_cur_success (s : State) (hd : PartialCell 8)
    (rest : List (PartialCell 8)) (hh : s.history = hd :: rest)
    (hc : PartialCell.compatible s.cur hd) :
    (executeInstr .mergePrior s).cur = PartialCell.mergeFn s.cur hd := by
  have hm : PartialCell.merge s.cur hd = some (PartialCell.mergeFn s.cur hd) := by
    unfold PartialCell.merge; rw [if_pos hc]
  simp [executeInstr, hh, hm]

/-- When history has a head and the merge fails (`不通`), the machine halts. -/
theorem mergePrior_halted_conflict (s : State) (hd : PartialCell 8)
    (rest : List (PartialCell 8)) (hh : s.history = hd :: rest)
    (hc : ¬ PartialCell.compatible s.cur hd) :
    (executeInstr .mergePrior s).halted = true := by
  have hm : PartialCell.merge s.cur hd = none := by
    unfold PartialCell.merge; rw [if_neg hc]
  simp [executeInstr, hh, hm]

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

end SSBX.Foundation.Wen.Core
