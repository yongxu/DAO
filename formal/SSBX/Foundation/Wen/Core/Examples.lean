/-
# Foundation.Wen.Core.Examples — basic R 8 bit-machine test programs

A small gallery of example programs, all expressed purely on `R 8`
with **no Yi / Hexagram / Shi / Pauli** semantics.  These witnesses
exercise each of the eight primitive instructions and demonstrate
their algebraic identities.

## What is here

* **§ 1 `nopProg`** — a single `nop` then `halt`.
* **§ 2 `flipBit0Prog`** — flip bit 0, then halt.
* **§ 3 `setAllBitsProg`** — write `true` into every bit.
* **§ 4 `loopProg`** — an unconditional jump-to-self (non-halting).
* **§ 5 `branchProg`** — a conditional branch on bit 0.
* **§ 6 `pushPopProg`** — push, mutate, then pop (round-trip).
* **§ 7 `xorMaskProg`** — XOR with a constant mask.

For each program we give:
* The program (as `List Instr`).
* A small fuel bound that suffices for termination.
* Algebraic correctness lemmas (`runFuel`-based).

These doubled as smoke tests for the interpreter.  No `sorry`, no
`axiom`, no Atlas overlay.

## Doctrinal anchor

* `r8.md` v0.2 §15.10 (interpreter primitives).
* `wen-algebra.md` v0.6 §10.7 (interpreter foundation).
-/

import SSBX.Foundation.Wen.Core.Instruction
import SSBX.Foundation.Wen.Core.State
import SSBX.Foundation.Wen.Core.Machine

-- The `by decide` proofs inside `⟨k, by decide⟩` Fin literals are
-- elaborated to closed proofs that the underlying linter then flags
-- as "never executed" inside the larger tactic block.  This is
-- cosmetic; silence locally.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace SSBX.Foundation.Wen.Core
namespace Examples

open SSBX.Foundation.R
open SSBX.Foundation.R.R (basis)

/-! ## § 0 A useful step-unfolding helper

To keep example proofs readable, we expose a single rewriting lemma
that unfolds one `runFuel (n+1)` step on a non-halted state.  This
hides the inner `if/match` and lets each example's correctness proof
proceed by chaining a small number of `rfl`-friendly rewrites.
-/

/-- Unfold one `runFuel (n+1)` step on a non-halted state. -/
theorem runFuel_succ_of_not_halted (prog : List Instr) (n : Nat) (s : State)
    (h : s.halted = false) :
    runFuel prog (n+1) s = runFuel prog n (step prog s) := by
  show (if s.halted = true then s else runFuel prog n (step prog s))
      = runFuel prog n (step prog s)
  simp [h]

/-! ## § 1 The `nop` program -/

/-- `nopProg`: a `nop` then a `halt`. -/
def nopProg : List Instr := [.nop, .halt]

/-- After 2 fuel units, `nopProg` halts. -/
theorem nopProg_halts (input : R 8) :
    (run nopProg input 2).halted = true := by
  -- Two steps: nop (pc 0 → 1), halt (pc 1 → halted).
  unfold run
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  -- step nopProg (init input) = executeInstr nop (init input)
  show (runFuel nopProg 1 (executeInstr .nop (State.init input))).halted = true
  -- After nop, pc=1, not halted; next is halt → halted.
  rw [runFuel_succ_of_not_halted _ _ _
      (by rfl : (executeInstr .nop (State.init input)).halted = false)]
  -- step on the post-nop state fetches instruction at pc=1 = halt
  show (runFuel nopProg 0
      (executeInstr .halt (executeInstr .nop (State.init input)))).halted = true
  rfl

/-- After 2 fuel units, `nopProg` leaves the input cell unchanged. -/
theorem nopProg_preserves_input (input : R 8) :
    (run nopProg input 2).cur = input := by
  unfold run
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  show (runFuel nopProg 1 (executeInstr .nop (State.init input))).cur = input
  rw [runFuel_succ_of_not_halted _ _ _
      (by rfl : (executeInstr .nop (State.init input)).halted = false)]
  show (runFuel nopProg 0
      (executeInstr .halt (executeInstr .nop (State.init input)))).cur = input
  rfl

/-! ## § 2 The `flipBit 0` program -/

/-- `flipBit0Prog`: flip bit 0, then halt. -/
def flipBit0Prog : List Instr := [.flipBit ⟨0, by decide⟩, .halt]

/-- After 2 fuel units, `flipBit0Prog` halts with bit 0 of the input
    inverted. -/
theorem flipBit0Prog_correct (input : R 8) :
    (run flipBit0Prog input 2).cur =
      flipBitR8 ⟨0, by decide⟩ input := by
  unfold run
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  show (runFuel flipBit0Prog 1
      (executeInstr (.flipBit ⟨0, by decide⟩) (State.init input))).cur
    = flipBitR8 ⟨0, by decide⟩ input
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (executeInstr (.flipBit ⟨0, by decide⟩) (State.init input)).halted = false)]
  rfl

theorem flipBit0Prog_halts (input : R 8) :
    (run flipBit0Prog input 2).halted = true := by
  unfold run
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  show (runFuel flipBit0Prog 1
      (executeInstr (.flipBit ⟨0, by decide⟩) (State.init input))).halted = true
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (executeInstr (.flipBit ⟨0, by decide⟩) (State.init input)).halted = false)]
  rfl

/-! ## § 3 The `setAllBitsProg`

Write `true` into every one of the 8 bits, then halt.
-/

/-- Sets every bit to `true`, then halts.  9 instructions. -/
def setAllBitsProg : List Instr :=
  [ .writeBit ⟨0, by decide⟩ true
  , .writeBit ⟨1, by decide⟩ true
  , .writeBit ⟨2, by decide⟩ true
  , .writeBit ⟨3, by decide⟩ true
  , .writeBit ⟨4, by decide⟩ true
  , .writeBit ⟨5, by decide⟩ true
  , .writeBit ⟨6, by decide⟩ true
  , .writeBit ⟨7, by decide⟩ true
  , .halt ]

/-- Helper: chain 9 `runFuel_succ_of_not_halted` rewrites. -/
private theorem setAllBitsProg_unrolls (input : R 8) :
    runFuel setAllBitsProg 9 (State.init input)
      = step setAllBitsProg
          (step setAllBitsProg
            (step setAllBitsProg
              (step setAllBitsProg
                (step setAllBitsProg
                  (step setAllBitsProg
                    (step setAllBitsProg
                      (step setAllBitsProg
                        (step setAllBitsProg (State.init input))))))))) := by
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step setAllBitsProg (State.init input)).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step setAllBitsProg (step setAllBitsProg (State.init input))).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
        (State.init input)))).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
        (step setAllBitsProg (State.init input))))).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
        (step setAllBitsProg (step setAllBitsProg (State.init input)))))).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
        (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
          (State.init input))))))).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
        (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
          (step setAllBitsProg (State.init input)))))))).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
        (step setAllBitsProg (step setAllBitsProg (step setAllBitsProg
          (step setAllBitsProg (step setAllBitsProg
            (State.init input))))))))).halted = false)]
  rfl

/-- After 9 fuel units, `setAllBitsProg` is halted. -/
theorem setAllBitsProg_halts (input : R 8) :
    (run setAllBitsProg input 9).halted = true := by
  unfold run
  rw [setAllBitsProg_unrolls]
  rfl

/-! ## § 4 The infinite loop -/

/-- `loopProg`: jump to self, forever. -/
def loopProg : List Instr := [.jump 0]

/-- One step of `loopProg` from the init state returns the init state. -/
theorem step_loopProg_init (input : R 8) :
    step loopProg (State.init input) = State.init input := by
  unfold step State.init
  show (if ({ cur := input, history := [], pc := 0, halted := false } : State).halted
        then ({ cur := input, history := [], pc := 0, halted := false } : State)
        else match loopProg[({ cur := input, history := [], pc := 0, halted := false } : State).pc]? with
          | none => { ({ cur := input, history := [], pc := 0, halted := false } : State) with halted := true }
          | some instr => executeInstr instr { cur := input, history := [], pc := 0, halted := false })
      = { cur := input, history := [], pc := 0, halted := false }
  rfl

/-- `runFuel` on `loopProg` is stuttering: every fuel amount returns
    the init state. -/
theorem runFuel_loopProg_init (input : R 8) (n : Nat) :
    runFuel loopProg n (State.init input) = State.init input := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
          (State.init input).halted = false)]
      rw [step_loopProg_init]
      exact ih

/-- `loopProg` never reaches a halted state. -/
theorem loopProg_never_halts (input : R 8) (n : Nat) :
    (run loopProg input n).halted = false := by
  unfold run
  rw [runFuel_loopProg_init]
  rfl

/-! ## § 5 The branch program

A simple conditional: branch on bit 0.  If bit 0 = true, jump to
pc=3 (the "true" branch); else fall through to pc=1 (the "false"
branch).
-/

/-- `branchProg`: tests bit 0; writes a fixed value to bit 7 in each
    branch (true → set bit 7 true; false → set bit 7 false). -/
def branchProg : List Instr :=
  [ .branchBitEq ⟨0, by decide⟩ true 3   -- pc=0
  , .writeBit ⟨7, by decide⟩ false       -- pc=1
  , .halt                                -- pc=2
  , .writeBit ⟨7, by decide⟩ true        -- pc=3
  , .halt ]                              -- pc=4

/-- If bit 0 of the input is `true`, `branchProg` jumps to pc=3 in
    one step. -/
theorem branchProg_takes_true_branch (input : R 8)
    (h : input ⟨0, by decide⟩ = true) :
    step branchProg (State.init input)
      = { State.init input with pc := 3 } := by
  -- Convert `input ⟨0, by decide⟩` to `input 0` (they're the same Fin).
  have h' : input 0 = true := h
  show (if (State.init input).halted = true
        then State.init input
        else match branchProg[(State.init input).pc]? with
          | none => { State.init input with halted := true }
          | some instr => executeInstr instr (State.init input))
      = { State.init input with pc := 3 }
  have hinit : (State.init input).halted = false := rfl
  simp only [hinit]
  show (match branchProg[(State.init input).pc]? with
        | none => { State.init input with halted := true }
        | some instr => executeInstr instr (State.init input))
      = { State.init input with pc := 3 }
  show executeInstr (.branchBitEq ⟨0, by decide⟩ true 3) (State.init input)
      = { State.init input with pc := 3 }
  show (if (State.init input).cur ⟨0, by decide⟩ = true
        then { State.init input with pc := 3 }
        else { State.init input with pc := (State.init input).pc + 1 })
      = { State.init input with pc := 3 }
  have : (State.init input).cur ⟨0, by decide⟩ = true := h
  rw [if_pos this]

/-- If bit 0 of the input is `false`, `branchProg` falls through to
    pc=1 in one step. -/
theorem branchProg_takes_false_branch (input : R 8)
    (h : input ⟨0, by decide⟩ = false) :
    step branchProg (State.init input)
      = { State.init input with pc := 1 } := by
  show (if (State.init input).halted = true
        then State.init input
        else match branchProg[(State.init input).pc]? with
          | none => { State.init input with halted := true }
          | some instr => executeInstr instr (State.init input))
      = { State.init input with pc := 1 }
  have hinit : (State.init input).halted = false := rfl
  simp only [hinit]
  show (match branchProg[(State.init input).pc]? with
        | none => { State.init input with halted := true }
        | some instr => executeInstr instr (State.init input))
      = { State.init input with pc := 1 }
  show executeInstr (.branchBitEq ⟨0, by decide⟩ true 3) (State.init input)
      = { State.init input with pc := 1 }
  show (if (State.init input).cur ⟨0, by decide⟩ = true
        then { State.init input with pc := 3 }
        else { State.init input with pc := (State.init input).pc + 1 })
      = { State.init input with pc := 1 }
  have hne : (State.init input).cur ⟨0, by decide⟩ ≠ true := by
    show input ⟨0, by decide⟩ ≠ true
    rw [h]; decide
  rw [if_neg hne]
  show { State.init input with pc := 0 + 1 } = { State.init input with pc := 1 }
  rfl

/-! ## § 6 The push/pop round-trip

Demonstrates the linear-tape memory: push the current cell, mutate
the cell, then pop to restore.  Final `cur` equals the input. -/

/-- `pushPopProg`: push, flip bit 0, pop, halt. -/
def pushPopProg : List Instr :=
  [ .push                                -- pc=0
  , .flipBit ⟨0, by decide⟩              -- pc=1
  , .pop                                 -- pc=2
  , .halt ]                              -- pc=3

/-- After 4 fuel units, `pushPopProg` restores the input cell. -/
theorem pushPopProg_restores (input : R 8) :
    (run pushPopProg input 4).cur = input := by
  unfold run
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  -- After push: cur=input, history=[input], pc=1
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step pushPopProg (State.init input)).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step pushPopProg (step pushPopProg (State.init input))).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step pushPopProg (step pushPopProg (step pushPopProg (State.init input)))).halted = false)]
  -- Now after 4 steps: cur=input, halted=true.
  rfl

/-- After 4 fuel units, `pushPopProg` halts. -/
theorem pushPopProg_halts (input : R 8) :
    (run pushPopProg input 4).halted = true := by
  unfold run
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step pushPopProg (State.init input)).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step pushPopProg (step pushPopProg (State.init input))).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step pushPopProg (step pushPopProg (step pushPopProg (State.init input)))).halted = false)]
  rfl

/-! ## § 7 The xorMask program -/

/-- `xorMaskProg m`: XOR with `m`, then halt. -/
def xorMaskProg (m : R 8) : List Instr := [.xorMask m, .halt]

/-- After 2 fuel units, `xorMaskProg m` produces `input + m`. -/
theorem xorMaskProg_correct (input m : R 8) :
    (run (xorMaskProg m) input 2).cur = input + m := by
  unfold run
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step (xorMaskProg m) (State.init input)).halted = false)]
  rfl

theorem xorMaskProg_halts (input m : R 8) :
    (run (xorMaskProg m) input 2).halted = true := by
  unfold run
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl : (State.init input).halted = false)]
  rw [runFuel_succ_of_not_halted _ _ _ (by rfl :
      (step (xorMaskProg m) (State.init input)).halted = false)]
  rfl

/-- XORing with `0` is the identity. -/
theorem xorMaskProg_zero (input : R 8) :
    (run (xorMaskProg 0) input 2).cur = input := by
  rw [xorMaskProg_correct]
  simp

/-- Applying `xorMaskProg m` twice cancels (involution): XORing twice
    with the same mask gives back the input.  Proved via the
    `R 8`-group identity `v + m + m = v`. -/
theorem xorMaskProg_twice (input m : R 8) :
    (run (xorMaskProg m) ((run (xorMaskProg m) input 2).cur) 2).cur = input := by
  rw [xorMaskProg_correct, xorMaskProg_correct]
  rw [add_assoc]
  show input + (m + m) = input
  rw [R.add_self]
  simp

end Examples
end SSBX.Foundation.Wen.Core
