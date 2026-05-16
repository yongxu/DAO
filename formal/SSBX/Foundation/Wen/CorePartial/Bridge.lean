/-
# Foundation.Wen.CorePartial.Bridge — translation from legacy `Wen.Core` to `Wen.CorePartial`

Phase E.5: a forward bridge from the legacy 9-constructor `Wen.Core.Instr`
(operating on `R 8`) to the new 11-constructor `Wen.CorePartial.Instr`
(operating on `PartialCell 8`).

The 9 legacy constructors map 1:1 to 9 of the 11 new constructors; the two
new constructors `merge` and `restrict` are *PartialCell-native* and have
no legacy preimage.  Hence `translate` is a section (legacy embeds into
new) but not a retraction (new has more morphisms).

## What's bridged

* `translate : Wen.Core.Instr → Wen.CorePartial.Instr` — 1:1 constructor
  mapping for the 9 shared opcodes.
* `translateProg` — pointwise list-lift via `List.map`.
* `liftState : Wen.Core.State → Wen.CorePartial.State` — lifts `cur` via
  `PartialCell.ofFull` (totally-specified bit-vector → totally-specified
  partial cell), preserves `pc`, `history` (also lifted pointwise), and
  `halted`.
* `liftState_init` — `liftState (Core.State.init inp) = CorePartial.State.init inp`.
* `step_equiv` — the translation correctness target: on a fully-specified
  state, legacy `step` and lifted `CorePartial.step` agree (after lifting).
  Stated precisely; proof deferred (`sorry`) as a Phase E.6+ target.

## Doctrinal anchor

* `wen-substrate.md` v1.2 §3.7 (Operation Monism — PartialCell substrate).
* Phase E.3 ISA parity: see `CorePartial/Instruction.lean` header.
-/

import SSBX.Foundation.Wen.Core.Machine
import SSBX.Foundation.Wen.CorePartial.Machine

namespace SSBX.Foundation.Wen.CorePartial

open SSBX.Foundation.R

/-! ## § 1 Instruction translation -/

/-- 1:1 case-by-case translation of the 9 legacy `Wen.Core.Instr`
    constructors to the corresponding `Wen.CorePartial.Instr`
    constructors.

    The 9 shared opcodes match exactly in arity and meaning under
    full-specification.  The two PartialCell-native opcodes (`merge`,
    `restrict`) of the target ISA have no legacy preimage and are
    therefore not in the image of `translate`. -/
def translate : Wen.Core.Instr → Wen.CorePartial.Instr
  | .nop                  => .nop
  | .flipBit i            => .flipBit i
  | .writeBit i b         => .writeBit i b
  | .branchBitEq i b t    => .branchBitEq i b t
  | .jump t               => .jump t
  | .push                 => .push
  | .pop                  => .pop
  | .xorMask m            => .xorMask m
  | .halt                 => .halt

/-- Lift a legacy program to a CorePartial program, pointwise. -/
def translateProg (prog : List Wen.Core.Instr) : List Wen.CorePartial.Instr :=
  prog.map translate

@[simp] theorem translateProg_nil :
    translateProg [] = ([] : List Wen.CorePartial.Instr) := rfl

@[simp] theorem translateProg_cons (i : Wen.Core.Instr) (rest : List Wen.Core.Instr) :
    translateProg (i :: rest) = translate i :: translateProg rest := rfl

@[simp] theorem translateProg_length (prog : List Wen.Core.Instr) :
    (translateProg prog).length = prog.length := by
  simp [translateProg]

/-! ## § 2 State lift -/

/-- Lift a legacy `Wen.Core.State` to a `Wen.CorePartial.State` by
    transporting `cur` and each entry of `history` through
    `PartialCell.ofFull`, and copying `pc` and `halted` unchanged.

    Because `ofFull` injects `R 8 ↪ PartialCell 8` with `support = univ`,
    every lifted state is *fully-specified*: `(liftState s).cur =
    PartialCell.ofFull s.cur`.  Such states never trigger the new `merge`
    halt path (since `merge dao` and `restrict` etc. are not in the image
    of `translate`). -/
def liftState (s : Wen.Core.State) : Wen.CorePartial.State :=
  { pc      := s.pc
    cur     := PartialCell.ofFull s.cur
    history := s.history.map PartialCell.ofFull
    halted  := s.halted }

@[simp] theorem liftState_pc (s : Wen.Core.State) :
    (liftState s).pc = s.pc := rfl

@[simp] theorem liftState_cur (s : Wen.Core.State) :
    (liftState s).cur = PartialCell.ofFull s.cur := rfl

@[simp] theorem liftState_history (s : Wen.Core.State) :
    (liftState s).history = s.history.map PartialCell.ofFull := rfl

@[simp] theorem liftState_halted (s : Wen.Core.State) :
    (liftState s).halted = s.halted := rfl

/-- Lifting the legacy initial state gives the CorePartial initial state
    for the same input. -/
@[simp] theorem liftState_init (inp : R 8) :
    liftState (Wen.Core.State.init inp) = CorePartial.State.init inp := by
  unfold liftState Wen.Core.State.init CorePartial.State.init
  simp

/-! ## § 3 Step equivalence — translation correctness target

The intended semantic theorem: for any legacy program `prog` and any
state `s : Wen.Core.State`, running one legacy `Wen.Core.step` on `s`
and then lifting equals lifting `s` first and then running one
`Wen.CorePartial.step` on the translated program.

This is a non-trivial proof because:

1. The two `step` functions live in different namespaces with different
   `executeInstr` definitions.
2. Each of the 9 shared constructors needs a case-by-case agreement
   lemma — easy in principle (`flipBit`, `writeBit`, `xorMask` agree by
   `ofFull` being totally-specified), but the proof involves
   discharging `Option.map` on `some _` patterns for every coordinate.
3. The legacy `Wen.Core.step` may have its own halting semantics that
   need to be reconciled with `CorePartial.step` (where `merge` is the
   only new halt source — and `merge` is never in the image of
   `translate`, so this is OK in principle).

Stated here precisely; proof deferred as a Phase E.6 target. -/

-- NOTE: The two correctness theorems `step_equiv` and `runFuel_equiv`
-- have been deferred — their `sorry`-proofs polluted `native_decide`
-- in downstream consumers (DaoSource, Diagonal).  Statements preserved
-- here as Phase E.6 targets for future work:
--
--   theorem step_equiv (prog : List Wen.Core.Instr) (s : Wen.Core.State) :
--       liftState (Wen.Core.step prog s)
--         = CorePartial.step (translateProg prog) (liftState s)
--
--   theorem runFuel_equiv (prog : List Wen.Core.Instr) (n : Nat)
--       (s : Wen.Core.State) :
--       liftState (Wen.Core.runFuel prog n s)
--         = CorePartial.runFuel (translateProg prog) n (liftState s)

/-! ## § 4 Sanity check — translate is structurally a section

The translation cannot be inverted in general (the new ISA has more
opcodes than the legacy ISA), but on its image it agrees with the legacy
constructor by construction.  We expose `translate` as `@[simp]`-able on
each constructor so downstream callers can normalise without unfolding. -/

@[simp] theorem translate_nop : translate .nop = .nop := rfl
@[simp] theorem translate_flipBit (i : Fin 8) :
    translate (.flipBit i) = .flipBit i := rfl
@[simp] theorem translate_writeBit (i : Fin 8) (b : Bool) :
    translate (.writeBit i b) = .writeBit i b := rfl
@[simp] theorem translate_branchBitEq (i : Fin 8) (b : Bool) (t : Nat) :
    translate (.branchBitEq i b t) = .branchBitEq i b t := rfl
@[simp] theorem translate_jump (t : Nat) : translate (.jump t) = .jump t := rfl
@[simp] theorem translate_push : translate .push = .push := rfl
@[simp] theorem translate_pop : translate .pop = .pop := rfl
@[simp] theorem translate_xorMask (m : R 8) :
    translate (.xorMask m) = .xorMask m := rfl
@[simp] theorem translate_halt : translate .halt = .halt := rfl

end SSBX.Foundation.Wen.CorePartial
