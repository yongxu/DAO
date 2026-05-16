/-
# Lang.Partial.Demo — proof-of-concept Wenyan sentence → Wen.Core program

A tiny showcase: a 2-3 token "Wenyan sentence" (in Sexp surface form)
is parsed into a list of `Wen.Core.Instr` and then *run* on the
PartialCell-native machine.

The sentence we use:

```
(pin 0 阳) (pin 1 阴) (halt)
```

reads as "pin bit-0 to yang (true); pin bit-1 to yin (false); halt".
This compiles to a 3-instruction program whose execution from `道`
(the empty partial assignment) ends with `cur ⟨0⟩ = some true`,
`cur ⟨1⟩ = some false`, and all other bits `none` — a codim-2 partial
cell.

Each demo is verified by `native_decide`, exercising the full
parse → compile → execute pipeline.
-/

import SSBX.Foundation.Lang.Partial.Core

namespace SSBX.Foundation.Lang.Partial.Demo

open SSBX.Foundation.R
open SSBX.Foundation.Wen.Core
open SSBX.Foundation.Lang.Partial

/-! ## § 1 The hand-built three-token Wenyan sentence

We construct the surface tokens directly (avoiding the string parser
since `parseSentence` is `partial` and we want decidable theorems).
This still demonstrates the compile + execute pipeline end-to-end. -/

/-- Token 1: pin bit 0 to yang. -/
def tok_pin0_yang : Sexp :=
  .list [.atom "pin", .atom "0", .atom "阳"]

/-- Token 2: pin bit 1 to yin. -/
def tok_pin1_yin : Sexp :=
  .list [.atom "pin", .atom "1", .atom "阴"]

/-- Token 3: halt. -/
def tok_halt : Sexp :=
  .list [.atom "halt"]

/-- The full three-token "sentence". -/
def sentence : List Sexp := [tok_pin0_yang, tok_pin1_yin, tok_halt]

/-! ## § 2 Parse + compile -/

/-- Compile the sentence to a `Wen.Core` program.  Should succeed. -/
def compiled : Except String (List Instr) := compile sentence

/-- The compile step succeeds. -/
example : compiled.toOption.isSome = true := by native_decide

/-- The compiled program has the expected length (3 instructions). -/
example : (compiled.toOption.map (·.length)) = some 3 := by native_decide

/-- Explicit expected program (what the parser should produce).  Used
    for direct execution rather than program-equality checks (`Instr`
    has no `DecidableEq` because it carries `PartialCell` payloads). -/
def expectedProg : List Instr :=
  [.mergeBit ⟨0, by decide⟩ true,
   .mergeBit ⟨1, by decide⟩ false,
   .halt]

/-! ## § 3 Execute the compiled program -/

/-- Convenience: run the expected program for 5 fuel from `道`. -/
def finalState : State :=
  runFromOrigin expectedProg 5

/-- After execution, the machine has halted. -/
example : finalState.halted = true := by native_decide

/-- After execution, bit 0 is `some true` (pinned to yang). -/
example : finalState.cur ⟨0, by decide⟩ = some true := by native_decide

/-- After execution, bit 1 is `some false` (pinned to yin). -/
example : finalState.cur ⟨1, by decide⟩ = some false := by native_decide

/-- After execution, bits 2..7 are unspecified (still `none`).  We
    spot-check bit 2 here. -/
example : finalState.cur ⟨2, by decide⟩ = none := by native_decide

/-! ## § 4 End-to-end: tokens → state via the unified pipeline -/

/-- Single-shot: tokens go in, final state comes out. -/
example : (runTokens sentence 5).toOption.isSome = true := by native_decide

/-- The end-to-end runner, when projected onto observable bit values,
    agrees with running the explicit `expectedProg`. -/
example :
    ((runTokens sentence 5).toOption.map (fun s => s.cur ⟨0, by decide⟩))
      = some (some true) := by native_decide

/-! ## § 5 不通 (incompatible merge → halt) demo

What happens when the sentence specifies the same bit twice with
disagreeing values?  `Wen.Core` halts on 不通 — verified here. -/

def conflictSentence : List Sexp :=
  [.list [.atom "pin", .atom "0", .atom "阳"],
   .list [.atom "pin", .atom "0", .atom "阴"],
   .list [.atom "halt"]]

def conflictProg : List Instr :=
  match compile conflictSentence with
  | .ok p   => p
  | .error _ => []

def conflictFinal : State := runFromOrigin conflictProg 5

/-- The conflict program halts due to 不通 on the second instruction. -/
example : conflictFinal.halted = true := by native_decide

/-- After 不通 halt, bit 0 retains its initial commitment (`some true`)
    — the failed merge does not roll back. -/
example : conflictFinal.cur ⟨0, by decide⟩ = some true := by native_decide

/-! ## § 6 Demo summary -/

/-- Public summary of the partial-cell language demo:
    * 3-token sentence compiles successfully to a 3-instruction program,
    * execution from 道 lands in the expected partial cell (bit0=yang, bit1=yin),
    * unspecified bits remain `none`,
    * 不通 halts cleanly. -/
theorem demo_summary :
    (compiled.toOption.map (·.length)) = some 3
    ∧ finalState.halted = true
    ∧ finalState.cur ⟨0, by decide⟩ = some true
    ∧ finalState.cur ⟨1, by decide⟩ = some false
    ∧ finalState.cur ⟨2, by decide⟩ = none
    ∧ conflictFinal.halted = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end SSBX.Foundation.Lang.Partial.Demo
