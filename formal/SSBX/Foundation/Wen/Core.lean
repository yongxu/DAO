/-
# `SSBX.Foundation.Wen.Core` — umbrella import for the language-
independent R 8 bit-machine interpreter core

Canonical doctrine: `docs-next/10_formal_形式/wen-algebra.md` v0.6 +
`docs-next/10_formal_形式/r8.md` v0.2.

The Wen Core operates **directly on `R 8 = Fin 8 → Bool`** with a
language-independent instruction set.  No semantic naming (Yi 爻/时态,
Hexagram, Shi, Bagua, Pauli, …) appears anywhere in this subtree;
overlays live in `Foundation/Atlas/`.

This umbrella pulls the whole subtree in one import.

## Module map

* `Instruction.lean` — the 8-constructor `Instr` inductive (plus the
  `xorMask` `R 8`-add primitive); language-independent.
* `State.lean`       — `State` record + carrier-level update helpers
  (`flipBitR8`, `writeBitR8`) and their algebraic identities.
* `Machine.lean`     — single-step `executeInstr`, fetch-decode `step`,
  fuel-bounded `runFuel`, and core algebraic theorems
  (`nop_advances_pc`, `flipBit_involutive`, `writeBit_idempotent`,
  `runFuel_halt_idempotent`, `runFuel_fuel_monotone_halted`, …).
* `Universal.lean`   — `InstrEncoding`, `encodeProgInput`, `equivObs`,
  `Simulates`, `IsUniversal`, `UniversalInterpreterExists` (target
  spec for `Foundation/Wen/MetaInterp/`).
* `Examples.lean`    — a small gallery of test programs:
  `nopProg`, `flipBit0Prog`, `setAllBitsProg`, `loopProg`,
  `branchProg`, `pushPopProg`, `xorMaskProg`.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §10.7 (Interpreter Foundation).
* `r8.md` v0.2 §15.10 (Interpreter primitives), §11
  (behavior/judgment).
* Language-independence principle: `wen-algebra.md` v0.6 §0.3,
  §0.5; `r8.md` v0.2 §0.4.

## Relationship to legacy `Foundation/Bagua/BaguaTuring.lean`

`BaguaTuring.lean` defines a Yi-named state machine where state =
`Hexagram × Shi` (a 256-cell carrier identified via Yi vocabulary).
This Wen Core operates on the same 256-cell carrier algebraically
(`R 8`), but **without** any Yi names.  The two coexist:

* `BaguaTuring.lean` — Yi-named overlay; retained.
* `Wen.Core` — language-independent foundation; new in v0.6.

Future integration (out of scope here): an Atlas module
`Foundation/Atlas/Yi/Bridge.lean` will define a bijection
`Hexagram × Shi ≃ R 8` and a translation from `YiInstr` to `Instr`
that respects single-step semantics.
-/

import SSBX.Foundation.Wen.Core.Instruction
import SSBX.Foundation.Wen.Core.State
import SSBX.Foundation.Wen.Core.Machine
import SSBX.Foundation.Wen.Core.Universal
import SSBX.Foundation.Wen.Core.Examples
