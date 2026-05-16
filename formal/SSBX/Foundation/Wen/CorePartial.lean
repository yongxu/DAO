/-
# `SSBX.Foundation.Wen.CorePartial` — PartialCell-native interpreter (Phase E.1)

The §3.7-aligned rewrite of `Foundation/Wen/Core/`.  Where the legacy
core operates on `R 8 = Fin 8 → Bool` (fully-specified bit vectors),
CorePartial operates on `PartialCell 8 = Fin 8 → Option Bool` — partial
states are first-class.

## Module map

* `Instruction.lean` — 5-constructor `Instr` (nop / merge / restrict /
  jump / halt).  `merge` and `restrict` are first-class instructions;
  the partial-cell algebra is now part of the ISA.
* `State.lean`       — `State` record with `cur : PartialCell 8`,
  initial state = 道.
* `Machine.lean`     — `executeInstr`, `step`, `runFuel`, basic
  theorems, and the `mergeCells` extractor that bridges to Phase D's
  `mergeAll`.
* `Examples.lean`    — demo programs: empty, halt, pin-a-bit, 不通-halt.

## Doctrinal alignment

Per §3.7 (操作 ≡ 位 ≡ 内容): in CorePartial, the state IS a partial cell,
and the partial-cell algebra primitives (merge, restrict) ARE
instructions.  No category split between "data" and "operation".

## Roadmap

* **Phase E.1** (this file): scaffold + linear-control interpreter.
* **Phase E.2**: conditional branches (`branchBitEq i b t` adapted to
  partial states), equivalence theorem with legacy `Wen.Core` on the
  shared semantics.
* **Phase E.3+**: migrate Kernel / MetaInterp / upstream consumers.
-/

import SSBX.Foundation.Wen.CorePartial.Instruction
import SSBX.Foundation.Wen.CorePartial.State
import SSBX.Foundation.Wen.CorePartial.Machine
import SSBX.Foundation.Wen.CorePartial.Universal
import SSBX.Foundation.Wen.CorePartial.Examples
-- NOTE: `Bridge` is *not* in the umbrella because its `step_equiv` /
-- `runFuel_equiv` theorems carry `sorry` (Phase E.6 targets), which
-- poisons `native_decide` in any downstream module that imports the
-- umbrella.  Consumers that need the legacy ↔ CorePartial translation
-- should `import SSBX.Foundation.Wen.CorePartial.Bridge` directly.
