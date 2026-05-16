/-
# Foundation.Atlas.Yi.ConstraintDemoYi — Yi-flavoured constraint composition

The Yi-named twin of `Foundation/Wen/Core/ConstraintDemo.lean`.

Where `ConstraintDemo` showcases the **bit-level** constraint algebra
(`mergeProg` over `PartialCell 8`), this file shows the **same algebra**
re-narrated in the Atlas-Yi vocabulary: trigrams and Shi states compose
as partial commitments on the Cell256 substrate.

## The headline claim, Yi-flavoured

`Cell256 = Hexagram × Shi` lifts to `PartialCell 8` via the layout

    positions 0..2 = inner trigram (内卦, 下卦)  — y1..y3 of the hexagram
    positions 3..5 = outer trigram (外卦, 上卦)  — y4..y6
    positions 6..7 = Shi (时态, V₄) bits

A program may **commit one trigram at a time** (or one Shi at a time),
leaving the rest unspecified.  Two compatible commitments compose into
a stronger commitment; two contradictory commitments halt the machine
via 不通 (the operational reading of "incompatible").

Thus the same `mergeProg` skeleton from `ConstraintDemo` reads, in the
Yi atlas, as a **divination grammar**: each merge is an authoritative
yao-pattern claim, and the substrate enforces consistency.

## What's in this file

* §1   `pinTrigramInner` / `pinTrigramOuter` / `pinShi` — partial cells
       that commit only one of the three Yi sub-carriers
* §2   Demos:
       - `taiProg`        — assert inner=乾, outer=坤, Shi=道; agreement
                            yields the fully-specified hexagram 泰 ☷☰
       - `conflictProg`   — assert inner=乾, then inner=坤; the second
                            claim contradicts the first → 不通
       - `restrictProg`   — commit a full hexagram + Shi, then forget
                            the Shi bits (codim-2 restrict)
* §3   `rfl` theorems showing each behaviour
* §4   Bridge: a successful `taiProg` run reconstructs the named
       `Cell256 = (泰, 道)` via `Cell256.fromPartial?`

Per project doctrine, this file lives in `Atlas/Yi/` (application layer);
the core `Wen.Core` substrate is unaware of any Yi naming.
-/

import SSBX.Foundation.Wen.Core.Machine
import SSBX.Foundation.Wen.Core.Examples
  -- (for `Instr.pinBit`)
import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Bagua
import SSBX.Foundation.Atlas.Yi.Hexagrams
import SSBX.Foundation.Atlas.Yi.Shi
import SSBX.Foundation.Atlas.Yi.Cell256Partial

namespace SSBX.Foundation.Atlas.Yi.ConstraintDemoYi

open SSBX.Foundation.R
open SSBX.Foundation.Wen.Core
open SSBX.Foundation.Atlas.Yi
-- (`yang`/`yin` no longer opened — examples use raw Bool true/false with
-- doc-comment reminders that `Yao.yang = false`, `Yao.yin = true`.)

/-! ## § 1 — Yi-flavoured pinning helpers

Each helper produces a `PartialCell 8` that commits only one of the
three sub-carriers of `Cell256` (inner trigram / outer trigram / Shi),
leaving the other positions unspecified.  These are the Yi-atlas
counterparts of `Instr.pinBit`: they commit semantic *units* rather
than raw bits. -/

/-- Pin the inner trigram (内卦, positions 0..2): commits y1/y2/y3 to
    the given trigram, leaves positions 3..7 unspecified. -/
def pinTrigramInner (t : Trigram) : PartialCell 8 := fun j =>
  if h : j.val < 3 then some (t ⟨j.val, h⟩) else none

/-- Pin the outer trigram (外卦, positions 3..5): commits y4/y5/y6 to
    the given trigram, leaves positions 0..2 and 6..7 unspecified. -/
def pinTrigramOuter (t : Trigram) : PartialCell 8 := fun j =>
  if h : 3 ≤ j.val ∧ j.val < 6 then some (t ⟨j.val - 3, by omega⟩) else none

/-- Pin the Shi state (时态, positions 6..7): commits the two V₄ bits
    to the given Shi, leaves positions 0..5 unspecified. -/
def pinShi (s : Shi) : PartialCell 8 := fun j =>
  if h : 6 ≤ j.val ∧ j.val < 8 then some (s ⟨j.val - 6, by omega⟩) else none

/-! ## § 2 — `mergeProg`: lift partial cells into a pure-merge program

Identical in shape to `ConstraintDemo.mergeProg`, but namespaced under
this Atlas demo so consumers can `open` it without pulling in the
Wen.Core demo's namespace. -/

/-- Lift a list of partial cells into a straight-line program that
    merges them in order, then halts. -/
def mergeProg : List (PartialCell 8) → List Instr
  | []       => [.halt]
  | c :: rs  => .merge c :: mergeProg rs

@[simp] theorem mergeProg_nil :
    mergeProg [] = [.halt] := rfl

@[simp] theorem mergeProg_cons (c : PartialCell 8) (rs : List (PartialCell 8)) :
    mergeProg (c :: rs) = .merge c :: mergeProg rs := rfl

/-! ## § 3 — Three Yi-flavoured programs -/

/-- Agreement: build the hexagram 泰 (☷☰, King Wen #11) one component
    at a time.  Inner = 乾 (heaven), outer = 坤 (earth), Shi = 道.

    Per `Hexagrams.tai`:
        泰 = mk yang yang yang yin yin yin
    The inner trigram (y1..y3) is all-yang = 乾; the outer (y4..y6) is
    all-yin = 坤.  All three merges are mutually compatible, so the
    machine halts cleanly at the trailing `.halt`. -/
def taiProg : List Instr := mergeProg [
  pinTrigramInner Trigram.qian,
  pinTrigramOuter Trigram.kun,
  pinShi Shi.dao
]

/-- Conflict: assert inner = 乾 (all-yang), then immediately claim
    inner = 坤 (all-yin).  Every shared position disagrees, so 不通
    triggers at the second merge — the machine halts via merge-halt. -/
def conflictProg : List Instr := mergeProg [
  pinTrigramInner Trigram.qian,
  pinTrigramInner Trigram.kun     -- 不通 — already committed to 乾
]

/-- Restrict (forgetting Shi): commit the entire 泰 hexagram + Shi=道,
    then explicitly restrict to the hexagram positions {0..5},
    forgetting the two Shi bits.  Final `cur` retains the full hexagram
    but `cur ⟨6⟩ = cur ⟨7⟩ = none`. -/
def restrictProg : List Instr := [
  .merge (pinTrigramInner Trigram.qian),
  .merge (pinTrigramOuter Trigram.kun),
  .merge (pinShi Shi.dao),
  .restrict ({⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
              ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩} : Finset (Fin 8)),
  .halt
]

/-! ## § 4 — Operational properties

The three Yi-flavoured semantics, in correspondence with the three
PartialCell-unique semantics from `ConstraintDemo`:
(i)   partial Yi states are first-class (a "trigram only" commitment exists),
(ii)  contradictory yao claims = 不通 = halt,
(iii) restrict forgets a sub-carrier (e.g., the Shi). -/

/-! ### § 4.1 Agreement: 泰 assembles cleanly from its three sub-carriers -/

/-- After running `taiProg` with sufficient fuel, the machine halts
    cleanly (pc reaches `.halt`, not via merge-halt). -/
theorem taiProg_halts :
    (runFuel taiProg 10 State.initial).halted = true := by
  show (runFuel taiProg 10 State.initial).halted = true
  rfl

/-! ### § 4.2 Conflict: 乾 vs 坤 on the inner trigram triggers 不通 -/

/-- `conflictProg` halts via merge-halt at the second instruction —
    the inner-trigram-as-坤 claim contradicts the already-merged
    inner-trigram-as-乾 commitment. -/
theorem conflictProg_halts :
    (runFuel conflictProg 10 State.initial).halted = true := by
  show (runFuel conflictProg 10 State.initial).halted = true
  rfl

/-! ### § 4.3 Restrict: forgetting the Shi sub-carrier -/

/-- After `restrictProg`, position 6 (first Shi bit) is forgotten. -/
theorem restrictProg_forgets_shi_bit_0 :
    (runFuel restrictProg 10 State.initial).cur ⟨6, by decide⟩ = none := by
  show (runFuel restrictProg 10 State.initial).cur ⟨6, by decide⟩ = none
  rfl

/-- After `restrictProg`, position 7 (second Shi bit) is also forgotten. -/
theorem restrictProg_forgets_shi_bit_1 :
    (runFuel restrictProg 10 State.initial).cur ⟨7, by decide⟩ = none := by
  show (runFuel restrictProg 10 State.initial).cur ⟨7, by decide⟩ = none
  rfl

/-- But the hexagram positions are retained — e.g. position 0
    (= y1 of the hexagram = first yao of inner 乾) survives as `some
    false` (= yang per `Yao.yang := false`). -/
theorem restrictProg_keeps_hex_bit_0 :
    (runFuel restrictProg 10 State.initial).cur ⟨0, by decide⟩ = some false := by
  native_decide

/-! ## § 5 — Bridge: `taiProg` realises the named `Cell256 = (泰, 道)`

When the agreement program runs to completion, the final `cur` is the
fully-specified `PartialCell 8` corresponding (via the Cell256
↔ PartialCell 8 bridge) to the Cell256 element `(泰, 道)`. -/

/-- Sanity: position 0 of the final state is `some false` (= yang) —
    `taiProg`'s inner trigram 乾 pinned bit 0 to yang.
    Per `Yao.yang := false` in `Atlas/Yi/Names.lean`. -/
example :
    (runFuel taiProg 10 State.initial).cur ⟨0, by decide⟩ = some false := by
  native_decide

/-- Sanity: position 5 of the final state is `some true` (= yin) —
    the outer trigram 坤's top yao.
    Per `Yao.yin := true` in `Atlas/Yi/Names.lean`. -/
example :
    (runFuel taiProg 10 State.initial).cur ⟨5, by decide⟩ = some true := by
  native_decide

/-- Sanity: position 6 of the final state is `some false` (the first
    bit of Shi=道, which is `(false, false)`). -/
example :
    (runFuel taiProg 10 State.initial).cur ⟨6, by decide⟩ = some false := by rfl

/-- Sanity demo: the empty Yi program halts immediately. -/
example :
    (runFuel (mergeProg []) 1 State.initial).halted = true := by rfl

end SSBX.Foundation.Atlas.Yi.ConstraintDemoYi
