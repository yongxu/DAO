/-
# GodelR8 — Gödel/Halting undecidability at the R₈ = Cell256 layer

> **Doctrinal cross-reference**: `docs-next/10_formal_形式/wen-substrate.md`
> v1.0.3 §4.10 (R-Family as Substrate of Decidable Formal Systems).
> Specifically §4.10.2 (Gödel incompleteness in R-Family) and §4.10.3
> (Halting problem in R-Family): undecidability lives at the
> **unbounded finite countable layer** `⋃_N R_N`, not at `R_∞`.
> R_8 = Hexagram × Shi (V₄) = 256 cells is the **first culturally
> salient articulation layer** (§3.5.5) where this diagonal is
> stateable in the Yi-Hexagram naming overlay.
>
> **Historical note**: the canonical pre-Phase-F proof was originally
> on the abandoned 192-cell layer (`Cell192 := Hexagram × Fin 3` with
> Z/3 cyclic Shi), `Foundation/Bagua/GodelLi.lean` (988 LOC, 49
> theorems, 1 axiom). Was preserved on branch `salvage/cell192-full`
> (commit `da09d63`, 2026-05-15); **branch deleted 2026-05-16** after
> confirming the R_8 / V₄ migration (Phase F.2) was complete and the
> salvage was no longer needed. The commit hash `da09d63` may still
> be reachable via reflog for ~90 days; after that, gc-collected.
> The R_8 / V₄ migration replaced the Z/3 cyclic Shi with the V₄
> Klein four-group `{道, 已, 今, 未}` and re-proved the diagonal on
> the 256-cell layer; this file is the re-export anchor under the
> name requested by wen-substrate.

## Z/3 essentiality — answered

**Z/3 is NOT essential** to the Gödel proof.  The salvage
`GodelLi.lean` uses the Shi component only as:

  1. A *carrier* (`Cell192 := Hexagram × Shi`, 192 = 64×3 cells).
  2. A passive label set written by `setShi` and read by `branchShiEq`,
     both of which require only `DecidableEq` on Shi.
  3. `cuoState` (the cuo-symmetry operator on YiState) acts trivially
     on the Shi component (`(h, s) ↦ (h.cuo, s)`).

The Z/3 group operations `Shi.next`, `Shi.prev`, `next_three` exist
in the legacy Cell192 module but **are never used inside `GodelLi`**.
Consequently V₄ works as a *drop-in*: 4 elements give strictly more
room than 3, and the R 2 Klein-four four-group's involutive structure
(complement / reverse / cuoZong) replaces the cyclic Z/3 successor
without disturbing any theorem of the Gödel proof.

The Phase F.2 migration confirmed this in practice: the entire
49-theorem GodelLi was reproved on Cell256 with no structural
changes to the diagonal argument (only the type signature
`Cell192 → R 8` was retargeted).

## Architecture of this file

This file is a thin **re-export anchor** under the requested
`Wen.MetaInterp.GodelR8` namespace.  The actual proofs already live
in two canonical Cell256 modules:

* `Foundation/Atlas/Yi/Diagonal.lean` (647 LOC, **0 axioms**,
  **0 sorry**): language-independent R₈ kernel on `Wen.Core`'s
  `Instr` ISA; `KleeneInverter` as a `Prop` hypothesis, not an
  axiom.  This is the **canonical R₈ Gödel theorem**.
* `Foundation/Atlas/Yi/Classical/Diagonal/GodelLi.lean` (1309 LOC,
  **1 axiom** = `kleene_recursion_axiom`, **0 sorry**): the
  Cell256-migrated full Yi-flavoured port with `YiInstr` ISA on
  `Hexagram × Shi` (V₄, 256 cells).  This is the Atlas-Yi overlay.

Both are wired into `formal/SSBX.lean`.  This re-export gives them
a single discoverable name under `Wen.MetaInterp` so that downstream
work building the actual `metaInterpProg : List YiInstr` (witness
for `KleeneInverter`) can directly state its target as discharging
the hypothesis of `halts_undecidable_under_kleene` below.

## Constraints obeyed

  * **0 sorry**.
  * **0 new axioms** (the language-independent kernel uses
    `KleeneInverter` as a `Prop` hypothesis; the YiInstr variant's
    existing `kleene_recursion_axiom` is not re-introduced here).
  * No new mathematical content; aliases and a public bundle only.
-/

import SSBX.Foundation.Atlas.Yi.Diagonal

namespace SSBX.Foundation.Wen.MetaInterp.GodelR8

open SSBX.Foundation.R
open SSBX.Foundation.Wen.Core
open SSBX.Foundation.Atlas.Yi.Diagonal

/-! ## § 1 Canonical R₈ aliases (language-independent kernel)

These re-export the Atlas-Yi language-independent forms on
`Wen.Core`'s `R 8` machine.  The names here use the
`Wen.MetaInterp.GodelR8` namespace and append an `_r8` suffix where
ambiguous, so they coexist cleanly with the Atlas-Yi originals.
-/

/-- **R₈ Halts predicate**: `p` halts on input `inp : R 8` iff some
    fuel makes `Wen.Core.runFuel`'s halt flag true.

    Re-export of `Atlas.Yi.Diagonal.Halts` — see that module for the
    Σ₁ shape and `halts_iff_exists_fuel` derivation. -/
abbrev Halts_r8 (p : List Instr) (inp : R 8) : Prop := Halts p inp

/-- **R₈ Kleene-style inverter** (Prop, not axiom): for every Lean
    Bool decider on `(p, inp)`, there is a program `D` such that
    `Halts D inp ↔ decide D inp = false`.

    Re-export of `Atlas.Yi.Diagonal.KleeneInverter`.  A witness will
    be built by `Foundation/Wen/MetaInterp/` once the universal
    interpreter + s-m-n machinery is complete; until then this
    statement is used as a hypothesis only. -/
abbrev KleeneInverter_r8 : Prop := KleeneInverter

/-! ## § 2 The R₈ Gödel theorem (conditional)

The **headline statement** as requested by wen-substrate §4.10.
-/

/-- **Gödel/Halting undecidability at R₈** (conditional version):

    Under the Kleene-inverter hypothesis (a Prop, no axiom), the
    halting predicate on `(List Instr, R 8)` is **not** decidable
    by any Lean `Bool` function.  Standard diagonal argument.

    This is the precise wen-substrate.md §4.10.3 claim formalised
    on R₈: the bounded-vs-unbounded boundary within `⋃_N R_N`
    crosses at the unbounded-finite layer, of which `R 8` (the
    256-cell Cartesian space) is the first culturally salient
    instance.

    Re-export of `Atlas.Yi.Diagonal.halts_undecidable_under_kleene`. -/
theorem godel_r8_undecidability (h_kleene : KleeneInverter_r8) :
    ¬ ∃ decide : List Instr → R 8 → Bool,
        ∀ p inp, decide p inp = true ↔ Halts_r8 p inp :=
  halts_undecidable_under_kleene h_kleene

/-- **Complement undecidability at R₈** (conditional): the
    complement `¬ Halts` is likewise undecidable.

    Re-export of `Atlas.Yi.Diagonal.not_halts_undecidable_under_kleene`. -/
theorem not_halts_r8_undecidability (h_kleene : KleeneInverter_r8) :
    ¬ ∃ decide : List Instr → R 8 → Bool,
        ∀ p inp, decide p inp = true ↔ ¬ Halts_r8 p inp :=
  not_halts_undecidable_under_kleene h_kleene

/-- **Fixed-input Halts undecidability at R₈** (conditional): for any
    fixed `inp₀ : R 8`, deciding `Halts p inp₀` over the program alone
    is undecidable.

    Re-export of `Atlas.Yi.Diagonal.halts_at_fixed_undecidable_under_kleene`. -/
theorem halts_at_fixed_r8_undecidability
    (h_kleene : KleeneInverter_r8) (inp₀ : R 8) :
    ¬ ∃ decide : List Instr → Bool,
        ∀ p, decide p = true ↔ Halts_r8 p inp₀ :=
  halts_at_fixed_undecidable_under_kleene h_kleene inp₀

/-! ## § 3 Rice four-images on R₈

The four uniform halting properties (Π_all / Π_some / Π_some_no /
Π_none) are all undecidable.  In the 道家四象 (four-symbols) frame:

| Π          | Form                       | 四象         |
|------------|----------------------------|--------------|
| Π_all      | `∀ inp, Halts p inp`      | 太阳 (everywhere halts)   |
| Π_some     | `∃ inp, Halts p inp`      | 少阳 (somewhere halts)    |
| Π_some_no  | `∃ inp, ¬ Halts p inp`    | 少阴 (somewhere doesn't)  |
| Π_none     | `∀ inp, ¬ Halts p inp`    | 太阴 (nowhere halts)      |

Re-export of `Atlas.Yi.Diagonal.rice_four_images_under_kleene`.
-/

/-- **Rice 四象 at R₈** (conditional bundle): all four uniform
    halting properties are undecidable under the Kleene-inverter
    hypothesis. -/
theorem rice_four_images_r8 (h_kleene : KleeneInverter_r8) :
    (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∀ inp, Halts_r8 p inp)
    ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∃ inp, Halts_r8 p inp)
    ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∃ inp, ¬ Halts_r8 p inp)
    ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∀ inp, ¬ Halts_r8 p inp) :=
  rice_four_images_under_kleene h_kleene

/-! ## § 4 Public summary

A single bundle that exposes the canonical R₈ Gödel content.
-/

/-- **Public R₈ Gödel summary** (wen-substrate §4.10 anchor):

    Bundles the canonical R₈ undecidability results.  All conditional
    on `KleeneInverter_r8` (a `Prop` hypothesis to be discharged by
    the in-progress `metaInterpProg` construction); the §1-§2
    non-trivial halting witnesses from `Atlas.Yi.Diagonal` are
    unconditional but not re-bundled here. -/
theorem godel_r8_summary :
    (KleeneInverter_r8 →
        ¬ ∃ decide : List Instr → R 8 → Bool,
            ∀ p inp, decide p inp = true ↔ Halts_r8 p inp)
    ∧ (KleeneInverter_r8 →
        ¬ ∃ decide : List Instr → R 8 → Bool,
            ∀ p inp, decide p inp = true ↔ ¬ Halts_r8 p inp)
    ∧ (∀ inp₀ : R 8, KleeneInverter_r8 →
        ¬ ∃ decide : List Instr → Bool,
            ∀ p, decide p = true ↔ Halts_r8 p inp₀)
    ∧ (KleeneInverter_r8 →
        (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∀ inp, Halts_r8 p inp)
        ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∃ inp, Halts_r8 p inp)
        ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∃ inp, ¬ Halts_r8 p inp)
        ∧ (¬ ∃ d : List Instr → Bool, ∀ p, d p = true ↔ ∀ inp, ¬ Halts_r8 p inp)) :=
  ⟨godel_r8_undecidability,
   not_halts_r8_undecidability,
   fun inp₀ h_kleene => halts_at_fixed_r8_undecidability h_kleene inp₀,
   rice_four_images_r8⟩

end SSBX.Foundation.Wen.MetaInterp.GodelR8
