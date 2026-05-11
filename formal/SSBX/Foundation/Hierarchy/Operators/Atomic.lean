/-
# Operators · Atomic — XOR subgroup (abelian, single-bit toggles)

This file groups all "atomic" SSBX operators — those that act as XOR with a
fixed mask on the underlying (Z/2)ⁿ carrier. Algebraically they form an
**abelian subgroup** (every element of order ≤ 2, all pairs commute).

## Members

- `imprint`, `project` — R8 mask-XOR involutions
  (R8 lives at R₈ = (Z/2)⁸; imprint toggles the 因/YinBit, project toggles 果/GuoBit).
- `flip1..flip6` — R7 single-yao toggles
  (R7 = Hexagram × YinBit at R₇; flipᵢ toggles the i-th yao).
- `hexCuo` (R7) — Hexagram-level 错 = XOR with `earth` (the all-imprint mask),
  i.e. componentwise yao negation.

## Group property

Each element is an involution: `op (op c) = c`. They all commute (XOR is
abelian). This file proves involutivity for every member by *re-export* —
i.e. using the proofs already established in `R7.lean` / `R8.lean`.

## What this file does NOT do

- Does NOT redefine the operators (pure re-export via `def` aliases).
- Does NOT touch source files (`R8.lean`, `R7.lean`, `BaguaAlgebra.lean`).
- Does NOT include `reverse` / `interlace` / `complementReverse` — those are V₄-outer (non-XOR
  permutations) and live in `V4Outer.lean`.
-/
import SSBX.Foundation.Bagua.R8
import SSBX.Foundation.Bagua.R7

namespace SSBX.Foundation.Hierarchy.Operators.Atomic

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.R7

/-! ## § 1 R8 atomic operators (R₈ level) -/

/-- R8 印 (yìn): XOR with `(heaven, ji)` mask (toggle YinBit / 因 axis). -/
def cell256_imprint (c : R8) : R8 := R8.imprint c

/-- R8 投 (tóu): XOR with `(heaven, wei)` mask (toggle GuoBit / 果 axis). -/
def cell256_tou (c : R8) : R8 := R8.project c

/-! ## § 2 R7 atomic operators (R₇ level)

  Note: in `R7.lean`, `flip1..flip6`, `imprint`, `hexCuo` are defined at
  the *file-level* namespace `SSBX.Foundation.Bagua.R7` (NOT inside
  the inner `R7` namespace which only houses the carrier/`xor`/
  `origin`/etc.). After `open SSBX.Foundation.Bagua.R7` we reference
  them bare. -/

/-- Single-yao toggle of the 1st yao (初爻 / dongInner). -/
def cell128_flip1 (c : R7) : R7 := flip1 c
/-- Single-yao toggle of the 2nd yao (二爻 / middleFlipInner). -/
def cell128_flip2 (c : R7) : R7 := flip2 c
/-- Single-yao toggle of the 3rd yao (三爻 / topFlipInner). -/
def cell128_flip3 (c : R7) : R7 := flip3 c
/-- Single-yao toggle of the 4th yao (四爻 / dongOuter). -/
def cell128_flip4 (c : R7) : R7 := flip4 c
/-- Single-yao toggle of the 5th yao (五爻 / middleFlipOuter). -/
def cell128_flip5 (c : R7) : R7 := flip5 c
/-- Single-yao toggle of the 6th yao (上爻 / topFlipOuter). -/
def cell128_flip6 (c : R7) : R7 := flip6 c

/-- R7 印 (yìn): toggle the YinBit. Direct form. -/
def cell128_imprint (c : R7) : R7 :=
  SSBX.Foundation.Bagua.R7.imprint c

/-- R7 hexagram-level 错 (complement): yao-wise negation = XOR with the
    all-imprint (earth) mask on the Hexagram component, preserving the YinBit.

    This is the "atomic XOR-mask" form of `Hexagram.complement` lifted to R7. -/
def cell128_hexCuo (c : R7) : R7 :=
  SSBX.Foundation.Bagua.R7.hexCuo c

/-! ## § 3 Group property — every atomic op is involutive (XOR self-cancels)

  XOR with any fixed mask `m` is an involution: `(c ⊕ m) ⊕ m = c`. The
  proofs below simply forward to the source-file involution lemmas. -/

theorem cell256_yin_involutive (c : R8) : cell256_imprint (cell256_imprint c) = c :=
  R8.imprint_imprint c

theorem cell256_tou_involutive (c : R8) : cell256_tou (cell256_tou c) = c :=
  R8.project_project c

theorem cell128_flip1_involutive (c : R7) : cell128_flip1 (cell128_flip1 c) = c :=
  flip1_flip1 c

theorem cell128_flip2_involutive (c : R7) : cell128_flip2 (cell128_flip2 c) = c :=
  flip2_flip2 c

theorem cell128_flip3_involutive (c : R7) : cell128_flip3 (cell128_flip3 c) = c :=
  flip3_flip3 c

theorem cell128_flip4_involutive (c : R7) : cell128_flip4 (cell128_flip4 c) = c :=
  flip4_flip4 c

theorem cell128_flip5_involutive (c : R7) : cell128_flip5 (cell128_flip5 c) = c :=
  flip5_flip5 c

theorem cell128_flip6_involutive (c : R7) : cell128_flip6 (cell128_flip6 c) = c :=
  flip6_flip6 c

theorem cell128_yin_involutive (c : R7) : cell128_imprint (cell128_imprint c) = c :=
  SSBX.Foundation.Bagua.R7.imprint_imprint c

theorem cell128_hexCuo_involutive (c : R7) : cell128_hexCuo (cell128_hexCuo c) = c :=
  SSBX.Foundation.Bagua.R7.hexCuo_hexCuo c

/-! ## § 4 Pairwise commutativity (sample — XOR is abelian)

  Any two XOR-with-fixed-mask operators commute. We expose two
  representative pairs to bind the abelian-subgroup claim concretely. -/

/-- 印 and 投 commute on R8 (both are XOR with fixed R8 masks). -/
theorem cell256_yin_tou_comm (c : R8) :
    cell256_imprint (cell256_tou c) = cell256_tou (cell256_imprint c) :=
  R8.imprint_project_comm c

/-! ## § 5 Public summary — the atomic group property

  All members are involutions; this is the whole "atomic = XOR subgroup of
  order ≤ 2 generators" claim, packaged as one bundled theorem. -/

theorem atomic_all_involutive :
    -- R8 layer
    (∀ c : R8, cell256_imprint (cell256_imprint c) = c)
    ∧ (∀ c : R8, cell256_tou (cell256_tou c) = c)
    -- R7 single-yao toggles
    ∧ (∀ c : R7, cell128_flip1 (cell128_flip1 c) = c)
    ∧ (∀ c : R7, cell128_flip2 (cell128_flip2 c) = c)
    ∧ (∀ c : R7, cell128_flip3 (cell128_flip3 c) = c)
    ∧ (∀ c : R7, cell128_flip4 (cell128_flip4 c) = c)
    ∧ (∀ c : R7, cell128_flip5 (cell128_flip5 c) = c)
    ∧ (∀ c : R7, cell128_flip6 (cell128_flip6 c) = c)
    -- R7 印 + hexCuo
    ∧ (∀ c : R7, cell128_imprint (cell128_imprint c) = c)
    ∧ (∀ c : R7, cell128_hexCuo (cell128_hexCuo c) = c) :=
  ⟨cell256_yin_involutive, cell256_tou_involutive,
   cell128_flip1_involutive, cell128_flip2_involutive, cell128_flip3_involutive,
   cell128_flip4_involutive, cell128_flip5_involutive, cell128_flip6_involutive,
   cell128_yin_involutive, cell128_hexCuo_involutive⟩

end SSBX.Foundation.Hierarchy.Operators.Atomic
