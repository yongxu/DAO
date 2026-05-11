/-
# Operators · Atomic — XOR subgroup (abelian, single-bit toggles)

This file groups all "atomic" SSBX operators — those that act as XOR with a
fixed mask on the underlying (Z/2)ⁿ carrier. Algebraically they form an
**abelian subgroup** (every element of order ≤ 2, all pairs commute).

## Members

- `yin`, `tou` — Cell256 mask-XOR involutions
  (Cell256 lives at R₈ = (Z/2)⁸; yin toggles the 因/YinBit, tou toggles 果/GuoBit).
- `flip1..flip6` — Cell128 single-yao toggles
  (Cell128 = Hexagram × YinBit at R₇; flipᵢ toggles the i-th yao).
- `hexCuo` (Cell128) — Hexagram-level 错 = XOR with `earth` (the all-yin mask),
  i.e. componentwise yao negation.

## Group property

Each element is an involution: `op (op c) = c`. They all commute (XOR is
abelian). This file proves involutivity for every member by *re-export* —
i.e. using the proofs already established in `Cell128.lean` / `Cell256.lean`.

## What this file does NOT do

- Does NOT redefine the operators (pure re-export via `def` aliases).
- Does NOT touch source files (`Cell256.lean`, `Cell128.lean`, `BaguaAlgebra.lean`).
- Does NOT include `reverse` / `interlace` / `complementReverse` — those are V₄-outer (non-XOR
  permutations) and live in `V4Outer.lean`.
-/
import SSBX.Foundation.Bagua.Cell256
import SSBX.Foundation.Bagua.Cell128

namespace SSBX.Foundation.Hierarchy.Operators.Atomic

open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.Cell128

/-! ## § 1 Cell256 atomic operators (R₈ level) -/

/-- Cell256 印 (yìn): XOR with `(heaven, ji)` mask (toggle YinBit / 因 axis). -/
def cell256_yin (c : Cell256) : Cell256 := Cell256.yin c

/-- Cell256 投 (tóu): XOR with `(heaven, wei)` mask (toggle GuoBit / 果 axis). -/
def cell256_tou (c : Cell256) : Cell256 := Cell256.tou c

/-! ## § 2 Cell128 atomic operators (R₇ level)

  Note: in `Cell128.lean`, `flip1..flip6`, `yin`, `hexCuo` are defined at
  the *file-level* namespace `SSBX.Foundation.Bagua.Cell128` (NOT inside
  the inner `Cell128` namespace which only houses the carrier/`xor`/
  `origin`/etc.). After `open SSBX.Foundation.Bagua.Cell128` we reference
  them bare. -/

/-- Single-yao toggle of the 1st yao (初爻 / dongInner). -/
def cell128_flip1 (c : Cell128) : Cell128 := flip1 c
/-- Single-yao toggle of the 2nd yao (二爻 / middleFlipInner). -/
def cell128_flip2 (c : Cell128) : Cell128 := flip2 c
/-- Single-yao toggle of the 3rd yao (三爻 / topFlipInner). -/
def cell128_flip3 (c : Cell128) : Cell128 := flip3 c
/-- Single-yao toggle of the 4th yao (四爻 / dongOuter). -/
def cell128_flip4 (c : Cell128) : Cell128 := flip4 c
/-- Single-yao toggle of the 5th yao (五爻 / middleFlipOuter). -/
def cell128_flip5 (c : Cell128) : Cell128 := flip5 c
/-- Single-yao toggle of the 6th yao (上爻 / topFlipOuter). -/
def cell128_flip6 (c : Cell128) : Cell128 := flip6 c

/-- Cell128 印 (yìn): toggle the YinBit. Direct form. -/
def cell128_yin (c : Cell128) : Cell128 :=
  SSBX.Foundation.Bagua.Cell128.yin c

/-- Cell128 hexagram-level 错 (complement): yao-wise negation = XOR with the
    all-yin (earth) mask on the Hexagram component, preserving the YinBit.

    This is the "atomic XOR-mask" form of `Hexagram.complement` lifted to Cell128. -/
def cell128_hexCuo (c : Cell128) : Cell128 :=
  SSBX.Foundation.Bagua.Cell128.hexCuo c

/-! ## § 3 Group property — every atomic op is involutive (XOR self-cancels)

  XOR with any fixed mask `m` is an involution: `(c ⊕ m) ⊕ m = c`. The
  proofs below simply forward to the source-file involution lemmas. -/

theorem cell256_yin_involutive (c : Cell256) : cell256_yin (cell256_yin c) = c :=
  Cell256.yin_yin c

theorem cell256_tou_involutive (c : Cell256) : cell256_tou (cell256_tou c) = c :=
  Cell256.tou_tou c

theorem cell128_flip1_involutive (c : Cell128) : cell128_flip1 (cell128_flip1 c) = c :=
  flip1_flip1 c

theorem cell128_flip2_involutive (c : Cell128) : cell128_flip2 (cell128_flip2 c) = c :=
  flip2_flip2 c

theorem cell128_flip3_involutive (c : Cell128) : cell128_flip3 (cell128_flip3 c) = c :=
  flip3_flip3 c

theorem cell128_flip4_involutive (c : Cell128) : cell128_flip4 (cell128_flip4 c) = c :=
  flip4_flip4 c

theorem cell128_flip5_involutive (c : Cell128) : cell128_flip5 (cell128_flip5 c) = c :=
  flip5_flip5 c

theorem cell128_flip6_involutive (c : Cell128) : cell128_flip6 (cell128_flip6 c) = c :=
  flip6_flip6 c

theorem cell128_yin_involutive (c : Cell128) : cell128_yin (cell128_yin c) = c :=
  SSBX.Foundation.Bagua.Cell128.yin_yin c

theorem cell128_hexCuo_involutive (c : Cell128) : cell128_hexCuo (cell128_hexCuo c) = c :=
  SSBX.Foundation.Bagua.Cell128.hexCuo_hexCuo c

/-! ## § 4 Pairwise commutativity (sample — XOR is abelian)

  Any two XOR-with-fixed-mask operators commute. We expose two
  representative pairs to bind the abelian-subgroup claim concretely. -/

/-- 印 and 投 commute on Cell256 (both are XOR with fixed Cell256 masks). -/
theorem cell256_yin_tou_comm (c : Cell256) :
    cell256_yin (cell256_tou c) = cell256_tou (cell256_yin c) :=
  Cell256.yin_tou_comm c

/-! ## § 5 Public summary — the atomic group property

  All members are involutions; this is the whole "atomic = XOR subgroup of
  order ≤ 2 generators" claim, packaged as one bundled theorem. -/

theorem atomic_all_involutive :
    -- Cell256 layer
    (∀ c : Cell256, cell256_yin (cell256_yin c) = c)
    ∧ (∀ c : Cell256, cell256_tou (cell256_tou c) = c)
    -- Cell128 single-yao toggles
    ∧ (∀ c : Cell128, cell128_flip1 (cell128_flip1 c) = c)
    ∧ (∀ c : Cell128, cell128_flip2 (cell128_flip2 c) = c)
    ∧ (∀ c : Cell128, cell128_flip3 (cell128_flip3 c) = c)
    ∧ (∀ c : Cell128, cell128_flip4 (cell128_flip4 c) = c)
    ∧ (∀ c : Cell128, cell128_flip5 (cell128_flip5 c) = c)
    ∧ (∀ c : Cell128, cell128_flip6 (cell128_flip6 c) = c)
    -- Cell128 印 + hexCuo
    ∧ (∀ c : Cell128, cell128_yin (cell128_yin c) = c)
    ∧ (∀ c : Cell128, cell128_hexCuo (cell128_hexCuo c) = c) :=
  ⟨cell256_yin_involutive, cell256_tou_involutive,
   cell128_flip1_involutive, cell128_flip2_involutive, cell128_flip3_involutive,
   cell128_flip4_involutive, cell128_flip5_involutive, cell128_flip6_involutive,
   cell128_yin_involutive, cell128_hexCuo_involutive⟩

end SSBX.Foundation.Hierarchy.Operators.Atomic
