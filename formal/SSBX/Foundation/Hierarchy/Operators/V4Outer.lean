/-
# Operators · V4Outer — V₄ Klein-four outer operators (non-XOR permutations)

This file groups SSBX operators that are **not** XOR-with-fixed-mask. They
involve genuine permutations of the underlying carrier:

- `reverse` (综) — yao-order reversal: `(y₁..y₆) ↦ (y₆..y₁)`. Hexagram time-reversal.
- `interlace` (互) — inner-trigram extraction: `(y₁..y₆) ↦ (y₂, y₃, y₄, y₃, y₄, y₅)`.
- `complementReverse` (错综) — composite `complement ∘ reverse` (or equivalently `reverse ∘ complement`).

## V₄ Klein-four relations

`{id, complement, reverse, complementReverse}` is a **Klein four-group** at the Hexagram level:
- Every element is its own inverse: `x² = id`.
- The composite of any two non-identity elements is the third.
- All elements commute.

Although `complement` itself is XOR (atomic), the V₄ *structure* lives here because
its non-trivial part (`reverse`, `complementReverse`) requires the permutation. `interlace` is
included as a sibling non-XOR operator (it is NOT in the V₄ — it has fixed
points 乾/坤 and is not invertible — but it is the canonical other "outer"
op in the operator family).

## What this file does NOT do

- Does NOT redefine the operators (re-export via `def` aliases).
- Does NOT touch source files.
- Does NOT include atomic XOR ops — those live in `Atomic.lean`.
-/
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Bagua.Cell256
import SSBX.Foundation.Bagua.Cell128

namespace SSBX.Foundation.Hierarchy.Operators.V4Outer

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.Cell128

/-! ## § 1 Hexagram-level V₄ outer operators

  The Klein four-group lives at R₆ on `Hexagram`. -/

/-- 综 (reverse): hexagram yao-order reversal. NON-XOR permutation. -/
def hex_zong (h : Hexagram) : Hexagram := Hexagram.reverse h

/-- 错综 (complementReverse): composite `complement ∘ reverse`. -/
def hex_cuoZong (h : Hexagram) : Hexagram := Hexagram.complementReverse h

/-- 互 (interlace): inner-trigram extraction. NON-XOR (and NOT invertible — has
    乾/坤 as fixed points; included here as the canonical sibling non-XOR
    operator, not as a V₄ member). -/
def hex_hu (h : Hexagram) : Hexagram := Hexagram.interlace h

/-- 错 (complement): yao-wise negation. Atomic-XOR (with earth mask), but included
    here as a V₄ generator for the Klein-four relations. -/
def hex_cuo (h : Hexagram) : Hexagram := Hexagram.complement h

/-! ## § 2 Cell128 lifts (preserve YinBit)

  Note: in `Cell128.lean`, `hexZong` and `hexHu` live at the *file-level*
  namespace `SSBX.Foundation.Bagua.Cell128` (NOT inside the inner `Cell128`
  namespace). After `open SSBX.Foundation.Bagua.Cell128` we reference bare. -/

/-- 综 lifted to Cell128 (preserves the YinBit / 因 axis). -/
def cell128_zong (c : Cell128) : Cell128 := hexZong c

/-- 互 lifted to Cell128. -/
def cell128_hu (c : Cell128) : Cell128 := hexHu c

/-! ## § 3 Cell256 lifts (preserve Shi V₄) -/

/-- 综 lifted to Cell256 (preserves the Shi V₄ component). -/
def cell256_zong (c : Cell256) : Cell256 := Cell256.hexZong c

/-- 互 lifted to Cell256. -/
def cell256_hu (c : Cell256) : Cell256 := Cell256.hexHu c

/-! ## § 4 V₄ Klein-four relations on Hexagram

  `{id, complement, reverse, complementReverse}` ≅ V₄. We prove each defining relation:
  - involutivity (`x² = id`) for complement, reverse, complementReverse
  - commutativity (`complement ∘ reverse = reverse ∘ complement`)
  - composite identity (`complementReverse = complement ∘ reverse`) -/

/-- V₄ relation 1: 综² = id. -/
theorem zong_involutive (h : Hexagram) : hex_zong (hex_zong h) = h :=
  Hexagram.reverse_involutive h

/-- V₄ relation 2: 错² = id. -/
theorem cuo_involutive (h : Hexagram) : hex_cuo (hex_cuo h) = h :=
  Hexagram.complement_involutive h

/-- V₄ relation 3: 错综² = id. -/
theorem cuoZong_involutive (h : Hexagram) : hex_cuoZong (hex_cuoZong h) = h :=
  Hexagram.cuoZong_cuoZong h

/-- V₄ relation 4: 错 and 综 commute (the group is abelian). -/
theorem cuo_zong_commute (h : Hexagram) :
    hex_cuo (hex_zong h) = hex_zong (hex_cuo h) :=
  Hexagram.complement_reverse_comm h

/-- V₄ relation 5: 错综 = 错 ∘ 综 (defining the composite). -/
theorem cuoZong_eq_cuo_zong (h : Hexagram) :
    hex_cuoZong h = hex_cuo (hex_zong h) := rfl

/-! ## § 5 Cell128 / Cell256 lift involutivity -/

theorem cell128_zong_involutive (c : Cell128) : cell128_zong (cell128_zong c) = c :=
  hexZong_hexZong c

theorem cell256_zong_involutive (c : Cell256) : cell256_zong (cell256_zong c) = c :=
  Cell256.hexZong_hexZong c

/-! ## § 6 互 fixed-point characterisation (sibling outer op)

  `interlace` is NOT a V₄ member — it has the two fixed points {乾, 坤} and is
  not an involution in general. The fixed-point characterisation is its
  signature property. -/

theorem hu_fixed_iff (h : Hexagram) :
    hex_hu h = h ↔ h = Hexagram.heaven ∨ h = Hexagram.earth :=
  Hexagram.interlace_fixed_point h

/-! ## § 7 Public summary — the V₄ Klein-four group property + outer interlace

  Bundles the full V₄ group axioms on `{id, complement, reverse, complementReverse}` plus the
  characterisation of the sibling outer operator `interlace`. -/

theorem v4_outer_summary :
    -- Identity-element fact (`id² = id` is reflexive; we record it for
    -- structural completeness of the V₄ multiplication table).
    (∀ h : Hexagram, h = h)
    -- Three non-trivial involutions (Klein-four element orders all ≤ 2)
    ∧ (∀ h : Hexagram, hex_cuo (hex_cuo h) = h)
    ∧ (∀ h : Hexagram, hex_zong (hex_zong h) = h)
    ∧ (∀ h : Hexagram, hex_cuoZong (hex_cuoZong h) = h)
    -- Abelian (complement ∘ reverse = reverse ∘ complement)
    ∧ (∀ h : Hexagram, hex_cuo (hex_zong h) = hex_zong (hex_cuo h))
    -- Composite definition (complementReverse = complement ∘ reverse)
    ∧ (∀ h : Hexagram, hex_cuoZong h = hex_cuo (hex_zong h))
    -- Cell128 / Cell256 lift involutivity (reverse is preserved through lifts)
    ∧ (∀ c : Cell128, cell128_zong (cell128_zong c) = c)
    ∧ (∀ c : Cell256, cell256_zong (cell256_zong c) = c)
    -- Sibling outer interlace fixed-point characterisation
    ∧ (∀ h : Hexagram, hex_hu h = h ↔ h = Hexagram.heaven ∨ h = Hexagram.earth) :=
  ⟨fun _ => rfl, cuo_involutive, zong_involutive, cuoZong_involutive,
   cuo_zong_commute, cuoZong_eq_cuo_zong,
   cell128_zong_involutive, cell256_zong_involutive,
   hu_fixed_iff⟩

end SSBX.Foundation.Hierarchy.Operators.V4Outer
