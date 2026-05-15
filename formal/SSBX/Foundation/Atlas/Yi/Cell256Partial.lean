/-
# Foundation.Atlas.Yi.Cell256Partial — Cell256 ↔ PartialCell 8 bridge

This is the印/投 instance of the partial-cell view at the R₈ ceiling.

A `Cell256 = Hexagram × Shi` lifts canonically to a fully-specified
`PartialCell 8` via the 8-bit layout

    positions 0..5 = the six yao of the hexagram
    positions 6..7 = the two Shi bits (ji / wei)

Conversely, a `PartialCell 8` with full support recovers a unique
`Cell256` (via `fromPartial?`).

This file bridges the Atlas-named R₈ stratum with the language-
independent partial-cell substrate from `Foundation/R/PartialCell.lean`,
giving the Yi tradition its place in the partial-cell lattice without
the core having to know any Yi names.
-/

import SSBX.Foundation.R.PartialCell
import SSBX.Foundation.Atlas.Yi.Cell256

namespace SSBX.Foundation.Atlas.Yi.Cell256

open SSBX.Foundation.R

/-- Flatten `Cell256 = Hexagram × Shi` to `R 8`.
    Layout: yao 0..5 → positions 0..5, Shi bits → positions 6..7. -/
def toR8 (c : Cell256) : R 8 := fun i =>
  if h : i.val < 6 then c.1 ⟨i.val, h⟩
  else c.2 ⟨i.val - 6, by omega⟩

/-- Inflate `R 8` to `Cell256` via the inverse layout. -/
def fromR8 (v : R 8) : Cell256 :=
  (fun i : Fin 6 => v ⟨i.val, by omega⟩,
   fun i : Fin 2 => v ⟨i.val + 6, by omega⟩)

theorem fromR8_toR8 (c : Cell256) : fromR8 (toR8 c) = c := by
  rcases c with ⟨h, s⟩
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · funext i
    rcases i with ⟨k, hk⟩
    show toR8 (h, s) ⟨k, by omega⟩ = h ⟨k, hk⟩
    unfold toR8
    rw [dif_pos (show k < 6 from hk)]
  · funext i
    rcases i with ⟨k, hk⟩
    show toR8 (h, s) ⟨k + 6, by omega⟩ = s ⟨k, hk⟩
    unfold toR8
    rw [dif_neg (show ¬ k + 6 < 6 by omega)]
    congr 1

theorem toR8_fromR8 (v : R 8) : toR8 (fromR8 v) = v := by
  funext j
  rcases j with ⟨k, hk⟩
  unfold toR8 fromR8
  by_cases hcase : k < 6
  · rw [dif_pos hcase]
  · rw [dif_neg hcase]
    show v ⟨(k - 6) + 6, _⟩ = v ⟨k, hk⟩
    congr 1
    apply Fin.ext
    show (k - 6) + 6 = k
    omega

/-- Lift `Cell256` to a fully-specified `PartialCell 8` (印 at the ceiling). -/
def toPartial (c : Cell256) : PartialCell 8 := PartialCell.ofFull (toR8 c)

/-- Project `PartialCell 8` to `Cell256`; succeeds iff fully specified. -/
def fromPartial? (p : PartialCell 8) : Option Cell256 :=
  (PartialCell.toFull? p).map fromR8

@[simp] theorem fromPartial?_toPartial (c : Cell256) :
    fromPartial? (toPartial c) = some c := by
  unfold fromPartial? toPartial
  rw [PartialCell.toFull?_ofFull]
  simp [fromR8_toR8]

end SSBX.Foundation.Atlas.Yi.Cell256
