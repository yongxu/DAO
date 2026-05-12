/-
# R4Carry -- R4-squared saved-current carry for the meta-interpreter

The saved-current problem in F.7c is not a flat 256-case phenomenon.  The
canonical self-similarity theorem gives

  R8 ~= R4 x R4

so the current cell can be carried as two R4 surfaces while `META.cur` is
temporarily reused for fetch and opcode dispatch.

This module is intentionally pure: it fixes the carrier, round-trips, and
finite enumeration.  It does not depend on fetch, dispatch, or block code.
-/
import SSBX.Foundation.Squaring.SelfSimilarity

namespace SSBX.Foundation.Wen.MetaInterp.R4Carry

open SSBX.Foundation.Bagua.BenZheng
open SSBX.Foundation.Squaring.SelfSimilarity

/-! ## R4-squared carry -/

/-- A saved-current carry is the self-similar R8 decomposition `R4 x R4`. -/
abbrev SavedCurrentCarry : Type :=
  SSBX.Foundation.Hierarchy.LiftProject.R4 ×
    SSBX.Foundation.Hierarchy.LiftProject.R4

/-- Read an R8 cell as its canonical R4-squared carry. -/
def carryOfCell : SSBX.Foundation.Bagua.R8.R8 → SavedCurrentCarry :=
  r8_to_r4_squared

/-- Reconstruct an R8 cell from its canonical R4-squared carry. -/
def cellOfCarry : SavedCurrentCarry → SSBX.Foundation.Bagua.R8.R8 :=
  r4_squared_to_r8

theorem cellOfCarry_carryOfCell (c : SSBX.Foundation.Bagua.R8.R8) :
    cellOfCarry (carryOfCell c) = c :=
  r8_eq_r4_squared.left_inv c

theorem carryOfCell_cellOfCarry (carry : SavedCurrentCarry) :
    carryOfCell (cellOfCarry carry) = carry :=
  r8_eq_r4_squared.right_inv carry

/-- All R4-squared saved-current carries, generated structurally from Mian. -/
def savedCurrentCarries : List SavedCurrentCarry :=
  Mian.all.flatMap (fun inner => Mian.all.map (fun outer => (inner, outer)))

theorem savedCurrentCarries_length :
    savedCurrentCarries.length = 256 := by
  native_decide

/-- Public summary: R8 current cells and R4-squared carries round-trip exactly. -/
theorem r4_carry_summary :
    (∀ c : SSBX.Foundation.Bagua.R8.R8, cellOfCarry (carryOfCell c) = c)
    ∧ (∀ carry : SavedCurrentCarry, carryOfCell (cellOfCarry carry) = carry)
    ∧ savedCurrentCarries.length = 256 := by
  exact ⟨cellOfCarry_carryOfCell, carryOfCell_cellOfCarry, savedCurrentCarries_length⟩

end SSBX.Foundation.Wen.MetaInterp.R4Carry
