/-
# R4Carry -- R4-squared saved-current carry for the meta-interpreter

The saved-current problem in F.7c is not a flat 256-case phenomenon.  The
canonical self-similarity theorem gives

  R8 ~= R4 x R4

so the current cell can be carried as two R4 surfaces while `META.cur` is
temporarily reused for fetch and opcode dispatch.

This module is intentionally pure: it fixes the carrier, round-trips, and
finite enumeration.  It does not depend on fetch, dispatch, or block code.

## History

Originally this file imported `Foundation/Squaring/SelfSimilarity.lean`
for the Yi-flavoured `R8 ≃ R4 × R4` bijection (`r8_to_r4_squared`,
`r4_squared_to_r8`).  The v0.6 R-Family restructure retired the
`Foundation/Squaring/` directory; the language-independent squaring step
`R 8 ≃ R 4 × R 4` now lives in `Foundation/R/Squaring.lean`
(`R8_eq_R4_sq`).  This file, however, operates over the **Yi-flavoured**
Bagua `R8` (`Hexagram × Shi`) and `Mian`-shaped `R4`, so we inline the
Yi-specific bijection locally rather than reaching for the parametric
`R 8 = Fin 8 → Bool` form.  (A future Atlas/Yi migration may rebase this
on the parametric carrier; that is out of scope for the P4.4 cleanup.)
-/
import Mathlib.Logic.Equiv.Basic
import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.BenZheng
import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Wen.MetaInterp.R4Carry

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BenZheng

/-! ## Local re-statement of the `R8 ≃ R4 × R4` Yi-flavoured bijection

Adapted (inlined) from the retired
`Foundation/Squaring/SelfSimilarity.lean` so this file no longer depends
on the `Squaring/` subtree. -/

private def benToSiXiang : Ben → SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang
  | .thing    => ⟨.yang, .yang⟩
  | .motion   => ⟨.yang, .yin⟩
  | .interval => ⟨.yin,  .yang⟩
  | .event    => ⟨.yin,  .yin⟩

private def siXiangToBen : SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang → Ben
  | ⟨.yang, .yang⟩ => .thing
  | ⟨.yang, .yin⟩  => .motion
  | ⟨.yin,  .yang⟩ => .interval
  | ⟨.yin,  .yin⟩  => .event

private def zhengToSiXiang : Zheng → SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang
  | .trace    => ⟨.yang, .yang⟩
  | .momentum => ⟨.yang, .yin⟩
  | .pivot    => ⟨.yin,  .yang⟩
  | .occasion => ⟨.yin,  .yin⟩

private def siXiangToZheng : SSBX.Foundation.Bagua.BaguaAlgebra.SiXiang → Zheng
  | ⟨.yang, .yang⟩ => .trace
  | ⟨.yang, .yin⟩  => .momentum
  | ⟨.yin,  .yang⟩ => .pivot
  | ⟨.yin,  .yin⟩  => .occasion

private def r8_to_8yao
    (c : SSBX.Foundation.Bagua.R8.R8) :
    Yao × Yao × Yao × Yao × Yao × Yao × Yao × Yao :=
  let ⟨h, s⟩ := c
  let y7 : Yao := if s.1 then .yin else .yang
  let y8 : Yao := if s.2 then .yin else .yang
  (h.y1, h.y2, h.y3, h.y4, h.y5, h.y6, y7, y8)

private def yao8_to_r8 :
    Yao × Yao × Yao × Yao × Yao × Yao × Yao × Yao →
      SSBX.Foundation.Bagua.R8.R8 :=
  fun ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ =>
    let h : SSBX.Foundation.Yi.Yi.Hexagram := ⟨y1, y2, y3, y4, y5, y6⟩
    let b1 : Bool := match y7 with | .yang => false | .yin => true
    let b2 : Bool := match y8 with | .yang => false | .yin => true
    (h, (b1, b2))

private def r8_to_r4_squared
    (c : SSBX.Foundation.Bagua.R8.R8) :
    SSBX.Foundation.Hierarchy.LiftProject.R4 ×
      SSBX.Foundation.Hierarchy.LiftProject.R4 :=
  let ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := r8_to_8yao c
  let inner : SSBX.Foundation.Hierarchy.LiftProject.R4 :=
    (siXiangToBen ⟨y1, y2⟩, siXiangToZheng ⟨y3, y4⟩)
  let outer : SSBX.Foundation.Hierarchy.LiftProject.R4 :=
    (siXiangToBen ⟨y5, y6⟩, siXiangToZheng ⟨y7, y8⟩)
  (inner, outer)

private def r4_squared_to_r8 :
    SSBX.Foundation.Hierarchy.LiftProject.R4 ×
      SSBX.Foundation.Hierarchy.LiftProject.R4 →
        SSBX.Foundation.Bagua.R8.R8 :=
  fun ⟨inner, outer⟩ =>
    let ⟨bi, zi⟩ := inner
    let ⟨bo, zo⟩ := outer
    let ⟨y1, y2⟩ := benToSiXiang bi
    let ⟨y3, y4⟩ := zhengToSiXiang zi
    let ⟨y5, y6⟩ := benToSiXiang bo
    let ⟨y7, y8⟩ := zhengToSiXiang zo
    yao8_to_r8 ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩

private abbrev R8Local : Type := SSBX.Foundation.Bagua.R8.R8
private abbrev R4Local : Type := SSBX.Foundation.Hierarchy.LiftProject.R4

private def r8_eq_r4_squared : R8Local ≃ (R4Local × R4Local) where
  toFun := r8_to_r4_squared
  invFun := r4_squared_to_r8
  left_inv := by
    rintro ⟨⟨y1, y2, y3, y4, y5, y6⟩, ⟨b1, b2⟩⟩
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;>
    cases y5 <;> cases y6 <;> cases b1 <;> cases b2 <;> rfl
  right_inv := by
    rintro ⟨⟨bi, zi⟩, ⟨bo, zo⟩⟩
    cases bi <;> cases zi <;> cases bo <;> cases zo <;> rfl

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
