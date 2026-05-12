/-
# ClassicalTextRHierarchyBridge — classical text surface and R-hierarchy typed bridge

This file records only the direct bridge from the classical text surface aliases in
`WenyanText` to the already-defined `YiInstr` interpreter and R8 operators.
It deliberately does not claim that the full `MetaInterp.Universal` theorem is
complete here.
-/
import SSBX.Foundation.Wen.WenyanText

namespace SSBX.Foundation.Wen.ClassicalTextRHierarchyBridge

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanText

/-! ## § 1 Classical text instruction aliases are YiInstr constructors -/

/-- The classical text surface instruction names are definitional aliases of `YiInstr`. -/
theorem classical_text_instruction_aliases_are_yiinstr :
    «不动» = YiInstr.nop
    ∧ «互» = YiInstr.interlace
    ∧ «错» = YiInstr.complement
    ∧ «综» = YiInstr.reverse
    ∧ «推» = YiInstr.push
    ∧ «取» = YiInstr.pop
    ∧ «终» = YiInstr.halt
    ∧ (∀ s : Shi, «设时» s = YiInstr.setShi s)
    ∧ (∀ i : Fin 6, «翻爻» i = YiInstr.flipYao i)
    ∧ (∀ i j : Fin 6, ∀ n : Nat, «比爻» i j n = YiInstr.branchYaoEq i j n)
    ∧ (∀ s : Shi, ∀ n : Nat, «比时» s n = YiInstr.branchShiEq s n)
    ∧ (∀ n : Nat, «跳» n = YiInstr.jump n) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    (fun _ => rfl), (fun _ => rfl), (fun _ _ _ => rfl),
    (fun _ _ => rfl), (fun _ => rfl)⟩

/-! ## § 2 Surface operators match R8 operators -/

/-- Executing classical text `互/错/综` changes the current R8 cell exactly as R8 says. -/
theorem classical_text_surface_ops_match_r8_ops (s : YiState) :
    (YiState.execute «互» s).cur = R8.hexHu s.cur
    ∧ (YiState.execute «错» s).cur = R8.hexCuo s.cur
    ∧ (YiState.execute «综» s).cur = R8.hexZong s.cur
    ∧ (∀ sh : Shi, (YiState.execute («设时» sh) s).cur = (s.cur.1, sh)) := by
  exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-! ## § 3 Way judge bridge summary -/

/-- The classical text Way-judge program is the same program as the R8 Way judge. -/
theorem classical_text_way_judge_program_alias :
    «道判之程» = daoJudgeProg := rfl

/-- Applying the classical text Way-judge program computes the same verdict as `daoJudge`. -/
theorem classical_text_way_judge_execution_alias (h : Hexagram) :
    «施» «道判之程» h = daoJudge h := rfl

/-- Doctrine-level summary: classical text syntax, YiInstr execution, and R8 Way judgment align. -/
theorem classical_text_way_judge_rhierarchy_bridge_summary :
    («道判之程» = daoJudgeProg)
    ∧ (∀ h : Hexagram, «施» «道判之程» h = daoJudge h)
    ∧ (∀ h : Hexagram, «施» «道判之程» h =
        (if h.isTian then Shi.ji else Shi.wei)) := by
  exact ⟨rfl, (fun _ => rfl), fun h => by
    show daoJudge h = _
    exact daoJudge_correct h⟩

/-! ## § 4 Scope boundary -/

/-- Boundary marker: this bridge proves direct alias/execution facts, not full universality. -/
theorem classical_text_rhierarchy_scope_boundary :
    (∀ s : YiState,
      (YiState.execute «互» s).cur = R8.hexHu s.cur
      ∧ (YiState.execute «错» s).cur = R8.hexCuo s.cur
      ∧ (YiState.execute «综» s).cur = R8.hexZong s.cur)
    ∧ (∀ h : Hexagram, «施» «道判之程» h = daoJudge h) := by
  exact ⟨(fun _ => ⟨rfl, rfl, rfl⟩), fun _ => rfl⟩

end SSBX.Foundation.Wen.ClassicalTextRHierarchyBridge
