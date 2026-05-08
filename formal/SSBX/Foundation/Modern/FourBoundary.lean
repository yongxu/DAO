/-
# FourBoundary — 测 / 量 / 推 / 感 四界不混同

Companion: `义理/边界/四界不混同 · 测量推感.md`
-/
import SSBX.Foundation.Modern.LiangBoundary
import SSBX.Foundation.Modern.CeBoundary
import SSBX.Foundation.Modern.TuiBoundary
import SSBX.Foundation.Modern.GanBoundary

namespace SSBX.Foundation.Modern.FourBoundary

/-- 本轮完成的四个边界层。 -/
inductive BoundaryKind : Type
  | liang
  | ce
  | tui
  | gan
  deriving Repr, DecidableEq

/-- 测、量、推、感四界两两不同。 -/
theorem four_boundaries_pairwise_distinct :
    BoundaryKind.ce ≠ BoundaryKind.liang
    ∧ BoundaryKind.ce ≠ BoundaryKind.tui
    ∧ BoundaryKind.ce ≠ BoundaryKind.gan
    ∧ BoundaryKind.liang ≠ BoundaryKind.tui
    ∧ BoundaryKind.liang ≠ BoundaryKind.gan
    ∧ BoundaryKind.tui ≠ BoundaryKind.gan := by
  simp

/-- “测 ≠ 量 ≠ 推 ≠ 感”的链式读法。 -/
theorem ce_liang_tui_gan_chain_distinct :
    BoundaryKind.ce ≠ BoundaryKind.liang
    ∧ BoundaryKind.liang ≠ BoundaryKind.tui
    ∧ BoundaryKind.tui ≠ BoundaryKind.gan := by
  exact ⟨four_boundaries_pairwise_distinct.1,
    four_boundaries_pairwise_distinct.2.2.2.1,
    four_boundaries_pairwise_distinct.2.2.2.2.2⟩

theorem four_boundary_summary :
    BoundaryKind.ce ≠ BoundaryKind.liang
    ∧ BoundaryKind.ce ≠ BoundaryKind.tui
    ∧ BoundaryKind.ce ≠ BoundaryKind.gan
    ∧ BoundaryKind.liang ≠ BoundaryKind.tui
    ∧ BoundaryKind.liang ≠ BoundaryKind.gan
    ∧ BoundaryKind.tui ≠ BoundaryKind.gan :=
  four_boundaries_pairwise_distinct

end SSBX.Foundation.Modern.FourBoundary
