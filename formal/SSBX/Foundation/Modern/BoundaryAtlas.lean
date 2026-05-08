/-
# BoundaryAtlas — 知 / 感 / 行 / 证 / 名 / 量 / 测 / 推

Companion: `义理/边界/边界总图谱 · 知感行证名量测推.md`
-/
import SSBX.Foundation.Modern.ZhiBoundary
import SSBX.Foundation.Modern.GanBoundary
import SSBX.Foundation.Modern.XingBoundary
import SSBX.Foundation.Modern.ZhengBoundary
import SSBX.Foundation.Modern.MingBoundary
import SSBX.Foundation.Modern.LiangBoundary
import SSBX.Foundation.Modern.CeBoundary
import SSBX.Foundation.Modern.TuiBoundary

namespace SSBX.Foundation.Modern.BoundaryAtlas

/-- 当前这一层已经落成的八个边界。 -/
inductive BoundaryLayer : Type
  | zhi
  | gan
  | xing
  | zheng
  | ming
  | liang
  | ce
  | tui
  deriving Repr, DecidableEq

/-- 八界两两不同。 -/
theorem boundary_layers_pairwise_distinct :
    BoundaryLayer.zhi ≠ BoundaryLayer.gan
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.xing
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.zheng
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.xing
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.zheng
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.zheng
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.ming ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.ming ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.ming ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.liang ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.liang ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.ce ≠ BoundaryLayer.tui := by
  simp

/-- 链式读法：知、感、行、证、名、量、测、推不混同。 -/
theorem boundary_layer_chain_distinct :
    BoundaryLayer.zhi ≠ BoundaryLayer.gan
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.xing
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.zheng
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.ming ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.liang ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.ce ≠ BoundaryLayer.tui := by
  simp

/-- 公开摘要：这一层八个边界不互相塌缩。 -/
theorem boundary_atlas_summary :
    BoundaryLayer.zhi ≠ BoundaryLayer.gan
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.xing
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.zheng
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.zhi ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.xing
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.zheng
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.gan ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.zheng
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.xing ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.ming
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.zheng ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.ming ≠ BoundaryLayer.liang
    ∧ BoundaryLayer.ming ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.ming ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.liang ≠ BoundaryLayer.ce
    ∧ BoundaryLayer.liang ≠ BoundaryLayer.tui
    ∧ BoundaryLayer.ce ≠ BoundaryLayer.tui :=
  boundary_layers_pairwise_distinct

end SSBX.Foundation.Modern.BoundaryAtlas
