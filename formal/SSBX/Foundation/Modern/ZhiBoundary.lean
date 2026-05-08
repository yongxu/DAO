/-
# ZhiBoundary — 知之边界 / 明辨述贯存

Companion: `义理/边界/知的边界 · 明辨述.md`

This file keeps a thin typed skeleton:

1. "知" is not the whole of "可知"; it is the process that reaches
   describable Li through access, distinction, articulation, coherence,
   and retention;
2. a complete knowing skeleton maps into `KnowableBoundary.Knowable`;
3. an incomplete skeleton maps outside the describable-Li interface.
-/
import SSBX.Foundation.Modern.KeBoundary

namespace SSBX.Foundation.Modern.ZhiBoundary

open SSBX.Foundation.Modern.KnowableBoundary
open SSBX.Foundation.Modern.KeBoundary

/-! ## § 1 Axes of zhi-boundaries -/

/-- "知"的五条流程轴：明、辨、述、贯、存。 -/
inductive ZhiAxis : Type
  | access
  | distinction
  | articulation
  | coherence
  | retention
  deriving Repr, DecidableEq

/-- 五条“知”轴两两不同的核心见证。 -/
theorem zhi_axes_pairwise_distinct :
    ZhiAxis.access ≠ ZhiAxis.distinction
    ∧ ZhiAxis.access ≠ ZhiAxis.articulation
    ∧ ZhiAxis.access ≠ ZhiAxis.coherence
    ∧ ZhiAxis.access ≠ ZhiAxis.retention
    ∧ ZhiAxis.distinction ≠ ZhiAxis.articulation
    ∧ ZhiAxis.distinction ≠ ZhiAxis.coherence
    ∧ ZhiAxis.distinction ≠ ZhiAxis.retention
    ∧ ZhiAxis.articulation ≠ ZhiAxis.coherence
    ∧ ZhiAxis.articulation ≠ ZhiAxis.retention
    ∧ ZhiAxis.coherence ≠ ZhiAxis.retention := by
  simp

/-! ## § 2 Complete knowing skeleton -/

/-- 一个最薄的知流程骨架。 -/
structure ZhiSkeleton where
  access : BoundarySide
  distinction : BoundarySide
  articulation : BoundarySide
  coherence : BoundarySide
  retention : BoundarySide
  deriving Repr

/-- 完整知：可入、可辨、可述、可贯、可存。 -/
def CompleteZhi (z : ZhiSkeleton) : Prop :=
  z.access = .inside
    ∧ z.distinction = .inside
    ∧ z.articulation = .inside
    ∧ z.coherence = .inside
    ∧ z.retention = .inside

/-- 从“知”流程映射回可描述之理边界。 -/
def zhiAsKnowable (z : ZhiSkeleton) : KnowableRegion :=
  match z.access, z.distinction, z.articulation, z.coherence, z.retention with
  | .inside, .inside, .inside, .inside, .inside => .withinDescribableLi
  | _, _, _, _, _ => .beyondDescribableLi

/-- 完整知流程必落在可知内侧。 -/
theorem complete_zhi_maps_to_knowable (z : ZhiSkeleton) :
    CompleteZhi z → Knowable (zhiAsKnowable z) := by
  intro h
  cases z with
  | mk a d s c r =>
      rcases h with ⟨ha, hd, hs, hc, hr⟩
      simp at ha
      simp at hd
      simp at hs
      simp at hc
      simp at hr
      subst a
      subst d
      subst s
      subst c
      subst r
      rfl

/-- 任一缺失轴都会把本 skeleton 落到可描述之理外侧。 -/
theorem incomplete_zhi_maps_beyond_describable_li
    (z : ZhiSkeleton)
    (h : ¬ CompleteZhi z) :
    zhiAsKnowable z = .beyondDescribableLi := by
  cases z with
  | mk a d s c r =>
      cases a <;> cases d <;> cases s <;> cases c <;> cases r <;>
        simp [zhiAsKnowable, CompleteZhi] at h ⊢

/-! ## § 3 Public summary -/

/-- 公开摘要：
    (1) 五条“知”轴两两不同；
    (2) 完整知流程落入可知内侧；
    (3) 缺失轴的流程落入可描述之理外侧。 -/
theorem zhi_boundary_summary :
    (ZhiAxis.access ≠ ZhiAxis.distinction
      ∧ ZhiAxis.access ≠ ZhiAxis.articulation
      ∧ ZhiAxis.access ≠ ZhiAxis.coherence
      ∧ ZhiAxis.access ≠ ZhiAxis.retention
      ∧ ZhiAxis.distinction ≠ ZhiAxis.articulation
      ∧ ZhiAxis.distinction ≠ ZhiAxis.coherence
      ∧ ZhiAxis.distinction ≠ ZhiAxis.retention
      ∧ ZhiAxis.articulation ≠ ZhiAxis.coherence
      ∧ ZhiAxis.articulation ≠ ZhiAxis.retention
      ∧ ZhiAxis.coherence ≠ ZhiAxis.retention)
    ∧ (∀ z : ZhiSkeleton, CompleteZhi z → Knowable (zhiAsKnowable z))
    ∧ (∀ z : ZhiSkeleton, ¬ CompleteZhi z →
        zhiAsKnowable z = .beyondDescribableLi) :=
  ⟨zhi_axes_pairwise_distinct,
   complete_zhi_maps_to_knowable,
   incomplete_zhi_maps_beyond_describable_li⟩

end SSBX.Foundation.Modern.ZhiBoundary
