/-
# XingBoundary — 行之边界 / 能境作效

Companion: `义理/边界/行的边界 · 能境作效.md`

This file refines `KeBoundary.ActionabilityRegion` with a thin process
skeleton for action: agent, capacity, context, operation, and effect.
-/
import SSBX.Foundation.Modern.KeBoundary

namespace SSBX.Foundation.Modern.XingBoundary

open SSBX.Foundation.Modern.KeBoundary

/-! ## § 1 Axes of xing-boundaries -/

/-- “行”的五条流程轴：主体、能力、境况、操作、效果。 -/
inductive XingAxis : Type
  | agent
  | capacity
  | context
  | operation
  | effect
  deriving Repr, DecidableEq

/-- 五条“行”轴两两不同的核心见证。 -/
theorem xing_axes_pairwise_distinct :
    XingAxis.agent ≠ XingAxis.capacity
    ∧ XingAxis.agent ≠ XingAxis.context
    ∧ XingAxis.agent ≠ XingAxis.operation
    ∧ XingAxis.agent ≠ XingAxis.effect
    ∧ XingAxis.capacity ≠ XingAxis.context
    ∧ XingAxis.capacity ≠ XingAxis.operation
    ∧ XingAxis.capacity ≠ XingAxis.effect
    ∧ XingAxis.context ≠ XingAxis.operation
    ∧ XingAxis.context ≠ XingAxis.effect
    ∧ XingAxis.operation ≠ XingAxis.effect := by
  simp

/-! ## § 2 Complete action skeleton -/

structure XingSkeleton where
  agent : BoundarySide
  capacity : BoundarySide
  context : BoundarySide
  operation : BoundarySide
  effect : BoundarySide
  deriving Repr

/-- 完整行：有主体、有能力、有境况、有操作、有可验效果。 -/
def CompleteXing (x : XingSkeleton) : Prop :=
  x.agent = .inside
    ∧ x.capacity = .inside
    ∧ x.context = .inside
    ∧ x.operation = .inside
    ∧ x.effect = .inside

/-- 从“行”流程映射回 `KeBoundary` 的可行边界。 -/
def xingAsActionability (x : XingSkeleton) : ActionabilityRegion :=
  match x.agent, x.capacity, x.context, x.operation, x.effect with
  | .inside, .inside, .inside, .inside, .inside => .actionable
  | _, _, _, _, _ => .unactionable

/-- 完整行流程必落在可行内侧。 -/
theorem complete_xing_maps_to_actionable (x : XingSkeleton) :
    CompleteXing x → Actionable (xingAsActionability x) := by
  intro h
  cases x with
  | mk a c k o e =>
      rcases h with ⟨ha, hc, hk, ho, he⟩
      simp at ha
      simp at hc
      simp at hk
      simp at ho
      simp at he
      subst a
      subst c
      subst k
      subst o
      subst e
      rfl

/-- 任一缺失轴都会把本 skeleton 落到不可行一侧。 -/
theorem incomplete_xing_maps_to_unactionable
    (x : XingSkeleton)
    (h : ¬ CompleteXing x) :
    xingAsActionability x = .unactionable := by
  cases x with
  | mk a c k o e =>
      cases a <;> cases c <;> cases k <;> cases o <;> cases e <;>
        simp [xingAsActionability, CompleteXing] at h ⊢

/-! ## § 3 Public summary -/

theorem xing_boundary_summary :
    (XingAxis.agent ≠ XingAxis.capacity
      ∧ XingAxis.agent ≠ XingAxis.context
      ∧ XingAxis.agent ≠ XingAxis.operation
      ∧ XingAxis.agent ≠ XingAxis.effect
      ∧ XingAxis.capacity ≠ XingAxis.context
      ∧ XingAxis.capacity ≠ XingAxis.operation
      ∧ XingAxis.capacity ≠ XingAxis.effect
      ∧ XingAxis.context ≠ XingAxis.operation
      ∧ XingAxis.context ≠ XingAxis.effect
      ∧ XingAxis.operation ≠ XingAxis.effect)
    ∧ (∀ x : XingSkeleton, CompleteXing x → Actionable (xingAsActionability x))
    ∧ (∀ x : XingSkeleton, ¬ CompleteXing x →
        xingAsActionability x = .unactionable) :=
  ⟨xing_axes_pairwise_distinct,
   complete_xing_maps_to_actionable,
   incomplete_xing_maps_to_unactionable⟩

end SSBX.Foundation.Modern.XingBoundary
