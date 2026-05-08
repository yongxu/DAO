/-
# ZhengBoundary — 证之边界 / 命题系统推导证书

Companion: `义理/边界/证的边界 · 命题系统证书.md`

This file refines `KeBoundary.ProofRegion` with a thin proof-interface
skeleton. It does not develop proof theory, model theory, independence,
or incompleteness results.
-/
import SSBX.Foundation.Modern.KeBoundary

namespace SSBX.Foundation.Modern.ZhengBoundary

open SSBX.Foundation.Modern.KnowableBoundary
open SSBX.Foundation.Modern.KeBoundary

/-! ## § 1 Axes of zheng-boundaries -/

/-- “证”的五条流程轴：命题、系统、推导、检查器、证书。 -/
inductive ZhengAxis : Type
  | proposition
  | system
  | derivation
  | checker
  | certificate
  deriving Repr, DecidableEq

/-- 五条“证”轴两两不同的核心见证。 -/
theorem zheng_axes_pairwise_distinct :
    ZhengAxis.proposition ≠ ZhengAxis.system
    ∧ ZhengAxis.proposition ≠ ZhengAxis.derivation
    ∧ ZhengAxis.proposition ≠ ZhengAxis.checker
    ∧ ZhengAxis.proposition ≠ ZhengAxis.certificate
    ∧ ZhengAxis.system ≠ ZhengAxis.derivation
    ∧ ZhengAxis.system ≠ ZhengAxis.checker
    ∧ ZhengAxis.system ≠ ZhengAxis.certificate
    ∧ ZhengAxis.derivation ≠ ZhengAxis.checker
    ∧ ZhengAxis.derivation ≠ ZhengAxis.certificate
    ∧ ZhengAxis.checker ≠ ZhengAxis.certificate := by
  simp

/-! ## § 2 Complete proof skeleton -/

structure ZhengSkeleton where
  proposition : BoundarySide
  system : BoundarySide
  derivation : BoundarySide
  checker : BoundarySide
  certificate : BoundarySide
  deriving Repr

/-- 完整证：有命题、有系统、有推导、有检查器、有证书。 -/
def CompleteZheng (z : ZhengSkeleton) : Prop :=
  z.proposition = .inside
    ∧ z.system = .inside
    ∧ z.derivation = .inside
    ∧ z.checker = .inside
    ∧ z.certificate = .inside

/-- 从“证”流程映射回 `KeBoundary` 的 proof interface。 -/
def zhengAsProofRegion (z : ZhengSkeleton) : ProofRegion :=
  match z.proposition, z.system, z.derivation, z.checker, z.certificate with
  | .inside, .inside, .inside, .inside, .inside => .provable
  | _, _, _, _, _ => .unprovable

/-- 完整证流程必落在可证内侧。 -/
theorem complete_zheng_maps_to_provable (z : ZhengSkeleton) :
    CompleteZheng z → Provable (zhengAsProofRegion z) := by
  intro h
  cases z with
  | mk p s d c cert =>
      rcases h with ⟨hp, hs, hd, hc, hcert⟩
      simp at hp
      simp at hs
      simp at hd
      simp at hc
      simp at hcert
      subst p
      subst s
      subst d
      subst c
      subst cert
      rfl

/-- 任一缺失轴都会把本 skeleton 落到不可证一侧。 -/
theorem incomplete_zheng_maps_to_unprovable
    (z : ZhengSkeleton)
    (h : ¬ CompleteZheng z) :
    zhengAsProofRegion z = .unprovable := by
  cases z with
  | mk p s d c cert =>
      cases p <;> cases s <;> cases d <;> cases c <;> cases cert <;>
        simp [zhengAsProofRegion, CompleteZheng] at h ⊢

/-- 证的边界仍可被语言描述；这不是完整证明论，只是可说 skeleton。 -/
theorem zheng_boundary_is_sayable_skeleton (z : ZhengSkeleton) :
    Sayable (proofRegionAsKnowable (zhengAsProofRegion z)) :=
  proof_boundary_is_sayable_skeleton _

/-! ## § 3 Public summary -/

theorem zheng_boundary_summary :
    (ZhengAxis.proposition ≠ ZhengAxis.system
      ∧ ZhengAxis.proposition ≠ ZhengAxis.derivation
      ∧ ZhengAxis.proposition ≠ ZhengAxis.checker
      ∧ ZhengAxis.proposition ≠ ZhengAxis.certificate
      ∧ ZhengAxis.system ≠ ZhengAxis.derivation
      ∧ ZhengAxis.system ≠ ZhengAxis.checker
      ∧ ZhengAxis.system ≠ ZhengAxis.certificate
      ∧ ZhengAxis.derivation ≠ ZhengAxis.checker
      ∧ ZhengAxis.derivation ≠ ZhengAxis.certificate
      ∧ ZhengAxis.checker ≠ ZhengAxis.certificate)
    ∧ (∀ z : ZhengSkeleton, CompleteZheng z → Provable (zhengAsProofRegion z))
    ∧ (∀ z : ZhengSkeleton, ¬ CompleteZheng z →
        zhengAsProofRegion z = .unprovable)
    ∧ (∀ z : ZhengSkeleton, Sayable (proofRegionAsKnowable (zhengAsProofRegion z))) :=
  ⟨zheng_axes_pairwise_distinct,
   complete_zheng_maps_to_provable,
   incomplete_zheng_maps_to_unprovable,
   zheng_boundary_is_sayable_skeleton⟩

end SSBX.Foundation.Modern.ZhengBoundary
