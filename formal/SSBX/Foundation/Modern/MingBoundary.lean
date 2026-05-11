/-
# MingBoundary — 名之边界 / 指称符号约定域消歧

Companion: `义理/边界/名的边界 · 指称定名.md`

This file handles the nameable / unnameable deferred boundary from
`KnowableBoundary`. It does not claim that naming is the same as knowing:
names can point, classify, or disambiguate without exhausting the thing.
-/
import SSBX.Foundation.Modern.KeBoundary

namespace SSBX.Foundation.Modern.MingBoundary

open SSBX.Foundation.Modern.KnowableBoundary
open SSBX.Foundation.Modern.KeBoundary

/-! ## § 1 Axes of ming-boundaries -/

/-- “名”的五条流程轴：所指、符号、约定、域、消歧。 -/
inductive MingAxis : Type
  | referent
  | sign
  | convention
  | scope
  | disambiguation
  deriving Repr, DecidableEq

/-- 五条“名”轴两两不同的核心见证。 -/
theorem ming_axes_pairwise_distinct :
    MingAxis.referent ≠ MingAxis.sign
    ∧ MingAxis.referent ≠ MingAxis.convention
    ∧ MingAxis.referent ≠ MingAxis.scope
    ∧ MingAxis.referent ≠ MingAxis.disambiguation
    ∧ MingAxis.sign ≠ MingAxis.convention
    ∧ MingAxis.sign ≠ MingAxis.scope
    ∧ MingAxis.sign ≠ MingAxis.disambiguation
    ∧ MingAxis.convention ≠ MingAxis.scope
    ∧ MingAxis.convention ≠ MingAxis.disambiguation
    ∧ MingAxis.scope ≠ MingAxis.disambiguation := by
  simp

/-! ## § 2 Nameable / unnameable -/

/-- 名边界的两侧：可名 / 不可名。 -/
inductive NamingRegion : Type
  | nameable
  | unnameable
  deriving Repr, DecidableEq

def Nameable (r : NamingRegion) : Prop :=
  r = .nameable

def Unnameable (r : NamingRegion) : Prop :=
  r = .unnameable

theorem naming_region_exhaustive (r : NamingRegion) :
    Nameable r ∨ Unnameable r := by
  cases r <;> simp [Nameable, Unnameable]

theorem nameable_not_unnameable (r : NamingRegion) :
    Nameable r → ¬ Unnameable r := by
  intro hn interlace
  unfold Nameable at hn
  unfold Unnameable at interlace
  rw [hn] at interlace
  cases interlace

theorem unnameable_not_nameable (r : NamingRegion) :
    Unnameable r → ¬ Nameable r := by
  intro interlace hn
  exact nameable_not_unnameable r hn interlace

theorem naming_boundary_complete :
    (∀ r : NamingRegion, Nameable r ∨ Unnameable r)
    ∧ (∀ r : NamingRegion, Nameable r → ¬ Unnameable r)
    ∧ (∀ r : NamingRegion, Unnameable r → ¬ Nameable r) :=
  ⟨naming_region_exhaustive,
   nameable_not_unnameable,
   unnameable_not_nameable⟩

/-! ## § 3 Complete naming skeleton -/

structure MingSkeleton where
  referent : BoundarySide
  sign : BoundarySide
  convention : BoundarySide
  scope : BoundarySide
  disambiguation : BoundarySide
  deriving Repr

/-- 完整名：有所指、有符号、有约定、有论域、有消歧。 -/
def CompleteMing (m : MingSkeleton) : Prop :=
  m.referent = .inside
    ∧ m.sign = .inside
    ∧ m.convention = .inside
    ∧ m.scope = .inside
    ∧ m.disambiguation = .inside

/-- 从“名”流程映射到可名 / 不可名边界。 -/
def mingAsNamingRegion (m : MingSkeleton) : NamingRegion :=
  match m.referent, m.sign, m.convention, m.scope, m.disambiguation with
  | .inside, .inside, .inside, .inside, .inside => .nameable
  | _, _, _, _, _ => .unnameable

/-- 完整名流程必落在可名内侧。 -/
theorem complete_ming_maps_to_nameable (m : MingSkeleton) :
    CompleteMing m → Nameable (mingAsNamingRegion m) := by
  intro h
  cases m with
  | mk r s c scope d =>
      rcases h with ⟨hr, hs, hc, hscope, hd⟩
      simp at hr
      simp at hs
      simp at hc
      simp at hscope
      simp at hd
      subst r
      subst s
      subst c
      subst scope
      subst d
      rfl

/-- 任一缺失轴都会把本 skeleton 落到不可名一侧。 -/
theorem incomplete_ming_maps_to_unnameable
    (m : MingSkeleton)
    (h : ¬ CompleteMing m) :
    mingAsNamingRegion m = .unnameable := by
  cases m with
  | mk r s c scope d =>
      cases r <;> cases s <;> cases c <;> cases scope <;> cases d <;>
        simp [mingAsNamingRegion, CompleteMing] at h ⊢

/-! ## § 4 Handoff from KnowableBoundary -/

/-- `KnowableBoundary` deferred 的可名 / 不可名由本文件承接。 -/
def handledInMingBoundary : DeferredKeBoundary → Bool
  | .nameable
  | .unnameable => true
  | .feelable
  | .unfeelable
  | .actionable
  | .unactionable
  | .provable
  | .unprovable
  | .measurable
  | .unmeasurable => false

/-- “名”边界只承接 deferred 的可名 / 不可名。 -/
theorem handled_in_ming_iff_nameable (b : DeferredKeBoundary) :
    handledInMingBoundary b = true ↔ b = .nameable ∨ b = .unnameable := by
  cases b <;> simp [handledInMingBoundary]

/-- 可名 / 不可名：Knowable 不处理，Ke 不处理，Ming 承接。 -/
theorem name_deferred_boundaries_handled_in_ming :
    handledHere .nameable = false ∧ handledInKeBoundary .nameable = false
    ∧ handledInMingBoundary .nameable = true
    ∧ handledHere .unnameable = false ∧ handledInKeBoundary .unnameable = false
    ∧ handledInMingBoundary .unnameable = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## § 5 Public summary -/

theorem ming_boundary_summary :
    (MingAxis.referent ≠ MingAxis.sign
      ∧ MingAxis.referent ≠ MingAxis.convention
      ∧ MingAxis.referent ≠ MingAxis.scope
      ∧ MingAxis.referent ≠ MingAxis.disambiguation
      ∧ MingAxis.sign ≠ MingAxis.convention
      ∧ MingAxis.sign ≠ MingAxis.scope
      ∧ MingAxis.sign ≠ MingAxis.disambiguation
      ∧ MingAxis.convention ≠ MingAxis.scope
      ∧ MingAxis.convention ≠ MingAxis.disambiguation
      ∧ MingAxis.scope ≠ MingAxis.disambiguation)
    ∧ (∀ r : NamingRegion, Nameable r ∨ Unnameable r)
    ∧ (∀ r : NamingRegion, Nameable r → ¬ Unnameable r)
    ∧ (∀ r : NamingRegion, Unnameable r → ¬ Nameable r)
    ∧ (∀ m : MingSkeleton, CompleteMing m → Nameable (mingAsNamingRegion m))
    ∧ (∀ m : MingSkeleton, ¬ CompleteMing m →
        mingAsNamingRegion m = .unnameable)
    ∧ (∀ b : DeferredKeBoundary,
        handledInMingBoundary b = true ↔ b = .nameable ∨ b = .unnameable)
    ∧ (handledHere .nameable = false ∧ handledInKeBoundary .nameable = false
      ∧ handledInMingBoundary .nameable = true
      ∧ handledHere .unnameable = false ∧ handledInKeBoundary .unnameable = false
      ∧ handledInMingBoundary .unnameable = true) :=
  ⟨ming_axes_pairwise_distinct,
   naming_region_exhaustive,
   nameable_not_unnameable,
   unnameable_not_nameable,
   complete_ming_maps_to_nameable,
   incomplete_ming_maps_to_unnameable,
   handled_in_ming_iff_nameable,
   name_deferred_boundaries_handled_in_ming⟩

end SSBX.Foundation.Modern.MingBoundary
