/-
# KeBoundary — 可感 / 可行 / 可证 之边界

Companion: `义理/边界/可的边界 · 感行证.md`

本文件承接 `KnowableBoundary.lean` 中 deferred 的“可”边界：

1. 可感 / 不可感；
2. 可行 / 不可行；
3. 可证 / 不可证。

其中“可证 / 不可证”只作 typed skeleton：区分 proof-interface 内外，
不展开证明论、模型论或独立性证明。

可测 / 不可测虽也从 `KnowableBoundary.lean` deferred，但由
`LiangBoundary.lean` 承接；可名 / 不可名由 `MingBoundary.lean` 承接。
本文件保持“感 / 行 / 证”的边界职责。
-/
import SSBX.Foundation.Modern.KnowableBoundary

namespace SSBX.Foundation.Modern.KeBoundary

open SSBX.Foundation.Modern.KnowableBoundary

/-! ## § 1 Axes of ke-boundaries -/

/-- “可”的轴：可知、可感、可行、可证。 -/
inductive KeAxis : Type
  | know
  | sense
  | act
  | prove
  deriving Repr, DecidableEq

/-- 边界两侧：界内 / 界外。 -/
inductive BoundarySide : Type
  | inside
  | outside
  deriving Repr, DecidableEq

/-- 一个“可”边界由轴与两侧构成。 -/
structure KeBoundary where
  axis : KeAxis
  side : BoundarySide
  deriving Repr

def knowBoundaryInside : KeBoundary := ⟨.know, .inside⟩
def senseBoundaryInside : KeBoundary := ⟨.sense, .inside⟩
def actBoundaryInside : KeBoundary := ⟨.act, .inside⟩
def proveBoundaryInside : KeBoundary := ⟨.prove, .inside⟩

/-- 边界两侧穷尽：任一 side 不是 inside 就是 outside。 -/
theorem boundary_side_exhaustive (s : BoundarySide) :
    s = .inside ∨ s = .outside := by
  cases s <;> simp

/-- inside 与 outside 不相同。 -/
theorem inside_ne_outside :
    BoundarySide.inside ≠ BoundarySide.outside := by
  intro h
  cases h

/-- 任一 `KeBoundary` 都有明确的 inside / outside 一侧。 -/
theorem ke_boundary_side_exhaustive (b : KeBoundary) :
    b.side = .inside ∨ b.side = .outside :=
  boundary_side_exhaustive b.side

/-- 可感轴不同于可知轴。 -/
theorem sense_axis_ne_know_axis :
    KeAxis.sense ≠ KeAxis.know := by
  intro h
  cases h

/-- 可行轴不同于可知轴。 -/
theorem act_axis_ne_know_axis :
    KeAxis.act ≠ KeAxis.know := by
  intro h
  cases h

/-- 可证轴不同于可知轴，虽它会使用可知语言。 -/
theorem prove_axis_ne_know_axis :
    KeAxis.prove ≠ KeAxis.know := by
  intro h
  cases h

/-- 四条“可”轴两两不同的核心见证。 -/
theorem ke_axes_pairwise_distinct :
    KeAxis.know ≠ KeAxis.sense
    ∧ KeAxis.know ≠ KeAxis.act
    ∧ KeAxis.know ≠ KeAxis.prove
    ∧ KeAxis.sense ≠ KeAxis.act
    ∧ KeAxis.sense ≠ KeAxis.prove
    ∧ KeAxis.act ≠ KeAxis.prove := by
  simp

/-! ## § 2 可感 / 不可感 -/

/-- 感受边界的两侧。 -/
inductive SensibilityRegion : Type
  | feelable
  | unfeelable
  deriving Repr, DecidableEq

def Feelable (r : SensibilityRegion) : Prop :=
  r = .feelable

def Unfeelable (r : SensibilityRegion) : Prop :=
  r = .unfeelable

/-- 可感 / 不可感 穷尽感受边界。 -/
theorem sensibility_exhaustive (r : SensibilityRegion) :
    Feelable r ∨ Unfeelable r := by
  cases r <;> simp [Feelable, Unfeelable]

/-- 可感与不可感互斥。 -/
theorem feelable_not_unfeelable (r : SensibilityRegion) :
    Feelable r → ¬ Unfeelable r := by
  intro hf interlace
  unfold Feelable at hf
  unfold Unfeelable at interlace
  rw [hf] at interlace
  cases interlace

/-- 不可感与可感互斥。 -/
theorem unfeelable_not_feelable (r : SensibilityRegion) :
    Unfeelable r → ¬ Feelable r := by
  intro interlace hf
  exact feelable_not_unfeelable r hf interlace

/-- 可感边界完备：可感 / 不可感穷尽，且两向互斥。 -/
theorem sensibility_boundary_complete :
    (∀ r : SensibilityRegion, Feelable r ∨ Unfeelable r)
    ∧ (∀ r : SensibilityRegion, Feelable r → ¬ Unfeelable r)
    ∧ (∀ r : SensibilityRegion, Unfeelable r → ¬ Feelable r) :=
  ⟨sensibility_exhaustive, feelable_not_unfeelable, unfeelable_not_feelable⟩

/-! ## § 3 可行 / 不可行 -/

/-- 行动边界的两侧。 -/
inductive ActionabilityRegion : Type
  | actionable
  | unactionable
  deriving Repr, DecidableEq

def Actionable (r : ActionabilityRegion) : Prop :=
  r = .actionable

def Unactionable (r : ActionabilityRegion) : Prop :=
  r = .unactionable

/-- 可行 / 不可行 穷尽行动边界。 -/
theorem actionability_exhaustive (r : ActionabilityRegion) :
    Actionable r ∨ Unactionable r := by
  cases r <;> simp [Actionable, Unactionable]

/-- 可行与不可行互斥。 -/
theorem actionable_not_unactionable (r : ActionabilityRegion) :
    Actionable r → ¬ Unactionable r := by
  intro ha interlace
  unfold Actionable at ha
  unfold Unactionable at interlace
  rw [ha] at interlace
  cases interlace

/-- 不可行与可行互斥。 -/
theorem unactionable_not_actionable (r : ActionabilityRegion) :
    Unactionable r → ¬ Actionable r := by
  intro interlace ha
  exact actionable_not_unactionable r ha interlace

/-- 可行边界完备：可行 / 不可行穷尽，且两向互斥。 -/
theorem actionability_boundary_complete :
    (∀ r : ActionabilityRegion, Actionable r ∨ Unactionable r)
    ∧ (∀ r : ActionabilityRegion, Actionable r → ¬ Unactionable r)
    ∧ (∀ r : ActionabilityRegion, Unactionable r → ¬ Actionable r) :=
  ⟨actionability_exhaustive, actionable_not_unactionable, unactionable_not_actionable⟩

/-! ## § 4 可证 / 不可证 typed skeleton -/

/-- 证明边界的两侧：在当前 proof interface 内，或在其外。 -/
inductive ProofRegion : Type
  | provable
  | unprovable
  deriving Repr, DecidableEq

def Provable (r : ProofRegion) : Prop :=
  r = .provable

def Unprovable (r : ProofRegion) : Prop :=
  r = .unprovable

/-- 可证 / 不可证 穷尽当前 proof skeleton。 -/
theorem proof_region_exhaustive (r : ProofRegion) :
    Provable r ∨ Unprovable r := by
  cases r <;> simp [Provable, Unprovable]

/-- 可证与不可证互斥。 -/
theorem provable_not_unprovable (r : ProofRegion) :
    Provable r → ¬ Unprovable r := by
  intro hp interlace
  unfold Provable at hp
  unfold Unprovable at interlace
  rw [hp] at interlace
  cases interlace

/-- 不可证与可证互斥。 -/
theorem unprovable_not_provable (r : ProofRegion) :
    Unprovable r → ¬ Provable r := by
  intro interlace hp
  exact provable_not_unprovable r hp interlace

/-- 可证边界完备：可证 / 不可证穷尽，且两向互斥。 -/
theorem proof_boundary_complete :
    (∀ r : ProofRegion, Provable r ∨ Unprovable r)
    ∧ (∀ r : ProofRegion, Provable r → ¬ Unprovable r)
    ∧ (∀ r : ProofRegion, Unprovable r → ¬ Provable r) :=
  ⟨proof_region_exhaustive, provable_not_unprovable, unprovable_not_provable⟩

/-- 证明边界使用可知语言表达：这里不展开证明论，只把 proof-boundary 作为可说 skeleton。 -/
def proofRegionAsKnowable (_r : ProofRegion) : KnowableRegion :=
  .withinDescribableLi

/-- 可证 / 不可证 的区分本身仍在可说界内表达。 -/
theorem proof_boundary_is_sayable_skeleton (r : ProofRegion) :
    Sayable (proofRegionAsKnowable r) := by
  rfl

/-! ## § 5 This file completes the feel/action/proof deferred boundaries -/

/-- `KnowableBoundary` 中 deferred 的可感 / 可行 / 可证，在本文件中承接处理；
    可测 / 不可测留给 `LiangBoundary.lean`，可名 / 不可名留给 `MingBoundary.lean`。
    保持 constructor-explicit，使未来新增 deferred 轴必须显式审计。 -/
def handledInKeBoundary : DeferredKeBoundary → Bool
  | .feelable
  | .unfeelable
  | .actionable
  | .unactionable
  | .provable
  | .unprovable => true
  | .measurable
  | .unmeasurable
  | .nameable
  | .unnameable => false

/-- 本文件准确承接可感 / 可行 / 可证六个 deferred 项。 -/
theorem feel_act_proof_boundaries_handled_here :
    handledHere .feelable = false ∧ handledInKeBoundary .feelable = true
    ∧ handledHere .unfeelable = false ∧ handledInKeBoundary .unfeelable = true
    ∧ handledHere .actionable = false ∧ handledInKeBoundary .actionable = true
    ∧ handledHere .unactionable = false ∧ handledInKeBoundary .unactionable = true
    ∧ handledHere .provable = false ∧ handledInKeBoundary .provable = true
    ∧ handledHere .unprovable = false ∧ handledInKeBoundary .unprovable = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 可测 / 不可测不在本文件处理；它们被明确留给“量”边界。 -/
theorem measurable_boundaries_not_handled_in_ke :
    handledHere .measurable = false ∧ handledInKeBoundary .measurable = false
    ∧ handledHere .unmeasurable = false ∧ handledInKeBoundary .unmeasurable = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- 可名 / 不可名不在本文件处理；它们被明确留给“名”边界。 -/
theorem name_boundaries_not_handled_in_ke :
    handledHere .nameable = false ∧ handledInKeBoundary .nameable = false
    ∧ handledHere .unnameable = false ∧ handledInKeBoundary .unnameable = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## § 6 Public summary -/

/-- 公开摘要：
    (0) 四条“可”轴两两不同；
    (1) 可感 / 不可感穷尽且互斥；
    (2) 可行 / 不可行穷尽且互斥；
    (3) 可证 / 不可证在 typed proof skeleton 中穷尽且互斥；
    (4) proof-boundary 只作可说 skeleton，不展开证明论；
    (5) deferred 可感 / 可行 / 可证边界由本文件承接；
    (6) deferred 可测 / 不可测边界明确不在本文件处理；
    (7) deferred 可名 / 不可名边界明确不在本文件处理。 -/
theorem ke_boundary_summary :
    (KeAxis.know ≠ KeAxis.sense
      ∧ KeAxis.know ≠ KeAxis.act
      ∧ KeAxis.know ≠ KeAxis.prove
      ∧ KeAxis.sense ≠ KeAxis.act
      ∧ KeAxis.sense ≠ KeAxis.prove
      ∧ KeAxis.act ≠ KeAxis.prove)
    ∧ (∀ b : KeBoundary, b.side = .inside ∨ b.side = .outside)
    ∧ (∀ r : SensibilityRegion, Feelable r ∨ Unfeelable r)
    ∧ (∀ r : SensibilityRegion, Feelable r → ¬ Unfeelable r)
    ∧ (∀ r : SensibilityRegion, Unfeelable r → ¬ Feelable r)
    ∧ (∀ r : ActionabilityRegion, Actionable r ∨ Unactionable r)
    ∧ (∀ r : ActionabilityRegion, Actionable r → ¬ Unactionable r)
    ∧ (∀ r : ActionabilityRegion, Unactionable r → ¬ Actionable r)
    ∧ (∀ r : ProofRegion, Provable r ∨ Unprovable r)
    ∧ (∀ r : ProofRegion, Provable r → ¬ Unprovable r)
    ∧ (∀ r : ProofRegion, Unprovable r → ¬ Provable r)
    ∧ (∀ r : ProofRegion, Sayable (proofRegionAsKnowable r))
    ∧ (handledHere .feelable = false ∧ handledInKeBoundary .feelable = true
      ∧ handledHere .unfeelable = false ∧ handledInKeBoundary .unfeelable = true
      ∧ handledHere .actionable = false ∧ handledInKeBoundary .actionable = true
      ∧ handledHere .unactionable = false ∧ handledInKeBoundary .unactionable = true
      ∧ handledHere .provable = false ∧ handledInKeBoundary .provable = true
      ∧ handledHere .unprovable = false ∧ handledInKeBoundary .unprovable = true)
    ∧ (handledHere .measurable = false ∧ handledInKeBoundary .measurable = false
      ∧ handledHere .unmeasurable = false ∧ handledInKeBoundary .unmeasurable = false)
    ∧ (handledHere .nameable = false ∧ handledInKeBoundary .nameable = false
      ∧ handledHere .unnameable = false ∧ handledInKeBoundary .unnameable = false) :=
  ⟨ke_axes_pairwise_distinct,
   ke_boundary_side_exhaustive,
   sensibility_exhaustive,
   feelable_not_unfeelable,
   unfeelable_not_feelable,
   actionability_exhaustive,
   actionable_not_unactionable,
   unactionable_not_actionable,
   proof_region_exhaustive,
   provable_not_unprovable,
   unprovable_not_provable,
   proof_boundary_is_sayable_skeleton,
   feel_act_proof_boundaries_handled_here,
   measurable_boundaries_not_handled_in_ke,
   name_boundaries_not_handled_in_ke⟩

end SSBX.Foundation.Modern.KeBoundary
