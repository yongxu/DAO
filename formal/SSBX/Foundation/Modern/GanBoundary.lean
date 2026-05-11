/-
# GanBoundary — 感之边界 / 受觉现报

Companion: `义理/边界/感的边界 · 受觉现.md`

本文件形式化一个薄的“感”边界：

1. “感”不是“测”：感可有现象性，但未必有仪器、校准、记录；
2. “感”不是“量”：感可被量化，但感本身不是数量或测度；
3. “感”不是“推”：感可以成为推断材料，但不是推断命题；
4. 完整的感受流程映射到 `KeBoundary` 的可感内侧。
-/
import SSBX.Foundation.Modern.KeBoundary

namespace SSBX.Foundation.Modern.GanBoundary

open SSBX.Foundation.Modern.KeBoundary

/-! ## § 1 Axes of gan-boundaries -/

/-- “感”的五条流程轴：触、受、感、现、报。 -/
inductive GanAxis : Type
  | exposure
  | reception
  | affection
  | phenomenality
  | report
  deriving Repr, DecidableEq

/-- 五条“感”轴两两不同的核心见证。 -/
theorem gan_axes_pairwise_distinct :
    GanAxis.exposure ≠ GanAxis.reception
    ∧ GanAxis.exposure ≠ GanAxis.affection
    ∧ GanAxis.exposure ≠ GanAxis.phenomenality
    ∧ GanAxis.exposure ≠ GanAxis.report
    ∧ GanAxis.reception ≠ GanAxis.affection
    ∧ GanAxis.reception ≠ GanAxis.phenomenality
    ∧ GanAxis.reception ≠ GanAxis.report
    ∧ GanAxis.affection ≠ GanAxis.phenomenality
    ∧ GanAxis.affection ≠ GanAxis.report
    ∧ GanAxis.phenomenality ≠ GanAxis.report := by
  simp

/-! ## § 2 触 / 未触 -/

inductive ExposureRegion : Type
  | exposed
  | unexposed
  deriving Repr, DecidableEq

def Exposed (r : ExposureRegion) : Prop := r = .exposed
def Unexposed (r : ExposureRegion) : Prop := r = .unexposed

theorem exposure_region_exhaustive (r : ExposureRegion) :
    Exposed r ∨ Unexposed r := by
  cases r <;> simp [Exposed, Unexposed]

theorem exposed_not_unexposed (r : ExposureRegion) :
    Exposed r → ¬ Unexposed r := by
  intro he interlace
  unfold Exposed at he
  unfold Unexposed at interlace
  rw [he] at interlace
  cases interlace

theorem unexposed_not_exposed (r : ExposureRegion) :
    Unexposed r → ¬ Exposed r := by
  intro interlace he
  exact exposed_not_unexposed r he interlace

theorem exposure_boundary_complete :
    (∀ r : ExposureRegion, Exposed r ∨ Unexposed r)
    ∧ (∀ r : ExposureRegion, Exposed r → ¬ Unexposed r)
    ∧ (∀ r : ExposureRegion, Unexposed r → ¬ Exposed r) :=
  ⟨exposure_region_exhaustive, exposed_not_unexposed, unexposed_not_exposed⟩

/-! ## § 3 受 / 未受 -/

inductive ReceptionRegion : Type
  | received
  | unreceived
  deriving Repr, DecidableEq

def Received (r : ReceptionRegion) : Prop := r = .received
def Unreceived (r : ReceptionRegion) : Prop := r = .unreceived

theorem reception_region_exhaustive (r : ReceptionRegion) :
    Received r ∨ Unreceived r := by
  cases r <;> simp [Received, Unreceived]

theorem received_not_unreceived (r : ReceptionRegion) :
    Received r → ¬ Unreceived r := by
  intro hr interlace
  unfold Received at hr
  unfold Unreceived at interlace
  rw [hr] at interlace
  cases interlace

theorem unreceived_not_received (r : ReceptionRegion) :
    Unreceived r → ¬ Received r := by
  intro interlace hr
  exact received_not_unreceived r hr interlace

theorem reception_boundary_complete :
    (∀ r : ReceptionRegion, Received r ∨ Unreceived r)
    ∧ (∀ r : ReceptionRegion, Received r → ¬ Unreceived r)
    ∧ (∀ r : ReceptionRegion, Unreceived r → ¬ Received r) :=
  ⟨reception_region_exhaustive, received_not_unreceived, unreceived_not_received⟩

/-! ## § 4 感 / 未感 -/

inductive AffectionRegion : Type
  | affected
  | unaffected
  deriving Repr, DecidableEq

def Affected (r : AffectionRegion) : Prop := r = .affected
def Unaffected (r : AffectionRegion) : Prop := r = .unaffected

theorem affection_region_exhaustive (r : AffectionRegion) :
    Affected r ∨ Unaffected r := by
  cases r <;> simp [Affected, Unaffected]

theorem affected_not_unaffected (r : AffectionRegion) :
    Affected r → ¬ Unaffected r := by
  intro ha interlace
  unfold Affected at ha
  unfold Unaffected at interlace
  rw [ha] at interlace
  cases interlace

theorem unaffected_not_affected (r : AffectionRegion) :
    Unaffected r → ¬ Affected r := by
  intro interlace ha
  exact affected_not_unaffected r ha interlace

theorem affection_boundary_complete :
    (∀ r : AffectionRegion, Affected r ∨ Unaffected r)
    ∧ (∀ r : AffectionRegion, Affected r → ¬ Unaffected r)
    ∧ (∀ r : AffectionRegion, Unaffected r → ¬ Affected r) :=
  ⟨affection_region_exhaustive, affected_not_unaffected, unaffected_not_affected⟩

/-! ## § 5 现象化 / 未现象化 -/

inductive PhenomenalRegion : Type
  | phenomenal
  | nonphenomenal
  deriving Repr, DecidableEq

def Phenomenal (r : PhenomenalRegion) : Prop := r = .phenomenal
def Nonphenomenal (r : PhenomenalRegion) : Prop := r = .nonphenomenal

theorem phenomenal_region_exhaustive (r : PhenomenalRegion) :
    Phenomenal r ∨ Nonphenomenal r := by
  cases r <;> simp [Phenomenal, Nonphenomenal]

theorem phenomenal_not_nonphenomenal (r : PhenomenalRegion) :
    Phenomenal r → ¬ Nonphenomenal r := by
  intro hp hn
  unfold Phenomenal at hp
  unfold Nonphenomenal at hn
  rw [hp] at hn
  cases hn

theorem nonphenomenal_not_phenomenal (r : PhenomenalRegion) :
    Nonphenomenal r → ¬ Phenomenal r := by
  intro hn hp
  exact phenomenal_not_nonphenomenal r hp hn

theorem phenomenal_boundary_complete :
    (∀ r : PhenomenalRegion, Phenomenal r ∨ Nonphenomenal r)
    ∧ (∀ r : PhenomenalRegion, Phenomenal r → ¬ Nonphenomenal r)
    ∧ (∀ r : PhenomenalRegion, Nonphenomenal r → ¬ Phenomenal r) :=
  ⟨phenomenal_region_exhaustive,
   phenomenal_not_nonphenomenal,
   nonphenomenal_not_phenomenal⟩

/-! ## § 6 可报 / 不可报 -/

inductive FeelingReportRegion : Type
  | reportable
  | unreportable
  deriving Repr, DecidableEq

def Reportable (r : FeelingReportRegion) : Prop := r = .reportable
def Unreportable (r : FeelingReportRegion) : Prop := r = .unreportable

theorem feeling_report_region_exhaustive (r : FeelingReportRegion) :
    Reportable r ∨ Unreportable r := by
  cases r <;> simp [Reportable, Unreportable]

theorem reportable_not_unreportable (r : FeelingReportRegion) :
    Reportable r → ¬ Unreportable r := by
  intro hr interlace
  unfold Reportable at hr
  unfold Unreportable at interlace
  rw [hr] at interlace
  cases interlace

theorem unreportable_not_reportable (r : FeelingReportRegion) :
    Unreportable r → ¬ Reportable r := by
  intro interlace hr
  exact reportable_not_unreportable r hr interlace

theorem feeling_report_boundary_complete :
    (∀ r : FeelingReportRegion, Reportable r ∨ Unreportable r)
    ∧ (∀ r : FeelingReportRegion, Reportable r → ¬ Unreportable r)
    ∧ (∀ r : FeelingReportRegion, Unreportable r → ¬ Reportable r) :=
  ⟨feeling_report_region_exhaustive,
   reportable_not_unreportable,
   unreportable_not_reportable⟩

/-! ## § 7 Complete feeling pipeline -/

structure GanSkeleton where
  exposure : ExposureRegion
  reception : ReceptionRegion
  affection : AffectionRegion
  phenomenality : PhenomenalRegion
  report : FeelingReportRegion
  deriving Repr

def CompleteGan (g : GanSkeleton) : Prop :=
  Exposed g.exposure
    ∧ Received g.reception
    ∧ Affected g.affection
    ∧ Phenomenal g.phenomenality
    ∧ Reportable g.report

def ganAsSensibility (g : GanSkeleton) : SensibilityRegion :=
  match g.exposure, g.reception, g.affection, g.phenomenality, g.report with
  | .exposed, .received, .affected, .phenomenal, .reportable => .feelable
  | _, _, _, _, _ => .unfeelable

theorem complete_gan_maps_to_feelable (g : GanSkeleton) :
    CompleteGan g → Feelable (ganAsSensibility g) := by
  intro h
  cases g with
  | mk e r a p rep =>
      rcases h with ⟨he, hr, ha, hp, hrep⟩
      simp [Exposed] at he
      simp [Received] at hr
      simp [Affected] at ha
      simp [Phenomenal] at hp
      simp [Reportable] at hrep
      subst e
      subst r
      subst a
      subst p
      subst rep
      rfl

theorem incomplete_gan_maps_to_unfeelable (g : GanSkeleton) (h : ¬ CompleteGan g) :
    ganAsSensibility g = .unfeelable := by
  cases g with
  | mk e r a p rep =>
      cases e <;> cases r <;> cases a <;> cases p <;> cases rep <;>
        simp [ganAsSensibility, CompleteGan, Exposed, Received, Affected,
          Phenomenal, Reportable] at h ⊢

/-! ## § 8 Public summary -/

theorem gan_boundary_summary :
    (GanAxis.exposure ≠ GanAxis.reception
      ∧ GanAxis.exposure ≠ GanAxis.affection
      ∧ GanAxis.exposure ≠ GanAxis.phenomenality
      ∧ GanAxis.exposure ≠ GanAxis.report
      ∧ GanAxis.reception ≠ GanAxis.affection
      ∧ GanAxis.reception ≠ GanAxis.phenomenality
      ∧ GanAxis.reception ≠ GanAxis.report
      ∧ GanAxis.affection ≠ GanAxis.phenomenality
      ∧ GanAxis.affection ≠ GanAxis.report
      ∧ GanAxis.phenomenality ≠ GanAxis.report)
    ∧ (∀ r : ExposureRegion, Exposed r ∨ Unexposed r)
    ∧ (∀ r : ExposureRegion, Exposed r → ¬ Unexposed r)
    ∧ (∀ r : ExposureRegion, Unexposed r → ¬ Exposed r)
    ∧ (∀ r : ReceptionRegion, Received r ∨ Unreceived r)
    ∧ (∀ r : ReceptionRegion, Received r → ¬ Unreceived r)
    ∧ (∀ r : ReceptionRegion, Unreceived r → ¬ Received r)
    ∧ (∀ r : AffectionRegion, Affected r ∨ Unaffected r)
    ∧ (∀ r : AffectionRegion, Affected r → ¬ Unaffected r)
    ∧ (∀ r : AffectionRegion, Unaffected r → ¬ Affected r)
    ∧ (∀ r : PhenomenalRegion, Phenomenal r ∨ Nonphenomenal r)
    ∧ (∀ r : PhenomenalRegion, Phenomenal r → ¬ Nonphenomenal r)
    ∧ (∀ r : PhenomenalRegion, Nonphenomenal r → ¬ Phenomenal r)
    ∧ (∀ r : FeelingReportRegion, Reportable r ∨ Unreportable r)
    ∧ (∀ r : FeelingReportRegion, Reportable r → ¬ Unreportable r)
    ∧ (∀ r : FeelingReportRegion, Unreportable r → ¬ Reportable r)
    ∧ (∀ g : GanSkeleton, CompleteGan g → Feelable (ganAsSensibility g))
    ∧ (∀ g : GanSkeleton, ¬ CompleteGan g → ganAsSensibility g = .unfeelable) :=
  ⟨gan_axes_pairwise_distinct,
   exposure_region_exhaustive,
   exposed_not_unexposed,
   unexposed_not_exposed,
   reception_region_exhaustive,
   received_not_unreceived,
   unreceived_not_received,
   affection_region_exhaustive,
   affected_not_unaffected,
   unaffected_not_affected,
   phenomenal_region_exhaustive,
   phenomenal_not_nonphenomenal,
   nonphenomenal_not_phenomenal,
   feeling_report_region_exhaustive,
   reportable_not_unreportable,
   unreportable_not_reportable,
   complete_gan_maps_to_feelable,
   incomplete_gan_maps_to_unfeelable⟩

end SSBX.Foundation.Modern.GanBoundary
