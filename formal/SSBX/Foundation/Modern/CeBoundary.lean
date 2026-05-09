/-
# CeBoundary — 测之边界 / 观测流程 / 读数记录

Companion: `义理/边界/测的边界 · 观验读.md`

本文件形式化一个薄的“测”边界：

1. “测”不是“量”的同义词，而是把对象经接口、方法、校准、读数、
   记录落成可读结果的流程；
2. “测”也不是“推”：测止于读数 / 记录，统计推断是下一层；
3. 六条测量接口轴在本 typed skeleton 中各有内外两侧，且穷尽互斥；
4. 完整测量流程映射到 `LiangBoundary` 的 measurement 内侧。
-/
import SSBX.Foundation.Modern.LiangBoundary
import SSBX.Foundation.Modern.QuantumSpacetime

namespace SSBX.Foundation.Modern.CeBoundary

open SSBX.Foundation.Modern.LiangBoundary
open SSBX.Foundation.Modern.QuantumSpacetime

/-! ## § 1 Axes of ce-boundaries -/

/-- “测”的六条流程轴：可观、接口、方法、校准、读数、记录。 -/
inductive CeAxis : Type
  | observability
  | interface
  | protocol
  | calibration
  | readout
  | record
  deriving Repr, DecidableEq

/-- 六条“测”轴两两不同的核心见证。 -/
theorem ce_axes_pairwise_distinct :
    CeAxis.observability ≠ CeAxis.interface
    ∧ CeAxis.observability ≠ CeAxis.protocol
    ∧ CeAxis.observability ≠ CeAxis.calibration
    ∧ CeAxis.observability ≠ CeAxis.readout
    ∧ CeAxis.observability ≠ CeAxis.record
    ∧ CeAxis.interface ≠ CeAxis.protocol
    ∧ CeAxis.interface ≠ CeAxis.calibration
    ∧ CeAxis.interface ≠ CeAxis.readout
    ∧ CeAxis.interface ≠ CeAxis.record
    ∧ CeAxis.protocol ≠ CeAxis.calibration
    ∧ CeAxis.protocol ≠ CeAxis.readout
    ∧ CeAxis.protocol ≠ CeAxis.record
    ∧ CeAxis.calibration ≠ CeAxis.readout
    ∧ CeAxis.calibration ≠ CeAxis.record
    ∧ CeAxis.readout ≠ CeAxis.record := by
  simp

/-! ## § 2 可观 / 不可观 -/

/-- 可观边界：对象是否能进入观测窗口。 -/
inductive ObservabilityRegion : Type
  | observable
  | unobservable
  deriving Repr, DecidableEq

def Observable (r : ObservabilityRegion) : Prop :=
  r = .observable

def Unobservable (r : ObservabilityRegion) : Prop :=
  r = .unobservable

theorem observability_region_exhaustive (r : ObservabilityRegion) :
    Observable r ∨ Unobservable r := by
  cases r <;> simp [Observable, Unobservable]

theorem observable_not_unobservable (r : ObservabilityRegion) :
    Observable r → ¬ Unobservable r := by
  intro ho hu
  unfold Observable at ho
  unfold Unobservable at hu
  rw [ho] at hu
  cases hu

theorem unobservable_not_observable (r : ObservabilityRegion) :
    Unobservable r → ¬ Observable r := by
  intro hu ho
  exact observable_not_unobservable r ho hu

/-- 可观边界完备：可观 / 不可观穷尽，且两向互斥。 -/
theorem observability_boundary_complete :
    (∀ r : ObservabilityRegion, Observable r ∨ Unobservable r)
    ∧ (∀ r : ObservabilityRegion, Observable r → ¬ Unobservable r)
    ∧ (∀ r : ObservabilityRegion, Unobservable r → ¬ Observable r) :=
  ⟨observability_region_exhaustive,
   observable_not_unobservable,
   unobservable_not_observable⟩

/-! ## § 3 可接 / 不可接 -/

/-- 接口边界：观测接口 / 仪器是否已经接上对象。 -/
inductive InterfaceRegion : Type
  | interfaced
  | uninterfaced
  deriving Repr, DecidableEq

def Interfaced (r : InterfaceRegion) : Prop :=
  r = .interfaced

def Uninterfaced (r : InterfaceRegion) : Prop :=
  r = .uninterfaced

theorem interface_region_exhaustive (r : InterfaceRegion) :
    Interfaced r ∨ Uninterfaced r := by
  cases r <;> simp [Interfaced, Uninterfaced]

theorem interfaced_not_uninterfaced (r : InterfaceRegion) :
    Interfaced r → ¬ Uninterfaced r := by
  intro hi hu
  unfold Interfaced at hi
  unfold Uninterfaced at hu
  rw [hi] at hu
  cases hu

theorem uninterfaced_not_interfaced (r : InterfaceRegion) :
    Uninterfaced r → ¬ Interfaced r := by
  intro hu hi
  exact interfaced_not_uninterfaced r hi hu

/-- 接口边界完备：可接 / 不可接穷尽，且两向互斥。 -/
theorem interface_boundary_complete :
    (∀ r : InterfaceRegion, Interfaced r ∨ Uninterfaced r)
    ∧ (∀ r : InterfaceRegion, Interfaced r → ¬ Uninterfaced r)
    ∧ (∀ r : InterfaceRegion, Uninterfaced r → ¬ Interfaced r) :=
  ⟨interface_region_exhaustive,
   interfaced_not_uninterfaced,
   uninterfaced_not_interfaced⟩

/-! ## § 4 有法 / 无法 -/

/-- 方法边界：测量协议是否已指定。 -/
inductive ProtocolRegion : Type
  | specified
  | unspecified
  deriving Repr, DecidableEq

def ProtocolSpecified (r : ProtocolRegion) : Prop :=
  r = .specified

def ProtocolUnspecified (r : ProtocolRegion) : Prop :=
  r = .unspecified

theorem protocol_region_exhaustive (r : ProtocolRegion) :
    ProtocolSpecified r ∨ ProtocolUnspecified r := by
  cases r <;> simp [ProtocolSpecified, ProtocolUnspecified]

theorem specified_not_unspecified (r : ProtocolRegion) :
    ProtocolSpecified r → ¬ ProtocolUnspecified r := by
  intro hs hu
  unfold ProtocolSpecified at hs
  unfold ProtocolUnspecified at hu
  rw [hs] at hu
  cases hu

theorem unspecified_not_specified (r : ProtocolRegion) :
    ProtocolUnspecified r → ¬ ProtocolSpecified r := by
  intro hu hs
  exact specified_not_unspecified r hs hu

/-- 方法边界完备：有法 / 无法穷尽，且两向互斥。 -/
theorem protocol_boundary_complete :
    (∀ r : ProtocolRegion, ProtocolSpecified r ∨ ProtocolUnspecified r)
    ∧ (∀ r : ProtocolRegion, ProtocolSpecified r → ¬ ProtocolUnspecified r)
    ∧ (∀ r : ProtocolRegion, ProtocolUnspecified r → ¬ ProtocolSpecified r) :=
  ⟨protocol_region_exhaustive,
   specified_not_unspecified,
   unspecified_not_specified⟩

/-! ## § 5 已校 / 未校 -/

/-- 校准边界：尺度、零点、基线或参照是否已固定。 -/
inductive CalibrationRegion : Type
  | calibrated
  | uncalibrated
  deriving Repr, DecidableEq

def Calibrated (r : CalibrationRegion) : Prop :=
  r = .calibrated

def Uncalibrated (r : CalibrationRegion) : Prop :=
  r = .uncalibrated

theorem calibration_region_exhaustive (r : CalibrationRegion) :
    Calibrated r ∨ Uncalibrated r := by
  cases r <;> simp [Calibrated, Uncalibrated]

theorem calibrated_not_uncalibrated (r : CalibrationRegion) :
    Calibrated r → ¬ Uncalibrated r := by
  intro hc hu
  unfold Calibrated at hc
  unfold Uncalibrated at hu
  rw [hc] at hu
  cases hu

theorem uncalibrated_not_calibrated (r : CalibrationRegion) :
    Uncalibrated r → ¬ Calibrated r := by
  intro hu hc
  exact calibrated_not_uncalibrated r hc hu

/-- 校准边界完备：已校 / 未校穷尽，且两向互斥。 -/
theorem calibration_boundary_complete :
    (∀ r : CalibrationRegion, Calibrated r ∨ Uncalibrated r)
    ∧ (∀ r : CalibrationRegion, Calibrated r → ¬ Uncalibrated r)
    ∧ (∀ r : CalibrationRegion, Uncalibrated r → ¬ Calibrated r) :=
  ⟨calibration_region_exhaustive,
   calibrated_not_uncalibrated,
   uncalibrated_not_calibrated⟩

/-! ## § 6 可读 / 不可读 -/

/-- 读数边界：测量是否产生可读输出。 -/
inductive ReadoutRegion : Type
  | readable
  | unreadable
  deriving Repr, DecidableEq

def Readable (r : ReadoutRegion) : Prop :=
  r = .readable

def Unreadable (r : ReadoutRegion) : Prop :=
  r = .unreadable

theorem readout_region_exhaustive (r : ReadoutRegion) :
    Readable r ∨ Unreadable r := by
  cases r <;> simp [Readable, Unreadable]

theorem readable_not_unreadable (r : ReadoutRegion) :
    Readable r → ¬ Unreadable r := by
  intro hr hu
  unfold Readable at hr
  unfold Unreadable at hu
  rw [hr] at hu
  cases hu

theorem unreadable_not_readable (r : ReadoutRegion) :
    Unreadable r → ¬ Readable r := by
  intro hu hr
  exact readable_not_unreadable r hr hu

/-- 读数边界完备：可读 / 不可读穷尽，且两向互斥。 -/
theorem readout_boundary_complete :
    (∀ r : ReadoutRegion, Readable r ∨ Unreadable r)
    ∧ (∀ r : ReadoutRegion, Readable r → ¬ Unreadable r)
    ∧ (∀ r : ReadoutRegion, Unreadable r → ¬ Readable r) :=
  ⟨readout_region_exhaustive,
   readable_not_unreadable,
   unreadable_not_readable⟩

/-! ## § 7 可记 / 不可记 -/

/-- 记录边界：读数是否进入可复核记录。 -/
inductive RecordRegion : Type
  | recorded
  | unrecorded
  deriving Repr, DecidableEq

def Recorded (r : RecordRegion) : Prop :=
  r = .recorded

def Unrecorded (r : RecordRegion) : Prop :=
  r = .unrecorded

theorem record_region_exhaustive (r : RecordRegion) :
    Recorded r ∨ Unrecorded r := by
  cases r <;> simp [Recorded, Unrecorded]

theorem recorded_not_unrecorded (r : RecordRegion) :
    Recorded r → ¬ Unrecorded r := by
  intro hr hu
  unfold Recorded at hr
  unfold Unrecorded at hu
  rw [hr] at hu
  cases hu

theorem unrecorded_not_recorded (r : RecordRegion) :
    Unrecorded r → ¬ Recorded r := by
  intro hu hr
  exact recorded_not_unrecorded r hr hu

/-- 记录边界完备：可记 / 不可记穷尽，且两向互斥。 -/
theorem record_boundary_complete :
    (∀ r : RecordRegion, Recorded r ∨ Unrecorded r)
    ∧ (∀ r : RecordRegion, Recorded r → ¬ Unrecorded r)
    ∧ (∀ r : RecordRegion, Unrecorded r → ¬ Recorded r) :=
  ⟨record_region_exhaustive,
   recorded_not_unrecorded,
   unrecorded_not_recorded⟩

/-! ## § 8 Complete measurement pipeline -/

/-- 一个最薄的测量流程骨架。 -/
structure CeSkeleton where
  observability : ObservabilityRegion
  interface : InterfaceRegion
  protocol : ProtocolRegion
  calibration : CalibrationRegion
  readout : ReadoutRegion
  record : RecordRegion
  deriving Repr

/-- 完整测量：可观、可接、有法、已校、可读、可记。 -/
def CompleteCe (m : CeSkeleton) : Prop :=
  Observable m.observability
    ∧ Interfaced m.interface
    ∧ ProtocolSpecified m.protocol
    ∧ Calibrated m.calibration
    ∧ Readable m.readout
    ∧ Recorded m.record

/-- 从“测”流程映射回“量”的测量边界。 -/
def ceAsLiangMeasurement (m : CeSkeleton) : MeasurementRegion :=
  match m.observability, m.interface, m.protocol, m.calibration, m.readout, m.record with
  | .observable, .interfaced, .specified, .calibrated, .readable, .recorded =>
      .measurableByInterface
  | _, _, _, _, _, _ =>
      .unmeasurableByInterface

/-- 完整测量流程必落在“量”的 measurement 内侧。 -/
theorem complete_ce_maps_to_liang_measurable (m : CeSkeleton) :
    CompleteCe m → MeasurableByInterface (ceAsLiangMeasurement m) := by
  intro h
  cases m with
  | mk o i p c r d =>
      rcases h with ⟨ho, hi, hp, hc, hr, hd⟩
      simp [Observable] at ho
      simp [Interfaced] at hi
      simp [ProtocolSpecified] at hp
      simp [Calibrated] at hc
      simp [Readable] at hr
      simp [Recorded] at hd
      subst o
      subst i
      subst p
      subst c
      subst r
      subst d
      rfl

/-- 任一缺失轴都会把本 skeleton 落到不可由接口测得的一侧。 -/
theorem incomplete_ce_maps_to_liang_unmeasurable
    (m : CeSkeleton)
    (h : ¬ CompleteCe m) :
    ceAsLiangMeasurement m = .unmeasurableByInterface := by
  cases m with
  | mk o i p c r d =>
      cases o <;> cases i <;> cases p <;> cases c <;> cases r <;> cases d <;>
        simp [ceAsLiangMeasurement, CompleteCe, Observable, Interfaced,
          ProtocolSpecified, Calibrated, Readable, Recorded] at h ⊢

/-! ## § 9 Measurement is not inference -/

/-- 测量产物与推断产物分层：测止于记录，推断另起。 -/
inductive CeProduct : Type
  | measurementRecord
  | inferenceClaim
  deriving Repr, DecidableEq

/-- 测量记录不是推断命题。 -/
theorem measurement_record_ne_inference_claim :
    CeProduct.measurementRecord ≠ CeProduct.inferenceClaim := by
  intro h
  cases h

/-- 量子时空的 typed collapse outcome 已经是“测”的读数侧。 -/
def collapseOutcomeReadout (_o : CollapseOutcome) : ReadoutRegion :=
  .readable

/-- 量子时空的 typed collapse outcome 已经可读。 -/
theorem collapse_outcome_is_readable (o : CollapseOutcome) :
    Readable (collapseOutcomeReadout o) := by
  rfl

/-! ## § 10 Public summary -/

/-- 公开摘要：
    (1) 六条“测”轴两两不同；
    (2) 可观、可接、有法、已校、可读、可记六组边界均穷尽且互斥；
    (3) 完整测量流程落到“量”的 measurement 内侧；
    (4) 缺失轴的流程落到“量”的 measurement 外侧；
    (5) 测量记录不是推断命题；
    (6) typed collapse outcome 已经可读。 -/
theorem ce_boundary_summary :
    (CeAxis.observability ≠ CeAxis.interface
      ∧ CeAxis.observability ≠ CeAxis.protocol
      ∧ CeAxis.observability ≠ CeAxis.calibration
      ∧ CeAxis.observability ≠ CeAxis.readout
      ∧ CeAxis.observability ≠ CeAxis.record
      ∧ CeAxis.interface ≠ CeAxis.protocol
      ∧ CeAxis.interface ≠ CeAxis.calibration
      ∧ CeAxis.interface ≠ CeAxis.readout
      ∧ CeAxis.interface ≠ CeAxis.record
      ∧ CeAxis.protocol ≠ CeAxis.calibration
      ∧ CeAxis.protocol ≠ CeAxis.readout
      ∧ CeAxis.protocol ≠ CeAxis.record
      ∧ CeAxis.calibration ≠ CeAxis.readout
      ∧ CeAxis.calibration ≠ CeAxis.record
      ∧ CeAxis.readout ≠ CeAxis.record)
    ∧ (∀ r : ObservabilityRegion, Observable r ∨ Unobservable r)
    ∧ (∀ r : ObservabilityRegion, Observable r → ¬ Unobservable r)
    ∧ (∀ r : ObservabilityRegion, Unobservable r → ¬ Observable r)
    ∧ (∀ r : InterfaceRegion, Interfaced r ∨ Uninterfaced r)
    ∧ (∀ r : InterfaceRegion, Interfaced r → ¬ Uninterfaced r)
    ∧ (∀ r : InterfaceRegion, Uninterfaced r → ¬ Interfaced r)
    ∧ (∀ r : ProtocolRegion, ProtocolSpecified r ∨ ProtocolUnspecified r)
    ∧ (∀ r : ProtocolRegion, ProtocolSpecified r → ¬ ProtocolUnspecified r)
    ∧ (∀ r : ProtocolRegion, ProtocolUnspecified r → ¬ ProtocolSpecified r)
    ∧ (∀ r : CalibrationRegion, Calibrated r ∨ Uncalibrated r)
    ∧ (∀ r : CalibrationRegion, Calibrated r → ¬ Uncalibrated r)
    ∧ (∀ r : CalibrationRegion, Uncalibrated r → ¬ Calibrated r)
    ∧ (∀ r : ReadoutRegion, Readable r ∨ Unreadable r)
    ∧ (∀ r : ReadoutRegion, Readable r → ¬ Unreadable r)
    ∧ (∀ r : ReadoutRegion, Unreadable r → ¬ Readable r)
    ∧ (∀ r : RecordRegion, Recorded r ∨ Unrecorded r)
    ∧ (∀ r : RecordRegion, Recorded r → ¬ Unrecorded r)
    ∧ (∀ r : RecordRegion, Unrecorded r → ¬ Recorded r)
    ∧ (∀ m : CeSkeleton, CompleteCe m → MeasurableByInterface (ceAsLiangMeasurement m))
    ∧ (∀ m : CeSkeleton, ¬ CompleteCe m → ceAsLiangMeasurement m = .unmeasurableByInterface)
    ∧ CeProduct.measurementRecord ≠ CeProduct.inferenceClaim
    ∧ (∀ o : CollapseOutcome, Readable (collapseOutcomeReadout o)) :=
  ⟨ce_axes_pairwise_distinct,
   observability_region_exhaustive,
   observable_not_unobservable,
   unobservable_not_observable,
   interface_region_exhaustive,
   interfaced_not_uninterfaced,
   uninterfaced_not_interfaced,
   protocol_region_exhaustive,
   specified_not_unspecified,
   unspecified_not_specified,
   calibration_region_exhaustive,
   calibrated_not_uncalibrated,
   uncalibrated_not_calibrated,
   readout_region_exhaustive,
   readable_not_unreadable,
   unreadable_not_readable,
   record_region_exhaustive,
   recorded_not_unrecorded,
   unrecorded_not_recorded,
   complete_ce_maps_to_liang_measurable,
   incomplete_ce_maps_to_liang_unmeasurable,
   measurement_record_ne_inference_claim,
   collapse_outcome_is_readable⟩

end SSBX.Foundation.Modern.CeBoundary
