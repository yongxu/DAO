/-
# LiangBoundary — 量之边界 / 数量 / 度量 / 测度 / 测量 / 量词

Companion: `义理/边界/量的边界 · 数测度.md`

本文件形式化一个薄的“量”边界：

1. “量”不是单轴词：数量、度量、测度、测量、量词是五条不同接口；
2. 每条接口在本 typed skeleton 中都有内外两侧，且穷尽互斥；
3. `KnowableBoundary.lean` deferred 的可测 / 不可测不由 `KeBoundary.lean`
   处理，而由本文件承接；
4. Kolmogorov 概率、computational-basis Born rule、以及量子时空测量输出
   只作为已有 Lean 锚点接入，不在此处冒充完整物理测量理论。
-/
import SSBX.Foundation.Modern.KeBoundary
import SSBX.Foundation.Modern.Kolmogorov
import SSBX.Foundation.Modern.Quantum
import SSBX.Foundation.Modern.QuantumSpacetime

namespace SSBX.Foundation.Modern.LiangBoundary

open MeasureTheory
open SSBX.Foundation.Modern.KnowableBoundary
open SSBX.Foundation.Modern.KeBoundary
open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumSpacetime

/-! ## § 1 Axes of liang-boundaries -/

/-- “量”的五条轴：数量、度量、测度、测量、量词。 -/
inductive LiangAxis : Type
  | quantity
  | metric
  | measureTheory
  | measurement
  | quantifier
  deriving Repr, DecidableEq

/-- 五条“量”轴两两不同的核心见证。 -/
theorem liang_axes_pairwise_distinct :
    LiangAxis.quantity ≠ LiangAxis.metric
    ∧ LiangAxis.quantity ≠ LiangAxis.measureTheory
    ∧ LiangAxis.quantity ≠ LiangAxis.measurement
    ∧ LiangAxis.quantity ≠ LiangAxis.quantifier
    ∧ LiangAxis.metric ≠ LiangAxis.measureTheory
    ∧ LiangAxis.metric ≠ LiangAxis.measurement
    ∧ LiangAxis.metric ≠ LiangAxis.quantifier
    ∧ LiangAxis.measureTheory ≠ LiangAxis.measurement
    ∧ LiangAxis.measureTheory ≠ LiangAxis.quantifier
    ∧ LiangAxis.measurement ≠ LiangAxis.quantifier := by
  simp

/-! ## § 2 数量 / 非数量 -/

/-- 数量边界：是否已经成为一个 value-bearing quantity。 -/
inductive QuantityRegion : Type
  | quantitative
  | nonquantitative
  deriving Repr, DecidableEq

def Quantitative (r : QuantityRegion) : Prop :=
  r = .quantitative

def Nonquantitative (r : QuantityRegion) : Prop :=
  r = .nonquantitative

theorem quantity_region_exhaustive (r : QuantityRegion) :
    Quantitative r ∨ Nonquantitative r := by
  cases r <;> simp [Quantitative, Nonquantitative]

theorem quantitative_not_nonquantitative (r : QuantityRegion) :
    Quantitative r → ¬ Nonquantitative r := by
  intro hq hn
  unfold Quantitative at hq
  unfold Nonquantitative at hn
  rw [hq] at hn
  cases hn

theorem nonquantitative_not_quantitative (r : QuantityRegion) :
    Nonquantitative r → ¬ Quantitative r := by
  intro hn hq
  exact quantitative_not_nonquantitative r hq hn

/-- 数量边界完备：数量 / 非数量穷尽，且两向互斥。 -/
theorem quantity_boundary_complete :
    (∀ r : QuantityRegion, Quantitative r ∨ Nonquantitative r)
    ∧ (∀ r : QuantityRegion, Quantitative r → ¬ Nonquantitative r)
    ∧ (∀ r : QuantityRegion, Nonquantitative r → ¬ Quantitative r) :=
  ⟨quantity_region_exhaustive,
   quantitative_not_nonquantitative,
   nonquantitative_not_quantitative⟩

/-! ## § 3 度量 / 非度量 -/

/-- 度量边界：是否进入尺度、距离、大小比较接口。 -/
inductive MetricRegion : Type
  | metricable
  | unmetricable
  deriving Repr, DecidableEq

def Metricable (r : MetricRegion) : Prop :=
  r = .metricable

def Unmetricable (r : MetricRegion) : Prop :=
  r = .unmetricable

theorem metric_region_exhaustive (r : MetricRegion) :
    Metricable r ∨ Unmetricable r := by
  cases r <;> simp [Metricable, Unmetricable]

theorem metricable_not_unmetricable (r : MetricRegion) :
    Metricable r → ¬ Unmetricable r := by
  intro hm interlace
  unfold Metricable at hm
  unfold Unmetricable at interlace
  rw [hm] at interlace
  cases interlace

theorem unmetricable_not_metricable (r : MetricRegion) :
    Unmetricable r → ¬ Metricable r := by
  intro interlace hm
  exact metricable_not_unmetricable r hm interlace

/-- 度量边界完备：可度量 / 不可度量穷尽，且两向互斥。 -/
theorem metric_boundary_complete :
    (∀ r : MetricRegion, Metricable r ∨ Unmetricable r)
    ∧ (∀ r : MetricRegion, Metricable r → ¬ Unmetricable r)
    ∧ (∀ r : MetricRegion, Unmetricable r → ¬ Metricable r) :=
  ⟨metric_region_exhaustive,
   metricable_not_unmetricable,
   unmetricable_not_metricable⟩

/-! ## § 4 测度可测 / 测度不可测 -/

/-- 测度论边界：事件是否在当前 σ-代数 / measurable interface 内。 -/
inductive MeasureRegion : Type
  | sigmaMeasurable
  | sigmaUnmeasurable
  deriving Repr, DecidableEq

def SigmaMeasurable (r : MeasureRegion) : Prop :=
  r = .sigmaMeasurable

def SigmaUnmeasurable (r : MeasureRegion) : Prop :=
  r = .sigmaUnmeasurable

theorem measure_region_exhaustive (r : MeasureRegion) :
    SigmaMeasurable r ∨ SigmaUnmeasurable r := by
  cases r <;> simp [SigmaMeasurable, SigmaUnmeasurable]

theorem sigma_measurable_not_unmeasurable (r : MeasureRegion) :
    SigmaMeasurable r → ¬ SigmaUnmeasurable r := by
  intro hm interlace
  unfold SigmaMeasurable at hm
  unfold SigmaUnmeasurable at interlace
  rw [hm] at interlace
  cases interlace

theorem sigma_unmeasurable_not_measurable (r : MeasureRegion) :
    SigmaUnmeasurable r → ¬ SigmaMeasurable r := by
  intro interlace hm
  exact sigma_measurable_not_unmeasurable r hm interlace

/-- 测度论边界完备：σ-可测 / σ-不可测穷尽，且两向互斥。 -/
theorem measure_theoretic_boundary_complete :
    (∀ r : MeasureRegion, SigmaMeasurable r ∨ SigmaUnmeasurable r)
    ∧ (∀ r : MeasureRegion, SigmaMeasurable r → ¬ SigmaUnmeasurable r)
    ∧ (∀ r : MeasureRegion, SigmaUnmeasurable r → ¬ SigmaMeasurable r) :=
  ⟨measure_region_exhaustive,
   sigma_measurable_not_unmeasurable,
   sigma_unmeasurable_not_measurable⟩

/-! ## § 5 测量可读 / 测量不可读 -/

/-- 测量边界：是否能经观测 / 测量接口落成可读结果。 -/
inductive MeasurementRegion : Type
  | measurableByInterface
  | unmeasurableByInterface
  deriving Repr, DecidableEq

def MeasurableByInterface (r : MeasurementRegion) : Prop :=
  r = .measurableByInterface

def UnmeasurableByInterface (r : MeasurementRegion) : Prop :=
  r = .unmeasurableByInterface

theorem measurement_region_exhaustive (r : MeasurementRegion) :
    MeasurableByInterface r ∨ UnmeasurableByInterface r := by
  cases r <;> simp [MeasurableByInterface, UnmeasurableByInterface]

theorem measurable_by_interface_not_unmeasurable (r : MeasurementRegion) :
    MeasurableByInterface r → ¬ UnmeasurableByInterface r := by
  intro hm interlace
  unfold MeasurableByInterface at hm
  unfold UnmeasurableByInterface at interlace
  rw [hm] at interlace
  cases interlace

theorem unmeasurable_by_interface_not_measurable (r : MeasurementRegion) :
    UnmeasurableByInterface r → ¬ MeasurableByInterface r := by
  intro interlace hm
  exact measurable_by_interface_not_unmeasurable r hm interlace

/-- 测量边界完备：可由接口测得 / 不可由接口测得穷尽，且两向互斥。 -/
theorem measurement_boundary_complete :
    (∀ r : MeasurementRegion, MeasurableByInterface r ∨ UnmeasurableByInterface r)
    ∧ (∀ r : MeasurementRegion, MeasurableByInterface r → ¬ UnmeasurableByInterface r)
    ∧ (∀ r : MeasurementRegion, UnmeasurableByInterface r → ¬ MeasurableByInterface r) :=
  ⟨measurement_region_exhaustive,
   measurable_by_interface_not_unmeasurable,
   unmeasurable_by_interface_not_measurable⟩

/-! ## § 6 量词有域 / 无域 -/

/-- 量词边界：∀ / ∃ 等量词是否有明确论域。 -/
inductive QuantifierRegion : Type
  | scoped
  | unscoped
  deriving Repr, DecidableEq

def Scoped (r : QuantifierRegion) : Prop :=
  r = .scoped

def Unscoped (r : QuantifierRegion) : Prop :=
  r = .unscoped

theorem quantifier_region_exhaustive (r : QuantifierRegion) :
    Scoped r ∨ Unscoped r := by
  cases r <;> simp [Scoped, Unscoped]

theorem scoped_not_unscoped (r : QuantifierRegion) :
    Scoped r → ¬ Unscoped r := by
  intro hs interlace
  unfold Scoped at hs
  unfold Unscoped at interlace
  rw [hs] at interlace
  cases interlace

theorem unscoped_not_scoped (r : QuantifierRegion) :
    Unscoped r → ¬ Scoped r := by
  intro interlace hs
  exact scoped_not_unscoped r hs interlace

/-- 量词边界完备：有域 / 无域穷尽，且两向互斥。 -/
theorem quantifier_boundary_complete :
    (∀ r : QuantifierRegion, Scoped r ∨ Unscoped r)
    ∧ (∀ r : QuantifierRegion, Scoped r → ¬ Unscoped r)
    ∧ (∀ r : QuantifierRegion, Unscoped r → ¬ Scoped r) :=
  ⟨quantifier_region_exhaustive,
   scoped_not_unscoped,
   unscoped_not_scoped⟩

/-! ## § 7 Handoffs and existing mathematical anchors -/

/-- `KnowableBoundary` deferred 的可测 / 不可测由本文件承接。 -/
def handledInLiangBoundary : DeferredKeBoundary → Bool
  | .measurable
  | .unmeasurable => true
  | .feelable
  | .unfeelable
  | .actionable
  | .unactionable
  | .provable
  | .unprovable
  | .nameable
  | .unnameable => false

/-- “量”边界只承接 deferred 的可测 / 不可测。 -/
theorem handled_in_liang_iff_measurable (b : DeferredKeBoundary) :
    handledInLiangBoundary b = true ↔ b = .measurable ∨ b = .unmeasurable := by
  cases b <;> simp [handledInLiangBoundary]

/-- 可测 / 不可测：Knowable 不处理，Ke 不处理，Liang 承接。 -/
theorem measurable_deferred_boundaries_handled_in_liang :
    handledHere .measurable = false ∧ handledInKeBoundary .measurable = false
    ∧ handledInLiangBoundary .measurable = true
    ∧ handledHere .unmeasurable = false ∧ handledInKeBoundary .unmeasurable = false
    ∧ handledInLiangBoundary .unmeasurable = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Kolmogorov 概率测度的归一锚点：总测度为 1。 -/
theorem probability_measure_normalizes
    (α : Type*) [MeasurableSpace α] (P : ProbabilityMeasure α) :
    (P : Measure α) Set.univ = 1 :=
  SSBX.Foundation.Modern.Kolmogorov.prob_total_one α P

/-- computational-basis Born rule 的“量”读法：二值权重非负且归一。 -/
theorem born_rule_gives_normalized_measurement_weights
    (ψ : Qubit) (hψ : computationalBasisNormalized ψ) :
    0 ≤ bornProb0 ψ ∧ 0 ≤ bornProb1 ψ
      ∧ bornProb0 ψ + bornProb1 ψ = 1 :=
  computational_basis_born_rule ψ hψ

/-- 量子时空文档中的 typed collapse outcome，进入“量”的测量接口内侧。 -/
def collapseOutcomeMeasurementRegion (_o : CollapseOutcome) : MeasurementRegion :=
  .measurableByInterface

/-- 已形成 `CollapseOutcome` 的结果，按定义已是测量接口可读。 -/
theorem collapse_outcome_is_measurable_by_interface (o : CollapseOutcome) :
    MeasurableByInterface (collapseOutcomeMeasurementRegion o) := by
  rfl

/-- 任意 typed measurement 的输出都落在“量”的测量接口内侧。 -/
theorem every_typed_measurement_lands_in_liang_measurement_region
    (m : Measurement) (s : PreMeasurement) :
    MeasurableByInterface (collapseOutcomeMeasurementRegion (m s)) := by
  rfl

/-- 已有量子时空锚点：测量输出没有第四类。 -/
theorem collapse_output_has_no_fourth_liang_class (o : CollapseOutcome) :
    withinMeasurementLimit o :=
  collapse_outcome_exhaustive o

/-! ## § 8 Public summary -/

/-- 公开摘要：
    (1) “量”的五条轴两两不同；
    (2) 数量、度量、测度、测量、量词五组边界均穷尽且互斥；
    (3) 可测 / 不可测由 “量” 边界承接；
    (4) 概率测度总量为 1；
    (5) computational-basis Born rule 给二值非负归一权重；
    (6) typed measurement output 进入测量接口内侧且没有第四类。 -/
theorem liang_boundary_summary :
    (LiangAxis.quantity ≠ LiangAxis.metric
      ∧ LiangAxis.quantity ≠ LiangAxis.measureTheory
      ∧ LiangAxis.quantity ≠ LiangAxis.measurement
      ∧ LiangAxis.quantity ≠ LiangAxis.quantifier
      ∧ LiangAxis.metric ≠ LiangAxis.measureTheory
      ∧ LiangAxis.metric ≠ LiangAxis.measurement
      ∧ LiangAxis.metric ≠ LiangAxis.quantifier
      ∧ LiangAxis.measureTheory ≠ LiangAxis.measurement
      ∧ LiangAxis.measureTheory ≠ LiangAxis.quantifier
      ∧ LiangAxis.measurement ≠ LiangAxis.quantifier)
    ∧ (∀ r : QuantityRegion, Quantitative r ∨ Nonquantitative r)
    ∧ (∀ r : QuantityRegion, Quantitative r → ¬ Nonquantitative r)
    ∧ (∀ r : QuantityRegion, Nonquantitative r → ¬ Quantitative r)
    ∧ (∀ r : MetricRegion, Metricable r ∨ Unmetricable r)
    ∧ (∀ r : MetricRegion, Metricable r → ¬ Unmetricable r)
    ∧ (∀ r : MetricRegion, Unmetricable r → ¬ Metricable r)
    ∧ (∀ r : MeasureRegion, SigmaMeasurable r ∨ SigmaUnmeasurable r)
    ∧ (∀ r : MeasureRegion, SigmaMeasurable r → ¬ SigmaUnmeasurable r)
    ∧ (∀ r : MeasureRegion, SigmaUnmeasurable r → ¬ SigmaMeasurable r)
    ∧ (∀ r : MeasurementRegion, MeasurableByInterface r ∨ UnmeasurableByInterface r)
    ∧ (∀ r : MeasurementRegion, MeasurableByInterface r → ¬ UnmeasurableByInterface r)
    ∧ (∀ r : MeasurementRegion, UnmeasurableByInterface r → ¬ MeasurableByInterface r)
    ∧ (∀ r : QuantifierRegion, Scoped r ∨ Unscoped r)
    ∧ (∀ r : QuantifierRegion, Scoped r → ¬ Unscoped r)
    ∧ (∀ r : QuantifierRegion, Unscoped r → ¬ Scoped r)
    ∧ (∀ b : DeferredKeBoundary,
        handledInLiangBoundary b = true ↔ b = .measurable ∨ b = .unmeasurable)
    ∧ (handledHere .measurable = false ∧ handledInKeBoundary .measurable = false
      ∧ handledInLiangBoundary .measurable = true
      ∧ handledHere .unmeasurable = false ∧ handledInKeBoundary .unmeasurable = false
      ∧ handledInLiangBoundary .unmeasurable = true)
    ∧ (∀ (α : Type*) [MeasurableSpace α] (P : ProbabilityMeasure α),
        (P : Measure α) Set.univ = 1)
    ∧ (∀ ψ : Qubit, computationalBasisNormalized ψ →
        0 ≤ bornProb0 ψ ∧ 0 ≤ bornProb1 ψ
          ∧ bornProb0 ψ + bornProb1 ψ = 1)
    ∧ (∀ (m : Measurement) (s : PreMeasurement),
        MeasurableByInterface (collapseOutcomeMeasurementRegion (m s)))
    ∧ (∀ o : CollapseOutcome, withinMeasurementLimit o) :=
  ⟨liang_axes_pairwise_distinct,
   quantity_region_exhaustive,
   quantitative_not_nonquantitative,
   nonquantitative_not_quantitative,
   metric_region_exhaustive,
   metricable_not_unmetricable,
   unmetricable_not_metricable,
   measure_region_exhaustive,
   sigma_measurable_not_unmeasurable,
   sigma_unmeasurable_not_measurable,
   measurement_region_exhaustive,
   measurable_by_interface_not_unmeasurable,
   unmeasurable_by_interface_not_measurable,
   quantifier_region_exhaustive,
   scoped_not_unscoped,
   unscoped_not_scoped,
   handled_in_liang_iff_measurable,
   measurable_deferred_boundaries_handled_in_liang,
   probability_measure_normalizes,
   born_rule_gives_normalized_measurement_weights,
   every_typed_measurement_lands_in_liang_measurement_region,
   collapse_output_has_no_fourth_liang_class⟩

end SSBX.Foundation.Modern.LiangBoundary
