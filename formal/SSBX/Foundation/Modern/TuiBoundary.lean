/-
# TuiBoundary — 推之边界 / 前提规则结论

Companion: `义理/边界/推的边界 · 前规则结.md`

本文件形式化一个薄的“推”边界：

1. “推”不是“测”：测止于记录，推从前提与规则得结论；
2. “推”不是“量”：推可以使用量，但产物是 inference claim；
3. “推”不是“感”：感可以供给材料，但不等于推导；
4. 完整推理流程由前提、规则、推导、结论、担保五轴构成。
-/
import SSBX.Foundation.Modern.CeBoundary
import SSBX.Foundation.Modern.NaturalDeduction

namespace SSBX.Foundation.Modern.TuiBoundary

open SSBX.Foundation.Modern.CeBoundary

/-! ## § 1 Axes of tui-boundaries -/

inductive TuiAxis : Type
  | premise
  | rule
  | derivation
  | conclusion
  | warrant
  deriving Repr, DecidableEq

theorem tui_axes_pairwise_distinct :
    TuiAxis.premise ≠ TuiAxis.rule
    ∧ TuiAxis.premise ≠ TuiAxis.derivation
    ∧ TuiAxis.premise ≠ TuiAxis.conclusion
    ∧ TuiAxis.premise ≠ TuiAxis.warrant
    ∧ TuiAxis.rule ≠ TuiAxis.derivation
    ∧ TuiAxis.rule ≠ TuiAxis.conclusion
    ∧ TuiAxis.rule ≠ TuiAxis.warrant
    ∧ TuiAxis.derivation ≠ TuiAxis.conclusion
    ∧ TuiAxis.derivation ≠ TuiAxis.warrant
    ∧ TuiAxis.conclusion ≠ TuiAxis.warrant := by
  simp

/-! ## § 2 前提有 / 前提缺 -/

inductive PremiseRegion : Type
  | available
  | missing
  deriving Repr, DecidableEq

def PremiseAvailable (r : PremiseRegion) : Prop := r = .available
def PremiseMissing (r : PremiseRegion) : Prop := r = .missing

theorem premise_region_exhaustive (r : PremiseRegion) :
    PremiseAvailable r ∨ PremiseMissing r := by
  cases r <;> simp [PremiseAvailable, PremiseMissing]

theorem premise_available_not_missing (r : PremiseRegion) :
    PremiseAvailable r → ¬ PremiseMissing r := by
  intro ha hm
  unfold PremiseAvailable at ha
  unfold PremiseMissing at hm
  rw [ha] at hm
  cases hm

theorem premise_missing_not_available (r : PremiseRegion) :
    PremiseMissing r → ¬ PremiseAvailable r := by
  intro hm ha
  exact premise_available_not_missing r ha hm

theorem premise_boundary_complete :
    (∀ r : PremiseRegion, PremiseAvailable r ∨ PremiseMissing r)
    ∧ (∀ r : PremiseRegion, PremiseAvailable r → ¬ PremiseMissing r)
    ∧ (∀ r : PremiseRegion, PremiseMissing r → ¬ PremiseAvailable r) :=
  ⟨premise_region_exhaustive,
   premise_available_not_missing,
   premise_missing_not_available⟩

/-! ## § 3 规则有 / 规则缺 -/

inductive RuleRegion : Type
  | specified
  | unspecified
  deriving Repr, DecidableEq

def RuleSpecified (r : RuleRegion) : Prop := r = .specified
def RuleUnspecified (r : RuleRegion) : Prop := r = .unspecified

theorem rule_region_exhaustive (r : RuleRegion) :
    RuleSpecified r ∨ RuleUnspecified r := by
  cases r <;> simp [RuleSpecified, RuleUnspecified]

theorem rule_specified_not_unspecified (r : RuleRegion) :
    RuleSpecified r → ¬ RuleUnspecified r := by
  intro hs interlace
  unfold RuleSpecified at hs
  unfold RuleUnspecified at interlace
  rw [hs] at interlace
  cases interlace

theorem rule_unspecified_not_specified (r : RuleRegion) :
    RuleUnspecified r → ¬ RuleSpecified r := by
  intro interlace hs
  exact rule_specified_not_unspecified r hs interlace

theorem rule_boundary_complete :
    (∀ r : RuleRegion, RuleSpecified r ∨ RuleUnspecified r)
    ∧ (∀ r : RuleRegion, RuleSpecified r → ¬ RuleUnspecified r)
    ∧ (∀ r : RuleRegion, RuleUnspecified r → ¬ RuleSpecified r) :=
  ⟨rule_region_exhaustive,
   rule_specified_not_unspecified,
   rule_unspecified_not_specified⟩

/-! ## § 4 已推 / 未推 -/

inductive DerivationRegion : Type
  | derived
  | underived
  deriving Repr, DecidableEq

def Derived (r : DerivationRegion) : Prop := r = .derived
def Underived (r : DerivationRegion) : Prop := r = .underived

theorem derivation_region_exhaustive (r : DerivationRegion) :
    Derived r ∨ Underived r := by
  cases r <;> simp [Derived, Underived]

theorem derived_not_underived (r : DerivationRegion) :
    Derived r → ¬ Underived r := by
  intro hd interlace
  unfold Derived at hd
  unfold Underived at interlace
  rw [hd] at interlace
  cases interlace

theorem underived_not_derived (r : DerivationRegion) :
    Underived r → ¬ Derived r := by
  intro interlace hd
  exact derived_not_underived r hd interlace

theorem derivation_boundary_complete :
    (∀ r : DerivationRegion, Derived r ∨ Underived r)
    ∧ (∀ r : DerivationRegion, Derived r → ¬ Underived r)
    ∧ (∀ r : DerivationRegion, Underived r → ¬ Derived r) :=
  ⟨derivation_region_exhaustive,
   derived_not_underived,
   underived_not_derived⟩

/-! ## § 5 有结论 / 无结论 -/

inductive ConclusionRegion : Type
  | concluded
  | unconcluded
  deriving Repr, DecidableEq

def Concluded (r : ConclusionRegion) : Prop := r = .concluded
def Unconcluded (r : ConclusionRegion) : Prop := r = .unconcluded

theorem conclusion_region_exhaustive (r : ConclusionRegion) :
    Concluded r ∨ Unconcluded r := by
  cases r <;> simp [Concluded, Unconcluded]

theorem concluded_not_unconcluded (r : ConclusionRegion) :
    Concluded r → ¬ Unconcluded r := by
  intro hc interlace
  unfold Concluded at hc
  unfold Unconcluded at interlace
  rw [hc] at interlace
  cases interlace

theorem unconcluded_not_concluded (r : ConclusionRegion) :
    Unconcluded r → ¬ Concluded r := by
  intro interlace hc
  exact concluded_not_unconcluded r hc interlace

theorem conclusion_boundary_complete :
    (∀ r : ConclusionRegion, Concluded r ∨ Unconcluded r)
    ∧ (∀ r : ConclusionRegion, Concluded r → ¬ Unconcluded r)
    ∧ (∀ r : ConclusionRegion, Unconcluded r → ¬ Concluded r) :=
  ⟨conclusion_region_exhaustive,
   concluded_not_unconcluded,
   unconcluded_not_concluded⟩

/-! ## § 6 有担保 / 无担保 -/

inductive WarrantRegion : Type
  | warranted
  | unwarranted
  deriving Repr, DecidableEq

def Warranted (r : WarrantRegion) : Prop := r = .warranted
def Unwarranted (r : WarrantRegion) : Prop := r = .unwarranted

theorem warrant_region_exhaustive (r : WarrantRegion) :
    Warranted r ∨ Unwarranted r := by
  cases r <;> simp [Warranted, Unwarranted]

theorem warranted_not_unwarranted (r : WarrantRegion) :
    Warranted r → ¬ Unwarranted r := by
  intro hw interlace
  unfold Warranted at hw
  unfold Unwarranted at interlace
  rw [hw] at interlace
  cases interlace

theorem unwarranted_not_warranted (r : WarrantRegion) :
    Unwarranted r → ¬ Warranted r := by
  intro interlace hw
  exact warranted_not_unwarranted r hw interlace

theorem warrant_boundary_complete :
    (∀ r : WarrantRegion, Warranted r ∨ Unwarranted r)
    ∧ (∀ r : WarrantRegion, Warranted r → ¬ Unwarranted r)
    ∧ (∀ r : WarrantRegion, Unwarranted r → ¬ Warranted r) :=
  ⟨warrant_region_exhaustive,
   warranted_not_unwarranted,
   unwarranted_not_warranted⟩

/-! ## § 7 Complete inference pipeline -/

structure TuiSkeleton where
  premise : PremiseRegion
  rule : RuleRegion
  derivation : DerivationRegion
  conclusion : ConclusionRegion
  warrant : WarrantRegion
  deriving Repr

def CompleteTui (t : TuiSkeleton) : Prop :=
  PremiseAvailable t.premise
    ∧ RuleSpecified t.rule
    ∧ Derived t.derivation
    ∧ Concluded t.conclusion
    ∧ Warranted t.warrant

def tuiAsCeProduct (t : TuiSkeleton) : CeProduct :=
  match t.premise, t.rule, t.derivation, t.conclusion, t.warrant with
  | .available, .specified, .derived, .concluded, .warranted => .inferenceClaim
  | _, _, _, _, _ => .measurementRecord

theorem complete_tui_yields_inference_claim (t : TuiSkeleton) :
    CompleteTui t → tuiAsCeProduct t = .inferenceClaim := by
  intro h
  cases t with
  | mk p r d c w =>
      rcases h with ⟨hp, hr, hd, hc, hw⟩
      simp [PremiseAvailable] at hp
      simp [RuleSpecified] at hr
      simp [Derived] at hd
      simp [Concluded] at hc
      simp [Warranted] at hw
      subst p
      subst r
      subst d
      subst c
      subst w
      rfl

theorem incomplete_tui_not_inference_claim (t : TuiSkeleton) (h : ¬ CompleteTui t) :
    tuiAsCeProduct t = .measurementRecord := by
  cases t with
  | mk p r d c w =>
      cases p <;> cases r <;> cases d <;> cases c <;> cases w <;>
        simp [tuiAsCeProduct, CompleteTui, PremiseAvailable, RuleSpecified,
          Derived, Concluded, Warranted] at h ⊢

/-- 自然演绎的 Modus Ponens 作为“推”的最小规则锚点。 -/
theorem modus_ponens_anchor {P Q : Prop} (hpq : P → Q) (hp : P) : Q :=
  SSBX.Foundation.Modern.NaturalDeduction.imp_elim hpq hp

/-- 测量记录与推断命题在 `CeBoundary` 中已经被证明不同。 -/
theorem tui_claim_ne_measurement_record :
    CeProduct.inferenceClaim ≠ CeProduct.measurementRecord := by
  intro h
  exact measurement_record_ne_inference_claim h.symm

/-! ## § 8 Public summary -/

theorem tui_boundary_summary :
    (TuiAxis.premise ≠ TuiAxis.rule
      ∧ TuiAxis.premise ≠ TuiAxis.derivation
      ∧ TuiAxis.premise ≠ TuiAxis.conclusion
      ∧ TuiAxis.premise ≠ TuiAxis.warrant
      ∧ TuiAxis.rule ≠ TuiAxis.derivation
      ∧ TuiAxis.rule ≠ TuiAxis.conclusion
      ∧ TuiAxis.rule ≠ TuiAxis.warrant
      ∧ TuiAxis.derivation ≠ TuiAxis.conclusion
      ∧ TuiAxis.derivation ≠ TuiAxis.warrant
      ∧ TuiAxis.conclusion ≠ TuiAxis.warrant)
    ∧ (∀ r : PremiseRegion, PremiseAvailable r ∨ PremiseMissing r)
    ∧ (∀ r : PremiseRegion, PremiseAvailable r → ¬ PremiseMissing r)
    ∧ (∀ r : PremiseRegion, PremiseMissing r → ¬ PremiseAvailable r)
    ∧ (∀ r : RuleRegion, RuleSpecified r ∨ RuleUnspecified r)
    ∧ (∀ r : RuleRegion, RuleSpecified r → ¬ RuleUnspecified r)
    ∧ (∀ r : RuleRegion, RuleUnspecified r → ¬ RuleSpecified r)
    ∧ (∀ r : DerivationRegion, Derived r ∨ Underived r)
    ∧ (∀ r : DerivationRegion, Derived r → ¬ Underived r)
    ∧ (∀ r : DerivationRegion, Underived r → ¬ Derived r)
    ∧ (∀ r : ConclusionRegion, Concluded r ∨ Unconcluded r)
    ∧ (∀ r : ConclusionRegion, Concluded r → ¬ Unconcluded r)
    ∧ (∀ r : ConclusionRegion, Unconcluded r → ¬ Concluded r)
    ∧ (∀ r : WarrantRegion, Warranted r ∨ Unwarranted r)
    ∧ (∀ r : WarrantRegion, Warranted r → ¬ Unwarranted r)
    ∧ (∀ r : WarrantRegion, Unwarranted r → ¬ Warranted r)
    ∧ (∀ t : TuiSkeleton, CompleteTui t → tuiAsCeProduct t = .inferenceClaim)
    ∧ (∀ t : TuiSkeleton, ¬ CompleteTui t → tuiAsCeProduct t = .measurementRecord)
    ∧ CeProduct.inferenceClaim ≠ CeProduct.measurementRecord :=
  ⟨tui_axes_pairwise_distinct,
   premise_region_exhaustive,
   premise_available_not_missing,
   premise_missing_not_available,
   rule_region_exhaustive,
   rule_specified_not_unspecified,
   rule_unspecified_not_specified,
   derivation_region_exhaustive,
   derived_not_underived,
   underived_not_derived,
   conclusion_region_exhaustive,
   concluded_not_unconcluded,
   unconcluded_not_concluded,
   warrant_region_exhaustive,
   warranted_not_unwarranted,
   unwarranted_not_warranted,
   complete_tui_yields_inference_claim,
   incomplete_tui_not_inference_claim,
   tui_claim_ne_measurement_record⟩

end SSBX.Foundation.Modern.TuiBoundary
