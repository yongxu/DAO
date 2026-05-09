/-
# QuantumRelativitySumOverMiddleChannelBridge -- S15 sum-over-middle boundary

Companion:
`义理/sum-over-middle通道组合候选 · Markov桥S15.md`

S15 adds the finite "sum over middle states" composition candidate missing from
S13/S14:

1. the composed endpoint amplitude is a finite sum of
   `left(a,b) * right(b,c)` over an explicit middle-state list;
2. nonzero composed amplitude implies a two-step witness through at least one
   listed middle state;
3. the concrete `prepared -> evolved -> measured` process has a nonzero
   two-step composed amplitude even though `prepared -> measured` is not a
   one-step transition.

This is not a full path integral, a unitary/CPTP law, or an empirical channel
law.  It deliberately records that sum-over-middle composition targets a
two-step reachability boundary rather than the current one-step
`QuantumChannelSkeleton`.
-/
import Mathlib.Tactic.NormNum
import SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge

namespace SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite sum support lemma -/

/-- A finite complex list with nonzero sum has at least one nonzero entry. -/
theorem list_sum_ne_zero_has_nonzero_entry (xs : List ℂ) :
    xs.sum ≠ 0 -> ∃ x : ℂ, x ∈ xs ∧ x ≠ 0 := by
  intro hsum
  induction xs with
  | nil =>
      simp at hsum
  | cons x xs ih =>
      by_cases hx : x = 0
      · have htail : xs.sum ≠ 0 := by
          intro hxs
          exact hsum (by simp [hx, hxs])
        rcases ih htail with ⟨y, hy, hyne⟩
        exact ⟨y, by simp [hy], hyne⟩
      · exact ⟨x, by simp, hx⟩

/-! ## § 2 Sum-over-middle composition -/

/-- Endpoint amplitude obtained by summing products over displayed middle states. -/
def sumOverMiddleChannelAmplitude {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P)
    (a c : P.State) : ℂ :=
  (middle.map fun b =>
    left.amplitudeLayer.amplitude a b * right.amplitudeLayer.amplitude b c).sum

/-- Two-step reachability through a displayed finite middle-state list. -/
def TwoStepReachableViaList {P : FiniteProcess}
    (middle : List P.State) (a c : P.State) : Prop :=
  ∃ b : P.State, b ∈ middle ∧ P.step a b ∧ P.step b c

/--
If the sum-over-middle endpoint amplitude is nonzero, at least one listed
middle state carries nonzero left and right amplitudes; support-respecting
channels then give a two-step process witness.
-/
theorem sumOverMiddle_support_implies_two_step
    {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P)
    {a c : P.State} :
    sumOverMiddleChannelAmplitude middle left right a c ≠ 0 ->
      TwoStepReachableViaList middle a c := by
  intro hsum
  rcases list_sum_ne_zero_has_nonzero_entry
      (middle.map fun b =>
        left.amplitudeLayer.amplitude a b * right.amplitudeLayer.amplitude b c)
      (by simpa [sumOverMiddleChannelAmplitude] using hsum) with
    ⟨x, hxmem, hxne⟩
  rcases List.mem_map.mp hxmem with ⟨b, hbmem, hbeq⟩
  have hprod :
      left.amplitudeLayer.amplitude a b * right.amplitudeLayer.amplitude b c ≠ 0 := by
    rw [hbeq]
    exact hxne
  have hleft : left.amplitudeLayer.amplitude a b ≠ 0 := by
    intro hzero
    exact hprod (by simp [hzero])
  have hright : right.amplitudeLayer.amplitude b c ≠ 0 := by
    intro hzero
    exact hprod (by simp [hzero])
  exact
    ⟨ b
    , hbmem
    , left.amplitudeLayer.amplitude_support_implies_step a b hleft
    , right.amplitudeLayer.amplitude_support_implies_step b c hright
    ⟩

/--
A composition boundary for sum-over-middle amplitude.

It is not a `QuantumChannelSkeleton P`, because its support naturally lands in
two-step reachability rather than one-step `P.step`.
-/
structure SumOverMiddleChannelComposition {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P) where
  amplitude : P.State -> P.State -> ℂ
  amplitude_boundary :
    ∀ a c : P.State,
      amplitude a c = sumOverMiddleChannelAmplitude middle left right a c
  support_implies_two_step :
    ∀ a c : P.State,
      amplitude a c ≠ 0 -> TwoStepReachableViaList middle a c

/-- Canonical sum-over-middle composition boundary for two channel candidates. -/
def sumOverMiddleChannelComposition {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P) :
    SumOverMiddleChannelComposition middle left right where
  amplitude := sumOverMiddleChannelAmplitude middle left right
  amplitude_boundary := by
    intro _a _c
    rfl
  support_implies_two_step := by
    intro _a _c h
    exact sumOverMiddle_support_implies_two_step middle left right h

/-- The canonical composition boundary computes by the finite middle sum. -/
theorem sumOverMiddleChannelComposition_boundary
    {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P)
    (a c : P.State) :
    (sumOverMiddleChannelComposition middle left right).amplitude a c =
      sumOverMiddleChannelAmplitude middle left right a c :=
  rfl

/-- The canonical composition boundary maps nonzero support to two-step reachability. -/
theorem sumOverMiddleChannelComposition_support
    {P : FiniteProcess}
    (middle : List P.State) (left right : QuantumChannelSkeleton P)
    {a c : P.State} :
    (sumOverMiddleChannelComposition middle left right).amplitude a c ≠ 0 ->
      TwoStepReachableViaList middle a c :=
  (sumOverMiddleChannelComposition middle left right).support_implies_two_step a c

/-- Closed boundary for finite sum-over-middle channel composition. -/
def SumOverMiddleChannelBoundaryClosed : Prop :=
  ∀ {P : FiniteProcess} (middle : List P.State)
      (left right : QuantumChannelSkeleton P),
    ∃ C : SumOverMiddleChannelComposition middle left right,
      (∀ a c : P.State,
        C.amplitude a c = sumOverMiddleChannelAmplitude middle left right a c)
        ∧ (∀ a c : P.State,
          C.amplitude a c ≠ 0 -> TwoStepReachableViaList middle a c)

theorem sum_over_middle_channel_boundary_closed :
    SumOverMiddleChannelBoundaryClosed := by
  intro _P middle left right
  refine ⟨sumOverMiddleChannelComposition middle left right, ?_, ?_⟩
  · intro _a _c
    rfl
  · intro a c h
    exact sumOverMiddleChannelComposition_support middle left right h

/-! ## § 3 Concrete two-step witness -/

/-- A nonzero amplitude candidate on the two concrete one-step edges. -/
def concreteStepAmplitude : ConcreteState -> ConcreteState -> ℂ
  | .prepared, .evolved => 1
  | .evolved, .measured => 1
  | _, _ => 0

/-- Concrete nonzero one-step amplitude skeleton. -/
def concreteStepAmplitudeSkeleton : QuantumAmplitudeSkeleton concreteProcess where
  amplitude := concreteStepAmplitude
  amplitude_support_implies_step := by
    intro a b h
    unfold QuantumAmplitudeSupport at h
    cases a <;> cases b <;>
      simp [concreteStepAmplitude, concreteProcess, ConcreteState.step] at h ⊢

/-- Concrete channel skeleton whose amplitudes are nonzero on the two process edges. -/
def concreteStepQuantumChannelSkeleton : QuantumChannelSkeleton concreteProcess where
  amplitudeLayer := concreteStepAmplitudeSkeleton
  classicalBoundary := concreteFiniteProbabilityKernel
  amplitude_support_refines_classical := by
    intro a b h
    unfold QuantumAmplitudeSupport at h
    cases a <;> cases b <;>
      simp [concreteStepAmplitudeSkeleton, concreteStepAmplitude,
        concreteFiniteProbabilityKernel, ConcreteState.step] at h ⊢

/-- The prepared-to-measured sum over the evolved middle state has amplitude `1`. -/
theorem concrete_sumOverMiddle_prepared_measured_amplitude :
    sumOverMiddleChannelAmplitude [ConcreteState.evolved]
      concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
      ConcreteState.prepared ConcreteState.measured = 1 := by
  norm_num [sumOverMiddleChannelAmplitude, concreteStepQuantumChannelSkeleton,
    concreteStepAmplitudeSkeleton, concreteStepAmplitude]

/-- Prepared-to-measured is not a concrete one-step transition. -/
theorem concrete_prepared_measured_not_one_step :
    ¬ concreteProcess.step ConcreteState.prepared ConcreteState.measured := by
  simp [concreteProcess, ConcreteState.step]

/-- The nonzero prepared-to-measured composed amplitude gives a two-step witness. -/
theorem concrete_sumOverMiddle_prepared_measured_two_step :
    TwoStepReachableViaList (P := concreteProcess) [ConcreteState.evolved]
      ConcreteState.prepared ConcreteState.measured := by
  exact sumOverMiddle_support_implies_two_step [ConcreteState.evolved]
    concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
    (by
      rw [concrete_sumOverMiddle_prepared_measured_amplitude]
      norm_num)

end SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
