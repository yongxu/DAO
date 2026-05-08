/-
# QuantumRelativityNonzeroPathAmplitudeBridge — nonzero path-amplitude witness

Companion:
`义理/非零路径振幅候选 · Markov桥S5b.md`

This module advances the S5 interference candidate by one conservative step:

1. it proves that any nonzero path amplitude in the S5 skeleton is confined to
   a valid path witness;
2. it therefore projects to reachability and `causalBefore`;
3. it gives the concrete three-state bridge a nonzero path-amplitude witness by
   using a validity-indicator amplitude.

This still does not prove a physical phase law, path integral, destructive
interference over actual alternative paths, Born-rule derivation, unitarity,
CPTP channel laws, decoherence, or empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge

namespace SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Nonzero path amplitudes stay inside path/causal boundaries -/

/-- A nonzero path amplitude must lie on a valid path witness. -/
theorem nonzero_path_amplitude_implies_valid {P : FiniteProcess}
    (A : PathAmplitudeSkeleton P) (p : ProcessPath P) :
    A.pathAmplitude p ≠ 0 → p.valid :=
  A.path_support_implies_valid p

/-- A nonzero path amplitude therefore gives reachability of its endpoints. -/
theorem nonzero_path_amplitude_implies_reachable {P : FiniteProcess}
    (A : PathAmplitudeSkeleton P) (p : ProcessPath P) :
    A.pathAmplitude p ≠ 0 → Reachable P p.start p.stop := by
  intro h
  exact path_implies_reachable p
    (nonzero_path_amplitude_implies_valid A p h)

/-- A nonzero path amplitude also has the causal-before reading. -/
theorem nonzero_path_amplitude_implies_causal_before {P : FiniteProcess}
    (A : PathAmplitudeSkeleton P) (p : ProcessPath P) :
    A.pathAmplitude p ≠ 0 →
      causalBefore (P := P) ⟨p.start⟩ ⟨p.stop⟩ :=
  nonzero_path_amplitude_implies_reachable A p

/-! ## § 2 A validity-indicator path-amplitude candidate -/

/--
The validity-indicator path-amplitude candidate.

It assigns amplitude `1` to valid path witnesses and `0` otherwise.  This is a
nonzero candidate interface only.  It is not a physical action, phase law,
unitary dynamics, or path integral.
-/
noncomputable def validPathIndicatorPathAmplitudeSkeleton
    (P : FiniteProcess) (C : QuantumChannelSkeleton P) :
    PathAmplitudeSkeleton P where
  channel := C
  pathAmplitude := by
    classical
    exact fun p => if p.valid then (1 : ℂ) else 0
  path_support_implies_valid := by
    classical
    intro p h
    by_contra hp
    simp [hp] at h
  composed_amplitude := by
    classical
    intro c
    have hcomp : (composeProcessPaths c).valid := composed_path_valid c
    simp [hcomp, c.left_valid, c.right_valid]

/-- Every valid path has nonzero validity-indicator amplitude. -/
theorem valid_path_indicator_nonzero {P : FiniteProcess}
    (C : QuantumChannelSkeleton P) (p : ProcessPath P) :
    p.valid →
      (validPathIndicatorPathAmplitudeSkeleton P C).pathAmplitude p ≠ 0 := by
  classical
  intro hp
  simp [validPathIndicatorPathAmplitudeSkeleton, hp]

/-! ## § 3 Concrete nonzero witness -/

/-- The concrete one-step path from `prepared` to `evolved`. -/
def concretePreparedEvolvedPath : ProcessPath concreteProcess where
  start := ConcreteState.prepared
  stop := ConcreteState.evolved
  valid := concreteProcess.step ConcreteState.prepared ConcreteState.evolved

/-- The concrete one-step path from `evolved` to `measured`. -/
def concreteEvolvedMeasuredPath : ProcessPath concreteProcess where
  start := ConcreteState.evolved
  stop := ConcreteState.measured
  valid := concreteProcess.step ConcreteState.evolved ConcreteState.measured

/-- The two concrete one-step paths compose at `evolved`. -/
def concretePreparedMeasuredComposable :
    ComposableProcessPaths concreteProcess where
  left := concretePreparedEvolvedPath
  right := concreteEvolvedMeasuredPath
  middle_eq := rfl
  left_valid := prepared_to_evolved_step
  right_valid := evolved_to_measured_step

/-- The concrete composed path from `prepared` to `measured`. -/
def concretePreparedMeasuredPath : ProcessPath concreteProcess :=
  composeProcessPaths concretePreparedMeasuredComposable

/-- The concrete bridge with a nonzero validity-indicator path-amplitude candidate. -/
noncomputable def concreteNonzeroPathAmplitudeSkeleton :
    PathAmplitudeSkeleton concreteProcess :=
  validPathIndicatorPathAmplitudeSkeleton
    concreteProcess
    concreteQuantumChannelSkeleton

/-- The concrete composed path is valid. -/
theorem concrete_prepared_measured_path_valid :
    concretePreparedMeasuredPath.valid :=
  composed_path_valid concretePreparedMeasuredComposable

/-- The concrete composed path has nonzero candidate amplitude. -/
theorem concrete_prepared_measured_path_nonzero_amplitude :
    concreteNonzeroPathAmplitudeSkeleton.pathAmplitude
      concretePreparedMeasuredPath ≠ 0 :=
  valid_path_indicator_nonzero
    concreteQuantumChannelSkeleton
    concretePreparedMeasuredPath
    concrete_prepared_measured_path_valid

/-- The concrete nonzero path-amplitude witness gives reachability. -/
theorem concrete_nonzero_path_amplitude_reachable :
    Reachable concreteProcess
      ConcreteState.prepared
      ConcreteState.measured :=
  nonzero_path_amplitude_implies_reachable
    concreteNonzeroPathAmplitudeSkeleton
    concretePreparedMeasuredPath
    concrete_prepared_measured_path_nonzero_amplitude

/-- The concrete nonzero path-amplitude witness gives causal-before. -/
theorem concrete_nonzero_path_amplitude_causal_before :
    causalBefore (P := concreteProcess)
      ⟨ConcreteState.prepared⟩
      ⟨ConcreteState.measured⟩ :=
  nonzero_path_amplitude_implies_causal_before
    concreteNonzeroPathAmplitudeSkeleton
    concretePreparedMeasuredPath
    concrete_prepared_measured_path_nonzero_amplitude

/-! ## § 4 Public summary -/

/-- Public summary for S5b:
    nonzero path amplitudes are now connected to path validity, reachability,
    and causal-before; the concrete three-state bridge has one nonzero
    path-amplitude witness.  This closes a nonzero candidate witness only, not
    physical phase dynamics, real interference, Born-rule derivation, unitarity,
    CPTP laws, decoherence, or empirical closure. -/
theorem nonzero_path_amplitude_bridge_summary :
    (∀ {P : FiniteProcess} (A : PathAmplitudeSkeleton P)
        (p : ProcessPath P),
        A.pathAmplitude p ≠ 0 → p.valid)
    ∧ (∀ {P : FiniteProcess} (A : PathAmplitudeSkeleton P)
        (p : ProcessPath P),
        A.pathAmplitude p ≠ 0 → Reachable P p.start p.stop)
    ∧ (∀ {P : FiniteProcess} (A : PathAmplitudeSkeleton P)
        (p : ProcessPath P),
        A.pathAmplitude p ≠ 0 →
          causalBefore (P := P) ⟨p.start⟩ ⟨p.stop⟩)
    ∧ HasPathAmplitudeProjection concreteProcess
    ∧ concreteNonzeroPathAmplitudeSkeleton.pathAmplitude
        concretePreparedMeasuredPath ≠ 0
    ∧ Reachable concreteProcess
        ConcreteState.prepared
        ConcreteState.measured
    ∧ causalBefore (P := concreteProcess)
        ⟨ConcreteState.prepared⟩
        ⟨ConcreteState.measured⟩
    ∧ HasInterferenceCandidate
    ∧ (∀ z : ℂ, (bornRuleCandidate z).candidateWeight = ampProb z)
    ∧ WenConstructiveCoverage := by
  rcases interference_bridge_summary with
    ⟨_hConcretePath, _hGridPath, hInterference,
      _hPathComposition, hBornBoundary, _hBornNonnegative,
      _hConcreteChannel, _hGridChannel, _hGridLength, hCoverage⟩
  exact
    ⟨ fun A p => nonzero_path_amplitude_implies_valid A p
    , fun A p => nonzero_path_amplitude_implies_reachable A p
    , fun A p => nonzero_path_amplitude_implies_causal_before A p
    , ⟨concreteNonzeroPathAmplitudeSkeleton⟩
    , concrete_prepared_measured_path_nonzero_amplitude
    , concrete_nonzero_path_amplitude_reachable
    , concrete_nonzero_path_amplitude_causal_before
    , hInterference
    , hBornBoundary
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge
