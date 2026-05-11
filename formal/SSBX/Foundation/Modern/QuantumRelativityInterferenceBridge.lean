/-
# QuantumRelativityInterferenceBridge — path amplitude and interference candidates

Companion:
`义理/干涉与测量律候选 · Markov桥S5.md`

This module advances the Markov/causal bridge by one conservative S5 step:

1. it adds a path-amplitude skeleton on top of the S4 amplitude/channel layer;
2. it records a formal path-amplitude composition interface;
3. it records a destructive-interference candidate;
4. it records a Born-rule-shaped boundary as `ampProb`, without deriving the
   Born rule from the Markov bridge.

This still does not prove physical interference, a unitary path integral,
CPTP channel laws, a measurement postulate, decoherence, or empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge

namespace SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge

open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Text.OperatorCellMap

/-! ## § 1 Path amplitude skeleton -/

/--
A path-amplitude candidate over a finite process.

The `channel` field carries the S4 amplitude/channel candidate.  The
`pathAmplitude` field is only a complex-valued path interface.  Its composition
law is a candidate equation over explicit `ComposableProcessPaths`; it is not a
path integral, not a unitarity theorem, and not a physical interference law.
-/
structure PathAmplitudeSkeleton (P : FiniteProcess) where
  channel : QuantumChannelSkeleton P
  pathAmplitude : ProcessPath P → ℂ
  path_support_implies_valid :
    ∀ p : ProcessPath P, pathAmplitude p ≠ 0 → p.valid
  composed_amplitude :
    ∀ c : ComposableProcessPaths P,
      pathAmplitude (composeProcessPaths c) =
        pathAmplitude c.left * pathAmplitude c.right

/-- A process has a path-amplitude projection when such a candidate exists. -/
def HasPathAmplitudeProjection (P : FiniteProcess) : Prop :=
  Nonempty (PathAmplitudeSkeleton P)

/-- Path-amplitude composition is available at the S5 candidate-interface level. -/
theorem amplitude_path_composition {P : FiniteProcess}
    (A : PathAmplitudeSkeleton P) (c : ComposableProcessPaths P) :
    A.pathAmplitude (composeProcessPaths c) =
      A.pathAmplitude c.left * A.pathAmplitude c.right :=
  A.composed_amplitude c

/-! ## § 2 Interference and Born-shaped candidates -/

/-- A destructive-interference candidate: two amplitudes whose sum cancels. -/
structure InterferenceCandidate where
  leftAmplitude : ℂ
  rightAmplitude : ℂ
  cancels : leftAmplitude + rightAmplitude = 0

/-- S5 has an interference candidate when such a cancellation witness exists. -/
def HasInterferenceCandidate : Prop :=
  Nonempty InterferenceCandidate

/-- A minimal destructive-interference witness, kept separate from any path law. -/
def destructiveInterferenceWitness : InterferenceCandidate where
  leftAmplitude := 1
  rightAmplitude := -1
  cancels := by
    norm_num

/-- The interference candidate exists as a typed witness. -/
theorem interference_candidate : HasInterferenceCandidate :=
  ⟨destructiveInterferenceWitness⟩

/--
A Born-rule-shaped candidate boundary.

This records the familiar shape `weight = ampProb amplitude`.  It does not say
that the Markov bridge derives the Born rule, and it does not provide a
normalized measurement law over paths.
-/
structure BornRuleCandidateBoundary where
  amplitude : ℂ
  candidateWeight : ℝ
  boundary : candidateWeight = ampProb amplitude

/-- Build the Born-shaped boundary for any single complex amplitude. -/
def bornRuleCandidate (z : ℂ) : BornRuleCandidateBoundary where
  amplitude := z
  candidateWeight := ampProb z
  boundary := rfl

/-- The Born-shaped candidate is exactly the `ampProb` boundary. -/
theorem born_rule_candidate_boundary (z : ℂ) :
    (bornRuleCandidate z).candidateWeight = ampProb z :=
  rfl

/-- The Born-shaped candidate weight is nonnegative, because `ampProb` is norm square. -/
theorem born_rule_candidate_nonnegative (z : ℂ) :
    0 ≤ (bornRuleCandidate z).candidateWeight :=
  Complex.normSq_nonneg z

/-! ## § 3 Minimal concrete candidates -/

/--
The zero path-amplitude candidate is a conservative placeholder.

It opens the path-amplitude interface without asserting nontrivial physical
interference.  Since all path amplitudes are zero, the validity condition is
vacuous and the composition equation is definitionally true.
-/
def zeroPathAmplitudeSkeleton (P : FiniteProcess)
    (C : QuantumChannelSkeleton P) : PathAmplitudeSkeleton P where
  channel := C
  pathAmplitude := fun _ => 0
  path_support_implies_valid := by
    intro p h
    exact False.elim (h rfl)
  composed_amplitude := by
    intro c
    simp

/-- Concrete bridge path-amplitude candidate. -/
def concretePathAmplitudeSkeleton :
    PathAmplitudeSkeleton concreteProcess :=
  zeroPathAmplitudeSkeleton concreteProcess concreteQuantumChannelSkeleton

/-- Operator-cell grid bridge path-amplitude candidate. -/
def operatorCellGridPathAmplitudeSkeleton :
    PathAmplitudeSkeleton operatorCellGridProcess :=
  zeroPathAmplitudeSkeleton operatorCellGridProcess operatorCellGridQuantumChannelSkeleton

/-! ## § 4 Public summary -/

/-- Public summary for S5:
    concrete and `371 × 256` grid bridges now carry path-amplitude candidates
    above the S4 amplitude/channel layer.  S5 also records an interference
    candidate and a Born-rule-shaped `ampProb` boundary.  These are candidate
    interfaces only: no nonzero physical path amplitudes, no unitary path
    integral, no Born-rule derivation from Markov weights, and no empirical
    closure are proved here. -/
theorem interference_bridge_summary :
    HasPathAmplitudeProjection concreteProcess
    ∧ HasPathAmplitudeProjection operatorCellGridProcess
    ∧ HasInterferenceCandidate
    ∧ (∀ {P : FiniteProcess} (A : PathAmplitudeSkeleton P)
        (c : ComposableProcessPaths P),
        A.pathAmplitude (composeProcessPaths c) =
          A.pathAmplitude c.left * A.pathAmplitude c.right)
    ∧ (∀ z : ℂ, (bornRuleCandidate z).candidateWeight = ampProb z)
    ∧ (∀ z : ℂ, 0 ≤ (bornRuleCandidate z).candidateWeight)
    ∧ HasQuantumChannelCandidate concreteProcess
    ∧ HasQuantumChannelCandidate operatorCellGridProcess
    ∧ allOperatorCells.length = 94976
    ∧ WenConstructiveCoverage := by
  rcases amplitude_channel_bridge_summary with
    ⟨_hConcreteProb, _hConcreteAmp, hConcreteChannel,
      _hGridProb, _hGridAmp, hGridChannel,
      _hAmpLayer, _hChannelLayer, _hConcreteProjection, _hGridProjection,
      _hConcreteStep, _hGridStep, _hBorn, hGridLength, hCoverage⟩
  exact
    ⟨ ⟨concretePathAmplitudeSkeleton⟩
    , ⟨operatorCellGridPathAmplitudeSkeleton⟩
    , interference_candidate
    , fun A c => amplitude_path_composition A c
    , born_rule_candidate_boundary
    , born_rule_candidate_nonnegative
    , hConcreteChannel
    , hGridChannel
    , hGridLength
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
