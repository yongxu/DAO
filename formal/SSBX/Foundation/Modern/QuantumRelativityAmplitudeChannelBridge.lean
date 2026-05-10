/-
# QuantumRelativityAmplitudeChannelBridge — classical Markov vs quantum layers

Companion:
`义理/经典Markov与量子振幅分层 · Markov桥S4.md`

This module advances the Markov/causal bridge by one conservative S4 step:

1. the existing finite probability kernel is marked as the classical Markov
   layer;
2. a separate complex-amplitude skeleton is introduced;
3. a channel candidate carries an amplitude skeleton plus a classical boundary
   projection;
4. the layer tags prove that amplitude/channel candidates are not the same
   formal object as the classical Markov kernel.

This still does not prove a physical quantum channel, unitarity, interference,
Born-rule derivation from the bridge, decoherence, or empirical closure.
-/
import SSBX.Foundation.Modern.Quantum
import SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge

namespace SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge

open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary
open SSBX.Text.OperatorCellMap

/-! ## § 1 Layer tags -/

/-- The bridge layers kept separate in S4. -/
inductive BridgeLayerKind : Type
  | classicalMarkov
  | quantumAmplitude
  | quantumChannel
  deriving Repr, DecidableEq

/-- The existing finite probability kernel belongs to the classical Markov layer. -/
def finiteProbabilityKernelLayer : BridgeLayerKind :=
  .classicalMarkov

/-- A complex-amplitude skeleton belongs to the quantum amplitude candidate layer. -/
def amplitudeSkeletonLayer : BridgeLayerKind :=
  .quantumAmplitude

/-- A channel skeleton belongs to the quantum channel candidate layer. -/
def channelSkeletonLayer : BridgeLayerKind :=
  .quantumChannel

/-- The quantum amplitude layer is not the classical Markov kernel layer. -/
theorem amplitude_layer_is_not_markov_kernel :
    amplitudeSkeletonLayer ≠ finiteProbabilityKernelLayer := by
  decide

/-- The quantum channel layer is not the classical Markov kernel layer. -/
theorem channel_layer_is_not_markov_kernel :
    channelSkeletonLayer ≠ finiteProbabilityKernelLayer := by
  decide

/-! ## § 2 Amplitude and channel skeletons -/

/-- The support of an amplitude candidate: the entry is nonzero. -/
def QuantumAmplitudeSupport {P : FiniteProcess}
    (amp : P.State → P.State → ℂ) (a b : P.State) : Prop :=
  amp a b ≠ 0

/--
A quantum-amplitude candidate over a finite process.

This is only a support-respecting complex amplitude interface.  It does not
assert normalization, unitarity, interference laws, or Born probabilities.
-/
structure QuantumAmplitudeSkeleton (P : FiniteProcess) where
  amplitude : P.State → P.State → ℂ
  amplitude_support_implies_step :
    ∀ a b : P.State, QuantumAmplitudeSupport amplitude a b → P.step a b

/-- A process has an amplitude projection when such a candidate exists. -/
def HasQuantumAmplitudeProjection (P : FiniteProcess) : Prop :=
  Nonempty (QuantumAmplitudeSkeleton P)

/--
A quantum-channel candidate keeps amplitude data separate from the classical
finite probability boundary.

The `classicalBoundary` field is intentionally explicit: a channel candidate
may project back to the classical finite kernel boundary, but it is not itself
identified with that boundary.
-/
structure QuantumChannelSkeleton (P : FiniteProcess) where
  amplitudeLayer : QuantumAmplitudeSkeleton P
  classicalBoundary : FiniteProbabilityKernelSkeleton P
  amplitude_support_refines_classical :
    ∀ a b : P.State,
      QuantumAmplitudeSupport amplitudeLayer.amplitude a b →
        classicalBoundary.support a b

/-- A process has a quantum-channel candidate when such a skeleton exists. -/
def HasQuantumChannelCandidate (P : FiniteProcess) : Prop :=
  Nonempty (QuantumChannelSkeleton P)

/-- The classical boundary carried by a channel candidate. -/
def QuantumChannelSkeleton.toFiniteProbabilityKernel {P : FiniteProcess}
    (C : QuantumChannelSkeleton P) : FiniteProbabilityKernelSkeleton P :=
  C.classicalBoundary

/-- Channel candidates keep, rather than erase, the finite Markov boundary. -/
theorem channel_projection_keeps_markov_boundary {P : FiniteProcess}
    (C : QuantumChannelSkeleton P) :
    HasFiniteProbabilityProjection P :=
  ⟨C.toFiniteProbabilityKernel⟩

/-- Nonzero channel amplitudes refine the carried classical Markov support. -/
theorem channel_amplitude_support_refines_classical {P : FiniteProcess}
    (C : QuantumChannelSkeleton P) {a b : P.State} :
    QuantumAmplitudeSupport C.amplitudeLayer.amplitude a b →
      C.classicalBoundary.support a b :=
  C.amplitude_support_refines_classical a b

/-- Therefore nonzero channel amplitudes still respect the process step relation. -/
theorem channel_amplitude_support_implies_step {P : FiniteProcess}
    (C : QuantumChannelSkeleton P) {a b : P.State} :
    QuantumAmplitudeSupport C.amplitudeLayer.amplitude a b →
      P.step a b := by
  intro h
  exact C.classicalBoundary.support_implies_step a b
    (channel_amplitude_support_refines_classical C h)

/-! ## § 3 Minimal concrete candidates -/

/--
The zero amplitude candidate is a conservative placeholder.

It opens the amplitude layer without smuggling in a physical channel law.  Since
all amplitudes are zero, the support-respecting condition is vacuous.
-/
def zeroQuantumAmplitudeSkeleton (P : FiniteProcess) :
    QuantumAmplitudeSkeleton P where
  amplitude := fun _ _ => 0
  amplitude_support_implies_step := by
    intro a b h
    exact False.elim (h rfl)

/-- Concrete bridge amplitude candidate. -/
def concreteQuantumAmplitudeSkeleton :
    QuantumAmplitudeSkeleton concreteProcess :=
  zeroQuantumAmplitudeSkeleton concreteProcess

/-- Operator-cell grid bridge amplitude candidate. -/
def operatorCellGridQuantumAmplitudeSkeleton :
    QuantumAmplitudeSkeleton operatorCellGridProcess :=
  zeroQuantumAmplitudeSkeleton operatorCellGridProcess

/-- Concrete bridge channel candidate: amplitude layer plus S2 classical boundary. -/
def concreteQuantumChannelSkeleton :
    QuantumChannelSkeleton concreteProcess where
  amplitudeLayer := concreteQuantumAmplitudeSkeleton
  classicalBoundary := concreteFiniteProbabilityKernel
  amplitude_support_refines_classical := by
    intro a b h
    exact False.elim (h rfl)

/-- Operator-cell grid channel candidate: amplitude layer plus S2 classical boundary. -/
def operatorCellGridQuantumChannelSkeleton :
    QuantumChannelSkeleton operatorCellGridProcess where
  amplitudeLayer := operatorCellGridQuantumAmplitudeSkeleton
  classicalBoundary := operatorCellGridFiniteProbabilityKernel
  amplitude_support_refines_classical := by
    intro a b h
    exact False.elim (h rfl)

/-! ## § 4 Public summary -/

/-- Public summary for S4:
    concrete and `371 × 256` grid bridges now carry separate classical Markov,
    amplitude, and channel-candidate layers.  The layer tags prove that
    amplitude/channel candidates are not the same formal object as the
    classical finite probability kernel; channel candidates still project back
    to that classical boundary.  The only Born-rule fact reused here is the
    existing one-qubit computational-basis theorem from `Quantum.lean`. -/
theorem amplitude_channel_bridge_summary :
    HasFiniteProbabilityProjection concreteProcess
    ∧ HasQuantumAmplitudeProjection concreteProcess
    ∧ HasQuantumChannelCandidate concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ HasQuantumAmplitudeProjection operatorCellGridProcess
    ∧ HasQuantumChannelCandidate operatorCellGridProcess
    ∧ amplitudeSkeletonLayer ≠ finiteProbabilityKernelLayer
    ∧ channelSkeletonLayer ≠ finiteProbabilityKernelLayer
    ∧ (∀ _C : QuantumChannelSkeleton concreteProcess,
        HasFiniteProbabilityProjection concreteProcess)
    ∧ (∀ _C : QuantumChannelSkeleton operatorCellGridProcess,
        HasFiniteProbabilityProjection operatorCellGridProcess)
    ∧ (∀ C : QuantumChannelSkeleton concreteProcess,
        ∀ a b : ConcreteState,
          QuantumAmplitudeSupport C.amplitudeLayer.amplitude a b →
            concreteProcess.step a b)
    ∧ (∀ C : QuantumChannelSkeleton operatorCellGridProcess,
        ∀ a b : OperatorCellGridState,
          QuantumAmplitudeSupport C.amplitudeLayer.amplitude a b →
            operatorCellGridProcess.step a b)
    ∧ (∀ ψ : Qubit, computationalBasisNormalized ψ →
        0 ≤ bornProb0 ψ ∧ 0 ≤ bornProb1 ψ ∧ bornProb0 ψ + bornProb1 ψ = 1)
    ∧ allOperatorCells.length = 94976
    ∧ WenConstructiveCoverage := by
  exact
    ⟨ ⟨concreteFiniteProbabilityKernel⟩
    , ⟨concreteQuantumAmplitudeSkeleton⟩
    , ⟨concreteQuantumChannelSkeleton⟩
    , ⟨operatorCellGridFiniteProbabilityKernel⟩
    , ⟨operatorCellGridQuantumAmplitudeSkeleton⟩
    , ⟨operatorCellGridQuantumChannelSkeleton⟩
    , amplitude_layer_is_not_markov_kernel
    , channel_layer_is_not_markov_kernel
    , fun C => channel_projection_keeps_markov_boundary C
    , fun C => channel_projection_keeps_markov_boundary C
    , fun C a b => channel_amplitude_support_implies_step C
    , fun C a b => channel_amplitude_support_implies_step C
    , fun ψ hψ => computational_basis_born_rule ψ hψ
    , allOperatorCells_length
    , wen_constructive_coverage_192_371
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
