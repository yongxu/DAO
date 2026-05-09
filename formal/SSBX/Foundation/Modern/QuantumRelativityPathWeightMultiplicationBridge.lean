/-
# QuantumRelativityPathWeightMultiplicationBridge -- S19 path-weight multiplication

Companion:
`义理/路径权重乘法候选 · Markov桥S19.md`

S19 closes the finite path-weight multiplication law that was deliberately left
open in S3.  The old `ProcessPath` still only records endpoints and validity, so
this module introduces a refined finite kernel path whose edges carry positive
Markov weights.  Its path weight is the product of displayed edge weights, and
append composition multiplies those products.

This is a finite typed-skeleton law.  It does not prove a path integral,
continuous-time dynamics, stochastic independence, unitary/CPTP laws, metric
recovery, or empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge

namespace SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge

open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
open SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
open SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Current endpoint-only pathWeight boundary -/

/--
The original S0/S3 `pathWeight` is endpoint-only and currently constant `1`.
Its multiplicativity is therefore closed, but only as a placeholder boundary.
-/
theorem current_pathWeight_compose_multiplicative
    {P : FiniteProcess}
    (K : MarkovKernelSkeleton P)
    (c : ComposableProcessPaths P) :
    pathWeight K (composeProcessPaths c)
      = pathWeight K c.left * pathWeight K c.right := by
  simp [pathWeight]

/-! ## § 2 Finite kernel-edge paths -/

/-- A one-step kernel edge with positive Markov weight. -/
structure KernelEdge {P : FiniteProcess}
    (K : MarkovKernelSkeleton P) (a b : P.State) where
  positive_weight : K.weight a b ≠ 0

namespace KernelEdge

/-- Weight carried by a displayed kernel edge. -/
def weight {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State} (_e : KernelEdge K a b) : Nat :=
  K.weight a b

/-- A positive-weight kernel edge is a process step. -/
theorem step {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State} (e : KernelEdge K a b) :
    P.step a b :=
  positive_weight_implies_step K e.positive_weight

end KernelEdge

/--
A finite kernel path indexed by its endpoints.  The constructors make endpoint
matching part of the type, so append can only compose matching paths.
-/
inductive KernelPath {P : FiniteProcess}
    (K : MarkovKernelSkeleton P) : P.State -> P.State -> Type where
  | refl (a : P.State) : KernelPath K a a
  | snoc {a b c : P.State} :
      KernelPath K a b -> KernelEdge K b c -> KernelPath K a c

namespace KernelPath

/-- Product of all displayed edge weights. -/
def weight {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State} : KernelPath K a b -> Nat
  | refl _ => 1
  | snoc p e => weight p * KernelEdge.weight e

/-- Append two endpoint-matching finite kernel paths. -/
def append {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b c : P.State} :
    KernelPath K a b -> KernelPath K b c -> KernelPath K a c
  | p, refl _ => p
  | p, snoc q e => snoc (append p q) e

/-- A finite kernel path can be read back as the older endpoint-only path. -/
def toProcessPath {P : FiniteProcess} {K : MarkovKernelSkeleton P}
    {a b : P.State} (_p : KernelPath K a b) : ProcessPath P :=
  { start := a
    stop := b
    valid := True }

/-- Read two endpoint-matching kernel paths as an old S3 composable pair. -/
def toComposableProcessPaths {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (q : KernelPath K b c) :
    ComposableProcessPaths P :=
  { left := toProcessPath p
    right := toProcessPath q
    middle_eq := rfl
    left_valid := True.intro
    right_valid := True.intro }

/-- Appending finite kernel paths preserves the old S3 reachable reading. -/
theorem append_reachable {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (q : KernelPath K b c) :
    Reachable P a c :=
  composed_path_reachable (toComposableProcessPaths p q)

/-- Appending finite kernel paths preserves the old S3 causal-before reading. -/
theorem append_causal_before {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (q : KernelPath K b c) :
    causalBefore (P := P) ⟨a⟩ ⟨c⟩ :=
  composed_path_causal_before (toComposableProcessPaths p q)

/-- The core path-weight multiplication law for finite kernel paths. -/
theorem weight_append {P : FiniteProcess}
    {K : MarkovKernelSkeleton P} {a b c : P.State}
    (p : KernelPath K a b) (q : KernelPath K b c) :
    weight (append p q) = weight p * weight q := by
  induction q with
  | refl =>
      simp [append, weight]
  | snoc q e ih =>
      simp [append, weight, ih, Nat.mul_assoc]

end KernelPath

/-! ## § 3 Concrete two-step witness -/

def concretePreparedEvolvedEdge :
    KernelEdge concreteKernel ConcreteState.prepared ConcreteState.evolved where
  positive_weight := by decide

def concreteEvolvedMeasuredEdge :
    KernelEdge concreteKernel ConcreteState.evolved ConcreteState.measured where
  positive_weight := by decide

def concretePreparedEvolvedKernelPath :
    KernelPath concreteKernel ConcreteState.prepared ConcreteState.evolved :=
  KernelPath.snoc (KernelPath.refl (K := concreteKernel) ConcreteState.prepared)
    concretePreparedEvolvedEdge

def concreteEvolvedMeasuredKernelPath :
    KernelPath concreteKernel ConcreteState.evolved ConcreteState.measured :=
  KernelPath.snoc (KernelPath.refl (K := concreteKernel) ConcreteState.evolved)
    concreteEvolvedMeasuredEdge

def concretePreparedMeasuredKernelPath :
    KernelPath concreteKernel ConcreteState.prepared ConcreteState.measured :=
  KernelPath.append concretePreparedEvolvedKernelPath
    concreteEvolvedMeasuredKernelPath

theorem concrete_prepared_measured_kernel_path_weight :
    KernelPath.weight concretePreparedMeasuredKernelPath = 1 := by
  simp [concretePreparedMeasuredKernelPath, concretePreparedEvolvedKernelPath,
    concreteEvolvedMeasuredKernelPath, KernelPath.append, KernelPath.weight,
    KernelEdge.weight, concreteKernel, ConcreteState.weight]

theorem concrete_two_step_path_weight_multiplicative :
    KernelPath.weight concretePreparedMeasuredKernelPath
      =
        KernelPath.weight concretePreparedEvolvedKernelPath
          * KernelPath.weight concreteEvolvedMeasuredKernelPath := by
  exact KernelPath.weight_append concretePreparedEvolvedKernelPath
    concreteEvolvedMeasuredKernelPath

/-! ## § 4 Remaining physical ledger -/

inductive PendingBeyondS19 where
  | stochasticIndependenceSemantics
  | generalAllPathEnumeration
  | generalPathIntegral
  | amplitudeDynamics
  | measurementPostulateSemantics
  | decoherenceBoundary
  | unitaryCPTPChannelLaw
  | metricRecovery
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS19 (_b : PendingBeyondS19) : Bool :=
  false

theorem pending_boundary_not_closed_by_s19
    (b : PendingBeyondS19) :
    ClosedByStepwiseS19 b = false := by
  cases b <;> rfl

def PathWeightMultiplicationBoundaryClosed : Prop :=
  (∀ {P : FiniteProcess}
      (K : MarkovKernelSkeleton P)
      (c : ComposableProcessPaths P),
      pathWeight K (composeProcessPaths c)
        = pathWeight K c.left * pathWeight K c.right)
    ∧ (∀ {P : FiniteProcess}
        {K : MarkovKernelSkeleton P}
        {a b c : P.State}
        (p : KernelPath K a b) (q : KernelPath K b c),
        KernelPath.weight (KernelPath.append p q)
          = KernelPath.weight p * KernelPath.weight q)

theorem path_weight_multiplication_boundary_closed :
    PathWeightMultiplicationBoundaryClosed := by
  exact
    ⟨ fun K c => current_pathWeight_compose_multiplicative K c
    , fun p q => KernelPath.weight_append p q
    ⟩

/-! ## § 5 Public summary -/

theorem path_weight_multiplication_bridge_summary :
    PathWeightMultiplicationBoundaryClosed
    ∧ KernelPath.weight concretePreparedMeasuredKernelPath = 1
    ∧ Reachable concreteProcess ConcreteState.prepared ConcreteState.measured
    ∧ causalBefore (P := concreteProcess)
        ⟨ConcreteState.prepared⟩ ⟨ConcreteState.measured⟩
    ∧ (∀ b : PendingBeyondS19, ClosedByStepwiseS19 b = false)
    ∧ WenConstructiveCoverage := by
  rcases born_rule_derivation_bridge_summary with
    ⟨_hBorn, _hSumOverMiddleBorn, _hDerivation, _hConcrete,
      _hPending, hCoverage⟩
  exact
    ⟨ path_weight_multiplication_boundary_closed
    , concrete_prepared_measured_kernel_path_weight
    , KernelPath.append_reachable concretePreparedEvolvedKernelPath
        concreteEvolvedMeasuredKernelPath
    , KernelPath.append_causal_before concretePreparedEvolvedKernelPath
        concreteEvolvedMeasuredKernelPath
    , pending_boundary_not_closed_by_s19
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
