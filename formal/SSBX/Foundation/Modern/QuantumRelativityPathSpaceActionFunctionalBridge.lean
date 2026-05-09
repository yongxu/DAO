/-
# QuantumRelativityPathSpaceActionFunctionalBridge -- S25 finite path-space action

Companion:
`义理/路径空间作用量泛函候选 · Markov桥S25.md`

S25 advances S24 from a displayed continuous action coordinate to a finite
path-space action-functional candidate:

1. define a real-valued action functional on finite visible-key quotient
   classes;
2. give the two-route quotient path space the action values `0` and `1`;
3. prove those values match the S5r finite action-index law;
4. prove branch samples agree with the S24 continuous action-coordinate
   samples;
5. prove the induced quotient-support amplitude sum cancels and has
   Born-shaped weight zero.

This is a finite quotient-path action-functional candidate.  It is not a
smooth or infinite-dimensional path-space action functional, not a variational
principle, not an Euler-Lagrange theorem, not a Hamiltonian generator theorem,
not a continuous unitary group, not a path integral, and not empirical closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge

namespace SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge

noncomputable section

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
open SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
open SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge
open SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
open SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite path-space action functional -/

/-- A finite path-space action functional on visible-key quotient classes. -/
structure FinitePathSpaceActionFunctionalCandidate (P : FiniteProcess) where
  action : TwoStepPathKeyQuotient P -> ℝ
  actionIndex : TwoStepPathKeyQuotient P -> Nat
  action_matches_index :
    ∀ q : TwoStepPathKeyQuotient P, action q = (actionIndex q : ℝ)

/-- Amplitude induced by a finite path-space action index. -/
def pathSpaceActionSampledAmplitude {P : FiniteProcess}
    (F : FinitePathSpaceActionFunctionalCandidate P)
    (q : TwoStepPathKeyQuotient P) : ℂ :=
  actionIndexAmplitude (F.actionIndex q)

/-- Finite quotient-support sum induced by a finite path-space action
functional. -/
def quotientSupportPathSpaceActionAmplitudeSum {P : FiniteProcess}
    (F : FinitePathSpaceActionFunctionalCandidate P)
    (qs : List (TwoStepPathKeyQuotient P)) : ℂ :=
  (qs.map fun q => pathSpaceActionSampledAmplitude F q).sum

/-- Born-shaped candidate weight for a finite path-space action support sum. -/
def quotientSupportPathSpaceActionBornWeight {P : FiniteProcess}
    (F : FinitePathSpaceActionFunctionalCandidate P)
    (qs : List (TwoStepPathKeyQuotient P)) : ℝ :=
  ampProb (quotientSupportPathSpaceActionAmplitudeSum F qs)

/-! ## § 2 Two-route finite path-space action -/

/-- Two-route quotient path-space action functional: upper has value `0`,
lower has value `1`, matching the S5r action-index law. -/
def twoRoutePathSpaceActionFunctional :
    FinitePathSpaceActionFunctionalCandidate twoRouteProcess where
  action q := (twoRouteQuotientActionPhaseLaw.actionIndex q : ℝ)
  actionIndex := twoRouteQuotientActionPhaseLaw.actionIndex
  action_matches_index := by
    intro q
    rfl

theorem two_route_upper_path_space_action_value :
    twoRoutePathSpaceActionFunctional.action
      (twoStepPathQuotientClass twoRouteUpperPath) = 0 := by
  norm_num [twoRoutePathSpaceActionFunctional,
    twoRouteQuotientActionPhaseLaw, twoStepPathKey, twoRouteUpperPath]

theorem two_route_lower_path_space_action_value :
    twoRoutePathSpaceActionFunctional.action
      (twoStepPathQuotientClass twoRouteLowerPath) = 1 := by
  norm_num [twoRoutePathSpaceActionFunctional,
    twoRouteQuotientActionPhaseLaw, twoStepPathKey, twoRouteLowerPath]

theorem two_route_path_space_action_index_matches_action_phase_law
    (q : TwoStepPathKeyQuotient twoRouteProcess) :
    twoRoutePathSpaceActionFunctional.actionIndex q =
      twoRouteQuotientActionPhaseLaw.actionIndex q := by
  rfl

/-- Branches are read as the displayed upper/lower quotient classes. -/
def branchPathQuotientClass :
    ActionMeasurementBranch -> TwoStepPathKeyQuotient twoRouteProcess
  | .upper => twoStepPathQuotientClass twoRouteUpperPath
  | .lower => twoStepPathQuotientClass twoRouteLowerPath

theorem branch_path_space_action_value_eq_continuous_action_value
    (b : ActionMeasurementBranch) :
    twoRoutePathSpaceActionFunctional.action (branchPathQuotientClass b) =
      branchContinuousActionValue b := by
  cases b <;>
    norm_num [branchPathQuotientClass, branchContinuousActionValue,
      branchActionTime, displayedContinuousActionFunctional,
      twoRoutePathSpaceActionFunctional, twoRouteQuotientActionPhaseLaw,
      twoStepPathKey, twoRouteUpperPath, twoRouteLowerPath]

theorem path_space_action_sampled_amplitude_eq_action_phase_amplitude
    (q : TwoStepPathKeyQuotient twoRouteProcess) :
    pathSpaceActionSampledAmplitude twoRoutePathSpaceActionFunctional q =
      quotientActionPhaseAmplitude twoRouteQuotientActionPhaseLaw q := by
  rfl

theorem quotientSupportPathSpaceActionAmplitudeSum_eq_action_phase_sum
    (qs : List (TwoStepPathKeyQuotient twoRouteProcess)) :
    quotientSupportPathSpaceActionAmplitudeSum
        twoRoutePathSpaceActionFunctional qs =
      quotientSupportActionPhaseAmplitudeSum
        twoRouteQuotientActionPhaseLaw qs := by
  simp [quotientSupportPathSpaceActionAmplitudeSum,
    quotientSupportActionPhaseAmplitudeSum, pathSpaceActionSampledAmplitude,
    quotientActionPhaseAmplitude, twoRoutePathSpaceActionFunctional]

/-- The two-route quotient support cancels under the finite path-space action
functional. -/
theorem two_route_path_space_action_support_amplitude_cancels :
    quotientSupportPathSpaceActionAmplitudeSum twoRoutePathSpaceActionFunctional
      twoRouteSourceTargetQuotientEnumeration = 0 := by
  rw [quotientSupportPathSpaceActionAmplitudeSum_eq_action_phase_sum]
  exact two_route_action_phase_support_amplitude_cancels

theorem two_route_path_space_action_support_born_weight_zero :
    quotientSupportPathSpaceActionBornWeight twoRoutePathSpaceActionFunctional
      twoRouteSourceTargetQuotientEnumeration = 0 := by
  rw [quotientSupportPathSpaceActionBornWeight,
    two_route_path_space_action_support_amplitude_cancels]
  simp [ampProb]

/-! ## § 3 Closed S25 boundary -/

/-- Closed finite path-space action-functional facts used by S25. -/
def FinitePathSpaceActionFunctionalClosed : Prop :=
  (∀ q : TwoStepPathKeyQuotient twoRouteProcess,
      twoRoutePathSpaceActionFunctional.action q =
        (twoRoutePathSpaceActionFunctional.actionIndex q : ℝ))
    ∧ twoRoutePathSpaceActionFunctional.action
      (twoStepPathQuotientClass twoRouteUpperPath) = 0
    ∧ twoRoutePathSpaceActionFunctional.action
      (twoStepPathQuotientClass twoRouteLowerPath) = 1
    ∧ (∀ q : TwoStepPathKeyQuotient twoRouteProcess,
        twoRoutePathSpaceActionFunctional.actionIndex q =
          twoRouteQuotientActionPhaseLaw.actionIndex q)
    ∧ (∀ b : ActionMeasurementBranch,
        twoRoutePathSpaceActionFunctional.action (branchPathQuotientClass b) =
          branchContinuousActionValue b)
    ∧ (∀ q : TwoStepPathKeyQuotient twoRouteProcess,
        pathSpaceActionSampledAmplitude twoRoutePathSpaceActionFunctional q =
          quotientActionPhaseAmplitude twoRouteQuotientActionPhaseLaw q)
    ∧ quotientSupportPathSpaceActionAmplitudeSum
        twoRoutePathSpaceActionFunctional
        twoRouteSourceTargetQuotientEnumeration = 0
    ∧ quotientSupportPathSpaceActionBornWeight
        twoRoutePathSpaceActionFunctional
        twoRouteSourceTargetQuotientEnumeration = 0

theorem finite_path_space_action_functional_closed :
    FinitePathSpaceActionFunctionalClosed := by
  exact
    ⟨ twoRoutePathSpaceActionFunctional.action_matches_index
    , two_route_upper_path_space_action_value
    , two_route_lower_path_space_action_value
    , two_route_path_space_action_index_matches_action_phase_law
    , branch_path_space_action_value_eq_continuous_action_value
    , path_space_action_sampled_amplitude_eq_action_phase_amplitude
    , two_route_path_space_action_support_amplitude_cancels
    , two_route_path_space_action_support_born_weight_zero
    ⟩

/-! ## § 4 Remaining physical ledger -/

inductive PendingBeyondS25 where
  | smoothOrInfinitePathSpaceActionFunctional
  | variationalPrinciple
  | eulerLagrangeEquations
  | hamiltonianGenerator
  | continuousTimeUnitaryGroup
  | selfAdjointOperatorSemantics
  | generalSchrodingerDynamics
  | generalPathIntegral
  | generalHilbertMeasurement
  | projectionValuedMeasures
  | povmSemantics
  | decoherenceDynamics
  | empiricalClosure
  deriving DecidableEq, Repr

def ClosedByStepwiseS25 (_b : PendingBeyondS25) : Bool :=
  false

theorem pending_boundary_not_closed_by_s25
    (b : PendingBeyondS25) :
    ClosedByStepwiseS25 b = false := by
  cases b <;> rfl

/-! ## § 5 Public summary -/

theorem path_space_action_functional_bridge_summary :
    FinitePathSpaceActionFunctionalClosed
    ∧ ContinuousActionFunctionalClosed
    ∧ TwoRouteActionPhaseLawBoundaryComplete
    ∧ FinitePhaseEvolutionClosed
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS25, ClosedByStepwiseS25 b = false)
    ∧ WenConstructiveCoverage := by
  rcases continuous_action_functional_bridge_summary with
    ⟨hContinuousAction, hFinitePhase, hActionToBorn,
      hBornMeasurement, _hPendingS24, hCoverage⟩
  rcases action_phase_law_bridge_summary with
    ⟨hActionPhase, _hKeySum, _hKeyWeight, _hLedger, _hCoverageS5r⟩
  exact
    ⟨ finite_path_space_action_functional_closed
    , hContinuousAction
    , hActionPhase
    , hFinitePhase
    , hActionToBorn
    , hBornMeasurement
    , pending_boundary_not_closed_by_s25
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge
