/-
# QuantumRelativityFiniteActionExtremumBridge -- S26 finite action extremum

Companion:
`义理/有限作用量极值候选 · Markov桥S26.md`

S26 advances S25 by proving a finite extremum fact on the displayed two-route
quotient support:

1. define finite action gaps on quotient path classes;
2. prove the lower-minus-upper action gap is `1`;
3. prove the upper quotient path is a finite action minimum on the displayed
   source/target quotient support;
4. prove the lower quotient path is not such a minimum.

This is only a finite support extremum candidate for the two-route quotient
path space.  It is not a smooth variation space, not a stationary-action
principle, not an Euler-Lagrange theorem, not a Hamiltonian generator theorem,
not continuous-time unitary dynamics, not a path integral, and not empirical
closure.
-/
import Mathlib.Tactic
import SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge

namespace SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge

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
open SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge
open SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
open SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite action gap and support minimum -/

/-- Finite action gap from a base quotient path to a varied quotient path. -/
def finiteActionGap {P : FiniteProcess}
    (F : FinitePathSpaceActionFunctionalCandidate P)
    (base varied : TwoStepPathKeyQuotient P) : ℝ :=
  F.action varied - F.action base

/-- A quotient path is a finite action minimum on a displayed finite support. -/
def FiniteActionMinimumOnSupport {P : FiniteProcess}
    (F : FinitePathSpaceActionFunctionalCandidate P)
    (support : List (TwoStepPathKeyQuotient P))
    (q0 : TwoStepPathKeyQuotient P) : Prop :=
  q0 ∈ support ∧ ∀ q, q ∈ support -> F.action q0 ≤ F.action q

/-! ## § 2 Two-route finite extremum facts -/

theorem two_route_upper_in_action_extremum_support :
    twoStepPathQuotientClass twoRouteUpperPath ∈
      twoRouteSourceTargetQuotientEnumeration := by
  simp [twoRouteSourceTargetQuotientEnumeration]

theorem two_route_lower_in_action_extremum_support :
    twoStepPathQuotientClass twoRouteLowerPath ∈
      twoRouteSourceTargetQuotientEnumeration := by
  simp [twoRouteSourceTargetQuotientEnumeration]

theorem two_route_upper_to_lower_action_gap :
    finiteActionGap twoRoutePathSpaceActionFunctional
      (twoStepPathQuotientClass twoRouteUpperPath)
      (twoStepPathQuotientClass twoRouteLowerPath) = 1 := by
  rw [finiteActionGap, two_route_lower_path_space_action_value,
    two_route_upper_path_space_action_value]
  norm_num

theorem two_route_lower_to_upper_action_gap :
    finiteActionGap twoRoutePathSpaceActionFunctional
      (twoStepPathQuotientClass twoRouteLowerPath)
      (twoStepPathQuotientClass twoRouteUpperPath) = -1 := by
  rw [finiteActionGap, two_route_upper_path_space_action_value,
    two_route_lower_path_space_action_value]
  norm_num

theorem two_route_lower_action_eq_upper_plus_one :
    twoRoutePathSpaceActionFunctional.action
      (twoStepPathQuotientClass twoRouteLowerPath) =
        twoRoutePathSpaceActionFunctional.action
          (twoStepPathQuotientClass twoRouteUpperPath) + 1 := by
  rw [two_route_lower_path_space_action_value,
    two_route_upper_path_space_action_value]
  norm_num

/-- On the displayed two-route quotient support, the upper path is a finite
minimum of the S25 path-space action functional. -/
theorem two_route_upper_is_finite_action_minimum :
    FiniteActionMinimumOnSupport twoRoutePathSpaceActionFunctional
      twoRouteSourceTargetQuotientEnumeration
      (twoStepPathQuotientClass twoRouteUpperPath) := by
  constructor
  · exact two_route_upper_in_action_extremum_support
  · intro q hq
    simp [twoRouteSourceTargetQuotientEnumeration] at hq
    rcases hq with hq | hq
    · rw [hq]
    · rw [hq, two_route_upper_path_space_action_value,
        two_route_lower_path_space_action_value]
      norm_num

/-- The lower path is not a minimum on the displayed two-route quotient support,
because the upper path has strictly smaller finite action. -/
theorem two_route_lower_not_finite_action_minimum :
    ¬ FiniteActionMinimumOnSupport twoRoutePathSpaceActionFunctional
      twoRouteSourceTargetQuotientEnumeration
      (twoStepPathQuotientClass twoRouteLowerPath) := by
  intro h
  have hle := h.2 (twoStepPathQuotientClass twoRouteUpperPath)
    two_route_upper_in_action_extremum_support
  rw [two_route_lower_path_space_action_value,
    two_route_upper_path_space_action_value] at hle
  norm_num at hle

/-! ## § 3 Closed S26 boundary -/

/-- Closed finite action-extremum facts used by S26. -/
def TwoRouteFiniteActionExtremumClosed : Prop :=
  twoStepPathQuotientClass twoRouteUpperPath ∈
      twoRouteSourceTargetQuotientEnumeration
    ∧ twoStepPathQuotientClass twoRouteLowerPath ∈
      twoRouteSourceTargetQuotientEnumeration
    ∧ finiteActionGap twoRoutePathSpaceActionFunctional
      (twoStepPathQuotientClass twoRouteUpperPath)
      (twoStepPathQuotientClass twoRouteLowerPath) = 1
    ∧ finiteActionGap twoRoutePathSpaceActionFunctional
      (twoStepPathQuotientClass twoRouteLowerPath)
      (twoStepPathQuotientClass twoRouteUpperPath) = -1
    ∧ twoRoutePathSpaceActionFunctional.action
      (twoStepPathQuotientClass twoRouteLowerPath) =
        twoRoutePathSpaceActionFunctional.action
          (twoStepPathQuotientClass twoRouteUpperPath) + 1
    ∧ FiniteActionMinimumOnSupport twoRoutePathSpaceActionFunctional
      twoRouteSourceTargetQuotientEnumeration
      (twoStepPathQuotientClass twoRouteUpperPath)
    ∧ ¬ FiniteActionMinimumOnSupport twoRoutePathSpaceActionFunctional
      twoRouteSourceTargetQuotientEnumeration
      (twoStepPathQuotientClass twoRouteLowerPath)

theorem finite_action_extremum_closed :
    TwoRouteFiniteActionExtremumClosed := by
  exact
    ⟨ two_route_upper_in_action_extremum_support
    , two_route_lower_in_action_extremum_support
    , two_route_upper_to_lower_action_gap
    , two_route_lower_to_upper_action_gap
    , two_route_lower_action_eq_upper_plus_one
    , two_route_upper_is_finite_action_minimum
    , two_route_lower_not_finite_action_minimum
    ⟩

/-! ## § 4 Remaining physical ledger -/

inductive PendingBeyondS26 where
  | smoothOrInfinitePathSpaceActionFunctional
  | continuousVariationSpace
  | stationaryActionPrinciple
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

def ClosedByStepwiseS26 (_b : PendingBeyondS26) : Bool :=
  false

theorem pending_boundary_not_closed_by_s26
    (b : PendingBeyondS26) :
    ClosedByStepwiseS26 b = false := by
  cases b <;> rfl

/-! ## § 5 Public summary -/

theorem finite_action_extremum_bridge_summary :
    TwoRouteFiniteActionExtremumClosed
    ∧ FinitePathSpaceActionFunctionalClosed
    ∧ ContinuousActionFunctionalClosed
    ∧ TwoRouteActionPhaseLawBoundaryComplete
    ∧ FinitePhaseEvolutionClosed
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS26, ClosedByStepwiseS26 b = false)
    ∧ WenConstructiveCoverage := by
  rcases path_space_action_functional_bridge_summary with
    ⟨hPath, hContinuous, hActionPhase, hFinitePhase, hActionToBorn,
      hBorn, _hPendingS25, hCoverage⟩
  exact
    ⟨ finite_action_extremum_closed
    , hPath
    , hContinuous
    , hActionPhase
    , hFinitePhase
    , hActionToBorn
    , hBorn
    , pending_boundary_not_closed_by_s26
    , hCoverage
    ⟩

end

end SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge
