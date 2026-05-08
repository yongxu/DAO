/-
# QuantumRelativityQuotientSupportAlgebraBridge -- quotient-support algebra

Companion:
`义理/商支撑代数候选 · Markov桥S5p.md`

This module advances S5o by adding finite list algebra for quotient supports:

1. quotient-support sums distribute over append;
2. quotient-support sums are stable under permutation and reversal;
3. duplicated zero-sum quotient supports still cancel;
4. the two-route quotient-support cancellation is stable under reversal and
   under appending two cancelled supports.

This is only finite list algebra over quotient classes.  It is not general
all-path enumeration, not a path integral, not a Born-rule derivation, not
unitary/CPTP dynamics, and not empirical closure.
-/
import SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge

namespace SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge

open SSBX.Foundation.Modern.Quantum
open SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
open SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
open SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
open SSBX.Foundation.Modern.QuantumRelativityWenBoundary

/-! ## § 1 Finite quotient-support list algebra -/

/-- Append two finite quotient-support lists. -/
def appendQuotientSupports {P : FiniteProcess}
    (xs ys : List (TwoStepPathKeyQuotient P)) :
    List (TwoStepPathKeyQuotient P) :=
  xs ++ ys

/-- Reverse a finite quotient-support list. -/
def reverseQuotientSupport {P : FiniteProcess}
    (xs : List (TwoStepPathKeyQuotient P)) :
    List (TwoStepPathKeyQuotient P) :=
  xs.reverse

/-- Duplicate a finite quotient-support list. -/
def duplicateQuotientSupport {P : FiniteProcess}
    (xs : List (TwoStepPathKeyQuotient P)) :
    List (TwoStepPathKeyQuotient P) :=
  appendQuotientSupports xs xs

theorem quotient_support_amplitude_sum_append {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs ys : List (TwoStepPathKeyQuotient P)) :
    quotientSupportAmplitudeSum K (appendQuotientSupports xs ys) =
      quotientSupportAmplitudeSum K xs + quotientSupportAmplitudeSum K ys := by
  simp [quotientSupportAmplitudeSum, appendQuotientSupports,
    List.map_append, List.sum_append]

theorem quotient_support_born_weight_append_boundary {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs ys : List (TwoStepPathKeyQuotient P)) :
    quotientSupportBornWeight K (appendQuotientSupports xs ys) =
      ampProb
        (quotientSupportAmplitudeSum K xs
          + quotientSupportAmplitudeSum K ys) := by
  rw [quotientSupportBornWeight,
    quotient_support_amplitude_sum_append]

theorem quotient_support_amplitude_sum_perm {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    {xs ys : List (TwoStepPathKeyQuotient P)}
    (h : xs.Perm ys) :
    quotientSupportAmplitudeSum K xs =
      quotientSupportAmplitudeSum K ys := by
  unfold quotientSupportAmplitudeSum
  exact (h.map fun q => quotientKeyAmplitude K q).sum_eq

theorem quotient_support_born_weight_perm {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    {xs ys : List (TwoStepPathKeyQuotient P)}
    (h : xs.Perm ys) :
    quotientSupportBornWeight K xs =
      quotientSupportBornWeight K ys := by
  rw [quotientSupportBornWeight, quotientSupportBornWeight,
    quotient_support_amplitude_sum_perm K h]

theorem quotient_support_amplitude_sum_reverse {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs : List (TwoStepPathKeyQuotient P)) :
    quotientSupportAmplitudeSum K (reverseQuotientSupport xs) =
      quotientSupportAmplitudeSum K xs := by
  exact quotient_support_amplitude_sum_perm K
    (List.reverse_perm xs)

theorem quotient_support_born_weight_reverse {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs : List (TwoStepPathKeyQuotient P)) :
    quotientSupportBornWeight K (reverseQuotientSupport xs) =
      quotientSupportBornWeight K xs := by
  rw [quotientSupportBornWeight, quotientSupportBornWeight,
    quotient_support_amplitude_sum_reverse K xs]

theorem quotient_support_amplitude_sum_duplicate {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs : List (TwoStepPathKeyQuotient P)) :
    quotientSupportAmplitudeSum K (duplicateQuotientSupport xs) =
      quotientSupportAmplitudeSum K xs + quotientSupportAmplitudeSum K xs := by
  exact quotient_support_amplitude_sum_append K xs xs

theorem quotient_support_duplicate_cancels_of_canceling {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs : List (TwoStepPathKeyQuotient P))
    (h : quotientSupportAmplitudeSum K xs = 0) :
    quotientSupportAmplitudeSum K (duplicateQuotientSupport xs) = 0 := by
  rw [quotient_support_amplitude_sum_duplicate K xs, h]
  simp

theorem quotient_support_duplicate_born_weight_zero_of_canceling
    {P : FiniteProcess}
    (K : TwoStepKeyAmplitudeCandidate P)
    (xs : List (TwoStepPathKeyQuotient P))
    (h : quotientSupportAmplitudeSum K xs = 0) :
    quotientSupportBornWeight K (duplicateQuotientSupport xs) = 0 := by
  rw [quotientSupportBornWeight,
    quotient_support_duplicate_cancels_of_canceling K xs h]
  simp [ampProb]

/-! ## § 2 Two-route quotient-support algebra witnesses -/

/-- The two-route quotient support in reversed order. -/
def twoRouteReversedQuotientSupport :=
  reverseQuotientSupport twoRouteSourceTargetQuotientEnumeration

theorem two_route_reversed_quotient_support_perm :
    twoRouteSourceTargetQuotientEnumeration.Perm
      twoRouteReversedQuotientSupport := by
  exact (List.reverse_perm twoRouteSourceTargetQuotientEnumeration).symm

theorem two_route_reversed_quotient_support_amplitude_cancels :
    quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteReversedQuotientSupport = 0 := by
  simpa [twoRouteReversedQuotientSupport] using
    (quotient_support_amplitude_sum_reverse
      twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration).trans
        two_route_quotient_support_amplitude_sum_cancels

theorem two_route_reversed_quotient_support_born_weight_zero :
    quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteReversedQuotientSupport = 0 := by
  rw [quotientSupportBornWeight,
    two_route_reversed_quotient_support_amplitude_cancels]
  simp [ampProb]

/-- Append the displayed quotient support to its reversed zero-sum support. -/
def twoRouteDoubleQuotientSupport :=
  appendQuotientSupports
    twoRouteSourceTargetQuotientEnumeration
    twoRouteReversedQuotientSupport

theorem two_route_double_quotient_support_amplitude_cancels :
    quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0 := by
  rw [twoRouteDoubleQuotientSupport,
    quotient_support_amplitude_sum_append,
    two_route_quotient_support_amplitude_sum_cancels,
    two_route_reversed_quotient_support_amplitude_cancels]
  simp

theorem two_route_double_quotient_support_born_weight_zero :
    quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0 := by
  rw [quotientSupportBornWeight,
    two_route_double_quotient_support_amplitude_cancels]
  simp [ampProb]

/-! ## § 3 Public summary -/

/-- Public summary for S5p:
    quotient-support sums now have append, permutation, reverse, and duplicate
    cancellation stability; the two-route quotient-support cancellation remains
    stable under reversal and under appending two cancelled supports.  This
    proves only finite quotient-support list algebra, not all-path
    enumeration, path integral, Born-rule derivation, unitary/CPTP dynamics,
    or empirical closure. -/
theorem quotient_support_algebra_bridge_summary :
    (∀ {P : FiniteProcess}
        (K : TwoStepKeyAmplitudeCandidate P)
        (xs ys : List (TwoStepPathKeyQuotient P)),
        quotientSupportAmplitudeSum K
          (appendQuotientSupports xs ys) =
            quotientSupportAmplitudeSum K xs
              + quotientSupportAmplitudeSum K ys)
    ∧ (∀ {P : FiniteProcess}
        (K : TwoStepKeyAmplitudeCandidate P)
        {xs ys : List (TwoStepPathKeyQuotient P)}
        (_h : xs.Perm ys),
        quotientSupportAmplitudeSum K xs =
          quotientSupportAmplitudeSum K ys)
    ∧ (∀ {P : FiniteProcess}
        (K : TwoStepKeyAmplitudeCandidate P)
        (xs : List (TwoStepPathKeyQuotient P)),
        quotientSupportAmplitudeSum K (reverseQuotientSupport xs) =
          quotientSupportAmplitudeSum K xs)
    ∧ quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteReversedQuotientSupport = 0
    ∧ quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteReversedQuotientSupport = 0
    ∧ quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0
    ∧ quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0
    ∧ WenConstructiveCoverage := by
  rcases quotient_support_bridge_summary with
    ⟨_hClasses, _hComplete, _hKeys, _hCancel, _hBorn,
      _hRepresentatives, hCoverage⟩
  exact
    ⟨ quotient_support_amplitude_sum_append
    , quotient_support_amplitude_sum_perm
    , quotient_support_amplitude_sum_reverse
    , two_route_reversed_quotient_support_amplitude_cancels
    , two_route_reversed_quotient_support_born_weight_zero
    , two_route_double_quotient_support_amplitude_cancels
    , two_route_double_quotient_support_born_weight_zero
    , hCoverage
    ⟩

end SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge
