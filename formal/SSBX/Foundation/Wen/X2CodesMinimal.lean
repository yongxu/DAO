/-
# `SSBX.Foundation.Wen.X2CodesMinimal` — forcing `axes = 8` from minimality

Fourth companion in the Open Problem #2 chain (after `X2Codes.lean`,
`X2CodesUniqueness.lean`, `X2CodesFace.lean`).  Discharges item **(a)**
of `wen-substrate.md` §4.7bis.5: *"forcing `axes = 8` from minimality."*

## The honest minimality argument

We extend `UGCandidateFace` to `UGCandidateMinimal` with **three**
structural axioms.  Each is independently motivated by the doctrine
(§3.7 operation monism + §4.7bis.3 cardinality table), and *together*
they force `axes = 8` — but separately none of them is "axes = 8" in
disguise.  We make this explicit by checking each axiom against the
candidate values `axes ∈ {1, 2, 4, 8, 16, …}`.

### Axiom (M1) — Squaring-tower closure (§3.7).

The carrier is the value of `RTower Bool k` for some `k`.  Equivalently,
**`axes = 2 ^ k`** for some `k : ℕ`.  This is the §3.7 operation-monism
constraint: the substrate arises by iterating the squaring functor `Σ`
on the 2-element seed `Bool`.  Each squaring doubles the *axis count*,
not the cell count: `axes(R₁) = 1, axes(R₂) = 2, axes(R₄) = 4, axes(R₈) = 8, …`.

Effect: cuts `axes ∈ {1, 2, 4, 8, 16, 32, …}`.

### Axiom (M2) — Four max-symmetric corners (§4.7bis.3, row 4).

There exist **4 distinct cells** simultaneously fixed by *both*
the palindrome involution AND the X²-self-square predicate (top half of
the bit-pattern equals bottom half).  This is the documented
`card_pal_inter_x2 = 4` count of §4.7bis.3.

On `Fin axes → Bool` with the standard bit-reverse palindrome and the
top-half/bottom-half X² predicate, the count `|IsPalindrome ∩ IsX2|`
is `2 ^ ⌈axes / 4⌉` (a palindromic X²-cell is determined by `⌈axes/4⌉`
free bits).  Requiring this count `≥ 4` therefore forces
**`⌈axes / 4⌉ ≥ 2`, i.e., `axes ≥ 5`** — in the squaring-tower lattice
`{1, 2, 4, 8, …}` this means **`axes ≥ 8`**.

This axiom is *not* "axes ≥ 8" in disguise: it is a *combinatorial
content* statement about a specific 4-cell sub-lattice that the §4.7bis
doctrinal table records.  The 4-cell minimum is doctrinally tied to the
4-element 本/征 × 形/解 fourfold of §3.5–§3.7 (each max-symmetric corner
realises one of the four fourfold-quadrant fixed points).

Effect: cuts `axes ∈ {8, 16, 32, …}` (when combined with M1).

### Axiom (M3) — Tower-depth minimality.

Among UG candidates satisfying (M1) and (M2), the substrate is at the
**least** tower depth that makes (M2) possible.  Equivalently:
`k = 3`, the unique minimal value of `k` for which `2 ^ k ≥ 8` and
`RTower Bool k` admits 4 palindromic X² corners.

This axiom is *not* "axes = 8" in disguise: it is the standard
Occam / minimality principle — the substrate is the *smallest* (M1)+(M2)
satisfier.  Without (M3) the doctrine would also admit `axes = 16, 32, …`
as legitimate UGs.

### Conclusion

(M1) + (M2) + (M3) together force **`axes = 8`** with no remaining
freedom.  The proof is a finite case-check: for each `k < 3` the
(M2) cardinality bound fails (`2 ^ ⌈2^k / 4⌉ < 4`), so the smallest
admissible tower depth is `k = 3`, hence `axes = 2^3 = 8`.

## Outcome (formal)

* `UGCandidateMinimal extends UGCandidateFace` — adds M1/M2/M3 fields.
* `wenCodeUGMinimal : UGCandidateMinimal` — the witness.
* `minimal_forces_axes_eight : ∀ U : UGCandidateMinimal, U.axes = 8` —
  the central theorem.

This closes item (a) of §4.7bis.5 modulo the doctrinal commitments
spelled out above (each is independent of "axes = 8" itself).
-/
import SSBX.Foundation.Wen.X2CodesFace

namespace SSBX.Foundation.Wen.X2Codes

open SSBX.Foundation.R

/-! ## §1  Generic bit-reverse and X²-self-square on `Fin N → Bool`

These are the two predicates whose intersection has cardinality 4 in
the §4.7bis.3 doctrinal table.  We define them *generically* on
`Fin N → Bool` so the count argument applies at any tower level. -/

/-- Generic bit-reverse on an `N`-bit pattern: bit `i` ↔ bit `N-1-i`. -/
def bitReverse {N : ℕ} (v : Fin N → Bool) : Fin N → Bool :=
  fun i => v ⟨N - 1 - i.val, by
    rcases N with _ | N
    · exact i.elim0
    · omega⟩

/-- A bit-pattern is **palindromic** iff fixed by `bitReverse`. -/
def IsPalindromeBits {N : ℕ} (v : Fin N → Bool) : Prop :=
  bitReverse v = v

instance {N : ℕ} (v : Fin N → Bool) : Decidable (IsPalindromeBits v) := by
  unfold IsPalindromeBits; infer_instance

/-- A bit-pattern is **X²-self-square** iff its top half equals its
bottom half.  For `N = 2M` even: `v i = v (M + i)` for all `i < M`.
For odd `N` the predicate is vacuously false (no clean half-split). -/
def IsX2Bits {N : ℕ} (v : Fin N → Bool) : Prop :=
  ∀ i : Fin N, ∀ h : i.val + N / 2 < N,
    v i = v ⟨i.val + N / 2, h⟩

instance {N : ℕ} (v : Fin N → Bool) : Decidable (IsX2Bits v) := by
  unfold IsX2Bits; infer_instance

instance instDecidablePalX2 {N : ℕ} (v : Fin N → Bool) :
    Decidable (IsPalindromeBits v ∧ IsX2Bits v) :=
  inferInstance

/-! ## §2  The cardinality count `|IsPal ∩ IsX2|` at small tower levels

For each candidate axis count `axes ∈ {1, 2, 4, 8}`, we verify the
count `|IsPalindromeBits ∩ IsX2Bits|`.  The 4-cell threshold is
first crossed at `axes = 8`. -/

theorem palX2_count_axes_one :
    (Finset.univ.filter
      (fun v : Fin 1 → Bool => IsPalindromeBits v ∧ IsX2Bits v)).card ≤ 2 := by
  decide

theorem palX2_count_axes_two :
    (Finset.univ.filter
      (fun v : Fin 2 → Bool => IsPalindromeBits v ∧ IsX2Bits v)).card ≤ 2 := by
  decide

theorem palX2_count_axes_four :
    (Finset.univ.filter
      (fun v : Fin 4 → Bool => IsPalindromeBits v ∧ IsX2Bits v)).card ≤ 2 := by
  decide

theorem palX2_count_axes_eight :
    (Finset.univ.filter
      (fun v : Fin 8 → Bool => IsPalindromeBits v ∧ IsX2Bits v)).card = 4 := by
  decide

/-! ## §3  `UGCandidateMinimal` — the three-axiom minimality structure

Extends `UGCandidateFace` with the squaring-tower axiom (M1), the
4-corner axiom (M2), and the minimality axiom (M3).  See module
docstring for the structural justification of each.  -/

structure UGCandidateMinimal extends UGCandidateFace where
  /-- (M1) **Squaring-tower closure** (§3.7 operation monism):
      `axes = 2 ^ tower_depth` for some `tower_depth : ℕ`. -/
  tower_depth : ℕ
  axes_eq_pow_two : axes = 2 ^ tower_depth
  /-- (M2) **Four max-symmetric corners** (§4.7bis.3 cardinality table):
      at least 4 distinct bit-cells satisfy palindrome ∧ X²-self-square.

      Cardinality-bound form — equivalent in content to the existential
      `∃ S, S.card = 4 ∧ ∀ v ∈ S, …` form, but easier for the
      `DecidablePred` resolution at construction sites. -/
  four_corners :
    4 ≤ (Finset.univ.filter
      (fun v : Fin axes → Bool => IsPalindromeBits v ∧ IsX2Bits v)).card
  /-- (M3) **Tower-depth minimality**: no smaller tower depth admits
      4 palindromic X² corners.  Equivalently: at every smaller
      `tower_depth' < tower_depth`, the count `|IsPal ∩ IsX2|` on
      `Fin (2 ^ tower_depth') → Bool` is `< 4`. -/
  tower_depth_minimal :
    ∀ k' < tower_depth,
      (Finset.univ.filter
        (fun v : Fin (2 ^ k') → Bool =>
          IsPalindromeBits v ∧ IsX2Bits v)).card < 4

/-! ## §4  The witness — `wenCodeUGMinimal`

`wenCodeUGFace` lifts to a `UGCandidateMinimal` with
`tower_depth = 3` (so `axes = 2^3 = 8`), the four documented corners
`{0, 102, 153, 255}`, and the minimality check discharged at
`k' ∈ {0, 1, 2}` by `decide`. -/

noncomputable def wenCodeUGMinimal : UGCandidateMinimal where
  toUGCandidateFace := wenCodeUGFace
  tower_depth := 3
  axes_eq_pow_two := by decide
  four_corners := le_of_eq palX2_count_axes_eight.symm
  tower_depth_minimal := by
    intro k' hk'
    interval_cases k' <;> decide

/-! ## §5  The central theorem — `minimal_forces_axes_eight`

The three axioms together force `axes = 8`.  Proof skeleton:
1. From (M1): `axes = 2 ^ tower_depth`.
2. From (M2) + (M3): `tower_depth ≥ 3` (any smaller `k'` violates the
   4-corner count by `tower_depth_minimal`, but `four_corners` provides
   4 such corners at the actual depth — so the actual depth must NOT be
   < 3, i.e., `tower_depth ≥ 3`).
3. By minimality (M3 + tower-depth-≥-3): `tower_depth = 3`.
4. Therefore `axes = 2 ^ 3 = 8`. -/

/-- (M2) directly states the cardinality lower bound. -/
theorem four_corners_count_lb (U : UGCandidateMinimal) :
    4 ≤ (Finset.univ.filter
      (fun v : Fin U.axes → Bool => IsPalindromeBits v ∧ IsX2Bits v)).card :=
  U.four_corners

/-- From (M1) + (M2): `tower_depth ≥ 3`.  At each `k' ∈ {0,1,2}`,
the count of palindromic X² patterns on `Fin (2^k') → Bool` is `≤ 2`,
so M2's lower bound of 4 cannot be met. -/
theorem tower_depth_ge_three (U : UGCandidateMinimal) : 3 ≤ U.tower_depth := by
  by_contra h
  push_neg at h
  have hlb := four_corners_count_lb U
  rw [U.axes_eq_pow_two] at hlb
  interval_cases U.tower_depth
  · -- tower_depth = 0 ⇒ axes = 1; count ≤ 2 contradicts hlb : 4 ≤ count
    have h2 : (2 : ℕ) ^ 0 = 1 := rfl
    rw [h2] at hlb
    exact absurd (le_trans hlb palX2_count_axes_one) (by decide)
  · have h2 : (2 : ℕ) ^ 1 = 2 := rfl
    rw [h2] at hlb
    exact absurd (le_trans hlb palX2_count_axes_two) (by decide)
  · have h2 : (2 : ℕ) ^ 2 = 4 := rfl
    rw [h2] at hlb
    exact absurd (le_trans hlb palX2_count_axes_four) (by decide)

/-- Symmetric upper bound: if `tower_depth > 3`, then the *witness*
`wenCodeUGMinimal` would no longer be the minimum.  Minimality (M3) +
the existence of a depth-3 solution forces `tower_depth ≤ 3`.

The argument: at `tower_depth = 3`, the count is exactly 4 (proven by
`palX2_count_axes_eight`).  For `U` to be a valid `UGCandidateMinimal`
with `tower_depth ≥ 4`, the axiom (M3) requires the count at every
`k' < tower_depth` to be `< 4`.  But at `k' = 3` the count is exactly
`4`, contradicting `4 < 4`.

This is *the load-bearing structural fact* — minimality is not just
"smallest", it is "smallest under M2's count threshold". -/
theorem tower_depth_le_three (U : UGCandidateMinimal) : U.tower_depth ≤ 3 := by
  by_contra h
  push_neg at h
  -- (M3) applied at k' = 3 < tower_depth gives count_at_3 < 4.
  have hmin := U.tower_depth_minimal 3 h
  -- But the count at k' = 3 is exactly 4 (palX2_count_axes_eight).
  rw [show (2 : ℕ) ^ 3 = 8 from rfl] at hmin
  rw [palX2_count_axes_eight] at hmin
  exact absurd hmin (by decide)

/-- **Main theorem (item (a) of §4.7bis.5 discharged).**
Every `UGCandidateMinimal` has `axes = 8`. -/
theorem minimal_forces_axes_eight (U : UGCandidateMinimal) : U.axes = 8 := by
  have hge := tower_depth_ge_three U
  have hle := tower_depth_le_three U
  have heq : U.tower_depth = 3 := Nat.le_antisymm hle hge
  rw [U.axes_eq_pow_two, heq]
  decide

/-! ## §6  Corollary — eliminating the `axes = 8` hypothesis

`X2CodesFace.face_uniqueness_conjecture` carried `U.axes = 8` as a
hypothesis.  With `minimal_forces_axes_eight` in hand, the hypothesis
is automatic for `UGCandidateMinimal`. -/

/-- The minimality-discharged form of `face_uniqueness_conjecture`:
the `axes = 8` hypothesis is no longer needed; minimality forces it. -/
def minimal_uniqueness_conjecture : Prop :=
  ∀ U : UGCandidateMinimal,
    Nonempty (UGCandidate.Iso U.toUGCandidate wenCodeUGMinimal.toUGCandidate)

/-- The cardinality precondition is now automatic.  Any `UGCandidateMinimal`
has carrier type-equivalent to `WenCode`. -/
theorem minimal_carrier_equiv_wenCode (U : UGCandidateMinimal) :
    Nonempty (U.Carrier ≃ WenCode) :=
  carrier_equiv_wenCode U.toUGCandidate (minimal_forces_axes_eight U)

/-! ## §7  Self-test -/

example : wenCodeUGMinimal.tower_depth = 3 := rfl
example : wenCodeUGMinimal.axes = 8 := rfl
example : wenCodeUGMinimal.toUGCandidate.axes = 8 := rfl
example : (3 : ℕ) ≤ wenCodeUGMinimal.tower_depth := by decide

end SSBX.Foundation.Wen.X2Codes
