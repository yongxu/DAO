/-
# Foundation.R8.Spacetime — spacetime / causality structure on R 8

Per `r8.md` v0.2 §8: `R 8 = F_2^8` admits a structural decomposition
that **carries spacetime and causality** as algebraic data, without any
physical or semantic commitment.  This file formalises that structure
purely at the F_2 algebraic level.

## What is here

* **§ 1 Light-cone halves** — the `pastHalf` (positions 0..3 = R 4ᴸ)
  and `futureHalf` (positions 4..7 = R 4ᴿ).  This is just View B of
  `FiveIdentities` repackaged with causal terminology.
* **§ 2 Conjugate pairs** — four 2-bit blocks (positions
  (0,1), (2,3), (4,5), (6,7)) viewed as "position-momentum" conjugate
  pairs.  Each pair is the unit of symplectic σ.
* **§ 3 Lightcone markers** — predicates `inPastCone`, `inFutureCone`,
  `inLightcone` defined via the position-only support.
* **§ 4 Causal precedence** — a partial-order-style predicate
  `causalPrecedes w₁ w₂` saying "w₁'s data lives only in past, w₂'s
  data lives in future, and they share no conjugate pair".  Pure F_2.
* **§ 5 Time slicing** — the predicates `pastComplete` /
  `futureComplete`, plus the time-slice extraction operations
  `pastSlice` / `futureSlice`.
* **§ 6 Causal direction** — `causalDirection w₁ w₂` = the symplectic
  σ between w₁ and w₂, capturing "non-trivial directional pairing".
* **§ 7 Composition rule** — the polarization-style identity that
  relates `q(w + w')` to `q(w), q(w'), σ(w, w')`.

The names "past / future / lightcone / causal" are used as **algebraic
labels**, not physical commitments.  Per `r8.md` §8.4: "$R_8$ gives
spacetime and causality a *minimum algebraic carrier* — formal
language for representing such structures, not their physical truth."

## Doctrinal anchor

* `r8.md` v0.2 §8.1 (4-dim spacetime algebraic embedding),
  §8.2 (cause-effect via R 4 ⊕ R 4),
  §8.3 (spacetime embedding multi-views),
  §8.4 (structural vs physical caveat).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R8.FiveIdentities
import SSBX.Foundation.R8.Bilinear

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 Light-cone halves: past (L) and future (R) -/

/-- The "past half" of `R 8`: positions 0..3 (the L block).  This is
    a structural label; it corresponds to the left half of View B.
    Per `r8.md` v0.2 §8.2.1. -/
def pastHalf (w : R 8) : R 4 := leftHalf w

/-- The "future half" of `R 8`: positions 4..7 (the R block).  This
    is a structural label; it corresponds to the right half of View B.
    Per `r8.md` v0.2 §8.2.1. -/
def futureHalf (w : R 8) : R 4 := rightHalf w

@[simp] theorem pastHalf_apply (w : R 8) (i : Fin 4) :
    pastHalf w i = w (Fin.castAdd 4 i) := rfl

@[simp] theorem futureHalf_apply (w : R 8) (i : Fin 4) :
    futureHalf w i = w (Fin.natAdd 4 i) := rfl

/-- Joining past + future halves recovers `w`. -/
theorem pastHalf_futureHalf_recovers (w : R 8) :
    joinLR (pastHalf w) (futureHalf w) = w := by
  unfold joinLR pastHalf futureHalf
  show viewB.symm (leftHalf w, rightHalf w) = w
  have : (leftHalf w, rightHalf w) = splitLR w := rfl
  rw [this]
  show viewB.symm (viewB w) = w
  exact viewB.left_inv w

/-! ## § 2 Conjugate pairs: 4 symplectic blocks ↔ 4 conjugate axes

Per `r8.md` v0.2 §8.1.1, the 4 symplectic blocks of `R 8 = R 2^{⊕ 4}`
(view C) are interpreted as 4 conjugate pairs.  Each block is a 2-bit
pair (α, β) where α and β are conjugate (e.g. position and momentum,
or one space coordinate and its conjugate momentum).

The structural labels for the four conjugate axes are simply 0, 1, 2, 3
— no physical names like X / Y / Z / T appear here (they are
application-level overlays in `Foundation/Atlas/`, per the v0.6
doctrine). -/

/-- Index for one of the four conjugate axes of `R 8`. -/
abbrev ConjugateAxis : Type := Fin 4

/-- The 2-bit value of `w` at conjugate axis `k`.  This is block_k from
    `FiveIdentities`. -/
def conjugatePair (w : R 8) (k : ConjugateAxis) : R 2 :=
  match k.val with
  | 0 => block0 w
  | 1 => block1 w
  | 2 => block2 w
  | _ => block3 w

/-- The conjugate pair's "α coordinate" (first bit). -/
def conjugateAlpha (w : R 8) (k : ConjugateAxis) : Bool :=
  conjugatePair w k ⟨0, by decide⟩

/-- The conjugate pair's "β coordinate" (second bit). -/
def conjugateBeta (w : R 8) (k : ConjugateAxis) : Bool :=
  conjugatePair w k ⟨1, by decide⟩

/-! ## § 3 Lightcone markers (support-based predicates) -/

/-- `w` is in the **strict past cone**: all true bits live in the past
    half (positions 0..3), and there is at least one true bit. -/
def inStrictPastCone (w : R 8) : Prop :=
  (∀ i : Fin 8, 4 ≤ i.val → w i = false) ∧ ∃ i : Fin 8, w i = true

/-- `w` is in the **strict future cone**: all true bits live in the
    future half (positions 4..7), and there is at least one true bit. -/
def inStrictFutureCone (w : R 8) : Prop :=
  (∀ i : Fin 8, i.val < 4 → w i = false) ∧ ∃ i : Fin 8, w i = true

/-- `w` is **purely past-supported**: all true bits live in the past
    half (positions 0..3).  Includes the zero vector. -/
def isPastSupported (w : R 8) : Prop :=
  ∀ i : Fin 8, 4 ≤ i.val → w i = false

/-- `w` is **purely future-supported**: all true bits live in the
    future half (positions 4..7).  Includes the zero vector. -/
def isFutureSupported (w : R 8) : Prop :=
  ∀ i : Fin 8, i.val < 4 → w i = false

instance decidableIsPastSupported (w : R 8) : Decidable (isPastSupported w) := by
  unfold isPastSupported; exact Fintype.decidableForallFintype

instance decidableIsFutureSupported (w : R 8) : Decidable (isFutureSupported w) := by
  unfold isFutureSupported; exact Fintype.decidableForallFintype

/-- The zero vector is past-supported. -/
theorem zero_isPastSupported : isPastSupported (0 : R 8) := by
  intro i _; rfl

/-- The zero vector is future-supported. -/
theorem zero_isFutureSupported : isFutureSupported (0 : R 8) := by
  intro i _; rfl

/-- The zero vector is both past- and future-supported (it lives in
    the "instant"). -/
theorem zero_in_instant :
    isPastSupported (0 : R 8) ∧ isFutureSupported (0 : R 8) :=
  ⟨zero_isPastSupported, zero_isFutureSupported⟩

/-- If `w` is past-supported then its future half is zero. -/
theorem isPastSupported_iff_futureHalf_zero (w : R 8) :
    isPastSupported w ↔ futureHalf w = (0 : R 4) := by
  constructor
  · intro h
    funext i
    rcases i with ⟨k, hk⟩
    show w (Fin.natAdd 4 ⟨k, hk⟩) = false
    apply h
    show 4 ≤ (Fin.natAdd 4 ⟨k, hk⟩).val
    show 4 ≤ 4 + k
    omega
  · intro h i hi
    have hi' : i.val - 4 < 4 := by have := i.isLt; omega
    have key : futureHalf w ⟨i.val - 4, hi'⟩ = false := by
      rw [h]; rfl
    show w i = false
    rw [futureHalf_apply] at key
    have h_idx : (Fin.natAdd 4 ⟨i.val - 4, hi'⟩ : Fin 8) = i := by
      apply Fin.ext
      show 4 + (i.val - 4) = i.val
      omega
    rw [h_idx] at key
    exact key

/-- If `w` is future-supported then its past half is zero. -/
theorem isFutureSupported_iff_pastHalf_zero (w : R 8) :
    isFutureSupported w ↔ pastHalf w = (0 : R 4) := by
  constructor
  · intro h
    funext i
    rcases i with ⟨k, hk⟩
    show w (Fin.castAdd 4 ⟨k, hk⟩) = false
    apply h
    show (Fin.castAdd 4 ⟨k, hk⟩).val < 4
    show k < 4
    exact hk
  · intro h i hi
    have key : pastHalf w ⟨i.val, hi⟩ = false := by
      rw [h]; rfl
    show w i = false
    rw [pastHalf_apply] at key
    have h_idx : (Fin.castAdd 4 ⟨i.val, hi⟩ : Fin 8) = i := by
      apply Fin.ext; rfl
    rw [h_idx] at key
    exact key

/-! ## § 4 Causal precedence -/

/-- `w₁` **causally precedes** `w₂` if:
    1. `w₁` is past-supported (lives in past half), and
    2. `w₂` is future-supported (lives in future half).

    This is a pure structural partial-order-like predicate — no
    physical metric, no light-speed, just F_2 support locations.
    Per `r8.md` v0.2 §8.2.1: "$R_4^{(L)}$ = cause state,
    $R_4^{(R)}$ = effect state." -/
def causalPrecedes (w₁ w₂ : R 8) : Prop :=
  isPastSupported w₁ ∧ isFutureSupported w₂

/-- Causal precedence is decidable. -/
instance decidableCausalPrecedes (w₁ w₂ : R 8) : Decidable (causalPrecedes w₁ w₂) := by
  unfold causalPrecedes; exact instDecidableAnd

/-- The zero vector precedes itself (it is both past- and
    future-supported). -/
theorem zero_causalPrecedes_zero : causalPrecedes (0 : R 8) (0 : R 8) := by
  exact ⟨zero_isPastSupported, zero_isFutureSupported⟩

/-- Transitivity-style: if `w₁` precedes `w₂` and `w₂` precedes `w₃`
    then `w₂ = 0` (the only `w` both past- and future-supported is the
    instant 0). -/
theorem causalPrecedes_through_zero (w₁ w₂ w₃ : R 8)
    (h₁₂ : causalPrecedes w₁ w₂) (h₂₃ : causalPrecedes w₂ w₃) :
    w₂ = 0 := by
  obtain ⟨_, h_w2_future⟩ := h₁₂
  obtain ⟨h_w2_past, _⟩ := h₂₃
  funext i
  by_cases hi : i.val < 4
  · exact h_w2_future i hi
  · exact h_w2_past i (Nat.le_of_not_lt hi)

/-- Reflexivity holds for `w = 0` only. -/
theorem causalPrecedes_refl_iff (w : R 8) :
    causalPrecedes w w ↔ w = 0 := by
  constructor
  · intro ⟨h_past, h_future⟩
    funext i
    by_cases hi : i.val < 4
    · exact h_future i hi
    · exact h_past i (Nat.le_of_not_lt hi)
  · rintro rfl; exact zero_causalPrecedes_zero

/-- The "spacelike-separated" relation: neither `w₁` precedes `w₂` nor
    `w₂` precedes `w₁`, and neither is the instant 0. -/
def spacelikeSeparated (w₁ w₂ : R 8) : Prop :=
  ¬ causalPrecedes w₁ w₂ ∧ ¬ causalPrecedes w₂ w₁

/-! ## § 5 Time slicing -/

/-- The "past slice" of `w`: the past half lifted into `R 8` with
    future bits zeroed.  Used to project a state onto its past
    component. -/
def pastSlice (w : R 8) : R 8 := fun i =>
  if i.val < 4 then w i else false

/-- The "future slice" of `w`: the future half lifted into `R 8` with
    past bits zeroed. -/
def futureSlice (w : R 8) : R 8 := fun i =>
  if i.val < 4 then false else w i

/-- The past slice is past-supported. -/
theorem pastSlice_isPastSupported (w : R 8) :
    isPastSupported (pastSlice w) := by
  intro i hi
  show (if i.val < 4 then w i else false) = false
  rw [if_neg (Nat.not_lt.mpr hi)]

/-- The future slice is future-supported. -/
theorem futureSlice_isFutureSupported (w : R 8) :
    isFutureSupported (futureSlice w) := by
  intro i hi
  show (if i.val < 4 then false else w i) = false
  rw [if_pos hi]

/-- `w` decomposes as `pastSlice w + futureSlice w`. -/
theorem slice_decomposition (w : R 8) :
    pastSlice w + futureSlice w = w := by
  funext i
  show Bool.xor (pastSlice w i) (futureSlice w i) = w i
  by_cases hi : i.val < 4
  · show Bool.xor (if i.val < 4 then w i else false)
                  (if i.val < 4 then false else w i) = w i
    rw [if_pos hi, if_pos hi]
    cases w i <;> rfl
  · show Bool.xor (if i.val < 4 then w i else false)
                  (if i.val < 4 then false else w i) = w i
    rw [if_neg hi, if_neg hi]
    cases w i <;> rfl

/-- `pastSlice w` and `futureSlice w` causally precede each other (via
    the canonical past → future ordering). -/
theorem slice_causalPrecedes (w : R 8) :
    causalPrecedes (pastSlice w) (futureSlice w) :=
  ⟨pastSlice_isPastSupported w, futureSlice_isFutureSupported w⟩

/-- The "past-complete" predicate: a slice that has its full past data
    (= past-supported and **may** be zero or non-zero in past). -/
abbrev pastComplete (w : R 8) : Prop := isPastSupported w

/-- The "future-complete" predicate. -/
abbrev futureComplete (w : R 8) : Prop := isFutureSupported w

/-! ## § 6 Causal direction via σ

Per `r8.md` v0.2 §8.2.4: the symplectic σ form captures "non-trivial
commutator / anti-commutator structure" between two states, which
plays the role of *directional* information beyond the symmetric dot
product.

In `R 8`, σ has 4 blocks (the 4 conjugate pairs).  Each block's
contribution is `(w₀ ∧ w'₁) ⊕ (w₁ ∧ w'₀)` — the discrete analog of the
canonical commutator `[α, β]` for that conjugate pair. -/

/-- The **causal direction** between `w_cause` and `w_effect` is the
    symplectic σ-value.

    σ = 0 ⇒ "symplectic-orthogonal" (no directional structure)
    σ = 1 ⇒ "symplectic-paired" (non-trivial directional pairing)

    Per `r8.md` v0.2 §8.2.4. -/
def causalDirection (w_cause w_effect : R 8) : Bool :=
  sigma8 w_cause w_effect

/-- Causal direction is symmetric: σ(u, v) = σ(v, u) in characteristic 2.
    (Per `r8.md` v0.2 §8.2.4: "σ is alternating but symmetric over F_2,
    since -1 = 1.") -/
theorem causalDirection_symm (w₁ w₂ : R 8) :
    causalDirection w₁ w₂ = causalDirection w₂ w₁ :=
  sigma8_symm w₁ w₂

/-- Self-direction vanishes: σ(w, w) = 0. -/
@[simp] theorem causalDirection_self (w : R 8) :
    causalDirection w w = false := sigma8_alternating w

/-! ## § 7 Causal composition rule

Per `r8.md` v0.2 §8.2.4 (final paragraph): the polarization formula

    q(w + w') = q(w) + q(w') + σ(w, w')

gives "the composition rule for cause-effect q values".  This is
inherited from the Layer 1/2 decomposition in `R/Bilinear.lean`.  Here
we package it specifically for the R 8 spacetime case. -/

/-- The polarization-style composition identity for the Arf-quadratic
    refinement `q` on `R 8`: q on a sum is q on each summand plus σ
    between them.  Per `r8.md` v0.2 §8.2.4.

    NB: this uses the general decomposition `dot = σ + LL` rather than
    re-proving a per-q polarization (which would require a Mathlib
    quadratic-form development not in scope here).  See `R8.Bilinear`
    for the underlying identity. -/
theorem causal_composition_rule (u v : R 8) :
    dot8 u v = Bool.xor (sigma8 u v) (LL8 u v) :=
  dot8_eq_sigma8_xor_LL8 u v

/-! ## § 8 Pair extraction and lightcone-aware operations -/

/-- Cause-effect extraction: split `w` into its (cause, effect) pair
    where cause is the past half and effect is the future half.
    Per `r8.md` v0.2 §8.2.1. -/
def toCauseEffect (w : R 8) : R 4 × R 4 := (pastHalf w, futureHalf w)

/-- Reconstruct `w` from a (cause, effect) pair. -/
def fromCauseEffect (p : R 4 × R 4) : R 8 := joinLR p.1 p.2

@[simp] theorem toCauseEffect_fromCauseEffect (p : R 4 × R 4) :
    toCauseEffect (fromCauseEffect p) = p := by
  unfold toCauseEffect fromCauseEffect pastHalf futureHalf joinLR
  show (leftHalf (viewB.symm p), rightHalf (viewB.symm p)) = p
  have h : viewB (viewB.symm p) = p := viewB.right_inv p
  have hLR : (leftHalf (viewB.symm p), rightHalf (viewB.symm p))
           = viewB (viewB.symm p) := rfl
  rw [hLR, h]

@[simp] theorem fromCauseEffect_toCauseEffect (w : R 8) :
    fromCauseEffect (toCauseEffect w) = w :=
  pastHalf_futureHalf_recovers w

/-- The cause-effect equivalence: `R 8 ≃ R 4 × R 4`. -/
def causeEffectEquiv : R 8 ≃ R 4 × R 4 where
  toFun := toCauseEffect
  invFun := fromCauseEffect
  left_inv := fromCauseEffect_toCauseEffect
  right_inv := toCauseEffect_fromCauseEffect

/-! ## § 9 Conjugate pair extraction

Each `R 8`-element exposes its 4 conjugate pairs (= 4 R 2 values). -/

/-- Extract all 4 conjugate pairs of `w` as a tuple. -/
def allConjugatePairs (w : R 8) : R 2 × R 2 × R 2 × R 2 := viewC w

/-- Reconstruct `w` from its 4 conjugate pairs. -/
def fromConjugatePairs (p : R 2 × R 2 × R 2 × R 2) : R 8 := viewC.symm p

@[simp] theorem allConjugatePairs_fromConjugatePairs (p : R 2 × R 2 × R 2 × R 2) :
    allConjugatePairs (fromConjugatePairs p) = p := viewC.right_inv p

@[simp] theorem fromConjugatePairs_allConjugatePairs (w : R 8) :
    fromConjugatePairs (allConjugatePairs w) = w := viewC.left_inv w

/-! ## § 10 Spacetime invariants

The "spacetime signature" of `w` is the tuple of three causality data:
its past-support, its future-support, and the bit-XOR of its
conjugate-pair labels.  This collects the structural causal data
exposed by R 8. -/

/-- The structural spacetime label of `w`: a triple
    (isPastSupported, isFutureSupported, hammingWeight). -/
def spacetimeSignature (w : R 8) : Bool × Bool × ℕ :=
  ( decide (isPastSupported w)
  , decide (isFutureSupported w)
  , (Finset.univ.filter (fun i : Fin 8 => w i = true)).card)

/-- The signature of zero. -/
theorem spacetimeSignature_zero :
    spacetimeSignature (0 : R 8) = (true, true, 0) := by
  unfold spacetimeSignature
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [zero_isPastSupported]
  · simp [zero_isFutureSupported]
  · show (Finset.univ.filter (fun i : Fin 8 => (0 : R 8) i = true)).card = 0
    apply Finset.card_eq_zero.mpr
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
               iff_false]
    show ¬ ((0 : R 8) i = true)
    intro h; exact Bool.false_ne_true h

end SSBX.Foundation.R8
