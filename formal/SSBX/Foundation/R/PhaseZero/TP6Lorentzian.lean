/-
# Foundation.R.PhaseZero.TP6Lorentzian — Lorentzian-4-region bridge for T_P6

Per `docs-next/10_formal_形式/gut-roadmap.md` **Phase 0 Stream P0-B (G6.2)**:
extends `T_P6` (V₄ carrier minimality on `R 2`) with a concrete physical
realisation — the **Lorentzian causal-region partition** of an algebraic
Minkowski 4-vector.

## Bridge claim

`R 2` is the minimum non-trivial multi-modality carrier (P6).  One
canonical realisation of that 4-modality is the partition of an
(algebraic) Minkowski 4-vector `v : Fin 4 → K` (over any ordered field
`K` such as `ℝ` or `ℚ`) by its causal class:

| Region              | V₄ atom    | (content, frame) | Defining predicate                  |
|---------------------|------------|------------------|-------------------------------------|
| null / lightcone    | `Shi.dao`  | (F, F)           | `minkowski v = 0`                   |
| past-timelike       | `Shi.ji`   | (T, F)           | `minkowski v > 0 ∧ v 0 ≤ 0`        |
| spacelike           | `Shi.jin`  | (T, T)           | `minkowski v < 0`                   |
| future-timelike     | `Shi.wei`  | (F, T)           | `minkowski v > 0 ∧ v 0 > 0`        |

Here `content` = bit 0 of `Shi`, `frame` = bit 1 of `Shi` (matching the
`Atlas/Yi/Shi.lean` convention).  The mapping reads:

* `content` bit = "is **non**-null-and-non-future-timelike"
  (false on null; true on past-timelike, spacelike).
* `frame` bit   = "is **non**-null-and-non-past-timelike"
  (false on null, past-timelike; true on spacelike, future-timelike).

Equivalently: the two bits encode "in past cone?" XOR "in future cone?"
under a re-labelling of the four Lorentzian causal regions.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` Phase 0 Stream P0-B (G6.2).
* `Foundation/R/PhaseZero.lean` § 2 (`T_P6` V₄ carrier minimality).
* `Foundation/Atlas/Yi/Shi.lean` (Shi naming).

## Constraints honoured

* **No Mathlib `Geometry.Manifold.Lorentzian` dependency** — the
  Minkowski form is given by the elementary algebraic expression
  `v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2` over a parametric field `K`.
* **No new axioms** — comparisons go through `Decidable` instances
  available from `[LinearOrder K]`.
* The construction is fully algebraic and works uniformly over any
  `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`.
-/

import SSBX.Foundation.R.PhaseZero
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

-- The bridge below shares `K`-instance contexts across multiple theorems;
-- many individual theorems only need a strict subset of the instances in
-- the enclosing `section`'s `variable`, but the bundled exposure is the
-- intended interface.  The unused-section-vars linter is therefore
-- locally silenced.
set_option linter.unusedSectionVars false

namespace SSBX.Foundation.R.PhaseZero.TP6Lorentzian

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 The algebraic Minkowski form -/

/-- Algebraic Minkowski quadratic form on a 4-vector over an ordered field
    `K`, signature `(+, -, -, -)`:

        Q(v) = v₀² - v₁² - v₂² - v₃²

    Standard physics convention.  No real-analytic / manifold structure
    is used — this is *only* a polynomial in the field. -/
def minkowski {K : Type*} [Field K] (v : Fin 4 → K) : K :=
  v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2

/-! ## § 2 The Lorentzian-region bridge

We compute the V₄ atom (= `Shi` value) attached to a 4-vector by case
analysis on the sign of the Minkowski form and the sign of the time
coordinate `v 0`. -/

section Bridge

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `lorentzianRegion v` — the V₄ atom of the Lorentzian region
    containing `v : Fin 4 → K`.  See module header for the
    correspondence table.

    Computation: case on the Minkowski form, then on the time
    coordinate.  Uses classical decidability on the field (available
    from `[LinearOrder K]`). -/
noncomputable def lorentzianRegion (v : Fin 4 → K) : Shi :=
  if minkowski v = 0 then Shi.dao            -- null / lightcone
  else if 0 < minkowski v then               -- timelike
    if 0 < v 0 then Shi.wei                  -- future
    else Shi.ji                              -- past (incl. v 0 = 0 — impossible here since m > 0 ⇒ v 0 ≠ 0)
  else Shi.jin                               -- spacelike (m < 0)

/-! ### § 2.1 Region membership predicates -/

/-- A 4-vector is **null** when its Minkowski form vanishes. -/
def isNull (v : Fin 4 → K) : Prop := minkowski v = 0

/-- A 4-vector is **timelike** when its Minkowski form is positive. -/
def isTimelike (v : Fin 4 → K) : Prop := 0 < minkowski v

/-- A 4-vector is **spacelike** when its Minkowski form is negative. -/
def isSpacelike (v : Fin 4 → K) : Prop := minkowski v < 0

/-- A 4-vector is **future-timelike** when it is timelike with positive
    time coordinate. -/
def isFutureTimelike (v : Fin 4 → K) : Prop :=
  0 < minkowski v ∧ 0 < v 0

/-- A 4-vector is **past-timelike** when it is timelike with non-positive
    time coordinate (since `m > 0 ⇒ v 0 ≠ 0`, this is equivalent to
    `v 0 < 0`). -/
def isPastTimelike (v : Fin 4 → K) : Prop :=
  0 < minkowski v ∧ ¬ (0 < v 0)

/-! ### § 2.2 Region ↔ Shi correspondence theorems -/

/-- Null vectors land on `Shi.dao`. -/
theorem lorentzianRegion_null (v : Fin 4 → K) (h : isNull v) :
    lorentzianRegion v = Shi.dao := by
  unfold lorentzianRegion
  simp [isNull] at h
  simp [h]

/-- Future-timelike vectors land on `Shi.wei`. -/
theorem lorentzianRegion_future_timelike (v : Fin 4 → K)
    (h : isFutureTimelike v) : lorentzianRegion v = Shi.wei := by
  obtain ⟨hm, ht⟩ := h
  unfold lorentzianRegion
  have h_ne : minkowski v ≠ 0 := ne_of_gt hm
  simp [h_ne, hm, ht]

/-- Past-timelike vectors land on `Shi.ji`. -/
theorem lorentzianRegion_past_timelike (v : Fin 4 → K)
    (h : isPastTimelike v) : lorentzianRegion v = Shi.ji := by
  obtain ⟨hm, ht⟩ := h
  unfold lorentzianRegion
  have h_ne : minkowski v ≠ 0 := ne_of_gt hm
  simp [h_ne, hm, ht]

/-- Spacelike vectors land on `Shi.jin`. -/
theorem lorentzianRegion_spacelike (v : Fin 4 → K)
    (h : isSpacelike v) : lorentzianRegion v = Shi.jin := by
  unfold lorentzianRegion
  unfold isSpacelike at h
  have h_ne : minkowski v ≠ 0 := ne_of_lt h
  have h_not_pos : ¬ (0 < minkowski v) := not_lt.mpr (le_of_lt h)
  simp [h_ne, h_not_pos]

/-! ### § 2.3 Range / partition -/

/-- The image of `lorentzianRegion` is contained in the four Shi atoms. -/
theorem lorentzianRegion_in_atoms (v : Fin 4 → K) :
    lorentzianRegion v = Shi.dao ∨ lorentzianRegion v = Shi.ji ∨
    lorentzianRegion v = Shi.jin ∨ lorentzianRegion v = Shi.wei := by
  unfold lorentzianRegion
  by_cases h : minkowski v = 0
  · simp [h]
  · simp [h]
    by_cases h' : 0 < minkowski v
    · simp [h']
      by_cases h'' : 0 < v 0
      · simp [h'']
      · simp [h'']
    · simp [h']

end Bridge

/-! ## § 3 Canonical witnesses

We provide four canonical 4-vector witnesses — one for each Lorentzian
region — and verify they land on the expected `Shi` atom.  These witnesses
use generic field elements `0, 1 : K` so they work over any
`[Field K] [LinearOrder K] [IsStrictOrderedRing K]` and in particular
over `ℝ` and `ℚ`. -/

section Witnesses

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Canonical future-timelike witness `(1, 0, 0, 0)`: positive time
    coordinate, zero spatial part; Minkowski form `= 1 > 0`. -/
def futureTimelikeWitness : Fin 4 → K
  | ⟨0, _⟩ => 1
  | _ => 0

/-- Canonical past-timelike witness `(-1, 0, 0, 0)`: negative time
    coordinate, zero spatial part; Minkowski form `= 1 > 0`. -/
def pastTimelikeWitness : Fin 4 → K
  | ⟨0, _⟩ => -1
  | _ => 0

/-- Canonical spacelike witness `(0, 1, 0, 0)`: zero time coordinate,
    unit spatial part; Minkowski form `= -1 < 0`. -/
def spacelikeWitness : Fin 4 → K
  | ⟨1, _⟩ => 1
  | _ => 0

/-- Canonical null witness `(1, 1, 0, 0)`: equal time and spatial
    coordinates; Minkowski form `= 1 - 1 = 0`. -/
def nullWitness : Fin 4 → K
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | _ => 0

/-! ### § 3.1 Minkowski-form evaluations on witnesses -/

theorem minkowski_futureTimelikeWitness :
    minkowski (futureTimelikeWitness : Fin 4 → K) = 1 := by
  unfold minkowski futureTimelikeWitness
  ring

theorem minkowski_pastTimelikeWitness :
    minkowski (pastTimelikeWitness : Fin 4 → K) = 1 := by
  unfold minkowski pastTimelikeWitness
  ring

theorem minkowski_spacelikeWitness :
    minkowski (spacelikeWitness : Fin 4 → K) = -1 := by
  unfold minkowski spacelikeWitness
  ring

theorem minkowski_nullWitness :
    minkowski (nullWitness : Fin 4 → K) = 0 := by
  unfold minkowski nullWitness
  ring

/-! ### § 3.2 Witnesses land on the expected Shi atom -/

/-- The future-timelike witness lands on `Shi.wei`. -/
theorem lorentzianRegion_futureTimelikeWitness :
    lorentzianRegion (futureTimelikeWitness : Fin 4 → K) = Shi.wei := by
  apply lorentzianRegion_future_timelike
  refine ⟨?_, ?_⟩
  · rw [minkowski_futureTimelikeWitness]; exact one_pos
  · show (0 : K) < futureTimelikeWitness ⟨0, by decide⟩
    simp [futureTimelikeWitness]

/-- The past-timelike witness lands on `Shi.ji`. -/
theorem lorentzianRegion_pastTimelikeWitness :
    lorentzianRegion (pastTimelikeWitness : Fin 4 → K) = Shi.ji := by
  apply lorentzianRegion_past_timelike
  refine ⟨?_, ?_⟩
  · rw [minkowski_pastTimelikeWitness]; exact one_pos
  · show ¬ ((0 : K) < pastTimelikeWitness ⟨0, by decide⟩)
    -- `pastTimelikeWitness ⟨0, _⟩ = -1`; `simp` discharges `¬ (0 < -1)`.
    simp [pastTimelikeWitness]

/-- The spacelike witness lands on `Shi.jin`. -/
theorem lorentzianRegion_spacelikeWitness :
    lorentzianRegion (spacelikeWitness : Fin 4 → K) = Shi.jin := by
  apply lorentzianRegion_spacelike
  unfold isSpacelike
  rw [minkowski_spacelikeWitness]
  exact neg_one_lt_zero

/-- The null witness lands on `Shi.dao`. -/
theorem lorentzianRegion_nullWitness :
    lorentzianRegion (nullWitness : Fin 4 → K) = Shi.dao := by
  apply lorentzianRegion_null
  unfold isNull
  exact minkowski_nullWitness

end Witnesses

/-! ## § 4 The packaged T_P6 Lorentzian bridge theorem -/

/-- **T_P6.lorentzian_bridge** — the Lorentzian-4-region bridge for T_P6.

    Packages:

    1. `lorentzianRegion v` lands among the four V₄ atoms
       `{Shi.dao, Shi.ji, Shi.jin, Shi.wei}` for every Minkowski 4-vector
       `v : Fin 4 → K`.

    2. The four canonical witnesses
       `{nullWitness, pastTimelikeWitness, spacelikeWitness, futureTimelikeWitness}`
       hit each region exactly once, demonstrating the bridge is
       surjective (every V₄ atom is realised by some Lorentzian region).

    This realises the Phase 0 Stream P0-B (G6.2) deliverable: bridging
    `R 2`'s V₄ structure (from `T_P6` of `Foundation.R.PhaseZero`) to
    the Lorentzian causal structure of an algebraic 4-vector space. -/
theorem T_P6_lorentzian_bridge
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (∀ v : Fin 4 → K, lorentzianRegion v = Shi.dao
        ∨ lorentzianRegion v = Shi.ji
        ∨ lorentzianRegion v = Shi.jin
        ∨ lorentzianRegion v = Shi.wei)
  ∧ lorentzianRegion (nullWitness : Fin 4 → K) = Shi.dao
  ∧ lorentzianRegion (pastTimelikeWitness : Fin 4 → K) = Shi.ji
  ∧ lorentzianRegion (spacelikeWitness : Fin 4 → K) = Shi.jin
  ∧ lorentzianRegion (futureTimelikeWitness : Fin 4 → K) = Shi.wei :=
  ⟨lorentzianRegion_in_atoms,
   lorentzianRegion_nullWitness,
   lorentzianRegion_pastTimelikeWitness,
   lorentzianRegion_spacelikeWitness,
   lorentzianRegion_futureTimelikeWitness⟩

/-! ## § 5 (content, frame) decomposition per T_P6

The Shi atom `lorentzianRegion v` has two bits — the `(content, frame)`
decomposition from `T_P6`.  This section makes the bit-level reading
explicit. -/

section ContentFrame

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The `content` bit (= bit 0 of the Shi atom) of `lorentzianRegion v`.
    True precisely on past-timelike and spacelike vectors (= "non-null
    AND non-future-timelike"). -/
noncomputable def contentBit (v : Fin 4 → K) : Bool :=
  (lorentzianRegion v) ⟨0, by decide⟩

/-- The `frame` bit (= bit 1 of the Shi atom) of `lorentzianRegion v`.
    True precisely on spacelike and future-timelike vectors (= "non-null
    AND non-past-timelike"). -/
noncomputable def frameBit (v : Fin 4 → K) : Bool :=
  (lorentzianRegion v) ⟨1, by decide⟩

/-- The content-frame decomposition of the future-timelike region:
    `(content, frame) = (false, true)`, matching `Shi.wei`. -/
theorem contentBit_frameBit_futureTimelikeWitness :
    contentBit (futureTimelikeWitness : Fin 4 → K) = false
    ∧ frameBit (futureTimelikeWitness : Fin 4 → K) = true := by
  refine ⟨?_, ?_⟩
  · unfold contentBit
    rw [lorentzianRegion_futureTimelikeWitness]
    rfl
  · unfold frameBit
    rw [lorentzianRegion_futureTimelikeWitness]
    rfl

/-- The content-frame decomposition of the past-timelike region:
    `(content, frame) = (true, false)`, matching `Shi.ji`. -/
theorem contentBit_frameBit_pastTimelikeWitness :
    contentBit (pastTimelikeWitness : Fin 4 → K) = true
    ∧ frameBit (pastTimelikeWitness : Fin 4 → K) = false := by
  refine ⟨?_, ?_⟩
  · unfold contentBit
    rw [lorentzianRegion_pastTimelikeWitness]
    rfl
  · unfold frameBit
    rw [lorentzianRegion_pastTimelikeWitness]
    rfl

/-- The content-frame decomposition of the spacelike region:
    `(content, frame) = (true, true)`, matching `Shi.jin`. -/
theorem contentBit_frameBit_spacelikeWitness :
    contentBit (spacelikeWitness : Fin 4 → K) = true
    ∧ frameBit (spacelikeWitness : Fin 4 → K) = true := by
  refine ⟨?_, ?_⟩
  · unfold contentBit
    rw [lorentzianRegion_spacelikeWitness]
    rfl
  · unfold frameBit
    rw [lorentzianRegion_spacelikeWitness]
    rfl

/-- The content-frame decomposition of the null region:
    `(content, frame) = (false, false)`, matching `Shi.dao`. -/
theorem contentBit_frameBit_nullWitness :
    contentBit (nullWitness : Fin 4 → K) = false
    ∧ frameBit (nullWitness : Fin 4 → K) = false := by
  refine ⟨?_, ?_⟩
  · unfold contentBit
    rw [lorentzianRegion_nullWitness]
    rfl
  · unfold frameBit
    rw [lorentzianRegion_nullWitness]
    rfl

end ContentFrame

end SSBX.Foundation.R.PhaseZero.TP6Lorentzian
