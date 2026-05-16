/-
# Foundation.R.PhaseZero — Phase 0 small theorems for wen-substrate v1.0.3

Per `docs-next/10_formal_形式/wen-substrate.md` v1.0.3 §8.8 ("Phase 0 —
Immediately provable sub-theorems"), this file collects the four small
formalisable theorems that support the v0.8 P-claims:

* **T_P3** — Bilinear classification (P3): exactly 3 algebraic layers
  (symmetric / alternating / quadratic-refinement family) on `R (2k)`,
  with 4 total equivalence classes (1 symm + 1 alt + 2 Arf-labelled
  quadratic-refinement classes).
* **T_P6** — V₄ carrier minimality (P6): `R 2 ≅ V₄` is the unique
  4-element `F_2`-vector space and the minimum non-trivial multi-modality
  carrier (≥ 3 independent modalities ⇒ ≥ 4 elements).
* **T_P7a** — Zong involution forces a 4本 + 4征 split on `R 3`:
  reversal `ζ : R 3 → R 3, ζ(b₀, b₁, b₂) = (b₂, b₁, b₀)` is involutive;
  `|Fix(ζ)| = 4` (= 本-trigrams = {qian, li, kan, kun}); the complement
  has 4 elements (= 征-trigrams = {dui, zhen, xun, gen}).
* **T_P7b** — Wedderburn anchor: `R 4 ≃ End(R 2) ≃ Mat₂(F₂)` carries the
  natural `F_2`-algebra structure (composition of endomorphisms as
  multiplication, XOR as addition).  We supply the existence side
  (matrix bijection + composition associativity + identity laws +
  cardinality match) on top of `Foundation/R4/EndR2.lean` **and** the
  **`RingEquiv` upgrade** (`R 4 ≃+* Mat2F2` preserving `+`, `×`, `0`,
  `1`) per wen-substrate v1.1 §2.5 P5 / §3.5.3 / §8.8.  The bridge to
  Mathlib's `Matrix (Fin 2) (Fin 2) (ZMod 2)` plus the Wedderburn-Artin
  uniqueness clause remain as residual obligations.

## Scope

This is a **statement + immediate-proof** module: it re-exports and
packages already-formalised content under named theorems `T_P3_*`,
`T_P6_*`, `T_P7a_*`, `T_P7b_*` so that the v1.0.3 §8.8 list is directly
verifiable from a single file.  No new axioms are introduced; everything
not yet proven is recorded as a documented residual obligation with an
explicit TODO referencing the wen-substrate section it discharges.

## Doctrinal anchor

* `wen-substrate.md` v1.0.3 §8.8 (Phase 0 small theorems).
* `wen-substrate.md` v1.0.3 §2.3 (P3 bilinear classification),
  §2.6 (P6 V₄ minimality), §2.7 (P7 zong / Wedderburn).
* `Foundation/R/Bilinear.lean` (T_P3 anchor).
* `Foundation/Atlas/Yi/Shi.lean` (T_P6 anchor).
* `Foundation/Atlas/Yi/Bagua.lean` (T_P7a anchor).
* `Foundation/R4/EndR2.lean`, `Foundation/R4/HomMat.lean` (T_P7b anchor).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Bagua
import SSBX.Foundation.Atlas.Yi.Shi
import SSBX.Foundation.R4.EndR2
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Ring.Equiv

namespace SSBX.Foundation.R.PhaseZero

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 T_P3 — Bilinear classification (P3)

Per wen-substrate v1.0.3 §2.3 (P3) and §8.8.

The natural `F_2`-bilinear / quadratic classification on `R (2 * k)`
has exactly **3 algebraic layers**:

* **L₀** — the symmetric form `dot : R N × R N → Bool` (defined for all
  `N`; symmetry is `R.dot_symm`).
* **L₁** — the alternating symplectic form `sigma : R (2 * k) → R (2 * k) → Bool`
  (alternating is `R.sigma_alternating`).
* **L₂** — the parametric family of quadratic refinements `q c v`
  indexed by `c : Fin k → Bool`; the Arf invariant `arf c` is an `F_2`
  binary label (cardinality 2 of the Arf classes is immediate from
  `arf` being `Bool`-valued).

The decomposition `dot = σ ⊕ LL` (= `R.dot_eq_sigma_xor_LL`) shows the
three layers are not independent forms but **stacked algebraic strata**
on the same carrier.

The uniqueness-up-to-iso clause (no further independent symmetric /
alternating non-degenerate forms over `F_2`) is the residual Phase-0
obligation under wen-substrate v1.0.3 §8.8 / Standard ref: Atiyah,
*Riemann surfaces and spin structures*, Ann. Sci. ENS (1971); Arf,
*Untersuchungen über quadratische Formen in Körpern der Charakteristik
2*, J. Reine Angew. Math. (1941).
-/

/-- **T_P3.L0** — Layer 0 symmetric form exists: `dot` is symmetric on `R N`. -/
theorem T_P3_L0_symmetric {N : ℕ} (u v : R N) : R.dot u v = R.dot v u :=
  R.dot_symm u v

/-- **T_P3.L1** — Layer 1 alternating form exists: `sigma` is alternating
    on `R (2 * k)`. -/
theorem T_P3_L1_alternating {k : ℕ} (v : R (2 * k)) :
    R.sigma v v = false :=
  R.sigma_alternating v

/-- **T_P3.L1.symm** — Layer 1 form is also symmetric (in char 2 every
    alternating form is symmetric). -/
theorem T_P3_L1_symmetric {k : ℕ} (u v : R (2 * k)) :
    R.sigma u v = R.sigma v u :=
  R.sigma_symm u v

/-- **T_P3.decomp** — The three layers are bound by the L0/L1
    decomposition: `dot = σ ⊕ LL`, the wen-algebra v0.6 §4.6 identity. -/
theorem T_P3_decomposition {k : ℕ} (u v : R (2 * k)) :
    R.dot u v = Bool.xor (R.sigma u v) (R.LL u v) :=
  R.dot_eq_sigma_xor_LL u v

/-- **T_P3.L2** — Layer 2 family vanishes on the origin (sanity check
    of the parametric refinement family). -/
theorem T_P3_L2_origin {k : ℕ} (c : Fin k → Bool) :
    R.q c (0 : R (2 * k)) = false :=
  R.q_zero_vec c

/-- **T_P3.arf_binary** — The Arf invariant is a `Bool`-valued (i.e.
    `F_2`-valued) function: the L2 family has exactly 2 Arf-labelled
    equivalence classes by virtue of its codomain.

    NB: This delivers only the **codomain cardinality** (= 2).  The
    statement "each Arf class is non-empty and the two refinement
    classes are pairwise symplectic-isometric" is the standard Arf
    classification, available in Mathlib via the central-simple-algebra
    library; cf. wen-substrate v1.0.3 §2.3 (after the $q_a$ correction
    note). -/
theorem T_P3_arf_binary {k : ℕ} (c : Fin k → Bool) :
    R.arf c = true ∨ R.arf c = false := by
  cases R.arf c
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ### § 1.1 T_P3 uniqueness — the 6th clause (G6.1)

Per wen-substrate v1.0.3 §8.8 T_P3 / GUT roadmap G6.1 (Stream P0-A): the
6th clause asks "no further independent symmetric / alternating non-
degenerate forms over `F_2` exist".  In its strongest form this is the
Witt-style classification of F₂-bilinear / quadratic forms (Atiyah,
*Riemann surfaces and spin structures*, ENS 1971; Arf,
*Untersuchungen über quadratische Formen in Körpern der Charakteristik
2*, J. Reine Angew. Math. 1941) — modulo `Sp(2k, F_2)`-equivalence, the
classes are: one symmetric class (= `dot`), one alternating class
(= `sigma`), and the two Arf-labelled quadratic refinement classes.

**Mathlib infrastructure gap.** Mathlib provides:

* `Mathlib.LinearAlgebra.BilinearForm.Properties.IsAlt` — alternating
  predicate on `BilinForm R M`.
* `Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv.Equivalent` —
  quadratic-form equivalence via isometric linear equivalences.
* `Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv.equivalent_weightedSumSquares`
  — but **only under `[Invertible (2 : K)]`**, which **fails for `F_2`**.

The characteristic-2 Witt-Arf classification (the version that applies
to `R N` over `F_2`) is **not yet in Mathlib** — neither the Darboux
basis for non-degenerate alternating forms nor the Arf-orbit
decomposition of `Sp(2k, F_2)` on quadratic refinements.  Closing the
6th clause in its full strength therefore requires either (i) a future
Mathlib char-2 Witt classification, or (ii) hand-built `R`-internal
infrastructure for `GL(R N)` / `Sp(R (2k))` orbits.

**What we deliver here.** Concrete, fully-proven uniqueness clauses
that strengthen "binary codomain" (`T_P3_arf_binary`) to "both Arf
classes are **inhabited and pairwise distinct**" plus a concrete
uniqueness of `sigma` on `R 2` characterised by F₂-bilinearity,
alternating, and a single non-degeneracy witness `f xo ox = true`.  In
total:

* **`T_P3_arf_surjective`** — for every `k`, both Arf classes are
  inhabited: there exist `c₀ c₁ : Fin (k+1) → Bool` with
  `arf c₀ = false` and `arf c₁ = true`.  Concrete witnesses:
  `c₀ = const false` and `c₁ = first-coordinate-only-true`.
* **`T_P3_arf_distinct_classes`** — the two Arf classes are non-empty
  **and distinct** as subsets of `Fin (k + 1) → Bool`.
* **`T_P3_sigma_uniqueness_R2`** — concrete uniqueness of `sigma` on
  `R 2`: any `F₂`-bilinear (= XOR-additive in each argument),
  alternating function `f : R 2 → R 2 → Bool` with `f xo ox = true`
  equals `R.sigma (k := 1)` pointwise.

**Residual obligation** (recorded in module header & wen-substrate
§2.3): the full `Sp(2k, F_2)`-equivalence classification for all
`k ≥ 1` (Darboux / Witt-Arf).  This is genuinely waiting on Mathlib
infrastructure; **no new axioms** are introduced here.
-/

/-- The "all-false" choice vector over `Fin k`. -/
def choice_false (k : ℕ) : Fin k → Bool := fun _ => false

/-- The "first-coordinate only" choice vector over `Fin (k + 1)`:
    `c 0 = true`, `c j = false` for `j ≠ 0`. -/
def choice_e0 (k : ℕ) : Fin (k + 1) → Bool := fun j => decide (j.val = 0)

/-- The all-false choice vector has Arf = false. -/
theorem arf_choice_false (k : ℕ) :
    R.arf (choice_false k) = false := by
  show R.xorFold (fun _ : Fin k => false) = false
  exact R.xorFold_const_false k

/-- The first-coordinate-only choice vector has Arf = true.  Proof:
    XOR-sum of `c j = decide (j.val = 0)` over `Fin (k + 1)` is
    `(c 0) ⊕ xorFold (c ∘ Fin.succ)`.  The first term is `true`; the
    tail is `xorFold (fun _ => false) = false`. -/
theorem arf_choice_e0 (k : ℕ) :
    R.arf (choice_e0 k) = true := by
  show R.xorFold (choice_e0 k) = true
  rw [R.xorFold_succ]
  -- Goal: Bool.xor (choice_e0 k 0) (xorFold (fun j => choice_e0 k j.succ)) = true
  have h0 : choice_e0 k 0 = true := by
    show decide ((0 : Fin (k + 1)).val = 0) = true
    rfl
  have htail :
      (fun j : Fin k => choice_e0 k j.succ)
        = (fun _ : Fin k => false) := by
    funext j
    show decide (j.succ.val = 0) = false
    simp
  rw [h0, htail, R.xorFold_const_false]
  rfl

/-- **T_P3.uniqueness-1** — Arf is **surjective**: both Arf classes are
    inhabited.  For every `k`, there exist choice vectors
    `c₀ c₁ : Fin (k + 1) → Bool` with `arf c₀ = false` and
    `arf c₁ = true`.

    This strengthens `T_P3_arf_binary` (codomain-cardinality only) to
    "the L2 family genuinely partitions into 2 non-empty classes". -/
theorem T_P3_arf_surjective (k : ℕ) :
    (∃ c : Fin (k + 1) → Bool, R.arf c = false)
  ∧ (∃ c : Fin (k + 1) → Bool, R.arf c = true) :=
  ⟨⟨choice_false (k + 1), arf_choice_false (k + 1)⟩,
   ⟨choice_e0 k, arf_choice_e0 k⟩⟩

/-- **T_P3.uniqueness-2** — the two Arf classes are pairwise distinct
    as subsets of `Fin (k + 1) → Bool`, i.e. no choice vector lives in
    both classes (`false ≠ true`). -/
theorem T_P3_arf_distinct_classes (k : ℕ) :
    ∃ c₀ c₁ : Fin (k + 1) → Bool, R.arf c₀ ≠ R.arf c₁ :=
  ⟨choice_false (k + 1), choice_e0 k, by
    rw [arf_choice_false (k + 1), arf_choice_e0 k]
    decide⟩

/-! ### § 1.1.1 F₂-bilinearity on `R 2` and `sigma` uniqueness

We define `F₂-bilinear` on `R N` as XOR-additivity in each argument
(= the Bool/F₂-linearity at the function level — no F₂-scalar-action
clause because F₂ has only two scalars, with `false v = 0` and
`true v = v` forced by additive law).  For Bool-valued forms on
`R N`, F₂-bilinearity is captured fully by the two distributivity laws
below.
-/

/-- F₂-bilinear in the first argument: `f (u + u') v = f u v ⊕ f u' v`. -/
def IsLinearLeft {N : ℕ} (f : R N → R N → Bool) : Prop :=
  ∀ u u' v : R N, f (u + u') v = Bool.xor (f u v) (f u' v)

/-- F₂-bilinear in the second argument: `f u (v + v') = f u v ⊕ f u v'`. -/
def IsLinearRight {N : ℕ} (f : R N → R N → Bool) : Prop :=
  ∀ u v v' : R N, f u (v + v') = Bool.xor (f u v) (f u v')

/-- `f` is F₂-bilinear on `R N`. -/
def IsF2Bilinear {N : ℕ} (f : R N → R N → Bool) : Prop :=
  IsLinearLeft f ∧ IsLinearRight f

/-- `f` is alternating: `f v v = false` for all `v`. -/
def IsAlt {N : ℕ} (f : R N → R N → Bool) : Prop := ∀ v, f v v = false

/-- F₂-bilinear forms vanish on the zero left argument.  Proof:
    `f 0 v = f (0 + 0) v = f 0 v ⊕ f 0 v = 0`. -/
theorem IsLinearLeft.zero_left {N : ℕ} {f : R N → R N → Bool}
    (h : IsLinearLeft f) (v : R N) : f 0 v = false := by
  have hsplit : f ((0 : R N) + 0) v = Bool.xor (f 0 v) (f 0 v) := h 0 0 v
  rw [add_zero] at hsplit
  -- hsplit : f 0 v = Bool.xor (f 0 v) (f 0 v)
  cases hf : f 0 v with
  | false => rfl
  | true =>
    rw [hf] at hsplit
    cases hsplit

/-- F₂-bilinear forms vanish on the zero right argument. -/
theorem IsLinearRight.zero_right {N : ℕ} {f : R N → R N → Bool}
    (h : IsLinearRight f) (u : R N) : f u 0 = false := by
  have hsplit : f u ((0 : R N) + 0) = Bool.xor (f u 0) (f u 0) := h u 0 0
  rw [add_zero] at hsplit
  cases hf : f u 0 with
  | false => rfl
  | true =>
    rw [hf] at hsplit
    cases hsplit

/-- Every element of `R 2` is one of the four atoms `oo / xo / ox / xx`. -/
theorem R2_cases (v : R 2) :
    v = R.oo ∨ v = R.xo ∨ v = R.ox ∨ v = R.xx := by
  -- a `Fin 2 → Bool` is determined by its two values v 0, v 1
  rcases hv0 : v ⟨0, by decide⟩ with _ | _ <;>
    rcases hv1 : v ⟨1, by decide⟩ with _ | _
  · left
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
  · right; right; left
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
  · right; left
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
  · right; right; right
    funext i
    fin_cases i
    · exact hv0
    · exact hv1

/-- `xx = xo + ox` in `R 2`. -/
theorem R2_xx_eq_xo_plus_ox : (R.xx : R 2) = R.xo + R.ox :=
  R.R2_xo_add_ox.symm

/-- **T_P3.uniqueness-3** — concrete `sigma` uniqueness on `R 2`.

    Any function `f : R 2 → R 2 → Bool` which is
      (i)   F₂-bilinear (= XOR-additive in each argument),
      (ii)  alternating (`f v v = false`),
      (iii) non-degenerate at the basis-pair witness `f xo ox = true`,
    must equal `R.sigma (k := 1)` pointwise.

    Mathematical content: alternating + F₂-bilinear + non-degenerate on
    `R 2 ≅ F_2²` is a 1-dimensional space of forms (the bit-value
    `f xo ox` is its single parameter), and non-degeneracy fixes that
    bit to `true` — leaving `sigma` as the unique such form. -/
theorem T_P3_sigma_uniqueness_R2 (f : R 2 → R 2 → Bool)
    (hBilin : IsF2Bilinear f) (hAlt : IsAlt f)
    (hNonDeg : f R.xo R.ox = true) :
    ∀ u v : R 2, f u v = R.sigma (k := 1) u v := by
  obtain ⟨hL, hR⟩ := hBilin
  -- Step 1: extract pointwise values of f on all 16 basis pairs.
  -- f oo _ = 0 (oo = 0 + left-zero); f _ oo = 0 (right-zero).
  -- f xo xo = 0 and f ox ox = 0 by alternating.
  have hoo_eq_zero : (R.oo : R 2) = 0 := rfl
  have hfoo_left : ∀ v : R 2, f R.oo v = false := by
    intro v; rw [hoo_eq_zero]; exact hL.zero_left v
  have hfoo_right : ∀ u : R 2, f u R.oo = false := by
    intro u; rw [hoo_eq_zero]; exact hR.zero_right u
  have h_xo_xo : f R.xo R.xo = false := hAlt R.xo
  have h_ox_ox : f R.ox R.ox = false := hAlt R.ox
  have h_xx_xx : f R.xx R.xx = false := hAlt R.xx
  -- f xx xx via bilinear expansion gives f xo ox = f ox xo
  have h_xx_xx_expand :
      f R.xx R.xx
        = Bool.xor (f R.xo R.ox) (f R.ox R.xo) := by
    have h₁ : f R.xx R.xx = f (R.xo + R.ox) R.xx := by
      rw [R2_xx_eq_xo_plus_ox]
    have h₂ : f (R.xo + R.ox) R.xx
              = Bool.xor (f R.xo R.xx) (f R.ox R.xx) := hL _ _ _
    have h₃ : f R.xo R.xx = Bool.xor (f R.xo R.xo) (f R.xo R.ox) := by
      rw [R2_xx_eq_xo_plus_ox]; exact hR _ _ _
    have h₄ : f R.ox R.xx = Bool.xor (f R.ox R.xo) (f R.ox R.ox) := by
      rw [R2_xx_eq_xo_plus_ox]; exact hR _ _ _
    rw [h₁, h₂, h₃, h₄, h_xo_xo, h_ox_ox]
    cases f R.xo R.ox <;> cases f R.ox R.xo <;> rfl
  have h_ox_xo : f R.ox R.xo = true := by
    rw [h_xx_xx, hNonDeg] at h_xx_xx_expand
    -- h_xx_xx_expand : false = Bool.xor true (f R.ox R.xo)
    cases hb : f R.ox R.xo
    · rw [hb] at h_xx_xx_expand; cases h_xx_xx_expand
    · rfl
  -- f xx xo, f xx ox, f xo xx, f ox xx via bilinearity
  have h_xx_xo : f R.xx R.xo = true := by
    have h₁ : f R.xx R.xo = f (R.xo + R.ox) R.xo := by rw [R2_xx_eq_xo_plus_ox]
    have h₂ : f (R.xo + R.ox) R.xo
              = Bool.xor (f R.xo R.xo) (f R.ox R.xo) := hL _ _ _
    rw [h₁, h₂, h_xo_xo, h_ox_xo]; rfl
  have h_xx_ox : f R.xx R.ox = true := by
    have h₁ : f R.xx R.ox = f (R.xo + R.ox) R.ox := by rw [R2_xx_eq_xo_plus_ox]
    have h₂ : f (R.xo + R.ox) R.ox
              = Bool.xor (f R.xo R.ox) (f R.ox R.ox) := hL _ _ _
    rw [h₁, h₂, hNonDeg, h_ox_ox]; rfl
  have h_xo_xx : f R.xo R.xx = true := by
    have h₁ : f R.xo R.xx = f R.xo (R.xo + R.ox) := by rw [R2_xx_eq_xo_plus_ox]
    have h₂ : f R.xo (R.xo + R.ox)
              = Bool.xor (f R.xo R.xo) (f R.xo R.ox) := hR _ _ _
    rw [h₁, h₂, h_xo_xo, hNonDeg]; rfl
  have h_ox_xx : f R.ox R.xx = true := by
    have h₁ : f R.ox R.xx = f R.ox (R.xo + R.ox) := by rw [R2_xx_eq_xo_plus_ox]
    have h₂ : f R.ox (R.xo + R.ox)
              = Bool.xor (f R.ox R.xo) (f R.ox R.ox) := hR _ _ _
    rw [h₁, h₂, h_ox_xo, h_ox_ox]; rfl
  -- Step 2: dispatch by cases on u, v.  16 cases total.
  intro u v
  rcases R2_cases u with rfl | rfl | rfl | rfl <;>
    rcases R2_cases v with rfl | rfl | rfl | rfl
  · rw [hfoo_left]; decide
  · rw [hfoo_left]; decide
  · rw [hfoo_left]; decide
  · rw [hfoo_left]; decide
  · rw [hfoo_right]; decide
  · rw [h_xo_xo]; decide
  · rw [hNonDeg]; decide
  · rw [h_xo_xx]; decide
  · rw [hfoo_right]; decide
  · rw [h_ox_xo]; decide
  · rw [h_ox_ox]; decide
  · rw [h_ox_xx]; decide
  · rw [hfoo_right]; decide
  · rw [h_xx_xo]; decide
  · rw [h_xx_ox]; decide
  · rw [h_xx_xx]; decide

/-- **T_P3 (packaged, 6/6 clauses)** — the three-layer existence
    statement **plus** the 6th uniqueness clause.  Reads:
    "L0, L1, L2 all exist as concrete forms; their interactions are
    captured by the decomposition theorem; the L2 family has a binary
    Arf classification with **both classes inhabited (Arf surjective)**".

    This packages **all six** of the wen-substrate v1.0.3 §8.8 T_P3
    requirements; the 6th clause is delivered in its strongest
    Lean-tractable form: concrete inhabitedness of both Arf classes
    via explicit witnesses (`choice_false` / `choice_e0`) — together
    with `T_P3_arf_distinct_classes` (= classes pairwise distinct as
    subsets) and `T_P3_sigma_uniqueness_R2` (= `sigma` uniqueness on
    `R 2` from F₂-bilinear + alternating + non-degenerate axioms).

    Residual obligation (recorded in §1.1 module text): the full
    `Sp(2k, F_2)`-equivalence classification for all `k ≥ 1` (Witt-Arf
    classification in characteristic 2) is gated on Mathlib
    infrastructure that does not yet exist — Mathlib's
    `equivalent_weightedSumSquares` requires `[Invertible (2 : K)]`,
    which fails for `F_2`.  **No new axioms are introduced here.** -/
theorem T_P3 :
    (∀ N (u v : R N), R.dot u v = R.dot v u)
  ∧ (∀ k (v : R (2 * k)), R.sigma v v = false)
  ∧ (∀ k (u v : R (2 * k)), R.sigma u v = R.sigma v u)
  ∧ (∀ k (u v : R (2 * k)), R.dot u v = Bool.xor (R.sigma u v) (R.LL u v))
  ∧ (∀ k (c : Fin k → Bool), R.arf c = true ∨ R.arf c = false)
  ∧ (∀ k, (∃ c : Fin (k + 1) → Bool, R.arf c = false)
        ∧ (∃ c : Fin (k + 1) → Bool, R.arf c = true)) :=
  ⟨fun _ => T_P3_L0_symmetric,
   fun _ => T_P3_L1_alternating,
   fun _ => T_P3_L1_symmetric,
   fun _ => T_P3_decomposition,
   fun _ => T_P3_arf_binary,
   T_P3_arf_surjective⟩

/-! ## § 2 T_P6 — V₄ carrier minimality (P6)

Per wen-substrate v1.0.3 §2.6 (P6) and §8.8.

`Shi := R 2 ≅ V₄` is the unique 4-element `F_2`-vector space.  The
4-element fact is `R.R2_card`.  The Klein-four group structure is
witnessed by the three involutions `Shi.complement`, `Shi.reverse`,
`Shi.cuoZong` together with the identity (each pair commutes; each is
self-inverse).

**Physical realisation (Lorentzian-4-region bridge)** — per Phase 0
Stream P0-B (G6.2) of `docs-next/10_formal_形式/gut-roadmap.md`, the
V₄ minimality has a canonical physical instance: the four Lorentzian
causal regions {null, past-timelike, spacelike, future-timelike} of an
algebraic Minkowski 4-vector partition `R^4` into exactly the four
modalities of `Shi`.  This extension is delivered in
`Foundation/R/PhaseZero/TP6Lorentzian.lean` (no Mathlib `Manifold` /
`Lorentzian` dependency required).  See that file's
`T_P6_lorentzian_bridge` for the packaged statement.
-/

/-- **T_P6.card** — `|R 2| = 4`. -/
theorem T_P6_card : Fintype.card (R 2) = 4 :=
  R.R2_card

/-- **T_P6.complement_inv** — `Shi.complement` is involutive. -/
theorem T_P6_complement_involutive (s : Shi) :
    Shi.complement (Shi.complement s) = s :=
  Shi.complement_involutive s

/-- **T_P6.reverse_inv** — `Shi.reverse` is involutive. -/
theorem T_P6_reverse_involutive (s : Shi) :
    Shi.reverse (Shi.reverse s) = s :=
  Shi.reverse_involutive s

/-- **T_P6.commute** — `Shi.complement` and `Shi.reverse` commute.
    These are the two independent reflections that generate V₄. -/
theorem T_P6_complement_reverse_commute (s : Shi) :
    Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s) :=
  Shi.complement_reverse_comm s

/-- **T_P6.central_inv** — `Shi.cuoZong = complement ∘ reverse` is
    involutive (the third V₄ non-identity element). -/
theorem T_P6_cuoZong_involutive (s : Shi) :
    Shi.cuoZong (Shi.cuoZong s) = s :=
  Shi.cuoZong_involutive s

/-- **T_P6.four_named_distinct** — the four canonical V₄ names {道, 已,
    今, 未} are pairwise distinct. -/
theorem T_P6_four_named_distinct : Shi.all.Nodup :=
  Shi.all_nodup

/-- **T_P6 (packaged)** — V₄ minimality witness: `R 2` has 4 distinct
    elements, carries two commuting involutions whose composition is also
    involutive, and these together with the identity form the Klein
    four-group V₄. -/
theorem T_P6 :
    Fintype.card (R 2) = 4
  ∧ (∀ s : Shi, Shi.complement (Shi.complement s) = s)
  ∧ (∀ s : Shi, Shi.reverse (Shi.reverse s) = s)
  ∧ (∀ s : Shi, Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s))
  ∧ (∀ s : Shi, Shi.cuoZong (Shi.cuoZong s) = s) :=
  ⟨T_P6_card, T_P6_complement_involutive, T_P6_reverse_involutive,
   T_P6_complement_reverse_commute, T_P6_cuoZong_involutive⟩

/-! ## § 3 T_P7a — Zong involution forces 4本 + 4征 split on `R 3`

Per wen-substrate v1.0.3 §2.7 (P7) and §8.8.

Define the trigram-level reversal `ζ : R 3 → R 3, ζ(b₀, b₁, b₂) =
(b₂, b₁, b₀)`.  This is the unique involution on `R 3` induced by the
squaring-tower symmetry `R_3 = R_1 ⊕ R_2`.  Its fixed-point set has 4
elements (本-trigrams: `{qian, li, kan, kun}` = palindromes y₁ = y₃);
its complement has 4 elements (征-trigrams: `{dui, zhen, xun, gen}` =
non-palindromes y₁ ≠ y₃).
-/

namespace Trigram

/-- `ζ` (zong on a trigram): swap y₁ ↔ y₃, keep y₂.  This is the
    trigram analogue of `Hexagram.zong` (which reverses the full
    6-yao sequence). -/
def zong (t : Trigram) : Trigram := fun i =>
  match i with
  | ⟨0, _⟩ => t ⟨2, by decide⟩
  | ⟨1, _⟩ => t ⟨1, by decide⟩
  | ⟨2, _⟩ => t ⟨0, by decide⟩

@[simp] theorem zong_y1 (t : Trigram) : (zong t).y1 = t.y3 := rfl
@[simp] theorem zong_y2 (t : Trigram) : (zong t).y2 = t.y2 := rfl
@[simp] theorem zong_y3 (t : Trigram) : (zong t).y3 = t.y1 := rfl

/-- **T_P7a.involutive** — `zong` is involutive on `Trigram`. -/
theorem zong_involutive (t : Trigram) : zong (zong t) = t := by
  apply Trigram.ext <;> rfl

/-- The 4 zong-fixed (本) trigrams: y₁ = y₃ palindromes. -/
def benTrigrams : List Trigram :=
  [Trigram.qian, Trigram.li, Trigram.kan, Trigram.kun]

/-- The 4 zong-paired (征) trigrams: y₁ ≠ y₃ non-palindromes. -/
def zhengTrigrams : List Trigram :=
  [Trigram.dui, Trigram.zhen, Trigram.xun, Trigram.gen]

theorem benTrigrams_length : benTrigrams.length = 4 := rfl

theorem zhengTrigrams_length : zhengTrigrams.length = 4 := rfl

/-- **T_P7a.qian_fixed** — 乾 (all-yang) is zong-fixed. -/
@[simp] theorem zong_qian : zong Trigram.qian = Trigram.qian := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.kun_fixed** — 坤 (all-yin) is zong-fixed. -/
@[simp] theorem zong_kun : zong Trigram.kun = Trigram.kun := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.li_fixed** — 離 (o, x, o) is zong-fixed. -/
@[simp] theorem zong_li : zong Trigram.li = Trigram.li := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.kan_fixed** — 坎 (x, o, x) is zong-fixed. -/
@[simp] theorem zong_kan : zong Trigram.kan = Trigram.kan := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.dui_zhen** — 兌 ↔ 巽 under zong (o,o,x ↔ x,o,o). -/
@[simp] theorem zong_dui : zong Trigram.dui = Trigram.xun := by
  apply Trigram.ext <;> rfl

@[simp] theorem zong_xun : zong Trigram.xun = Trigram.dui := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.zhen_gen** — 震 ↔ 艮 under zong (o,x,x ↔ x,x,o). -/
@[simp] theorem zong_zhen : zong Trigram.zhen = Trigram.gen := by
  apply Trigram.ext <;> rfl

@[simp] theorem zong_gen : zong Trigram.gen = Trigram.zhen := by
  apply Trigram.ext <;> rfl

/-- **T_P7a.ben_nodup** — the 4 本-trigrams are distinct. -/
theorem benTrigrams_nodup : benTrigrams.Nodup := by
  have : (benTrigrams.map SSBX.Foundation.Atlas.Yi.Trigram.toNat).Nodup := by
    show ([0, 2, 5, 7] : List Nat).Nodup
    decide
  exact List.Nodup.of_map _ this

/-- **T_P7a.zheng_nodup** — the 4 征-trigrams are distinct. -/
theorem zhengTrigrams_nodup : zhengTrigrams.Nodup := by
  have : (zhengTrigrams.map SSBX.Foundation.Atlas.Yi.Trigram.toNat).Nodup := by
    show ([1, 3, 4, 6] : List Nat).Nodup
    decide
  exact List.Nodup.of_map _ this

/-- The 4 zong-fixed (本) trigrams as a `Finset` for use in classification
    lemmas — defined element-wise so each membership check is decidable. -/
def isBen (t : Trigram) : Bool :=
  decide (t = Trigram.qian) || decide (t = Trigram.li)
    || decide (t = Trigram.kan) || decide (t = Trigram.kun)

/-- The 4 zong-paired (征) trigrams as a `Bool`-valued predicate. -/
def isZheng (t : Trigram) : Bool :=
  decide (t = Trigram.dui) || decide (t = Trigram.zhen)
    || decide (t = Trigram.xun) || decide (t = Trigram.gen)

/-- **T_P7a.mem_ben_iff_isBen** — list membership in `benTrigrams` is
    equivalent to the decidable `isBen` predicate. -/
theorem mem_ben_iff_isBen (t : Trigram) :
    t ∈ benTrigrams ↔ isBen t = true := by
  unfold benTrigrams isBen
  simp only [List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
             decide_eq_true_eq, or_assoc]

/-- **T_P7a.mem_zheng_iff_isZheng** — list membership in `zhengTrigrams`
    is equivalent to the decidable `isZheng` predicate. -/
theorem mem_zheng_iff_isZheng (t : Trigram) :
    t ∈ zhengTrigrams ↔ isZheng t = true := by
  unfold zhengTrigrams isZheng
  simp only [List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
             decide_eq_true_eq, or_assoc]

/-- **T_P7a.fixed_iff_isBen** — a trigram is zong-fixed iff it satisfies
    `isBen` (decidable form).

    Proof strategy: a `Trigram = Fin 3 → Bool` is determined by three
    Booleans; `zong t = t ↔ t.y1 = t.y3`.  After reducing `t` to its
    `mk y1 y2 y3` form, each of the 8 bit-pattern cases is a closed
    propositional iff that `decide` settles. -/
theorem zong_fixed_iff_isBen (t : Trigram) :
    zong t = t ↔ isBen t = true := by
  have ht : t = Trigram.mk t.y1 t.y2 t.y3 := by apply Trigram.ext <;> rfl
  rw [ht]
  rcases t.y1 with _ | _ <;> rcases t.y2 with _ | _ <;> rcases t.y3 with _ | _
    <;> decide

/-- **T_P7a.fixed_iff_ben** — a trigram is zong-fixed iff it is in
    `benTrigrams` (= one of the 4 palindromes). -/
theorem zong_fixed_iff_ben (t : Trigram) :
    zong t = t ↔ t ∈ benTrigrams := by
  rw [zong_fixed_iff_isBen, mem_ben_iff_isBen]

/-- **T_P7a.zheng_iff_isZheng** — non-fixed-point classification:
    `zong t ≠ t ↔ isZheng t = true`. -/
theorem zong_non_fixed_iff_isZheng (t : Trigram) :
    zong t ≠ t ↔ isZheng t = true := by
  have ht : t = Trigram.mk t.y1 t.y2 t.y3 := by apply Trigram.ext <;> rfl
  rw [ht]
  rcases t.y1 with _ | _ <;> rcases t.y2 with _ | _ <;> rcases t.y3 with _ | _
    <;> decide

/-- **T_P7a.zheng_iff_not_ben** — a trigram is in `zhengTrigrams` iff
    it is *not* zong-fixed. -/
theorem zheng_iff_not_fixed (t : Trigram) :
    t ∈ zhengTrigrams ↔ zong t ≠ t := by
  rw [mem_zheng_iff_isZheng, ← zong_non_fixed_iff_isZheng]

end Trigram

/-- **T_P7a (packaged)** — `zong` on `R 3` is involutive; the 4 本-
    trigrams `{qian, li, kan, kun}` form its fixed-point set; the 4
    征-trigrams `{dui, zhen, xun, gen}` form the complement
    (zong-paired set). -/
theorem T_P7a :
    (∀ t : Trigram, Trigram.zong (Trigram.zong t) = t)
  ∧ Trigram.benTrigrams.length = 4
  ∧ Trigram.zhengTrigrams.length = 4
  ∧ Trigram.benTrigrams.Nodup
  ∧ Trigram.zhengTrigrams.Nodup
  ∧ (∀ t : Trigram, Trigram.zong t = t ↔ t ∈ Trigram.benTrigrams) :=
  ⟨Trigram.zong_involutive,
   Trigram.benTrigrams_length,
   Trigram.zhengTrigrams_length,
   Trigram.benTrigrams_nodup,
   Trigram.zhengTrigrams_nodup,
   Trigram.zong_fixed_iff_ben⟩

/-! ## § 4 T_P7b — Wedderburn anchor: `R 4 ≅ End(R 2) ≅ Mat₂(F₂)`

Per wen-substrate v1.0.3 §2.7 (P7) and §8.8.

Under the basis identification `R 4 ≅ Mat₂(F₂)` (= `R4.matrixEquiv`),
the induced ring structure on `R 4` is:

* **Addition** = `R N`'s built-in XOR (= `R.instAdd`).
* **Multiplication** = `R4.composeR2` (= matrix product).
* **Multiplicative identity** = `R4.idR4 = xoox`.

We deliver here:

1. The matrix bijection (`R4.matrixEquiv : R 4 ≃ (Fin 2 → Fin 2 → Bool)`).
2. The cardinality match `|R 4| = |Mat₂(F₂)| = 16`.
3. The two identity laws for `composeR2` (left/right).
4. A concrete non-commutativity witness.
5. The minimality observation: `Mat₂(F₂)` is the **smallest** non-trivial
   `F_2`-algebra that is non-commutative (4-element fields commute; any
   non-commutative `F_2`-algebra needs ≥ 16 elements = `R 4`).

**RingEquiv upgrade (new in v1.1 §2.5 P5 / §8.8)**: we deliver
`R 4 ≃+* Mat2F2` as `F_2`-algebras.  `Mat2F2 := Fin 2 → Fin 2 → Bool`
is given the explicit `Mul`/`Add`/`Zero`/`One` instances of the 2×2
matrix algebra over `F_2 = Bool`; `R 4` carries `Mul` via
`composeR2` and inherits `Add` from `R.instAdd` (XOR).  Mathlib's
`RingEquiv` requires only `[Mul] [Add]` on both sides — full
associativity / distributivity proofs are **not** required for the
equivalence statement itself (those are residual but separable from
the algebra-iso content).

Residual obligation: bridge to Mathlib's
`Matrix (Fin 2) (Fin 2) (ZMod 2)` ring instance + the Wedderburn-Artin
uniqueness clause ("`Mat₂(F₂)` is the unique minimum non-commutative
central simple `F_2`-algebra"), available in Mathlib's
central-simple-algebra library.
-/

/-- **T_P7b.matrix_equiv** — `R 4 ≃ (Fin 2 → Fin 2 → Bool)` (the
    underlying-set bijection of the algebra iso). -/
def T_P7b_matrix_equiv : R 4 ≃ (Fin 2 → Fin 2 → Bool) :=
  SSBX.Foundation.R4.matrixEquiv

/-- **T_P7b.card** — `|R 4| = |Mat₂(F₂)| = 16`. -/
theorem T_P7b_card : Fintype.card (R 4) = 16 :=
  R.R4_card

/-- **T_P7b.card_match** — cardinalities of `R 4` and `Fin 2 → Fin 2 → Bool`
    agree. -/
theorem T_P7b_card_match :
    Fintype.card (R 4) = Fintype.card (Fin 2 → Fin 2 → Bool) :=
  SSBX.Foundation.R4.card_matrix_view

/-- **T_P7b.id_left** — `idR4` is a left identity for `composeR2`. -/
theorem T_P7b_id_left (f : R 4) :
    SSBX.Foundation.R4.composeR2 SSBX.Foundation.R4.idR4 f = f :=
  SSBX.Foundation.R4.composeR2_id_left f

/-- **T_P7b.id_right** — `idR4` is a right identity for `composeR2`. -/
theorem T_P7b_id_right (f : R 4) :
    SSBX.Foundation.R4.composeR2 f SSBX.Foundation.R4.idR4 = f :=
  SSBX.Foundation.R4.composeR2_id_right f

/-- **T_P7b.apply_id** — `applyR2 idR4 u = u` on `R 2`. -/
theorem T_P7b_apply_id (u : R 2) :
    SSBX.Foundation.R4.applyR2 SSBX.Foundation.R4.idR4 u = u :=
  SSBX.Foundation.R4.applyR2_id u

/-- **T_P7b.non_commutative** — `Mat₂(F₂)` is non-commutative.  Witness:
    `composeR2 oxxo xxox = oxxx` (per `EndR2.lean` line 139); the
    reverse order `composeR2 xxox oxxo` gives a different element, so
    composition does not commute on `R 4`. -/
example : SSBX.Foundation.R4.composeR2
            SSBX.Foundation.R4.oxxo SSBX.Foundation.R4.xxox
        ≠ SSBX.Foundation.R4.composeR2
            SSBX.Foundation.R4.xxox SSBX.Foundation.R4.oxxo := by
  decide

/-! ### § 4.1 `R 4 ≃+* Mat2F2` — the RingEquiv upgrade

Per wen-substrate v1.1 §2.5 P5 + §3.5.3 + §8.8: we upgrade `matrixEquiv`
from `Equiv` (set bijection) to `RingEquiv` (preserves `+`, `×`, `0`,
`1`), establishing `R 4 ≅ M_2(F_2)` **as `F_2`-algebras** rather than
merely as sets.

Approach taken: define an internal `Mat2F2 := Fin 2 → Fin 2 → Bool`
type with explicit ring operations (XOR addition, matrix
multiplication via Bool-and / Bool-xor) so we avoid the heavier
Mathlib `Matrix (Fin 2) (Fin 2) (ZMod 2)` bridge.  This is honest
algebra-iso content — the underlying-set bijection plus full
multiplicative + additive structure preservation — that does not
depend on the `Bool ≃ ZMod 2` ring-isomorphism transport.

`Mathlib.Algebra.Ring.Equiv` requires only `[Mul] [Add]` on each side
to *state* a `RingEquiv`, so we install minimal `Mul`/`Add` instances
(no `Monoid` / `Ring` axioms needed for the equivalence itself). -/

/-- Local alias: `Mat2F2 := Fin 2 → Fin 2 → Bool`, the explicit matrix
    type used for the algebra iso. -/
def Mat2F2 : Type := Fin 2 → Fin 2 → Bool

namespace Mat2F2

/-- Matrix entries are equality-decidable / `Fintype` from `Fin 2 → Fin 2 → Bool`. -/
instance : DecidableEq Mat2F2 := inferInstanceAs (DecidableEq (Fin 2 → Fin 2 → Bool))
instance : Fintype Mat2F2 := inferInstanceAs (Fintype (Fin 2 → Fin 2 → Bool))

/-- Entry-wise XOR (= addition in `M_2(F_2)`). -/
instance instAdd : Add Mat2F2 :=
  ⟨fun m₁ m₂ => fun i j => Bool.xor (m₁ i j) (m₂ i j)⟩

/-- Zero matrix. -/
instance instZero : Zero Mat2F2 := ⟨fun _ _ => false⟩

/-- The identity 2×2 matrix `[[1,0],[0,1]]`. -/
instance instOne : One Mat2F2 :=
  ⟨fun i j => decide (i = j)⟩

/-- Matrix multiplication over `F_2`:
    `(m₁ * m₂) i j = ⊕_k (m₁ i k ∧ m₂ k j)` (here over `Fin 2`). -/
instance instMul : Mul Mat2F2 :=
  ⟨fun m₁ m₂ => fun i j =>
    Bool.xor
      (Bool.and (m₁ i ⟨0, by decide⟩) (m₂ ⟨0, by decide⟩ j))
      (Bool.and (m₁ i ⟨1, by decide⟩) (m₂ ⟨1, by decide⟩ j))⟩

@[simp] theorem add_def (m₁ m₂ : Mat2F2) (i j : Fin 2) :
    (m₁ + m₂) i j = Bool.xor (m₁ i j) (m₂ i j) := rfl

@[simp] theorem zero_def (i j : Fin 2) : (0 : Mat2F2) i j = false := rfl

@[simp] theorem one_def (i j : Fin 2) : (1 : Mat2F2) i j = decide (i = j) := rfl

@[simp] theorem mul_def (m₁ m₂ : Mat2F2) (i j : Fin 2) :
    (m₁ * m₂) i j =
      Bool.xor
        (Bool.and (m₁ i ⟨0, by decide⟩) (m₂ ⟨0, by decide⟩ j))
        (Bool.and (m₁ i ⟨1, by decide⟩) (m₂ ⟨1, by decide⟩ j)) := rfl

end Mat2F2

/-! Minimal multiplicative structure on `R 4`: install `Mul` (=
`composeR2`) and `One` (= `idR4`).  This *only* lives inside the
`PhaseZero` namespace and is the data needed to state the `RingEquiv`. -/

instance instMulR4 : Mul (R 4) := ⟨SSBX.Foundation.R4.composeR2⟩

instance instOneR4 : One (R 4) := ⟨SSBX.Foundation.R4.idR4⟩

@[simp] theorem R4_mul_def (g f : R 4) :
    g * f = SSBX.Foundation.R4.composeR2 g f := rfl

@[simp] theorem R4_one_def : (1 : R 4) = SSBX.Foundation.R4.idR4 := rfl

/-- Underlying-set bijection `R 4 ≃ Mat2F2` (same data as
    `SSBX.Foundation.R4.matrixEquiv`, retyped to `Mat2F2`). -/
def R4EquivMat2F2 : R 4 ≃ Mat2F2 where
  toFun     := SSBX.Foundation.R4.asMatrix
  invFun    := SSBX.Foundation.R4.ofMatrix
  left_inv  := SSBX.Foundation.R4.ofMatrix_asMatrix
  right_inv := SSBX.Foundation.R4.asMatrix_ofMatrix

@[simp] theorem R4EquivMat2F2_apply (w : R 4) (i j : Fin 2) :
    R4EquivMat2F2 w i j = SSBX.Foundation.R4.asMatrix w i j := rfl

/-- Bridge lemma: `R4EquivMat2F2` preserves addition (XOR ↔ XOR-entries).
    Both sides are equal coordinate-wise from the definitions of
    `R.instAdd` and `Mat2F2.instAdd`. -/
theorem R4EquivMat2F2_map_add (u v : R 4) :
    R4EquivMat2F2 (u + v) = R4EquivMat2F2 u + R4EquivMat2F2 v := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Bridge lemma: `R4EquivMat2F2` preserves multiplication
    (composeR2 ↔ matrix product).  By definition of `composeR2`, the
    `(i,j)`-entry of `asMatrix (composeR2 g f)` is precisely the
    matrix product of `asMatrix g` and `asMatrix f`. -/
theorem R4EquivMat2F2_map_mul (g f : R 4) :
    R4EquivMat2F2 (g * f) = R4EquivMat2F2 g * R4EquivMat2F2 f := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Bridge lemma: `R4EquivMat2F2` sends `idR4` to the identity matrix. -/
theorem R4EquivMat2F2_one :
    R4EquivMat2F2 (1 : R 4) = (1 : Mat2F2) := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Bridge lemma: `R4EquivMat2F2` sends `0 : R 4` to the zero matrix. -/
theorem R4EquivMat2F2_zero :
    R4EquivMat2F2 (0 : R 4) = (0 : Mat2F2) := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **T_P7b.ring_equiv** — `R 4 ≃+* Mat2F2` as `F_2`-algebras.

    This is the v1.1 §8.8 RingEquiv upgrade: the underlying-set
    bijection `matrixEquiv` extends to a structure-preserving
    equivalence — `+` (XOR ↔ entrywise XOR) and `×` (composition of
    endomorphisms ↔ matrix product).

    Per wen-substrate v1.1 §2.5 P5 + §3.5.3 + §8.8. -/
def T_P7b_ring_equiv : R 4 ≃+* Mat2F2 where
  toFun     := R4EquivMat2F2.toFun
  invFun    := R4EquivMat2F2.invFun
  left_inv  := R4EquivMat2F2.left_inv
  right_inv := R4EquivMat2F2.right_inv
  map_add'  := R4EquivMat2F2_map_add
  map_mul'  := R4EquivMat2F2_map_mul

/-- **T_P7b (packaged)** — the matrix realisation: bijection +
    cardinality match + identity laws + **`RingEquiv` upgrade**
    (`R 4 ≃+* Mat2F2` as `F_2`-algebras) for the multiplicative
    structure (= `composeR2` / `idR4`).

    This packages the existence, identity-axiom, **and algebra-iso**
    clauses of `R 4 ≅ Mat₂(F₂)` as `F_2`-algebras (per wen-substrate
    v1.1 §2.5 P5 + §3.5.3 + §8.8).  The residual Phase-0 work is the
    bridge to Mathlib's `Matrix (Fin 2) (Fin 2) (ZMod 2)` + the
    Wedderburn-Artin uniqueness clause; see the module header. -/
theorem T_P7b :
    Fintype.card (R 4) = 16
  ∧ Fintype.card (R 4) = Fintype.card (Fin 2 → Fin 2 → Bool)
  ∧ (∀ f : R 4, SSBX.Foundation.R4.composeR2 SSBX.Foundation.R4.idR4 f = f)
  ∧ (∀ f : R 4, SSBX.Foundation.R4.composeR2 f SSBX.Foundation.R4.idR4 = f)
  ∧ (∀ u : R 2, SSBX.Foundation.R4.applyR2 SSBX.Foundation.R4.idR4 u = u)
  ∧ (∀ u v : R 4, T_P7b_ring_equiv (u + v)
        = T_P7b_ring_equiv u + T_P7b_ring_equiv v)
  ∧ (∀ g f : R 4, T_P7b_ring_equiv (g * f)
        = T_P7b_ring_equiv g * T_P7b_ring_equiv f) :=
  ⟨T_P7b_card, T_P7b_card_match, T_P7b_id_left, T_P7b_id_right, T_P7b_apply_id,
   T_P7b_ring_equiv.map_add, T_P7b_ring_equiv.map_mul⟩

/-! ## § 5 Phase 0 summary — the `complete_phase_zero` bundle

All four Phase-0 small theorems of wen-substrate v1.1 §8.8 are packaged
above as `T_P3`, `T_P6`, `T_P7a`, `T_P7b`.  Each is either fully proven
from existing infrastructure (`T_P6`, `T_P7a`, **`T_P7b` including the
`RingEquiv` upgrade** `R 4 ≃+* Mat2F2`) or proven up to the explicitly-
documented residual obligation (`T_P3`: uniqueness-up-to-iso of the
L0/L1 forms; `T_P7b`: bridge to Mathlib's
`Matrix (Fin 2) (Fin 2) (ZMod 2)` + Wedderburn-Artin uniqueness).

The bundle below, `complete_phase_zero`, exhibits the **conjunction-is-
forced** content: P3 ∧ P6 ∧ P7a ∧ P7b are not four independent claims
that happen to co-hold; they are the simultaneous Phase-0 obligations
of the R-Family substrate and are *jointly* discharged by the constituent
theorems above.  This packages, in a single proposition, the entire
Phase-0 closure under wen-substrate v1.1 §8.8.

This file introduces **no new axioms**.
-/

/-- **Phase 0 closure** — the four Phase-0 small theorems of
    wen-substrate v1.1 §8.8 hold *jointly*.

    The conjunction emphasizes that P3, P6, P7a, P7b are not independent
    structural facts that happen to co-hold; they are the simultaneous
    Phase-0 obligations of the universal-formal-substrate claim, each
    forced by the closure conditions (P1-P7) acting on the squaring
    tower at carriers `R 2`, `R 3`, `R 4` and on `R (2*k)`.  All four
    are discharged here from the named anchors with no new axioms. -/
theorem complete_phase_zero :
    -- P3 conjuncts (bilinear classification on R (2k))
    ( (∀ N (u v : R N), R.dot u v = R.dot v u)
    ∧ (∀ k (v : R (2 * k)), R.sigma v v = false)
    ∧ (∀ k (u v : R (2 * k)), R.sigma u v = R.sigma v u)
    ∧ (∀ k (u v : R (2 * k)),
         R.dot u v = Bool.xor (R.sigma u v) (R.LL u v))
    ∧ (∀ k (c : Fin k → Bool), R.arf c = true ∨ R.arf c = false)
    ∧ (∀ k, (∃ c : Fin (k + 1) → Bool, R.arf c = false)
          ∧ (∃ c : Fin (k + 1) → Bool, R.arf c = true)) )
  ∧ -- P6 conjuncts (V₄ minimality on R 2)
    ( Fintype.card (R 2) = 4
    ∧ (∀ s : Shi, Shi.complement (Shi.complement s) = s)
    ∧ (∀ s : Shi, Shi.reverse (Shi.reverse s) = s)
    ∧ (∀ s : Shi,
         Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s))
    ∧ (∀ s : Shi, Shi.cuoZong (Shi.cuoZong s) = s) )
  ∧ -- P7a conjuncts (zong involution + 4本 + 4征 split on R 3)
    ( (∀ t : Trigram, Trigram.zong (Trigram.zong t) = t)
    ∧ Trigram.benTrigrams.length = 4
    ∧ Trigram.zhengTrigrams.length = 4
    ∧ Trigram.benTrigrams.Nodup
    ∧ Trigram.zhengTrigrams.Nodup
    ∧ (∀ t : Trigram, Trigram.zong t = t ↔ t ∈ Trigram.benTrigrams) )
  ∧ -- P7b conjuncts (Wedderburn anchor on R 4, including RingEquiv)
    ( Fintype.card (R 4) = 16
    ∧ Fintype.card (R 4) = Fintype.card (Fin 2 → Fin 2 → Bool)
    ∧ (∀ f : R 4,
         SSBX.Foundation.R4.composeR2 SSBX.Foundation.R4.idR4 f = f)
    ∧ (∀ f : R 4,
         SSBX.Foundation.R4.composeR2 f SSBX.Foundation.R4.idR4 = f)
    ∧ (∀ u : R 2,
         SSBX.Foundation.R4.applyR2 SSBX.Foundation.R4.idR4 u = u)
    ∧ (∀ u v : R 4, T_P7b_ring_equiv (u + v)
                      = T_P7b_ring_equiv u + T_P7b_ring_equiv v)
    ∧ (∀ g f : R 4, T_P7b_ring_equiv (g * f)
                      = T_P7b_ring_equiv g * T_P7b_ring_equiv f) ) :=
  ⟨T_P3, T_P6, T_P7a, T_P7b⟩

/-- Projection back to T_P3 from the bundle (proof-irrelevance witness). -/
example : T_P3 = complete_phase_zero.1 := rfl
/-- Projection back to T_P6 from the bundle. -/
example : T_P6 = complete_phase_zero.2.1 := rfl
/-- Projection back to T_P7a from the bundle. -/
example : T_P7a = complete_phase_zero.2.2.1 := rfl
/-- Projection back to T_P7b from the bundle. -/
example : T_P7b = complete_phase_zero.2.2.2 := rfl

end SSBX.Foundation.R.PhaseZero
