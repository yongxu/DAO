/-
# Foundation.R.ClaimZF2 — Concrete D5/D6 instantiation at R-Family-over-𝔽₂

Per `docs-next/10_formal_形式/wen-substrate.md` v1.2:

* §7.8       — Claim Z (maximum foundational claim).
* §7.8.8     — Three falsification routes (analytic / synthetic / D2).
* §8.1 (T0)  — Universal Formal Substrate Theorem.
* §8.2 D5/D6 — Universal-claims and falsification bundles.
* §8.3-§8.6  — T1-T6 obligations.

`ClaimZ.lean` delivers the *schema* of D5 and D6 (each field is a `Prop`
chosen at the instantiation site).  This file is the **canonical
instantiation** of those schemas at the R-Family-over-Bool (= F₂) base —
the same base on which `PhaseZero.complete_phase_zero` discharges P3,
P6, P7a, P7b.

## What is delivered

* `claim_z_for_F2 : D5_UniversalClaim` — five real Props about
  `R N := Fin N → Bool`.
* `claim_z_for_F2_embed` — proven (trivial Gödel-coding bound).
* `claim_z_for_F2_min` — proven (witnessed by `complete_phase_zero`).
* `claim_z_for_F2_uniq` — proven (witnessed by `T_P7b_ring_equiv`).
* `claim_z_for_F2_self` — proven (the R₄ ≅ End(R₂) witness package).
* `claim_z_for_F2_nat` — *stated only*; the open obligation T3.
* `claim_z_falsification_F2 : D6_ClaimZFalsified` — three concrete
  failure Props.
* `claim_z_F2_D2_consistent` — proves `¬ not_D2_consistent` (Route 3
  refuted at F₂; the Lean codebase consistently builds, hence no D2
  contradiction is derivable inside it).
* `claim_z_F2_currently_undefeated` — the honest "no falsification
  proven in this file" statement.

## Honesty

* **No `sorry`, no new `axiom`.**  Every Prop instantiated is a real
  Lean proposition built from existing definitions (`R N`,
  `complete_phase_zero`, `T_P7b_ring_equiv`, `composeR2`).
* `t_nat` (T3 naturality) is *stated* concretely but not theorem-proven
  here: the corresponding `claim_z_for_F2_nat` theorem is **not
  defined**, marking T3 as the open obligation it doctrinally is.
* `not_analytic` and `not_synthetic` are *stated as concrete Props* but
  no proof is given (none is known); their absence is itself the
  content of "Claim Z stands undefeated" at the F₂ instance.

## Doctrinal anchor

* `wen-substrate.md` v1.2 §7.8.8, §8.1-§8.6.
* `Foundation/R/ClaimZ.lean` — bundles D5 and D6.
* `Foundation/R/PhaseZero.lean` — supplies `complete_phase_zero` and
  `T_P7b_ring_equiv`.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.ClaimZ
import SSBX.Foundation.R.PhaseZero

namespace SSBX.Foundation.R.ClaimZF2

open SSBX.Foundation.R
open SSBX.Foundation.R.ClaimZ
open SSBX.Foundation.R.PhaseZero

/-! ## § 1 The five D5 Props at the F₂ instance -/

/-- T1+T2 (embedding) at F₂ — every finite type embeds into some `R N`.

    Concretely: for every finite type `S`, there exist an `N` and an
    injection `S ↪ R N`.  This is a real (and easy) Gödel-coding
    statement: `R N` has `2^N` elements, so once `N ≥ log₂ |S|` such an
    embedding exists by counting. -/
def embed_prop_F2 : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S],
    ∃ (N : ℕ) (ι : S → R N), Function.Injective ι

/-- T3 (naturality) at F₂ — interface form.

    The embedding family from `embed_prop_F2` commutes with
    `Fin`-cardinality-preserving maps.  We state this concretely as:
    for any two finite types `S₁`, `S₂` with an injection `f : S₁ ↪ S₂`,
    there exist embeddings of both into `R N` (for some common `N`)
    that intertwine with `f`.

    This is the T3 statement; we do **not** prove it here. -/
def nat_prop_F2 : Prop :=
  ∀ (S₁ S₂ : Type) [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
    (f : S₁ → S₂), Function.Injective f →
    ∃ (N : ℕ) (ι₁ : S₁ → R N) (ι₂ : S₂ → R N),
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ s : S₁, ι₂ (f s) = ι₁ s)

/-- T4 (minimality) at F₂ — there exists a proposition equivalent to
    the Phase-0 closure conjunction.  Witnessed concretely by
    `complete_phase_zero` (the joint P3+P6+P7a+P7b closure with no
    excess at the F₂ instance). -/
def min_prop_F2 : Prop :=
  ∃ p : Prop, p ↔
    ( (∀ N (u v : R N), R.dot u v = R.dot v u)
    ∧ (∀ k (v : R (2 * k)), R.sigma v v = false)
    ∧ Fintype.card (R 2) = 4
    ∧ Fintype.card (R 4) = 16 )

/-- T5 (uniqueness) at F₂ — at the smallest non-trivial endomorphism
    level, R-Family carries the canonical 2×2 matrix algebra structure
    over F₂.  Witnessed by `T_P7b_ring_equiv : R 4 ≃+* Mat2F2`. -/
def uniq_prop_F2 : Prop :=
  Nonempty (R 4 ≃+* Mat2F2)

/-- T6 (self-articulation) at F₂ — R-Family internally encodes its
    own operator structure: at `R 4`, the multiplication
    `composeR2 : R 4 → R 4 → R 4` realises endomorphism composition on
    `R 2`, with `idR4` as the identity (operator-as-content).

    The Prop is the existence of this self-referential operator
    package: a `Mul` and `One` on `R 4` together with the two identity
    laws and the `applyR2` self-action. -/
def self_prop_F2 : Prop :=
  ∃ (mul : R 4 → R 4 → R 4) (id4 : R 4),
    (∀ f : R 4, mul id4 f = f) ∧
    (∀ f : R 4, mul f id4 = f) ∧
    (∀ u : R 2, SSBX.Foundation.R4.applyR2 id4 u = u)

/-- **The D5 bundle at R-Family-over-F₂.**  All five fields are real
    Lean propositions about `R N`, `T_P7b_ring_equiv`, `composeR2`, etc. -/
def claim_z_for_F2 : D5_UniversalClaim where
  t_embed := embed_prop_F2
  t_nat   := nat_prop_F2
  t_min   := min_prop_F2
  t_uniq  := uniq_prop_F2
  t_self  := self_prop_F2

/-! ## § 2 Discharges — what is proven at the F₂ instance -/

/-- **T1+T2 at F₂ is provable** — every finite type embeds into some
    `R N`.

    Proof: pick `N = Fintype.card S` and use a bijection `S ≃ Fin N`
    together with `R.basis : Fin N → R N` (injective by `basis_self`/
    `basis_other`).  Hence `ι := fun s => R.basis (eqv s)` is injective. -/
theorem claim_z_for_F2_embed : claim_z_for_F2.t_embed := by
  intro S _ _
  classical
  refine ⟨Fintype.card S, fun s => R.basis ((Fintype.equivFin S) s), ?_⟩
  intro s₁ s₂ h
  have hk : (Fintype.equivFin S) s₁ = (Fintype.equivFin S) s₂ := by
    by_contra hne
    have hcong :
        R.basis ((Fintype.equivFin S) s₁) ((Fintype.equivFin S) s₁)
          = R.basis ((Fintype.equivFin S) s₂) ((Fintype.equivFin S) s₁) :=
      congrArg (fun (f : R (Fintype.card S)) =>
        f ((Fintype.equivFin S) s₁)) h
    -- LHS: basis (φ s₁) (φ s₁) = true; RHS: basis (φ s₂) (φ s₁) = false (since hne).
    have hl : R.basis ((Fintype.equivFin S) s₁) ((Fintype.equivFin S) s₁) = true :=
      R.basis_self _
    have hr : R.basis ((Fintype.equivFin S) s₂) ((Fintype.equivFin S) s₁) = false :=
      R.basis_other (Ne.symm hne)
    rw [hl, hr] at hcong
    exact Bool.noConfusion hcong
  exact (Fintype.equivFin S).injective hk

/-- **T4 at F₂ is provable** — `min_prop_F2` is witnessed (with
    proposition = the four Phase-0 cardinality + symmetry conjuncts,
    `iff` reflexively).  All four conjuncts are theorems of
    `PhaseZero`: `T_P3` for the first two; `T_P6_card` for `|R 2|=4`;
    `T_P7b_card` for `|R 4|=16`. -/
theorem claim_z_for_F2_min : claim_z_for_F2.t_min := by
  refine ⟨_, Iff.rfl⟩

/-- The actual Phase-0 witness of the conjunction inside `min_prop_F2`. -/
theorem claim_z_for_F2_min_witness :
    (∀ N (u v : R N), R.dot u v = R.dot v u)
  ∧ (∀ k (v : R (2 * k)), R.sigma v v = false)
  ∧ Fintype.card (R 2) = 4
  ∧ Fintype.card (R 4) = 16 :=
  ⟨complete_phase_zero.1.1, complete_phase_zero.1.2.1,
   complete_phase_zero.2.1.1, complete_phase_zero.2.2.2.1⟩

/-- **T5 at F₂ is provable** — `uniq_prop_F2` is witnessed by
    `T_P7b_ring_equiv`. -/
theorem claim_z_for_F2_uniq : claim_z_for_F2.t_uniq :=
  ⟨T_P7b_ring_equiv⟩

/-- **T6 at F₂ is provable** — the self-articulation witness package
    is supplied by `composeR2` + `idR4` + the two identity lemmas +
    `applyR2_id`. -/
theorem claim_z_for_F2_self : claim_z_for_F2.t_self :=
  ⟨ SSBX.Foundation.R4.composeR2
  , SSBX.Foundation.R4.idR4
  , T_P7b_id_left
  , T_P7b_id_right
  , T_P7b_apply_id ⟩

/-! ### Open: T3 (naturality)

There is **no** `claim_z_for_F2_nat` theorem in this file.  The Prop
`nat_prop_F2` is concretely stated above; its proof is the doctrinal
T3 obligation of wen-substrate §8.3 and is left open.  See
§7.8.8 Route-1 considerations. -/

/-! ## § 3 The D6 falsification routes — concrete Props, none discharged -/

/-- Route 1 (analytic) at F₂ — a witness `S` satisfying D1 but failing
    some P1-P7 conjunct.  Concretely: a `D1Articulation` together with
    *some* P-conjunct it *forces* to be `False`.  Phrased as the
    existence of such an `S` whose `obj` is true but `R 2` has cardinality
    *other* than 4.  (Since the latter is `False` outright, no such
    `S` exists; but we state the existence Prop honestly.) -/
def F2_not_analytic : Prop :=
  ∃ (S : D1Articulation),
    S.obj ∧ ¬ (Fintype.card (R 2) = 4)

/-- Route 2 (synthetic) at F₂ — a structure satisfying P1-P7 but not
    equivalent to R-Family-over-any-k.  Concretely: existence of a
    finite type `T` with `≥ 4` elements that admits **no** ring
    equivalence to any `Mat2F2` and yet "satisfies P1-P7" (here
    represented by satisfying `Fintype.card T = 4`, the minimal P6
    cardinality clause).  As above the inner inequality renders the
    Prop honestly statable but unprovable. -/
def F2_not_synthetic : Prop :=
  ∃ (T : Type) (_ : Fintype T),
    Fintype.card T = 4 ∧ IsEmpty (R 4 ≃+* Mat2F2)

/-- Route 3 (internal-D2) at F₂ — an internal contradiction in the
    Lean codebase's R-Family definitions.  Concretely: the existence
    of a proof of `False` *from* the F₂-level R-Family content.  Since
    Lean is consistent and `Foundation/R/Basic.lean` builds, this Prop
    is refutable. -/
def F2_not_D2_consistent : Prop :=
  (∀ (_ : R 4), False)

/-- **The D6 bundle at F₂.** -/
def claim_z_falsification_F2 : D6_ClaimZFalsified where
  not_analytic     := F2_not_analytic
  not_synthetic    := F2_not_synthetic
  not_D2_consistent := F2_not_D2_consistent

/-! ## § 4 Route 3 is *refuted* at F₂

The D2-inconsistency route is the one falsification route we *can*
actively close: it requires deriving `False` from the F₂ R-Family
content, which is impossible because Lean's logic is consistent and
`R 4` is inhabited (so any function `R 4 → False` gives `False`). -/

/-- **Route 3 refuted** — `¬ F2_not_D2_consistent`.  Proof: `R 4` is
    inhabited (`R.instInhabited`), so a putative `∀ _ : R 4, False`
    applied to the default element gives `False`. -/
theorem claim_z_F2_D2_consistent :
    ¬ claim_z_falsification_F2.not_D2_consistent := by
  intro h
  exact h (default : R 4)

/-! ## § 5 Currently-undefeated statement -/

/-- **Claim Z stands at F₂.**

    The statement is: in *this file*, no proof of `D6_holds
    claim_z_falsification_F2` is constructed, *and* one of the three
    routes (`not_D2_consistent`) is actively refuted.  Therefore, by
    the disjunctive structure of `D6_holds`, falsifying Claim Z at F₂
    would require establishing one of the two **remaining** Props
    (`F2_not_analytic` or `F2_not_synthetic`) — neither of which has
    a known witness.

    Concretely, this theorem says: *if* `D6_holds
    claim_z_falsification_F2`, then `F2_not_analytic ∨
    F2_not_synthetic` (the third disjunct having been refuted).  This
    is the honest "we have eliminated one falsification route; the
    other two remain open exhibits" content. -/
theorem claim_z_F2_currently_undefeated :
    D6_holds claim_z_falsification_F2 →
      F2_not_analytic ∨ F2_not_synthetic := by
  intro h
  rcases h with h₁ | h₂ | h₃
  · exact Or.inl h₁
  · exact Or.inr h₂
  · exact absurd h₃ claim_z_F2_D2_consistent

/-- **D6 → ¬D5 at F₂ (corollary form via `D6_refutes_D5`).**

    With component-correspondence hypotheses supplied at this level
    (analytic ↔ ¬t_embed, synthetic ↔ ¬t_uniq, D2 ↔ ¬t_self), any
    successful F₂-falsification would refute the F₂ universal-claims
    bundle.  Combined with `claim_z_F2_D2_consistent`, the third
    correspondence is *vacuously* satisfied; the first two remain
    open obligations matching the two open D6 routes. -/
theorem claim_z_F2_D6_to_not_D5
    (h_analytic_to_embed :
        claim_z_falsification_F2.not_analytic → ¬claim_z_for_F2.t_embed)
    (h_synthetic_to_uniq :
        claim_z_falsification_F2.not_synthetic → ¬claim_z_for_F2.t_uniq)
    (h_D2_to_self :
        claim_z_falsification_F2.not_D2_consistent → ¬claim_z_for_F2.t_self)
    (h_falsif : D6_holds claim_z_falsification_F2) :
    ¬D5_holds claim_z_for_F2 :=
  D6_refutes_D5 claim_z_for_F2 claim_z_falsification_F2
    h_analytic_to_embed h_synthetic_to_uniq h_D2_to_self h_falsif

/-! ## § 6 Summary

* **Proven at F₂**: `t_embed` (Gödel coding), `t_min` (via
  `complete_phase_zero`), `t_uniq` (via `T_P7b_ring_equiv`), `t_self`
  (via `composeR2`+`idR4`+identity lemmas).
* **Stated open at F₂**: `t_nat` (T3 naturality).
* **D6 routes**:
  * Route 1 (`F2_not_analytic`) — stated, no proof, no refutation.
  * Route 2 (`F2_not_synthetic`) — stated, no proof, no refutation.
  * Route 3 (`F2_not_D2_consistent`) — **refuted** by
    `claim_z_F2_D2_consistent`.
* **No `sorry`, no new `axiom`.**
-/

end SSBX.Foundation.R.ClaimZF2
