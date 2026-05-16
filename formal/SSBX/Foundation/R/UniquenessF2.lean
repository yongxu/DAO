/-
# Foundation.R.UniquenessF2 — T5-A skeleton: P1-P7 ⟹ R-family-over-F₂

Per `docs-next/10_formal_形式/gut-roadmap.md` **Phase 2 (T5-A)**:

> Any structure `S` satisfying P1-P7 (the wen-substrate's 7 closure
> conditions) is **equivalent** (categorical / Morita / bi-interpretable)
> to R-family-over-F₂ within the **F₂-Boolean classical scope**.

This is the **synthetic** direction of Claim Z — the converse to Phase 1's
analytic direction (`d1_implies_P` in `Foundation/R/ClaimZ.lean`).
Together with Phase 1's full closure, T5-A gives a publishable GUT claim.

## Status

**This is the scaffolding phase.** The proof is the next 2-4 months of
work per the GUT roadmap.  This file delivers:

1. The `P1P7_Satisfier_F2` *family* structure — the design decision of
   what it means to satisfy P1-P7 in F₂-Boolean classical scope.
2. The main theorem statement `T5_A`.
3. A 5-step proof scaffold with `sorry` per step and **explicit TODO**
   comments naming the Mathlib / our-infrastructure dependency.
4. A `risk_assessment` docstring listing the three risk options.

Every `sorry` here is paired with a specific TODO describing what is
needed to close it.  **No new axioms** are introduced.

## Phase 0 prerequisites (now complete)

- **G6.1** T_P3 uniqueness via Arf surjectivity
  (`PhaseZero` § 1.1, `T_P3_arf_surjective` / `T_P3_sigma_uniqueness_R2`).
- **G6.2** T_P6 Lorentzian bridge
  (`PhaseZero/TP6Lorentzian.lean`).
- **G6.3** T_P7b Wedderburn cardinality-uniqueness + Mathlib bridge
  (`PhaseZero/TP7bUniqueness.lean`).

These supply the **uniqueness clauses** that Steps 3-4 of the T5-A
proof consume.

## Strategy A (Step 1+2 partial discharge in F₂-Boolean scope)

`Foundation/R/StrategyA.lean` already discharges T4 step 3's
Stone-Birkhoff chain *for the classical-Boolean scope*: any finite
`BooleanRing α` embeds into `R N` for some `N` (= the `ZMod 2`-finrank
of α).  This is the **type-level** discharge of Steps 1+2 below; the
ring-level discharge (= Stone's theorem as a `RingEquiv`, not merely a
set-bijection) is the new content T5-A must provide.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` Phase 2 (T5-A).
* `docs-next/10_formal_形式/wen-substrate.md` v1.2 §7.8.3
  (synthetic direction of Claim Z).
* `Foundation/R/ClaimZ.lean` — `PClosure` schema + `D1Articulation`.
* `Foundation/R/StrategyA.lean` — partial Step 1+2 discharge.
* `Foundation/R/PhaseZero.lean` — `complete_phase_zero`.
* `Foundation/R/PhaseZero/TP7bUniqueness.lean` — `T_P7b_uniqueness_card_eq_16`.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.StrategyA
import SSBX.Foundation.R.PhaseZero
import SSBX.Foundation.R.PhaseZero.TP7bUniqueness
import SSBX.Foundation.R.ClaimZ
import SSBX.Foundation.R.Squaring

namespace SSBX.Foundation.R.UniquenessF2

open SSBX.Foundation.R
open SSBX.Foundation.R.PhaseZero
open SSBX.Foundation.R.ClaimZ

/-! ## § 1 The `P1P7_Satisfier_F2` structure

**Design decision** (the most consequential single choice in T5-A).

R-family is a *family* `R : ℕ → Type`, with `R N := Fin N → Bool`.  A
P1-P7 satisfier in F₂-Boolean classical scope must therefore also be a
**family of carriers** indexed by layer number `N`, together with the
seven closure conditions pinned to their F₂-Boolean specialisations:

* **P1** (minimum non-trivial structure → F₂):  each `carrier N` is
  finite, decidable-equality, and the *base layer* `carrier 1` has
  cardinality 2 (the F₂-bit forcing).  (Per Strategy A, this — plus
  P2 — already forces `carrier N ↪ R N` as types; what remains is
  forcing it as F₂-algebras.)
* **P2** (composition via direct sum): each `carrier (N + M) ≃ carrier N × carrier M`.
* **P3** (bilinear classification, 3-layer in char 2): the carrier
  family carries a symmetric `dot`, an alternating `sigma`, and a
  binary `arf` invariant, with the wen-algebra v0.6 §4 identities.
* **P4** (squaring tower self-similarity): `carrier (N + N) ≃ carrier N × carrier N`,
  with cardinality doubling.  This is `P2 at M = N` plus the
  forced-by-P1 cardinality `|carrier 1| = 2`.
* **P5** (Hom-as-content / operation-as-content): `carrier 4` has a
  ring structure realising `End(carrier 2)` (operations are themselves
  carrier elements).
* **P6** (V₄ minimality at `carrier 2`): `|carrier 2| = 4` with two
  commuting involutions whose composition is also involutive.
* **P7a** (aspect alphabet at `carrier 3`): `|carrier 3| = 8` with a
  zong involution giving a 4-本 + 4-征 split.
* **P7b** (atomic operations at `carrier 4`): `carrier 4` is
  ring-isomorphic to `Mat₂(F₂)`.

**Why this form?** It is the minimal data that:

1. Forces each component of `R N` (carriers, composition, bilinear,
   squaring, ring, modality, alphabet, atomic ops) to be witnessed at
   the corresponding layer of the satisfier.
2. Is *too tight* to be vacuously true: the existence of all eight
   fields is non-trivial — e.g., `(N : ℕ → Type) ↦ Unit` fails P6
   (cardinality 4) and P7b (Mat₂ structure).
3. Is *not so tight* as to bake in equivalence to R-family by fiat:
   the carrier family `S.carrier` is an arbitrary `ℕ → Type`, with
   no a priori connection to `R`.

The conclusion of T5-A then becomes: **the only family** satisfying all
eight closure clauses (in F₂-Boolean classical scope) is the R-family
itself — up to layerwise type / ring equivalence.
-/

/-- **P1P7_Satisfier_F2** — a family of carriers `S N : Type` indexed by
    layer `N : ℕ`, equipped with the F₂-Boolean specialisation of each
    P-closure condition.

    The conclusion of T5-A is `∀ S : P1P7_Satisfier_F2, ∀ N, S.carrier N ≃ R N`
    (as types, with ring equivalence at the layers where ring structure
    exists). -/
structure P1P7_Satisfier_F2 where
  /-- The carrier family — an arbitrary `ℕ → Type`, to be forced to
      `R` (= `fun N => Fin N → Bool`) by P1-P7. -/
  carrier : ℕ → Type
  /-- Each carrier is finite (decidability of equality + Fintype). -/
  fintype : ∀ N, Fintype (carrier N)
  /-- Each carrier has decidable equality. -/
  decEq : ∀ N, DecidableEq (carrier N)

  /-- **P1** — minimum non-trivial structure (F₂ at the base):
      `|carrier 1| = 2`.  Per `wen-substrate` v1.2 §2.1.

      This is the cardinality form of the "binary distinction forces
      F₂" lynchpin (Strategy A's char-2 forcing, applied to the base
      layer).  Combined with `carrier_isBooleanRing`, this gives the
      full F₂-base anchor. -/
  p1_base_card : Fintype.card (carrier 1) = 2

  /-- **P1+** — each carrier is a `BooleanRing`.  Per `wen-substrate`
      v1.2 §2.1 + Strategy A.

      This is the F₂-Boolean *operations* anchor (independent of the
      cardinality `p1_base_card` above).  Combined, they fully pin the
      base layer to `F₂` via `boolean_ring_embeds_into_R` from
      `Foundation/R/StrategyA.lean`. -/
  carrier_isBooleanRing : ∀ N, BooleanRing (carrier N)

  /-- **P2** — composition via direct sum:
      `carrier (N + M) ≃ carrier N × carrier M` as types.  Per
      `wen-substrate` v1.2 §2.2. -/
  p2_directSum : ∀ N M, carrier (N + M) ≃ carrier N × carrier M

  /-- **P3** — bilinear classification (3-layer, char-2):

      The carrier family supplies a `dot`, `sigma`, and `arf` matching
      `Foundation/R/Bilinear.lean`'s signature.  Per `wen-substrate`
      v1.2 §2.3.

      We state existence of the three forms at the family level; the
      identities (symmetry, alternation, Arf binary, decomposition
      `dot = sigma ⊕ LL`) are the content of the `dot`/`sigma`/`arf`
      *fields* below combined with `p3_identities`. -/
  p3_dot : ∀ N, carrier N → carrier N → Bool
  p3_sigma : ∀ k, carrier (2 * k) → carrier (2 * k) → Bool
  p3_arf : ∀ k, (Fin k → Bool) → Bool
  /-- The wen-algebra v0.6 §4 identities for the three layers. -/
  p3_identities :
      (∀ N (u v : carrier N), p3_dot N u v = p3_dot N v u)
    ∧ (∀ k (v : carrier (2 * k)), p3_sigma k v v = false)
    ∧ (∀ k (u v : carrier (2 * k)), p3_sigma k u v = p3_sigma k v u)
    ∧ (∀ k (c : Fin k → Bool), p3_arf k c = true ∨ p3_arf k c = false)
    -- Arf surjectivity (G6.1 strengthening): both classes inhabited
    ∧ (∀ k, (∃ c : Fin (k + 1) → Bool, p3_arf (k + 1) c = false)
          ∧ (∃ c : Fin (k + 1) → Bool, p3_arf (k + 1) c = true))

  /-- **P4** — squaring tower self-similarity:
      `carrier (N + N) ≃ carrier N × carrier N`.  Per `wen-substrate`
      v1.2 §2.4.

      This is `p2_directSum N N` — explicit field provided for the
      proof of the "tower forced from R₁" step. -/
  p4_squaring : ∀ N, carrier (N + N) ≃ carrier N × carrier N

  /-- **P5** — Hom-as-content: `carrier 4` has multiplication realising
      endomorphism composition on `carrier 2`, with a specified
      identity.  Per `wen-substrate` v1.2 §2.5. -/
  p5_mulR4 : carrier 4 → carrier 4 → carrier 4
  p5_oneR4 : carrier 4
  p5_id_left : ∀ f, p5_mulR4 p5_oneR4 f = f
  p5_id_right : ∀ f, p5_mulR4 f p5_oneR4 = f

  /-- **P6** — V₄ minimality at `carrier 2`: cardinality 4, with two
      commuting involutions whose composition is the third
      non-identity V₄ element.  Per `wen-substrate` v1.2 §2.6. -/
  p6_card : Fintype.card (carrier 2) = 4
  p6_invol_a : carrier 2 → carrier 2
  p6_invol_b : carrier 2 → carrier 2
  p6_invol_a_involutive : ∀ s, p6_invol_a (p6_invol_a s) = s
  p6_invol_b_involutive : ∀ s, p6_invol_b (p6_invol_b s) = s
  p6_invol_commute : ∀ s, p6_invol_a (p6_invol_b s) = p6_invol_b (p6_invol_a s)

  /-- **P7a** — aspect alphabet at `carrier 3`: cardinality 8 with a
      zong involution and 4-本 + 4-征 split.  Per `wen-substrate` v1.2 §2.7a. -/
  p7a_card : Fintype.card (carrier 3) = 8
  p7a_zong : carrier 3 → carrier 3
  p7a_zong_involutive : ∀ t, p7a_zong (p7a_zong t) = t
  /-- The fixed-point set of `zong` has exactly 4 elements (the 4 本-trigrams). -/
  p7a_fixed_card : Fintype.card { t : carrier 3 // p7a_zong t = t } = 4

  /-- **P7b** Mul on `carrier 4` — the `Mul` instance for the
      RingEquiv field below.  Per `wen-substrate` v1.2 §2.7b + G6.3
      Wedderburn uniqueness.

      Note: the field `p5_mulR4` is a *function*; this field wraps it
      in a `Mul` instance so the `RingEquiv` field can be stated. -/
  p7b_mul_instance : Mul (carrier 4)
  /-- **P7b** Add on `carrier 4` — the `Add` instance for the
      RingEquiv field below.  BooleanRing on `carrier 4` (from
      `carrier_isBooleanRing 4`) already gives Add, but we expose a
      dedicated field for explicit instance management. -/
  p7b_add_instance : Add (carrier 4)
  /-- **P7b** cardinality — `|carrier 4| = 16`.  Per `wen-substrate`
      v1.2 §2.7b. -/
  p7b_card : Fintype.card (carrier 4) = 16
  /-- **P7b** RingEquiv — `carrier 4 ≃+* Mat2F2` as F_2-algebras.
      Per `wen-substrate` v1.2 §2.7b + G6.3 Wedderburn uniqueness.

      Combined with `T_P7b_ring_equiv` from `PhaseZero`, this gives
      the Step 3 closure (transport of ring structure across the type
      equivalence proven in Step 2). -/
  p7b_mat2F2_equiv :
      @Nonempty
        (@RingEquiv (carrier 4) Mat2F2
          p7b_mul_instance Mat2F2.instMul
          p7b_add_instance Mat2F2.instAdd)

/-! ## § 2 The main theorem statement: T5_A

The conclusion of T5-A is that **any** `P1P7_Satisfier_F2` is layerwise
type-equivalent to R-family-over-F₂.  At the layers where ring structure
exists (`carrier 4` ↔ `Mat₂(F₂)` ↔ `R 4`), the equivalence lifts to a
ring isomorphism.

We state the **layerwise type-equivalence** form as the primary T5_A
theorem; the ring-iso refinement at `N = 4` is a corollary witnessed by
the structure's own `p7b_mat2F2_equiv` field combined with
`T_P7b_ring_equiv` from `PhaseZero`.

**Risk acknowledgement**: per the roadmap, the chosen form of T5-A may
require revision if the design above turns out either too tight (some
genuine F₂-Boolean substrate fails one of these eight clauses) or too
loose (some non-R-family structure satisfies all eight).  See the
`risk_assessment` docstring at the end of this file.
-/

/-- **T5-A (synthetic direction of Claim Z, F₂-Boolean classical scope)**.

    Any structure family `S : P1P7_Satisfier_F2` is layerwise
    type-equivalent to R-family-over-F₂:

        ∀ N, Nonempty (S.carrier N ≃ R N).

    The five-step proof scaffold is below; each step is currently
    `sorry`-stubbed with a TODO comment naming the
    Mathlib / infrastructure dependency required to close it.

    This is the **scaffolding** of T5-A — the full proof is the next
    2-4 months of work per the GUT roadmap Phase 2. -/
theorem T5_A : ∀ S : P1P7_Satisfier_F2, ∀ N : ℕ,
    Nonempty (S.carrier N ≃ R N) := by
  intro S N
  -- Equip the carrier with its Fintype / DecidableEq instances from the
  -- structure fields, so cardinality lemmas typecheck.
  haveI : Fintype (S.carrier N) := S.fintype N
  haveI : DecidableEq (S.carrier N) := S.decEq N
  -- ────────────────────────────────────────────────────────────────
  -- Step 1: P1 + P1+ + Boolean ring axioms ⟹ S.carrier N is a finite
  --         Boolean algebra.
  -- ────────────────────────────────────────────────────────────────
  have hBA : BooleanRing (S.carrier N) := S.carrier_isBooleanRing N
  -- Step 1 is essentially *free* given the structure design: we declared
  -- `carrier_isBooleanRing` as a structure field, so it's available
  -- directly.  The substantive content of Step 1 is the **forcing**
  -- argument — *why* a P1-P7 satisfier in F₂-Boolean scope must be a
  -- Boolean ring (rather than merely a Boolean algebra at the lattice
  -- level).  That forcing is the §8.4.1 Strategy A discharge content;
  -- it shows up here as a **structure design constraint** rather than
  -- a proof obligation, by choice of `P1P7_Satisfier_F2`.

  -- ────────────────────────────────────────────────────────────────
  -- Step 2: Stone / Birkhoff representation: finite BA ≃ F₂^N.
  -- ────────────────────────────────────────────────────────────────
  -- TODO (Step 2): Use `boolean_ring_embeds_into_R` from
  -- `Foundation/R/StrategyA.lean` to get an injection
  -- `S.carrier N ↪ R N'` for some `N'`.  Then use cardinality:
  -- `|S.carrier N|` must equal `2^N` (by `p2_directSum` + induction +
  -- `p1_base_card`), so `N' = N` and the injection is a bijection
  -- (hence an `Equiv`).
  --
  -- Mathlib pieces needed:
  --   * `Fintype.equivOfCardEq` (already used in Strategy A): finite
  --     types of equal cardinality are equiv.
  --   * Induction on `N` with `p2_directSum N 1 : carrier (N+1) ≃
  --     carrier N × carrier 1` (need to handle the `N + 1` vs `N + M`
  --     parity carefully).
  --
  -- Our infrastructure pieces needed:
  --   * `SSBX.Foundation.R.boolean_ring_embeds_into_R` (Strategy A
  --     deliverable (3)).
  --   * `R.card_eq` (= `|R N| = 2^N`).
  --
  -- Once cardinality is pinned to `2^N`, the type-equivalence
  -- `S.carrier N ≃ R N` follows from
  -- `Fintype.truncEquivOfCardEq` (cf. Strategy A's
  -- `boolean_ring_embeds_into_R` for the pattern).
  have hCardR : Fintype.card (R N) = 2 ^ N := R.card_eq N
  have hCardCarrier : Fintype.card (S.carrier N) = 2 ^ N := by
    sorry -- TODO Step 2: induction on N using p2_directSum at (N-1,1)
          -- and p1_base_card; base case is p1_base_card directly when N=1,
          -- and N=0 needs `|carrier 0| = 1` (an additional refinement of
          -- P1 — currently NOT a field; consider adding `p1_zero_card`
          -- or deriving from `BooleanRing` + emptiness of any rank-zero
          -- module).
  sorry
  -- ────────────────────────────────────────────────────────────────
  -- Step 3: P3-P5 + Wedderburn uniqueness ⟹ ring part pinned to M₂(F₂).
  -- ────────────────────────────────────────────────────────────────
  -- TODO (Step 3): Use `T_P7b_uniqueness_card_eq_16` from
  -- `PhaseZero/TP7bUniqueness.lean` together with `p7b_mat2F2_equiv` to
  -- transport `T_P7b_ring_equiv : R 4 ≃+* Mat2F2` to a
  -- `RingEquiv (S.carrier 4) (R 4)`.  Combined with Step 2 at `N = 4`,
  -- the type-equivalence at `N = 4` lifts to a ring equivalence.
  --
  -- Our infrastructure:
  --   * `T_P7b_ring_equiv : R 4 ≃+* Mat2F2`.
  --   * `T_P7b_uniqueness_card_eq_16` — any Fintype RingEquiv to
  --     Mat2F2 has card 16.
  --   * `p7b_mat2F2_equiv` (structure field) — supplies `carrier 4
  --     ≃+* Mat2F2`.
  --
  -- The two RingEquivs compose: `S.carrier 4 ≃+* Mat2F2 ≃+* R 4`
  -- (using `T_P7b_ring_equiv.symm`).  This is the Step-3 closure at the
  -- ring layer.

  -- ────────────────────────────────────────────────────────────────
  -- Step 4: P4 squaring + tower uniqueness ⟹ all R_N forced from R₁.
  -- ────────────────────────────────────────────────────────────────
  -- TODO (Step 4): Combine `p4_squaring` (= `p2_directSum N N`) with
  -- the base-layer equivalence `S.carrier 1 ≃ R 1` (from Step 2 at
  -- N=1) to induct upward:
  --   * `S.carrier (2N) ≃ S.carrier N × S.carrier N`  (p4_squaring)
  --   * `R (2N) ≃ R N × R N`  (R.squaringEquiv from
  --     `Foundation/R/Squaring.lean`)
  --   * If `S.carrier N ≃ R N` (induction hypothesis), then
  --     `S.carrier (2N) ≃ R N × R N ≃ R (2N)`.
  --
  -- This covers the powers-of-2 tower {1, 2, 4, 8, ...} directly.
  -- For arbitrary N, combine with `p2_directSum N M : carrier (N+M)
  -- ≃ carrier N × carrier M` and induction on N.
  --
  -- Our infrastructure:
  --   * `R.squaringEquiv (N : ℕ) : R (N + N) ≃ R N × R N` (from
  --     `Foundation/R/Squaring.lean`).
  --   * `R.R2_eq_R1_sq`, `R.R4_eq_R2_sq`, `R.R8_eq_R4_sq` — concrete
  --     witnesses at N = 1, 2, 4.
  --   * `Equiv.trans`, `Equiv.prodCongr` for composing equivs.

  -- ────────────────────────────────────────────────────────────────
  -- Step 5: 12-item D2 aggregator closes ⟹ S ≃ R-family-over-F₂.
  -- ────────────────────────────────────────────────────────────────
  -- TODO (Step 5): Aggregate the 12-item D2 closure (per `wen-substrate`
  -- v1.0.3 §3.1 — `RFamilyStructure.lean` is the navigation hub).  At
  -- this point the layerwise type-equivalence `S.carrier N ≃ R N` is
  -- proven for all `N` by Steps 2 + 4 induction; the bilinear forms
  -- (`p3_dot`, `p3_sigma`, `p3_arf`) transport across via the type
  -- equiv; the ring structure at `N = 4` is the Step 3 conclusion; the
  -- V₄ structure at `N = 2` is forced by the equivalence + `p6_card`
  -- agreeing with `T_P6_card`; the trigram structure at `N = 3` is
  -- forced by `p7a_card` agreeing with `R 3` cardinality.
  --
  -- Aggregator pieces (each of the 12 items of `wen-substrate` §3.1):
  --
  --   1. Carriers — Step 2 (`hCardCarrier` + truncEquivOfCardEq).
  --   2. Origin — N = 0 base case of Step 2.
  --   3. Direct sum — `p2_directSum` matches `R.directSumEquiv`.
  --   4. Bilinear layers — `p3_dot/sigma/arf` transport across the
  --      type equiv; agreement with `R.dot/sigma/arf` needs an extra
  --      naturality / uniqueness obligation (each `T_P3` clause from
  --      `PhaseZero` constrains the form modulo `Sp(2k, F_2)`).
  --   5. Squaring tower — Step 4.
  --   6. Hom-as-content — `p5_mulR4` transports across to match
  --      `composeR2` on `R 4`.
  --   7. Ring at R 4 — Step 3.
  --   8. R∞ profinite — `Foundation/RInfty/Profinite.lean` (not
  --      needed for finite-layer T5-A; deferred to T5-B/T5-C).
  --   9. Atlas naming on R 2 — orthogonal to T5-A claim (semantic
  --      naming layer; doesn't constrain the equivalence).
  --   10. R 3 aspect alphabet — `p7a_card` + `p7a_zong` transport.
  --   11. Atomic ops at R 4 — Step 3 + `T_P7b_uniqueness_card_eq_16`.
  --   12. Self-following / closure — meta-level; this theorem itself
  --       is the witness.

/-! ## § 3 Risk assessment

Per the GUT roadmap Phase 2, the T5-A statement above may need revision
in one of three ways if the design of `P1P7_Satisfier_F2` turns out
incorrect.  These three options are the **acknowledged risks** of the
synthetic direction:

-/

/--
**Risk assessment for T5-A (GUT roadmap Phase 2).**

The proof scaffold above may encounter one of three difficulties; per
the GUT roadmap, the corresponding mitigation in each case is:

* **Option (a)** — *Strengthen P1-P7*.

  If there exists a structure `S` satisfying `PClosure` (per
  `Foundation/R/ClaimZ.lean`) but **not** equivalent to R-family-over-F₂,
  then `P1P7_Satisfier_F2` above is too loose.  Mitigation: add
  constraints to the structure (e.g., naturality of the bilinear forms
  under `p2_directSum`, ring-uniqueness of `p7b_mat2F2_equiv`, etc.)
  until the loose-witness disappears.  This is standard foundational
  revision: the wen-substrate doctrine itself is being updated as
  Mathlib + our work clarify the necessary closure conditions.

* **Option (b)** — *Weaken T5-A statement*.

  If even after strengthening, strict layerwise iso (`carrier N ≃ R N`)
  is not the right notion of "equivalence", switch to **Morita
  equivalence** or **bi-interpretation**:

      ∀ S : P1P7_Satisfier_F2, MoritaEquiv S.carrier R

  This is the standard categorical move: pin equivalence at the level
  of *categories* rather than *families of types*.  Mathlib's
  `Mathlib.RingTheory.Morita` library + Wedderburn-Artin
  (`IsSimpleRing.exists_ringEquiv_matrix_divisionRing`) gives the
  Morita-form of T_P7b for free; T5-A becomes the statement that the
  full Morita equivalence (not just the ring at `N = 4`) is forced.

* **Option (c)** — *Change `PClosure` form*.

  If neither (a) nor (b) suffices — e.g., the closure conditions
  themselves are mis-articulated — revisit `PClosure` in
  `Foundation/R/ClaimZ.lean` and the wen-substrate v1.2 §2.1-§2.7
  definitions.  This is the **most disruptive** option: it would
  require re-doing Phase 1 (D1 ⟹ P_i) under the revised P-closure.
  The roadmap flags this as a *measure of last resort*.

**Current best-bet**: Option (a) is most likely needed at the
naturality level (item 4 of the §3.1 aggregator: bilinear forms must
agree with `R.dot/sigma/arf` *naturally* under `p2_directSum`, not just
as *some* forms with the right identities).  We expect to extend
`P1P7_Satisfier_F2` with naturality fields as Steps 2-4 are filled in.
-/
def risk_assessment : Unit := ()

/-! ## § 4 Summary

* **Status**: scaffolding phase.  All proof content is `sorry`-stubbed
  with explicit TODO comments naming each missing piece.
* **No new axioms** introduced.
* **Compiles** (modulo `sorry` warnings) — see lake build target
  `SSBX.Foundation.R.UniquenessF2`.
* **Next steps** per GUT roadmap Phase 2:
  1. Discharge Step 2 cardinality induction (estimated 2-3 weeks).
  2. Discharge Step 3 ring-uniqueness lift (estimated 2-3 weeks,
     mostly cleanup of `T_P7b_uniqueness_card_eq_16` + structure
     transport).
  3. Discharge Step 4 squaring-tower induction (estimated 1 month,
     requires careful handling of `p2_directSum` parity and the
     Atomic vs Tower distinction).
  4. Discharge Step 5 aggregator (estimated 1-2 months, mostly
     bookkeeping at the §3.1 12-item level, plus naturality
     refinements per the Risk Assessment).

Total: 2-4 months heavy work to close all five steps.

This file is the **commitment to the structural shape** of T5-A.
-/

end SSBX.Foundation.R.UniquenessF2
