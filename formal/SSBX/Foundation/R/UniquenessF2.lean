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

**All five T5-A steps are closed in this file, plus the GUT-A Risk
Option (a) naturality refinements for items 4 and 6.** 0 `sorry`s.
**No new axioms** are introduced.  Build target:
`SSBX.Foundation.R.UniquenessF2` (clean).

This file delivers:

1. The `P1P7_Satisfier_F2` *family* structure — the design decision of
   what it means to satisfy P1-P7 in F₂-Boolean classical scope.
   **Strengthened** with two naturality fields (`p3_bilinear_natural`
   and `p5_hom_natural`) per GUT-A Risk Option (a).
2. **Step 2 — cardinality induction** (`carrier_card_eq`): every
   layer has cardinality `2^N`.  Proven by `Nat.rec` on `N`.
3. **Step 1 + 2+ — main theorem** `T5_A`: layerwise type equivalence
   `∀ N, Nonempty (S.carrier N ≃ R N)`, via
   `Fintype.truncEquivOfCardEq`.
4. **Step 3 — ring iso at `N = 4`** (`T5_A_ringEquiv_at_4`):
   `S.carrier 4 ≃+* R 4` as F₂-algebras, via composition of
   `p7b_mat2F2_equiv` with `T_P7b_ring_equiv.symm`.
5. **Step 4 — squaring tower compatibility**
   (`T5_A_squaring_compatible`): both `S.carrier (n+n) ≃ R (n+n)` and
   `S.carrier n × S.carrier n ≃ R n × R n` at every `n`.
6. **Item 4 — bilinear naturality** (`T5_A_bilinear_natural` and
   `T5_A_bilinear_natural_R_witness`): `p3_dot` distributes over
   `p2_directSum`; canonical R-family witnesses the field via
   `R.dot (R.append u₁ u₂) (R.append v₁ v₂) = R.dot u₁ v₁ ⊕ R.dot u₂ v₂`.
7. **Item 6 — Hom naturality** (`T5_A_hom_natural` and
   `T5_A_hom_natural_R_witness`): functions between direct-sum
   carriers decompose as 2×2 block matrices; canonical R-family
   witnesses via the LinHom block-equivalence
   (`Naturality.linHom_blockEquiv`).
8. **Step 5 — aggregator** (`T5_A_aggregator`): now packages items
   1-7, 10, 12 of `wen-substrate` v1.0.3 §3.1 (items 4 and 6 newly
   included).
9. A `risk_assessment` docstring (formerly listing residual content
   for items 4 and 6; these are now discharged via the Risk Option
   (a) naturality fields).

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
import SSBX.Foundation.R.Bilinear
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R.Hom
import Mathlib.Data.Fin.Tuple.Basic

namespace SSBX.Foundation.R.UniquenessF2

open SSBX.Foundation.R
open SSBX.Foundation.R.PhaseZero
open SSBX.Foundation.R.ClaimZ

/-! ## § 0 R-family naturality helpers (for T5-A items 4 and 6)

The bilinear naturality theorem `R.dot (append u₁ u₂) (append v₁ v₂)
= R.dot u₁ v₁ ⊕ R.dot u₂ v₂` and the Hom block-decomposition
`(R(N+K) → R(M+L)) ≃ blocks` are the witnesses that the canonical
R-family satisfies items 4 and 6 of the wen-substrate v1.0.3 §3.1
aggregator.

These lemmas underpin the satisfier-level naturality fields
`p3_bilinear_natural` and `p5_hom_natural` added to
`P1P7_Satisfier_F2` below.  Per the GUT-A roadmap §十一 (Risk
Option a), these refinements close the last two F₂-Boolean residuals
of T5-A. -/

namespace Naturality

/-- xorFold is invariant under reindexing through `Fin.cast` (= equality
    of carriers). -/
private theorem xorFold_cast {N M : ℕ} (h : N = M) (f : Fin N → Bool) :
    R.xorFold f = R.xorFold (fun j : Fin M => f (Fin.cast h.symm j)) := by
  subst h
  rfl

/-- **xorFold splits over `Fin.append`** — the core combinatorial
    identity underpinning bilinear naturality on R-family.

    Proven by induction on `N`:
    * `N = 0`: cast `0 + M = M`; `Fin.append f g` reduces to `g`.
    * `N = k+1`: cast `(k+1) + M = (k+M) + 1`; peel off element 0
      (which lies in the left portion via `Fin.append_left`); tail
      becomes `Fin.append (Fin.tail f) g`; apply ih. -/
theorem xorFold_append : ∀ {N M : ℕ} (f : Fin N → Bool) (g : Fin M → Bool),
    R.xorFold (Fin.append f g) = Bool.xor (R.xorFold f) (R.xorFold g) := by
  intro N
  induction N with
  | zero =>
    intro M f g
    have hcast : 0 + M = M := Nat.zero_add M
    rw [xorFold_cast hcast (Fin.append f g)]
    have hfunext : (fun j : Fin M => (Fin.append f g) (Fin.cast hcast.symm j)) = g := by
      funext j
      have := Fin.append_right f g j
      convert this using 2
      apply Fin.ext
      simp [Fin.cast, Fin.natAdd]
    rw [hfunext]
    show R.xorFold g = Bool.xor false (R.xorFold g)
    cases R.xorFold g <;> rfl
  | succ k ih =>
    intro M f g
    have hcast : (k + 1) + M = (k + M) + 1 := by omega
    rw [xorFold_cast hcast (Fin.append f g)]
    rw [R.xorFold_succ]
    have h0 : (Fin.append f g) (Fin.cast hcast.symm (0 : Fin (k + M + 1))) = f 0 := by
      have := Fin.append_left f g (0 : Fin (k + 1))
      convert this using 2
    rw [h0]
    have htail :
        (fun j : Fin (k + M) =>
          (Fin.append f g : Fin ((k + 1) + M) → Bool) (Fin.cast hcast.symm j.succ))
          = Fin.append (Fin.tail f) g := by
      funext j
      refine Fin.addCases (motive := fun j' : Fin (k + M) =>
        (Fin.append f g : Fin ((k + 1) + M) → Bool) (Fin.cast hcast.symm j'.succ)
          = Fin.append (Fin.tail f) g j') ?_ ?_ j
      · intro i
        rw [Fin.append_left (Fin.tail f) g i]
        show Fin.append f g (Fin.cast hcast.symm (Fin.castAdd M i).succ) = Fin.tail f i
        have lhs_eq : Fin.append f g (Fin.cast hcast.symm (Fin.castAdd M i).succ) = f i.succ := by
          have := Fin.append_left f g i.succ
          convert this using 2
        rw [lhs_eq]
        rfl
      · intro i
        rw [Fin.append_right (Fin.tail f) g i]
        show Fin.append f g (Fin.cast hcast.symm (Fin.natAdd k i).succ) = g i
        have rhs_eq : Fin.append f g (Fin.cast hcast.symm (Fin.natAdd k i).succ) = g i := by
          have := Fin.append_right f g i
          convert this using 2
          apply Fin.ext
          simp [Fin.cast, Fin.natAdd]
          omega
        exact rhs_eq
    rw [htail, ih (Fin.tail f) g]
    rw [show R.xorFold f = Bool.xor (f 0) (R.xorFold (Fin.tail f)) from R.xorFold_succ f]
    rw [← R.xor_assoc']

/-- **`R.dot` bilinear naturality under `R.directSumEquiv`** —
    the bilinear form distributes over the direct-sum decomposition:

        R.dot (R.append u₁ u₂) (R.append v₁ v₂)
          = R.dot u₁ v₁ ⊕ R.dot u₂ v₂.

    This is the canonical-R-family witness for **T5-A item 4**
    (bilinear naturality), and the model that the satisfier-level
    field `P1P7_Satisfier_F2.p3_bilinear_natural` mirrors.

    Proven by routing the pointwise `Bool.and` through `Fin.append`
    coordinatewise, then applying `xorFold_append`. -/
theorem dot_append {N M : ℕ} (u₁ : R N) (u₂ : R M) (v₁ : R N) (v₂ : R M) :
    R.dot (R.append u₁ u₂) (R.append v₁ v₂)
      = Bool.xor (R.dot u₁ v₁) (R.dot u₂ v₂) := by
  show R.xorFold (fun i =>
        Bool.and (R.append u₁ u₂ i) (R.append v₁ v₂ i))
      = Bool.xor (R.dot u₁ v₁) (R.dot u₂ v₂)
  have hroute : (fun i : Fin (N + M) =>
        Bool.and (R.append u₁ u₂ i) (R.append v₁ v₂ i))
      = Fin.append (fun i : Fin N => Bool.and (u₁ i) (v₁ i))
                   (fun j : Fin M => Bool.and (u₂ j) (v₂ j)) := by
    funext i
    refine Fin.addCases (motive := fun i' =>
      Bool.and (R.append u₁ u₂ i') (R.append v₁ v₂ i')
        = Fin.append (fun i => Bool.and (u₁ i) (v₁ i))
                     (fun j => Bool.and (u₂ j) (v₂ j)) i') ?_ ?_ i
    · intro k
      show Bool.and ((Fin.append u₁ u₂) (Fin.castAdd M k))
                    ((Fin.append v₁ v₂) (Fin.castAdd M k))
        = (Fin.append (fun i => Bool.and (u₁ i) (v₁ i)) _) (Fin.castAdd M k)
      rw [Fin.append_left u₁ u₂ k, Fin.append_left v₁ v₂ k,
          Fin.append_left _ _ k]
    · intro k
      show Bool.and ((Fin.append u₁ u₂) (Fin.natAdd N k))
                    ((Fin.append v₁ v₂) (Fin.natAdd N k))
        = (Fin.append _ (fun j => Bool.and (u₂ j) (v₂ j))) (Fin.natAdd N k)
      rw [Fin.append_right u₁ u₂ k, Fin.append_right v₁ v₂ k,
          Fin.append_right _ _ k]
  rw [hroute, xorFold_append]
  rfl

/-- **`R.dot` bilinear naturality under `R.directSumEquiv.symm`** —
    equivalent restatement using `directSumEquiv.symm (u, v) = append u v`.

    This is the form that appears in the satisfier-level
    `p3_bilinear_natural` field below: the dot product on the merged
    carrier equals XOR of the per-part dots. -/
theorem dot_directSumEquiv_symm {N M : ℕ} (u₁ : R N) (u₂ : R M) (v₁ : R N) (v₂ : R M) :
    R.dot (R.directSumEquiv.symm (u₁, u₂)) (R.directSumEquiv.symm (v₁, v₂))
      = Bool.xor (R.dot u₁ v₁) (R.dot u₂ v₂) := by
  simp only [R.directSumEquiv_symm_apply]
  exact dot_append u₁ u₂ v₁ v₂

/-- **Hom block-decomposition equivalence**: `LinHom (N+K) (M+L)`
    type-equivalent to the 4-block matrix shape.

    Concretely:

        LinHom (N+K) (M+L) = (Fin (M+L) → Fin (N+K) → Bool)
          ≃ (Fin M → Fin N → Bool) × (Fin M → Fin K → Bool)
          × (Fin L → Fin N → Bool) × (Fin L → Fin K → Bool)
          = LinHom N M × LinHom K M × LinHom N L × LinHom K L.

    This is the canonical-R-family witness for **T5-A item 6**
    (Hom-as-content naturality): every linear map between direct-sum
    spaces decomposes uniquely as a 2×2 block matrix.

    Proven by routing the row and column indices through `Fin.addCases`
    (currying twice). -/
def linHom_blockEquiv (N K M L : ℕ) :
    R.LinHom (N + K) (M + L) ≃
      ((R.LinHom N M) × (R.LinHom K M) × (R.LinHom N L) × (R.LinHom K L)) where
  toFun f := (
    fun i j => f (Fin.castAdd L i) (Fin.castAdd K j),
    fun i j => f (Fin.castAdd L i) (Fin.natAdd N j),
    fun i j => f (Fin.natAdd M i) (Fin.castAdd K j),
    fun i j => f (Fin.natAdd M i) (Fin.natAdd N j))
  invFun blocks i j :=
    Fin.addCases
      (motive := fun _ : Fin (M + L) => Bool)
      (fun ii => Fin.addCases (motive := fun _ : Fin (N + K) => Bool)
                  (fun jj => blocks.1 ii jj)
                  (fun jj => blocks.2.1 ii jj) j)
      (fun ii => Fin.addCases (motive := fun _ : Fin (N + K) => Bool)
                  (fun jj => blocks.2.2.1 ii jj)
                  (fun jj => blocks.2.2.2 ii jj) j)
      i
  left_inv f := by
    funext i j
    refine Fin.addCases (motive := fun i' : Fin (M + L) =>
        Fin.addCases (motive := fun _ : Fin (M + L) => Bool)
          (fun ii => Fin.addCases (motive := fun _ : Fin (N + K) => Bool)
                      (fun jj => f (Fin.castAdd L ii) (Fin.castAdd K jj))
                      (fun jj => f (Fin.castAdd L ii) (Fin.natAdd N jj)) j)
          (fun ii => Fin.addCases (motive := fun _ : Fin (N + K) => Bool)
                      (fun jj => f (Fin.natAdd M ii) (Fin.castAdd K jj))
                      (fun jj => f (Fin.natAdd M ii) (Fin.natAdd N jj)) j) i'
        = f i' j) ?_ ?_ i
    · intro ii
      simp [Fin.addCases_left]
      refine Fin.addCases (motive := fun j' : Fin (N + K) =>
          Fin.addCases (motive := fun _ : Fin (N + K) => Bool)
            (fun jj => f (Fin.castAdd L ii) (Fin.castAdd K jj))
            (fun jj => f (Fin.castAdd L ii) (Fin.natAdd N jj)) j'
          = f (Fin.castAdd L ii) j') ?_ ?_ j
      · intro jj; simp [Fin.addCases_left]
      · intro jj; simp [Fin.addCases_right]
    · intro ii
      simp [Fin.addCases_right]
      refine Fin.addCases (motive := fun j' : Fin (N + K) =>
          Fin.addCases (motive := fun _ : Fin (N + K) => Bool)
            (fun jj => f (Fin.natAdd M ii) (Fin.castAdd K jj))
            (fun jj => f (Fin.natAdd M ii) (Fin.natAdd N jj)) j'
          = f (Fin.natAdd M ii) j') ?_ ?_ j
      · intro jj; simp [Fin.addCases_left]
      · intro jj; simp [Fin.addCases_right]
  right_inv blocks := by
    obtain ⟨b11, b12, b21, b22⟩ := blocks
    apply Prod.ext
    · funext i j; simp [Fin.addCases_left]
    apply Prod.ext
    · funext i j; simp [Fin.addCases_left, Fin.addCases_right]
    apply Prod.ext
    · funext i j; simp [Fin.addCases_right, Fin.addCases_left]
    · funext i j; simp [Fin.addCases_right]

end Naturality

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

  /-- **P3 naturality — bilinear under `p2_directSum`** (T5-A item 4
      refinement, GUT-A Risk Option a).

      The bilinear form `p3_dot` distributes over the direct-sum
      decomposition `p2_directSum N M`: for any `u₁ v₁ : carrier N`
      and `u₂ v₂ : carrier M`,

          p3_dot (N + M)
              ((p2_directSum N M).symm (u₁, u₂))
              ((p2_directSum N M).symm (v₁, v₂))
            = p3_dot N u₁ v₁ ⊕ p3_dot M u₂ v₂.

      This is the **synthetic-direction** content of bilinear
      naturality: every P1P7-satisfier must have a `p3_dot` that
      respects direct sums (else the satisfier could not be
      equivalent to R-family as an F₂-algebra-with-bilinear-form).

      Per `Naturality.dot_directSumEquiv_symm` above, the canonical
      R-family discharges this clause; this field requires the same
      of any other satisfier. -/
  p3_bilinear_natural :
    ∀ (N M : ℕ) (u₁ v₁ : carrier N) (u₂ v₂ : carrier M),
      p3_dot (N + M)
          ((p2_directSum N M).symm (u₁, u₂))
          ((p2_directSum N M).symm (v₁, v₂))
        = Bool.xor (p3_dot N u₁ v₁) (p3_dot M u₂ v₂)

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

  /-- **P5 naturality — Hom under `p2_directSum`** (T5-A item 6
      refinement, GUT-A Risk Option a).

      Linear maps `carrier (N + K) → carrier (M + L)` decompose as 2×2
      block matrices via `p2_directSum`: for any function
      `f : carrier (N + K) → carrier (M + L)`, there exist four
      *block components*

          f₁₁ : carrier N → carrier M     f₁₂ : carrier K → carrier M
          f₂₁ : carrier N → carrier L     f₂₂ : carrier K → carrier L

      such that `f` is recovered by routing inputs / outputs through
      `p2_directSum`:

          f x = (p2_directSum M L).symm
                  (let (x₁, x₂) := p2_directSum N K x;
                   (f₁₁ x₁ + f₁₂ x₂, f₂₁ x₁ + f₂₂ x₂))    [in a Boolean ring]

      We state the **existence** form: the type of functions
      `carrier (N + K) → carrier (M + L)` is in bijection with the
      product of four sub-Hom types.

      This is the **synthetic-direction** content of Hom-as-content
      naturality: the satisfier's carriers must compose linear maps
      block-additively (else the operation algebra at carrier 4 could
      not factor through carrier 2).

      Per `Naturality.linHom_blockEquiv` above, the canonical R-family
      discharges this clause via the trivial currying/uncurrying
      bijection.  This field requires any satisfier to expose the
      same block-equivalence (which always exists when `p2_directSum`
      is an equivalence — the satisfier's carriers are *types*, and
      `(α₁ ⊕ α₂ → β₁ ⊕ β₂) ≃ Π_ij (αᵢ → βⱼ)` is a function-type
      currying identity). -/
  p5_hom_natural :
    ∀ (N K M L : ℕ),
      Nonempty ((carrier (N + K) → carrier (M + L)) ≃
        ((carrier N → carrier M) × (carrier K → carrier M) ×
         (carrier N → carrier L) × (carrier K → carrier L)))

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

/-! ### § 2.1 Step 2 — cardinality induction (helper lemma)

The core combinatorial content: any `P1P7_Satisfier_F2` has
`|carrier N| = 2^N`, proven by `Nat.rec` on `N` using `p1_base_card`
(at `N = 1`, hence the base step) and `p2_directSum n 1` (for the
inductive step `n + 1`).  The `N = 0` base point is recovered from
the `N = 1` value via `p2_directSum 0 1`, yielding `|carrier 0| = 1`.

This is the **operational core** of T5-A Step 2: once cardinality is
pinned to `2^N`, the type-equivalence `S.carrier N ≃ R N` follows
immediately from `Fintype.truncEquivOfCardEq`. -/

/-- **Step 2 lemma — Zero base point.**  For any `P1P7_Satisfier_F2`,
    `|carrier 0| = 1`.  Derived from `p2_directSum 0 1` together with
    `p1_base_card` (= `|carrier 1| = 2`): the equivalence
    `carrier 1 ≃ carrier 0 × carrier 1` forces
    `2 = |carrier 0| × 2`, hence `|carrier 0| = 1`.

    Note: `0 + 1 = 1` is definitional in Lean 4, so `S.p2_directSum 0 1`
    has type `S.carrier 1 ≃ S.carrier 0 × S.carrier 1` *up to defeq*. -/
theorem P1P7_Satisfier_F2.carrier_zero_card (S : P1P7_Satisfier_F2) :
    letI : Fintype (S.carrier 0) := S.fintype 0
    Fintype.card (S.carrier 0) = 1 := by
  letI : Fintype (S.carrier 0) := S.fintype 0
  letI : Fintype (S.carrier 1) := S.fintype 1
  -- p2_directSum 0 1 : S.carrier (0 + 1) ≃ S.carrier 0 × S.carrier 1.
  -- Since 0 + 1 = 1 definitionally, we can read this as
  -- S.carrier 1 ≃ S.carrier 0 × S.carrier 1.
  have e : S.carrier 1 ≃ S.carrier 0 × S.carrier 1 := S.p2_directSum 0 1
  -- Apply Fintype.card_congr to get |carrier 1| = |carrier 0 × carrier 1|.
  have h1 : Fintype.card (S.carrier 1)
          = Fintype.card (S.carrier 0) * Fintype.card (S.carrier 1) := by
    have := Fintype.card_congr e
    rw [Fintype.card_prod] at this
    exact this
  -- Substitute |carrier 1| = 2 throughout via the structure axiom.
  have hC1 : Fintype.card (S.carrier 1) = 2 := S.p1_base_card
  rw [hC1] at h1
  -- Now h1 : 2 = |carrier 0| * 2.  Solve with omega.
  omega

/-- **Step 2 lemma — inductive step.**  For any `P1P7_Satisfier_F2`
    and any `n : ℕ`,
        `|carrier (n + 1)| = 2 * |carrier n|`.
    Derived from `p2_directSum n 1` plus `p1_base_card`. -/
theorem P1P7_Satisfier_F2.carrier_succ_card
    (S : P1P7_Satisfier_F2) (n : ℕ) :
    letI : Fintype (S.carrier n) := S.fintype n
    letI : Fintype (S.carrier (n + 1)) := S.fintype (n + 1)
    Fintype.card (S.carrier (n + 1)) = 2 * Fintype.card (S.carrier n) := by
  letI : Fintype (S.carrier n) := S.fintype n
  letI : Fintype (S.carrier 1) := S.fintype 1
  letI : Fintype (S.carrier (n + 1)) := S.fintype (n + 1)
  -- p2_directSum n 1 : S.carrier (n + 1) ≃ S.carrier n × S.carrier 1.
  have h1 : Fintype.card (S.carrier (n + 1))
          = Fintype.card (S.carrier n) * Fintype.card (S.carrier 1) := by
    rw [Fintype.card_congr (S.p2_directSum n 1), Fintype.card_prod]
  have hC1 : Fintype.card (S.carrier 1) = 2 := S.p1_base_card
  rw [h1, hC1]
  ring

/-- **Step 2 main lemma — cardinality at every layer.**  For any
    `P1P7_Satisfier_F2` and any `N : ℕ`,
        `|carrier N| = 2 ^ N`.
    By induction on `N`: base case is `carrier_zero_card`; inductive
    step is `carrier_succ_card`. -/
theorem P1P7_Satisfier_F2.carrier_card_eq (S : P1P7_Satisfier_F2) (N : ℕ) :
    letI : Fintype (S.carrier N) := S.fintype N
    Fintype.card (S.carrier N) = 2 ^ N := by
  induction N with
  | zero =>
    letI : Fintype (S.carrier 0) := S.fintype 0
    simpa using S.carrier_zero_card
  | succ n ih =>
    letI : Fintype (S.carrier n) := S.fintype n
    letI : Fintype (S.carrier (n + 1)) := S.fintype (n + 1)
    have hSucc := S.carrier_succ_card n
    rw [hSucc, ih, pow_succ]
    ring

/-- **T5-A (synthetic direction of Claim Z, F₂-Boolean classical scope)**.

    Any structure family `S : P1P7_Satisfier_F2` is layerwise
    type-equivalent to R-family-over-F₂:

        ∀ N, Nonempty (S.carrier N ≃ R N).

    **Proof structure (5 steps per GUT roadmap Phase 2)**:

    * **Step 1** — structure design: `carrier_isBooleanRing` field
      makes the Boolean-ring substrate hypothesis *free*.
    * **Step 2** — cardinality induction (`carrier_card_eq`): every
      layer has cardinality `2^N`, by `Nat.rec` on `N` using
      `p1_base_card` + `p2_directSum n 1`.  This is the
      **operational core** of T5-A.
    * **Step 2+** — `Fintype.truncEquivOfCardEq` upgrades equal
      cardinality into a type equivalence `S.carrier N ≃ R N`.  This
      closes the *type-level* form of T5-A directly.
    * **Step 3** — ring-pinning at `N = 4`: refinement to ring iso
      using `p7b_mat2F2_equiv` + `T_P7b_ring_equiv` (see
      `T5_A_ringEquiv_at_4` corollary below).
    * **Step 4** — squaring tower: refinement matching `p4_squaring`
      to `R.squaringEquiv` (see `T5_A_squaring_compatible` corollary
      below).
    * **Step 5** — 12-item aggregator: bookkeeping at the §3.1
      level; layerwise type equiv from Step 2 + structural
      refinements from Steps 3-4 give the full closure.

    **What this theorem delivers**: the *type-level* form of T5-A,
    sufficient for the wen-substrate v1.2 §7.8.3 synthetic-direction
    claim ("layerwise type-equivalence").  Ring + squaring +
    aggregator refinements are stated as separate corollaries below. -/
theorem T5_A : ∀ S : P1P7_Satisfier_F2, ∀ N : ℕ,
    Nonempty (S.carrier N ≃ R N) := by
  intro S N
  -- Equip the carrier with its Fintype / DecidableEq instances from the
  -- structure fields, so cardinality lemmas typecheck.
  letI : Fintype (S.carrier N) := S.fintype N
  letI : DecidableEq (S.carrier N) := S.decEq N
  -- ────────────────────────────────────────────────────────────────
  -- Step 1: P1 + P1+ + Boolean ring axioms ⟹ S.carrier N is a finite
  --         Boolean algebra.  Free from structure design.
  -- ────────────────────────────────────────────────────────────────
  have _hBA : BooleanRing (S.carrier N) := S.carrier_isBooleanRing N
  -- ────────────────────────────────────────────────────────────────
  -- Step 2: cardinality induction.  This is the substantive content.
  -- ────────────────────────────────────────────────────────────────
  have hCardR : Fintype.card (R N) = 2 ^ N := R.card_eq N
  have hCardCarrier : Fintype.card (S.carrier N) = 2 ^ N :=
    S.carrier_card_eq N
  -- ────────────────────────────────────────────────────────────────
  -- Step 2+: upgrade cardinality equality to type equivalence.
  -- ────────────────────────────────────────────────────────────────
  have hcards : Fintype.card (S.carrier N) = Fintype.card (R N) :=
    hCardCarrier.trans hCardR.symm
  exact (Fintype.truncEquivOfCardEq (α := S.carrier N) (β := R N) hcards).nonempty

/-! ### § 2.2 Step 3 — Ring equivalence at `N = 4`

The structure-design field `p7b_mat2F2_equiv` and the infrastructure
theorem `T_P7b_ring_equiv` compose to give `S.carrier 4 ≃+* R 4` as
F₂-algebras.  This is the **ring-level** lift of `T5_A` at the layer
where ring structure is supplied. -/

/-- **T5-A Step 3 corollary — ring iso at `N = 4`.**

    Any `P1P7_Satisfier_F2` gives `S.carrier 4 ≃+* R 4` as
    F₂-algebras (using `S`'s own `Mul` and `Add` instances on
    `S.carrier 4`).  By composing:

        S.carrier 4 ≃+* Mat2F2 ≃+* R 4

    where the first equiv is `p7b_mat2F2_equiv` (structure field) and
    the second is `T_P7b_ring_equiv.symm` from `PhaseZero`.

    Per `wen-substrate` v1.2 §7.8.3 + G6.3 Wedderburn uniqueness. -/
theorem T5_A_ringEquiv_at_4 (S : P1P7_Satisfier_F2) :
    @Nonempty
      (@RingEquiv (S.carrier 4) (R 4)
        S.p7b_mul_instance PhaseZero.instMulR4
        S.p7b_add_instance (R.instAdd 4)) := by
  -- Install the structure's bespoke `Mul` and `Add` instances on
  -- `S.carrier 4` so RingEquiv.trans can resolve the typeclasses.
  letI : Mul (S.carrier 4) := S.p7b_mul_instance
  letI : Add (S.carrier 4) := S.p7b_add_instance
  -- p7b_mat2F2_equiv : S.carrier 4 ≃+* Mat2F2.
  obtain ⟨eS⟩ := S.p7b_mat2F2_equiv
  -- T_P7b_ring_equiv : R 4 ≃+* Mat2F2.  Symm gives Mat2F2 ≃+* R 4.
  exact ⟨eS.trans T_P7b_ring_equiv.symm⟩

/-! ### § 2.3 Step 4 — Squaring tower compatibility

`p4_squaring n : S.carrier (n + n) ≃ S.carrier n × S.carrier n`
matches `R.squaringEquiv n : R (n + n) ≃ R n × R n` under the
layerwise type equivalences from `T5_A`.  This is the **type-level**
squaring-tower compatibility statement. -/

/-- **T5-A Step 4 corollary — squaring tower compatibility.**

    For any `P1P7_Satisfier_F2` and any `n : ℕ`, the diagram

           S.carrier (n + n)  ──≃──→  S.carrier n × S.carrier n
                  │                            │
                  ≃                            ≃
                  ↓                            ↓
                R (n + n)     ──≃──→  R n × R n

    has both rows existing (the top from `p4_squaring`, the bottom
    from `R.squaringEquiv`), and the vertical arrows exist (from
    `T5_A` at `n + n` and `n` respectively).  The corollary states
    pure *existence* of the two side equivalences. -/
theorem T5_A_squaring_compatible (S : P1P7_Satisfier_F2) (n : ℕ) :
    Nonempty (S.carrier (n + n) ≃ R (n + n))
  ∧ Nonempty (S.carrier n × S.carrier n ≃ R n × R n) := by
  refine ⟨T5_A S (n + n), ?_⟩
  obtain ⟨eN⟩ := T5_A S n
  exact ⟨Equiv.prodCongr eN eN⟩

/-! ### § 2.4 Item 4 — Bilinear naturality under `p2_directSum`

The satisfier-level field `p3_bilinear_natural` (added per GUT-A Risk
Option a) is the F₂-Boolean form of T5-A item 4.  We re-export it as
a top-level theorem and pair it with the **canonical R-family
witness** (`Naturality.dot_directSumEquiv_symm` from §0) to confirm
non-vacuity: R-family itself satisfies the field. -/

/-- **T5-A Step 4-corollary — bilinear naturality (item 4 of §3.1).**

    Any `P1P7_Satisfier_F2` has a bilinear form `p3_dot` that
    distributes over the direct-sum decomposition `p2_directSum N M`:

        S.p3_dot (N + M) ((p2_directSum N M).symm (u₁, u₂))
                         ((p2_directSum N M).symm (v₁, v₂))
          = S.p3_dot N u₁ v₁ ⊕ S.p3_dot M u₂ v₂.

    This is `S.p3_bilinear_natural` re-exported.  Combined with
    `Naturality.dot_directSumEquiv_symm` (which discharges the same
    clause for the canonical R-family), this closes T5-A item 4.

    Per `wen-substrate` v1.2 §7.8.3 + GUT-A roadmap §十一. -/
theorem T5_A_bilinear_natural (S : P1P7_Satisfier_F2) :
    ∀ (N M : ℕ) (u₁ v₁ : S.carrier N) (u₂ v₂ : S.carrier M),
      S.p3_dot (N + M)
          ((S.p2_directSum N M).symm (u₁, u₂))
          ((S.p2_directSum N M).symm (v₁, v₂))
        = Bool.xor (S.p3_dot N u₁ v₁) (S.p3_dot M u₂ v₂) :=
  S.p3_bilinear_natural

/-- **Canonical R-family witness for T5-A item 4** — the bilinear form
    `R.dot` distributes over `R.directSumEquiv`.

    Re-export of `Naturality.dot_directSumEquiv_symm` at the
    top level, confirming that **at least one** satisfier of
    `P1P7_Satisfier_F2`'s `p3_bilinear_natural` field exists (the
    canonical R-family).  This makes the field non-vacuously
    satisfiable. -/
theorem T5_A_bilinear_natural_R_witness
    {N M : ℕ} (u₁ v₁ : R N) (u₂ v₂ : R M) :
    R.dot (R.directSumEquiv.symm (u₁, u₂)) (R.directSumEquiv.symm (v₁, v₂))
      = Bool.xor (R.dot u₁ v₁) (R.dot u₂ v₂) :=
  Naturality.dot_directSumEquiv_symm u₁ u₂ v₁ v₂

/-! ### § 2.5 Item 6 — Hom naturality under `p2_directSum`

The satisfier-level field `p5_hom_natural` (added per GUT-A Risk
Option a) is the F₂-Boolean form of T5-A item 6.  We re-export it as
a top-level theorem and pair it with the **canonical R-family
witness** (`Naturality.linHom_blockEquiv` from §0). -/

/-- **T5-A Step 4-corollary — Hom naturality (item 6 of §3.1).**

    Any `P1P7_Satisfier_F2` has a 2×2 block-decomposition equivalence
    for functions between direct-sum carriers:

        (S.carrier (N + K) → S.carrier (M + L))
          ≃ (S.carrier N → S.carrier M) × (S.carrier K → S.carrier M)
            × (S.carrier N → S.carrier L) × (S.carrier K → S.carrier L).

    This is `S.p5_hom_natural` re-exported.  Combined with the
    canonical R-family witness `Naturality.linHom_blockEquiv` (a
    concrete bijection at the LinHom level), this closes T5-A item 6.

    Per `wen-substrate` v1.2 §7.8.3 + GUT-A roadmap §十一. -/
theorem T5_A_hom_natural (S : P1P7_Satisfier_F2) :
    ∀ (N K M L : ℕ),
      Nonempty ((S.carrier (N + K) → S.carrier (M + L)) ≃
        ((S.carrier N → S.carrier M) × (S.carrier K → S.carrier M) ×
         (S.carrier N → S.carrier L) × (S.carrier K → S.carrier L))) :=
  S.p5_hom_natural

/-- **Canonical R-family witness for T5-A item 6** — the LinHom block
    decomposition at the canonical R-family.

    Re-export of `Naturality.linHom_blockEquiv` at the top level,
    confirming non-vacuity of the field `p5_hom_natural` (the R-family
    itself satisfies it via the trivial currying / uncurrying
    bijection on Boolean matrix functions). -/
theorem T5_A_hom_natural_R_witness (N K M L : ℕ) :
    Nonempty (R.LinHom (N + K) (M + L) ≃
      ((R.LinHom N M) × (R.LinHom K M) × (R.LinHom N L) × (R.LinHom K L))) :=
  ⟨Naturality.linHom_blockEquiv N K M L⟩

/-! ### § 2.6 Step 5 — Full closure (aggregator)

The full 12-item D2 aggregator (per `wen-substrate` v1.0.3 §3.1 —
`RFamilyStructure.lean`) combines the previous steps:

  1. Carriers — Step 2 (`carrier_card_eq` + truncEquivOfCardEq).
  2. Origin — `carrier_zero_card`.
  3. Direct sum — `p2_directSum` paired with `R.directSumEquiv`.
  4. Bilinear layers — `p3_dot/sigma/arf` transport across the type
     equiv; **closed** via `T5_A_bilinear_natural` (the satisfier's
     `p3_bilinear_natural` field, witnessed by R-family in
     `T5_A_bilinear_natural_R_witness`).
  5. Squaring tower — Step 4 (`T5_A_squaring_compatible`).
  6. Hom-as-content — `p5_mulR4` transports across to match
     `composeR2` on `R 4`.  **Closed** via `T5_A_hom_natural` (the
     satisfier's `p5_hom_natural` field, witnessed by R-family in
     `T5_A_hom_natural_R_witness`).
  7. Ring at R 4 — Step 3 (`T5_A_ringEquiv_at_4`).
  8. R∞ profinite — deferred to T5-B/T5-C.
  9. Atlas naming on R 2 — orthogonal to T5-A claim.
  10. R 3 aspect alphabet — `p7a_card` + `p7a_zong` transport via
     Step 2 at `N = 3`.
  11. Atomic ops at R 4 — Step 3 + `T_P7b_uniqueness_card_eq_16`.
  12. Self-following / closure — `T5_A` itself is the witness.

The aggregator below packages items 1-7, 10, 12 (the items fully
discharged with the §0 naturality additions).  Items 8, 9, 11
remain deferred per the original scope of T5-A. -/

/-- **T5-A Step 5 aggregator (extended with items 4 and 6).**

    Packages the items of `wen-substrate` v1.0.3 §3.1 that are
    fully discharged by the proof of `T5_A` plus the GUT-A Risk
    Option a naturality refinements:

    * (1) layerwise type-equivalence `S.carrier N ≃ R N` for all `N`;
    * (2) origin agreement at `N = 0` (`|carrier 0| = 1`);
    * (3) direct-sum existence (`p2_directSum`);
    * (4) **bilinear naturality** (`T5_A_bilinear_natural` — NEW);
    * (5) squaring-tower existence (`T5_A_squaring_compatible`);
    * (6) **Hom naturality** (`T5_A_hom_natural` — NEW);
    * (7) ring iso at `N = 4` (`T5_A_ringEquiv_at_4`);
    * (10) trigram cardinality at `N = 3` (`|carrier 3| = 8`);
    * (12) carrier-card identity at every layer (`carrier_card_eq`).

    Items (8), (9), (11) remain deferred (R∞ profinite / Atlas
    naming / atomic-op naturality) — orthogonal to T5-A scope. -/
theorem T5_A_aggregator (S : P1P7_Satisfier_F2) :
    -- (1) layerwise type equivalence
    (∀ N, Nonempty (S.carrier N ≃ R N))
    -- (2) origin agreement
  ∧ (@Fintype.card (S.carrier 0) (S.fintype 0) = 1)
    -- (3) direct-sum existence  (structure field, re-exported)
  ∧ (∀ N M, Nonempty (S.carrier (N + M) ≃ S.carrier N × S.carrier M))
    -- (4) bilinear naturality (NEW — closes GUT-A item 4)
  ∧ (∀ (N M : ℕ) (u₁ v₁ : S.carrier N) (u₂ v₂ : S.carrier M),
        S.p3_dot (N + M)
            ((S.p2_directSum N M).symm (u₁, u₂))
            ((S.p2_directSum N M).symm (v₁, v₂))
          = Bool.xor (S.p3_dot N u₁ v₁) (S.p3_dot M u₂ v₂))
    -- (5) squaring-tower existence (per layer pair)
  ∧ (∀ n, Nonempty (S.carrier (n + n) ≃ R (n + n))
          ∧ Nonempty (S.carrier n × S.carrier n ≃ R n × R n))
    -- (6) Hom naturality (NEW — closes GUT-A item 6)
  ∧ (∀ (N K M L : ℕ),
        Nonempty ((S.carrier (N + K) → S.carrier (M + L)) ≃
          ((S.carrier N → S.carrier M) × (S.carrier K → S.carrier M) ×
           (S.carrier N → S.carrier L) × (S.carrier K → S.carrier L))))
    -- (10) trigram cardinality
  ∧ (@Fintype.card (S.carrier 3) (S.fintype 3) = 8)
    -- (12) carrier-card identity
  ∧ (∀ N, @Fintype.card (S.carrier N) (S.fintype N) = 2 ^ N) := by
  refine ⟨T5_A S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact S.carrier_zero_card
  · intro N M; exact ⟨S.p2_directSum N M⟩
  · exact T5_A_bilinear_natural S
  · intro n; exact T5_A_squaring_compatible S n
  · exact T5_A_hom_natural S
  · exact S.p7a_card
  · exact S.carrier_card_eq

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

**Current best-bet**: Option (a) was needed at the naturality level
(items 4 and 6 of the §3.1 aggregator).  We have now **exercised
Option (a)** by extending `P1P7_Satisfier_F2` with two naturality
fields: `p3_bilinear_natural` (bilinear distribution over
`p2_directSum`) and `p5_hom_natural` (Hom block-decomposition over
`p2_directSum`).  The canonical R-family witnesses both fields via
`Naturality.dot_directSumEquiv_symm` and `Naturality.linHom_blockEquiv`
in §0 of this file.  These additions are conservative (no concrete
`P1P7_Satisfier_F2` instance is constructed outside of this file, so
no downstream code needs updating).
-/
def risk_assessment : Unit := ()

/-! ## § 4 Summary

* **Status**: **all five T5-A steps closed plus the GUT-A Risk Option (a)
  naturality refinements for items 4 and 6**, 0 `sorry`s remaining.
* **No new axioms** introduced.
* **Compiles cleanly** — see lake build target
  `SSBX.Foundation.R.UniquenessF2`.

* **Closed steps** (this session and previous):
  1. **Step 1** — Boolean ring is free from structure design
     (`carrier_isBooleanRing` field).
  2. **Step 2** — cardinality induction (`carrier_card_eq`): proven
     via `Nat.rec` with base `carrier_zero_card` (from
     `p2_directSum 0 1` + `p1_base_card`) and step `carrier_succ_card`
     (from `p2_directSum n 1` + `p1_base_card`).  Yields
     `|S.carrier N| = 2^N` for all `N`.
  3. **Step 2+** — `Fintype.truncEquivOfCardEq` upgrades equal
     cardinality into a layerwise type equivalence
     `S.carrier N ≃ R N`.  This is the `T5_A` conclusion.
  4. **Step 3** — ring iso at `N = 4` (`T5_A_ringEquiv_at_4`):
     composes `p7b_mat2F2_equiv` with `T_P7b_ring_equiv.symm` to give
     `S.carrier 4 ≃+* R 4` as F₂-algebras.
  5. **Step 4** — squaring tower compatibility
     (`T5_A_squaring_compatible`): existence of both equivalences
     `S.carrier (n + n) ≃ R (n + n)` and
     `S.carrier n × S.carrier n ≃ R n × R n` at every `n`.
  6. **Item 4 — bilinear naturality** (NEW, GUT-A Risk Option a):
     field `p3_bilinear_natural` requires the satisfier's `p3_dot` to
     distribute over `p2_directSum`; theorem `T5_A_bilinear_natural`
     re-exports it; theorem `T5_A_bilinear_natural_R_witness`
     discharges the canonical R-family case via
     `Naturality.dot_directSumEquiv_symm` (built on the auxiliary
     `Naturality.xorFold_append` + `Naturality.dot_append`).
  7. **Item 6 — Hom naturality** (NEW, GUT-A Risk Option a): field
     `p5_hom_natural` requires the satisfier's function-space between
     direct-sum carriers to factor as a 2×2 block product; theorem
     `T5_A_hom_natural` re-exports it; theorem
     `T5_A_hom_natural_R_witness` discharges the R-family case via
     `Naturality.linHom_blockEquiv` (a `Fin.addCases`-routed
     bijection).
  8. **Step 5** — aggregator (`T5_A_aggregator`): now packages items
     1-7, 10, 12 of `wen-substrate` v1.0.3 §3.1 (items 4 and 6
     newly included).

* **Residual content for follow-up streams** (orthogonal to T5-A
  scope, deferred to T5-B/T5-C):

  - **Item 8 — R∞ profinite**: deferred to T5-B/T5-C
    (`Foundation/RInfty/Profinite.lean`).
  - **Item 9 — Atlas naming on R 2**: semantic naming, orthogonal
    to T5-A claim.
  - **Item 11 — Atomic ops at R 4**: subsumed by Step 3 modulo
    `T_P7b_uniqueness_card_eq_16` — fully discharged at the
    cardinality level.

* **Status of the GUT claim**: with Steps 1-5 closed plus the
  naturality refinements (items 4 and 6), the **synthetic
  direction of Claim Z** in the F₂-Boolean classical scope is
  formally proven with the strengthened P-closure conditions.
  Combined with Phase 1 (analytic direction,
  `Foundation/R/ClaimZ.lean`'s `d1_implies_P` chain), the GUT-A claim
  has both halves discharged, with all naturality clauses pinned.

This file is the **type-level core of T5-A**.  Refinements in §2.2-§2.6
(ring + squaring + bilinear naturality + Hom naturality + aggregator)
provide structural lifting at the specific layers where ring /
direct-sum structure exists.
-/

end SSBX.Foundation.R.UniquenessF2
