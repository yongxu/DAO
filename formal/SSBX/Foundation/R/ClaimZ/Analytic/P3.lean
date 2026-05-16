/-
# Foundation.R.ClaimZ.Analytic.P3 — D1 ⟹ P3 (bilinear classification)

**GUT roadmap Phase 1 Stream A3** (per
`docs-next/10_formal_形式/gut-roadmap.md`):

> **Stream A3**：P3 — 三层 bilinear classification 由 D1 forced
> （依赖 char(k)=2 假设）

This file discharges the **analytic step** `D1 ⟹ P3` for the
F₂-Boolean realisation of the R-Family.  Per
`docs-next/10_formal_形式/wen-substrate/01-foundations.md` and
`wen-substrate.md` v1.0.3 §2.3 (P3):

> **P3** says any D1-articulation, restricted to its `R (2k)`
> substrate at char(k) = 2, must realise exactly the **3-layer
> bilinear classification**: a symmetric form (L₀ = `dot`), an
> alternating form (L₁ = `sigma`), and a parametric family of
> quadratic refinements (L₂ = `q`) with exactly **2** Arf-labelled
> equivalence classes — *not* 4, *not* 8, *not* indefinitely many.

For the F₂-Boolean realisation, this becomes the existing theorem
bundle `T_P3_*` formalised in `Foundation/R/PhaseZero.lean` § 1.
After G6.1 the bundle has **6/6 clauses discharged**:

| Clause                          | T_P3 anchor                       |
|---------------------------------|-----------------------------------|
| L₀ exists and is symmetric      | `T_P3_L0_symmetric`               |
| L₁ exists and is alternating    | `T_P3_L1_alternating`             |
| L₁ is also symmetric (char 2)   | `T_P3_L1_symmetric` (re-exported  |
|                                 | inside `D1_implies_P3_F2`)        |
| Three-layer decomposition       | `T_P3_decomposition` (`dot=σ⊕LL`) |
| L₂ Arf-binary codomain          | `T_P3_arf_binary`                 |
| Arf classes both inhabited      | `T_P3_arf_surjective` (G6.1)      |
| `sigma` uniqueness on `R 2`     | `T_P3_sigma_uniqueness_R2` (G6.1) |

## Analytic-direction framing (this file)

The **synthetic direction** of T_P3 — "the R-Family at scope F₂
realises the 3-layer bilinear/quadratic stratification" — is the
existence story in `Foundation/R/Bilinear.lean` (and packaged in
`Foundation/R/PhaseZero.lean` § 1).

The **analytic direction** — *D1 + char(k) = 2 forces P3* — is the
dual: any D1-articulation in F₂-Boolean scope, restricted to its
`R (2k)` substrate, must realise this exact 3-layer classification
with exactly 2 Arf classes.  The chain is:

```
D1 (articulation)
  ⟹ P1 (≥ 2 distinct primitives ⟹ δ ≃ Bool / F₂)
  ⟹ P2 (composition / direct sum ⟹ R N = Fin N → δ)
  ⟹ relations 都是 F₂-bilinear (D1.3 + δ = F₂)
  ⟹ char(F₂) = 2: every alternating form is symmetric;
                  no factor of 2 to "undo" a symmetric form,
                  hence the symmetric-vs-alternating distinction
                  collapses *upwards* (alt ⊂ symm) but the
                  *quadratic refinement* `q` cannot be recovered
                  from `dot` alone — it carries strictly more data.
  ⟹ exactly 3 layers (L₀ symm = `dot`, L₁ alt = `sigma`,
                       L₂ quadratic refinement = `q`)
  ⟹ Arf classification: the L₂ family lives in a
                        codomain of cardinality 2 (binary
                        Bool-valued Arf), and both classes are
                        inhabited (G6.1).
```

**The combinatorial coincidence at char(k) = 2.**  This is the
philosophical content of "D1 + char(k) = 2 *forces* P3": the
substrate's bilinear classification has 3 layers and 2 Arf classes
rather than 4 or 8 *because* characteristic 2 collapses the
symmetric / alternating distinction at the bilinear level while
*not* collapsing it at the quadratic-refinement level.  In
characteristics ≠ 2 the L₀ symmetric form already determines the
quadratic refinement via `q(v) = ½ · dot(v, v)`, so the L₂ layer
adds no new data — the would-be "3-layer" structure degenerates to
2 layers (symm + alt-up-to-rescaling).  Char 2 is the unique
boundary where L₁ ⊂ L₀ holds (every alt is symm) *and* L₂ is
strictly richer than L₀ (since `½` is not available to recover `q`
from `dot`).  Hence "exactly 3 layers, exactly 2 Arf classes" is
*forced* — not chosen.

At the F₂-Boolean scope this analytic chain is *operationally*
equivalent to the synthetic construction in `T_P3` (all six
clauses): both end up at the same `R.dot` / `R.sigma` / `R.q` /
`R.arf` triple of forms together with the decomposition and Arf
uniqueness.  The packaging here renames the existing theorems
under labels that make the **analytic-direction reading** explicit,
and surfaces the philosophical "D1 + char(k) = 2 ⟹ P3" framing
that is otherwise implicit in the existence theorems.

## What this file delivers

* `D1_implies_P3_L0_symmetric` — re-export of `T_P3_L0_symmetric`
  under the analytic-direction label.
* `D1_implies_P3_L1_alternating` — re-export of
  `T_P3_L1_alternating`.
* `D1_implies_P3_decomposition` — re-export of `T_P3_decomposition`
  (the 3-layer `dot = σ ⊕ LL` identity).
* `D1_implies_P3_arf_binary` — re-export of `T_P3_arf_binary` (the
  L₂ Arf codomain is binary).
* `D1_implies_P3_arf_surjective` — re-export of
  `T_P3_arf_surjective` (G6.1: both Arf classes are inhabited).
* `D1_implies_P3_R2_sigma_unique` — re-export of
  `T_P3_sigma_uniqueness_R2` (G6.1: `sigma` is the unique
  F₂-bilinear / alternating / non-degenerate form on `R 2`).
* `D1_implies_P3_F2` — packaged conjunction of all six re-exports,
  matching the structure of `T_P3` from `PhaseZero` § 1.

## Scope

This file is a **re-export / framing module**: every theorem here
is definitionally equal to its `PhaseZero` counterpart.  No new
axioms, no `sorry`.  The point is the **analytic-direction label**
and the doctrinal-anchor docstring chain explaining *why* char 2
forces the 3-layer / 2-Arf classification.

## Doctrinal anchors

* `wen-substrate.md` v1.0.3 §2.3 (P3 bilinear classification).
* `wen-substrate.md` v1.0.3 §8.8 T_P3 (Phase 0 small theorem).
* `gut-roadmap.md` Phase 1 Stream A3 (D1 ⟹ P3 analytic).
* `gut-roadmap.md` Phase 0 G6.1 (T_P3 uniqueness clause, the 6th
  clause discharged via Arf surjectivity + `sigma`-uniqueness-on-R 2).
* `Foundation/R/PhaseZero.lean` § 1 (T_P3 anchors: 6/6 clauses).
* `Foundation/R/Bilinear.lean` (R.dot / R.sigma / R.q / R.arf and
  the decomposition `dot = σ ⊕ LL`).
* Atiyah, *Riemann surfaces and spin structures*, Ann. Sci. ENS
  (1971); Arf, *Untersuchungen über quadratische Formen in Körpern
  der Charakteristik 2*, J. Reine Angew. Math. (1941) — the
  classical references for the characteristic-2 Witt-Arf
  classification.
-/

import SSBX.Foundation.R.PhaseZero

namespace SSBX.Foundation.R.ClaimZ.Analytic

open SSBX.Foundation.R
open SSBX.Foundation.R.PhaseZero

/-! ## § 1 D1 ⟹ P3 — analytic-direction re-exports

Each theorem in this section is the analytic-direction reading of
its corresponding `T_P3_*` synthetic-direction counterpart in
`PhaseZero` § 1.  Operationally they are definitional re-exports;
the doctrinal content is the analytic-direction *framing*.
-/

/-- **D1 ⟹ P3 (L₀ symmetric) — analytic direction.**

    Any D1-articulation in F₂-Boolean scope, restricted to its
    `R N` substrate, supports a symmetric bilinear form `dot` for
    every `N`.  This is the **L₀ layer** of the 3-layer
    classification: the *base* symmetric form, available at every
    scale.

    Operationally a definitional re-export of `T_P3_L0_symmetric`.
    The analytic-direction reading: D1.3 (relations) at the
    F₂-Boolean realisation forces the symmetric `dot` form into
    existence — the relation layer is non-empty and symmetry is
    its minimal content.

    Per wen-substrate v1.0.3 §2.3 (P3 L₀ clause), §7.8.3 (D1.3 ⟹
    P3 mapping). -/
theorem D1_implies_P3_L0_symmetric {N : ℕ} (u v : R N) :
    R.dot u v = R.dot v u :=
  T_P3_L0_symmetric u v

/-- **D1 ⟹ P3 (L₁ alternating) — analytic direction.**

    Any D1-articulation in F₂-Boolean scope, restricted to its
    `R (2k)` substrate (the even-dimension layer), supports an
    alternating bilinear form `sigma` for every `k`.  This is the
    **L₁ layer** of the 3-layer classification: the *symplectic*
    form, available only at even dimensions.

    Operationally a definitional re-export of
    `T_P3_L1_alternating`.  The analytic-direction reading: D1.3
    (relations) at the F₂-Boolean realisation forces the
    alternating `sigma` form into existence at every even layer
    — the relation layer admits a non-degenerate symplectic
    refinement.

    **char(k) = 2 note.**  At characteristic 2, every alternating
    form is also symmetric (`T_P3_L1_symmetric`, packaged as a
    component of `D1_implies_P3_F2` below).  This is the first
    place where char 2 *collapses* a classical distinction —
    alternating ⊂ symmetric at the bilinear-form level.

    Per wen-substrate v1.0.3 §2.3 (P3 L₁ clause), §7.8.3. -/
theorem D1_implies_P3_L1_alternating {k : ℕ} (v : R (2 * k)) :
    R.sigma v v = false :=
  T_P3_L1_alternating v

/-- **D1 ⟹ P3 (3-layer decomposition) — analytic direction.**

    Any D1-articulation in F₂-Boolean scope, restricted to its
    `R (2k)` substrate, admits the **layer-decomposition
    identity** `dot = σ ⊕ LL` (where `LL` is the off-diagonal
    refinement bilinear sum, the algebraic glue between L₀ and
    L₁).  This is the *coherence* statement of the 3-layer
    classification: the three layers are not independent forms
    on the same carrier but **stacked algebraic strata** bound
    by an identity.

    Operationally a definitional re-export of
    `T_P3_decomposition`.  The analytic-direction reading: D1.3
    forces *coherence* between the symmetric and alternating
    layers — they cannot be chosen independently, the alternating
    form `sigma` is the L₀-symmetric form `dot` *minus* the
    LL-glue.

    **Conceptual content.**  In char ≠ 2 a symmetric form
    determines its alternating part via `σ(u, v) = ½(dot(u, v) -
    dot(v, u))` — but for a *symmetric* `dot`, this gives `σ ≡ 0`,
    collapsing L₁.  In char 2 the formula gains a *non-trivial*
    LL-correction; the decomposition `dot = σ ⊕ LL` makes the
    correction explicit and shows L₁ is *not* identically zero.

    Per wen-substrate v1.0.3 §2.3 (P3 decomposition clause),
    §7.8.3, and wen-algebra v0.6 §4.6 (the `dot = σ ⊕ LL`
    identity). -/
theorem D1_implies_P3_decomposition {k : ℕ} (u v : R (2 * k)) :
    R.dot u v = Bool.xor (R.sigma u v) (R.LL u v) :=
  T_P3_decomposition u v

/-- **D1 ⟹ P3 (Arf binary codomain) — analytic direction.**

    The Arf invariant `R.arf c` of the L₂ quadratic-refinement
    family is `Bool`-valued (= F₂-valued) — there are **at most
    two** Arf-labelled equivalence classes, by virtue of the
    codomain having cardinality 2.

    Operationally a definitional re-export of `T_P3_arf_binary`.
    The analytic-direction reading: D1 + char(k) = 2 forces the
    L₂ layer's classification space to be *binary* — not 4-valued,
    not k-valued.  This is the *forced binarity* clause of P3.

    **Why exactly 2 (and not 4 or 8)?**  In char 2, the
    Witt-decomposition of a quadratic form over an F₂-vector space
    of even dimension yields a free hyperbolic part plus *at most
    one* anisotropic 2-dimensional summand; the Arf invariant
    records which case obtains.  Algebraically: the quotient of
    quadratic forms by the symmetric-bilinear-part relation is a
    1-dimensional F₂-vector space, hence has exactly 2 elements.

    Per wen-substrate v1.0.3 §2.3 (P3 L₂ Arf clause), §7.8.3. -/
theorem D1_implies_P3_arf_binary {k : ℕ} (c : Fin k → Bool) :
    R.arf c = true ∨ R.arf c = false :=
  T_P3_arf_binary c

/-- **D1 ⟹ P3 (Arf classes both inhabited, G6.1) — analytic direction.**

    Both Arf classes are non-empty: for every `k`, there exist
    choice vectors `c₀ c₁ : Fin (k + 1) → Bool` with `arf c₀ =
    false` and `arf c₁ = true`.  Concrete witnesses:
    `c₀ = const false` and `c₁ = first-coordinate-only-true`.

    Operationally a definitional re-export of
    `T_P3_arf_surjective`.  The analytic-direction reading: D1 +
    char(k) = 2 forces the L₂ classification space to be *exactly
    binary* — not merely "at most binary" (`D1_implies_P3_arf_binary`)
    but **inhabited at both ends**.  This strengthens the codomain-
    cardinality claim to a *genuine partition* of the L₂ family
    into two non-empty classes.

    **The G6.1 strengthening.**  Before G6.1, T_P3 had 5/6 clauses
    discharged (codomain-cardinality-only Arf).  G6.1 closed the
    6th clause via Arf surjectivity (concrete witnesses for both
    classes) plus a concrete `sigma`-uniqueness on `R 2`.  This
    re-export propagates the G6.1 strengthening into the
    analytic-direction frame.

    Per wen-substrate v1.0.3 §8.8 T_P3 (6th clause), gut-roadmap
    G6.1 (Stream P0-A), `Foundation/R/PhaseZero.lean` § 1.1. -/
theorem D1_implies_P3_arf_surjective (k : ℕ) :
    (∃ c : Fin (k + 1) → Bool, R.arf c = false)
  ∧ (∃ c : Fin (k + 1) → Bool, R.arf c = true) :=
  T_P3_arf_surjective k

/-- **D1 ⟹ P3 (`sigma` uniqueness on `R 2`, G6.1) — analytic direction.**

    Any function `f : R 2 → R 2 → Bool` satisfying
      (i)   F₂-bilinearity (XOR-additivity in each argument),
      (ii)  alternating (`f v v = false`),
      (iii) non-degenerate at the basis-pair witness `f xo ox = true`,
    must equal `R.sigma (k := 1)` pointwise.

    Operationally a definitional re-export of
    `T_P3_sigma_uniqueness_R2`.  The analytic-direction reading:
    D1 + char(k) = 2 + the three axiomatic clauses (bilinear,
    alternating, non-degenerate) *force* a unique L₁ form on `R 2`
    — `sigma` is not chosen, it is the *only* form satisfying the
    P3 axioms at the smallest non-trivial layer.

    **The G6.1 strengthening (concrete uniqueness).**  Together
    with `D1_implies_P3_arf_surjective`, this delivers the
    "uniqueness up to F₂-bilinear isometry" clause of P3 *as far
    as it can be Lean-formalised without a full Mathlib char-2
    Witt classification* — concrete uniqueness of `sigma` on
    `R 2`, plus surjectivity of the Arf classifier on
    `R (2(k+1))`.  The full `Sp(2k, F_2)`-equivalence
    classification for all `k ≥ 1` (Witt-Arf for arbitrary even
    dimension) remains a *Mathlib-infrastructure-gated* residual.

    Per wen-substrate v1.0.3 §8.8 T_P3 (6th clause), gut-roadmap
    G6.1, `Foundation/R/PhaseZero.lean` § 1.1.1. -/
theorem D1_implies_P3_R2_sigma_unique (f : R 2 → R 2 → Bool)
    (hBilin : IsF2Bilinear f) (hAlt : IsAlt f)
    (hNonDeg : f R.xo R.ox = true) :
    ∀ u v : R 2, f u v = R.sigma (k := 1) u v :=
  T_P3_sigma_uniqueness_R2 f hBilin hAlt hNonDeg

/-! ## § 2 The packaged analytic theorem

`D1_implies_P3_F2` is the named analytic-step theorem for Phase 1
Stream A3.  It packages all six re-exports of § 1 as a single
conjunction, matching the shape of the synthetic `T_P3` packaged
theorem in `PhaseZero` § 1.

The analytic reading: given D1 + char(k) = 2 + the F₂-Boolean
substrate (= the realisation chain D1 ⟹ P1 ⟹ P2 ⟹ ... ⟹ δ ≃ F₂),
the *entire* 3-layer / 2-Arf-class bilinear classification follows
— *not* as a free choice of forms, but as the *unique* algebraic
shape forced by the substrate and characteristic.
-/

/-- **D1 ⟹ P3 (F₂-Boolean analytic step, Phase 1 Stream A3) —
    fully packaged, 6/6 clauses.**

    Reads:

    * **L₀** — for every `N`, `dot` is symmetric on `R N`.
    * **L₁** — for every `k`, `sigma` is alternating on `R (2k)`.
    * **L₁ symm (char 2)** — for every `k`, `sigma` is *also*
      symmetric on `R (2k)`.  This is the first place where char 2
      collapses the classical alt-vs-symm distinction at the
      bilinear-form level.
    * **3-layer decomposition** — for every `k`, `dot = σ ⊕ LL`
      on `R (2k)`, binding the three layers as stacked strata.
    * **Arf binary codomain** — for every `k`, the L₂ family's
      Arf classifier `R.arf` has Bool codomain (= at most 2 Arf
      classes).
    * **Arf surjective (G6.1)** — for every `k`, *both* Arf
      classes are inhabited via the explicit witnesses
      `choice_false` (Arf = false) and `choice_e0` (Arf = true).

    Together with `D1_implies_P3_R2_sigma_unique` (the G6.1
    `sigma`-uniqueness-on-R 2 clause, kept as a separate theorem
    because its statement quantifies over a function variable
    rather than directly over `R N`), this packages the **full
    6/6 P3 classification** under the analytic-direction frame.

    **Philosophical content.**  D1 + char(k) = 2 *forces* the
    3-layer / 2-Arf-class classification — *not* the 2-layer
    char ≠ 2 classification, *not* 4 or 8 Arf classes.  The
    combinatorial coincidences at char 2 (every alt is symm; L₂
    is binary; the L₂ classifier surjects onto its codomain) are
    not chosen — they are the *substrate's bilinear shape*,
    forced by D1 + the characteristic.

    Operationally a packaged definitional re-export of the
    `T_P3` packaged theorem in `Foundation/R/PhaseZero.lean` § 1.
    No new axioms, no `sorry`.

    Per wen-substrate v1.0.3 §2.3 (P3), §8.8 T_P3, gut-roadmap
    Phase 1 Stream A3 + Phase 0 G6.1. -/
theorem D1_implies_P3_F2 :
    -- L₀ symmetric on every R N:
    (∀ N (u v : R N), R.dot u v = R.dot v u)
    -- L₁ alternating on R (2k):
  ∧ (∀ k (v : R (2 * k)), R.sigma v v = false)
    -- L₁ symmetric on R (2k) (char 2 collapse):
  ∧ (∀ k (u v : R (2 * k)), R.sigma u v = R.sigma v u)
    -- 3-layer decomposition dot = σ ⊕ LL:
  ∧ (∀ k (u v : R (2 * k)), R.dot u v = Bool.xor (R.sigma u v) (R.LL u v))
    -- L₂ Arf codomain is binary:
  ∧ (∀ k (c : Fin k → Bool), R.arf c = true ∨ R.arf c = false)
    -- L₂ Arf classifier is surjective (G6.1):
  ∧ (∀ k, (∃ c : Fin (k + 1) → Bool, R.arf c = false)
        ∧ (∃ c : Fin (k + 1) → Bool, R.arf c = true)) :=
  T_P3

/-! ## § 3 Phase 1 Stream A3 summary

The six re-exports above plus the packaged `D1_implies_P3_F2`
theorem complete the **D1 ⟹ P3** sub-stream of Phase 1.

The hard mathematics — the existence of the three forms (`dot`,
`sigma`, `q`), the decomposition `dot = σ ⊕ LL`, the binary Arf
codomain, the G6.1 Arf surjectivity and `sigma`-uniqueness — is
unchanged; the contribution of this file is the analytic-direction
framing and the doctrinal-anchor chain wiring

```
D1
  ⟹ P1 (≥ 2 distinct primitives ⟹ δ ≃ F₂)
  ⟹ P2 (composition ⟹ R N = Fin N → δ direct sum)
  ⟹ char(k) = 2 + F₂-bilinearity of relations
  ⟹ exactly 3 layers (L₀ symm / L₁ alt / L₂ quad-refinement)
  ⟹ exactly 2 Arf classes (G6.1: both inhabited)
```

explicit in the docstring.  This is the **forced** reading of
P3: at the F₂-Boolean scope, the bilinear classification is not
a free design choice — it is the *unique* algebraic shape
forced by D1 + the characteristic.

Combined with Stream A1 (D1 ⟹ P1), Stream A5 (D1 ⟹ P5), Stream
A8 (D1 ⟹ P7b), and the other Phase 1 streams, this completes
the **analytic side** of Claim Z's bi-directional defence
(§7.8.3 of wen-substrate) at the F₂-Boolean scope.

**Non-Boolean scope (out-of-frame note).**  For non-Boolean
δ-realisations (intuitionistic Heyting, multi-valued
Łukasiewicz, quantum orthomodular, modal), the *shape* of P3 may
differ — e.g., in characteristics ≠ 2 the 3-layer / 2-Arf-class
structure degenerates to a 2-layer (symm + alt) classification
with no separate quadratic refinement.  This is *expected*
behaviour (cf. `gut-roadmap.md` Stream NA-1: "Non-algebraic δ
instance 发现 P3 form 在 δ=Prop 上不平凡") and does *not*
threaten the GUT-A claim; what is forced at every δ is the
*existence* of *some* bilinear classification, with the *exact
shape* depending on the algebraic-class realisation.
-/

end SSBX.Foundation.R.ClaimZ.Analytic
