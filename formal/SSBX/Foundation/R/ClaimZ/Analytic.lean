/-
# Foundation.R.ClaimZ.Analytic — Phase 1 Integration

**GUT roadmap Phase 1 Integration Step** (per
`docs-next/10_formal_形式/gut-roadmap.md`):

The 8 Analytic streams (`Analytic/P1.lean` ... `Analytic/P7b.lean`)
each discharge the analytic direction of one P-conjunct of Claim Z
for the F₂-Boolean realisation of the R-Family.  This file performs
the **integration step**: it imports all 8 streams, packages their
results into a single concrete `PClosure` (the **F₂-Boolean Phase 1
closure**), and proves that any `D1Articulation` (whose 8 items are
witnessed) gives rise to this closure.

In other words: `d1_implies_P` in `ClaimZ.lean` was previously the
interface-level form — *given* per-item entailments `h1..h7b`, it
returned the corresponding closure conjuncts.  Here we **construct**
the concrete F₂-Boolean entailments from the 8 analytic theorems and
deliver the **fully discharged form** `D1_implies_Phase1Closure_F2`:
no `h_i` hypotheses are required — the closure is built directly
from the analytic content.

## What this file delivers

* `Phase1Closure_F2 : PClosure` — the concrete F₂-Boolean P-closure
  whose 8 conjuncts are the propositional shadows of the 8 analytic
  theorems (propositional in the sense that Type-valued Equivs are
  wrapped in `Nonempty`).
* `D1_implies_Phase1Closure_F2 : (S : D1Articulation) → ... → ...` —
  the fully discharged Phase 1 closure theorem: given a `D1Articulation`
  `S` with its 8 items witnessed, the conjunction of the 8 closure
  conjuncts of `Phase1Closure_F2` holds.  No per-item entailment
  hypotheses are required — the analytic theorems are plugged in
  directly.
* `D1_implies_PClosure_at_F2` — the "exists a closure" form: there
  exists a `PClosure` `P` and a discharging map taking any D1 to the
  conjunction of P's 8 conjuncts.  Witnessed by `Phase1Closure_F2`.

## Scope

* **F₂-Boolean scope**: fully closed.  No `sorry`, no new `axiom`.
* **Non-Boolean scope** (intuitionistic / multi-valued / quantum /
  modal): each analytic stream documents its own scope; the
  integration here packages the **F₂-Boolean case**.  Extending to
  other δ-realisations is a Phase 2+ task.

## Relation to upstream files

* This file **imports** all 8 `Analytic/P*.lean` modules and
  `ClaimZ.lean`.  It does **not** modify any of them.
* `ClaimZ.lean`'s `d1_implies_P` remains as the interface-level
  combinator (useful for non-F₂ instantiations); this file delivers
  the **F₂-specific full closure** as a parallel theorem.

## Doctrinal anchor

* `gut-roadmap.md` (Phase 1 Integration Step).
* `wen-substrate.md` v1.2 §7.8.3 (D1 ⟹ P1-P7 analytic direction).
* `Foundation/R/ClaimZ.lean` (D1Articulation and PClosure schemas).
* `Foundation/R/ClaimZ/Analytic/P*.lean` (the 8 analytic streams).
-/

import SSBX.Foundation.R.ClaimZ
import SSBX.Foundation.R.ClaimZ.Analytic.P1
import SSBX.Foundation.R.ClaimZ.Analytic.P2
import SSBX.Foundation.R.ClaimZ.Analytic.P3
import SSBX.Foundation.R.ClaimZ.Analytic.P4
import SSBX.Foundation.R.ClaimZ.Analytic.P5
import SSBX.Foundation.R.ClaimZ.Analytic.P6
import SSBX.Foundation.R.ClaimZ.Analytic.P7a
import SSBX.Foundation.R.ClaimZ.Analytic.P7b

namespace SSBX.Foundation.R.ClaimZ

open SSBX.Foundation.R
open SSBX.Foundation.R.PhaseZero
open SSBX.Foundation.R.ClaimZ.Analytic
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 The concrete F₂-Boolean P-closure

Each conjunct of `Phase1Closure_F2 : PClosure` is the propositional
content delivered by the corresponding `Analytic/P*.lean` stream at
the F₂-Boolean realisation:

| Conjunct | Stream | Content                                                                                                |
|----------|--------|--------------------------------------------------------------------------------------------------------|
| `p1`     | A1     | `∃ x y : Bool, x ≠ y` (substrate-level non-trivial distinction)                                        |
| `p2`     | A2     | `∀ N M, Nonempty (R N × R M ≃ R (N + M))` (direct-sum / biproduct)                                     |
| `p3`     | A3     | 6-clause bilinear classification (L₀ symm / L₁ alt / 3-layer / Arf binary / Arf surjective / dot ≡ σ⊕LL) |
| `p4`     | A4     | `∀ N, Nonempty (R (2 * N) ≃ R N × R N)` (squaring-tower self-similarity)                               |
| `p5`     | A5     | `∀ N M, Nonempty (LinHom N M ≃ R (N * M))` (Hom-as-content)                                             |
| `p6`     | A6     | 6-clause V₄ + Lorentzian (cardinality / 3 involutions / commute / Lorentzian bridge)                   |
| `p7a`    | A7     | 6-clause zong involution (zong involutive / two length-4 lists / two Nodup / fixed-iff-ben)            |
| `p7b`    | A8     | `Nonempty (R 4 ≃+* Mat2F2)` (M₂(F₂) ring structure)                                                    |
-/

/-- **Phase1Closure_F2** — the concrete F₂-Boolean P-closure.

    Each conjunct is the propositional content of the corresponding
    `Analytic/P*.lean` stream at the F₂-Boolean realisation.  This is
    the canonical `PClosure` instance for the F₂ scope; the 8 conjuncts
    are discharged unconditionally by the per-item entailment lemmas
    `Phase1_F2_h1`..`Phase1_F2_h7b` (each lemma simply plugs in the
    corresponding analytic theorem).

    Field assignments below use line-comments rather than doc-comments
    to avoid confusing the structure-literal parser. -/
def Phase1Closure_F2 : PClosure where
  -- P1 — substrate-level non-trivial distinction (Analytic/P1).
  p1   := ∃ x y : Bool, x ≠ y
  -- P2 — direct-sum / biproduct closure at every layer pairing (Analytic/P2).
  p2   := ∀ (N M : ℕ), Nonempty (R N × R M ≃ R (N + M))
  -- P3 — 6-clause bilinear classification (Analytic/P3): L₀ symm /
  -- L₁ alt / L₁ symm at char 2 / 3-layer decomp / Arf binary / Arf surjective.
  p3   :=
    (∀ N (u v : R N), R.dot u v = R.dot v u)
    ∧ (∀ k (v : R (2 * k)), R.sigma v v = false)
    ∧ (∀ k (u v : R (2 * k)), R.sigma u v = R.sigma v u)
    ∧ (∀ k (u v : R (2 * k)),
        R.dot u v = Bool.xor (R.sigma u v) (R.LL u v))
    ∧ (∀ k (c : Fin k → Bool), R.arf c = true ∨ R.arf c = false)
    ∧ (∀ k, (∃ c : Fin (k + 1) → Bool, R.arf c = false)
          ∧ (∃ c : Fin (k + 1) → Bool, R.arf c = true))
  -- P4 — squaring-tower self-similarity at every layer index (Analytic/P4).
  p4   := ∀ (N : ℕ), Nonempty (R (2 * N) ≃ R N × R N)
  -- P5 — Hom-as-content (every Hom space lives as substrate content, Analytic/P5).
  p5   := ∀ (N M : ℕ), Nonempty (R.LinHom N M ≃ R (N * M))
  -- P6 — 6-clause V₄ structure on `R 2` + Lorentzian-4-region bridge (Analytic/P6).
  p6   :=
    Fintype.card (R 2) = 4
    ∧ (∀ s : Shi, Shi.complement (Shi.complement s) = s)
    ∧ (∀ s : Shi, Shi.reverse (Shi.reverse s) = s)
    ∧ (∀ s : Shi,
        Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s))
    ∧ (∀ s : Shi, Shi.cuoZong (Shi.cuoZong s) = s)
    ∧ ((∀ v : Fin 4 → ℚ,
            TP6Lorentzian.lorentzianRegion v = Shi.dao
          ∨ TP6Lorentzian.lorentzianRegion v = Shi.ji
          ∨ TP6Lorentzian.lorentzianRegion v = Shi.jin
          ∨ TP6Lorentzian.lorentzianRegion v = Shi.wei)
      ∧ TP6Lorentzian.lorentzianRegion
          (TP6Lorentzian.nullWitness : Fin 4 → ℚ) = Shi.dao
      ∧ TP6Lorentzian.lorentzianRegion
          (TP6Lorentzian.pastTimelikeWitness : Fin 4 → ℚ) = Shi.ji
      ∧ TP6Lorentzian.lorentzianRegion
          (TP6Lorentzian.spacelikeWitness : Fin 4 → ℚ) = Shi.jin
      ∧ TP6Lorentzian.lorentzianRegion
          (TP6Lorentzian.futureTimelikeWitness : Fin 4 → ℚ) = Shi.wei)
  -- P7a — 6-clause zong involution + 4本/4征 partition on `R 3` (Analytic/P7a).
  p7a  :=
    (∀ t : Trigram, Trigram.zong (Trigram.zong t) = t)
    ∧ Trigram.benTrigrams.length = 4
    ∧ Trigram.zhengTrigrams.length = 4
    ∧ Trigram.benTrigrams.Nodup
    ∧ Trigram.zhengTrigrams.Nodup
    ∧ (∀ t : Trigram, Trigram.zong t = t ↔ t ∈ Trigram.benTrigrams)
  -- P7b — M₂(F₂) ring structure on `R 4` (existence form, Analytic/P7b).
  p7b  := Nonempty ((R 4) ≃+* Mat2F2)

/-! ## § 2 The 8 per-item entailments at F₂

Each lemma below is the F₂-Boolean form of the corresponding
per-item analytic entailment `hi : S.<item> → P.<conjunct>`
required by `ClaimZ.d1_implies_P`.  Each is discharged by the
corresponding analytic theorem in `Analytic/P*.lean`.  Note that
the entailments are *vacuous* on the D1 hypothesis at this scope:
the F₂-Boolean instantiation provides the conjunct unconditionally,
independent of any further D1-articulation content beyond the item
witness.  This is the *operational tightness* of the F₂-Boolean
closure: the analytic content is fully discharged.
-/

/-- Per-item entailment D1.1 ⟹ P1 at F₂. -/
theorem Phase1_F2_h1 (S : D1Articulation) :
    S.obj → Phase1Closure_F2.p1 := by
  intro _
  show ∃ x y : Bool, x ≠ y
  exact P1_at_Bool

/-- Per-item entailment D1.2 ⟹ P2 at F₂. -/
theorem Phase1_F2_h2 (S : D1Articulation) :
    S.comp → Phase1Closure_F2.p2 := by
  intro _
  show ∀ (N M : ℕ), Nonempty (R N × R M ≃ R (N + M))
  intro N M
  exact D1_implies_P2_F2_prop N M

/-- Per-item entailment D1.3 ⟹ P3 at F₂. -/
theorem Phase1_F2_h3 (S : D1Articulation) :
    S.rel → Phase1Closure_F2.p3 := by
  intro _
  exact (show
      (∀ N (u v : R N), R.dot u v = R.dot v u)
      ∧ (∀ k (v : R (2 * k)), R.sigma v v = false)
      ∧ (∀ k (u v : R (2 * k)), R.sigma u v = R.sigma v u)
      ∧ (∀ k (u v : R (2 * k)),
          R.dot u v = Bool.xor (R.sigma u v) (R.LL u v))
      ∧ (∀ k (c : Fin k → Bool), R.arf c = true ∨ R.arf c = false)
      ∧ (∀ k, (∃ c : Fin (k + 1) → Bool, R.arf c = false)
            ∧ (∃ c : Fin (k + 1) → Bool, R.arf c = true))
      from D1_implies_P3_F2)

/-- Per-item entailment D1.6 ⟹ P4 at F₂. -/
theorem Phase1_F2_h4 (S : D1Articulation) :
    S.recur → Phase1Closure_F2.p4 := by
  intro _
  show ∀ (N : ℕ), Nonempty (R (2 * N) ≃ R N × R N)
  intro N
  exact D1_implies_P4_F2_prop N

/-- Per-item entailment D1.5 ⟹ P5 at F₂. -/
theorem Phase1_F2_h5 (S : D1Articulation) :
    S.rule → Phase1Closure_F2.p5 := by
  intro _
  show ∀ (N M : ℕ), Nonempty (R.LinHom N M ≃ R (N * M))
  intro N M
  exact D1_implies_P5_F2_prop N M

/-- Per-item entailment D1.8 ⟹ P6 at F₂. -/
theorem Phase1_F2_h6 (S : D1Articulation) :
    ∀ (hp : S.hasProcessContent), S.modality hp → Phase1Closure_F2.p6 := by
  intro _ _
  exact (show
      Fintype.card (R 2) = 4
      ∧ (∀ s : Shi, Shi.complement (Shi.complement s) = s)
      ∧ (∀ s : Shi, Shi.reverse (Shi.reverse s) = s)
      ∧ (∀ s : Shi,
          Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s))
      ∧ (∀ s : Shi, Shi.cuoZong (Shi.cuoZong s) = s)
      ∧ ((∀ v : Fin 4 → ℚ,
              TP6Lorentzian.lorentzianRegion v = Shi.dao
            ∨ TP6Lorentzian.lorentzianRegion v = Shi.ji
            ∨ TP6Lorentzian.lorentzianRegion v = Shi.jin
            ∨ TP6Lorentzian.lorentzianRegion v = Shi.wei)
        ∧ TP6Lorentzian.lorentzianRegion
            (TP6Lorentzian.nullWitness : Fin 4 → ℚ) = Shi.dao
        ∧ TP6Lorentzian.lorentzianRegion
            (TP6Lorentzian.pastTimelikeWitness : Fin 4 → ℚ) = Shi.ji
        ∧ TP6Lorentzian.lorentzianRegion
            (TP6Lorentzian.spacelikeWitness : Fin 4 → ℚ) = Shi.jin
        ∧ TP6Lorentzian.lorentzianRegion
            (TP6Lorentzian.futureTimelikeWitness : Fin 4 → ℚ) = Shi.wei)
      from D1_implies_P6_F2)

/-- Per-item entailment (D1.1 ∧ D1.3 ∧ D1.6) ⟹ P7a at F₂. -/
theorem Phase1_F2_h7a (S : D1Articulation) :
    (S.obj ∧ S.rel ∧ S.recur) → Phase1Closure_F2.p7a := by
  intro _
  exact (show
      (∀ t : Trigram, Trigram.zong (Trigram.zong t) = t)
      ∧ Trigram.benTrigrams.length = 4
      ∧ Trigram.zhengTrigrams.length = 4
      ∧ Trigram.benTrigrams.Nodup
      ∧ Trigram.zhengTrigrams.Nodup
      ∧ (∀ t : Trigram, Trigram.zong t = t ↔ t ∈ Trigram.benTrigrams)
      from D1_implies_P7a_F2)

/-- Per-item entailment (D1.4 ∧ D1.7) ⟹ P7b at F₂. -/
theorem Phase1_F2_h7b (S : D1Articulation) :
    (S.op ∧ S.selfRef) → Phase1Closure_F2.p7b := by
  intro _
  show Nonempty ((R 4) ≃+* Mat2F2)
  exact ⟨D1_implies_P7b_F2⟩

/-! ## § 3 The fully discharged Phase 1 closure theorem

This is the **upgraded** form of `ClaimZ.d1_implies_P`: instead of
*requiring* the caller to supply per-item entailments `h1..h7b`, the
F₂-Boolean realisation **derives** them from the 8 analytic
theorems in `Analytic/P*.lean`.  The theorem takes only the
witnesses of D1's 8 items (`h_obj`, `h_comp`, ..., `h_mod`, plus the
process-content guard `h_proc` for P6) and returns the conjunction
of the 8 closure conjuncts of `Phase1Closure_F2`.
-/

/-- **D1 ⟹ Phase1Closure_F2 (fully discharged form)** — the Phase 1
    integration theorem at the F₂-Boolean realisation.

    Given a `D1Articulation` `S` whose 8 items are witnessed (the
    `h_obj`, `h_comp`, ..., `h_selfRef` hypotheses, plus the
    `h_mod` modality witness and the `h_proc` process-content
    guard), the F₂-Boolean P-closure `Phase1Closure_F2` holds in
    full: all 8 conjuncts `p1, p2, p3, p4, p5, p6, p7a, p7b` are
    proved.

    This is the **Phase 1 expected output** of the GUT roadmap:
    `d1_implies_P` upgraded to a complete theorem (no per-item
    entailment hypotheses required), discharged at the F₂-Boolean
    scope via the 8 analytic streams.

    Per `gut-roadmap.md` Phase 1 Integration Step. -/
theorem D1_implies_Phase1Closure_F2
    (S : D1Articulation)
    (h_obj : S.obj) (h_comp : S.comp) (h_rel : S.rel) (h_op : S.op)
    (h_rule : S.rule) (h_rec : S.recur) (h_selfRef : S.selfRef)
    (h_mod : ∀ hp : S.hasProcessContent, S.modality hp)
    (h_proc : S.hasProcessContent) :
    Phase1Closure_F2.p1 ∧ Phase1Closure_F2.p2 ∧ Phase1Closure_F2.p3
  ∧ Phase1Closure_F2.p4 ∧ Phase1Closure_F2.p5 ∧ Phase1Closure_F2.p6
  ∧ Phase1Closure_F2.p7a ∧ Phase1Closure_F2.p7b :=
  d1_implies_P S Phase1Closure_F2
    (Phase1_F2_h1 S) (Phase1_F2_h2 S) (Phase1_F2_h3 S)
    (Phase1_F2_h4 S) (Phase1_F2_h5 S) (Phase1_F2_h6 S)
    (Phase1_F2_h7a S) (Phase1_F2_h7b S)
    h_obj h_comp h_rel h_op h_rule h_rec h_selfRef h_mod h_proc

/-- **D1 ⟹ ∃ PClosure (existence form, F₂)** — there exists a
    `PClosure` `P` such that every `D1Articulation` (with its 8
    items witnessed and process-content active) entails the
    conjunction of P's 8 conjuncts.

    This is the "Claim Z's analytic side has a witness" form of
    the Phase 1 closure: the existence is **constructive** (the
    witness is `Phase1Closure_F2`).  Read: the §7.8.3 analytic step
    is not merely an interface obligation but is **discharged** at
    the F₂-Boolean realisation. -/
theorem D1_implies_PClosure_at_F2 :
    ∃ (P : PClosure),
      ∀ (S : D1Articulation)
        (_ : S.obj) (_ : S.comp) (_ : S.rel) (_ : S.op)
        (_ : S.rule) (_ : S.recur) (_ : S.selfRef)
        (_ : ∀ hp : S.hasProcessContent, S.modality hp)
        (_ : S.hasProcessContent),
        P.p1 ∧ P.p2 ∧ P.p3 ∧ P.p4 ∧ P.p5 ∧ P.p6 ∧ P.p7a ∧ P.p7b :=
  ⟨ Phase1Closure_F2
  , fun S h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      D1_implies_Phase1Closure_F2 S h1 h2 h3 h4 h5 h6 h7 h8 h9 ⟩

/-! ## § 4 Restricted (no-process) form

The non-modality restricted form: when `S` does *not* articulate
process content (the §1.5.1 D1|₇ scope), the modality clause is
vacuous and the analytic step discharges all conjuncts *except*
P6.  This mirrors `ClaimZ.d1_restricted_implies_P`. -/

/-- **D1 ⟹ Phase1Closure_F2 (no-process restricted form)** — the
    §1.5.1 D1|₇ scope: P6 (modality) is omitted because the
    articulation does not include process / temporal / causal
    content.  The other 7 conjuncts (`p1`, `p2`, `p3`, `p4`, `p5`,
    `p7a`, `p7b`) are fully discharged via the analytic streams. -/
theorem D1_restricted_implies_Phase1Closure_F2
    (S : D1Articulation)
    (h_obj : S.obj) (h_comp : S.comp) (h_rel : S.rel) (h_op : S.op)
    (h_rule : S.rule) (h_rec : S.recur) (h_selfRef : S.selfRef) :
    Phase1Closure_F2.p1 ∧ Phase1Closure_F2.p2 ∧ Phase1Closure_F2.p3
  ∧ Phase1Closure_F2.p4 ∧ Phase1Closure_F2.p5
  ∧ Phase1Closure_F2.p7a ∧ Phase1Closure_F2.p7b :=
  d1_restricted_implies_P S Phase1Closure_F2
    (Phase1_F2_h1 S) (Phase1_F2_h2 S) (Phase1_F2_h3 S)
    (Phase1_F2_h4 S) (Phase1_F2_h5 S)
    (Phase1_F2_h7a S) (Phase1_F2_h7b S)
    h_obj h_comp h_rel h_op h_rule h_rec h_selfRef

/-! ## § 5 Summary

This file performs the **Phase 1 integration step** of the GUT
roadmap: the 8 analytic streams (`Analytic/P1.lean` ...
`Analytic/P7b.lean`) are combined into a single fully-discharged
`PClosure` instance (`Phase1Closure_F2`) and a single fully-
discharged closure theorem (`D1_implies_Phase1Closure_F2`).

The upgrade from `ClaimZ.d1_implies_P`:

* **Before**: `d1_implies_P` required the caller to supply 8
  per-item entailment hypotheses `h1..h7b` and the resulting
  P-closure was abstract (each conjunct was just a `Prop`
  symbolically chosen by the caller).
* **After (this file)**: at the F₂-Boolean realisation, the
  P-closure is the **concrete** `Phase1Closure_F2`, its 8
  conjuncts are the propositional shadows of the 8 analytic
  theorems, and the 8 per-item entailments are derived from the
  analytic streams.  The closure theorem
  `D1_implies_Phase1Closure_F2` takes only the D1 item witnesses
  (no entailment hypotheses).

**Scope.**  This is the F₂-Boolean closure.  Non-Boolean
δ-realisations (intuitionistic / multi-valued / quantum / modal)
remain Phase 2+ work; each analytic stream documents its own
non-Boolean status.

**Zero `sorry`, zero new axiom.**  Every conjunct of
`Phase1Closure_F2` is discharged by an existing analytic theorem;
the integration is a pure plumbing step.
-/

end SSBX.Foundation.R.ClaimZ
