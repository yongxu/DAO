# Phase 1-4 Scaffolding Handoff (Checkpoint 2026-05-18)

**This document is the companion to**
`docs-next/10_formal_形式/enriched-universal-sayability-plan.md` (the plan).

**Read order**:

1. **Plan §0-3** — understand goal and architecture
2. **This doc §1** — see what was actually built (vs planned)
3. **This doc §2** — locate every placeholder
4. **This doc §3** — pick up where work left off
5. **Plan Appendix C** — cold-start resumption protocol (still valid)

## §1 What was built (PR #70, 2026-05-18)

### Files created

```
formal/SSBX/Foundation/Enriched/
├── Cotensor.lean         ~190 LOC  (Phase 1.1)
├── Weighted.lean         ~150 LOC  (Phase 1.2)
├── Monad.lean            ~140 LOC  (Phase 1.3)
├── Finitary.lean          ~95 LOC  (Phase 1.4)
└── Power.lean            ~135 LOC  (Phase 1.5)

formal/SSBX/Foundation/Doctrine/
├── EnrichedLawvereTheory.lean  [modified: bridge doc, sorry kept]
├── Instance/HilbertEnriched.lean  ~140 LOC  (Phase 3)
└── T_GUT_Enriched.lean         ~150 LOC  (Phase 4)
```

Total: 7 new files, ~1000 LOC scaffolding, all under namespace
`CategoryTheory.Enriched` (for Phase 1) and `SSBX.Foundation.Doctrine.*`
(for Phases 3-4).

### Build state

```
lake build SSBX  →  4191 jobs ✓
```

(Baseline before this work was 4184 jobs. +7 files → +7 jobs.)

### Axiom state

```
#print axioms CategoryTheory.Enriched.Power.theory_monad_equiv
  → does not depend on any axioms

#print axioms SSBX.Foundation.Doctrine.enriched_universal_sayability_statement
  → does not depend on any axioms
```

All new phase declarations are `True := trivial`, so they vacuously
depend on no axioms. **The existing 0-axiom 0-sorry framework is
completely unchanged.**

### Sorry state

| File | Sorry count | Status |
|---|---|---|
| `EnrichedLawvereTheory.lean` | 1 (freeVFunctor) | **kept honest** per `[[no-axiom-for-zero-sorry]]` |
| All 7 new files | 0 | placeholders are `True := trivial` |

The 1 sorry is *pre-existing* (not introduced by this work). It's
documented in the file as awaiting Phase 1.5 elaboration; closing it
now would route through Phase 1.5's `True` placeholder, which is the
exact "game the metric" failure mode the user has flagged.

## §2 Placeholder inventory — what each `True` represents

This is the **debt ledger**. Each entry is a placeholder that needs to be
replaced with real mathematical content during phase elaboration.

### Cotensor.lean (Phase 1.1)

| Location | Placeholder | Real content needed |
|---|---|---|
| line 177 | `hasCotensor_Type_statement_form` returns `True` | The actual `HasCotensor` instance for V = Type (cotensor = function space `X → Y`) |

### Weighted.lean (Phase 1.2)

| Location | Placeholder | Real content needed |
|---|---|---|
| `HasWeightedLimit.universal` | `True := trivial` | The actual universal property: for any cone over D with V-weight W, a unique factor through `limit` |
| `cotensor_is_weighted_limit_over_terminal_statement` | `True` | Theorem: when J = terminal V-category, weighted V-limit = V-cotensor |
| `conical_limit_is_constant_weighted_statement` | `True` | Theorem: when W = constant 𝟙_V, weighted V-limit = conical V-limit |

### Monad.lean (Phase 1.3)

| Location | Placeholder | Real content needed |
|---|---|---|
| `EnrichedNatTrans.naturality` | `True := trivial` | The V-naturality square: `F.map ≫ eHomWhiskerLeft (app Y) = eHomWhiskerRight (app X) ≫ G.map` |
| `EnrichedMonadStruct.assoc` | `True := trivial` | Monad associativity: `T(μ_X) ≫ μ_X = μ_(TX) ≫ μ_X` |
| `EnrichedMonadStruct.left_unit` | `True := trivial` | Left unit: `η_(TX) ≫ μ_X = 𝟙` |
| `EnrichedMonadStruct.right_unit` | `True := trivial` | Right unit: `T(η_X) ≫ μ_X = 𝟙` |
| `enrichedMonad_Type_specialises_to_Monad_statement` | `True` | Theorem: V = Type recovers Mathlib's ordinary `Monad` |

### Finitary.lean (Phase 1.4)

| Location | Placeholder | Real content needed |
|---|---|---|
| `PreservesFilteredConicalColimits := True` | full placeholder | Real preservation predicate over `HasConicalColimit` of filtered shapes |
| `finitary_enriched_monad_Type_specialises_statement` | `True` | Theorem: V = Type specialisation recovers ordinary finitary monad |

### Power.lean (Phase 1.5) — **the deep one**

| Location | Placeholder | Real content needed |
|---|---|---|
| `theory_induces_monad_statement` | `True` | Power 1999 §3: V-enriched Lawvere theory → finitary V-monad (forward direction); ~10 pages of math |
| `monad_induces_theory_statement` | `True` | Power 1999 §4: finitary V-monad → V-enriched Lawvere theory (backward direction); ~10 pages of math |
| `theory_monad_equiv` | `True := by trivial` | **THE THEOREM**: the 1-categorical equivalence (forward + backward + mutual-inverse). ~30 pages total in Power 1999 §§3-4. Closing this is the highest-leverage elaboration. |
| `power_bridge_for_enriched_lawvere_theory` | `True` | Wrapper for Phase 2 consumption (trivial once theory_monad_equiv is real) |

### EnrichedLawvereTheory.lean (Phase 2)

| Location | Placeholder | Real content needed |
|---|---|---|
| line ~885 `freeVFunctor` | **`sorry`** (kept honest) | Real V-functor `C ⥤ EnrichedModel V T C` constructed via Phase 1.5's Power 4.5 + V-cocompleteness |
| `freeForgetfulAdjunction` | `True := by trivial` | Real adjunction `freeVFunctor ⊣ forgetfulVFunctor` (Power 1999 §2 Thm 2.4) |
| `enriched_lawvere_iff_finitary_v_monad` (existing) | `True := by trivial` | The same theorem as Power.theory_monad_equiv, but in this file's API |

### HilbertEnriched.lean (Phase 3)

| Location | Placeholder | Real content needed |
|---|---|---|
| `FinHilbPlaceholder := Unit` | Unit placeholder | Real `FinHilb` as bundled category (Mathlib upstream work; ~500 LOC of infrastructure) |
| `TGUTRealisation_Hilb_intent_statement` | `True` | Actual `TGUTRealisationCore FinHilb ℂ` instance |
| `quantum_forgetful_to_hilbert_statement` | `True` | Forgetful functor PauliBase-Quantum → FinHilb |

### T_GUT_Enriched.lean (Phase 4)

| Location | Placeholder | Real content needed |
|---|---|---|
| `enriched_universal_sayability_statement` | `True := trivial` | **THE V0.6 THEOREM**: real `∀ V [SMCC V] [...] ∀ C δ M M', Nonempty (EnrichedRealIso V M M')` quantifier + proof via Power 4.5 |
| `enriched_specialises_to_categorical_statement` | `True` | Theorem: at V = Type recovers existing `universal_sayability` |
| `enriched_universal_sayability_at_Hilbert_statement` | `True` | Theorem: instantiation at V = FinHilb is non-vacuous |
| `v0_6_completion_criteria_recorded_statement` | `True` | meta-marker for §10 acceptance criteria |

## §3 Pick-up protocol (cold start)

### §3.1 Verify nothing regressed

```bash
# From repo root:

# 1. Full SSBX build
lake build SSBX
# Expected: 4191 jobs (or more if other PRs landed), build succeeds

# 2. Existing 0-axiom check (must not regress)
cat > /tmp/verify_baseline.lean << 'EOF'
import SSBX.Foundation.Doctrine.T_GUT
import SSBX.Foundation.Doctrine.Instance.Topological
import SSBX.Foundation.Doctrine.Instance.Heyting
import SSBX.Foundation.Doctrine.Instance.Algebraic
import SSBX.Foundation.Doctrine.Instance.Quantum

#print axioms SSBX.Foundation.Doctrine.TGUTRealisation.universal_sayability
#print axioms SSBX.Foundation.Doctrine.Instance.P3_topological
#print axioms SSBX.Foundation.Doctrine.Instance.P3_heyting
#print axioms SSBX.Foundation.Doctrine.Instance.quantum_universal_sayability_witness
#print axioms SSBX.Foundation.Doctrine.Instance.GUT_A_recovery_at_4
EOF
lake env lean /tmp/verify_baseline.lean
# Expected: each → [propext, Classical.choice, Quot.sound]

# 3. Phase 1-4 scaffold check (must remain True := trivial)
cat > /tmp/verify_scaffold.lean << 'EOF'
import SSBX.Foundation.Enriched.Power
import SSBX.Foundation.Doctrine.T_GUT_Enriched

#print axioms CategoryTheory.Enriched.Power.theory_monad_equiv
#print axioms SSBX.Foundation.Doctrine.enriched_universal_sayability_statement
EOF
lake env lean /tmp/verify_scaffold.lean
# Expected (if still scaffolding): "does not depend on any axioms"
# (After elaboration: should show [propext, Classical.choice, Quot.sound])
```

### §3.2 Choose where to pick up

The highest-leverage work is **Phase 1.5** (Power 1999 Theorem 4.5). Closing
that unblocks Phase 2 (close `freeVFunctor` sorry) and Phase 4 (real
`enriched_universal_sayability`). Suggested phase priority:

1. **Phase 1.5 elaboration** — Power 1999 §§3-4 constructive formalization
   - Real `theory_monad_equiv : EnrichedLawvereTheory V ≃ FinitaryEnrichedMonad V`
   - Likely 1500-3000 LOC of dense category theory
   - Requires real implementations of Phases 1.1-1.4 placeholders too
   - **Estimate: 2-3 months focused work**

2. **Phase 2 close** — once Phase 1.5 has real Power 4.5
   - Replace `freeVFunctor` sorry with proof routing through `theory_monad_equiv`
   - Strengthen `freeForgetfulAdjunction` from `True` to real adjunction
   - **Estimate: 1-2 weeks after Phase 1.5**

3. **Phase 3 elaboration** — FinHilb SMCC
   - Mathlib upstream: bundled `FinHilb` category, Hilbert tensor as
     monoidal structure
   - SSBX-local: `TGUTRealisationCore FinHilb ℂ` instance
   - **Estimate: 1-2 months**

4. **Phase 4 close** — real `enriched_universal_sayability`
   - Replace `True := trivial` with proper V-quantified theorem
   - Prove via Phase 1.5 Power 4.5
   - Instantiate at FinHilb (Phase 3)
   - Verify non-vacuous
   - **Estimate: 1 month after Phases 1.5 + 2 + 3**

### §3.3 If you're going to work on Phase 1.5

This is the deepest sub-task. Recommended reading order:

1. Power, J. 1999. *Enriched Lawvere theories*. TAC 6 no. 7. — read §§1-4 fully
2. Kelly 1982 §§3.7 (cotensors), §5 (V-monads), §6 (V-product-preserving V-functors)
3. Hyland-Power 2007 ENTCS 172. — modern survey
4. Mathlib's existing `Mathlib.CategoryTheory.Monad.*` — for the ordinary case patterns

Then the elaboration plan:

- Strengthen `EnrichedNatTrans.naturality` from `True` to real square
- Strengthen `EnrichedMonadStruct.assoc/left_unit/right_unit` from `True` to real axioms
- Define forward functor `theoryToMonad` (Power 1999 §3 construction)
- Define backward functor `monadToTheory` (Power 1999 §4 construction)
- Prove they are mutual inverses (this is the hard part)

Likely 8-15 PRs to upstream (each Mathlib PR conservatively 100-300 LOC). Multi-month engagement with Mathlib reviewers.

### §3.4 If you're going to work on Phase 4 (assuming Phase 1.5 is done)

Once Phase 1.5 lands real `theory_monad_equiv`:

1. Open `T_GUT_Enriched.lean`
2. Replace `enriched_universal_sayability_statement` body with the real proof:
   - Add proper `[Category V] [SMCC V] [HasCotensors V] ...` instances
   - State the theorem with real quantifier
   - Prove: apply `theory_monad_equiv`, then use free-forgetful adjunction
3. Update `#print axioms` should show `[propext, Classical.choice, Quot.sound]` (no more "does not depend on any axioms")
4. Add a Phase 4.1 follow-up file with the FinHilb instantiation:
   - Import HilbertEnriched.lean (assumed Phase 3 elaborated)
   - Specialise to V = FinHilb
   - Verify non-vacuous

### §3.5 Verification checklist (after any phase elaboration)

```bash
# 1. Build clean
lake build SSBX

# 2. Old 0-axiom theorems still 0-axiom
# (run verify_baseline.lean from §3.1)

# 3. New theorems show real axioms now (not "does not depend on any axioms")
# (run verify_scaffold.lean from §3.1)

# 4. No new sorry beyond freeVFunctor
grep -rn "sorry" formal/SSBX/Foundation/Enriched/ formal/SSBX/Foundation/Doctrine/T_GUT_Enriched.lean

# 5. No new axioms beyond Lean standard 3
grep -rn "^axiom " formal/SSBX/Foundation/
# Expected: 0 results (per [[no-axiom-for-zero-sorry]])
```

## §4 Cross-references

### In this codebase

- **Plan**: `docs-next/10_formal_形式/enriched-universal-sayability-plan.md` (PR #69)
- **E1 closure**: `docs-next/10_formal_形式/E1-rtower-theta-experiment.md` (PR #69) — why we're doing v0.6 (not RH-attack)
- **Phase 1-4 scaffolding code**: this PR (#70)
- **Existing universal_sayability**: `formal/SSBX/Foundation/Doctrine/T_GUT.lean:691`
- **Existing 4 substrates**: `formal/SSBX/Foundation/Doctrine/Instance/{Algebraic,Heyting,Quantum,Topological}.lean`

### Memory entries

- `[[e1-rtower-rh-closed]]` — RH is closed; this work is framework completion not RH attack
- `[[no-axiom-for-zero-sorry]]` — meta-rule: don't axiom out sorries; PR #51 incident
- `[[dont-drop-theorems]]` — meta-rule: don't weaken theorems
- `[[v4-shi-doctrine-out-2026-05-17]]` — V₄ retired; doesn't affect this work
- `[[squaring-tower]]` — R-tower structure; relevant for Phase 3 (Hilb realization)

### External

- Power 1999. *Enriched Lawvere theories*. TAC 6 no. 7. — primary mathematical reference
- Kelly 1982. *Basic Concepts of Enriched Category Theory*. — foundational V-category theory
- Hyland-Power 2007. ENTCS 172. — modern survey
- Mathlib zulip `#category-theory` — for upstream PR coordination

## §5 Honest disclaimers (for the agent picking this up)

1. **This is scaffolding, not the framework.** Plan §10's acceptance criteria are *all* still open. Each `True` is a debt entry.

2. **The math is hard.** Power 1999 §§3-4 is roughly 30 pages of dense V-enriched category theory. Formalizing it is a real multi-month research project, not a weekend hack.

3. **Mathlib coordination required.** The lower-level pieces (V-cotensor, weighted V-limits) realistically belong in Mathlib, not SSBX. Plan for upstream PR engagement.

4. **You will not "finish" Phase 1 in one session.** Set realistic milestones — e.g., "elaborate `EnrichedNatTrans.naturality` properly" might be one session's deliverable.

5. **Verify, don't trust.** After each elaboration, run §3.5 checklist. The PR #51 incident (provably-False axiom slipped past local typechecking) is a permanent reminder that build-success ≠ correctness.

6. **Stay honest about state.** If a session can't make a placeholder real, leave it as placeholder with updated doc. Don't game the metric by routing through other placeholders.

---

**End of handoff.**

**Last updated**: 2026-05-18 (immediately after PR #70 scaffolding land).

**Next checkpoint**: when Phase 1.5 elaboration produces real `theory_monad_equiv`. Update this doc's §2 inventory and §3 pick-up plan accordingly.
