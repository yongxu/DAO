# Plan: V-Enriched Universal Sayability — Fulfilling v0.2 Path C Original Ambition

**Status**: 2026-05-18 — Plan drafted, not started. Decision to pursue Option (iii) from `E1-rtower-theta-experiment.md` §6 + scope-correction analysis.

**Target Doctrine Version**: GUT-C v0.6 (enriched supersedes v0.5 direct categorical).

**Author**: Claude (Opus 4.7), at user's direction 2026-05-18.

**Scope**: Multi-month, multi-PR delivery. Estimated 6-12 months of focused work, possibly longer if Mathlib upstream cooperation is slow.

---

## 0. Cold-Start Context (Read This First if You're New)

This document is a **detailed roadmap to fulfill the original Path C v0.2 ambition** of GUT-C, which silently shrank to a 4-substrate discrete categorical version during execution (Phase γ.2, ~early 2026).

**The scope gap** (precise statement):

- **v0.2 promised**: `universal_sayability` quantifies over all V-enriched SMCC, including continuous (Hilb, Top, Met, Ban) substrates. Implemented via Power 1999 enriched-Lawvere-theory ≃ finitary V-monad equivalence (`gut-c-doctrine.md` v0.2 §§3.2, 11.1, "PR-3").
- **v0.5 delivered**: `universal_sayability` quantifies over 4 fixed discrete substrates (Algebraic over F_q / Heyting / Quantum Klein-four / Topological Sierpinski). Implemented via direct concrete iso construction (`componentIso` in `T_GUT.lean:691`).

The fossil of the original plan is the **929-LOC dead-code module** `formal/SSBX/Foundation/Doctrine/EnrichedLawvereTheory.lean`, which holds the V-enriched scaffolding with two sorries (`freeVFunctor`, `enriched_lawvere_iff_finitary_v_monad`) awaiting Mathlib upstream support.

**Why this plan exists**: user asked 2026-05-18 to fulfill the original ambition rather than silently accept the trimmed scope. The work is large but mechanically tractable — no new mathematics required, only formal-mathematics engineering.

**How to read this plan**:

- §1-3: Background and goal — read to understand *what* and *why*.
- §4-7: Phase-by-phase work — each phase has files, signatures, acceptance criteria.
- §8-9: Timeline and risks — managerial.
- §10-12: Success criteria, open decisions, references.
- Appendices: Glossary, file manifest, pick-up-mid-work guide.

**If you (another agent) are picking this up mid-work**: jump to Appendix C for the resumption protocol.

---

## 1. Background

### 1.1 Original ambition (v0.2 Path C)

From `gut-c-doctrine.md` v0.2 §3.2 (universal sayability program):

> A V-enriched Lawvere theory T_GUT together with a base SMCC V determines a category Mod_C(T_GUT) of T_GUT-models in any V-enriched ordinary category C. The universal sayability theorem asserts that for fixed C and generator δ, all T_GUT-models in C with generator-image δ are V-naturally isomorphic.

Crucially, the quantifier "any V-enriched ordinary category C" covers **continuous V's**:

- V = Set → ordinary Lawvere theory (Lawvere 1963)
- V = Ab → additive Lawvere theory (Linton 1966)
- V = Vect_K → linear theory / PROP
- V = Cat → 2-Lawvere theory
- **V = Top, Met, Ban, Hilb → continuous / analytic V-enriched theories**

The driving theorem is **Power 1999 *Enriched Lawvere theories*, TAC 6 no. 7, Theorem 4.5**:

> The 2-category of V-enriched Lawvere theories is 2-equivalent to the 2-category of finitary V-monads on V.

This equivalence, once formalized, would let us transfer model categoricity between V's via the finitary-V-monad side.

### 1.2 Current state (v0.5, post-PR #64)

`T_GUT.lean:691`:
```lean
theorem universal_sayability (δ : C) (M : TGUTRealisationCore C δ) :
    Nonempty (RealIso M (canonical δ)) :=
  ⟨{ iso := componentIso δ M }⟩
```

Where:
- `C : Type` — **no V-enrichment parameter**
- `TGUTRealisationCore C δ` — concrete per-substrate datum
- `componentIso` — direct componentwise iso construction

The four `Foundation/Doctrine/Instance/{Algebraic,Heyting,Quantum,Topological}.lean` files instantiate this for the four discrete substrates. All four are 0-axiom 0-sorry (post PR #61 + PR #64 audit).

### 1.3 What got deferred and why

**Deferred component**: V-enriched part of the framework — specifically, anything that requires V-cotensor or weighted enriched limits in V.

**Why it got deferred**:

1. **Mathlib gap**: Mathlib (as of 2026-05-18) has conical V-limits but **lacks V-cotensors and weighted V-limits**. These are *foundational* for Power 1999's setup. Without them, the V-enriched part of the framework cannot be fully formalized. Reference: `EnrichedLawvereTheory.lean:96-99`.

2. **No upstream activity**: Nobody in Mathlib is working on V-cotensor / weighted enriched limits (verified by checking `.lake/packages/mathlib/Mathlib/CategoryTheory/Enriched/` content as of 2026-05-18).

3. **Direct concrete route gave fast wins**: Each of the 4 discrete substrates was a ~500-LOC delivery achievable without enriched infrastructure. Cumulative win was visible; abstract win was invisible.

4. **Doctrine drift**: `gut-c-doctrine.md` was updated multiple times (v0.2 → v0.3 → v0.4 → v0.5) but the enriched ambition was never *explicitly* marked "deferred". It silently transitioned to "not currently implemented".

### 1.4 Decision (2026-05-18)

User reviewed scope gap analysis and chose **Option (iii): fulfill the original ambition** rather than accept the trimmed scope. This plan operationalizes that decision.

---

## 2. Goal Statement

### 2.1 Precise success criterion

A theorem of the following form (or equivalent), 0-axiom 0-sorry, in `Foundation/Doctrine/T_GUT_Enriched.lean`:

```lean
theorem enriched_universal_sayability
    {V : Type u'} [Category.{v'} V] [SymmetricMonoidalCategory V]
    [MonoidalClosed V] [HasFiniteProducts V] [HasCotensors V]
    [HasWeightedLimits V]                        -- Phase 1 deliverables
    [EnrichedLawvereTheory V T_GUT_V]            -- Phase 2 deliverable
    {C : Type u} [EnrichedOrdinaryCategory V C]
    [HasFiniteVProducts C] [HasVCotensors C]
    (δ : C) (M M' : EnrichedT_GUT_Model V T_GUT_V C δ) :
    Nonempty (EnrichedRealIso M M')
```

And this theorem must be **non-vacuously instantiated** at least once for a continuous V — see §6 (V=Hilb is the recommended first instance).

### 2.2 What "non-vacuously" means

The current `universal_sayability` is *technically* universal over `C : Type`, but only 4 substrates are actually verified to satisfy `TGUTRealisationCore`. For the enriched version, we need:

- At least 1 *continuous* V (recommendation: V = Hilb, the category of separable Hilbert spaces) with an actual enriched substrate
- That substrate must be `EnrichedT_GUT_Model V T_GUT_V C δ` for some real C and δ
- And `enriched_universal_sayability` instantiated there must give a non-trivial iso

### 2.3 What stays / what changes

**Preserved unchanged**:
- All existing 4-substrate work (`Algebraic`, `Heyting`, `Quantum`, `Topological` instance files)
- The existing `universal_sayability` theorem (at `T_GUT.lean:691`)
- All 0-axiom 0-sorry results

**Newly added**:
- Mathlib upstream contributions (Phase 1)
- Completion of `EnrichedLawvereTheory.lean` (Phase 2)
- New file: `Foundation/Doctrine/Instance/HilbertEnriched.lean` (Phase 3)
- New file: `Foundation/Doctrine/T_GUT_Enriched.lean` (Phase 4)

**Renamed / re-qualified**:
- Current `universal_sayability` → keep name; add comment "categorical version; V-enriched generalization in `T_GUT_Enriched.lean`"

---

## 3. Architecture

### 3.1 Three-layer dependency

```
┌─────────────────────────────────────────────────────────────┐
│ Layer 3: SSBX continuous substrate (Phase 3)                │
│   - Foundation/Doctrine/Instance/HilbertEnriched.lean       │
│   - Foundation/Doctrine/T_GUT_Enriched.lean (Phase 4)       │
│   ↑                                                          │
│ Layer 2: SSBX enriched core completion (Phase 2)            │
│   - Foundation/Doctrine/EnrichedLawvereTheory.lean          │
│     (close sorries: freeVFunctor, Power Thm 4.5)            │
│   ↑                                                          │
│ Layer 1: Mathlib upstream PR-3 (Phase 1)                    │
│   - V-cotensor                                               │
│   - Weighted enriched limits                                 │
│   - Finitary V-monad                                         │
│   - EnrichedMonad class                                      │
│   - Power 1999 Theorem 4.5 (statement; maybe proof)         │
└─────────────────────────────────────────────────────────────┘
```

**Critical path**: Layer 1 must land in Mathlib (or be vendored locally) before Layer 2 can close its sorries.

### 3.2 Vendor-or-upstream decision

Two routes:

- **Route U (upstream)**: Submit Mathlib PRs, get them reviewed and merged, then build on them. Slow (months per PR), but the work lives where it belongs and benefits everyone.
- **Route V (vendor)**: Copy the needed Mathlib infrastructure into `formal/SSBX/Foundation/Enriched/` and develop there. Fast (no review queue), but creates duplication.

**Recommendation**: Route U for the foundational pieces (V-cotensor, weighted limits — these are clean general-purpose Mathlib contributions). Route V for the SSBX-specific applications. Hybrid in practice.

### 3.3 Out of scope (for this plan)

- Adelic structure / RH attack (closed by `[[e1-rtower-rh-closed]]`)
- 2-categorical structure of V-enriched theories (Power 1999 only does 1-cat reduction)
- Internal type theory for V-categories (would require HoTT-level changes)
- Migration of existing 4 substrates into the enriched framework (they stay as-is; enriched framework adds *new* substrates)

---

## 4. Phase 1: Mathlib Upstream PR-3 (V-Cotensor + Weighted Enriched Limits)

### 4.1 What Mathlib has now (verified 2026-05-18)

```
Mathlib/CategoryTheory/Enriched/
├── Basic.lean                 ✓ EnrichedCategory V C
├── Ordinary/
│   └── Basic.lean             ✓ EnrichedOrdinaryCategory
├── Limits/
│   ├── HasConicalLimits.lean   ✓ Conical limits
│   ├── HasConicalProducts.lean ✓ Conical products
│   └── HasConicalTerminal.lean ✓ Conical terminal
```

**What exists**: bare `EnrichedCategory`, `EnrichedOrdinaryCategory`, **conical** limits/products/terminal.

**What's missing for Power 1999**:

- V-cotensor: given X : V, Y : C, the object `cotensor X Y : C` satisfying `Hom_C(Z, cotensor X Y) ≅ Hom_V(X, Hom_C(Z, Y))`
- General weighted V-limits (cotensors are a special case)
- Finitary V-monads (V-monads preserving filtered conical colimits)
- The `EnrichedMonad V` class

### 4.2 PR-3 sub-PR breakdown

#### Sub-PR 3.1: `Mathlib/CategoryTheory/Enriched/Limits/Cotensor.lean` (~300-500 LOC)

**Content**:
```lean
namespace CategoryTheory.Enriched

variable {V : Type u'} [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- The cotensor `X ⋔ Y` of `X : V` and `Y : C` is the V-cotensor: an
object of `C` representing the V-functor `Z ↦ (X ⟶[V] (Z ⟶[V] Y))`. -/
class HasCotensor (X : V) (Y : C) where
  cotensor : C
  hom_iso : ∀ Z, (Z ⟶ cotensor) ≃ (X ⟶ ((Z ⟶ Y) : V))
  -- ... naturality conditions

class HasCotensors where
  hasCotensor : ∀ (X : V) (Y : C), HasCotensor X Y

/-- For V = Set: cotensor X Y = X^Y (the function space). -/
instance Set_HasCotensors : @HasCotensors (Type*) _ _ C _ _ := ...

-- ... lemmas about cotensors and conical products
```

**References**:
- Kelly 1982 §3.7 (V-cotensors / "powers")
- nLab: [cotensor](https://ncatlab.org/nlab/show/cotensor)

#### Sub-PR 3.2: `Mathlib/CategoryTheory/Enriched/Limits/Weighted.lean` (~500-800 LOC)

**Content**:
```lean
/-- A V-weight is a V-functor W : J^op → V (in the enriched sense). -/
structure VWeight (V : Type u') [...] (J : Type) [Category J] where
  weight : J^op ⥤ V
  -- naturality

/-- The W-weighted V-limit of a V-diagram D : J → C is an object
`limit W D : C` together with a V-natural cone. -/
class HasWeightedLimit (W : VWeight V J) (D : J ⥤ C) where
  limit : C
  cone : ...
  isLimit : ...

class HasWeightedLimits where
  ...

/-- Cotensors are special weighted limits where J is terminal. -/
instance : HasCotensor → HasWeightedLimit ... := ...
```

**References**:
- Kelly 1982 §3.1-3.5 (weighted limits foundational chapter)
- Borceux 1994 vol. 2 Ch. 6

#### Sub-PR 3.3: `Mathlib/CategoryTheory/Enriched/Monad/Basic.lean` (~300-500 LOC)

**Content**:
```lean
/-- A V-enriched monad on a V-category C is a V-functor T : C → C
with V-natural η : id → T and μ : T² → T satisfying the monad laws. -/
class EnrichedMonad (T : C ⥤ C) [EnrichedFunctor V T] where
  η : 𝟭 C ⟶ T
  μ : T ⋙ T ⟶ T
  -- V-naturality + monad laws

/-- For V = Set: recovers ordinary Mathlib `Monad`. -/
instance : Monad → EnrichedMonad (V := Type*) := ...
```

#### Sub-PR 3.4: `Mathlib/CategoryTheory/Enriched/Monad/Finitary.lean` (~200-400 LOC)

**Content**:
```lean
/-- A V-monad is finitary if it preserves filtered conical colimits. -/
class FinitaryEnrichedMonad (T : C ⥤ C) [EnrichedMonad V T]
    [HasFilteredColimits C] where
  preserves_filtered_colimits : ∀ J : Type, [Category J] → [IsFiltered J] →
    PreservesColimitsOfShape J T
```

#### Sub-PR 3.5: `Mathlib/CategoryTheory/Enriched/Power.lean` — Power 1999 Theorem 4.5 (~500-1500 LOC)

**Content**:
```lean
/-- Power 1999 Theorem 4.5: the 2-category of V-enriched Lawvere theories
is 2-equivalent to the 2-category of finitary V-monads on V.

This file gives the 1-categorical reduction (objects + 1-morphisms).
The full 2-categorical version is left as a follow-up. -/

namespace CategoryTheory.Enriched.Power

/-- The forward functor: V-enriched Lawvere theory → finitary V-monad. -/
def theoryToMonad : EnrichedLawvereTheory V T → FinitaryEnrichedMonad V T := ...

/-- The backward functor: finitary V-monad → V-enriched Lawvere theory. -/
def monadToTheory : FinitaryEnrichedMonad V T → EnrichedLawvereTheory V T := ...

/-- The equivalence at the 1-categorical level. -/
theorem theory_monad_equiv :
    EnrichedLawvereTheory V T ≃ FinitaryEnrichedMonad V T := ...
```

**This is the largest sub-PR**. May need to be split further. The actual proof is technically subtle (size issues, choice principles).

### 4.3 Open design questions for Phase 1

- **Universe levels**: V-categories live in size-rich type universes. The Mathlib convention is to keep `[Category.{v'} V]` and `[Category.{v} C]` separate. Power 1999 may need `v' = v` or careful universe parameter management.
- **Choice principles**: Power 1999 may use classical choice essentially. Document any dependencies.
- **Conical vs weighted as default**: The current Mathlib `HasConicalProducts` etc. uses *conical*; Power 1999 uses *weighted*. Bridge lemmas needed.
- **Skeleton handling**: V-enriched Lawvere theories can have either strict or "up-to-iso" object data. Mathlib convention TBD.

### 4.4 Acceptance criteria for Phase 1

- All 5 sub-PRs merged into Mathlib `master`
- `lake update` in SSBX pulls in the new APIs
- Existing `EnrichedLawvereTheory.lean` builds against the new APIs (still with its sorries — Phase 2 will close them)

### 4.5 Risks for Phase 1

- **Slow review**: Mathlib has a small review team; large enriched-category PRs may sit for months
- **Design pushback**: Reviewers may have different opinions on weighted-vs-conical, universe handling
- **Mathematical errors**: Power 1999's proof has technical subtleties; replicating in Lean may surface gaps
- **Mitigation**: Engage Mathlib zulip/category-theory channel early; small first PR (3.1 only) to test reception

---

## 5. Phase 2: Close `EnrichedLawvereTheory.lean` Sorries

### 5.1 Current state of the file

`formal/SSBX/Foundation/Doctrine/EnrichedLawvereTheory.lean`:

- **929 LOC total**
- Currently `noncomputable def freeVFunctor` at line 882 has `sorry` body
- `EnrichedLawvereTheorySig V T` / `EnrichedLawvereTheory V T` structures: complete signatures, no sorries
- `EnrichedModel V T C` / `EnrichedModelMorphism`: complete
- `freePowerEnrichment` / `tensorPowerObj`: complete
- `freeForgetfulAdjunction` (line 889): currently `: True := by trivial` (placeholder for Power Thm 4.5)
- `PowerStrictTheory` (line 830): structure stub, `identity_on_objects : True := by trivial` placeholder
- No `axiom` declarations (clean)

### 5.2 Sorries to close

#### Sorry 1: `freeVFunctor` (line 882)

**Current**:
```lean
noncomputable def freeVFunctor :
    -- conceptually: `C ⥤ EnrichedModel V T C`
    C → EnrichedModel V T C :=
  fun _c => sorry
```

**Problem**: signature is degenerate (any function satisfies it). Needs to be promoted to a proper V-functor.

**Target after Phase 1**:
```lean
noncomputable def freeVFunctor : C ⥤ EnrichedModel V T C :=
  -- use Phase 1's `HasCotensors V C` + Power Theorem 4.5
  sorry  -- to be closed via Power 4.5

theorem freeVFunctor_isLeftAdjoint :
    IsLeftAdjoint (freeVFunctor V T C) := by
  -- use Power Theorem 4.5's adjunction
  sorry

theorem freeForgetfulAdjunction :
    freeVFunctor V T C ⊣ forgetfulVFunctor V T C := by
  -- ditto
  sorry
```

**Plan**: rewrite signature to be V-functor; supply proof using Phase 1's Power 4.5 API.

#### Sorry 2: `enriched_lawvere_iff_finitary_v_monad`

(Located in `EnrichedLawvereTheory.lean` — exact line TBD; search for "Theorem 4.5")

**Current**: placeholder `:= True := by trivial`

**Target**:
```lean
theorem enriched_lawvere_iff_finitary_v_monad
    [HasCotensors V V] [HasFilteredColimits V] :
    Nonempty (EnrichedLawvereTheory V T ≃ FinitaryEnrichedMonad V V) := by
  exact ⟨CategoryTheory.Enriched.Power.theory_monad_equiv⟩
```

**Plan**: direct port from Phase 1 Sub-PR 3.5.

### 5.3 Strategy per sorry

For each sorry:

1. **Read the surrounding doctrine note** — it documents the intended math
2. **Check Phase 1 has supplied** the relevant API
3. **Write the Lean proof** — usually a thin adapter over Phase 1
4. **Verify build** — `lake build SSBX.Foundation.Doctrine.EnrichedLawvereTheory`
5. **Run `#print axioms`** — must remain on `propext, Classical.choice, Quot.sound` only

### 5.4 Acceptance criteria for Phase 2

- `EnrichedLawvereTheory.lean`: 0 sorry, 0 axiom (beyond standard Lean 3)
- All theorems pass `#print axioms` check
- File documentation updated to reflect closures
- The dead-code section header (`### Forgetful and free V-T-models (Power 1999 §2)`) is no longer dead

---

## 6. Phase 3: Build Hilbert Substrate (V = Hilb)

### 6.1 Why Hilb (not Top, Met, Ban)

We need **at least one** continuous V to non-vacuously instantiate enriched_universal_sayability. Candidates:

| V | Pros | Cons |
|---|---|---|
| **Top** | Most general; preserves Heyting (Stone duality) and Topological (locale) substrates | Weakest analytic content; no inner product or norm |
| **Met** | Has Cauchy / completion | No tensor structure unless we go to Met-Closed |
| **Ban** | Banach algebras, C*-flavored | Too far from current Quantum substrate |
| **Hilb** | **Direct extension of existing Quantum (PauliBase on ℂ²)**; rich SMCC structure via Hilbert tensor product; opens spectral theory | Mathlib's Hilbert API focuses on bounded operators; some lemmas may be missing |

**Decision**: V = Hilb (separable Hilbert spaces with Hilbert tensor product). Rationale:

1. **Continuity with existing work**: PauliBase is finite-dim Hilbert; extending to separable infinite-dim is natural progression
2. **SMCC structure**: `(Hilb, ⊗_Hilb, ℂ)` is a well-established SMCC (e.g., Pisier 2003)
3. **Mathlib has**: `Mathlib.Analysis.InnerProductSpace.*`, `Mathlib.Analysis.NormedSpace.*` — much of the infrastructure
4. **Substrate symmetry**: existing 4-substrate framework has discrete-quantum (Klein-four); adding continuous-quantum (Hilb) makes the framework cover discrete-vs-continuous on the quantum axis
5. **Future RH possibility**: should this framework ever revisit RH (currently closed by E1), Hilb is where H-P-style operators would live

### 6.2 Carrier and generator (V = Hilb)

```lean
/-- The category of separable Hilbert spaces with bounded linear maps. -/
abbrev SepHilb : Type _ := SeparableHilbertSpaceCat ℂ

instance : SymmetricMonoidalCategory SepHilb := -- via Hilbert tensor product

/-- The generator: ℂ as a 1-dim Hilbert space. -/
def δ_Hilb : SepHilb := ⟨ℂ, _⟩

/-- T_GUT model carrier in Hilb: the R-tower realized via tensor powers. -/
def TGUTCarrier_Hilb : SepHilb := ...
```

### 6.3 R-tower realization in Hilb

The R-tower has sizes 2, 4, 16, 256, ... at levels R_0, R_1, R_2, R_4, R_8, ... If we identify R_n with `(ℂ²)^⊗n` (tensor power), then:

- R_0 = ℂ (terminal/initial)
- R_1 = ℂ² (qubit)
- R_2 = ℂ²⊗ℂ² ≅ ℂ⁴
- R_n = (ℂ²)^⊗n ≅ ℂ^(2^n)

But this is **finite-dim**. To get a separable infinite-dim substrate, we'd take the inductive limit or the full Fock space:

```lean
/-- The Hilbert Fock space: direct sum of all finite tensor powers. -/
def FockSpace : SepHilb := ⊕_{n=0}^∞ (ℂ²)^⊗n -- with l² norm
```

Or, more conservatively for first delivery, restrict to finite-dim case as the **finite-dim Hilb sub-substrate** — this directly extends PauliBase:

```lean
/-- Finite-dim Hilbert spaces: subSMCC of Hilb. -/
abbrev FinHilb : Type _ := FinDimHilbertSpaceCat ℂ

instance : SymmetricMonoidalCategory FinHilb := ...
```

**Decision for Phase 3.0**: Start with FinHilb (finite-dim) for the *first* enriched substrate. Adds separable infinite-dim Hilb as **Phase 3.5** (follow-up).

### 6.4 File manifest for Phase 3

```
formal/SSBX/Foundation/Doctrine/Instance/
├── HilbertEnriched.lean            (new, ~400-600 LOC)
│   - SepHilb / FinHilb SMCC instance
│   - TGUTCarrier_Hilb definition
│   - R-tower realization in Hilb
│   - TGUTRealisationCore_Hilb instance
│   - SymmetricMonoidalCategory FinHilb
│   - HasCotensors / HasWeightedLimits for FinHilb (Phase 1 application)
└── HilbertEnrichedTests.lean       (new, ~100 LOC)
    - Sanity tests
    - Compare with existing Quantum (PauliBase) at finite-dim
```

### 6.5 Connection to existing PauliBase Klein-four

The existing `Foundation/Doctrine/Instance/Quantum.lean` uses PauliBase (Klein-four `V₄ = {I, X, Y, Z}` on ℂ²). This is the *categorical* quantum substrate.

Phase 3's Hilb enriched substrate uses ℂ² as the carrier directly — **the same Hilbert space**, but viewed as a Hilb-object rather than as a Klein-four-acted-on object. They coexist:

- Quantum (categorical): PauliBase acts on ℂ²; T_GUT model is the *action structure*
- Hilbert (enriched): ℂ² is a Hilb-object; T_GUT model is the *Hilb-functorial structure*

Both are valid T_GUT models with related but distinct content. The relationship is:
```
Quantum (categorical)  --forget action structure-->  Hilbert (enriched)
```

This forgetful is *not* an iso — that's why Hilbert is a genuinely new substrate.

### 6.6 Acceptance criteria for Phase 3

- `HilbertEnriched.lean` builds, 0 sorry, 0 axiom (beyond standard)
- `TGUTRealisationCore_Hilb` is a valid instance
- `lake build SSBX.Foundation.Doctrine.Instance.HilbertEnriched` succeeds
- A sanity theorem (e.g., `TGUTCarrier_Hilb_isHilb : True`) compiles

---

## 7. Phase 4: Prove `enriched_universal_sayability`

### 7.1 Statement (target)

In a new file `formal/SSBX/Foundation/Doctrine/T_GUT_Enriched.lean` (~200-400 LOC):

```lean
namespace SSBX.Foundation.Doctrine

open CategoryTheory CategoryTheory.Enriched

variable (V : Type u') [Category.{v'} V] [SymmetricMonoidalCategory V]
variable [MonoidalClosed V] [HasFiniteProducts V]
variable [HasCotensors V V] [HasWeightedLimits V]

/-- The V-enriched version of T_GUT, instantiating Power 1999's enriched
Lawvere theory framework with the T_GUT operations and laws. -/
def T_GUT_V : EnrichedLawvereTheory V (TGUT_Carrier V) := ...

variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable [HasFiniteVProducts C] [HasVCotensors C V]

/-- A V-enriched T_GUT model in V-category C with generator-image δ. -/
abbrev EnrichedT_GUT_Model (δ : C) :=
  EnrichedModel V (T_GUT_V V) C  -- with generator constraint

/-- V-enriched universal sayability:
all V-T_GUT models in a fixed C with fixed generator δ
are V-enriched isomorphic. -/
theorem enriched_universal_sayability
    (δ : C) (M M' : EnrichedT_GUT_Model V δ) :
    Nonempty (EnrichedRealIso V M M') := by
  -- Use Power 1999 Theorem 4.5 (via Phase 2's
  -- `enriched_lawvere_iff_finitary_v_monad`):
  -- 1. Pass M, M' through to the finitary V-monad side
  -- 2. On the monad side, both are algebras for the same monad
  -- 3. The free-forgetful adjunction gives the iso
  sorry  -- closed by Phase 2's `freeForgetfulAdjunction`

end SSBX.Foundation.Doctrine
```

### 7.2 Proof outline

The proof has three steps:

1. **Lift to monad side**: Use `enriched_lawvere_iff_finitary_v_monad` (closed in Phase 2) to view T_GUT_V as a finitary V-monad T.
2. **Both M, M' are T-algebras**: By Power 1999, T-Alg(C) ≃ EnrichedModel V T_GUT_V C. So M, M' correspond to T-algebras A, A' on C.
3. **Algebras with same underlying are iso**: Use the free-forgetful adjunction at the algebra level + generator constraint to construct the iso between A and A'.

### 7.3 Files for Phase 4

```
formal/SSBX/Foundation/Doctrine/
├── T_GUT.lean                       (existing; unchanged or add cross-ref comment)
├── T_GUT_Enriched.lean              (new, ~200-400 LOC)
│   - T_GUT_V definition (V-enriched version)
│   - EnrichedT_GUT_Model alias
│   - enriched_universal_sayability theorem + proof
│   - Connection to existing categorical universal_sayability
├── T_GUT_EnrichedHilb.lean          (new, ~100 LOC; instantiates Phase 3)
│   - Specialize T_GUT_V to V = FinHilb (Phase 3 substrate)
│   - Prove enriched_universal_sayability for V = FinHilb
│   - Sanity: instantiate with some δ : FinHilb, verify non-vacuously
└── T_GUT_EnrichedHilb_Tests.lean    (new, ~50 LOC)
```

### 7.4 Acceptance criteria for Phase 4

- `T_GUT_Enriched.lean` and `T_GUT_EnrichedHilb.lean` build, 0-axiom 0-sorry
- `enriched_universal_sayability` `#print axioms` returns only `[propext, Classical.choice, Quot.sound]`
- Non-vacuous instantiation: `T_GUT_EnrichedHilb.lean` proves enriched_universal_sayability for V = FinHilb with a concrete δ
- Connection theorem proved or stated: `universal_sayability` (current categorical, T_GUT.lean:691) is a corollary of `enriched_universal_sayability` specialized to V = Type (= Set as monoidal)

---

## 8. Timeline & Resource Estimates

### 8.1 By phase (calendar time, single full-time developer or focused multi-session AI)

| Phase | Sub-tasks | LOC | Estimated calendar time | Mathlib review delay |
|---|---|---|---|---|
| 1 | Mathlib PR-3 (5 sub-PRs) | 1800-3700 | 2-3 months work + 3-6 months review | **major** |
| 2 | Close EnrichedLawvereTheory sorries | 200-400 | 1-2 weeks (after Phase 1) | none |
| 3 | Hilbert substrate | 500-700 | 2-4 weeks (parallel with Phase 2 if SMCC instance is in Mathlib already) | none |
| 4 | enriched_universal_sayability + Hilb instantiation | 350-550 | 2-3 weeks (after Phase 2 and 3) | none |

**Total**: 2850-5350 LOC over 4-7 months of focused work + 3-6 months Mathlib review delay. **Realistic total: 9-15 months from kickoff.**

### 8.2 Critical path

```
Phase 1 → Phase 2 → Phase 4
   ↓
   Phase 3 (parallel with Phase 2)
```

Phase 1 is the bottleneck. Cannot start Phase 2 until Phase 1's APIs are available (either upstream-merged or vendored locally).

### 8.3 Reduction options

| Option | Tradeoff |
|---|---|
| **Skip Phase 3 finite-dim, go direct to separable Hilb** | More math, less work later but more risk now |
| **Skip Phase 3 entirely, use V = Set as the trivial enriched case** | Demonstrates enriched framework works without continuous substrate, but doesn't fulfill original ambition's "continuous" promise — would need Phase 3 as follow-up anyway |
| **Vendor Mathlib gaps** (Route V) | Skip review delay; introduce duplication and maintenance debt |
| **Defer Phase 1.5 (Power Thm 4.5 proof)** to vendor / future Mathlib | Phase 2 can close sorries via the Power theorem *statement* + axiom; later replace axiom with proof when Phase 1.5 lands. *But* this violates `[[no-axiom-for-zero-sorry]]` unless the axiom is truly minimal and well-anchored to Power 1999 |

---

## 9. Risks Register

| ID | Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|---|
| R1 | Mathlib doesn't accept PR-3 (design rejected) | Medium | High | Engage zulip early; design with Mathlib conventions; offer to maintain branch |
| R2 | Mathlib review takes 12+ months | High | Medium | Vendor critical pieces locally; resync when upstream catches up |
| R3 | Power 1999 proof has technical subtleties surfacing only in Lean | Medium | Medium | Allocate buffer in Phase 1.5; consult Power directly if reachable |
| R4 | Universe / size issues in V-enriched setup | Medium | Medium | Follow Mathlib conventions strictly; document any escapes |
| R5 | Hilb SMCC structure missing from Mathlib | Low | Medium | Build it in Phase 3 as sub-deliverable |
| R6 | Existing 4-substrate work doesn't cleanly coexist with enriched | Low | Low | Keep parallel; document non-migration explicitly |
| R7 | User priorities shift before completion | Medium | Variable | Plan structure preserves intermediate value (each phase's deliverables stand alone) |
| R8 | Bus factor: agent / user discontinuity | Medium | High | This plan + Appendix C for cold pickup |

---

## 10. Success Definition (Done Done)

The work is "done" when ALL of the following hold:

1. ✓ Mathlib PR-3 sub-PRs merged into Mathlib `master` (or vendored equivalents in SSBX)
2. ✓ `EnrichedLawvereTheory.lean` has 0 sorry
3. ✓ At least one continuous V (recommended FinHilb) is implemented as a continuous substrate
4. ✓ `enriched_universal_sayability` proved, 0-axiom 0-sorry (beyond `propext, Classical.choice, Quot.sound`)
5. ✓ Non-vacuous instantiation: theorem applied to V = FinHilb with a concrete δ
6. ✓ `gut-c-doctrine.md` updated to v0.6 — explicit mark "V-enriched ambition: FULFILLED"
7. ✓ Memory `project_e1_rtower_rh_closed.md` updated to reflect new framework capabilities (note: RH still closed; enrichment doesn't reopen it, just delivers original Power 1999 ambition)
8. ✓ At least 2 sanity tests for V = FinHilb passing

**Stretch goals (would be nice but not gating)**:

- 9. ⊙ Separable infinite-dim Hilb (full SepHilb) substrate as Phase 3.5
- 10. ⊙ A second continuous substrate (Top or Met) to demonstrate genuine V-quantification
- 11. ⊙ Documentation of "discrete → enriched lift": migration path for existing 4 substrates

---

## 11. Open Decisions for Future Sessions

These are decisions *intentionally deferred* — pick up when their phase is reached:

| Decision | Phase | Notes |
|---|---|---|
| Universe handling: `[Category.{v} C]` vs `[Category.{u} C]` | 1.1 | Match Mathlib conventions; check at first PR |
| Conical vs weighted as default | 1.2 | Power 1999 uses weighted; SSBX may prefer conical; bridge lemmas either way |
| Skeleton vs up-to-iso for theory objects | 2 | Pure Power 1999 is skeleton; Mathlib idiomatic may differ |
| Finite-dim Hilb vs separable Hilb for first substrate | 3 | This plan says finite-dim; reconsider when Phase 1 lands |
| Migration of existing 4 substrates to enriched form | 4+ | Optional; keep parallel by default |
| Whether to remove or keep `freeVFunctor`'s placeholder signature | 2 | Plan says rewrite; could also delete and start fresh |

---

## 12. References

### 12.1 Mathematical references

- **Power, J. 1999**. *Enriched Lawvere theories*. Theory and Applications of Categories 6 no. 7, 83–93. — The central theorem (Thm 4.5) this plan operationalizes.
- **Kelly, G. M. 1982**. *Basic Concepts of Enriched Category Theory*. Cambridge University Press; TAC Reprint 10 (2005). — Reference for V-limits, V-cotensors, V-functor categories.
- **Lawvere, F. W. 1963**. *Functorial Semantics of Algebraic Theories*. PhD thesis Columbia; TAC Reprint 5 (2004). — Foundational `V = Set` case.
- **Hyland, M. and Power, J. 2007**. *The category theoretic understanding of universal algebra: Lawvere theories and monads*. ENTCS 172, 437–458. — Modern survey.
- **Borceux, F. 1994**. *Handbook of Categorical Algebra*, vol. 2. Cambridge University Press. — Ch. 6 weighted limits.
- **Linton, F. E. J. 1966**. *Some aspects of equational categories*. La Jolla 1965. — Additive theories `V = Ab` case.
- **Pisier, G. 2003**. *Introduction to Operator Space Theory*. Cambridge. — Hilb SMCC structure.

### 12.2 SSBX framework cross-references

- `formal/SSBX/Foundation/Doctrine/EnrichedLawvereTheory.lean` — Phase 2 target file (929 LOC, 2 sorries to close)
- `formal/SSBX/Foundation/Doctrine/T_GUT.lean:691` — current `universal_sayability` (preserve)
- `formal/SSBX/Foundation/Doctrine/LawvereTheory.lean` — sibling file (`V = Set` case, agent G1 delivery)
- `formal/SSBX/Foundation/Doctrine/Instance/{Algebraic,Heyting,Quantum,Topological}.lean` — existing 4 discrete substrates (do not modify)
- `docs-next/00_start/gut-c-doctrine.md` — versioned doctrine (currently v0.5; update to v0.6 when this plan completes)
- `docs-next/10_formal_形式/E1-rtower-theta-experiment.md` — the analysis that led to choosing this plan
- `docs-next/10_formal_形式/categorical-vs-analytic-gap.md` — (if user asks) sister doc explaining why this work doesn't help RH

### 12.3 Mathlib references (verified 2026-05-18)

```
Mathlib/CategoryTheory/Enriched/
├── Basic.lean                 — EnrichedCategory V C
├── Ordinary/Basic.lean        — EnrichedOrdinaryCategory
├── Limits/HasConical*.lean    — conical limits/products/terminal (existing)
└── (gaps to fill in Phase 1)
```

```
Mathlib/Analysis/InnerProductSpace/   — Hilbert space API for Phase 3
Mathlib/Analysis/NormedSpace/         — Banach API (for potential V=Ban)
Mathlib/CategoryTheory/Monad/Basic    — Monad class (Phase 1 will extend to enriched)
```

### 12.4 Memory cross-references

- `[[e1-rtower-rh-closed]]` — context: why RH is closed; this plan doesn't reopen it
- `[[no-axiom-for-zero-sorry]]` — meta-rule: closes sorries with proofs, not axioms
- `[[dont-drop-theorems]]` — meta-rule: don't weaken statements
- `[[v4-shi-doctrine-out-2026-05-17]]` — V₄ retired; doesn't affect this plan but useful context
- `[[squaring-tower]]` — R-tower structure; relevant for Phase 3 (Hilb realization)
- `[[final-theory-2026-05-10]]` — overall framework state

---

## 13. Memory and Doctrine Updates (When Complete)

Once Phase 4 lands:

1. **Update `gut-c-doctrine.md`** v0.5 → v0.6:
   - §3.2 Universal Sayability: mark "V-enriched: COMPLETE"
   - §11.1 PR-3: mark "DONE"
   - Add §3.2bis discussing the categorical/enriched relationship

2. **Add memory** `project_enriched_universal_sayability_done.md`:
   - Status: done
   - Date: <completion date>
   - Files: list of new/modified files
   - Cross-ref to this plan
   - Closes: this plan's promise

3. **Update memory** `project_e1_rtower_rh_closed.md`:
   - Add note: "Framework now V-enriched (V=FinHilb at minimum); RH path still closed by §3 root cause (T_GUT axioms remain non-analytic)"

4. **Update memory** `project_operator_metadata_layer.md` and others as relevant

---

## Appendix A: Glossary

| Term | Definition |
|---|---|
| V | A base symmetric monoidal closed category (the enriching base) |
| V-category | A category enriched over V; hom-objects live in V |
| V-functor | A functor between V-categories preserving V-structure |
| V-cotensor | The V-analogue of "function space"; written `X ⋔ Y` for `X : V`, `Y : C` |
| Weighted V-limit | The V-enriched generalization of conical limits; allows arbitrary V-weights |
| V-monad | A monad on a V-category whose unit and multiplication are V-natural |
| Finitary V-monad | A V-monad preserving filtered conical colimits |
| V-enriched Lawvere theory | Power 1999's V-enriched generalization of Lawvere's algebraic theories |
| FinHilb | The category of finite-dimensional Hilbert spaces over ℂ |
| SepHilb | The category of separable Hilbert spaces over ℂ |
| Power 1999 Theorem 4.5 | The 2-equivalence between V-enriched Lawvere theories and finitary V-monads |

## Appendix B: File Manifest

**Phase 1 (Mathlib)**:
```
Mathlib/CategoryTheory/Enriched/Limits/Cotensor.lean      [new]
Mathlib/CategoryTheory/Enriched/Limits/Weighted.lean      [new]
Mathlib/CategoryTheory/Enriched/Monad/Basic.lean          [new]
Mathlib/CategoryTheory/Enriched/Monad/Finitary.lean       [new]
Mathlib/CategoryTheory/Enriched/Power.lean                [new]
```

**Phase 2 (SSBX)**:
```
formal/SSBX/Foundation/Doctrine/EnrichedLawvereTheory.lean [modify: close 2 sorries]
```

**Phase 3 (SSBX)**:
```
formal/SSBX/Foundation/Doctrine/Instance/HilbertEnriched.lean       [new]
formal/SSBX/Foundation/Doctrine/Instance/HilbertEnrichedTests.lean  [new]
```

**Phase 4 (SSBX)**:
```
formal/SSBX/Foundation/Doctrine/T_GUT_Enriched.lean             [new]
formal/SSBX/Foundation/Doctrine/T_GUT_EnrichedHilb.lean         [new]
formal/SSBX/Foundation/Doctrine/T_GUT_EnrichedHilb_Tests.lean   [new]
```

**Documentation**:
```
docs-next/00_start/gut-c-doctrine.md                        [modify: v0.5 → v0.6]
docs-next/10_formal_形式/enriched-universal-sayability-plan.md [this file]
```

**Memory** (after completion):
```
project_enriched_universal_sayability_done.md   [new]
project_e1_rtower_rh_closed.md                  [modify: note enrichment]
```

## Appendix C: Picking This Up Mid-Work

If you (another Claude agent, or future self) are resuming this work:

### C.1 First steps (5 minutes)

1. Read this plan top-to-bottom — yes, all of it
2. Check current branch state: `git log --oneline -20`
3. Check Mathlib branch state: `cd .lake/packages/mathlib && git log --oneline -10`
4. Look for files matching the Phase 1-4 manifest in Appendix B — which exist?

### C.2 Determine current phase

Run this checklist:

```bash
# Check Phase 1 status
ls .lake/packages/mathlib/Mathlib/CategoryTheory/Enriched/Limits/ 2>/dev/null | grep -E "Cotensor|Weighted"
ls .lake/packages/mathlib/Mathlib/CategoryTheory/Enriched/Monad/ 2>/dev/null
ls .lake/packages/mathlib/Mathlib/CategoryTheory/Enriched/Power.lean 2>/dev/null

# Check Phase 2 status
grep -n "sorry" formal/SSBX/Foundation/Doctrine/EnrichedLawvereTheory.lean

# Check Phase 3 status
ls formal/SSBX/Foundation/Doctrine/Instance/HilbertEnriched*.lean 2>/dev/null

# Check Phase 4 status
ls formal/SSBX/Foundation/Doctrine/T_GUT_Enriched*.lean 2>/dev/null
```

Decision tree:
- If Phase 4 files exist + 0 sorry → Verify acceptance criteria §7.4 + §10
- Else if Phase 3 files exist → Verify Phase 3 done, pick up Phase 4
- Else if Phase 2 file has 0 sorry → Verify Phase 2 done, pick up Phase 3
- Else if Phase 1 files in Mathlib → Pick up Phase 2
- Else → Pick up Phase 1

### C.3 Watch out for

- **Don't introduce axioms** to close stubborn sorries — see [[no-axiom-for-zero-sorry]]; PR #51 incident was exactly this
- **Don't weaken theorems** to fit easier proofs — see [[dont-drop-theorems]]
- **Don't migrate existing 4 substrates** to enriched form by default — keep parallel
- **Don't break universal_sayability** at T_GUT.lean:691 — the categorical version stays
- **Don't reopen RH** as goal — [[e1-rtower-rh-closed]] specifically closes this; the enriched framework doesn't help RH

### C.4 When you're stuck

- **Mathlib categorical API questions**: check zulip `#category theory` channel
- **Power 1999 proof details**: read the paper directly (TAC vol 6 no 7, freely accessible)
- **SSBX framework history**: read MEMORY.md + the linked project memory files
- **This plan's intent**: ask user; or read §1.4 + §10

### C.5 Completion check

When you think you're done, run §10's checklist. ALL 8 must be ✓ for "done done". If any are ⊙ (stretch), document why.

---

**End of Plan.**

**Last updated**: 2026-05-18

**Plan size**: ~700 lines of Markdown.

**Total work scope**: 2850-5350 LOC across 4 phases, ~9-15 months calendar time.

**Recommended kickoff action**: do not start until user has reviewed this plan and committed resources (they may revise scope after reading).
