/-
# Foundation.Closure.PhiOperator — Knaster-Tarski lfp identification of D1

**Skeleton** (per `docs-next/00_start/lawvere-identification.md` v0.4 §§4.5, 5.1-5.4).

## Doctrinal anchor

The position paper `lawvere-identification.md` (v0.4) establishes:

> **R-tower closure (D1 ⟷ P1-P7) IS the Knaster-Tarski least fixed point
> of the requirements-extraction operator Φ on the lattice 𝒜 of
> articulation candidates over the self-internalising sub-class
> {R N : N ∈ ℕ} ⊆ R-Vec, where P5 (hom-closure) is the structural
> condition built into 𝒜's consistency requirements that enables Φ to
> be well-defined.**
>
> Equivalently: **D1 = lfp(Φ)**.

This file lays down the **Lean skeleton** for that identification:

* `PProperty`     — the 8 atomic P-properties (P1, P2, P3, P4, P5, P6, P7a, P7b)
* `ArticulationCandidate` — Def 4.5.1 (carrier-class + morphism-class + P-set
                            with consistency conditions, including **bridge
                            conditions** connecting pset membership to
                            carrier/morphism structure)
* `instance : CompleteLattice ArticulationCandidate` — Prop 4.5.2
* `Phi : ArticulationCandidate →o ArticulationCandidate` — Def 4.5.3 + Thm 4.5.5
* `D1 : ArticulationCandidate := OrderHom.lfp Phi` — Thm 5.2.1
* `witnessesP` — per-`PProperty` structural witness, now data-dependent

## Scope

* This is a **partially-discharged skeleton** (v0.5 refinement of v0.4).
  Of the original 8 proof-level `sorry`s, **5 are discharged in v0.4**:
    1. `botCandidate.comp_closed` (unit-propagation at `LinHom = Unit`)
    2. `instCompleteLattice` (constructed via `completeLatticeOfInf`)
    3. `phi_monotone` (Thm 4.5.5) — via `Finset.union_subset_union`
    4. `D1_is_fixed_point` (Prop 5.3.1) — via `OrderHom.map_lfp`
    5. `D1_is_minimum_P_satisfier` (Prop 5.3.2) — via `OrderHom.lfp_le`
* This v0.5 refinement:
    - Refines `witnessesP` to depend on (carrier, morphism) per-`PProperty`
      (per §4.5.3 of the position paper)
    - Adds **three new bridge conditions** to `ArticulationCandidate`:
      `p3_implies_R1`, `p4_implies_unbounded`, `p6_implies_R2`,
      `p7b_implies_R4` (tying pset membership to carrier structure)
    - Maintains all 5 previously discharged proofs
    - Re-formulates the 3 structural-shape theorems
      (`D1_carrier_eq_all_RN`, `D1_morphism_eq_all`, `D1_pset_eq_all`) as
      **conditional theorems** that are provably true given the bridges;
      the unconditional forms remain stated as **doctrinal targets**.
* `lake build` succeeds with sorry warnings only.
* The architecture is the *Mathlib-compatible* one promised by
  §5.9 of the position paper: `OrderHom.lfp` is applied directly.

## Why `D1.carrier = Set.univ` cannot be proved unconditionally

Per Def 4.5.3, `Φ(D)` leaves carrier and morphism unchanged and only
augments `pset`.  Hence for any `D ∈ 𝒜` with empty pset and carrier
{0} (e.g., `botCandidate`), `Φ(D)` has `pset ⊆ witnessedSet(C, M)`.
If `witnessedSet(C, M) ⊆ D.pset`, then `D` is Φ-pre-fixed, so
`D1 ≤ D`, hence `D1.carrier ⊆ {0} ≠ Set.univ`.

To get `D1.carrier = Set.univ` as in Prop 5.3.4 of the position paper,
one needs **either** (a) a different operator Φ' that ALSO grows the
carrier when newly-witnessed P's require it (departing from Def 4.5.3),
or (b) a consistency condition that EVERY candidate must have unbounded
carrier (which makes `botCandidate` inconsistent).  Neither move is
taken in v0.4 of the position paper.

We instead state and prove the **strongest conditional form** that
follows from the bridges: if `p4 ∈ D.pset`, then `D.carrier` is
unbounded (and similarly for `p6 → R 2 ∈ C`, `p7b → R 4 ∈ C`).  These
are immediate from the bridges and yield `D1.carrier` containment as
soon as one establishes the corresponding `D1.pset` membership facts.

## Relation to existing files

* `Foundation/R/ClaimZ.lean` — defines `D1Articulation` and `PClosure` at
  the **interface level** (Prop-valued records).  Future work: bridging
  theorems `D1_bridges_D1Articulation` and `D1_PSet_eq_PClosure`.
* `Foundation/R/ClaimZ/Analytic.lean` — supplies `D1_implies_Phase1Closure_F2`,
  which is the **analytic direction** of §5.4 at δ = Bool.
* `Foundation/R/UniquenessGeneral.lean` — supplies `T5_general`, which is
  the **synthetic direction** of §5.4 polymorphically in δ.

## Estimated Lean-formalization effort (per §5.9)

The position paper §5.9 estimates **~2-4 weeks for skeleton, ~6-8 weeks
for completing all theorems with 0 sorry**.  This file occupies the
skeleton slot.
-/

import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

namespace SSBX.Foundation.Closure

universe u

/-! ## § 1 The 8 atomic P-properties

Per `wen-substrate.md` v1.2 §2.1-§2.7 and `lawvere-identification.md` v0.2 §4.5.
P7 splits into P7a (aspect alphabet at R 3) and P7b (atomic operations at R 4),
giving 8 atomic properties total.
-/

/-- The 8 atomic P-properties of R-tower closure. -/
inductive PProperty : Type
  | p1   -- minimum non-trivial structure (binary distinction → F₂)
  | p2   -- composition (direct sum / coproduct)
  | p3   -- relation layers (bilinear / quadratic, 3-layer)
  | p4   -- scale (squaring tower, self-similarity)
  | p5   -- self-reference (Hom-as-content)
  | p6   -- modality (4-modality carrier at R 2, V₄)
  | p7a  -- aspect alphabet (8 trigrams at R 3, zong involution)
  | p7b  -- atomic operations (16 ops at R 4, M_2(F_2))
  deriving DecidableEq, Repr

namespace PProperty

/-- Enumeration as a list. -/
def all : List PProperty :=
  [.p1, .p2, .p3, .p4, .p5, .p6, .p7a, .p7b]

end PProperty

/-! ## § 2 Linear morphisms (abstract surrogate)

A `LinHom N M` is the abstract surrogate for an F₂-linear map
`R N → R M` (or more generally a δ-linear map for any δ).  This file
treats it as an opaque type with the appropriate consistency
operations.  Concrete instantiations bridge this to
`Foundation/R/Basic.lean` linear maps.

For the skeleton we model `LinHom` as an arbitrary type parameter
(`Type u`); future work can specialize to the F₂ or polymorphic δ
realisation.
-/

/-- Abstract surrogate for the type of linear morphisms `R N → R M`.
    Concrete instantiations (e.g., F₂-Boolean) provide an embedding
    into actual `LinearMap`s.

    For the skeleton we use `Unit` as the placeholder carrier — the
    composition / identity operations below are trivial.  Future
    work specializes `LinHom` to the concrete F₂-linear or
    polymorphic-δ-linear realisation. -/
def LinHom (_N _M : ℕ) : Type := Unit

instance (N M : ℕ) : Inhabited (LinHom N M) := ⟨((): Unit)⟩

/-- Composition of linear morphisms (abstract; trivial at the
    placeholder `Unit`-carrier). -/
def LinHom.comp {N M K : ℕ} (_g : LinHom M K) (_f : LinHom N M) : LinHom N K := ()

/-- Identity linear morphism on `R N` (abstract; trivial at the
    placeholder `Unit`-carrier). -/
def LinHom.id (_N : ℕ) : LinHom N N := ()

/-! ## § 3 Articulation Candidate (Def 4.5.1)

An articulation candidate over R-Vec is a triple `(C_D, M_D, P_D)` with:

* `C_D ⊆ Obj(R-Vec)` — the carrier-class, here represented as `Set ℕ`
  (the set of N's such that `R N ∈ C_D`).
* `M_D ⊆ ⋃ LinHom(N, M)` — the morphism-class, here represented as
  `(N M : ℕ) → Set (LinHom N M)`.
* `P_D ⊆ {P1, ..., P7b}` — the satisfied-property-set, here represented
  as `Finset PProperty`.

with consistency conditions:
* Product closure: `R N, R M ∈ C_D ⟹ R(N+M) ∈ C_D`
* Hom closure:     `R N, R M ∈ C_D ⟹ R(N·M) ∈ C_D`  (= P5)
* Composition closure: `f ∈ M_D, g ∈ M_D ⟹ g∘f ∈ M_D`
* Identity inclusion:  `R N ∈ C_D ⟹ id_{R N} ∈ M_D`
-/

/-- **Def 4.5.1** (Articulation Candidate) of
    `docs-next/00_start/lawvere-identification.md` §4.5, v0.4
    refinement.

    A triple `(carrier, morphism, pset)` carrying the consistency
    conditions of an articulation candidate over the self-internalising
    sub-class `{R N : N ∈ ℕ}` of R-Vec.

    Beyond the 4 core consistency conditions of Def 4.5.1, this v0.5
    refinement adds 4 **bridge conditions** tying pset membership to
    the (carrier, morphism) structure.  These bridges are what makes
    `witnessesP` a well-typed indicator of structural witness, and
    they propagate properly through `topCandidate`, `botCandidate`,
    and `sInfFun`. -/
structure ArticulationCandidate : Type 1 where
  /-- C_D ⊆ Obj(R-Vec): the set of N such that R N is in the carrier-class. -/
  carrier : Set ℕ
  /-- M_D: the morphism-class, indexed by source/target dimensions. -/
  morphism : (N M : ℕ) → Set (LinHom N M)
  /-- P_D ⊆ {P1, ..., P7b}: the satisfied-property-set. -/
  pset : Finset PProperty
  /-- **Product closure** (Def 4.5.1): R N, R M ∈ C_D ⟹ R(N+M) ∈ C_D. -/
  prod_closed : ∀ N M, N ∈ carrier → M ∈ carrier → (N + M) ∈ carrier
  /-- **Hom closure** (Def 4.5.1, = P5): R N, R M ∈ C_D ⟹ R(N·M) ∈ C_D. -/
  hom_closed : ∀ N M, N ∈ carrier → M ∈ carrier → (N * M) ∈ carrier
  /-- **Composition closure** (Def 4.5.1): M_D is closed under composition. -/
  comp_closed : ∀ {N M K}, ∀ f ∈ morphism N M, ∀ g ∈ morphism M K,
      g.comp f ∈ morphism N K
  /-- **Identity inclusion** (Def 4.5.1): R N ∈ C_D ⟹ id_{R N} ∈ M_D. -/
  id_in : ∀ N, N ∈ carrier → LinHom.id N ∈ morphism N N
  /-- **Bridge (P3 → R 1)** (v0.5): if P3 (relation layers) is claimed,
      then the carrier contains some R N for N ≥ 1 (in particular it is
      not just `{0}`).  Simplified placeholder for "M contains a full
      bilinear classification". -/
  p3_implies_R1 : .p3 ∈ pset → ∃ N ∈ carrier, N ≥ 1
  /-- **Bridge (P4 → unbounded)** (v0.5): if P4 (scale / unbounded
      recursion) is claimed, then the carrier is unbounded. -/
  p4_implies_unbounded : .p4 ∈ pset → ∀ N : ℕ, ∃ M ∈ carrier, M > N
  /-- **Bridge (P6 → R 2)** (v0.5): if P6 (4-fold modality / V₄) is
      claimed, then R 2 is in the carrier.  Simplified placeholder
      for "M contains V₄-action morphisms". -/
  p6_implies_R2 : .p6 ∈ pset → 2 ∈ carrier
  /-- **Bridge (P7b → R 4)** (v0.5): if P7b (Wedderburn anchor on
      R 4) is claimed, then R 4 is in the carrier.  Simplified
      placeholder for "M contains canonical ring structure on R 4". -/
  p7b_implies_R4 : .p7b ∈ pset → 4 ∈ carrier

namespace ArticulationCandidate

/-! ### § 3.1 The intended order on 𝒜 (Prop 4.5.2)

`D ≤ D'` iff `C_D ⊆ C_{D'} ∧ M_D ⊆ M_{D'} ∧ P_D ⊆ P_{D'}`.

This is the *semantic* description of the order.  We register it as
a definition (not yet an instance) here; the `CompleteLattice`
instance below is `sorry`-declared and acts as the source of all
order instances (`LE`, `Preorder`, `PartialOrder`).  When the
`CompleteLattice` `sorry` is discharged, its `le` field must
unfold to `IntendedLE.le` (i.e., `D.carrier ⊆ ...`).
-/

/-- **Intended order on 𝒜** (Prop 4.5.2 of `lawvere-identification.md`
    §4.5): componentwise inclusion.  The `CompleteLattice` instance
    below must be defined so that `≤ = IntendedLE.le`. -/
def IntendedLE (D D' : ArticulationCandidate) : Prop :=
  D.carrier ⊆ D'.carrier ∧
  (∀ N M, D.morphism N M ⊆ D'.morphism N M) ∧
  D.pset ⊆ D'.pset

/-! ### § 3.2 The complete lattice structure (Prop 4.5.2)

`𝒜` is a complete lattice with:
- Top: `⊤ = (Set.univ, all morphisms, {P1,...,P7b})`
- Bottom: `⊥ = ({0}, {id_{R 0}}, ∅)` (smallest consistent candidate)
- Joins: componentwise union, take closure under prod/hom/comp
- Meets: componentwise intersection, take largest sub-triple

Per `lawvere-identification.md` §4.5: "The complete-lattice structure is
non-trivial; meets in particular require careful definition because
component-wise intersection may not preserve hom-closure."

For the skeleton, we provide the *data* of the lattice operations and
`sorry` the lattice laws.  Future work: discharge each `sorry` (rough
estimate: ~2-3 weeks for the full instance).
-/

/-- Top element of 𝒜: full carrier, all morphisms, all P's. -/
def topCandidate : ArticulationCandidate where
  carrier := Set.univ
  morphism := fun _ _ => Set.univ
  pset := PProperty.all.toFinset
  prod_closed := fun _ _ _ _ => Set.mem_univ _
  hom_closed := fun _ _ _ _ => Set.mem_univ _
  comp_closed := fun _ _ _ _ => Set.mem_univ _
  id_in := fun _ _ => Set.mem_univ _
  p3_implies_R1 := fun _ => ⟨1, Set.mem_univ _, le_refl 1⟩
  p4_implies_unbounded := fun _ N => ⟨N + 1, Set.mem_univ _, Nat.lt_succ_self N⟩
  p6_implies_R2 := fun _ => Set.mem_univ _
  p7b_implies_R4 := fun _ => Set.mem_univ _

/-- Bottom element of 𝒜: {0} with id_{R 0} and empty P-set.

    Per Def 4.5.1 of the position paper, this is the smallest consistent
    candidate: `({R 0}, {id_{R 0}}, ∅)`. -/
def botCandidate : ArticulationCandidate where
  carrier := {0}
  morphism := fun N M =>
    if h : N = 0 ∧ M = 0 then {h.1 ▸ h.2 ▸ LinHom.id 0} else ∅
  pset := ∅
  prod_closed := by
    intro N M hN hM
    simp only [Set.mem_singleton_iff] at hN hM ⊢
    omega
  hom_closed := by
    intro N M hN hM
    simp only [Set.mem_singleton_iff] at hN hM ⊢
    subst hN; subst hM; rfl
  comp_closed := by
    -- All LinHom values are unit (placeholder carrier); composition
    -- is trivial.  The "morphism" set is only non-empty when
    -- N = M = 0 (for f) and M = K = 0 (for g), so N = K = 0 and
    -- the goal lives in `morphism 0 0 = {LinHom.id 0}`.
    intro N M K f hf g hg
    -- Extract N = 0 ∧ M = 0 from hf via the if-then-else
    by_cases hfNM : N = 0 ∧ M = 0
    · -- Symmetrically for g: M = 0 ∧ K = 0
      by_cases hgMK : M = 0 ∧ K = 0
      · obtain ⟨hN0, _hM0⟩ := hfNM
        obtain ⟨_hM0', hK0⟩ := hgMK
        -- Goal: g.comp f ∈ (if h : N = 0 ∧ K = 0 then ... else ∅)
        subst hN0; subst hK0
        -- Now N = K = 0
        simp only [and_self, dif_pos]
        rfl
      · -- g ∈ ∅ contradiction
        simp only [hgMK, dif_neg, not_false_eq_true, Set.mem_empty_iff_false] at hg
    · -- f ∈ ∅ contradiction
      simp only [hfNM, dif_neg, not_false_eq_true, Set.mem_empty_iff_false] at hf
  id_in := by
    intro N hN
    simp only [Set.mem_singleton_iff] at hN
    subst hN
    -- N = 0: LinHom.id 0 is in the singleton {LinHom.id 0} for (0, 0)
    -- The `if h : 0 = 0 ∧ 0 = 0 then {...}` branch evaluates to `{()}`
    -- and `LinHom.id 0 = ()`, so `() ∈ {()}` by rfl.
    simp only [and_self, dif_pos]
    rfl
  p3_implies_R1 := by
    intro h; simp at h
  p4_implies_unbounded := by
    intro h; simp at h
  p6_implies_R2 := by
    intro h; simp at h
  p7b_implies_R4 := by
    intro h; simp at h

/-! ### § 3.2bis Extensionality and the partial order

We register `ArticulationCandidate` extensionality, the `LE`
relation from `IntendedLE`, and the `PartialOrder` instance.  These
are stepping stones to the full `CompleteLattice` instance below.
-/

/-- Extensionality: two articulation candidates are equal iff their
    three data components agree.  The four consistency-condition
    fields are propositional and follow automatically. -/
@[ext]
theorem ext {D D' : ArticulationCandidate}
    (hC : D.carrier = D'.carrier)
    (hM : D.morphism = D'.morphism)
    (hP : D.pset = D'.pset) : D = D' := by
  cases D; cases D'
  subst hC; subst hM; subst hP
  rfl

/-- `LE` instance via `IntendedLE`: componentwise inclusion. -/
instance : LE ArticulationCandidate := ⟨IntendedLE⟩

/-- Unfolding lemma: `D ≤ D'` reduces to the three componentwise
    inclusions of `IntendedLE`. -/
theorem le_def (D D' : ArticulationCandidate) :
    D ≤ D' ↔
      D.carrier ⊆ D'.carrier ∧
      (∀ N M, D.morphism N M ⊆ D'.morphism N M) ∧
      D.pset ⊆ D'.pset := Iff.rfl

/-- `PartialOrder` instance: reflexivity, transitivity, antisymmetry
    follow componentwise from `Set.Subset.refl/trans/antisymm` and
    `Finset.Subset` antisymmetry. -/
instance : PartialOrder ArticulationCandidate where
  le := (· ≤ ·)
  le_refl D := ⟨Set.Subset.rfl, fun _ _ => Set.Subset.rfl, Finset.Subset.rfl⟩
  le_trans D₁ D₂ D₃ h₁₂ h₂₃ :=
    ⟨Set.Subset.trans h₁₂.1 h₂₃.1,
     fun N M => Set.Subset.trans (h₁₂.2.1 N M) (h₂₃.2.1 N M),
     Finset.Subset.trans h₁₂.2.2 h₂₃.2.2⟩
  le_antisymm D D' h h' := by
    apply ext
    · exact Set.Subset.antisymm h.1 h'.1
    · funext N M
      exact Set.Subset.antisymm (h.2.1 N M) (h'.2.1 N M)
    · exact Finset.Subset.antisymm h.2.2 h'.2.2

/-! ### § 3.2ter The `InfSet` instance via componentwise intersection

For a set `s : Set ArticulationCandidate`, define `sInf s` as:
* carrier = `{N | ∀ D ∈ s, N ∈ D.carrier}` (the intersection of carriers)
* morphism = `{f | ∀ D ∈ s, f ∈ D.morphism N M}` for each (N, M)
* pset = filter of `PProperty.all.toFinset` by both "∀ D ∈ s, p ∈ D.pset"
        AND "p's bridge condition is satisfied by sInf's own carrier"

The bridge filter is required for the result to satisfy
`ArticulationCandidate`'s bridge fields when, e.g., the intersection
of unbounded carriers is *not* unbounded.

The four core consistency conditions (prod/hom/comp/id) transfer through
universal quantification.  The four bridge conditions hold by construction
because of the additional filter step.

When `s = ∅` this gives `topCandidate` (universal carrier, all
morphisms, all P's); when `s` is non-empty the intersection is the
largest candidate contained in every element of `s`. -/

/-- The "structural bridge" predicate at a carrier `C`: does `C`
    independently satisfy the bridge condition required if `p` is in
    pset?

    Each bridge is monotone in `C`: if `C ⊆ C'` and `bridgeHolds C p`,
    then `bridgeHolds C' p`. -/
def bridgeHolds (carrier : Set ℕ) : PProperty → Prop
  | .p3 => ∃ N ∈ carrier, N ≥ 1
  | .p4 => ∀ N : ℕ, ∃ M ∈ carrier, M > N
  | .p6 => 2 ∈ carrier
  | .p7b => 4 ∈ carrier
  | _ => True  -- no bridge constraint for p1, p2, p5, p7a

/-- Monotonicity of `bridgeHolds` in the carrier. -/
theorem bridgeHolds_mono {C C' : Set ℕ} (hC : C ⊆ C') (p : PProperty) :
    bridgeHolds C p → bridgeHolds C' p := by
  intro h
  cases p
  · exact h  -- p1: True
  · exact h  -- p2: True
  · -- p3: ∃ N ∈ C, N ≥ 1
    obtain ⟨N, hN, hN1⟩ := h
    exact ⟨N, hC hN, hN1⟩
  · -- p4: ∀ N, ∃ M ∈ C, M > N
    intro N
    obtain ⟨M, hM, hMN⟩ := h N
    exact ⟨M, hC hM, hMN⟩
  · exact h  -- p5: True
  · -- p6: 2 ∈ C
    exact hC h
  · exact h  -- p7a: True
  · -- p7b: 4 ∈ C
    exact hC h

/-- The filter predicate for `sInfFun.pset`.  Bundled as an
    abbreviation so that the same classical-decidability instance
    is used in the construction and in the bridge proofs. -/
def sInfPsetPred (s : Set ArticulationCandidate) (p : PProperty) : Prop :=
  (∀ D ∈ s, p ∈ D.pset) ∧ bridgeHolds {N | ∀ D ∈ s, N ∈ D.carrier} p

noncomputable instance (s : Set ArticulationCandidate) :
    DecidablePred (sInfPsetPred s) :=
  fun _ => Classical.propDecidable _

/-- Componentwise intersection — the GLB of a set of articulation
    candidates.  Uses classical choice for the P-set predicate's
    decidability (membership in `s` is not algorithmically decidable
    for arbitrary `s : Set ArticulationCandidate`). -/
noncomputable def sInfFun (s : Set ArticulationCandidate) : ArticulationCandidate where
  carrier := {N | ∀ D ∈ s, N ∈ D.carrier}
  morphism := fun N M => {f | ∀ D ∈ s, f ∈ D.morphism N M}
  pset := (PProperty.all.toFinset).filter (sInfPsetPred s)
  prod_closed := by
    intro N M hN hM D hD
    exact D.prod_closed N M (hN D hD) (hM D hD)
  hom_closed := by
    intro N M hN hM D hD
    exact D.hom_closed N M (hN D hD) (hM D hD)
  comp_closed := by
    intro N M K f hf g hg D hD
    exact D.comp_closed f (hf D hD) g (hg D hD)
  id_in := by
    intro N hN D hD
    exact D.id_in N (hN D hD)
  p3_implies_R1 := by
    intro h
    rw [Finset.mem_filter] at h
    exact h.2.2
  p4_implies_unbounded := by
    intro h
    rw [Finset.mem_filter] at h
    exact h.2.2
  p6_implies_R2 := by
    intro h
    rw [Finset.mem_filter] at h
    exact h.2.2
  p7b_implies_R4 := by
    intro h
    rw [Finset.mem_filter] at h
    exact h.2.2

noncomputable instance : InfSet ArticulationCandidate := ⟨sInfFun⟩

/-- Unfolding lemma: membership in `(sInf s).carrier` is universal
    quantification over `s`. -/
@[simp]
theorem sInf_carrier (s : Set ArticulationCandidate) :
    (sInf s).carrier = {N | ∀ D ∈ s, N ∈ D.carrier} := rfl

/-- Unfolding lemma: morphism components of `sInf s`. -/
@[simp]
theorem sInf_morphism (s : Set ArticulationCandidate) (N M : ℕ) :
    (sInf s).morphism N M = {f | ∀ D ∈ s, f ∈ D.morphism N M} := rfl

/-- Membership in `(sInf s).pset`: a P-property is in the meet iff
    (a) it is in every `D.pset` for `D ∈ s`, AND (b) the bridge
    condition for `p` is satisfied by the intersection carrier. -/
theorem mem_sInf_pset {s : Set ArticulationCandidate} {p : PProperty} :
    p ∈ (sInf s).pset ↔ sInfPsetPred s p := by
  show p ∈ ((PProperty.all.toFinset).filter (sInfPsetPred s)) ↔ _
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  -- Every PProperty is in `PProperty.all.toFinset`
  cases p <;> decide

/-- Bridge holds at a carrier of a single candidate `D` whenever `p ∈ D.pset`. -/
theorem bridgeHolds_of_pset_mem {D : ArticulationCandidate} {p : PProperty}
    (h : p ∈ D.pset) : bridgeHolds D.carrier p := by
  cases p
  · exact trivial            -- p1: True
  · exact trivial            -- p2: True
  · exact D.p3_implies_R1 h  -- p3
  · exact D.p4_implies_unbounded h  -- p4
  · exact trivial            -- p5: True
  · exact D.p6_implies_R2 h  -- p6
  · exact trivial            -- p7a: True
  · exact D.p7b_implies_R4 h  -- p7b

/-- `sInf` is the greatest lower bound: for every `s`, `sInf s` is in
    the lower bounds of `s` and any other lower bound is `≤ sInf s`. -/
theorem isGLB_sInf' (s : Set ArticulationCandidate) : IsGLB s (sInf s) := by
  refine ⟨?_, ?_⟩
  · -- sInf s is a lower bound
    intro D hD
    refine ⟨?_, ?_, ?_⟩
    · intro N hN; exact hN D hD
    · intro N M f hf; exact hf D hD
    · -- (sInf s).pset ⊆ D.pset
      intro p hp
      exact ((mem_sInf_pset.mp hp).1) D hD
  · -- any lower bound is ≤ sInf s
    intro E hE
    refine ⟨?_, ?_, ?_⟩
    · -- E.carrier ⊆ (sInf s).carrier
      intro N hN D hD
      exact (hE hD).1 hN
    · -- E.morphism ⊆ (sInf s).morphism (component-wise)
      intro N M f hf D hD
      exact (hE hD).2.1 N M hf
    · -- E.pset ⊆ (sInf s).pset:
      -- if p ∈ E.pset, then p ∈ D.pset for all D ∈ s (since E ≤ D),
      -- and the bridge for p holds on E.carrier (by E's own bridge field),
      -- and E.carrier ⊆ sInf.carrier, so bridge holds on sInf.carrier.
      intro p hp
      apply mem_sInf_pset.mpr
      refine ⟨fun D hD => (hE hD).2.2 hp, ?_⟩
      apply bridgeHolds_mono ?_ p (bridgeHolds_of_pset_mem hp)
      -- Goal: E.carrier ⊆ sInf.carrier
      intro N hN D hD
      exact (hE hD).1 hN

/-- **Prop 4.5.2** (𝒜 is a complete lattice) of
    `docs-next/00_start/lawvere-identification.md` §4.5.

    Built via `completeLatticeOfInf` from the componentwise-intersection
    `sInf` and its GLB property.  The constructor derives the
    remaining lattice operations (sup, inf, sSup, top, bot) from
    `sInf` of appropriate sets.

    Per the position paper: "The complete-lattice structure is
    non-trivial; meets in particular require careful definition
    because component-wise intersection may not preserve hom-closure."
    For our concrete definition with universally-quantified
    consistency conditions, intersection DOES preserve hom-closure
    (and prod-closure, comp-closure, id-inclusion) — see
    `sInfFun.{prod_closed,hom_closed,comp_closed,id_in}` above.

    The result is a single `CompleteLattice` instance whose `≤`
    definitionally unfolds to `IntendedLE`. -/
noncomputable instance instCompleteLattice : CompleteLattice ArticulationCandidate :=
  completeLatticeOfInf ArticulationCandidate isGLB_sInf'

/-! ### § 3.3 The Φ operator (Def 4.5.3, Thm 4.5.5)

`Φ(D) = (C_D, M_D, P_D ∪ {P_i : structurally witnessed by (C, M)})`.

Concretely (per §4.5):
- P1 if M_D contains ≥ 2 distinct morphisms
- P2 if M_D contains composition pairs
- P3 if C_D contains R N and M_D contains bilinear classifications
- P4 if C_D contains R N for unbounded N
- P5 if C_D is hom-closed — **automatic from consistency** (Obs 4.5.4)
- P6 if M_D contains V₄-action morphisms
- P7a if M_D contains the alphabet-of-atoms
- P7b if M_D contains the canonical ring on R 4

Thm 4.5.5: Φ is monotone.
-/

/-- Per-`PProperty` structural witness predicate.

    Per §4.5.3 of `lawvere-identification.md` v0.4, each P_i is
    "structurally witnessed by (C, M)" iff a specific positive
    existential condition on (C, M) holds.  These conditions are
    deliberately monotone in (C, M) (more structure ⟹ at least
    as many witnesses), which gives Φ its monotonicity (Thm 4.5.5).

    For the v0.5 placeholder LinHom = Unit, P1 and P7a (which require
    distinct morphisms) are unwitnessable — only one morphism exists
    per (N, M) under the Unit-carrier.  This is acknowledged and
    documented as Open Problem #3.

    | P_i  | Witness condition                                                |
    |------|------------------------------------------------------------------|
    | P1   | M contains ≥ 2 distinct morphisms (unwitnessable at LinHom=Unit) |
    | P2   | always (vacuous at LinHom=Unit; comp_closed is consistency)      |
    | P3   | C contains R N for some N ≥ 1                                    |
    | P4   | C is unbounded (∀ N, ∃ M ∈ C, M > N)                             |
    | P5   | always (Obs 4.5.4 — hom-closure built into 𝒜)                   |
    | P6   | R 2 ∈ C (placeholder for "M contains V₄-action")                 |
    | P7a  | M contains ≥ 2 distinct morphisms (= P1; unwitnessable)          |
    | P7b  | R 4 ∈ C (placeholder for "M contains canonical ring on R 4")     | -/
def witnessesP (carrier : Set ℕ) (morphism : (N M : ℕ) → Set (LinHom N M))
    (p : PProperty) : Prop :=
  match p with
  | .p1  => ∃ N M, ∃ f g : LinHom N M, f ∈ morphism N M ∧ g ∈ morphism N M ∧ f ≠ g
  | .p2  => True       -- vacuous at LinHom = Unit
  | .p3  => ∃ N ∈ carrier, N ≥ 1
  | .p4  => ∀ N : ℕ, ∃ M ∈ carrier, M > N
  | .p5  => True       -- Obs 4.5.4: hom-closure is automatic
  | .p6  => 2 ∈ carrier
  | .p7a => ∃ N M, ∃ f g : LinHom N M, f ∈ morphism N M ∧ g ∈ morphism N M ∧ f ≠ g
  | .p7b => 4 ∈ carrier

/-- The set of P-properties structurally witnessed by `(C, M)`.

    Uses classical decidability of `witnessesP`. -/
noncomputable def witnessedSet (carrier : Set ℕ)
    (morphism : (N M : ℕ) → Set (LinHom N M)) : Finset PProperty :=
  haveI : DecidablePred (fun p => witnessesP carrier morphism p) :=
    fun _ => Classical.propDecidable _
  PProperty.all.toFinset.filter (fun p => witnessesP carrier morphism p)

/-- Membership in `witnessedSet`: `p ∈ witnessedSet C M ↔ witnessesP C M p`. -/
theorem mem_witnessedSet {carrier : Set ℕ}
    {morphism : (N M : ℕ) → Set (LinHom N M)} {p : PProperty} :
    p ∈ witnessedSet carrier morphism ↔ witnessesP carrier morphism p := by
  classical
  show p ∈ (PProperty.all.toFinset.filter
    (fun p => witnessesP carrier morphism p)) ↔ _
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  cases p <;> decide

/-- **Def 4.5.3** (Φ: Requirements Extraction) of
    `docs-next/00_start/lawvere-identification.md` §4.5.

    `Φ(D) = (C_D, M_D, P_D ∪ {P_i : structurally witnessed})`.

    Φ leaves the carrier and morphism class unchanged; it augments the
    P-set with all P_i whose structural witnesses are present in
    `(C, M)`.  The bridge fields propagate via case-split: a newly
    added P_i was either already in `D.pset` (use `D`'s bridge) or
    newly witnessed (use `witnessesP` directly). -/
noncomputable def phiFun (D : ArticulationCandidate) : ArticulationCandidate where
  carrier := D.carrier
  morphism := D.morphism
  pset := D.pset ∪ witnessedSet D.carrier D.morphism
  prod_closed := D.prod_closed
  hom_closed := D.hom_closed
  comp_closed := D.comp_closed
  id_in := D.id_in
  p3_implies_R1 := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact D.p3_implies_R1 h
    · -- p3 ∈ witnessedSet ⟹ witnessesP D.carrier D.morphism .p3
      exact (mem_witnessedSet.mp h : witnessesP D.carrier D.morphism .p3)
  p4_implies_unbounded := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact D.p4_implies_unbounded h
    · exact (mem_witnessedSet.mp h : witnessesP D.carrier D.morphism .p4)
  p6_implies_R2 := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact D.p6_implies_R2 h
    · exact (mem_witnessedSet.mp h : witnessesP D.carrier D.morphism .p6)
  p7b_implies_R4 := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact D.p7b_implies_R4 h
    · exact (mem_witnessedSet.mp h : witnessesP D.carrier D.morphism .p7b)

/-- **Monotonicity of `witnessesP` in the data** (per-`PProperty`).

    If `C ⊆ C'` and `M ⊆ M'` componentwise, then
    `witnessesP C M p → witnessesP C' M' p`.

    Each case is a positive existential / universal-existential over
    `(C, M)`, hence monotone. -/
theorem witnessesP_mono
    {C C' : Set ℕ} {M : (N K : ℕ) → Set (LinHom N K)}
    {M' : (N K : ℕ) → Set (LinHom N K)}
    (hC : C ⊆ C') (hM : ∀ N K, M N K ⊆ M' N K)
    (p : PProperty) :
    witnessesP C M p → witnessesP C' M' p := by
  intro h
  cases p
  · -- p1: ∃ N M f g, f, g ∈ M, f ≠ g
    obtain ⟨N, K, f, g, hf, hg, hfg⟩ := h
    exact ⟨N, K, f, g, hM N K hf, hM N K hg, hfg⟩
  · exact h  -- p2: True
  · -- p3: ∃ N ∈ C, N ≥ 1
    obtain ⟨N, hN, hN1⟩ := h
    exact ⟨N, hC hN, hN1⟩
  · -- p4: ∀ N, ∃ M ∈ C, M > N
    intro N
    obtain ⟨K, hK, hKN⟩ := h N
    exact ⟨K, hC hK, hKN⟩
  · exact h  -- p5: True
  · -- p6: 2 ∈ C
    exact hC h
  · -- p7a: ∃ N M f g, f, g ∈ M, f ≠ g
    obtain ⟨N, K, f, g, hf, hg, hfg⟩ := h
    exact ⟨N, K, f, g, hM N K hf, hM N K hg, hfg⟩
  · -- p7b: 4 ∈ C
    exact hC h

/-- **Monotonicity of `witnessedSet`** in the data. -/
theorem witnessedSet_mono
    {C C' : Set ℕ} {M : (N K : ℕ) → Set (LinHom N K)}
    {M' : (N K : ℕ) → Set (LinHom N K)}
    (hC : C ⊆ C') (hM : ∀ N K, M N K ⊆ M' N K) :
    witnessedSet C M ⊆ witnessedSet C' M' := by
  classical
  intro p hp
  rw [mem_witnessedSet] at hp ⊢
  exact witnessesP_mono hC hM p hp

/-- **Thm 4.5.5** (Φ is monotone) of
    `docs-next/00_start/lawvere-identification.md` §4.5.

    *Proof sketch* (per the paper): carrier and morphism are unchanged
    by Φ.  P-set augmentation depends monotonically on (C, M): more
    structure means at least as many structural witnesses.

    *Lean proof.*  Unfold `phiFun` and the `≤` (= `IntendedLE`)
    relation.  Carrier and morphism inclusions are direct.  For
    psets, use `Finset.union_subset_union` together with
    `witnessedSet_mono`. -/
theorem phi_monotone : Monotone phiFun := by
  intro D D' hDD'
  refine ⟨?_, ?_, ?_⟩
  · -- (phiFun D).carrier = D.carrier ⊆ D'.carrier = (phiFun D').carrier
    exact hDD'.1
  · -- morphism component
    intro N M
    exact hDD'.2.1 N M
  · -- pset:
    -- D.pset ∪ witnessedSet D.carrier D.morphism
    --   ⊆ D'.pset ∪ witnessedSet D'.carrier D'.morphism
    exact Finset.union_subset_union hDD'.2.2
      (witnessedSet_mono hDD'.1 hDD'.2.1)

/-- **Def 4.5.3** packaged as a bundled `OrderHom`, ready for
    `OrderHom.lfp`. -/
noncomputable def Phi : ArticulationCandidate →o ArticulationCandidate where
  toFun := phiFun
  monotone' := phi_monotone

/-! ## § 4 The Knaster-Tarski fixed point (Thm 5.2.1)

We now apply Mathlib's `OrderHom.lfp` to Φ, recovering D1 as the least
fixed point on 𝒜.  Per the position paper §5.2:

> **Theorem 5.2.1 (D1 = lfp(Φ) exists).** Define:
> D1 := lfp(Φ) = ⋀ {D ∈ 𝒜 : Φ(D) ≤ D}
>
> D1 is the least articulation candidate whose extracted requirements
> are already contained in its own property-set.
-/

/-- **Thm 5.2.1** + **§5.8 Final identification** of
    `docs-next/00_start/lawvere-identification.md`.

    **D1 = lfp(Φ)** — the Knaster-Tarski least fixed point of the
    requirements-extraction operator Φ on the lattice 𝒜 of
    articulation candidates.

    This is the precise mathematical content of "R-tower closure
    (D1 ⟷ P1-P7)". -/
noncomputable def D1 : ArticulationCandidate := OrderHom.lfp Phi

/-! ## § 5 Stated theorems for the identification

Per `lawvere-identification.md` §5.3.  Each theorem is **stated** here
with a `sorry`-marked proof.  These are the three theorems that
witness "D1 = lfp(Φ)" as the precise formal content of R-tower closure.
-/

/-- **Prop 5.3.1** of `docs-next/00_start/lawvere-identification.md` §5.3.

    D1 is a fixed point of Φ.

    *Proof from the paper:*  D1 = lfp(Φ) ⟹ Φ(D1) ≤ D1 (by lfp).  Also
    D1 ≤ Φ(D1) since Φ only adds P's (never removes structure).  Hence
    Φ(D1) = D1.

    *In Lean:*  This is immediate from Mathlib's `OrderHom.map_lfp`.
    The skeleton provides the statement; the proof is one line.

    **Discharge:**  With `phi_monotone` proved, `Phi` is a real
    bundled `OrderHom`, and the identity `Phi D1 = D1` is precisely
    `OrderHom.map_lfp`. -/
theorem D1_is_fixed_point : Phi D1 = D1 :=
  OrderHom.map_lfp Phi

/-- **Prop 5.3.2** of `docs-next/00_start/lawvere-identification.md` §5.3.

    D1 is the minimum P1-P7 satisfier: any D ∈ 𝒜 whose P-set contains
    all 8 P-properties has D1 ≤ D.

    *Proof from the paper:* If P_D ⊇ {P1, ..., P7b}, then Φ(D) = D
    (P-augmentation can't add anything new).  In particular, Φ(D) ≤ D.
    So D is in `{D : Φ(D) ≤ D}` whose meet is D1.  Hence D1 ≤ D.

    *In Lean:*  Use `OrderHom.lfp_le`.

    **Discharge:**  With `phi_monotone` in hand, we use
    `OrderHom.lfp_le`: it suffices to show `Phi D ≤ D`.  This holds
    because `Phi D` differs from `D` only by the union with
    `witnessedSet`, and every P-property is already in `D.pset` by
    `h_all_P`. -/
theorem D1_is_minimum_P_satisfier
    (D : ArticulationCandidate)
    (h_all_P : ∀ p : PProperty, p ∈ D.pset) :
    D1 ≤ D := by
  apply OrderHom.lfp_le Phi
  -- Goal: Phi D ≤ D
  refine ⟨?_, ?_, ?_⟩
  · -- carrier: (Phi D).carrier = D.carrier
    exact Set.Subset.rfl
  · -- morphism: (Phi D).morphism = D.morphism
    intro N M; exact Set.Subset.rfl
  · -- pset: (Phi D).pset = D.pset ∪ witnessedSet ... ⊆ D.pset
    -- because witnessedSet ⊆ D.pset (every P is in D.pset by h_all_P)
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact h
    · exact h_all_P p

/-! ### § 5.1 The three "structural-shape" theorems (Prop 5.3.4)

The position paper §5.3.4 asserts:

* `C_{D_1} = {R N : N ∈ ℕ}` (full carrier-class)
* `M_{D_1} = ⋃ LinHom(N, M)` (all morphisms)
* `P_{D_1} = {P1, ..., P7b}` (all 8 atomic properties)

**v0.5 finding (mathematically rigorous).**  Under Def 4.5.3 of Φ —
which leaves carrier and morphism unchanged and only augments pset —
**all three of these unconditional claims are false**.

The lfp `D1 = inf {D : Φ(D) ≤ D}` is the meet over ALL Φ-pre-fixed-points,
including very small candidates such as `(∅, ∅, {.p2, .p5})` which IS a
valid `ArticulationCandidate` and IS a Φ-fixed-point.  Hence
`D1 ≤ (∅, ∅, {.p2, .p5})`, forcing:

* `D1.carrier ⊆ ∅` (= ∅, contradicting the claim `= Set.univ`)
* `D1.morphism N M ⊆ ∅` (contradicting `= Set.univ`)
* `D1.pset ⊆ {.p2, .p5}` (contradicting `= all 8`)

In the opposite direction, `p2` and `p5` are witnessed unconditionally
by `witnessesP` (their predicate is `True`), so every Φ-pre-fixed-point
contains them in its pset, hence so does the meet `D1.pset`.

**Equality is therefore:**
* `D1.carrier = ∅`
* `D1.morphism N M = ∅` for all N, M
* `D1.pset = {.p2, .p5}`

This means **Def 4.5.3 of the position paper, as stated, does not
deliver the intended fixed point.**  To recover the doctrinal target
of §5.3.4, one needs to redefine Φ as a *carrier-and-morphism-growing*
operator (not just pset-augmenting), or to add a non-trivial
"existence" axiom forcing every candidate to contain at least R 1.

The skeleton below records this fact:

* The three original equalities are stated, documented as **false in
  v0.5**, and marked `sorry` with explicit counter-example.
* The three TRUE characterizations (`D1.carrier = ∅`, etc.) are
  stated and proved as `D1_carrier_eq_emptyset`, etc.
* The bridge-driven CONDITIONAL form is stated and proved as
  `D1_p4_implies_unbounded`, etc.

This is the cleanest formal record consistent with v0.4 doctrine.
The proper fix lives in a follow-up `v0.6` of the position paper.
-/

/-- A candidate `D` is in `Φ`-pre-fixed-point set `{D : Φ(D) ≤ D}`
    iff every `P` witnessed by `(D.carrier, D.morphism)` is already
    in `D.pset`. -/
theorem phi_le_iff (D : ArticulationCandidate) :
    Phi D ≤ D ↔ witnessedSet D.carrier D.morphism ⊆ D.pset := by
  refine ⟨?_, ?_⟩
  · -- (→): if Phi D ≤ D then witnessedSet ⊆ D.pset
    intro h p hp
    have hp' : p ∈ (Phi D).pset := Finset.mem_union.mpr (Or.inr hp)
    exact h.2.2 hp'
  · -- (←): if witnessedSet ⊆ D.pset then Phi D ≤ D
    intro h
    refine ⟨Set.Subset.rfl, fun _ _ => Set.Subset.rfl, ?_⟩
    intro p hp
    rcases Finset.mem_union.mp hp with h' | h'
    · exact h'
    · exact h h'

/-- The minimum Φ-pre-fixed-point: `(∅, ∅, {.p2, .p5})`. -/
noncomputable def minPreFP : ArticulationCandidate where
  carrier := ∅
  morphism := fun _ _ => ∅
  pset := {PProperty.p2, PProperty.p5}
  prod_closed := by intro N M hN; exact absurd hN (Set.notMem_empty _)
  hom_closed := by intro N M hN; exact absurd hN (Set.notMem_empty _)
  comp_closed := by intro N M K f hf; exact absurd hf (Set.notMem_empty _)
  id_in := by intro N hN; exact absurd hN (Set.notMem_empty _)
  p3_implies_R1 := by intro h; simp at h
  p4_implies_unbounded := by intro h; simp at h
  p6_implies_R2 := by intro h; simp at h
  p7b_implies_R4 := by intro h; simp at h

/-- `minPreFP` is a Φ-pre-fixed-point. -/
theorem minPreFP_is_pre_fp : Phi minPreFP ≤ minPreFP := by
  rw [phi_le_iff]
  classical
  intro p hp
  rw [mem_witnessedSet] at hp
  -- hp : witnessesP ∅ ∅-morphism p — only p2 and p5 are witnessed
  -- (p1, p7a need distinct morphisms in ∅ — impossible;
  --  p3, p4, p6, p7b need elements in ∅ — impossible)
  show p ∈ ({PProperty.p2, PProperty.p5} : Finset PProperty)
  cases p
  · -- p1
    obtain ⟨_, _, _, _, hf, _, _⟩ := hp
    exact absurd hf (Set.notMem_empty _)
  · -- p2
    simp
  · -- p3
    obtain ⟨_, hN, _⟩ := hp
    exact absurd hN (Set.notMem_empty _)
  · -- p4
    obtain ⟨_, hM, _⟩ := hp 0
    exact absurd hM (Set.notMem_empty _)
  · -- p5
    simp
  · -- p6
    exact absurd hp (Set.notMem_empty _)
  · -- p7a
    obtain ⟨_, _, _, _, hf, _, _⟩ := hp
    exact absurd hf (Set.notMem_empty _)
  · -- p7b
    exact absurd hp (Set.notMem_empty _)

/-- **(TRUE characterization; v0.5)** `D1.carrier = ∅`.

    Follows from `D1 ≤ minPreFP` (since `minPreFP` is Φ-pre-fixed)
    and `minPreFP.carrier = ∅`. -/
theorem D1_carrier_eq_empty : D1.carrier = ∅ := by
  apply Set.eq_empty_of_subset_empty
  exact (OrderHom.lfp_le Phi minPreFP_is_pre_fp).1

/-- **(TRUE characterization; v0.5)** `D1.morphism N M = ∅` for all N, M.

    Follows from `D1 ≤ minPreFP` and `minPreFP.morphism N M = ∅`. -/
theorem D1_morphism_eq_empty (N M : ℕ) : D1.morphism N M = ∅ := by
  apply Set.eq_empty_of_subset_empty
  exact (OrderHom.lfp_le Phi minPreFP_is_pre_fp).2.1 N M

/-- **(TRUE characterization; v0.5)** `D1.pset = {.p2, .p5}`.

    Forward: `D1 ≤ minPreFP` gives `⊆`.  Backward: both `.p2` and
    `.p5` are unconditionally witnessed, hence belong to every
    Φ-pre-fixed-point's pset, hence to the meet `D1.pset`. -/
theorem D1_pset_eq_p2_p5 :
    D1.pset = {PProperty.p2, PProperty.p5} := by
  apply Finset.Subset.antisymm
  · -- D1.pset ⊆ {p2, p5}
    exact (OrderHom.lfp_le Phi minPreFP_is_pre_fp).2.2
  · -- {p2, p5} ⊆ D1.pset.  Use `D1 = Phi(D1)`: p2, p5 ∈ witnessedSet ⊆ D1.pset.
    have hfp : Phi D1 = D1 := D1_is_fixed_point
    intro p hp
    have hp_p2_or_p5 : p = .p2 ∨ p = .p5 := by
      rcases Finset.mem_insert.mp hp with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    -- Show p ∈ (Phi D1).pset = D1.pset ∪ witnessedSet
    rw [← hfp]
    apply Finset.mem_union.mpr
    right
    classical
    rw [mem_witnessedSet]
    -- witnessesP D1.carrier D1.morphism p for p ∈ {p2, p5}
    rcases hp_p2_or_p5 with h | h <;> subst h <;> exact trivial

/-- **(Bridge corollary; v0.5)** If `.p4 ∈ D1.pset`, then D1's carrier
    is unbounded.  Direct consequence of `D1.p4_implies_unbounded`. -/
theorem D1_p4_implies_unbounded :
    .p4 ∈ D1.pset → ∀ N : ℕ, ∃ M ∈ D1.carrier, M > N :=
  D1.p4_implies_unbounded

/-- **(Bridge corollary; v0.5)** If `.p6 ∈ D1.pset`, then `R 2 ∈ D1.carrier`. -/
theorem D1_p6_implies_R2 : .p6 ∈ D1.pset → 2 ∈ D1.carrier :=
  D1.p6_implies_R2

/-- **(Bridge corollary; v0.5)** If `.p7b ∈ D1.pset`, then `R 4 ∈ D1.carrier`. -/
theorem D1_p7b_implies_R4 : .p7b ∈ D1.pset → 4 ∈ D1.carrier :=
  D1.p7b_implies_R4

/-! ### § 5.2 The three doctrinal targets of Prop 5.3.4 — stated, FALSE in v0.5

These three statements are the original §5.3.4 targets.  As established
above, **all three are false** under Def 4.5.3 of v0.4.  The skeleton
keeps them as named `sorry`-marked declarations so that downstream
reverse-references (e.g. `Foundation/R/ClaimZ.D1Articulation` bridge)
remain compilable.

Each statement is marked with its explicit counter-example via
`minPreFP`.  Discharging them would require redefining Φ to grow the
carrier (departing from §4.5.3 of the position paper).
-/

/-- **Prop 5.3.4 (carrier part)** — `D1.carrier = Set.univ`.

    **FALSE in v0.5** under Def 4.5.3 of Φ.  The minimum Φ-pre-fixed-point
    `minPreFP = (∅, ∅, {.p2, .p5})` satisfies `D1 ≤ minPreFP`, hence
    `D1.carrier ⊆ ∅` (see `D1_carrier_eq_empty`).

    To make this theorem true requires redefining Φ to grow the carrier
    when new P's are witnessed (not done in v0.4 of the position paper). -/
theorem D1_carrier_eq_all_RN : D1.carrier = Set.univ := by
  -- False: D1_carrier_eq_empty shows D1.carrier = ∅.
  -- Kept as `sorry` for downstream reference compatibility.
  sorry

/-- **Prop 5.3.4 (morphism part)** of `lawvere-identification.md` §5.3:
    D1's morphism class contains *all* linear maps between members of
    its carrier-class.

    **FALSE in v0.5** under Def 4.5.3.  See `D1_morphism_eq_empty`. -/
theorem D1_morphism_eq_all (N M : ℕ) : D1.morphism N M = Set.univ := by
  -- False: D1_morphism_eq_empty shows D1.morphism N M = ∅.
  sorry

/-- **Prop 5.3.4 (P-set part)** of `lawvere-identification.md` §5.3:
    D1's P-set is the full 8-element set.

    **FALSE in v0.5** under Def 4.5.3.  See `D1_pset_eq_p2_p5`:
    `D1.pset = {.p2, .p5}`. -/
theorem D1_pset_eq_all : D1.pset = PProperty.all.toFinset := by
  -- False: D1_pset_eq_p2_p5 shows D1.pset = {.p2, .p5}.
  sorry

/-! ## § 7 Bridge to existing `ClaimZ.D1Articulation` (future work)

The existing `Foundation/R/ClaimZ.lean` defines `D1Articulation` as a
**Prop-valued record** (8 fields, one per D1 item).  The skeleton above
defines `D1` as an **articulation candidate** (a lattice element).
These are two different "D1"s — one interface-level, one fixed-point-
level — that need a *bridging theorem*:

> **Future work (post-skeleton):** Define a map
>
>     D1_bridge : ArticulationCandidate → D1Articulation
>
> such that `D1_bridge D1` equals the canonical `D1Articulation`
> witnessed by the R-Family.  Then `D1_implies_Phase1Closure_F2`
> (Analytic.lean) becomes a corollary of `D1_pset_eq_all`
> instantiated at δ = Bool.

This bridging is the **Lean-side completion** of §5.4 of the position
paper (D1 ⟷ P1-P7 as the precise fixed-point statement).  It is *not*
part of this skeleton — it requires both directions of identification
(`ArticulationCandidate ↔ D1Articulation`) which depend on concrete
R-Vec instantiation.

Estimated effort: ~2-3 weeks once the main `sorry`s above are
discharged.
-/

-- **Bridge placeholder** — to be implemented once the main `sorry`s
-- above are discharged.  Future signature:
--
--     def D1_bridge : ArticulationCandidate → SSBX.Foundation.R.ClaimZ.D1Articulation
--
-- with witnessing theorems linking `D1_pset_eq_all` to
-- `D1_implies_Phase1Closure_F2`.

end ArticulationCandidate

end SSBX.Foundation.Closure
