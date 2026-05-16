/-
# Foundation.Closure.PhiOperator — Knaster-Tarski lfp identification of D1

**Skeleton** (per `docs-next/00_start/lawvere-identification.md` v0.2 §§4.5, 5.1-5.4).

## Doctrinal anchor

The position paper `lawvere-identification.md` (v0.2) establishes:

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
                            with consistency conditions)
* `instance : CompleteLattice ArticulationCandidate` — Prop 4.5.2
* `Phi : ArticulationCandidate →o ArticulationCandidate` — Def 4.5.3 + Thm 4.5.5
* `D1 : ArticulationCandidate := OrderHom.lfp Phi` — Thm 5.2.1
* Three stated theorems:
    - `D1_is_fixed_point` (Prop 5.3.1)
    - `D1_is_minimum_P_satisfier` (Prop 5.3.2)
    - `D1_carrier_eq_all_RN` (Prop 5.3.4)

## Scope

* This is a **partially-discharged skeleton**.  Of the original 8
  proof-level `sorry`s in the v0 skeleton, **5 are now discharged**:
    1. `botCandidate.comp_closed` (unit-propagation at `LinHom = Unit`)
    2. `instCompleteLattice` (constructed via `completeLatticeOfInf`
       from componentwise-intersection `sInfFun`)
    3. `phi_monotone` (Thm 4.5.5) — via `Finset.union_subset_union`
       plus `witnessedSet_mono`
    4. `D1_is_fixed_point` (Prop 5.3.1) — via `OrderHom.map_lfp`
    5. `D1_is_minimum_P_satisfier` (Prop 5.3.2) — via
       `OrderHom.lfp_le`
* The remaining **3 sorries** (`D1_carrier_eq_all_RN`,
  `D1_morphism_eq_all`, `D1_pset_eq_all`) are *false* under the
  current placeholder `witnessesP` (which only fires for P5), and so
  cannot be discharged without first refining the per-`PProperty`
  witnessing predicates.  See the doc-strings of those three
  theorems for the explicit counter-example
  (`D = (∅, ∅, {p5})` is a `Phi`-fixed-point).
* `lake build` succeeds with only `sorry` warnings, no errors.
* The architecture is the *Mathlib-compatible* one promised by
  §5.9 of the position paper: `OrderHom.lfp` is applied directly.
* Estimated remaining work (per-P_i witnesses + carrier-pset
  consistency conditions + Kleene iteration via
  `fixedPoints.lfp_eq_sSup_iterate`): ~2-4 weeks.

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
    `docs-next/00_start/lawvere-identification.md` §4.5.

    A triple `(carrier, morphism, pset)` carrying the consistency
    conditions of an articulation candidate over the self-internalising
    sub-class `{R N : N ∈ ℕ}` of R-Vec. -/
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
* pset = `(PProperty.all.toFinset).filter (fun p => ∀ D ∈ s, p ∈ D.pset)`

The consistency conditions transfer through universal quantification:
each `D ∈ s` has `prod_closed`, so the intersection has it too.

When `s = ∅` this gives `topCandidate` (universal carrier, all
morphisms, all P's); when `s` is non-empty the intersection is the
largest candidate contained in every element of `s`. -/

/-- Componentwise intersection — the GLB of a set of articulation
    candidates.  Uses classical choice for the P-set predicate's
    decidability (membership in `s` is not algorithmically decidable
    for arbitrary `s : Set ArticulationCandidate`). -/
noncomputable def sInfFun (s : Set ArticulationCandidate) : ArticulationCandidate where
  carrier := {N | ∀ D ∈ s, N ∈ D.carrier}
  morphism := fun N M => {f | ∀ D ∈ s, f ∈ D.morphism N M}
  pset :=
    haveI : DecidablePred (fun p : PProperty => ∀ D ∈ s, p ∈ D.pset) :=
      fun _ => Classical.propDecidable _
    (PProperty.all.toFinset).filter (fun p => ∀ D ∈ s, p ∈ D.pset)
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

/-- Membership in `(sInf s).pset`: a P-property is in the meet iff it
    is in every `D.pset` for `D ∈ s`. -/
theorem mem_sInf_pset {s : Set ArticulationCandidate} {p : PProperty} :
    p ∈ (sInf s).pset ↔ ∀ D ∈ s, p ∈ D.pset := by
  classical
  show p ∈ ((PProperty.all.toFinset).filter (fun p => ∀ D ∈ s, p ∈ D.pset)) ↔ _
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  -- Every PProperty is in `PProperty.all.toFinset`
  cases p <;> decide

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
      exact (mem_sInf_pset.mp hp) D hD
  · -- any lower bound is ≤ sInf s
    intro E hE
    refine ⟨?_, ?_, ?_⟩
    · -- E.carrier ⊆ (sInf s).carrier
      intro N hN D hD
      exact (hE hD).1 hN
    · -- E.morphism ⊆ (sInf s).morphism (component-wise)
      intro N M f hf D hD
      exact (hE hD).2.1 N M hf
    · -- E.pset ⊆ (sInf s).pset
      intro p hp
      exact mem_sInf_pset.mpr (fun D hD => (hE hD).2.2 hp)

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

/-- Decision predicate: does the (carrier, morphism) data structurally
    witness P_i?

    For the skeleton, we leave this `sorry`-stubbed at the per-P_i
    level.  Each predicate is decidable in principle (the witness
    conditions are first-order over finite/countable data), but
    formalizing each requires concrete work.

    Returns `true` if witnessed.  Default `false` means the property
    is not added by Φ. -/
def witnessesP (_carrier : Set ℕ) (_morphism : (N M : ℕ) → Set (LinHom N M))
    (p : PProperty) : Bool :=
  match p with
  | .p5 => true  -- Obs 4.5.4: hom-closure is automatic from 𝒜's consistency
  | _   => false  -- TODO: implement witnesses for P1, P2, P3, P4, P6, P7a, P7b

/-- The set of P-properties structurally witnessed by `(C, M)`. -/
def witnessedSet (carrier : Set ℕ) (morphism : (N M : ℕ) → Set (LinHom N M)) :
    Finset PProperty :=
  PProperty.all.toFinset.filter (fun p => witnessesP carrier morphism p = true)

/-- **Def 4.5.3** (Φ: Requirements Extraction) of
    `docs-next/00_start/lawvere-identification.md` §4.5.

    `Φ(D) = (C_D, M_D, P_D ∪ {P_i : structurally witnessed})`.

    Φ leaves the carrier and morphism class unchanged; it augments the
    P-set with all P_i whose structural witnesses are present in
    `(C, M)`. -/
def phiFun (D : ArticulationCandidate) : ArticulationCandidate where
  carrier := D.carrier
  morphism := D.morphism
  pset := D.pset ∪ witnessedSet D.carrier D.morphism
  prod_closed := D.prod_closed
  hom_closed := D.hom_closed
  comp_closed := D.comp_closed
  id_in := D.id_in

/-- **Monotonicity of `witnessesP` in the data** (per-`PProperty`).

    Stated as: if `C ⊆ C'` and `M ⊆ M'` componentwise, then
    `witnessesP C M p = true → witnessesP C' M' p = true`.

    For the current skeleton's `witnessesP` (P5 = constant true, all
    others = constant false), this is trivially true.  When the
    full per-P_i witnesses are implemented, each case will need its
    own monotonicity proof — but they all hold by inspection
    (witnesses are positive existential conditions on `(C, M)`). -/
theorem witnessesP_mono
    {C C' : Set ℕ} {M : (N K : ℕ) → Set (LinHom N K)}
    {M' : (N K : ℕ) → Set (LinHom N K)}
    (_hC : C ⊆ C') (_hM : ∀ N K, M N K ⊆ M' N K)
    (p : PProperty) :
    witnessesP C M p = true → witnessesP C' M' p = true := by
  -- Current witnessesP is constant in (C, M) for each p: P5 = true,
  -- others = false.  So `witnessesP C M p = witnessesP C' M' p`.
  cases p <;> intro h <;> exact h

/-- **Monotonicity of `witnessedSet`** in the data. -/
theorem witnessedSet_mono
    {C C' : Set ℕ} {M : (N K : ℕ) → Set (LinHom N K)}
    {M' : (N K : ℕ) → Set (LinHom N K)}
    (hC : C ⊆ C') (hM : ∀ N K, M N K ⊆ M' N K) :
    witnessedSet C M ⊆ witnessedSet C' M' := by
  intro p hp
  rw [witnessedSet, Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  exact witnessesP_mono hC hM p hp.2

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
def Phi : ArticulationCandidate →o ArticulationCandidate where
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

/-- **Prop 5.3.4** of `docs-next/00_start/lawvere-identification.md` §5.3.

    D1's structural shape: carrier = full {R N : N ∈ ℕ}.

    *Proof from the paper:* Needed for P4's unbounded recursion.

    *In Lean:*  Show D1.carrier = Set.univ by Kleene iteration
    (`fixedPoints.lfp_eq_sSup_iterate` from Mathlib, requires
    ω-continuity of Φ, which holds because the witnessing conditions
    depend only on finite data).

    **Sorry status:** This theorem is *FALSE for the current
    skeleton's placeholder `witnessesP`*: with `witnessesP _ _ p =
    (p = .p5)`, the candidate
    `D = (carrier={0}, morphism=trivial, pset={p5})` satisfies
    `Phi D ≤ D`, so `D1 ≤ D` and `D1.carrier ⊆ {0} ≠ Set.univ`.

    The theorem becomes *true* once the per-`PProperty` witnesses are
    fully implemented per §4.5: `witnessesP _ _ p4` must depend on
    the carrier being unbounded, and consistency conditions (e.g.,
    "if `p4 ∈ pset` then `carrier` is unbounded") must be added to
    `ArticulationCandidate`.  With those additions, Kleene iteration
    via `fixedPoints.lfp_eq_sSup_iterate` (Mathlib) discharges this.

    Estimated discharge effort (post-witnessesP refinement):
    ~1-2 weeks. -/
theorem D1_carrier_eq_all_RN : D1.carrier = Set.univ := by
  -- TODO: Kleene iteration after witnessesP and consistency are fully
  -- elaborated.  See note above for why this is currently unprovable.
  sorry

/-! ## § 6 Companion: D1's full structural characterization (Prop 5.3.4)

The position paper §5.3.4 also gives:

* `M_{D_1} = ⋃ LinHom(N, M)` (all linear maps)
* `P_{D_1} = {P1, ..., P7b}` (all 8 atomic properties)

These are stated as future-work theorems below for completeness.
-/

/-- **Prop 5.3.4 (morphism part)** of `lawvere-identification.md` §5.3:
    D1's morphism class contains *all* linear maps between members of
    its carrier-class.

    **Same scope caveat as `D1_carrier_eq_all_RN`**: false for the
    current placeholder `witnessesP`/`LinHom`; becomes true once
    per-`PProperty` witnesses are fully implemented (P3 forces all
    bilinear maps, P7a forces alphabet morphisms, P7b forces canonical
    ring, etc.). -/
theorem D1_morphism_eq_all (N M : ℕ) : D1.morphism N M = Set.univ := by
  -- TODO: Once witnessesP is fully elaborated, every linear map will
  -- be forced into D1.morphism by the P-witnessing constraints.
  sorry

/-- **Prop 5.3.4 (P-set part)** of `lawvere-identification.md` §5.3:
    D1's P-set is the full 8-element set.  This is the precise
    statement that "D1 satisfies all of P1-P7".

    **Same scope caveat as `D1_carrier_eq_all_RN`**: false for the
    current placeholder `witnessesP` (only P5 is witnessed); becomes
    true once witnessesP is fleshed out so that the lfp's pset
    accumulates all 8 properties. -/
theorem D1_pset_eq_all : D1.pset = PProperty.all.toFinset := by
  -- TODO: Once witnessesP fires for all 8 P's at the saturated D1,
  -- the lfp's pset will be PProperty.all.toFinset.
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
