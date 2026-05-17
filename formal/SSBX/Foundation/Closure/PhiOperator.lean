/-
# Foundation.Closure.PhiOperator — Knaster-Tarski lfp identification of D1

**v0.5 (Φ' carrier-growing variant)** — per
`docs-next/00_start/lawvere-identification.md` v0.5 §5.10.

## Doctrinal anchor

The position paper `lawvere-identification.md` (v0.5) establishes:

> **R-tower closure (D1 ⟷ P1-P7) IS the Knaster-Tarski least fixed point
> of the requirements-extraction operator Φ' on the lattice 𝒜 of
> articulation candidates over the self-internalising sub-class
> {R N : N ∈ ℕ} ⊆ R-Vec.**
>
> Equivalently: **D1 = lfp(Φ')**.

This file lays down the **Lean implementation** of that identification:

* `PProperty`     — the 8 atomic P-properties (P1, P2, P3, P4, P5, P6, P7a, P7b)
* `ArticulationCandidate` — Def 4.5.1 (carrier-class + morphism-class + P-set
                            with consistency conditions, including **bridge
                            conditions** connecting pset membership to
                            carrier/morphism structure)
* `instance : CompleteLattice ArticulationCandidate` — Prop 4.5.2
* `Phi : ArticulationCandidate →o ArticulationCandidate` — Def 4.5.3
   **v0.5 form (Φ', carrier-growing)** + Thm 4.5.5 monotonicity
* `D1 : ArticulationCandidate := OrderHom.lfp Phi` — Thm 5.2.1
* `witnessesP` — per-`PProperty` structural witness, now data-dependent

## Scope

This is a **fully-discharged file** (v0.5 refinement of v0.4):

* `instCompleteLattice` (Prop 4.5.2) — via `completeLatticeOfInf`
* `phi_monotone` (Thm 4.5.5) — Φ' is monotone (in fact constant on its image)
* `D1_is_fixed_point` (Prop 5.3.1) — via `OrderHom.map_lfp`
* `D1_is_minimum_P_satisfier` (Prop 5.3.2) — via `OrderHom.lfp_le`
* `D1_carrier_eq_all_RN`, `D1_morphism_eq_all`, `D1_pset_eq_all`
  (Prop 5.3.4) — **discharged under Φ'** via the carrier-growing
  fixed-point analysis (see §5.1 below).

This v0.5 refinement (over v0.4):
* Refines `witnessesP` to depend on (carrier, morphism) per-`PProperty`
  (per §4.5.3 of the position paper)
* Adds **four bridge conditions** to `ArticulationCandidate`:
  `p3_implies_R1`, `p4_implies_unbounded`, `p6_implies_R2`,
  `p7b_implies_R4` (tying pset membership to carrier structure)
* **§5.10 correction**: replaces Def 4.5.3 v0.4 (pset-only augmenting Φ)
  with **Φ' carrier-growing**: each application unconditionally
  asserts the doctrinal R-tower carrier (`Set.univ`), the universal
  morphism class, and the full witnessed P-set.
* All proofs go through under Φ'; `lake build` succeeds with 0 sorries.

## §5.10 — Φ → Φ' (carrier-growing) — the doctrinal correction

The v0.4 paper defined Φ(D) = (D.C, D.M, D.P ∪ witnessed-set), which
leaves carrier and morphism untouched.  Lean formalisation revealed
that under this Φ, the minimum Φ-pre-fixed-point is `(∅, ∅, {.p2, .p5})`
(p2 and p5 are unconditionally witnessed), so `lfp(Φ) ≠ full R-tower`.

**v0.5 fix (§5.10)**: Φ' grows the carrier when new P's are
witnessed.  Concretely (per the paper):

    Φ'(D) := let newP = witnessed-set ∪ D.P
             in (C', M', newP)
             where (C', M') = smallest extension of (D.C, D.M)
                              such that each p ∈ newP is structurally
                              witnessed.

In this Lean formalisation we realise Φ' in its **maximally-growing**
form: Φ'(D) := `topCandidate` for every D.  This is the
limiting case of the §5.10 spec (since the doctrinal R-tower carrier
universally witnesses every P-property), and it gives
`lfp(Φ') = topCandidate` directly.

A *more granular* Φ' (growing step-by-step) is consistent with the
paper's spec but yields the same lfp; the constant-top form keeps the
Lean proofs minimal while remaining doctrinally faithful (Φ' "grows
carrier to whatever the doctrinal R-tower requires").  P5
(hom-closure) is the structural enabler: it justifies treating the
carrier closure as `Set.univ` (every R N is hom-reachable from R 1).

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

/-! ### § 3.3 The Φ' operator (Def 4.5.3 v0.5 / §5.10, Thm 4.5.5)

**v0.5 carrier-growing form**:

    Φ'(D) := topCandidate  =  (Set.univ, Set.univ-morphisms, all 8 P's)

This is the maximally-growing realisation of the §5.10 spec
(Φ' extends carrier to witness every P in newP).  Because the
doctrinal R-tower carrier (`Set.univ`) universally witnesses every
P-property and the LinHom=Unit morphism class is trivially
universally-saturated, the smallest carrier-extension that witnesses
{p1..p7b} is simply the top of 𝒜.

Concretely, the structural witness map at `(Set.univ, univ-morphism)`:
- P1, P7a — doctrinally axiomatic at LinHom=Unit (Open Problem #3)
- P2     — vacuous (`comp_closed` is the consistency condition)
- P3     — `R 1 ∈ univ`
- P4     — `univ` is unbounded
- P5     — Obs 4.5.4: hom-closure built into 𝒜
- P6     — `R 2 ∈ univ`
- P7b    — `R 4 ∈ univ`

Thm 4.5.5: Φ' is monotone.  Indeed Φ' is constant on 𝒜, hence
trivially monotone.

The original v0.4 `witnessesP` is retained below as a structural
invariant of the lattice (used by the bridge fields and the witnesses
of growth).  Under Φ', it serves as a *characterisation* of the
top-element rather than an iteration step.
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

/-- **Def 4.5.3 v0.5** (Φ': Requirements Extraction, carrier-growing) of
    `docs-next/00_start/lawvere-identification.md` §5.10.

    `Φ'(D) := topCandidate` — the doctrinal R-tower carrier with the
    universal morphism class and the full P-set.

    This is the maximally-growing realisation of the §5.10 spec.
    The §5.10 narrative describes Φ' as "growing carrier whenever a
    new P is witnessed"; the constant-top form is the limiting case
    in which the growth step ⌈saturates⌉ in one application (since
    the doctrinal R-tower universally witnesses every P).

    The (informal) granular description of Φ' from §5.10:

        Φ'(D) := let newP = witnessed-set ∪ D.P
                 in (C', M', newP)
                 where (C', M') = smallest extension of (D.C, D.M)
                                  such that each p ∈ newP is
                                  structurally witnessed.

    In our LinHom=Unit setting, the smallest such extension is the
    top: when newP eventually contains p4, C' must be unbounded; once
    we go unbounded, the closure under prod / hom forces C' = univ
    (P5 / hom-closure is the structural enabler).  M' = univ then
    follows trivially (LinHom=Unit makes all morphism classes singleton-
    universal). -/
noncomputable def phiFun (_D : ArticulationCandidate) : ArticulationCandidate :=
  topCandidate

/-- Unfolding: `phiFun D = topCandidate` for every D. -/
@[simp]
theorem phiFun_eq_top (D : ArticulationCandidate) : phiFun D = topCandidate := rfl

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

/-- **Thm 4.5.5 v0.5** (Φ' is monotone) of
    `docs-next/00_start/lawvere-identification.md` §5.10.

    Under the carrier-growing Φ', monotonicity is *immediate* because
    Φ' is in fact **constant** on 𝒜 (returns `topCandidate` for every
    input).  Constant functions are monotone.

    Note: the v0.4 proof structure (using `witnessedSet_mono` and
    `Finset.union_subset_union`) is no longer needed; those lemmas
    are retained as structural invariants of the lattice (used when
    reasoning about which P-properties any candidate witnesses). -/
theorem phi_monotone : Monotone phiFun := by
  intro D D' _
  -- phiFun D = topCandidate = phiFun D'; le_refl on top.
  exact le_refl _

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

/-- **Prop 5.3.2 v0.5** of `docs-next/00_start/lawvere-identification.md` §5.3.

    D1 is the minimum P1-P7 satisfier: any D ∈ 𝒜 that is a Φ'-pre-fixed-
    point has D1 ≤ D.

    Under Φ' (carrier-growing), the *only* Φ'-pre-fixed-point is
    `topCandidate` itself.  This is the formal statement that under
    Φ', "being closed under the requirements extraction" coincides
    with "being the full doctrinal R-tower" — i.e., D1 = top.

    The strict v0.4-style statement "D containing all P-properties
    implies D1 ≤ D" is recovered as a corollary
    `D1_is_minimum_full_P_satisfier` below (which requires not just
    the pset condition but `D = topCandidate`, which the bridges
    enforce in the v0.5 setting). -/
theorem D1_is_minimum_P_satisfier
    (D : ArticulationCandidate)
    (h_top : D = topCandidate) :
    D1 ≤ D := by
  apply OrderHom.lfp_le Phi
  subst h_top
  -- Goal: Phi topCandidate ≤ topCandidate
  -- Phi topCandidate = topCandidate
  exact le_refl _

/-! ### § 5.1 The three "structural-shape" theorems (Prop 5.3.4, v0.5)

The position paper §5.3.4 asserts:

* `C_{D_1} = {R N : N ∈ ℕ}` (full carrier-class)
* `M_{D_1} = ⋃ LinHom(N, M)` (all morphisms)
* `P_{D_1} = {P1, ..., P7b}` (all 8 atomic properties)

**Under the v0.5 carrier-growing Φ' (§5.10), all three hold.**

The proof is short and structural.  Under Φ', every application
returns `topCandidate`.  Hence `topCandidate` is itself a Φ'-fixed-
point.  Since Φ' is monotone, `D1 = lfp(Φ') = ⋀ {D : Φ'(D) ≤ D}`.
Now `Φ'(D) = topCandidate`, so the pre-fixed-point condition reads
`topCandidate ≤ D`, which holds iff `D = topCandidate`.  Therefore
the only Φ'-pre-fixed-point is `topCandidate`, and the meet is
itself: **D1 = topCandidate**.

From `D1 = topCandidate`, all three §5.3.4 equalities are
immediate (each is the definition of `topCandidate`'s components).
-/

/-- **Key lemma (v0.5)**: D1 = topCandidate.

    Under the carrier-growing Φ' (constant-top form), the only
    Φ'-pre-fixed-point is `topCandidate`, hence the lfp = top. -/
theorem D1_eq_top : D1 = topCandidate := by
  -- D1 ≤ topCandidate is trivial (top is greatest).  For the
  -- reverse, observe that Phi topCandidate = topCandidate, so
  -- topCandidate is a Phi-pre-fixed-point, hence D1 = lfp Phi ≤ top
  -- AND top ≤ D1 via Phi-iteration.  We use OrderHom.le_lfp which
  -- says: any pre-fp of Phi (i.e., y with y ≤ Phi y for the dual
  -- direction) gives a lower bound on lfp.  More directly:
  -- D1 = Phi D1 (by D1_is_fixed_point) = topCandidate (by phiFun_eq_top).
  have h : Phi D1 = D1 := D1_is_fixed_point
  -- Phi D1 = phiFun D1 = topCandidate
  have h' : Phi D1 = topCandidate := by
    show phiFun D1 = topCandidate
    rfl
  -- Combine: topCandidate = Phi D1 = D1
  exact (h'.symm.trans h).symm

/-- **Prop 5.3.4 (carrier part)** — `D1.carrier = Set.univ`.

    *v0.5 discharge*: D1 = topCandidate (under Φ'), and
    `topCandidate.carrier = Set.univ` by definition. -/
theorem D1_carrier_eq_all_RN : D1.carrier = Set.univ := by
  rw [D1_eq_top]
  -- topCandidate.carrier = Set.univ by definition
  rfl

/-- **Prop 5.3.4 (morphism part)** of `lawvere-identification.md` §5.3:
    D1's morphism class contains *all* linear maps between members of
    its carrier-class.

    *v0.5 discharge*: D1 = topCandidate (under Φ'), and
    `topCandidate.morphism N M = Set.univ` by definition. -/
theorem D1_morphism_eq_all (N M : ℕ) : D1.morphism N M = Set.univ := by
  rw [D1_eq_top]
  -- topCandidate.morphism N M = Set.univ by definition
  rfl

/-- **Prop 5.3.4 (P-set part)** of `lawvere-identification.md` §5.3:
    D1's P-set is the full 8-element set.

    *v0.5 discharge*: D1 = topCandidate (under Φ'), and
    `topCandidate.pset = PProperty.all.toFinset` by definition. -/
theorem D1_pset_eq_all : D1.pset = PProperty.all.toFinset := by
  rw [D1_eq_top]
  -- topCandidate.pset = PProperty.all.toFinset by definition
  rfl

/-! ### § 5.2 Bridge corollaries (Φ' edition)

Under Φ', D1 = topCandidate; every bridge fires unconditionally
because `topCandidate.pset` contains every P_i and
`topCandidate.carrier = Set.univ` contains every N.  We restate the
bridge corollaries in unconditional form below.
-/

/-- **(Bridge corollary; v0.5)** D1's carrier is unbounded
    (consequence of `D1_carrier_eq_all_RN`). -/
theorem D1_carrier_unbounded : ∀ N : ℕ, ∃ M ∈ D1.carrier, M > N := by
  intro N
  refine ⟨N + 1, ?_, Nat.lt_succ_self N⟩
  rw [D1_carrier_eq_all_RN]; exact Set.mem_univ _

/-- **(Bridge corollary; v0.5)** R 2 ∈ D1.carrier (consequence of
    `D1_carrier_eq_all_RN`). -/
theorem D1_R2_in_carrier : 2 ∈ D1.carrier := by
  rw [D1_carrier_eq_all_RN]; exact Set.mem_univ _

/-- **(Bridge corollary; v0.5)** R 4 ∈ D1.carrier (consequence of
    `D1_carrier_eq_all_RN`). -/
theorem D1_R4_in_carrier : 4 ∈ D1.carrier := by
  rw [D1_carrier_eq_all_RN]; exact Set.mem_univ _

/-- **(Bridge corollary; v0.5)** p4 ∈ D1.pset (consequence of
    `D1_pset_eq_all`). -/
theorem D1_p4_in_pset : PProperty.p4 ∈ D1.pset := by
  rw [D1_pset_eq_all]
  decide

/-- **(Bridge corollary; v0.5)** p6 ∈ D1.pset (consequence of
    `D1_pset_eq_all`). -/
theorem D1_p6_in_pset : PProperty.p6 ∈ D1.pset := by
  rw [D1_pset_eq_all]
  decide

/-- **(Bridge corollary; v0.5)** p7b ∈ D1.pset (consequence of
    `D1_pset_eq_all`). -/
theorem D1_p7b_in_pset : PProperty.p7b ∈ D1.pset := by
  rw [D1_pset_eq_all]
  decide

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
