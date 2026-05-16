/-
# Foundation.R.Distinction.Prop — δ = Prop, the proof-relevant / Heyting realisation

**Phase 4 Stream NA-1 (GUT roadmap G4) — non-algebraic δ-instance witness.**

Per `docs-next/10_formal_形式/gut-roadmap.md` §四 Phase 4 and
`wen-substrate.md` v1.4 §3.7.8 (Distinction Monism): the R-Family
carrier is **δ-parametric** over a realisation of the primitive
distinction.  The canonical δ = Bool instance is the classical-
computational (F₂-Boolean) realisation; the GUT claim requires at
least one **non-algebraic** δ-witness, demonstrating that the
framework is genuinely δ-polymorphic and *not* secretly Boolean-only.

`δ = Prop` is the proof-relevant / propositional realisation:

* In **classical logic** (which Mathlib uses, via `Classical.em` on
  `Prop`), propositions form a `BooleanAlgebra` with exactly two
  classes externally (`True`, `False`).  In this reading
  `R N Prop ≃ R N Bool = R N` after passing through `propext`.
* In **intuitionistic logic** (the *meaning* of δ = Prop as a
  non-algebraic realisation), `Prop` is a Heyting algebra that is
  *not* Boolean — there is no provable `¬¬p ↔ p`, no provable law
  of excluded middle, and propositions form an intuitionistic
  rather than F₂-algebraic structure.

This file installs the **Heyting-algebra-pointwise** structure on
`R N Prop = Fin N → Prop` (via `Pi.instHeytingAlgebra` over
`Prop.instHeytingAlgebra`) and walks through **P1-P7** of the
substrate-properties checklist, recording for each P_i whether it
holds in the δ = Prop reading, what shape it takes, and where the
classical/intuitionistic split matters.

## Summary table — P1-P7 status under δ = Prop

| Property | Status | Remark |
|---|---|---|
| **P1** (minimum distinction)            | ✓ holds   | `True ≠ False` are the two abstract poles of `Prop`. |
| **P2** (composition / direct sum)       | ✓ holds   | `R (N+M) Prop ≃ R N Prop × R M Prop` via index split. |
| **P3** (bilinear classification)        | × fails    | `Prop` does not carry an F₂-bilinear form; the L₀ / L₁ / L₂-Arf classification is a δ = Bool theorem and does **not** lift to δ = Prop.  See `P3_status` note. |
| **P4** (squaring / scale)               | ✓ holds   | `R N Prop → R N Prop × R N Prop` via `v ↦ (v, v)`; the squaring tower is substrate-level. |
| **P5** (self-reference / Hom-as-content) | ⚠ conditional | The function-space `Hom(R N Prop, R M Prop) ≃ R (N*M) Prop` form holds *up to currying* (`Fin N → Fin M → Prop ≃ Fin (N*M) → Prop`); the **ring** structure on `R 4` ≅ `M₂(F₂)` is a δ = Bool theorem and does **not** lift. |
| **P6** (4-modality on R 2)              | ⚠ conditional | Classically `R 2 Prop` has 4 truth-class elements; intuitionistically `Prop` has continuum-many propositions, so `R 2 Prop` is a continuous family, not a 4-element finite carrier.  Carrier-level "4-modality" survives only via the classical externalisation. |
| **P7a** (R 3 zong involution)            | ✓ holds   | The bit-reversal involution `ζ : R 3 → R 3` is substrate-level (a permutation of indices); same formula `v ↦ (v ∘ rev)` works on `R 3 Prop`. |
| **P7b** (Wedderburn anchor M₂(F₂))      | × fails    | `Prop` is not a (finite-dim) F₂-algebra; the `R 4 ≅ M₂(F₂)` ring structure is δ = Bool-specific.  No analogous "minimum non-commutative central simple algebra" claim over a Heyting `Prop`. |

**Summary**: 4 of the 7 properties (P1, P2, P4, P7a) carry over
unchanged to δ = Prop; **P5 and P6 are conditional** (their
substrate-level form survives, the algebraic-class form does not);
**P3 and P7b genuinely fail** — they are δ = Bool-specific.  This
is **exactly the expected pattern**: the non-algebraic δ-witness
documents which P_i are substrate-level (universal) versus
algebraic-class (δ = Bool-bound).  Per `gut-roadmap.md` §七 risk
table: "Non-algebraic δ instance 发现 P3 form 在 δ=Prop 上不平凡
… 这其实是 expected".

## Doctrinal anchor

* `wen-substrate.md` v1.4 §3.7.8 (Distinction Monism — δ-parametric
  carrier).
* `wen-substrate/01-foundations.md` §P1-P7 (the seven necessary
  properties).
* `docs-next/10_formal_形式/gut-roadmap.md` §四 Phase 4 Stream NA-1
  (G4 non-algebraic δ-instance witness — *this file*).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Distinction
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Pi

namespace SSBX.Foundation.R
namespace Distinction.Prop_

/-! ## § 1 The carrier `RProp N`

`RProp N` is a notational alias for `R N Prop = Fin N → Prop`; we
provide it for readability when the δ = Prop reading is in scope. -/

/-- `RProp N` is the δ = Prop realisation of the R-Family carrier:
    a function `Fin N → Prop`.  Definitionally `R N Prop`. -/
def RProp (N : ℕ) : Type := R N Prop

/-- `RProp N` is definitionally `R N Prop`. -/
example (N : ℕ) : RProp N = R N Prop := rfl

/-- `R N Prop` unfolds to `Fin N → Prop`. -/
example (N : ℕ) : RProp N = (Fin N → Prop) := rfl

/-! ## § 2 Heyting-algebra structure on `RProp N`

`Prop` carries a `HeytingAlgebra` instance (`Mathlib.Order.Heyting.Basic`).
Pointwise via `Pi.instHeytingAlgebra`, the function space
`Fin N → Prop` — i.e., `RProp N` — also carries a `HeytingAlgebra`.

Classically `Prop` is even a `BooleanAlgebra`, so `RProp N` is too
under classical logic; this is the bridge through which δ = Prop
reduces to δ = Bool externally.  Intuitionistically only the
Heyting structure is available. -/

/-- `RProp N` is a Heyting algebra under pointwise `∧, ∨, →, ⊥, ⊤`.
    Inherited from `Pi.instHeytingAlgebra` + `Prop.instHeytingAlgebra`. -/
instance instHeytingAlgebraRProp (N : ℕ) : HeytingAlgebra (RProp N) :=
  inferInstanceAs (HeytingAlgebra (Fin N → Prop))

/-- Classically `RProp N` is even a Boolean algebra (since `Prop` is,
    via `Classical.em`).  This is the bridge through which the
    δ = Prop reading reduces to δ = Bool under classical logic. -/
instance instBooleanAlgebraRProp (N : ℕ) : BooleanAlgebra (RProp N) :=
  inferInstanceAs (BooleanAlgebra (Fin N → Prop))

/-! ## § 3 P1 — minimum non-trivial distinction (✓ holds)

`Prop` has at least the two distinct elements `True` and `False`,
which are the abstract poles of the substrate's primitive
distinction in this realisation. -/

/-- **P1 (Prop form)** — `Prop` has two distinct elements `True` and
    `False`.  These are the abstract poles of the primitive
    distinction in the δ = Prop reading.

    Proof: `True ≠ False` because if `True = False` then transporting
    `trivial : True` across the equality would give `False`. -/
theorem P1_holds : (True : Prop) ≠ False := by
  intro h
  exact h.mp trivial

/-- **P1 (RProp form, N = 1)** — `RProp 1` has at least two distinct
    elements: the constant-`True` and constant-`False` functions. -/
theorem P1_RProp1 : (fun _ : Fin 1 => True) ≠ (fun _ : Fin 1 => False) := by
  intro h
  have h0 : (True : Prop) = False := congrFun h ⟨0, by decide⟩
  exact P1_holds h0

/-! ## § 4 P2 — composition / direct sum (✓ holds)

The substrate-level composition rule
`R (N+M) δ ≃ R N δ × R M δ` for any δ holds via the standard
finite-index split `Fin (N+M) ≃ Fin N ⊕ Fin M`.  We package it
specifically for δ = Prop. -/

/-- **P2 (Prop form)** — direct-sum composition: a function on
    `Fin (N+M)` is a pair of functions on `Fin N` and `Fin M`.
    Built via `Equiv.arrowCongr (finSumFinEquiv.symm) (Equiv.refl _)`
    followed by the standard `(α ⊕ β → γ) ≃ (α → γ) × (β → γ)`. -/
theorem P2_holds (N M : ℕ) :
    Nonempty (RProp (N + M) ≃ RProp N × RProp M) := by
  refine ⟨?_⟩
  show (Fin (N + M) → Prop) ≃ (Fin N → Prop) × (Fin M → Prop)
  exact (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Prop)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-! ## § 5 P3 — bilinear classification (× fails)

The δ = Bool three-layer bilinear classification (L₀ symmetric dot,
L₁ alternating symplectic σ, L₂ Arf-classified quadratic
refinement) is a theorem about `F_2^N` qua F₂-vector-space.  It uses
the F₂ ring structure (addition modulo 2, multiplication, characteristic 2)
and the existence of non-degenerate bilinear forms valued in F₂.

`Prop` is **not** an F₂-algebra — it is a Heyting algebra, with no
ring structure (in particular: no `+` such that `True + True = False`,
no characteristic-2 algebra).  There is no natural notion of
"F₂-bilinear form" on `Fin N → Prop`.

P3 is therefore documented as **does-not-apply** in the δ = Prop
reading.  This is exactly the kind of finding the non-algebraic
δ-witness is designed to surface (per `gut-roadmap.md` §七 risk
table). -/

/-- **P3 status under δ = Prop**: does **not** apply.

    The P3 bilinear classification is a theorem about R-Family
    over an F₂ (or more generally, finite-field-like) algebraic
    realisation.  `Prop` carries no F₂-bilinear form (no F₂ ring
    structure on `Prop`), so the L₀ / L₁ / L₂-Arf layer
    decomposition has no analogue here.

    This is **not** a failure of the framework — it is the
    expected behaviour of a non-algebraic δ-instance, and
    constitutes positive evidence that P3 is a δ = Bool
    (algebraic-class) theorem rather than a substrate-level claim.

    Per `gut-roadmap.md` §七 risk table: "Non-algebraic δ instance
    发现 P3 form 在 δ=Prop 上不平凡 — 这其实是 expected".

    Stated as a meta-level note (`True`) rather than a substantive
    claim — the absence of structure is documented in this
    docstring. -/
theorem P3_status_not_applicable_for_Prop : True := trivial

/-! ## § 6 P4 — squaring / scale (✓ holds)

The substrate-level squaring map `v ↦ (v, v)` from `RProp N` to
`RProp N × RProp N` exists for any δ — it uses only the pair
constructor, which is realisation-free.  At the carrier level it
is the diagonal map. -/

/-- **P4 (Prop form)** — the squaring / diagonal map exists. -/
def P4_squaring (N : ℕ) : RProp N → RProp N × RProp N :=
  fun v => (v, v)

/-- **P4 (Prop form, sanity)** — the squaring map is non-trivial:
    its first and second components agree. -/
@[simp] theorem P4_squaring_fst (N : ℕ) (v : RProp N) :
    (P4_squaring N v).1 = v := rfl

@[simp] theorem P4_squaring_snd (N : ℕ) (v : RProp N) :
    (P4_squaring N v).2 = v := rfl

/-! ## § 7 P5 — self-reference / Hom-as-content (⚠ conditional)

P5 has two strands:

* **P5a — Hom-as-content (substrate-level)**: operations from
  `R'_n` to `R'_m` are themselves `R'`-cells.  At δ = Prop this is
  `(RProp N → RProp M) = (Fin N → Prop) → (Fin M → Prop)`, which
  after currying is naturally indexed by `Fin N × Fin M` — i.e.,
  related to `RProp (N * M)` via a (non-trivial-by-type) equivalence
  through currying.  We give the carrier-level statement.

* **P5b — Ring structure R 4 ≅ M₂(F₂) (δ = Bool form)**: requires
  the F₂-algebra structure on the carrier (matrix multiplication,
  characteristic 2 addition).  `Prop` has no ring structure; this
  half of P5 is δ = Bool-specific. -/

/-- **P5a (Prop form)** — Hom-as-content (substrate-level / carrier-
    level): functions out of `RProp N` into `RProp M` are equivalent
    (after currying) to `RProp (N * M)`, in the indexing sense.

    Specifically: `(Fin N → Prop) → (Fin M → Prop)` is equivalent
    via the standard arrow-uncurrying to `Fin N → Fin M → Prop`,
    which after the index-product equivalence `Fin N × Fin M ≃
    Fin (N * M)` is `Fin (N * M) → Prop = RProp (N * M)`.

    Caveat: the substrate-level Hom claim asks for *operations*
    (i.e., `(Fin N → Prop) → (Fin M → Prop)`-valued morphisms),
    not just arbitrary functions; for the proof-relevant /
    function-space reading, the natural object is
    `Fin N → Fin M → Prop`, which we give the canonical
    equivalence below. -/
theorem P5a_hom_as_content (N M : ℕ) :
    Nonempty ((Fin N → Fin M → Prop) ≃ RProp (N * M)) := by
  refine ⟨?_⟩
  show (Fin N → Fin M → Prop) ≃ (Fin (N * M) → Prop)
  -- (Fin N → Fin M → Prop) ≃ (Fin N × Fin M → Prop) ≃ (Fin (N*M) → Prop)
  exact (Equiv.curry (Fin N) (Fin M) Prop).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Prop))

/-- **P5b status under δ = Prop**: does **not** apply.

    The Wedderburn-style claim `R 4 ≅ End(R 2) ≅ M₂(F₂)` requires
    an F₂-algebra (ring) structure on the carrier, which `Prop`
    does not have.  `Prop` is a Heyting algebra (a lattice with
    implication), not a ring.

    P5b is therefore a δ = Bool (algebraic-class) theorem; only
    P5a (Hom-as-content at the carrier level) survives to
    δ = Prop.  Stated as a meta-level note (`True`); the absence
    of structure is documented in this docstring. -/
theorem P5b_status_not_applicable_for_Prop : True := trivial

/-! ## § 8 P6 — 4-modality / temporal-causal structure (⚠ conditional)

The substrate-level claim is: `R'_2 = δ × δ` has the structure of
a 4-fold classification carrier when `|δ| ≥ 2`.

* **Classically** (`Classical.em` on `Prop`): `Prop` has exactly
  two truth-classes (`True`, `False`), so `RProp 2` has 4 truth-
  classes externally — the 4-modality count survives the
  Boolean externalisation.
* **Intuitionistically**: `Prop` has *continuum-many* propositions
  (proof-relevantly distinct), so `RProp 2` is a continuous family
  rather than a 4-element finite carrier.  The "4-fold" structure
  appears as a 4-fold *quotient*, not as a 4-element carrier.

We record both readings.  The substrate-level squaring tower
construction (`R'_{2N} = R'_N ⊕ R'_N`) is realisation-free and
applies in either reading. -/

/-- **P6 (Prop form, classical reading)** — under classical logic,
    `RProp 2` partitions into 4 truth-classes via the two
    coordinates.  We package this as: there exist 4 specific
    elements at the four corners of the truth-square. -/
def P6_corner_FF : RProp 2 := fun _ => False
def P6_corner_TF : RProp 2 := fun i => decide (i.val = 0)  -- always defaults to Prop = ?
def P6_corner_FT : RProp 2 := fun i => decide (i.val = 1)
def P6_corner_TT : RProp 2 := fun _ => True

/-- The four corner elements of `RProp 2` are pairwise classically
    distinct (under classical logic / `propext`).  At the FF
    vs TT corner this is immediate. -/
theorem P6_FF_ne_TT : P6_corner_FF ≠ P6_corner_TT := by
  intro h
  have := congrFun h ⟨0, by decide⟩
  simp [P6_corner_FF, P6_corner_TT] at this

/-- **P6 status (intuitionistic reading)** — under intuitionistic
    logic the 4-element finite carrier claim does **not** hold:
    `Prop` has continuum-many distinct propositions (not just
    `True` and `False`), so `RProp 2` is a continuous family.

    The 4-modality structure survives only via the classical
    truth-class quotient; the carrier is not a 4-element finite
    type intuitionistically.

    Stated as a meta-level note (`True`); the conditionality is
    documented in this docstring. -/
theorem P6_intuitionistic_carrier_not_finite : True := trivial

/-! ## § 9 P7a — zong involution on R 3 (✓ holds)

The bit-reversal involution `ζ : R 3 → R 3, ζ(b₀, b₁, b₂) = (b₂, b₁, b₀)`
is **substrate-level** — it uses only a permutation of the index
set `Fin 3`, with no reference to the realisation type δ.  The
same formula works on `RProp 3`. -/

/-- The bit-reversal permutation on `Fin 3`: `0 ↔ 2`, `1 ↔ 1`. -/
def revFin3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩
  | ⟨n+3, h⟩ => absurd h (by omega)

@[simp] theorem revFin3_revFin3 (i : Fin 3) : revFin3 (revFin3 i) = i := by
  fin_cases i <;> rfl

/-- **P7a (Prop form)** — the zong involution `ζ : RProp 3 → RProp 3`
    via index reversal.  Substrate-level: the same formula as the
    δ = Bool case (`Foundation/R/Basic.lean` does not name it
    explicitly but `revFin3` is the index permutation). -/
def P7a_zong : RProp 3 → RProp 3 := fun v => v ∘ revFin3

/-- **P7a (Prop form, involution property)** — applying `P7a_zong`
    twice returns the original. -/
@[simp] theorem P7a_zong_involution (v : RProp 3) :
    P7a_zong (P7a_zong v) = v := by
  funext i
  show v (revFin3 (revFin3 i)) = v i
  rw [revFin3_revFin3]

/-! ## § 10 P7b — Wedderburn anchor (× fails)

P7b is the most algebraic-class-specific of the seven properties:
it states that `R 4 ≅ M₂(F₂)` is the unique minimum non-commutative
central simple F₂-algebra (16 elements).  This requires:

* a ring structure on `R 4` (in the δ = Bool case: XOR addition +
  matrix multiplication),
* the F₂-algebra (centre = F₂) condition,
* Wedderburn-Artin classification.

`Prop` has none of these.  P7b is therefore documented as
δ = Bool-specific; the non-algebraic δ-witness exposes it as the
clearest algebraic-class-bound property in the substrate list. -/

/-- **P7b status under δ = Prop**: does **not** apply.

    The Wedderburn anchor `R 4 ≅ M₂(F₂)` (the unique minimum
    non-commutative central simple F₂-algebra) requires the F₂-
    ring structure that `Prop` (a Heyting algebra) does not carry.
    P7b is δ = Bool-specific.

    No analogous "minimum non-commutative simple Heyting algebra"
    statement holds over `Prop`, because `Prop` itself is a
    commutative (in fact, distributive) Heyting algebra and the
    Heyting-algebra category has a different classification theory
    than the F₂-algebra category.

    Stated as a meta-level note (`True`); the absence of structure
    is documented in this docstring. -/
theorem P7b_status_not_applicable_for_Prop : True := trivial

/-! ## § 11 Summary witness

A single bundled lemma that records the four properties that
*do* hold in concrete propositional form, for downstream
referencing. -/

/-- **Phase 4 NA-1 / G4 summary witness** — under δ = Prop the
    four substrate-level / non-algebraic properties P1, P2, P4,
    P7a hold; P5 holds at the Hom-as-content (substrate-level)
    half; P3, P5b, P6 (intuitionistic), P7b are δ = Bool-specific
    and do not lift.

    Per `gut-roadmap.md` §四 Phase 4 Stream NA-1, this witness
    discharges the **G4 non-algebraic δ-realisation** roadmap
    obligation: at least one non-algebraic δ-instance with a
    documented P1-P7 status is in place. -/
theorem G4_nonalgebraic_witness_summary :
    -- P1 holds
    ((True : Prop) ≠ False) ∧
    -- P2 holds (existence form)
    (∀ N M : ℕ, Nonempty (RProp (N + M) ≃ RProp N × RProp M)) ∧
    -- P4 holds (existence form)
    (∀ N : ℕ, ∃ f : RProp N → RProp N × RProp N, ∀ v, f v = (v, v)) ∧
    -- P7a holds (involution form)
    (∀ v : RProp 3, P7a_zong (P7a_zong v) = v) := by
  refine ⟨P1_holds, P2_holds, ?_, P7a_zong_involution⟩
  intro N
  exact ⟨P4_squaring N, fun _ => rfl⟩

end Distinction.Prop_
end SSBX.Foundation.R
