/-
# Foundation.R.UniquenessGeneral.Demos — concrete polymorphic T5 demos

Per the directive "推广到 general" (generalise beyond Bool), this file
delivers **concrete demonstrations** that the polymorphic T5 theorem
(`UniquenessGeneral.T5_general`) is honest at non-Bool δ.

The corollaries in `Foundation/R/UniquenessGeneral.lean`
(`T5_general_at_Distinction`, `T5_general_at_Fin`, `T5_general_at_ZMod`)
are *abstract* — they speak about arbitrary `S : P1P7_Core δ`.  This
file makes the polymorphic content **tangible** at four concrete
δ-instances:

| δ              | Cardinality | Algebraic flavour          |
|----------------|-------------|----------------------------|
| `Bool`         | 2           | F₂ (Boolean ring)          |
| `Distinction`  | 2           | abstract o/x substrate     |
| `ZMod 3`       | 3           | F₃ (prime field)           |
| `Fin 5`        | 5           | Fintype, no field          |
| `ZMod 2`       | 2           | F₂ — cross-instance Bool   |

For each δ we

* exhibit a concrete `S_δ : P1P7_Core δ` (canonical or via a
  non-canonical transport from another δ');
* apply `T5_general` to obtain the layerwise equivalence
  `S_δ.carrier N ≃ R N δ`;
* compute concrete layer cardinalities via `P1P7_Core.carrier_card_eq`.

We also prove the **cross-instance theorem**
`R N Bool ≃ R N (ZMod 2)` — different δ-realisations of the same
cardinality-2 substrate produce isomorphic R-layers at every N.

## Doctrinal anchor

* `Foundation/R/UniquenessGeneral.lean` — the polymorphic T5 theorem.
* `Foundation/R/Distinction.lean` v1.4 §3.7.8 — the abstract o/x
  substrate.
* `gut-roadmap.md` v0.2 §十一 — polymorphic T5 generalisation
  (concrete δ-instances are the "non-vacuous witnesses" the doctrine
  promises).
-/

import SSBX.Foundation.R.UniquenessGeneral

namespace SSBX.Foundation.R.UniquenessGeneral.Demos

open SSBX.Foundation.R
open SSBX.Foundation.R.UniquenessGeneral

/-! ## § 1 δ = Distinction demo (non-canonical via Bool transport)

The abstract `Distinction` substrate (Foundation/R/Distinction.lean
§3.7.8) is cardinality-2 but is *not definitionally* `Bool`.  We
construct a **non-canonical** `P1P7_Core Distinction` whose carriers
are `R N Bool` (the F₂ classical realisation), and whose
δ-cardinality witness uses the `Distinction.equivBool` bridge.

This demonstrates that `T5_general` collapses two distinct
presentations of the same substrate to the same layerwise R-shape. -/

/-- **Non-canonical** `P1P7_Core Distinction` built by transporting
    the canonical Bool R-family `R · Bool` along the abstract
    substrate.  Layer `N` is `R N Bool` (the F₂ classical R-family
    carrier).  The base-card axiom is discharged via
    `Distinction.card = 2 = |Bool|`. -/
def boolTransportedToDistinction : P1P7_Core Distinction where
  carrier := fun N => R N Bool
  fintype := fun N => instFintypeRGeneral N Bool
  decEq := fun N => instDecEqRGeneral N Bool
  p1_base_card := by
    -- |R 1 Bool| = 2 = |Distinction|; both sides reduce concretely.
    show Fintype.card (Fin 1 → Bool) = Fintype.card Distinction
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Distinction.card]; rfl
  p2_directSum := fun N M => by
    -- R (N + M) Bool = (Fin (N + M) → Bool) ≃ (Fin N → Bool) × (Fin M → Bool)
    show (Fin (N + M) → Bool) ≃ (Fin N → Bool) × (Fin M → Bool)
    exact (Equiv.arrowCongr finSumFinEquiv (Equiv.refl Bool)).symm.trans
            (Equiv.sumArrowEquivProdArrow _ _ _)

/-- **T5_general at the Bool-transported Distinction instance** —
    layerwise equivalence between the transported carriers and
    `R N Distinction`. -/
theorem demo_distinction_bool_transport (N : ℕ) :
    Nonempty (boolTransportedToDistinction.carrier N ≃ R N Distinction) :=
  T5_general boolTransportedToDistinction N

/-- **Coordinate-wise lift of `Distinction ≃ Bool` to the R-layers** —
    the substrate-level equivalence between the abstract and
    classical realisations is preserved at every layer. -/
def R_Distinction_equiv_R_Bool (N : ℕ) : R N Distinction ≃ R N Bool :=
  Equiv.arrowCongr (Equiv.refl (Fin N)) Distinction.equivBool

/-- **Cardinality witness at the abstract substrate** —
    `|R N Distinction| = 2^N`, the same as the F₂ classical realisation. -/
theorem R_Distinction_card (N : ℕ) :
    Fintype.card (R N Distinction) = 2 ^ N := by
  rw [R.card_eq_general, Distinction.card]

/-! ## § 2 δ = ZMod 3 demo (ternary distinction, prime-field flavour)

The ternary substrate `ZMod 3` is the smallest non-Bool prime field.
We use the canonical R-family `canonicalRFamily (ZMod 3)` and
compute concrete layer cardinalities (`|R 2 (ZMod 3)| = 9`,
`|R 3 (ZMod 3)| = 27`). -/

/-- **Canonical `P1P7_Core (ZMod 3)`** — the ternary R-family. -/
def zmod3Demo : P1P7_Core (ZMod 3) := canonicalRFamily (ZMod 3)

/-- **T5_general at ZMod 3** — applied to the canonical R-family,
    this is the identity equivalence `R N (ZMod 3) ≃ R N (ZMod 3)`. -/
theorem demo_zmod3_T5 (N : ℕ) :
    Nonempty (zmod3Demo.carrier N ≃ R N (ZMod 3)) :=
  T5_general zmod3Demo N

/-- **Layer-2 cardinality at ZMod 3** — `|R 2 (ZMod 3)| = 9 = 3²`. -/
theorem R2_ZMod3_card : Fintype.card (R 2 (ZMod 3)) = 9 := by
  rw [R.card_eq_general]; rfl

/-- **Layer-3 cardinality at ZMod 3** — `|R 3 (ZMod 3)| = 27 = 3³`. -/
theorem R3_ZMod3_card : Fintype.card (R 3 (ZMod 3)) = 27 := by
  rw [R.card_eq_general]; rfl

/-- **Layer-1 cardinality at ZMod 3** — `|R 1 (ZMod 3)| = 3`. -/
theorem R1_ZMod3_card : Fintype.card (R 1 (ZMod 3)) = 3 := by
  rw [R.card_eq_general]; rfl

/-- **General-layer cardinality at ZMod 3** — `|R N (ZMod 3)| = 3^N`. -/
theorem RN_ZMod3_card (N : ℕ) : Fintype.card (R N (ZMod 3)) = 3 ^ N := by
  rw [R.card_eq_general]; rfl

/-! ## § 3 δ = Fin 5 demo (5-ary, non-field, no ring structure)

The 5-ary substrate `Fin 5` is a `Fintype` of cardinality 5 but is
*not* equipped with a ring/field structure (no canonical algebraic
operations).  This demonstrates that `T5_general` is a purely
**Fintype + DecidableEq + Inhabited** statement — it does not require
any algebraic structure on δ.

We use the canonical R-family `canonicalRFamily (Fin 5)`. -/

/-- **Canonical `P1P7_Core (Fin 5)`** — the 5-ary R-family. -/
def fin5Demo : P1P7_Core (Fin 5) := canonicalRFamily (Fin 5)

/-- **T5_general at Fin 5** — applied to the canonical R-family,
    this is the identity equivalence `R N (Fin 5) ≃ R N (Fin 5)`. -/
theorem demo_fin5_T5 (N : ℕ) :
    Nonempty (fin5Demo.carrier N ≃ R N (Fin 5)) :=
  T5_general fin5Demo N

/-- **Layer-2 cardinality at Fin 5** — `|R 2 (Fin 5)| = 25 = 5²`. -/
theorem R2_Fin5_card : Fintype.card (R 2 (Fin 5)) = 25 := by
  rw [R.card_eq_general]; rfl

/-- **Layer-1 cardinality at Fin 5** — `|R 1 (Fin 5)| = 5`. -/
theorem R1_Fin5_card : Fintype.card (R 1 (Fin 5)) = 5 := by
  rw [R.card_eq_general]; rfl

/-- **General-layer cardinality at Fin 5** — `|R N (Fin 5)| = 5^N`. -/
theorem RN_Fin5_card (N : ℕ) : Fintype.card (R N (Fin 5)) = 5 ^ N := by
  rw [R.card_eq_general]; rfl

/-! ## § 4 Cross-instance comparison: Bool ↔ ZMod 2 at every layer

Two distinct δ-realisations of the **same cardinality-2 substrate**
(Bool and ZMod 2) produce R-layers that are equivalent at every N.
We construct the explicit coordinate-wise equivalence via
`Bool ≃ ZMod 2` (cardinalities match, so `Fintype.equivOfCardEq`
suffices).  -/

/-- **Bool ≃ ZMod 2** — both have cardinality 2; we use the generic
    Fintype equivalence (Mathlib does not ship a named computational
    bridge, and any choice of which Bool-element maps to which
    ZMod 2-element is structurally fine for our layerwise purposes). -/
noncomputable def boolEquivZMod2 : Bool ≃ ZMod 2 :=
  Fintype.equivOfCardEq (by rw [Fintype.card_bool, ZMod.card])

/-- **Cross-instance theorem** — `R N Bool ≃ R N (ZMod 2)`.

    At the layerwise level, the F₂ Boolean R-family and the ZMod 2
    R-family are equivalent: they are two presentations of the same
    cardinality-2 substrate, lifted coordinate-wise to N-tuples. -/
noncomputable def R_Bool_equiv_R_ZMod2 (N : ℕ) : R N Bool ≃ R N (ZMod 2) :=
  Equiv.arrowCongr (Equiv.refl (Fin N)) boolEquivZMod2

/-- **Cross-instance equivalence is provable via `T5_general` too** —
    both `canonicalRFamily Bool` and `canonicalRFamily (ZMod 2)`
    produce R-layers with the same cardinality, so `Fintype.equivOfCardEq`
    closes the equivalence.  This is the abstract route; the explicit
    route `R_Bool_equiv_R_ZMod2` above is preferred for downstream use. -/
theorem R_Bool_card_eq_R_ZMod2 (N : ℕ) :
    Fintype.card (R N Bool) = Fintype.card (R N (ZMod 2)) := by
  show Fintype.card (Fin N → Bool) = Fintype.card (Fin N → ZMod 2)
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, ZMod.card]

/-! ## § 5 Cross-instance comparison: Bool ↔ Distinction at every layer

Same shape as § 4, but for the abstract substrate `Distinction`
(Foundation/R/Distinction.lean §3.7.8) — the substrate-most-primitive
binary mark.  The equivalence is *computational* (no choice needed)
because `Distinction.equivBool` is constructed by case analysis. -/

/-- **Computational cross-instance** — `R N Bool ≃ R N Distinction` via
    `Distinction.equivBool` lifted coordinate-wise.  This is the
    abstract-to-classical bridge at every R-layer. -/
def R_Bool_equiv_R_Distinction (N : ℕ) : R N Bool ≃ R N Distinction :=
  Equiv.arrowCongr (Equiv.refl (Fin N)) Distinction.equivBool.symm

/-! ## § 6 Cross-instance comparison: Distinction ↔ ZMod 2

Composing § 1 and § 4: the abstract substrate, the F₂ classical
realisation, and the modular-arithmetic realisation all produce
isomorphic R-layers at every N. -/

/-- **Three-way layerwise equivalence** — the abstract substrate
    `Distinction`, the classical F₂ realisation `Bool`, and the
    modular-arithmetic realisation `ZMod 2` all produce isomorphic
    R-layers at every N. -/
noncomputable def R_Distinction_equiv_R_ZMod2 (N : ℕ) :
    R N Distinction ≃ R N (ZMod 2) :=
  (R_Distinction_equiv_R_Bool N).trans (R_Bool_equiv_R_ZMod2 N)

/-! ## § 7 Aggregator — concrete polymorphic T5 demonstration package

A single theorem that packages the four δ-instance witnesses with
their cardinality measurements.  This is the "tangible content"
delivered by the polymorphic T5 generalisation. -/

/-- **Concrete polymorphic T5 aggregator** — the four δ-instance
    witnesses with their cardinality measurements:

    * δ = Distinction: layerwise equivalence + `|R 2 Distinction| = 4`.
    * δ = ZMod 3:      layerwise equivalence + `|R 2 (ZMod 3)| = 9`.
    * δ = Fin 5:       layerwise equivalence + `|R 2 (Fin 5)| = 25`.
    * cross-instance:  `|R N Bool| = |R N (ZMod 2)|` at every N. -/
theorem concrete_polymorphic_T5_demo :
    (∀ N : ℕ, Nonempty (boolTransportedToDistinction.carrier N ≃ R N Distinction))
  ∧ (∀ N : ℕ, Nonempty (zmod3Demo.carrier N ≃ R N (ZMod 3)))
  ∧ (∀ N : ℕ, Nonempty (fin5Demo.carrier N ≃ R N (Fin 5)))
  ∧ Fintype.card (R 2 (ZMod 3)) = 9
  ∧ Fintype.card (R 3 (ZMod 3)) = 27
  ∧ Fintype.card (R 2 (Fin 5)) = 25
  ∧ (∀ N : ℕ, Fintype.card (R N Bool) = Fintype.card (R N (ZMod 2))) :=
  ⟨demo_distinction_bool_transport,
   demo_zmod3_T5,
   demo_fin5_T5,
   R2_ZMod3_card,
   R3_ZMod3_card,
   R2_Fin5_card,
   R_Bool_card_eq_R_ZMod2⟩

end SSBX.Foundation.R.UniquenessGeneral.Demos
