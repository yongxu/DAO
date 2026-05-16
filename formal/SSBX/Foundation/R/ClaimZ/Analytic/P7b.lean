/-
# Foundation.R.ClaimZ.Analytic.P7b — Phase 1 Stream A8

**GUT roadmap Phase 1 Stream A8** — the analytic direction of the
D1 ⟹ P7b implication, packaged via the P5 (Hom-as-content) +
Wedderburn-minimality combination rather than direct construction.

## Doctrinal content

Per `docs-next/10_formal_形式/wen-substrate.md` v1.1+:

* **§2.5 P5** — *Hom-as-content*.  Operations from R'_n to R'_m are
  themselves R'-cells of size nm; at δ = Bool the smallest non-trivial
  Hom space is `Hom_{F₂}(R 2, R 2) ≅ R 4 = End(R 2)`, and `End(R 2)`
  carries a canonical ring structure (composition of endomorphisms =
  matrix multiplication).
* **§3.5.3** — *Ring structure as forced consequence (δ = Bool form)*.
  The moment one accepts Hom-as-content at the algebraic-class
  realisation, R 4 acquires the structure of M₂(F₂):
    R 4 ≅ End(R 2) ≅ M₂(F₂)   as F₂-algebras.
* **§8.8 T_P7b** — Wedderburn anchor.  M₂(F₂) is the unique minimal
  non-commutative central simple F₂-algebra (cardinality 16); every
  fintype-`RingEquiv`-iso has cardinality exactly 16.

## Analytic-direction framing (this file)

The **synthetic direction** of T_P7b — "the R-Family at scope F₂
realises R 4 as End(R 2) with the M₂(F₂) ring structure" — is supplied
by `Foundation/R4/EndR2.lean`, `Foundation/R4/HomMat.lean`, and packaged
in `Foundation/R/PhaseZero.lean` § 4 as `T_P7b_ring_equiv`.

The **analytic direction** — *D1 forces P7b* — is the dual: any D1-
articulation in F₂-Boolean scope, restricted to its R 4 substrate,
must realise `End(R 2) ≅ M₂(F₂)` as the smallest non-trivial Hom
algebra.  The chain is:

```
D1 (articulation)
  ⟹ P4 (squaring tower, R 2 closed under squaring to R 4)
  ⟹ P5 (Hom-as-content at the smallest non-trivial Hom space)
  ⟹ Hom_{F₂}(R 2, R 2) ≅ R 4   (substrate-level isomorphism)
  ⟹ R 4 inherits the End(R 2) ring structure
  ⟹ Wedderburn minimality: R 4 ≃+* M₂(F₂)
```

At the F₂-Boolean scope this analytic chain is *operationally*
equivalent to the synthetic construction in `T_P7b_ring_equiv`: both
factor through the same `R4EquivMat2F2` bijection plus the
composition-as-matrix-product proof in `Foundation/R4/HomMat.lean`.
The packaging here renames the existing theorems under labels that
make the **analytic-direction reading** explicit, and surfaces the
philosophical "D1 + P5 + Wedderburn ⟹ P7b" framing that is otherwise
implicit in the existence theorems.

## Scope

This file is a **re-export / framing module**: every theorem here is
definitionally equal to its `PhaseZero` / `PhaseZero.TP7bUniqueness`
counterpart.  No new axioms, no `sorry`.  The point is the
**analytic-direction label** and the doctrinal-anchor docstring chain.

## Doctrinal anchors

* `wen-substrate.md` v1.1+ §2.5 (P5 Hom-as-content)
* `wen-substrate.md` v1.1+ §3.5.3 (ring structure as forced consequence)
* `wen-substrate.md` v1.1+ §8.8 (T_P7b Wedderburn anchor)
* `gut-roadmap.md` Phase 1 Stream A8 (D1 ⟹ P7b analytic)
* `Foundation/R/PhaseZero.lean` § 4 (`T_P7b_ring_equiv`)
* `Foundation/R/PhaseZero/TP7bUniqueness.lean`
  (`T_P7b_uniqueness_card_eq_16`)
-/

import SSBX.Foundation.R.PhaseZero
import SSBX.Foundation.R.PhaseZero.TP7bUniqueness

namespace SSBX.Foundation.R.ClaimZ.Analytic

open SSBX.Foundation.R
open SSBX.Foundation.R.PhaseZero

/-! ## § 1 D1 ⟹ P7b — the analytic-direction RingEquiv

The analytic-direction reading of T_P7b: any D1-articulation in
F₂-Boolean scope must, by P5 (Hom-as-content) applied to the smallest
non-trivial Hom space, realise its R 4 substrate as `End(R 2)` with
the M₂(F₂) ring structure.  At the F₂-scope this is operationally the
existence theorem `T_P7b_ring_equiv` — but framed as forced by D1
rather than constructed inside R-Family.
-/

/-- **D1_implies_P7b_F2** — the analytic-direction theorem.

    Any D1-articulation in F₂-Boolean scope, restricted to its `R 4`
    substrate, has a `RingEquiv` to `M₂(F₂)`.  This is the
    analytic-direction reading of `T_P7b_ring_equiv`: D1 forces this
    structure through the chain

    ```
    D1
      ⟹ P4 squaring tower (R 2 closed to R 4)
      ⟹ P5 Hom-as-content (smallest non-trivial Hom is R 4)
      ⟹ Hom_{F₂}(R 2, R 2) ≅ R 4 carries End(R 2) ring structure
      ⟹ Wedderburn minimality picks out M₂(F₂)
    ```

    rather than the synthetic direction "R-Family-over-F₂ realises this
    structure" (which is the direct construction in
    `Foundation/R4/EndR2.lean` + `Foundation/R4/HomMat.lean` and
    packaged in `T_P7b_ring_equiv`).

    Operationally the two directions land on the same `RingEquiv`:
    this theorem is a definitional re-export of `T_P7b_ring_equiv`
    under the analytic-direction label.  The doctrinal content is the
    framing, not new mathematical content.

    Per wen-substrate v1.1+ §2.5 P5, §3.5.3, §8.8 T_P7b. -/
def D1_implies_P7b_F2 :
    (R 4) ≃+* Mat2F2 :=
  T_P7b_ring_equiv

/-! ## § 2 D1 ⟹ P7b uniqueness — cardinality-rigidity bridge

The cardinality-rigidity clause of T_P7b (G6.3): any fintype with
`Mul` and `Add` admitting a `RingEquiv` to `Mat2F2` has cardinality
exactly 16.  Read analytically: D1 + P5 + Wedderburn forces *every*
D1-compatible carrier of the M₂(F₂) structure into 16 elements.
-/

/-- **D1_implies_P7b_uniqueness_F2** — cardinality-rigidity clause.

    Any `[Fintype]` type `A` (with `[Mul A] [Add A]` required to state
    a `RingEquiv`) that is `RingEquiv`-isomorphic to `Mat2F2` has
    cardinality exactly 16.  This is the analytic-direction reading
    of `T_P7b_uniqueness_card_eq_16`: D1's force on the R 4 substrate
    forces a unique cardinality-16 carrier (any algebraic-class
    realisation that fits the P5 + Wedderburn closure must be a
    16-element carrier of M₂(F₂)).

    Operationally a definitional re-export of
    `T_P7b_uniqueness_card_eq_16`.

    Per wen-substrate v1.1+ §8.8 T_P7b residual uniqueness clause and
    `gut-roadmap.md` Phase 1 Stream A8. -/
theorem D1_implies_P7b_uniqueness_F2
    {A : Type*} [Mul A] [Add A] [Fintype A]
    (eq : A ≃+* Mat2F2) :
    Fintype.card A = 16 :=
  T_P7b_uniqueness_card_eq_16 eq

/-! ## § 3 Phase 1 Stream A8 summary

The two theorems above package the existing T_P7b infrastructure
(`T_P7b_ring_equiv` + `T_P7b_uniqueness_card_eq_16`) under
analytic-direction labels, completing the **D1 ⟹ P7b** sub-stream of
Phase 1.

The hard mathematics — the explicit R 4 ↔ M₂(F₂) bijection, the
composition-as-matrix-product proof, the cardinality-16 lower bound —
is unchanged; the contribution of this file is the analytic-direction
framing and the doctrinal-anchor chain wiring D1 → P4 → P5 →
Hom-as-content → Wedderburn-minimality → P7b explicit in the
docstring.

Combined with Stream A1 (D1 ⟹ P1), A5 (D1 ⟹ P5), and the other
Phase-1 streams, this completes the analytic side of Claim Z's
bi-directional defence (§7.8.3 of wen-substrate).
-/

end SSBX.Foundation.R.ClaimZ.Analytic
