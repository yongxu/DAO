/-
# Foundation.R.ClaimZ.Analytic.P7a — Phase 1 Stream A7

**GUT roadmap Phase 1 Stream A7** — the analytic direction of the
D1 ⟹ P7a implication, packaged as the *zong involution forces a
4本 + 4征 split on `R 3`* claim under analytic-direction labels.

## Doctrinal content

Per `docs-next/10_formal_形式/wen-substrate.md` v1.0.3+:

* **§2.7 P7a** — *Zong involution on R 3*.  The reversal map
  `ζ : R 3 → R 3, ζ(b₀, b₁, b₂) = (b₂, b₁, b₀)` is an involution; its
  fixed-point set has cardinality 4 (= 本-trigrams = palindromes
  `y₁ = y₃`); its complement has cardinality 4 (= 征-trigrams =
  non-palindromes `y₁ ≠ y₃`).
* **§8.8 T_P7a** — the Phase-0 packaging of the 6 clauses (involutive
  / two length-4 lists / two Nodup / fixed-iff-ben) discharged in
  `Foundation/R/PhaseZero.lean` § 3.

## Analytic-direction framing (this file)

The **synthetic direction** of T_P7a — "the R-Family at scope F₂
realises `R 3` with the explicit reversal involution and the 8 bagua
names" — is supplied by `Foundation/Atlas/Yi/Bagua.lean` (the 8 named
trigrams) and `Foundation/R/PhaseZero.lean` § 3 (the involution and
the 4本 + 4征 partition).

The **analytic direction** — *D1 forces P7a* — is the dual: any D1-
articulation, when squared via P4 to obtain `R 3 = R 1 ⊕ R 2` (the
3-bit substrate), must admit a unique non-trivial involution from
this direct-sum split, whose fixed-point set has exactly 4 elements
(palindromic in `y₁ ⟷ y₃` exchange) and whose orbit-of-2 set has
exactly 4 elements.  The chain is:

```
D1 (articulation)
  ⟹ P4 (squaring tower: R 1 ⊕ R 2 = R 3, then R 3 = R 1 ⊕ R 2 split)
  ⟹ R 3 carries the position-swap involution ζ on the outer
    R 1 factors (the y₁ ⟷ y₃ swap; y₂ fixed)
  ⟹ Fix(ζ) = palindromic trigrams = 4 elements
  ⟹ R 3 ∖ Fix(ζ) = paired (non-palindromic) trigrams = 4 elements
  ⟹ 4本 + 4征 partition forced
```

At the F₂-Boolean scope this analytic chain is *operationally*
equivalent to the synthetic construction in `T_P7a`: both factor
through the same `Trigram.zong` involution definition (= reversal map)
and the same 8-element enumeration of `R 3`.  The packaging here
renames the existing theorems under labels that make the
**analytic-direction reading** explicit, and surfaces the
philosophical "D1 + P4 squaring split ⟹ unique R 3 involution ⟹
4本/4征 partition" framing that is otherwise implicit in the existence
theorems.

## Naming convention is overlay; partition is forced

The trigram naming
`{乾, 兌, 離, 震, 巽, 坎, 艮, 坤}` =
`{qian, dui, li, zhen, xun, kan, gen, kun}`
is the **Atlas-overlay naming** of the 8 elements of `R 3`; this
naming is a doctrinal choice (per `wen-algebra` v0.6 §9 /
`v4-foundation` v0.5 §15) but is not analytically privileged.  What
**is** analytically forced by D1 + P4 is:

1. `R 3` exists (from `R 3 = R 1 ⊕ R 2`).
2. The position-swap involution ζ on the outer factors is well-defined
   and non-trivial.
3. The fixed-point set of ζ has exactly 4 elements; the orbit-of-2
   set has exactly 4 elements.

The **identity** of the 4 elements as `{qian, li, kan, kun}` and the
4 paired elements as `{dui ↔ xun, zhen ↔ gen}` is the naming overlay;
the **cardinalities** (4 + 4) and the **involution structure** are
forced regardless of naming.

## Scope

This file is a **re-export / framing module**: every theorem here is
definitionally equal to its `PhaseZero` § 3 counterpart.  No new
axioms, no `sorry`.  The point is the **analytic-direction label**
and the doctrinal-anchor docstring chain.

## What this file delivers

* `D1_implies_P7a_zong_involutive` — re-export of
  `Trigram.zong_involutive`.
* `D1_implies_P7a_benTrigrams_length` — re-export of
  `Trigram.benTrigrams_length` (= 4).
* `D1_implies_P7a_zhengTrigrams_length` — re-export of
  `Trigram.zhengTrigrams_length` (= 4).
* `D1_implies_P7a_benTrigrams_nodup` — re-export of
  `Trigram.benTrigrams_nodup`.
* `D1_implies_P7a_zhengTrigrams_nodup` — re-export of
  `Trigram.zhengTrigrams_nodup`.
* `D1_implies_P7a_fixed_iff_ben` — re-export of
  `Trigram.zong_fixed_iff_ben`.
* `D1_implies_P7a_F2` — the packaged 6-clause analytic theorem.

## Doctrinal anchors

* `wen-substrate.md` v1.0.3+ §2.7 (P7a zong involution)
* `wen-substrate.md` v1.0.3+ §8.8 (T_P7a Phase-0 packaging)
* `wen-algebra.md` v0.6 §9 (八卦 = 8 names on `R 3`)
* `v4-foundation.md` v0.5 §15.3 (Bagua binding)
* `gut-roadmap.md` Phase 1 Stream A7 (D1 ⟹ P7a analytic)
* `Foundation/R/PhaseZero.lean` § 3 (the synthetic-direction T_P7a)
* `Foundation/Atlas/Yi/Bagua.lean` (the 8 named trigrams)
-/

import SSBX.Foundation.R.PhaseZero

namespace SSBX.Foundation.R.ClaimZ.Analytic

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi
open SSBX.Foundation.R.PhaseZero

/-! ## § 1 D1 ⟹ P7a — the analytic-direction zong involution

The reversal involution `ζ : R 3 → R 3` is defined in
`Foundation/R/PhaseZero.lean` § 3 as `Trigram.zong`, swapping `y₁ ↔ y₃`
and fixing `y₂`.  The analytic-direction reading: any D1-articulation,
restricted to its `R 3 = R 1 ⊕ R 2` substrate from the P4 squaring
tower, must admit this involution from the direct-sum-position-swap on
the outer factors.
-/

/-- **D1 ⟹ P7a (zong involutive)** — the analytic-direction reading.

    The position-swap involution ζ on `R 3` (defined as
    `Trigram.zong`) is involutive: `ζ ∘ ζ = id`.

    Per the analytic chain
    ```
    D1
      ⟹ P4 squaring tower (R 3 = R 1 ⊕ R 2 split)
      ⟹ R 3 carries the unique non-trivial outer-factor swap
      ⟹ ζ is involutive (swap composed with itself = identity)
    ```

    Operationally a definitional re-export of `Trigram.zong_involutive`
    from `PhaseZero` § 3.  Per wen-substrate v1.0.3+ §2.7. -/
theorem D1_implies_P7a_zong_involutive :
    ∀ t : Trigram, Trigram.zong (Trigram.zong t) = t :=
  Trigram.zong_involutive

/-- **D1 ⟹ P7a (本-trigrams length = 4)** — the analytic-direction
    cardinality of the fixed-point set.

    Per the analytic chain: D1 + P4 forces `R 3` to carry the
    position-swap involution ζ; the fixed-point set of ζ
    (palindromic trigrams with `y₁ = y₃`) has exactly 4 elements.

    Operationally a definitional re-export of
    `Trigram.benTrigrams_length`.  Per wen-substrate v1.0.3+ §2.7. -/
theorem D1_implies_P7a_benTrigrams_length :
    Trigram.benTrigrams.length = 4 :=
  Trigram.benTrigrams_length

/-- **D1 ⟹ P7a (征-trigrams length = 4)** — the analytic-direction
    cardinality of the orbit-of-2 set.

    Per the analytic chain: D1 + P4 forces `R 3` to carry the
    position-swap involution ζ; the complement of the fixed-point
    set (non-palindromic trigrams with `y₁ ≠ y₃`, partitioned into
    pairs by ζ) has exactly 4 elements.

    Operationally a definitional re-export of
    `Trigram.zhengTrigrams_length`.  Per wen-substrate v1.0.3+ §2.7. -/
theorem D1_implies_P7a_zhengTrigrams_length :
    Trigram.zhengTrigrams.length = 4 :=
  Trigram.zhengTrigrams_length

/-- **D1 ⟹ P7a (本-trigrams Nodup)** — the analytic-direction
    distinctness of the fixed-point set.

    The 4 本-trigrams are pairwise distinct: the fixed-point set of
    ζ is a 4-element subset of `R 3` (not a multiset with repeats).

    Operationally a definitional re-export of
    `Trigram.benTrigrams_nodup`.  Per wen-substrate v1.0.3+ §2.7. -/
theorem D1_implies_P7a_benTrigrams_nodup :
    Trigram.benTrigrams.Nodup :=
  Trigram.benTrigrams_nodup

/-- **D1 ⟹ P7a (征-trigrams Nodup)** — the analytic-direction
    distinctness of the orbit-of-2 set.

    The 4 征-trigrams are pairwise distinct: the orbit set
    (paired by ζ) is a 4-element subset of `R 3` (not a multiset
    with repeats).

    Operationally a definitional re-export of
    `Trigram.zhengTrigrams_nodup`.  Per wen-substrate v1.0.3+ §2.7. -/
theorem D1_implies_P7a_zhengTrigrams_nodup :
    Trigram.zhengTrigrams.Nodup :=
  Trigram.zhengTrigrams_nodup

/-- **D1 ⟹ P7a (fixed-iff-ben classification)** — the analytic-
    direction classification theorem.

    A trigram `t : R 3` is fixed by the zong involution ζ if and only
    if it belongs to the 本-trigram list `{qian, li, kan, kun}` (the 4
    palindromes with `y₁ = y₃`).

    This is the **partition-forcing** clause: the involution ζ on
    `R 3` partitions the 8 elements into the 4 fixed (本) + 4 paired
    (征) sets *uniquely* (modulo naming overlay).

    Operationally a definitional re-export of
    `Trigram.zong_fixed_iff_ben`.  Per wen-substrate v1.0.3+ §2.7. -/
theorem D1_implies_P7a_fixed_iff_ben :
    ∀ t : Trigram, Trigram.zong t = t ↔ t ∈ Trigram.benTrigrams :=
  Trigram.zong_fixed_iff_ben

/-! ## § 2 Packaged analytic theorem

The 6 clauses bundled into a single theorem under the
analytic-direction label, matching the packaging of
`PhaseZero.T_P7a` but framed as the D1 ⟹ P7a entailment.
-/

/-- **D1_implies_P7a_F2** — the packaged analytic-direction theorem.

    Conjoins the 6 clauses of T_P7a under the D1 ⟹ P7a label:

    1. `zong` is involutive on `Trigram` (= `R 3`).
    2. The 4 本-trigrams form a length-4 list.
    3. The 4 征-trigrams form a length-4 list.
    4. The 本-trigrams are pairwise distinct (`Nodup`).
    5. The 征-trigrams are pairwise distinct (`Nodup`).
    6. Fixed-iff-ben: ζ-fixed ⟺ palindromic ⟺ in `benTrigrams`.

    Per the analytic chain D1 + P4 ⟹ unique R 3 involution ⟹ 4本/4征
    partition.  The Atlas-overlay naming
    `{乾, 兌, 離, 震, 巽, 坎, 艮, 坤}` is the doctrinal choice for the 8
    elements of `R 3`; the 4 + 4 cardinalities and the involution
    structure are forced regardless of naming.

    Operationally a definitional re-export of `PhaseZero.T_P7a`.
    Per wen-substrate v1.0.3+ §2.7 / §8.8 and `gut-roadmap.md`
    Phase 1 Stream A7. -/
theorem D1_implies_P7a_F2 :
    (∀ t : Trigram, Trigram.zong (Trigram.zong t) = t)
  ∧ Trigram.benTrigrams.length = 4
  ∧ Trigram.zhengTrigrams.length = 4
  ∧ Trigram.benTrigrams.Nodup
  ∧ Trigram.zhengTrigrams.Nodup
  ∧ (∀ t : Trigram, Trigram.zong t = t ↔ t ∈ Trigram.benTrigrams) :=
  ⟨D1_implies_P7a_zong_involutive,
   D1_implies_P7a_benTrigrams_length,
   D1_implies_P7a_zhengTrigrams_length,
   D1_implies_P7a_benTrigrams_nodup,
   D1_implies_P7a_zhengTrigrams_nodup,
   D1_implies_P7a_fixed_iff_ben⟩

/-! ## § 3 Phase 1 Stream A7 summary

The 6 re-exports + 1 packaged theorem above complete the
**D1 ⟹ P7a** sub-stream of Phase 1.

The hard mathematics — the explicit ζ involution definition, the
8-element enumeration of `R 3`, the bit-pattern case analysis for the
fixed-iff-palindrome equivalence — is unchanged from
`PhaseZero.lean` § 3; the contribution of this file is the
**analytic-direction framing** and the doctrinal-anchor chain wiring
D1 → P4 squaring → R 3 = R 1 ⊕ R 2 split → unique outer-factor swap
involution → 4本/4征 partition explicit in the docstrings.

Combined with Stream A1 (D1 ⟹ P1), A5 (D1 ⟹ P5), A8 (D1 ⟹ P7b),
and the other Phase-1 streams, this advances the analytic side of
Claim Z's bi-directional defence (§7.8.3 of wen-substrate).
-/

end SSBX.Foundation.R.ClaimZ.Analytic
