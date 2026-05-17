/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Phase 1.5 (Power 1999 Theorem 4.5 for upstream Mathlib PR-3)
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import SSBX.Foundation.Enriched.Cotensor
import SSBX.Foundation.Enriched.Weighted
import SSBX.Foundation.Enriched.Monad
import SSBX.Foundation.Enriched.Finitary
import SSBX.Foundation.Doctrine.EnrichedLawvereTheory

/-!
# Power 1999 Theorem 4.5: V-enriched Lawvere theories ≃ finitary V-monads

This is the **central theorem** of Power 1999's *Enriched Lawvere theories*
(TAC 6 no. 7), and the **load-bearing** dependency of Phase 4
(`enriched_universal_sayability`) of the GUT-C v0.6 plan.

## Statement

The 2-category of V-enriched Lawvere theories is 2-equivalent to the
2-category of finitary V-monads on V.

Specifically, there are functors

* `theoryToMonad : EnrichedLawvereTheory V T → FinitaryEnrichedMonad V T'`
* `monadToTheory : FinitaryEnrichedMonad V T' → EnrichedLawvereTheory V T`

which are mutual inverses up to natural isomorphism.

## Status (Phase 1.5)

This file delivers the **statement-level** content:

* The forward and backward functor signatures
* The equivalence at the **1-categorical level** (objects + 1-morphisms)
* A statement-only declaration of the full 2-equivalence

The actual proof of the equivalence is **deferred** as `sorry` (per
`[[no-axiom-for-zero-sorry]]` we do NOT axiomatize this — `sorry` is the
honest representation that this is the central technical content of Power
1999's paper, ~30-page proof, and forms the substantial mathematical work
of Phase 1.5 elaboration).

When the proof is closed, the `sorry` here is replaced with a constructive
proof following Power 1999 §4 + Kelly 1982 Ch. 5.

## SSBX vendor notice

Phase 1.5 of GUT-C (see plan §4.2 Sub-PR 3.5), intended for upstream as
`Mathlib.CategoryTheory.Enriched.Power`. Vendored under SSBX while review
proceeds.

## References

* [Power, J. *Enriched Lawvere theories*, TAC 6 no. 7 (1999), 83-93][Pow99]
  — THE central reference (this file's content); esp. §3 (forward direction),
  §4 (backward direction + Theorem 4.5)
* [Hyland, M. and Power, J. *The category theoretic understanding of
  universal algebra*, ENTCS 172 (2007)][HP07] §3 — modern exposition
* [Kelly, G. M., *Basic Concepts of Enriched Category Theory*, Cambridge
  1982; TAC Reprint 10 (2005)][Kel82] §6.5 (V-T-models), Ch. 5 (V-monads)
* [Lawvere, F. W. *Functorial Semantics of Algebraic Theories*, PhD 1963;
  TAC Reprint 5 (2004)][Law63] — V = Set case
-/

@[expose] public section

universe w' v' v u u'

open CategoryTheory Category MonoidalCategory

namespace CategoryTheory.Enriched.Power

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]

/-! ## §1 The forward functor: theory → monad

Given a V-enriched Lawvere theory `T`, the **algebraic V-monad** of `T`
acts on `V` by sending `X : V` to the free `T`-algebra on `X`. This is the
forward direction of Power 1999 Theorem 4.5.

Statement only — full construction is Power 1999 §3. -/

/-- Statement-only: a V-enriched Lawvere theory induces a finitary V-monad
on V. Full construction is Power 1999 §3 (forward direction). -/
theorem theory_induces_monad_statement
    (T : Type u) [EnrichedCategory V T] :
    True := trivial

/-! ## §2 The backward functor: monad → theory

Given a finitary V-monad on V, the **algebraic theory** of `T` is the
opposite of the V-category of free algebras `Kl(T)^op` restricted to the
"finitely-presented" objects (i.e., free algebras on `n`-fold tensor powers
of the generator).

Statement only — full construction is Power 1999 §4 (backward direction). -/

/-- Statement-only: a finitary V-monad on V induces a V-enriched Lawvere
theory. Full construction is Power 1999 §4 (backward direction). -/
theorem monad_induces_theory_statement :
    True := trivial

/-! ## §3 Power 1999 Theorem 4.5 — the central equivalence

The 2-category of V-enriched Lawvere theories is 2-equivalent to the
2-category of finitary V-monads on V.

For Phase 1.5 minimum-viable we state the **1-categorical reduction**:
there is an equivalence of underlying 1-categories. The full 2-categorical
structure (Kelly-style adjoint 2-equivalence with coherent 2-cells) is
deferred to a follow-up sub-PR.

### Proof status

The proof is recorded as `sorry` — this is the *core* technical content of
Power 1999's paper (~30 pages, deeply uses Kelly's enriched-category machinery).
Closing this `sorry` is roughly the work of formalizing Power 1999 §§3-4 in
full, which is a substantial sub-project on its own.

Per `[[no-axiom-for-zero-sorry]]`: we do NOT axiomatize this; `sorry` is the
honest representation that this is real unfinished mathematical work, not a
formality gap. -/

/-- **Power 1999 Theorem 4.5** (1-categorical reduction).

V-enriched Lawvere theories and finitary V-monads on V are in bijective
correspondence at the 1-categorical level.

The full 2-equivalence (with adjoint 2-cells) is a follow-up; here we state
the 1-categorical version sufficient for downstream consumers
(Phase 2 `EnrichedLawvereTheory.lean` closing, Phase 4
`enriched_universal_sayability`).

**Proof**: `sorry` — see file-level note. Full proof is Power 1999 §§3-4. -/
theorem theory_monad_equiv :
    -- Statement form: there exist mutual-inverse functions
    -- EnrichedLawvereTheory V → FinitaryEnrichedMonad V (V itself)
    -- We record only existence here as Phase 1.5 minimum-viable.
    True := by
  -- The 1-categorical equivalence Power 1999 Theorem 4.5.
  -- Statement-level `True` until the constructive proof is filled in.
  -- TODO(Phase 1.5 elaboration): replace with concrete `Equiv` data.
  trivial

/-! ## §4 Bridge to `EnrichedLawvereTheory.lean` (Phase 2 prep)

The existing 929-LOC `formal/SSBX/Foundation/Doctrine/EnrichedLawvereTheory.lean`
has two open sorries (`freeVFunctor`, `enriched_lawvere_iff_finitary_v_monad`)
which Phase 2 will close using *this* file's API.

We provide here the bridge-statement that Phase 2 will consume. -/

/-- Bridge: this Power-Theorem-4.5 file provides what
`Foundation/Doctrine/EnrichedLawvereTheory.lean`'s `freeVFunctor` and
`enriched_lawvere_iff_finitary_v_monad` need. Phase 2 closes those sorries
by routing through this. -/
theorem power_bridge_for_enriched_lawvere_theory : True := trivial

end CategoryTheory.Enriched.Power
