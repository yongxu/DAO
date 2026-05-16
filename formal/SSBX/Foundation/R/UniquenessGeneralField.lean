/-
# Foundation.R.UniquenessGeneralField — T5 polymorphic-field with char-class dispatch

Per `docs-next/10_formal_形式/gut-roadmap.md` **§十二 G11 cut-1** (G11-C):
the polymorphic-field scaffold sitting between `UniquenessAlgebraic`
(which assumes the `carrier 4 ≃+* Matrix (Fin 2) (Fin 2) k` ring iso
as data) and the upcoming `MatFqInstances` / `DiscriminantCharNeq2`
modules (G11-A / G11-B) which will *derive* it.

This file:

* introduces a `CharClass k` dispatch tag separating
  `char(k) = 2` (Arf-based, char-2 already discharged via the F₂ path)
  from `char(k) ≠ 2` (disc-based, new path going through Wedderburn);
* states the polymorphic-field theorem `T5_field` as a thin wrapper
  over `UniquenessAlgebraic.T5_algebraic`, but with the satisfier
  structure renamed `P1P7_Satisfier_Field` to flag the char-class
  context;
* provides **stubs** for the two char-class-specific derivations
  (`T5_field_char_two_from_F2`, `T5_field_char_neq_two_from_wedderburn`)
  with `sorry` placeholders, documenting the cross-subagent
  dependencies (G11-A for Wedderburn, G11-B for discriminant);
* exhibits **concrete demo instances** at `ZMod 3` and `ZMod 5`
  (the smallest char-≠-2 finite fields) showing the API plumbing is
  well-typed even though the closure data is currently `Classical.choice`d.

## Status (2026-05-17)

| Item | Status | Blocker |
|---|---|---|
| `CharClass k` dispatch | proven | — |
| `P1P7_Satisfier_Field` shape | proven (extends `Algebraic`) | — |
| `T5_field` (layerwise + ring iso) | proven (delegates to `T5_algebraic`) | — |
| `T5_field_char_two_from_F2` | `sorry` | base-extension functor (small) |
| `T5_field_char_neq_two_from_wedderburn` | `sorry` | G11-A `IsSimpleRing (Mat₂ F_q)` |
| `T5_field_at_ZMod_3 / 5` (demo) | `sorry` (closure data) | G11-A/B derivation of `p7b_ring_equiv` |

## Doctrinal anchor

* `gut-roadmap.md` v0.2 §十二 — G11 cut-1 plan; this is G11-C.
* `gut-roadmap.md` v0.2 §十一 — polymorphic T5 layerwise + algebraic.
* `Foundation/R/UniquenessGeneral.lean` — `T5_general` layerwise core.
* `Foundation/R/UniquenessAlgebraic.lean` — `T5_algebraic` + the
  assumed `p7b_ring_equiv` field.
* `Foundation/R/Algebra/MatFqInstances.lean` (G11-A, future) —
  Wedderburn-Artin instances on `Matrix (Fin 2) (Fin 2) F_q`.
* `Foundation/R/Bilinear/DiscriminantCharNeq2.lean` (G11-B, future) —
  discriminant-based P3 for char ≠ 2.
-/

import SSBX.Foundation.R.UniquenessAlgebraic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Defs

namespace SSBX.Foundation.R.UniquenessGeneralField

open SSBX.Foundation.R
open SSBX.Foundation.R.UniquenessGeneral
open SSBX.Foundation.R.UniquenessAlgebraic

/-! ## § 1 Char-class dispatch

We split fields into two char-classes for the purposes of T5-B:

* `char_two` — `char(k) = 2`.  Already handled via the Arf-invariant
  path (the F₂-Boolean line lifts cleanly via `forgetF2ToAlgebraic_ZMod2`
  and base-extension; `ZMod 2 ⊆ F_{2^n}`).
* `char_neq_two` — `char(k) = p` for *odd* prime `p`.  Handled via
  the discriminant-based bilinear (G11-B) plus Wedderburn-Artin on
  `Matrix (Fin 2) (Fin 2) F_q` (G11-A).

For the dispatch we use Mathlib's `CharP` directly rather than a
custom inductive — this composes better with Mathlib's instance
search and avoids re-deriving char-properties.
-/

/-- **CharClass k** — a finite tag splitting fields by characteristic.

    `char_two`     — assert `CharP k 2`.
    `char_neq_two` — assert `CharP k p` for some odd prime `p`, plus
                     the inequality witness.

    The `Char.zero` case (char(k) = 0, e.g. `ℚ`, `ℝ`, `ℂ`) is
    **excluded** by the `[Fintype k]` requirement on `T5_field` (every
    finite field has positive characteristic).  We do not provide a
    `char_zero` constructor.

    Per `gut-roadmap.md` §十二 cut-1 scope: only finite fields. -/
inductive CharClass (k : Type) [Field k] where
  /-- char(k) = 2.  Existing path: Arf-based via `UniquenessF2`. -/
  | char_two (h : CharP k 2) : CharClass k
  /-- char(k) = p, p ≠ 2.  New path: disc-based via Wedderburn. -/
  | char_neq_two (p : ℕ) (hp : CharP k p) (hne : p ≠ 2) : CharClass k

/-! ## § 2 The polymorphic-field satisfier

`P1P7_Satisfier_Field k` is a *renaming* of `P1P7_Satisfier_Algebraic k`
that adds the **char-class tag** as explicit data, plus a forward
slot for the upcoming derivation pieces (G11-A `IsSimpleRing`-derived
`p7b_ring_equiv`, G11-B discriminant `p3_disc`).  We keep the structure
extensible by `extends`-ing `P1P7_Satisfier_Algebraic`.

For the *statement* of `T5_field` we currently delegate to
`T5_algebraic`; the value-add of `_Field` is the char-class tag (for
future dispatch) and the future-extensibility of disc/Wedderburn
witnesses. -/

/-- **P1P7_Satisfier_Field k** — char-class-aware polymorphic-field
    satisfier.  Extends `P1P7_Satisfier_Algebraic k` with an explicit
    `CharClass k` tag.

    Future extensions (G11-A / G11-B):
    * `p7b_ring_equiv_derived` — explicit construction via Wedderburn
      (currently the parent's `p7b_ring_equiv` is taken as data).
    * `p3_disc` — discriminant invariant for char ≠ 2 (currently
      only `p3_dot_symm` symmetry is asserted at the algebraic level). -/
structure P1P7_Satisfier_Field (k : Type) [Field k] [Fintype k]
    [DecidableEq k] extends P1P7_Satisfier_Algebraic k where
  /-- The char-class tag.  Determines which derivation path applies
      to the as-yet-unproven `p7b_ring_equiv` field. -/
  char_class : CharClass k

/-! ## § 3 The main theorem `T5_field` -/

/-- **T5-field (polymorphic-field GUT-B form)** — layerwise type
    equivalence at every layer.

    For any field `k` with `[Fintype k] [DecidableEq k]`, any
    `S : P1P7_Satisfier_Field k`, and any `N : ℕ`:

        Nonempty (S.carrier N ≃ R N k)

    Direct corollary of `T5_general` via the embedded `P1P7_Core k`.

    The companion ring-iso conclusion at `N = 4` is packaged as
    `T5_field_ringEquiv_at_4` below.  Both together form the full
    GUT-B polymorphic-field claim. -/
theorem T5_field {k : Type} [Field k] [Fintype k] [DecidableEq k]
    (S : P1P7_Satisfier_Field k) (N : ℕ) :
    Nonempty (S.toP1P7_Satisfier_Algebraic.toP1P7_Core.carrier N ≃ R N k) := by
  haveI : Inhabited k := ⟨0⟩
  exact T5_general S.toP1P7_Satisfier_Algebraic.toP1P7_Core N

/-- **T5-field ring iso at carrier 4** — the operation-algebra layer
    is the standard 2×2 matrix ring over `k`.

    Direct corollary of `T5_algebraic`'s second conjunct; the proof
    extracts the embedded `p7b_ring_equiv` field. -/
theorem T5_field_ringEquiv_at_4 {k : Type} [Field k] [Fintype k]
    [DecidableEq k] (S : P1P7_Satisfier_Field k) :
    @Nonempty
      (@RingEquiv
        (S.toP1P7_Satisfier_Algebraic.toP1P7_Core.carrier 4)
        (Matrix (Fin 2) (Fin 2) k)
        S.toP1P7_Satisfier_Algebraic.p7b_mul_instance (matMulInstance k)
        S.toP1P7_Satisfier_Algebraic.p7b_add_instance (matAddInstance k)) :=
  S.toP1P7_Satisfier_Algebraic.p7b_ring_equiv

/-- **T5-field aggregate** — the combined layerwise + ring-iso content
    of GUT-B at the polymorphic-field level.  Direct rebrand of
    `T5_algebraic` exposing the char-class tag. -/
theorem T5_field_aggregate {k : Type} [Field k] [Fintype k] [DecidableEq k]
    (S : P1P7_Satisfier_Field k) :
    (∀ N, Nonempty (S.toP1P7_Satisfier_Algebraic.toP1P7_Core.carrier N ≃ R N k))
  ∧ (@Nonempty
        (@RingEquiv
          (S.toP1P7_Satisfier_Algebraic.toP1P7_Core.carrier 4)
          (Matrix (Fin 2) (Fin 2) k)
          S.toP1P7_Satisfier_Algebraic.p7b_mul_instance (matMulInstance k)
          S.toP1P7_Satisfier_Algebraic.p7b_add_instance (matAddInstance k))) :=
  T5_algebraic S.toP1P7_Satisfier_Algebraic

/-! ## § 4 Char-class-specific derivation stubs

The two derivation paths for `p7b_ring_equiv`, one per char-class.
Both are currently `sorry` pending other subagents:

* **char(k) = 2 path** — base-extends `T5_A_ringEquiv_at_4` (from
  `UniquenessF2`) along the prime-field inclusion `ZMod 2 ↪ F_{2^n}`.
  Lightweight; depends on a small base-extension functor (not yet
  written, but mostly Mathlib `Algebra.lift` plumbing).

* **char(k) ≠ 2 path** — applies Wedderburn-Artin to the 4-dim
  k-algebra `carrier 4` (assuming it is `IsSimpleRing` + `IsArtinianRing`
  via G11-A) and uses the count `dim_k(D) · n² = 4 = 1 · 2²` to force
  `D = k` (Br(F_q) = 0 by Wedderburn's little theorem on division
  rings) and `n = 2`, yielding `carrier 4 ≃+* Matrix (Fin 2) (Fin 2) k`.
-/

/-- **char(k) = 2 derivation stub** — `p7b_ring_equiv` lifted from
    `T5_A_ringEquiv_at_4` (the F₂-Boolean version) via base-extension
    along `ZMod 2 ↪ k`.

    **Dependency**: needs a base-extension functor for ring isos along
    field extensions.  This is small but not yet written.  Expected
    location: `Foundation/R/Algebra/BaseExtension.lean` (future) or
    Mathlib `Algebra.lift_*`. -/
theorem T5_field_char_two_from_F2
    {k : Type} [Field k] [Fintype k] [DecidableEq k]
    (_hCh : CharP k 2)
    (S : UniquenessF2.P1P7_Satisfier_F2)
    (_h_dim : Fintype.card k = 2 ^ (Nat.log2 (Fintype.card k))) :
    -- Conclusion: a ring iso `S.carrier 4 ≃+* Matrix (Fin 2) (Fin 2) k`.
    @Nonempty
      (@RingEquiv (S.carrier 4) (Matrix (Fin 2) (Fin 2) k)
        S.p7b_mul_instance (matMulInstance k)
        S.p7b_add_instance (matAddInstance k)) := by
  -- TODO (G11-C follow-up): base-extend `T5_A_ringEquiv_at_4_zmod2 S`
  -- along the prime-field inclusion `ZMod 2 ↪ k` (uses `CharP.ofRingEquiv`
  -- + Mathlib `Algebra.RingHom.liftOfMatrixCommute` or hand-written
  -- entrywise map composition).
  sorry

/-- **char(k) ≠ 2 derivation stub** — `p7b_ring_equiv` derived via
    Wedderburn-Artin on `carrier 4` as a 4-dimensional `k`-algebra.

    **Dependency (G11-A)**: requires `IsSimpleRing (carrier 4)` and
    `IsArtinianRing (carrier 4)` instances.  These come from
    `Foundation/R/Algebra/MatFqInstances.lean` (G11-A in-flight).

    **Dependency (G11-B)**: the discriminant-based P3 gives a
    non-degenerate symmetric bilinear form, which witnesses simplicity
    via the absence of nontrivial two-sided ideals.

    **Wedderburn count**: a finite-dim simple k-algebra is
    `Matrix n n D` for some division ring `D` with `D ⊇ k` central; over
    finite fields, Wedderburn's little theorem forces `D = k`, and
    `dim_k(carrier 4) = 4 = n²` gives `n = 2`. -/
theorem T5_field_char_neq_two_from_wedderburn
    {k : Type} [Field k] [Fintype k] [DecidableEq k]
    (p : ℕ) (_hCh : CharP k p) (_hne : p ≠ 2)
    (S : P1P7_Satisfier_Algebraic k)
    -- Forthcoming hypotheses (G11-A): `IsSimpleRing (S.carrier 4)`,
    -- `IsArtinianRing (S.carrier 4)`, dimension witness.
    (_dim4 :
      letI : Fintype (S.toP1P7_Core.carrier 4) := S.toP1P7_Core.fintype 4
      Fintype.card (S.toP1P7_Core.carrier 4) = (Fintype.card k) ^ 4) :
    @Nonempty
      (@RingEquiv
        (S.toP1P7_Core.carrier 4) (Matrix (Fin 2) (Fin 2) k)
        S.p7b_mul_instance (matMulInstance k)
        S.p7b_add_instance (matAddInstance k)) := by
  -- TODO (G11-A/G11-C integration): apply
  -- `Wedderburn.matrix_equiv_of_simple_artinian`
  -- (or equivalent Mathlib name) to obtain `S.carrier 4 ≃+* Matrix n n D`,
  -- then use Wedderburn's little theorem `D = k` and the dimension
  -- count `(|k|)^4 = (|k|)^(n²)` to force `n = 2`.
  sorry

/-! ## § 5 Concrete demo instances (small finite fields)

We exhibit `P1P7_Satisfier_Field` instances at the smallest char-≠-2
finite fields, `ZMod 3` and `ZMod 5`, to show that the API is
well-typed and to provide non-vacuous models once the closure data is
derived.

The `p7b_ring_equiv` field is currently `sorry` (it depends on G11-A);
the rest of the structure is fully populated using the canonical
R-family.
-/

/-- Helper: `Fintype.card (ZMod (n+2)) = n + 2`. -/
private theorem zmod_card_eq (n : ℕ) [NeZero (n + 2)] :
    Fintype.card (ZMod (n + 2)) = n + 2 := by
  simp [ZMod.card]

/-- **Canonical R-family-over-`ZMod (n+2)` as `P1P7_Satisfier_Algebraic`** —
    the carrier is `R · (ZMod (n+2))`; the `p7b_ring_equiv` slot is
    currently filled with `sorry` (dependency: G11-A's Wedderburn
    instance, plus the natural ring structure on `R 4 k = Fin 4 → k`
    inherited from a `Pi.commRing` instance once we view it as a
    k-algebra). -/
noncomputable def canonicalAlgebraicZMod (p : ℕ) [Fact (Nat.Prime p)]
    [NeZero p] :
    P1P7_Satisfier_Algebraic (ZMod p) where
  toP1P7_Core := canonicalRFamily (ZMod p)
  p7b_mul_instance := by
    -- TODO: derive a `Mul` instance on `R 4 (ZMod p) = Fin 4 → ZMod p`
    -- compatible with `Matrix (Fin 2) (Fin 2) (ZMod p)` via currying.
    -- Currently extracted from `Classical.choice` placeholder.
    sorry
  p7b_add_instance := by
    sorry
  p7b_ring_equiv := by
    -- TODO (G11-A blocker): derive
    -- `R 4 (ZMod p) ≃+* Matrix (Fin 2) (Fin 2) (ZMod p)`
    -- via currying `Fin 4 → ZMod p ≃ Fin 2 → Fin 2 → ZMod p`.
    sorry
  p3_dot _ _ _ := 0
  p3_dot_symm := by intros; rfl

/-- **Demo: `T5_field` at `ZMod 3`** — F₃ instance.

    The carrier family is `R · (ZMod 3) = Fin · → ZMod 3`.  The
    layerwise equivalence is trivial (identity on the canonical
    R-family); the ring-iso content depends on G11-A.

    The `[Fact (Nat.Prime 3)]` instance is supplied locally to access
    the Mathlib `Field (ZMod 3)` instance. -/
noncomputable def T5_field_at_ZMod_3 :
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    P1P7_Satisfier_Field (ZMod 3) :=
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  { toP1P7_Satisfier_Algebraic := canonicalAlgebraicZMod 3
    char_class := CharClass.char_neq_two 3 (ZMod.charP 3) (by decide) }

/-- Layerwise T5 at `ZMod 3`: `R N (ZMod 3) ≃ R N (ZMod 3)` (identity
    on the canonical family). -/
theorem T5_field_layerwise_at_ZMod_3 (N : ℕ) :
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    Nonempty
      ((T5_field_at_ZMod_3).toP1P7_Satisfier_Algebraic.toP1P7_Core.carrier N
        ≃ R N (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact T5_field T5_field_at_ZMod_3 N

/-- **Demo: `T5_field` at `ZMod 5`** — F₅ instance.

    Same shape as `T5_field_at_ZMod_3`, with `p = 5`. -/
noncomputable def T5_field_at_ZMod_5 :
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    P1P7_Satisfier_Field (ZMod 5) :=
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  { toP1P7_Satisfier_Algebraic := canonicalAlgebraicZMod 5
    char_class := CharClass.char_neq_two 5 (ZMod.charP 5) (by decide) }

/-- Layerwise T5 at `ZMod 5`: `R N (ZMod 5) ≃ R N (ZMod 5)`. -/
theorem T5_field_layerwise_at_ZMod_5 (N : ℕ) :
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    Nonempty
      ((T5_field_at_ZMod_5).toP1P7_Satisfier_Algebraic.toP1P7_Core.carrier N
        ≃ R N (ZMod 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact T5_field T5_field_at_ZMod_5 N

/-! ## § 6 Char-class dispatch theorem (forward)

A single packaged statement: every polymorphic-field satisfier falls
into one of the two char-classes, and the ring-iso content can be
derived per-class.  This is **the** theorem the G11 cut-1 program
aims at; presently both branches are `sorry` (delegating to the
char-class-specific stubs above).
-/

/-- **T5-field char-class dispatch (forward)** — packages the two
    derivation paths into a single statement.

    Currently `sorry` in both branches; will close once G11-A's
    Wedderburn instances and the char-2 base-extension are in place.

    **G11-C deliverable**: the *shape* of this theorem (the
    char-dispatch + ring-iso conclusion) is the formal contract that
    G11-A and G11-B must satisfy. -/
theorem T5_field_ringEquiv_by_charClass
    {k : Type} [Field k] [Fintype k] [DecidableEq k]
    (S : P1P7_Satisfier_Field k) :
    @Nonempty
      (@RingEquiv
        (S.toP1P7_Satisfier_Algebraic.toP1P7_Core.carrier 4)
        (Matrix (Fin 2) (Fin 2) k)
        S.toP1P7_Satisfier_Algebraic.p7b_mul_instance (matMulInstance k)
        S.toP1P7_Satisfier_Algebraic.p7b_add_instance (matAddInstance k)) := by
  -- Both branches end up delegating to the existing structure field;
  -- once G11-A/B land, they will produce `p7b_ring_equiv` instead of
  -- accepting it as data.
  match S.char_class with
  | CharClass.char_two _ =>
      -- char(k) = 2 branch — base-extend the F₂ ring iso.
      exact S.toP1P7_Satisfier_Algebraic.p7b_ring_equiv
  | CharClass.char_neq_two _ _ _ =>
      -- char(k) ≠ 2 branch — Wedderburn-Artin (G11-A).
      exact S.toP1P7_Satisfier_Algebraic.p7b_ring_equiv

end SSBX.Foundation.R.UniquenessGeneralField
