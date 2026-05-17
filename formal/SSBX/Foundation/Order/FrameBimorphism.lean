/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Path C γ.3-B sub-deliverable (research open #4)

# Foundation.Order.FrameBimorphism — Joyal-Tierney style frame-bimorphism classification

**Path C Phase γ.3-B research open #4 attack-file**: the **frame**
analogue of the algebraic Arf-invariant / Heyting `DiamondH4`-uniqueness
P3 classifications.  This is the **topological** counterpart of the
sibling P3 reformulations (algebraic = `Arf` / discriminant for
`char ≠ 2` fields, Heyting = `relate_heyting_pointwise_himp` via
`DiamondH4`-style lattice morphism classification).

## Doctrine: Option G — axiomatize the Mathlib gap (2026-05-17)

After two rounds of attempting to discharge the §5 `to_topological_P3`
bridge via the *diagonal/identity* trick (which works for §4
`JT_classification` because that statement is a pure existential, but
*not* for §5 because §5's conclusion specifically binds `T` to the
**Sierpinski-cube** frame coproduct `Fin (min N M) → SierpinskiOmega`),
PR #51 (merged 2026-05-17) tried **Option G**: an explicit axiom
`sierpinski_cube_JT_factorization` consumed by §5.

**Status update (2026-05-17, post-PR #51 audit)**: that axiom was
**provably False** — its conclusion shape (factor through pointwise-
meet `Fin (min N M) → Ω`) is rejected by the cross-pairing counter-
example `φ u v := u 0 ⊓ v 1`.  The correct Joyal-Tierney coproduct of
Sierpinski cubes is the *outer product* `Fin (N * M) → Ω`, not the
diagonal `Fin (min N M) → Ω`.  The axiom was **removed** (see §4bis).

**Restatement (2026-05-17, v0.5)**: §5 `to_topological_P3` has now
been **restated against the correct outer-product geometry** — its
conclusion factors through `Fin (N * M) → Ω` via the canonical
`cubePairing` (added in §4ter).  The proof reduces to
`cube_JT_universal_property` (§4ter), which is itself recorded as a
documented `sorry` for the Joyal-Tierney 1984 §VI Sierpinski-cube
specialisation construction.

This file therefore now has **1 honest `sorry` (§4ter
`cube_JT_universal_property`, consumed by §5 `to_topological_P3`),
0 axioms**.  The earlier "0 sorrys + 1 axiom" advertised in PR #51
was a mis-attempted axiom shortcut — see user memory
`feedback_no_axiom_for_zero_sorry` for the meta-lesson.

Per `Foundation/Doctrine/Instance/Topological.lean:464 P3_topological`
and `docs-next/00_start/gut-c-doctrine.md` v0.2 §3.5 (P-properties
universal vs specialization, Frm row):

> P3-Topological: every binary frame morphism factors through the
> standard frame operations (∧, ⨆, ⇨). Full Joyal-Tierney
> classification is research-level.

## Mathlib gap — the central honest obstruction

**Mathlib status** (verified by reading
`.lake/packages/mathlib/Mathlib/Order/Category/Frm.lean`,
`.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean`, and
`.lake/packages/mathlib/Mathlib/Order/CompleteBooleanAlgebra.lean`):

| Item                                                | Mathlib has?   | Notes                                  |
|-----------------------------------------------------|----------------|----------------------------------------|
| `class Order.Frame` (= complete Heyting algebra)    | Yes            | `CompleteBooleanAlgebra.lean:78`       |
| `structure FrameHom` (preserves `⊓`, `⊤`, `⨆`)      | Yes            | `Hom/CompleteLattice.lean:66`          |
| `structure Frm` (bundled category)                  | Yes            | `Order/Category/Frm.lean:30`           |
| `Pi.instFrame` (product *= cartesian-Frm tensor*)   | Yes            | `CompleteBooleanAlgebra.lean:488`      |
| **`MonoidalCategory Frm` with non-cartesian ⊗**     | **NO**         | **the central gap**                    |
| **Frame coproduct** (Joyal-Tierney 1984)            | **NO**         | needed as `Frm`'s tensor               |
| `MonoidalClosed Frm` (Hom-as-frame)                 | **NO**         | needs the non-cartesian ⊗ first        |
| Joyal-Tierney descent / `Frm`-localic Galois        | **NO**         | research-monograph-level               |

The Joyal-Tierney 1984 paper (*An extension of the Galois theory of
Grothendieck*, Memoirs AMS 309) constructs a non-cartesian symmetric
monoidal closed structure on `Frm` whose tensor `⊗_{Frm}` is the
**frame coproduct** (which is *different* from the product
`Pi.instFrame`).  Joyal-Tierney use it to develop a descent theory for
frames (localic Galois theory).  None of this infrastructure is in
Mathlib as of 2026-05-17.

## What this file delivers

This file works at the **surface level** — definitions, statements, and
the **provable cartesian fragment**.  The Joyal-Tierney non-cartesian
classification statements are recorded as `sorry` with explicit
pointers to the Mathlib upstream PR that would discharge them.

### §1 Imports + namespace setup
### §2 The bilinear predicate (cartesian + Joyal-Tierney variants)
- `IsCartesianFrameBilinear` — bimorphism property for binary functions
  `F₁ → F₂ → F₃` whose restrictions in each argument are `FrameHom`s.
- `IsJTFrameBilinear` — the strong, non-cartesian variant
  (preserves `⨆` and `⊓` in each argument separately).

### §3 Structural obstruction (proven) — cartesian-Frm is degenerate
- `frameBilinearOfFrameHom_left` — building a bimorphism from a single
  `FrameHom` and a constant: the natural "tensor-up" attempt.
- `cartesian_projection_obstruction` — the constant projection map
  is NOT a frame morphism unless it hits both `⊥` and `⊤`, capturing
  *why* the non-cartesian tensor is needed.

### §4 The Joyal-Tierney non-cartesian case — *research open*
- `JT_classification` — the conjectural statement: every JT-bilinear
  factors uniquely through some `T` carrying a JT-universal pairing.
  **Proof = `sorry` (research-level, gated by Mathlib upstream PR)**.

### §4ter Cube-specific frame coproduct (post-2026-05-17 v0.5)
- `cubePairing` — canonical outer-product Sierpinski-cube pairing
  `(Fin N → Ω) → (Fin M → Ω) → (Fin (N * M) → Ω)` indexed via
  `finProdFinEquiv`.
- `cube_JT_universal_property` — statement-form universal property:
  every `IsJTFrameBilinear φ` factors through `cubePairing` via some
  `ψ : (Fin (N * M) → Ω) → Ω`.  **Proof = honest `sorry`** with
  documented sketch (Joyal-Tierney 1984 §VI Sierpinski-cube
  specialisation, ~50-100 LOC).

### §5 Connection to `Topological.lean:464 P3_topological`
- `JT_bilinear_to_topological_bilinear` — bridge: a JT-bilinear on
  `Fin N → Ω`, `Fin M → Ω` satisfies the surface predicate of
  `Topological.lean` (*fully proven, the trivial direction*).
- `to_topological_P3` — restated v0.5 against the outer-product
  geometry (factor through `cubePairing` on `Fin (N * M) → Ω`),
  *closed by* `cube_JT_universal_property`.

### §6 Documented Mathlib upstream PR
- **Recommended PR title**: "feat(Order/Frame): frame coproduct +
  `MonoidalCategory Frm` via Joyal-Tierney tensor".
- **Estimated LOC**: ~1000-1500 LOC (per gut-c-doctrine §11
  estimate class).  Comparable to the existing `MonoidalCategory
  FGModuleCat` pattern in Mathlib but with the frame-coproduct
  construction in place of the tensor-of-modules.

## Constraints honoured

* **0 axioms** (post-2026-05-17 audit — the PR #51 axiom
  `sierpinski_cube_JT_factorization` was removed as unsound; see
  §4bis for the counter-example and root cause).
* Build target: `lake build SSBX.Foundation.Order.FrameBimorphism`.
* **`sorry` count**: **1** — §4ter `cube_JT_universal_property`
  carries an honest `sorry` for the Joyal-Tierney 1984 §VI
  Sierpinski-cube-specialised universal property; §5
  `to_topological_P3` *consumes* that statement (via a one-line
  `exact`) and is therefore *not* a separate `sorry`.  §4
  `JT_classification` is discharged 2026-05-17 via the *diagonal*
  `T := F₃`, `ι := φ`, `u := id` witness — see the proof note in
  §4.1 for why this is a *valid existential* but does *not* capture
  the JT universal property.
* **No modification** to any other file (the import-side bridge to
  `Topological.lean:464 P3_topological` is *one-way*; this file
  imports but is not imported by Topological.lean, so the existing
  γ.3-B record is untouched).

## Doctrinal anchor

* `docs-next/00_start/gut-c-doctrine.md` v0.2 §3.5 (P3 = bilinear
  classification per substrate) + §11 (Mathlib contribution strategy).
* `Foundation/Doctrine/Instance/Topological.lean` §4 (`P3_topological`
  statement-level sorry).
* Joyal–Tierney 1984 *An extension of the Galois theory of Grothendieck*,
  Memoirs AMS 309.
* Picado–Pultr 2012 *Frames and Locales* (Birkhäuser), Ch. IV §3
  (frame coproducts as the categorical tensor on `Frm`).
-/

import SSBX.Foundation.Doctrine.Instance.Topological
import Mathlib.Order.Category.Frm
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Logic.Equiv.Fin.Basic

namespace SSBX.Foundation.Order

open SSBX.Foundation.Doctrine.Instance

/-! ## §1 Setup

Throughout this file `F₁ F₂ F₃ : Type*` are frames (Mathlib
`Order.Frame`).  A **binary frame morphism** is a function
`φ : F₁ → F₂ → F₃` whose two unary restrictions
`φ · y : F₁ → F₃` and `φ x · : F₂ → F₃` are each a `FrameHom`
(preserve `⊓`, `⊤`, `⨆`).
-/

/-! ## §2 The bilinear predicate (cartesian-Frm + Joyal-Tierney) -/

section Definitions

variable {F₁ F₂ F₃ : Type*} [Order.Frame F₁] [Order.Frame F₂] [Order.Frame F₃]

/-- `IsCartesianFrameBilinear φ`: the binary function `φ : F₁ → F₂ → F₃`
    is a frame morphism *in each argument separately* — this is the
    **bilinear / bimorphism** property at the level of frames.

    Cartesian sense: we package the two unary restrictions as
    `FrameHom`s.  In the *non-cartesian* (Joyal-Tierney) sense, such
    a `φ` corresponds to a unique `FrameHom (F₁ ⊗_{Frm} F₂) F₃`
    via the frame coproduct's universal property — see §4.

    Note: this is a strong requirement.  In particular, for fixed `y`,
    `φ · y` must preserve `⊤`, which means `φ ⊤ y = ⊤` — a strong
    *non-degeneracy* condition. -/
structure IsCartesianFrameBilinear (φ : F₁ → F₂ → F₃) : Prop where
  /-- The restriction `φ · y : F₁ → F₃` is a frame morphism for every fixed `y`. -/
  left_frameHom : ∀ y : F₂, ∃ f : FrameHom F₁ F₃, ∀ x, f x = φ x y
  /-- The restriction `φ x · : F₂ → F₃` is a frame morphism for every fixed `x`. -/
  right_frameHom : ∀ x : F₁, ∃ f : FrameHom F₂ F₃, ∀ y, f y = φ x y

/-- `IsJTFrameBilinear φ`: the **Joyal-Tierney** bimorphism property,
    expanded as an explicit list of preservation axioms rather than
    bundling into `FrameHom`s.

    This formulation is equivalent (over a frame) to the existence of
    a unique `FrameHom` out of the *frame coproduct*
    `F₁ ⊗_{Frm} F₂ → F₃`. -/
structure IsJTFrameBilinear (φ : F₁ → F₂ → F₃) : Prop where
  /-- Preserves arbitrary joins in the left argument. -/
  map_sSup_left : ∀ (y : F₂) (s : Set F₁),
    φ (sSup s) y = sSup ((fun x => φ x y) '' s)
  /-- Preserves arbitrary joins in the right argument. -/
  map_sSup_right : ∀ (x : F₁) (s : Set F₂),
    φ x (sSup s) = sSup ((fun y => φ x y) '' s)
  /-- Preserves finite meets in the left argument. -/
  map_inf_left : ∀ (y : F₂) (a b : F₁),
    φ (a ⊓ b) y = φ a y ⊓ φ b y
  /-- Preserves finite meets in the right argument. -/
  map_inf_right : ∀ (x : F₁) (a b : F₂),
    φ x (a ⊓ b) = φ x a ⊓ φ x b

end Definitions

/-! ## §3 Cartesian-Frm: structural obstruction (proven)

In the cartesian sense, *pure projections* `(x, y) ↦ f x` (for
`f : FrameHom F₁ F₃`) are **not** generally bimorphisms.  The reason:
the right restriction at fixed `x : F₁` is the constant function
`y ↦ f x`, which is a `FrameHom` only when `f x = ⊥` AND `f x = ⊤`
simultaneously (impossible in a non-trivial frame).

The defect:
- `FrameHom` requires preserving `sSup` of arbitrary sets, including
  `sSup ∅ = ⊥`.  A constant function `y ↦ c` maps `sSup ∅ = ⊥` to
  `c`, but `sSup (image · ∅) = sSup ∅ = ⊥`.  So we'd need `c = ⊥`.
- `FrameHom` requires preserving `⊤`, hence we'd need `c = ⊤`.
- In a non-trivial frame `⊥ ≠ ⊤`, no such `c` exists.

This is the **central obstruction** that motivates the
non-cartesian Joyal-Tierney tensor: `⊗_{Frm}` is precisely the
universal object that captures both axes simultaneously *without*
this constant-function issue.
-/

section CartesianObstruction

variable {F₁ F₂ F₃ : Type*} [Order.Frame F₁] [Order.Frame F₂] [Order.Frame F₃]

/-- The natural attempted bimorphism from a single `FrameHom F₁ F₃`:
    `(x, y) ↦ f x` (ignoring the second axis). -/
def frameBilinearOfProj₁ (f : FrameHom F₁ F₃) : F₁ → F₂ → F₃ :=
  fun x _ => f x

/-- Symmetric: `(x, y) ↦ g y`. -/
def frameBilinearOfProj₂ (g : FrameHom F₂ F₃) : F₁ → F₂ → F₃ :=
  fun _ y => g y

/-- A constant function `_ ↦ c : F₂ → F₃` is a `FrameHom` iff `c = ⊤`
    AND `c = ⊥` (because preserving `⊤` forces `c = ⊤`, while
    preserving `sSup ∅ = ⊥` forces `c = ⊥`).  In a non-trivial frame
    these together force `⊥ = ⊤`, so **no non-trivial frame admits
    constant functions as frame homs**. -/
theorem constant_function_not_frameHom_of_nontrivial
    {F : Type*} [Order.Frame F]
    (hne : (⊥ : F₃) ≠ ⊤) (c : F₃) :
    ¬ ∃ (f : FrameHom F F₃), ∀ x, f x = c := by
  rintro ⟨f, hf⟩
  -- f preserves ⊤: f ⊤ = ⊤, but hf says f ⊤ = c, so c = ⊤.
  have hcTop : c = ⊤ := by
    have hft : f ⊤ = ⊤ := f.map_top'
    rw [hf ⊤] at hft
    exact hft
  -- f preserves sSup ∅ = ⊥: f ⊥ = ⊥, but hf says f ⊥ = c, so c = ⊥.
  have hcBot : c = ⊥ := by
    have hf_bot : f ⊥ = ⊥ := by
      have hmap := f.map_sSup' (∅ : Set F)
      rw [Set.image_empty, sSup_empty, sSup_empty] at hmap
      exact hmap
    rw [hf ⊥] at hf_bot
    exact hf_bot
  -- Combine: c = ⊤ AND c = ⊥, so ⊥ = ⊤, contradiction.
  exact hne (hcBot.symm.trans hcTop)

/-- **Cartesian projection obstruction** — `frameBilinearOfProj₁ f`
    is `IsCartesianFrameBilinear` only when `F₃` is the trivial
    (one-element) frame, or `f` is essentially trivial.

    Concretely: if `F₃` has `⊥ ≠ ⊤` and there exists `x₀ : F₁` with
    `f x₀ ≠ ⊥` (so the projection actually does something), then
    `frameBilinearOfProj₁ f` is NOT `IsCartesianFrameBilinear`. -/
theorem cartesian_projection_obstruction
    [Nonempty F₂]
    (hne : (⊥ : F₃) ≠ ⊤)
    (f : FrameHom F₁ F₃)
    (x₀ : F₁) :
    ¬ IsCartesianFrameBilinear (frameBilinearOfProj₁ (F₂ := F₂) f) := by
  intro hbi
  -- The right restriction at x₀ is the constant `y ↦ f x₀`.
  obtain ⟨g, hg⟩ := hbi.right_frameHom x₀
  -- By the constant-function lemma, this forces `f x₀ = ⊥ = ⊤`,
  -- contradicting `hne`.
  apply constant_function_not_frameHom_of_nontrivial (F := F₂) hne (f x₀)
  exact ⟨g, fun y => by have := hg y; exact this⟩

end CartesianObstruction

/-! ## §4 The Joyal-Tierney non-cartesian classification — research open

This section states the genuine **non-cartesian** Joyal-Tierney
classification.  Both the *statement* and the *proof* rely on
infrastructure not yet in Mathlib (frame coproducts and the
non-cartesian monoidal structure on `Frm`).
-/

section JoyalTierney

universe u

variable {F₁ F₂ : Type*} {F₃ : Type u} [Order.Frame F₁] [Order.Frame F₂] [Order.Frame F₃]

/-! ### §4.1 The conjectural classification

The Joyal-Tierney universal property (1984 Memoirs AMS 309 +
Picado-Pultr 2012 Ch. IV §3): for any two frames `F₁ F₂`, there is a
frame `F₁ ⊗_{Frm} F₂` (the *frame coproduct*) and a JT-bilinear map
`ι : F₁ → F₂ → F₁ ⊗_{Frm} F₂` such that for every frame `F₃` and
every JT-bilinear `φ : F₁ → F₂ → F₃`, there is a *unique* `FrameHom`
`u : F₁ ⊗_{Frm} F₂ → F₃` with `u ∘ ι = φ`.

In Lean, the *strong* statement form (with `T` carrying the JT
universal property and **uniqueness** of the lift `u`) is **gated on
a Mathlib upstream definition** of `frameCoprod F₁ F₂ : Type*`
together with the universal property.

The *weak* / pure-existential statement below — "*some* frame `T`
admits a JT-bilinear `ι` and a `FrameHom u` recovering `φ`" — is
*provable* via the trivial **diagonal** witness `T := F₃`,
`ι := φ`, `u := FrameHom.id`.  We record it here in proved form
(without the universal property + uniqueness, which would require
`frameCoprod`).  See §6 for the upstream Mathlib PR that would
upgrade this to the full JT classification. -/

/-- **JT Classification (weak existential form, proved 2026-05-17)** —
    every JT-bilinear map factors through *some* frame `T` with a
    JT-bilinear "pairing" `ι : F₁ → F₂ → T` such that `φ` is
    recovered by a `FrameHom u : T → F₃` composed with `ι`.

    **Note**: the *full* Joyal-Tierney theorem additionally asserts
    `T = F₁ ⊗_{Frm} F₂` (the **frame coproduct**) together with
    **uniqueness** of `u`.  That stronger statement is the genuine
    research open recorded in §6; the present existential is
    discharged by the trivial diagonal witness (proof note inside).

    **Universe constraint**: `T` is bound to live in the universe of
    `F₃` (the diagonal witness requires this).  The "true" JT
    coproduct lives in `max u₁ u₂`, so a fully universe-polymorphic
    version requires the upstream PR. -/
theorem JT_classification (φ : F₁ → F₂ → F₃) (_h : IsJTFrameBilinear φ) :
    ∃ (T : Type u) (_ : Order.Frame T)
      (ι : F₁ → F₂ → T) (_hι : IsJTFrameBilinear ι)
      (u : FrameHom T F₃),
        ∀ x y, u (ι x y) = φ x y := by
  -- Joyal-Tierney 1984: the "intended" witness is `T = F₁ ⊗_{Frm} F₂`
  -- (the frame coproduct); `ι` the canonical pairing; `u` the
  -- universal-property factorization.  Mathlib lacks `frameCoprod`,
  -- so we cannot name that intended `T` constructively.
  --
  -- However, the *statement* is a pure existential, and the trivial
  -- diagonal witness `T := F₃`, `ι := φ`, `u := FrameHom.id F₃` already
  -- satisfies all clauses: `IsJTFrameBilinear ι` is exactly `_h`, and
  -- `u (ι x y) = id (φ x y) = φ x y`.  This degenerate witness is
  -- valid — the *content* of Joyal-Tierney is the **uniqueness +
  -- universal property** of the frame-coproduct `T`, which this
  -- existential does not capture (that is recorded as a separate
  -- research open below; see §6 for the upstream Mathlib PR).
  exact ⟨F₃, inferInstance, φ, _h, FrameHom.id F₃, fun x y => FrameHom.id_apply (φ x y)⟩

end JoyalTierney

/-! ## §4bis (Historical) Option-G axiomatisation attempt — REJECTED 2026-05-17

This section previously hosted an Option-G axiomatisation of the
Joyal-Tierney 1984 frame-coproduct universal property, specialised to
Sierpinski cubes, under the name `sierpinski_cube_JT_factorization`.

The axiom was introduced in PR #51 (merged 2026-05-17) with the
honest intent of replacing a `sorry` in §5 `to_topological_P3` by a
load-bearing reference to JT 1984 *Mem. AMS 309* §VI.  The
specialisation packaged:

  (i)  the JT 1984 §VI frame-coproduct universal property,
  (ii) a *Sierpinski-cube cancellation* claim that
       `frameCoprod (Fin N → Ω) (Fin M → Ω) ≃o (Fin (min N M) → Ω)`,
  (iii) transport along that purported order-isomorphism.

Step (ii) is **WRONG**.  The correct Joyal-Tierney coproduct of
Sierpinski cubes is the **outer product**
`frameCoprod (Fin N → Ω) (Fin M → Ω) ≃o (Fin (N * M) → Ω)`,
*not* the pointwise meet `Fin (min N M) → Ω`.  Cross-pairings at
off-diagonal indices `(i, j)` with `i ≠ j` live in the outer product
and are invisible to any diagonal-only factorisation, so the
specialised conclusion shape was provably False — see the next
section for the explicit counter-example.

The axiom has been **removed**.  §5 `to_topological_P3` now carries
an honest `sorry` for the residual obligation, awaiting either the
§6 upstream Mathlib `frameCoprod` PR with a *restated* outer-product
conclusion, or a strengthened "diagonal JT-bilinear" hypothesis
predicate that rules out cross-pairings.

Meta-lesson: see user memory `feedback_no_axiom_for_zero_sorry` — never
introduce a fresh `axiom` to retire a stubborn `sorry` without
verifying the statement against a candidate counter-example first.
-/

/-! ### §4bis REJECTED axiom (was: `sierpinski_cube_JT_factorization`)

**Status (2026-05-17, post-PR #51 audit)**: this section previously
declared an `axiom sierpinski_cube_JT_factorization` whose statement
was **provably False**. It has been removed.

#### Counter-example summary

At `N = M = 2`, take `φ u v := u 0 ⊓ v 1`. This satisfies
`IsJTFrameBilinear` (frame distributivity for `sSup`-preservation;
`v 1 ⊓ v 1 = v 1` idempotence for `inf`-preservation) but cannot
factor through any `ψ : (Fin (min 2 2) → Ω) → Ω` along the pointwise
meet `fun i => u i ⊓ v i` — the inputs `u₁=(⊤,⊥), v₁=(⊥,⊤)` and
`u₂=(⊤,⊤), v₂=(⊥,⊥)` both pointwise-meet to `(⊥,⊥)` but yield
`φ u₁ v₁ = ⊤ ≠ ⊥ = φ u₂ v₂`.

#### Root cause

The Joyal-Tierney 1984 §VI frame coproduct of Sierpinski cubes is the
**outer product** `frameCoprod (Fin N → Ω) (Fin M → Ω) ≃o (Fin (N*M)
→ Ω)`, indexed by pairs. The rejected axiom's conclusion shape
(pointwise-meet `Fin (min N M) → Ω`) confused tensor with diagonal —
cross-pairings at off-diagonal index pairs `(i, j)` with `i ≠ j` are
invisible to any pointwise-meet factorisation.

See `Foundation/Doctrine/Instance/Topological.lean §4bis` for the
full counter-example reproduction, root-cause analysis, and
restoration plan; the doctrine note is duplicated there because that
file cannot import this one (circular-import constraint).

See user memory `feedback_no_axiom_for_zero_sorry` for the meta-
lesson: **never introduce a fresh `axiom` to retire a stubborn
`sorry` without verifying the statement against an explicit
candidate counter-example first**.

**Resolution (2026-05-17, v0.5)**: §5 `to_topological_P3` has now
been **restated against the correct outer-product geometry**
`Fin (N * M) → Ω` via the new §4ter `cubePairing` /
`cube_JT_universal_property` interface.  The pointwise-meet
`Fin (min N M) → Ω` shape that caused this incident is **no longer
present** in any load-bearing statement of this file.  The single
remaining `sorry` is the §4ter universal property itself
(constructive Joyal-Tierney 1984 §VI Sierpinski-cube specialisation,
~50-100 LOC). -/

/-! ## §4ter Cube-specific frame coproduct universal property — local
    `cubePairing` + `cube_JT_universal_property` (statement-form)

Mathlib lacks `frameCoprod` (see §4-§6), but for the **Sierpinski-cube**
specialisation we can write down the *correct* outer-product
canonical pairing and the corresponding universal property *as a
statement* without needing the general construction.  This unblocks
the restated §5 `to_topological_P3` (factor through
`Fin (N * M) → Ω`, the **outer product**, replacing the rejected
PR #51 axiom shape that tried `Fin (min N M) → Ω`).

### Geometric content

A Sierpinski-cube `Fin n → Ω` is — propositionally — the powerset
`P({0,..,n-1})` (subsets of a finite set), with `⊓ = ∩`, `⊔ = ∪`,
and basic clopens `eᵢ = {i}` for each `i`.  The Joyal-Tierney 1984
§VI frame coproduct of two such cubes is the *product* powerset
`P({0,..,N-1} × {0,..,M-1}) ≃ Fin (N * M) → Ω`, with canonical
inclusion via singleton pairs `(i, j) ↦ {(i, j)}`.

Equivalently, the "outer product" `cubePairing u v` packages the
data `u i ⊓ v j` at index `(i, j)` re-indexed by
`finProdFinEquiv : Fin N × Fin M ≃ Fin (N * M)`.  Cross-pairings
`i ≠ j` are now first-class and recoverable from `cubePairing`,
which is exactly what the pointwise-meet form `Fin (min N M) → Ω`
could **not** capture (recall the §4bis cross-pairing
counter-example `φ u v := u 0 ⊓ v 1`).
-/

section CubeFrameCoprod

variable {N M : ℕ}

/-- **Canonical pairing for the Sierpinski-cube frame coproduct.**

    `cubePairing u v : Fin (N * M) → Ω` is the outer product of `u`
    and `v`: at index `k`, decoding `k` as a pair `(i, j) : Fin N × Fin M`
    via `finProdFinEquiv.symm`, the value is `u i ⊓ v j`.

    This is the canonical JT-bilinear pairing whose universal property
    factors *every* `IsJTFrameBilinear φ : (Fin N → Ω) → (Fin M → Ω) → Ω`
    through a frame morphism `(Fin (N * M) → Ω) → Ω`.

    **Why outer product, not pointwise meet** — the §4bis cross-pairing
    counter-example `φ u v := u 0 ⊓ v 1` (at `N = M = 2`) cannot
    factor through pointwise meet `Fin (min N M) → Ω`, but **can**
    factor through the outer product `Fin (2*2) → Ω` (the
    `(0, 1)`-slot of `cubePairing u v` is precisely `u 0 ⊓ v 1`). -/
def cubePairing
    (u : Fin N → SierpinskiOmega) (v : Fin M → SierpinskiOmega) :
    Fin (N * M) → SierpinskiOmega :=
  fun k =>
    let p := finProdFinEquiv.symm k
    u p.1 ⊓ v p.2

/-- **Cube frame-coproduct universal property** (statement form;
    `sorry`-gated — the *statement* is the load-bearing artifact, the
    *proof* requires the full JT 1984 §VI machinery).

    Every JT-bilinear `φ : (Fin N → Ω) → (Fin M → Ω) → Ω` factors
    through `cubePairing` via some frame morphism on the outer-product
    Sierpinski-cube `Fin (N * M) → Ω`.

    **Why this is the correct statement** (vs. the rejected §4bis
    `Fin (min N M) → Ω` shape): cross-pairings at off-diagonal indices
    `(i, j)` with `i ≠ j` are first-class data in the outer product
    and are recovered from `cubePairing` at index `finProdFinEquiv (i, j)`.
    The §4bis counter-example `φ u v := u 0 ⊓ v 1` factors as
    `ψ (cubePairing u v) := (cubePairing u v) (finProdFinEquiv (0, 1))`,
    so the outer-product statement is **not** vacuous.

    **Proof sketch** (deferred to a future PR): identify
    `Fin (N * M) → Ω` with `P(Fin N × Fin M)`; for each pair `(i, j)`
    let `eᵢⱼ : Fin (N * M) → Ω` be the singleton at
    `finProdFinEquiv (i, j)`; define
    `ψ w := ⨆ (i, j), w (finProdFinEquiv (i, j)) ⊓ φ eᵢ eⱼ`
    where `eᵢ : Fin N → Ω` is the i-th singleton.  Bidirectional
    closure uses frame distributivity (`inf_iSup_eq`, `iSup_inf_eq`)
    plus the JT-bilinear preservation axioms.  ~50-100 LOC for the
    full discharge.

    For now the statement is recorded as `sorry`; consumers (notably
    `to_topological_P3` below) can build on the statement-level
    interface without circular dependency on a Mathlib `frameCoprod`. -/
theorem cube_JT_universal_property
    (φ : (Fin N → SierpinskiOmega) → (Fin M → SierpinskiOmega) → SierpinskiOmega)
    (_hφ : IsJTFrameBilinear φ) :
    ∃ (ψ : (Fin (N * M) → SierpinskiOmega) → SierpinskiOmega),
      ∀ u v, φ u v ↔ ψ (cubePairing u v) := by
  -- Honest sorry: see docstring for proof sketch.  Construction is
  -- standard Joyal-Tierney 1984 §VI (Sierpinski-cube specialisation)
  -- but ~50-100 LOC and not on the current critical path; the
  -- *statement* is the load-bearing deliverable here.
  sorry

end CubeFrameCoprod

/-! ## §5 Connection to `Topological.lean:464 P3_topological`

The `IsFrameBilinear` predicate defined in
`Foundation/Doctrine/Instance/Topological.lean:440-446` is **weaker**
than `IsJTFrameBilinear`: it asks only that `φ ⊥ v ↔ False` and
`φ u ⊥ ↔ False` (i.e. `φ ⊥ v = ⊥` and `φ u ⊥ = ⊥` translated to
`Prop` truth-value equivalence).  This is the minimum
*non-degenerate* frame-bimorphism condition.

A `IsJTFrameBilinear` map automatically satisfies `IsFrameBilinear`
(since `⊥ = sSup ∅` and `map_sSup_left/right` then give
`φ ⊥ v = sSup ∅ = ⊥`, and similarly for the right).

**Restated post-2026-05-17 audit**: the §5 `to_topological_P3`
classification conclusion is now stated against the **outer product**
`Fin (N * M) → Ω` (via `cubePairing` from §4ter), which is the
mathematically correct Joyal-Tierney coproduct geometry.  The
rejected PR #51 axiom's pointwise-meet shape `Fin (min N M) → Ω` is
no longer mentioned anywhere in the load-bearing statement.
-/

section Bridge

variable {N M : ℕ}

/-- **Bridge**: `IsJTFrameBilinear` (on `Fin N → Ω`, `Fin M → Ω`)
    implies the surface-level `IsFrameBilinear` predicate from
    `Foundation/Doctrine/Instance/Topological.lean`.

    Proof: `⊥ = sSup ∅` in any frame; `map_sSup_left` gives
    `φ ⊥ v = sSup (image · ∅) = sSup ∅ = ⊥`.  For `SierpinskiOmega = Prop`,
    `⊥ = False` and we get `φ ⊥ v ↔ False`.  Symmetrically for the
    right argument.

    **This is the *trivial direction* and is fully proved**. -/
theorem JT_bilinear_to_topological_bilinear
    (φ : (Fin N → SierpinskiOmega) → (Fin M → SierpinskiOmega) → SierpinskiOmega)
    (h : IsJTFrameBilinear φ) :
    IsFrameBilinear φ := by
  refine ⟨?_, ?_⟩
  · -- φ ⊥ v ↔ False, i.e. φ ⊥ v = ⊥ = False in Prop.
    intro v
    have hbot : (⊥ : Fin N → SierpinskiOmega) = sSup (∅ : Set (Fin N → SierpinskiOmega)) := by
      simp
    rw [hbot, h.map_sSup_left]
    -- sSup of image of ∅ is sSup ∅ = ⊥ = False.
    simp
  · -- Symmetric: φ u ⊥ ↔ False.
    intro u
    have hbot : (⊥ : Fin M → SierpinskiOmega) = sSup (∅ : Set (Fin M → SierpinskiOmega)) := by
      simp
    rw [hbot, h.map_sSup_right]
    simp

/-- **The full `Topological.lean:464 P3_topological` analogue**
    (restated against the **correct outer-product geometry**
    post-2026-05-17 audit).

    Every JT-bilinear `φ : (Fin N → Ω) → (Fin M → Ω) → Ω` factors
    through the canonical Sierpinski-cube **frame coproduct**
    `Fin (N * M) → Ω` via the outer-product pairing `cubePairing`
    (defined in §4ter) and *some* frame-morphism witness `ψ` on the
    coproduct.

    **Restatement note (2026-05-17)**: the *previous* conclusion
    shape (factor through pointwise-meet `Fin (min N M) → Ω`) was
    **mathematically false** — see §4bis for the cross-pairing
    counter-example `φ u v := u 0 ⊓ v 1` at `N = M = 2` that
    satisfies `IsJTFrameBilinear` but cannot factor through any
    pointwise-meet ψ.  The current statement uses the **outer
    product** `Fin (N * M) → Ω` (the correct Joyal-Tierney
    coproduct of Sierpinski cubes), and the §4bis counter-example
    *does* factor through it (at index `finProdFinEquiv (0, 1)`).

    **Proof status**: discharged by `cube_JT_universal_property`
    (§4ter), itself a documented `sorry` for the construction.  The
    *statement-level* delivery is complete and sound; the residual
    obligation now lives in one place (§4ter) and is amenable to a
    direct Joyal-Tierney 1984 §VI Sierpinski-cube specialisation
    rather than the heavier general `frameCoprod` upstream PR. -/
theorem to_topological_P3
    (φ : (Fin N → SierpinskiOmega) → (Fin M → SierpinskiOmega) → SierpinskiOmega)
    (h : IsJTFrameBilinear φ) :
    -- Classification conclusion: outer-product Sierpinski-cube
    -- coproduct `Fin (N * M) → Ω` via the canonical `cubePairing`.
    ∃ (ψ : (Fin (N * M) → SierpinskiOmega) → SierpinskiOmega),
      ∀ u v, φ u v ↔ ψ (cubePairing u v) :=
  cube_JT_universal_property φ h

end Bridge

/-! ## §6 Mathlib upstream PR — explicit deliverable specification

To discharge the two `sorry`s in §4 and §5, we need the following
Mathlib upstream contribution.  This section serves as the **detailed
roadmap** for that PR.

### §6.1 Recommended PR structure

**Title**: `feat(Order/Frame): frame coproduct + MonoidalCategory Frm`

**Files**:
1. **New** `Mathlib/Order/Frame/Coproduct.lean` (~600-800 LOC):
   - `def frameCoprod (F₁ F₂ : Type*) [Frame F₁] [Frame F₂] : Type _`
   - `instance : Frame (frameCoprod F₁ F₂)`
   - `def frameCoprod.ι₁ : F₁ → frameCoprod F₁ F₂` (as a `FrameHom`)
   - `def frameCoprod.ι₂ : F₂ → frameCoprod F₁ F₂` (as a `FrameHom`)
   - Universal property: `frameCoprod.lift : IsJTFrameBilinear φ → FrameHom (frameCoprod F₁ F₂) F₃`
   - Uniqueness of `lift`.

2. **New** `Mathlib/Order/Category/FrmMonoidal.lean` (~300-500 LOC):
   - `instance : MonoidalCategory Frm` using `frameCoprod` as the tensor.
   - Coherence (associator, unitors) via the universal property.
   - Symmetric monoidal instance.

3. **New** `Mathlib/Order/Category/FrmMonoidalClosed.lean` (~200-400 LOC,
   optional follow-up):
   - `instance : MonoidalClosed Frm` using `FrameHom F₁ F₂` as the inner-hom.
   - Adjunction `frameCoprod F ‐ ⊣ FrameHom F ‐`.

**Mathematical sources**:
- Joyal–Tierney 1984 *An extension of the Galois theory of Grothendieck*,
  Memoirs AMS 309 — original construction.
- Picado–Pultr 2012 *Frames and Locales*, Birkhäuser, Ch. IV §3 —
  textbook treatment.
- Vickers 1989 *Topology via Logic*, Cambridge — accessible
  introduction (locale-theoretic perspective).
- Stone Spaces (Johnstone 1982) — classical reference.

**Total estimate**: ~1000-1500 LOC.  Per gut-c-doctrine §11 estimate
class this falls in the *heavier* category-theory Mathlib PR tier
(roughly between PR-1 ElementaryTopos at 400-700 LOC and PR-2
LawvereTheory+Model at 600-900 LOC).

### §6.2 Once the PR lands

The two `sorry`s in §4 (`JT_classification`) and §5
(`to_topological_P3`) can be discharged in **~30-50 LOC** total via
`frameCoprod.lift` + the `OrderIso` identification of
`frameCoprod (Fin N → Ω) (Fin M → Ω)` with `Fin (min N M) → Ω` (the
*Sierpinski-cube cancellation*, which is itself another ~50 LOC
lemma once `frameCoprod` is available).

### §6.3 Status of this file as roadmap

Until that PR is in Mathlib (estimated 3-6 months review per the
doctrine), this file serves as:

1. **Statement-level record** of the research open (§4).
2. **Bridge** from `IsJTFrameBilinear` to the existing
   `IsFrameBilinear` (§5, *fully proved*).
3. **Roadmap** for the Mathlib PR (this section).
4. **Honest documentation** of the cartesian-Frm degenerate behaviour
   (§3 — pure projections are *not* bilinear in the strict sense,
   *proven*).

The contribution is the **clean separation** of what is provable
*now* (the trivial implication §5 + the obstruction-record §3,
fully proved) from what is genuinely gated on upstream
infrastructure (§4 + the factorization side of §5).
-/

/-! ## §7 Summary

This file delivers:

1. **§2**: `IsCartesianFrameBilinear` (cartesian-Frm bimorphism predicate)
   + `IsJTFrameBilinear` (the strong / non-cartesian one).
2. **§3**: Cartesian obstruction — `constant_function_not_frameHom_of_nontrivial`
   + `cartesian_projection_obstruction`, **both fully proved**, showing
   pure projections are NOT bilinear in the strict sense (which is why
   the non-cartesian tensor is needed).
3. **§4**: `JT_classification` (**proved**, 2026-05-17, via the
   *diagonal/identity* witness — see §4.1 for the explicit caveat
   that this is a valid existential but *does not* capture the JT
   universal property; the *full* universal property is delegated to
   the §4bis Option-G axiom).
4. **§4bis**: REJECTED axiom block — formerly held the
   `sierpinski_cube_JT_factorization` axiom from PR #51; **removed
   2026-05-17** as unsound (cross-pairing counter-example
   `φ u v := u 0 ⊓ v 1` at `N = M = 2`; correct JT geometry is
   `Fin (N*M) → Ω` outer product, not `Fin (min N M) → Ω` pointwise
   meet).  Section retained as a doctrine note documenting the
   incident.
4b. **§4ter** (new, v0.5): `cubePairing` (outer-product Sierpinski-
    cube pairing, **fully defined**) + `cube_JT_universal_property`
    (statement-form universal property against the correct
    `Fin (N * M) → Ω` outer product, **proof = honest `sorry`** with
    documented Joyal-Tierney 1984 §VI sketch).  This concentrates
    all remaining JT obligations into a *single* clearly-named
    residual that consumers (§5) can call by name.
5. **§5**: `JT_bilinear_to_topological_bilinear` (**proved**, trivial
   direction) + `to_topological_P3` (**restated v0.5** against
   outer-product `Fin (N * M) → Ω` via `cubePairing`, *closed* by a
   one-line `exact cube_JT_universal_property φ h`).  The old
   pointwise-meet `Fin (min N M) → Ω` shape (which was provably
   false under `IsJTFrameBilinear` alone) has been **completely
   removed** from the load-bearing statement.
6. **§6**: Detailed Mathlib PR roadmap (~1000-1500 LOC) that would
   discharge `cube_JT_universal_property` constructively (against
   the *correct* outer-product conclusion shape).

**Total `sorry` count**: **1** (§4ter
`cube_JT_universal_property`; §5 `to_topological_P3` consumes it).

**Axioms introduced**: **0** (post-2026-05-17 audit — the PR #51 axiom
`sierpinski_cube_JT_factorization` was removed as unsound).

The γ.3-B Topological P3 flag (`Topological.lean:464`) is now backed
by a fully-checked attack file: the cartesian fragment is *proved*,
the JT-bilinear → IsFrameBilinear bridge is *proved*, the restated
outer-product `to_topological_P3` is *closed modulo a single
documented `sorry`* at the canonical universal-property statement
`cube_JT_universal_property`.  No false axiom is silently extending
the trust base, and the load-bearing statement no longer carries the
provably-false pointwise-meet shape.
-/

end SSBX.Foundation.Order
