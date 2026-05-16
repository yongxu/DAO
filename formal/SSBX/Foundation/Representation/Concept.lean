/-
# Foundation.Representation.Concept — Strategy A: Concept-as-syntax + level

Per the representation-closure programme (`wen-substrate.md` v1.4 §Representation):
concepts are represented in the R-Family by encoding the D1+P1–P7 primitives
as inductive constructors of a `Concept` type, then mapping each concept to
its **structural level** `Concept.level : Concept → ℕ` (the smallest `R N`
index hosting it).

This module is the **compositional / denotational** half of the locator
programme.  Signature-based (Strategy B) and fixed-point (Strategy D)
locators live in `Signature.lean` and `Articulate.lean` respectively and
must agree with `Concept.level` on closed concepts.

## Constructors (D1+P1–P7 mirror)

* `atom`    — P1 minimum distinction; an atomic concept anchored by a string label.
* `compose` — P2 composition; combines two concepts at the same level.
* `square`  — P5 self-application; jumps to the next squaring-tower step
              (`R N × R N → R (N+N)`).
* `modal`   — P6 modal stamp; tags a concept with a V₄ Shi class, forcing
              level ≥ 2.
* `hom`     — Hom-as-content (P5 internalisation); forces level ≥ 4.
* `derive`  — P7 derivation step; level-preserving (rules don't enlarge
              the carrier they act on).

## Level formula

      level(atom)         = 1
      level(compose a b)  = max(level a, level b)
      level(square a b)   = 2 * max(level a, level b)
      level(modal v c)    = max(level c, 2)
      level(hom a b)      = max(2 * max(level a, level b), 4)
      level(derive r c)   = level c

Each clause is forced by the structural axis it represents (see the
representation-closure derivation in `wen-substrate.md`).

## Doctrinal anchor

* `wen-substrate.md` v1.4 §Representation (representation closure theorem).
* P1–P7 derivation from D1 (chapter 01).
* Squaring-tower step `R(N+N) ≅ R N × R N` formalised in
  `Foundation/R/Squaring.lean`.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.Atlas.Yi.Shi

namespace SSBX.Foundation.Representation

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 The `Concept` inductive type -/

/-- A **Concept** is a syntax tree built from the D1+P1–P7 primitives.  Each
    constructor maps to a distinct structural axis of the R-Family carrier:

    * `atom`    : P1 minimum distinction.
    * `compose` : P2 composition at the same level.
    * `square`  : P5 self-application, jumping `R N → R (2N)`.
    * `modal`   : P6 modal stamping with a V₄ Shi class.
    * `hom`     : Hom-as-content; forces level ≥ 4.
    * `derive`  : P7 derivation step (level-preserving).

    The label `String` on `atom` is a lexical anchor; subsequent locator
    strategies (B/D) may resolve it against a character table without
    altering the inductive structure. -/
inductive Concept where
  | atom    : String → Concept
  | compose : Concept → Concept → Concept
  | square  : Concept → Concept → Concept
  | modal   : Shi → Concept → Concept
  | hom     : Concept → Concept → Concept
  | derive  : Nat → Concept → Concept
  deriving Inhabited

namespace Concept

/-! ## § 2 The `level` function -/

/-- `level c` is the smallest `N` such that `c` admits a structural
    representation as an element of `R N`.

    The formula is forced by the constructor semantics:
    * `compose` stays at the same level (R_N has internal composition).
    * `square` jumps via the R-Family squaring step `R N × R N ≃ R (2N)`.
    * `modal` requires V₄ (= R 2) as a minimum modal carrier.
    * `hom` requires R 4 as the minimum Hom-as-content host (P5
       internalisation first becomes non-trivial at R 4 = V₄ × V₄).
    * `derive` preserves the level (rules act on R N, not above it). -/
def level : Concept → Nat
  | .atom _      => 1
  | .compose a b => max a.level b.level
  | .square a b  => 2 * max a.level b.level
  | .modal _ c   => max c.level 2
  | .hom a b     => max (2 * max a.level b.level) 4
  | .derive _ c  => c.level

@[simp] theorem level_atom (s : String) :
    (atom s).level = 1 := rfl

@[simp] theorem level_compose (a b : Concept) :
    (compose a b).level = max a.level b.level := rfl

@[simp] theorem level_square (a b : Concept) :
    (square a b).level = 2 * max a.level b.level := rfl

@[simp] theorem level_modal (v : Shi) (c : Concept) :
    (modal v c).level = max c.level 2 := rfl

@[simp] theorem level_hom (a b : Concept) :
    (hom a b).level = max (2 * max a.level b.level) 4 := rfl

@[simp] theorem level_derive (r : Nat) (c : Concept) :
    (derive r c).level = c.level := rfl

/-! ## § 3 Level lower-bounds (structural minimums) -/

/-- Every `Concept` lives at level ≥ 1 (P1: minimum distinction). -/
theorem level_pos (c : Concept) : 1 ≤ c.level := by
  induction c with
  | atom _ => show (1 : Nat) ≤ 1; omega
  | compose _ _ iha ihb =>
      show 1 ≤ max _ _
      omega
  | square _ _ iha ihb =>
      show 1 ≤ 2 * max _ _
      omega
  | modal _ _ ihc =>
      show 1 ≤ max _ 2
      omega
  | hom _ _ iha ihb =>
      show 1 ≤ max (2 * max _ _) 4
      omega
  | derive _ _ ihc => exact ihc

/-- Modal-stamped concepts live at level ≥ 2 (P6: minimum V₄ modality). -/
theorem level_modal_ge_two (v : Shi) (c : Concept) :
    2 ≤ (modal v c).level := by
  show 2 ≤ max c.level 2
  omega

/-- Hom-as-content concepts live at level ≥ 4 (P5: first non-trivial
    Hom-internalisation). -/
theorem level_hom_ge_four (a b : Concept) :
    4 ≤ (hom a b).level := by
  show 4 ≤ max (2 * max a.level b.level) 4
  omega

/-- Squared concepts have even level. -/
theorem level_square_even (a b : Concept) :
    2 ∣ (square a b).level := by
  show 2 ∣ 2 * max a.level b.level
  exact ⟨_, rfl⟩

/-! ## § 4 Worked examples (smoke tests) -/

/-- A primary atomic concept at level 1 — the simplest distinction. -/
def exAtom : Concept := atom "x"

/-- A modal-stamped atom (例: 道-stamped "x") — forced to R 2. -/
def exModal : Concept := modal Shi.dao exAtom

/-- Two atoms composed — stays at R 1. -/
def exCompose : Concept := compose exAtom exAtom

/-- Two atoms squared — jumps to R 2. -/
def exSquare : Concept := square exAtom exAtom

/-- Hom of two modal-atoms — forced to R 4 (since both sides at R 2, hom
    requires max(2*2, 4) = 4). -/
def exHomModal : Concept := hom exModal exModal

/-- Triply-nested squaring of atoms — lands at R 8 (the byte ceiling). -/
def exDeepSquare : Concept := square (square exSquare exSquare) (square exSquare exSquare)

/-! ### Computational checks -/

example : exAtom.level = 1 := rfl
example : exModal.level = 2 := rfl
example : exCompose.level = 1 := rfl
example : exSquare.level = 2 := rfl
example : exHomModal.level = 4 := rfl
example : exDeepSquare.level = 8 := rfl

/-! ## § 5 `cell` — placeholder mapping into `R c.level`

For each concept `c`, `cell c` produces a witness inhabitant of `R c.level`.
The full cell function (matching the 16-character process matrix and the
Cell256 lookup table) lives in `Foundation/Representation/Cell.lean`
(Strategy C, deferred).  Here we provide a **default witness** that
guarantees `cell` is total: the zero element of `R c.level` (= the
all-`false` bit-pattern, which corresponds to 道 at every level).

This is sufficient for the structural representation theorem; richer
witnesses (matching the wen-substrate lexical anchors) compose on top
without altering `level`.
-/

/-- The default cell witness: the zero element of `R c.level` (all-false /
    道-anchored).  Strategy C will refine this against the lexical tables. -/
def cell (c : Concept) : R c.level := fun _ => false

@[simp] theorem cell_atom (s : String) :
    cell (atom s) = (fun _ => false : R 1) := rfl

end Concept

end SSBX.Foundation.Representation
