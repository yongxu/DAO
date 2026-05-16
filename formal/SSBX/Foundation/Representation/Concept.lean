/-
# Foundation.Representation.Concept — Strategy A: Concept-as-syntax + level + cell

Per the representation-closure programme (`wen-substrate.md` v1.4 §Representation):
concepts are represented in the R-Family by encoding the D1+P1–P7 primitives
as inductive constructors of a `Concept` type, then mapping each concept to
its **structural level** `Concept.level : Concept → ℕ` and its **cell**
`Concept.cell c : R c.level` (a concrete inhabitant of the R-tower at that
level).

The two-projection map is:

      locate : Concept → Σ N, R N
      locate c := ⟨c.level, c.cell⟩

This module is the **compositional / denotational** half of the locator
programme.  Signature-based (Strategy B), fixed-point (Strategy D), and
o/x-bit-string (Strategy E) locators live in `Signature.lean`,
`Articulate.lean`, `OXPattern.lean` respectively and agree on shared inputs.

## Constructors (D1+P1–P7 mirror + Strategy E bridge)

* `atom`    — P1 minimum distinction; logical atom, level 1 (cell is the
              R 1 default zero — it's a label, not a bit pattern).
* `bits`    — Strategy E bridge: o/x string atom, level = `s.toList.length`,
              cell = `(fromOX s).snd` (the concrete parsed bit pattern).
* `compose` — P2 composition; combines two concepts at the same level
              (XOR on the lifted carriers).
* `square`  — P5 self-application; jumps to the next squaring-tower step
              (`R N × R N → R (N+N)`, level `2 * max`).
* `modal`   — P6 modal stamp; tags a concept with a V₄ Shi class, forcing
              level ≥ 2 (XOR with embedded V₄ element).
* `hom`     — Hom-as-content (P5 internalisation); forces level ≥ 4
              (squaring carrier, padded to ≥ 4).
* `derive`  — P7 derivation step; level-preserving, cell pass-through.

## Cell formulas (concrete realisations)

      cell(atom _)         := fun _ => false                                   -- R 1 zero
      cell(bits s)         := (fromOX s).snd                                   -- parsed pattern
      cell(compose a b) i  := xor (cell a embedded) (cell b embedded)          -- XOR @ max level
      cell(square a b)     := append of (cell a, cell b) lifted to max level   -- R (m+m)
      cell(modal v c) i    := xor (v embedded) (cell c embedded)               -- modal XOR
      cell(hom a b)        := square cell padded up to ≥ R 4
      cell(derive _ c)     := cell c                                           -- pass-through

## Doctrinal anchor

* `wen-substrate.md` v1.4 §Representation.
* P1–P7 derivation from D1 (chapter 01).
* Squaring-tower step `R(N+N) ≅ R N × R N` formalised in
  `Foundation/R/Squaring.lean`.
* O/x bit-string parser in `Foundation/Representation/OXPattern.lean`.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.Atlas.Yi.Shi
import SSBX.Foundation.Representation.OXPattern

namespace SSBX.Foundation.Representation

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 The `Concept` inductive type -/

/-- A **Concept** is a syntax tree built from the D1+P1–P7 primitives plus
    a `bits` bridge to the Strategy E o/x parser. -/
inductive Concept where
  | atom    : String → Concept
  | bits    : String → Concept
  | compose : Concept → Concept → Concept
  | square  : Concept → Concept → Concept
  | modal   : Shi → Concept → Concept
  | hom     : Concept → Concept → Concept
  | derive  : Nat → Concept → Concept
  deriving Inhabited

namespace Concept

/-! ## § 2 The `level` function -/

/-- `level c` is the smallest `N` such that `c` admits a structural
    representation as an element of `R N`. -/
def level : Concept → Nat
  | .atom _      => 1
  | .bits s      => s.toList.length
  | .compose a b => max a.level b.level
  | .square a b  => 2 * max a.level b.level
  | .modal _ c   => max c.level 2
  | .hom a b     => max (2 * max a.level b.level) 4
  | .derive _ c  => c.level

@[simp] theorem level_atom (s : String) :
    (atom s).level = 1 := rfl

@[simp] theorem level_bits (s : String) :
    (bits s).level = s.toList.length := rfl

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

/-- Non-empty `bits` concepts live at level ≥ 1.  (Empty `bits ""` has
    level 0; we treat it as a degenerate / "empty distinction" case.) -/
theorem level_bits_pos {s : String} (h : s.toList ≠ []) :
    1 ≤ (bits s).level := by
  show 1 ≤ s.toList.length
  exact List.length_pos_iff.mpr h

/-! ## § 4 The `cell` function — concrete R-tower inhabitants -/

/-- `cell c : R c.level` is a concrete inhabitant of the R-tower at level
    `c.level`.  Each constructor gets a structurally-determined formula. -/
def cell : (c : Concept) → R c.level
  | .atom _      => fun _ => false
  | .bits s      => (fromOX s).snd
  | .compose a b =>
      let ca := cell a
      let cb := cell b
      fun (i : Fin (max a.level b.level)) =>
        xor
          (if hia : i.val < a.level then ca ⟨i.val, hia⟩ else false)
          (if hib : i.val < b.level then cb ⟨i.val, hib⟩ else false)
  | .square a b =>
      let ca := cell a
      let cb := cell b
      let m := max a.level b.level
      fun (i : Fin (2 * m)) =>
        if _hi_first : i.val < m then
          if hia : i.val < a.level then ca ⟨i.val, hia⟩ else false
        else
          let j := i.val - m
          if hib : j < b.level then cb ⟨j, hib⟩ else false
  | .modal v c =>
      let cc := cell c
      fun (i : Fin (max c.level 2)) =>
        xor
          (if hi2 : i.val < 2 then v ⟨i.val, hi2⟩ else false)
          (if hic : i.val < c.level then cc ⟨i.val, hic⟩ else false)
  | .hom a b =>
      let ca := cell a
      let cb := cell b
      let m := max a.level b.level
      fun (i : Fin (max (2 * m) 4)) =>
        if _hi_inner : i.val < 2 * m then
          if _hi_first : i.val < m then
            if hia : i.val < a.level then ca ⟨i.val, hia⟩ else false
          else
            let j := i.val - m
            if hib : j < b.level then cb ⟨j, hib⟩ else false
        else
          false
  | .derive _ c => cell c

/-! ## § 5 Worked examples — level + cell smoke tests -/

/-- A logical atom at level 1; cell is the R 1 default zero. -/
def exAtom : Concept := atom "x"

/-- O/x bit-pattern at level 7 — the user's "ooxoxox" running example. -/
def exBitsSeven : Concept := bits "ooxoxox"

/-- Modal-stamped atom — forced to R 2. -/
def exModal : Concept := modal Shi.dao exAtom

/-- Two atoms composed — stays at R 1. -/
def exCompose : Concept := compose exAtom exAtom

/-- Two atoms squared — jumps to R 2. -/
def exSquare : Concept := square exAtom exAtom

/-- Hom of two modal atoms — forced to R 4. -/
def exHomModal : Concept := hom exModal exModal

/-- Triply-nested squaring — lands at R 8 (byte ceiling). -/
def exDeepSquare : Concept := square (square exSquare exSquare) (square exSquare exSquare)

/-! ### Level checks -/

example : exAtom.level = 1 := rfl
example : exBitsSeven.level = 7 := rfl
example : exModal.level = 2 := rfl
example : exCompose.level = 1 := rfl
example : exSquare.level = 2 := rfl
example : exHomModal.level = 4 := rfl
example : exDeepSquare.level = 8 := rfl

/-! ### Cell checks — bits parsed correctly via OXPattern bridge -/

/-- `bits "ooxoxox"` at level 7 has cell = the parsed bit pattern.  The
    bit-by-bit values match: positions 0='o'/false, 1='o', 2='x'/true,
    3='o', 4='x', 5='o', 6='x'. -/
example : exBitsSeven.cell ⟨2, by decide⟩ = true := rfl
example : exBitsSeven.cell ⟨0, by decide⟩ = false := rfl
example : exBitsSeven.cell ⟨6, by decide⟩ = true := rfl

/-- `bits` cells agree with `OXPattern.fromOX` by construction (no cast
    needed — types are definitionally aligned). -/
example (s : String) : (bits s).cell = (fromOX s).snd := rfl

/-- An R₂ bit-pattern: `bits "xo"` should have cell = R.xo. -/
example : (bits "xo").cell = R.xo := by
  funext i; fin_cases i <;> rfl

example : (bits "ox").cell = R.ox := by
  funext i; fin_cases i <;> rfl

/-- Derive wrappers pass cell through. -/
example (s : String) (r : Nat) : (derive r (bits s)).cell = (bits s).cell := rfl

/-- The 8-bit byte at R₈ from an o/x string. -/
example : (bits "ooxoxoxo").level = 8 := rfl
example : (bits "ooxoxoxo").cell ⟨7, by decide⟩ = false := rfl
example : (bits "ooxoxoxo").cell ⟨2, by decide⟩ = true := rfl

/-! ### Cell composition checks (Item 2 / cell laws) -/

/-- `compose (bits "x") (bits "x")` at R₁: XOR of true with itself = false. -/
example : (compose (bits "x") (bits "x")).cell ⟨0, by decide⟩ = false := by
  decide

/-- `compose (bits "x") (bits "o")` at R₁: XOR true ⊕ false = true. -/
example : (compose (bits "x") (bits "o")).cell ⟨0, by decide⟩ = true := by
  decide

/-- `square (bits "x") (bits "x")` at R₂: cell at pos 0 = x = true, pos 1 = x = true.
    Pointwise: matches `R.xx`. -/
example : (square (bits "x") (bits "x")).cell ⟨0, by decide⟩ = true := by decide
example : (square (bits "x") (bits "x")).cell ⟨1, by decide⟩ = true := by decide

/-- `square (bits "x") (bits "o")` at R₂: pos 0 = x (true), pos 1 = o (false). -/
example : (square (bits "x") (bits "o")).cell ⟨0, by decide⟩ = true := by decide
example : (square (bits "x") (bits "o")).cell ⟨1, by decide⟩ = false := by decide

/-- `square (bits "o") (bits "x")` at R₂: pos 0 = o, pos 1 = x. -/
example : (square (bits "o") (bits "x")).cell ⟨0, by decide⟩ = false := by decide
example : (square (bits "o") (bits "x")).cell ⟨1, by decide⟩ = true := by decide

/-- `modal Shi.ji (bits "o")` at R₂: `ji = xo` (V₄), bits "o" has level 1, cell = false@0.
    Result at pos 0: xor (ji at 0) (bits at 0) = xor true false = true. -/
example : (modal Shi.ji (bits "o")).cell ⟨0, by decide⟩ = true := by decide

/-- `derive` is cell pass-through at every level. -/
example (r : Nat) (s : String) : (derive r (bits s)).cell = (bits s).cell := rfl

end Concept

end SSBX.Foundation.Representation
