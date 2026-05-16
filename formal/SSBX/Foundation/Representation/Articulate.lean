/-
# Foundation.Representation.Articulate — Strategy D: self-articulation fixed-point

Per the representation-closure programme (`wen-substrate.md` v1.4
§Representation), the deepest of the three locator strategies is to
treat `locate` as the **fixed point of self-articulation**: a concept's
R-Family level is the level at which iterated self-articulation
stabilises.

The implementation here:

1. Defines `articulate : Concept → Concept` as a structural normaliser
   that **strips P7 derivation wrappers** (the "decorative" layer that
   does not change the carrier).
2. Proves `articulate` is **level-preserving** (Strategy D's basic
   structural lemma).
3. Proves `articulate` is **idempotent** — one pass suffices, so the
   fixed point is reached after a single application.
4. Defines `iterateArticulate` for explicit fuel-bounded iteration.
5. Defines `locateByFixedPoint` as the level at the fixed point.
6. Proves `locateByFixedPoint c = c.level` — the **three-locator
   agreement theorem** with Strategy A.

The philosophical content: **a concept's R-level is what survives
unbounded self-articulation**.  P7 (derivation) is the only constructor
that can be stripped without information loss; everything else is
load-bearing.

## Doctrinal anchor

* `wen-substrate.md` v1.4 §Representation.
* Strategy D from the representation-closure brainstorm.
* P7 (derivation rules) carries inferential content but no carrier
  enlargement — this is what makes derive-stripping the canonical
  articulation step.
-/

import SSBX.Foundation.Representation.Concept
import SSBX.Foundation.Representation.Signature

namespace SSBX.Foundation.Representation

open SSBX.Foundation.Atlas.Yi

namespace Concept

/-! ## § 1 The `articulate` normaliser -/

/-- `articulate c` performs one round of structural self-articulation:
    it strips all `derive` wrappers (P7 decorations) and recurses into
    sub-concepts.  Every other constructor is preserved structurally —
    those constructors are carrier-bearing (they affect `level`) and
    cannot be reduced without information loss.

    Termination: structural recursion on the sub-concept argument; the
    `derive _ c` case recurses on `c`, a strict subterm. -/
def articulate : Concept → Concept
  | .derive _ c  => articulate c
  | .atom s      => .atom s
  | .bits s      => .bits s
  | .compose a b => .compose (articulate a) (articulate b)
  | .square a b  => .square (articulate a) (articulate b)
  | .modal v c   => .modal v (articulate c)
  | .hom a b     => .hom (articulate a) (articulate b)

@[simp] theorem articulate_atom (s : String) :
    articulate (atom s) = atom s := rfl

@[simp] theorem articulate_bits (s : String) :
    articulate (bits s) = bits s := rfl

@[simp] theorem articulate_compose (a b : Concept) :
    articulate (compose a b) = compose (articulate a) (articulate b) := rfl

@[simp] theorem articulate_square (a b : Concept) :
    articulate (square a b) = square (articulate a) (articulate b) := rfl

@[simp] theorem articulate_modal (v : Shi) (c : Concept) :
    articulate (modal v c) = modal v (articulate c) := rfl

@[simp] theorem articulate_hom (a b : Concept) :
    articulate (hom a b) = hom (articulate a) (articulate b) := rfl

@[simp] theorem articulate_derive (r : Nat) (c : Concept) :
    articulate (derive r c) = articulate c := rfl

/-! ## § 2 Level preservation -/

/-- **Level preservation under self-articulation** — the central
    structural lemma of Strategy D.  Stripping derivations does not
    change the R-Family level because `derive` is level-preserving by
    construction (`level (derive r c) = c.level`). -/
theorem articulate_preserves_level (c : Concept) :
    (articulate c).level = c.level := by
  induction c with
  | atom s => rfl
  | bits s => rfl
  | compose a b iha ihb =>
      simp [articulate, level, iha, ihb]
  | square a b iha ihb =>
      simp [articulate, level, iha, ihb]
  | modal v c ihc =>
      simp [articulate, level, ihc]
  | hom a b iha ihb =>
      simp [articulate, level, iha, ihb]
  | derive r c ihc =>
      simp [articulate, level, ihc]

/-! ## § 3 Idempotence — one pass suffices -/

/-- The predicate "concept has no derive wrappers" — a concept is in
    `articulate`'s image iff it satisfies this. -/
def isNormalised : Concept → Prop
  | .atom _      => True
  | .bits _      => True
  | .compose a b => a.isNormalised ∧ b.isNormalised
  | .square a b  => a.isNormalised ∧ b.isNormalised
  | .modal _ c   => c.isNormalised
  | .hom a b     => a.isNormalised ∧ b.isNormalised
  | .derive _ _  => False

/-- One pass of `articulate` produces a normalised concept. -/
theorem articulate_isNormalised (c : Concept) :
    (articulate c).isNormalised := by
  induction c with
  | atom s => trivial
  | bits s => trivial
  | compose a b iha ihb =>
      simp [articulate, isNormalised]
      exact ⟨iha, ihb⟩
  | square a b iha ihb =>
      simp [articulate, isNormalised]
      exact ⟨iha, ihb⟩
  | modal v c ihc =>
      simp [articulate, isNormalised]
      exact ihc
  | hom a b iha ihb =>
      simp [articulate, isNormalised]
      exact ⟨iha, ihb⟩
  | derive r c ihc =>
      simp [articulate]
      exact ihc

/-- Normalised concepts are fixed by `articulate`. -/
theorem articulate_fix_of_normalised {c : Concept} (hn : c.isNormalised) :
    articulate c = c := by
  induction c with
  | atom s => rfl
  | bits s => rfl
  | compose a b iha ihb =>
      obtain ⟨ha, hb⟩ := hn
      simp [articulate, iha ha, ihb hb]
  | square a b iha ihb =>
      obtain ⟨ha, hb⟩ := hn
      simp [articulate, iha ha, ihb hb]
  | modal v c ihc =>
      simp [articulate, ihc hn]
  | hom a b iha ihb =>
      obtain ⟨ha, hb⟩ := hn
      simp [articulate, iha ha, ihb hb]
  | derive r c _ihc =>
      exact (hn).elim

/-- **Articulate is idempotent.**  One application reaches the fixed
    point; further applications do nothing. -/
theorem articulate_idempotent (c : Concept) :
    articulate (articulate c) = articulate c :=
  articulate_fix_of_normalised (articulate_isNormalised c)

/-! ## § 4 Fuel-bounded iteration -/

/-- `iterateArticulate n c` applies `articulate` exactly `n` times.
    By idempotence, `iterateArticulate n c = articulate c` whenever
    `n ≥ 1`. -/
def iterateArticulate : Nat → Concept → Concept
  | 0,     c => c
  | n+1,   c => iterateArticulate n (articulate c)

@[simp] theorem iterateArticulate_zero (c : Concept) :
    iterateArticulate 0 c = c := rfl

@[simp] theorem iterateArticulate_succ (n : Nat) (c : Concept) :
    iterateArticulate (n+1) c = iterateArticulate n (articulate c) := rfl

/-- Level is preserved across any iteration count. -/
theorem iterateArticulate_preserves_level (n : Nat) (c : Concept) :
    (iterateArticulate n c).level = c.level := by
  induction n generalizing c with
  | zero => rfl
  | succ k ih =>
      simp [iterateArticulate]
      rw [ih (articulate c), articulate_preserves_level]

/-- After `≥ 1` step, the iteration is the same as a single articulate
    (by idempotence). -/
theorem iterateArticulate_succ_eq_articulate (n : Nat) (c : Concept) :
    iterateArticulate (n+1) c = articulate c := by
  induction n generalizing c with
  | zero => rfl
  | succ k ih =>
      rw [iterateArticulate_succ, ih (articulate c), articulate_idempotent]

/-! ## § 5 `locateByFixedPoint` and the agreement theorem -/

/-- The **fixed-point locator**: the level reached after sufficient
    self-articulation iterations.  Fuel = 8 (matches the R₈ ceiling)
    is more than enough by idempotence — a single step suffices. -/
def locateByFixedPoint (c : Concept) : Nat :=
  (iterateArticulate 8 c).level

/-- **Strategy A ↔ Strategy D agreement.**  The fixed-point locator
    returns the same value as the direct (compositional) locator on
    every concept.

    This is the central representation-closure theorem: locate via
    self-articulation fixed point and locate via structural induction
    coincide; both compute the same R-Family level. -/
theorem locateByFixedPoint_eq_level (c : Concept) :
    locateByFixedPoint c = c.level := by
  show (iterateArticulate 8 c).level = c.level
  exact iterateArticulate_preserves_level 8 c

/-! ## § 6 Worked examples — fixed-point computation -/

example : locateByFixedPoint (atom "x") = 1 := by
  rw [locateByFixedPoint_eq_level]; rfl

example : locateByFixedPoint (modal Shi.dao (atom "x")) = 2 := by
  rw [locateByFixedPoint_eq_level]; rfl

/-- Strip derivations: a derivation-wrapped concept articulates to its
    derivation-free core. -/
example :
    articulate (derive 7 (derive 3 (atom "x"))) = atom "x" := by
  simp [articulate]

/-- Nested derivations are flattened to atoms (under `articulate`). -/
example :
    articulate (derive 1 (compose (derive 2 (atom "a")) (atom "b")))
      = compose (atom "a") (atom "b") := by
  simp [articulate]

/-- The fixed-point locator is invariant under derivation depth. -/
example (n : Nat) (c : Concept) :
    locateByFixedPoint (derive n c) = locateByFixedPoint c := by
  simp [locateByFixedPoint_eq_level, level]

end Concept

/-! ## § 7 The three-locator agreement summary -/

/-- **Strategy A ↔ D agreement.**  For every concept `c`, the
    compositional locator and the fixed-point locator coincide. -/
theorem locator_agreement_AD (c : Concept) :
    Concept.locateByFixedPoint c = c.level :=
  Concept.locateByFixedPoint_eq_level c

/-- **Strategy A ↔ B agreement.**  For every concept `c`, the
    compositional locator and the signature locator coincide. -/
theorem locator_agreement_AB (c : Concept) :
    c.signatureLevel = c.level :=
  Concept.signature_level_eq c

/-- **Strategy B ↔ D agreement.**  For every concept `c`, the signature
    locator and the fixed-point locator coincide. -/
theorem locator_agreement_BD (c : Concept) :
    c.signatureLevel = Concept.locateByFixedPoint c := by
  rw [locator_agreement_AB, ← locator_agreement_AD]

/-- **Master representation-closure theorem (three-way agreement).**

    For every concept `c`, all three locators — compositional (A),
    signature (B), and fixed-point (D) — return the same R-Family level.

    This is the formal completion of the representation-closure
    programme: the existence claim "concept ↦ R-tower coordinate" is
    realised by three independent constructive locators, which provably
    coincide on every concept. -/
theorem locator_agreement (c : Concept) :
    Concept.locateByFixedPoint c = c.level ∧
    c.signatureLevel = c.level ∧
    c.signatureLevel = Concept.locateByFixedPoint c := by
  refine ⟨locator_agreement_AD c, locator_agreement_AB c, locator_agreement_BD c⟩

/-! ## § 8 Cross-strategy worked examples (level-by-level) -/

namespace Concept

/-- R₁ — bare atom: all three locators report level 1. -/
example :
    (atom "x").level = 1 ∧
    (atom "x").signatureLevel = 1 ∧
    locateByFixedPoint (atom "x") = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · show (1 : Nat) = 1; rfl
  · show (1 : Nat) = 1; rfl
  · rw [locateByFixedPoint_eq_level]; rfl

/-- R₂ — modal atom: all three locators report level 2. -/
example :
    (modal Shi.dao (atom "x")).level = 2 ∧
    (modal Shi.dao (atom "x")).signatureLevel = 2 ∧
    locateByFixedPoint (modal Shi.dao (atom "x")) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · show (max 1 2 : Nat) = 2; rfl
  · show (max 1 2 : Nat) = 2; rfl
  · rw [locateByFixedPoint_eq_level]; rfl

/-- R₂ — atom squared: all three locators report level 2. -/
example :
    (square (atom "x") (atom "y")).level = 2 ∧
    (square (atom "x") (atom "y")).signatureLevel = 2 ∧
    locateByFixedPoint (square (atom "x") (atom "y")) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · show (2 * max 1 1 : Nat) = 2; rfl
  · show (2 * max 1 1 : Nat) = 2; rfl
  · rw [locateByFixedPoint_eq_level]; rfl

/-- R₄ — hom of atoms: all three locators report level 4. -/
example :
    (hom (atom "x") (atom "y")).level = 4 ∧
    (hom (atom "x") (atom "y")).signatureLevel = 4 ∧
    locateByFixedPoint (hom (atom "x") (atom "y")) = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · show (max (2 * max 1 1) 4 : Nat) = 4; rfl
  · show (max (2 * max 1 1) 4 : Nat) = 4; rfl
  · rw [locateByFixedPoint_eq_level]; rfl

/-- R₈ — triply-nested squaring of atoms reaches the byte ceiling. -/
example :
    let c := square (square (square (atom "x") (atom "y"))
                            (square (atom "x") (atom "y")))
                    (square (square (atom "x") (atom "y"))
                            (square (atom "x") (atom "y")))
    c.level = 8 := rfl

/-- Derivation wrappers are invisible to the direct locator. -/
example (n : Nat) :
    (derive n (modal Shi.jin (square (atom "x") (atom "y")))).level =
        (modal Shi.jin (square (atom "x") (atom "y"))).level := rfl

end Concept

end SSBX.Foundation.Representation
