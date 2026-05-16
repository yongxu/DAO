/-
# Foundation.Representation.Signature — Strategy B: invariant fingerprinting

Per the representation-closure programme (`wen-substrate.md` v1.4
§Representation), an alternative locator strategy is to extract a
**structural signature** from any concept and reconstruct the R-Family
level from the recorded invariants.

A `ConceptSignature` records:

* `level`            — the R-Family level (matches `Concept.level`).
* `modalActive`      — whether any sub-tree carries a `modal` stamp
                       (P6 active flag).
* `homInternalised`  — whether any sub-tree contains `hom` (P5 active flag).
* `squaredEver`      — whether any sub-tree contains `square` (P5 step flag).
* `recursionDepth`   — syntactic depth of the concept tree (P4 / P7).
* `derivationDepth`  — number of `derive` wrappers (P7-only depth).

The level field captures the R-Family index directly; the other flags
are independent structural invariants useful for downstream analysis
(e.g., classifying which P-axes are activated).

The map `ConceptSignature.toLevel` returns the level field; the central
theorem `signature_level_eq` shows it agrees with `Concept.level` on
every concept (proved by structural induction).

## Doctrinal anchor

* `wen-substrate.md` v1.4 §Representation.
* Strategy B from the representation-closure brainstorm.
-/

import SSBX.Foundation.Representation.Concept

namespace SSBX.Foundation.Representation

open SSBX.Foundation.Atlas.Yi

/-! ## § 1 The `ConceptSignature` structure -/

/-- Structural signature of a `Concept`.

    | Field             | P-axis             | Role                              |
    |-------------------|--------------------|-----------------------------------|
    | `level`           | (locator)          | the R-Family level                |
    | `modalActive`     | P6                 | any modal stamp present?          |
    | `homInternalised` | P5                 | any Hom-internalisation present?  |
    | `squaredEver`     | P5 squaring        | any squaring constructor present? |
    | `recursionDepth`  | P4                 | syntactic tree depth              |
    | `derivationDepth` | P7                 | derive-wrapper count              |
-/
structure ConceptSignature where
  level            : Nat
  modalActive      : Bool
  homInternalised  : Bool
  squaredEver      : Bool
  recursionDepth   : Nat
  derivationDepth  : Nat
  deriving Inhabited

namespace ConceptSignature

/-- The signature of an atomic concept: level 1, no flags. -/
def atomic : ConceptSignature where
  level := 1
  modalActive := false
  homInternalised := false
  squaredEver := false
  recursionDepth := 1
  derivationDepth := 0

/-- The level reconstructed from the signature — just the `level` field. -/
def toLevel (sig : ConceptSignature) : Nat := sig.level

@[simp] theorem toLevel_def (sig : ConceptSignature) :
    sig.toLevel = sig.level := rfl

@[simp] theorem toLevel_atomic : atomic.toLevel = 1 := rfl

end ConceptSignature

namespace Concept

/-! ## § 2 `signature` — extract invariants from a `Concept` -/

/-- Extract the structural signature of a concept by single-pass induction.

    Flags (modalActive, homInternalised, squaredEver) propagate from
    sub-trees to the parent; depths add accordingly; the `level` field
    is computed by the same recursion as `Concept.level`. -/
def signature : Concept → ConceptSignature
  | .atom _ =>
      { level := 1
        modalActive := false
        homInternalised := false
        squaredEver := false
        recursionDepth := 1
        derivationDepth := 0 }
  | .compose a b =>
      let sa := a.signature
      let sb := b.signature
      { level := max sa.level sb.level
        modalActive := sa.modalActive || sb.modalActive
        homInternalised := sa.homInternalised || sb.homInternalised
        squaredEver := sa.squaredEver || sb.squaredEver
        recursionDepth := max sa.recursionDepth sb.recursionDepth + 1
        derivationDepth := max sa.derivationDepth sb.derivationDepth }
  | .square a b =>
      let sa := a.signature
      let sb := b.signature
      { level := 2 * max sa.level sb.level
        modalActive := sa.modalActive || sb.modalActive
        homInternalised := sa.homInternalised || sb.homInternalised
        squaredEver := true
        recursionDepth := max sa.recursionDepth sb.recursionDepth + 1
        derivationDepth := max sa.derivationDepth sb.derivationDepth }
  | .modal _ c =>
      let sc := c.signature
      { level := max sc.level 2
        modalActive := true
        homInternalised := sc.homInternalised
        squaredEver := sc.squaredEver
        recursionDepth := sc.recursionDepth + 1
        derivationDepth := sc.derivationDepth }
  | .hom a b =>
      let sa := a.signature
      let sb := b.signature
      { level := max (2 * max sa.level sb.level) 4
        modalActive := sa.modalActive || sb.modalActive
        homInternalised := true
        squaredEver := sa.squaredEver || sb.squaredEver
        recursionDepth := max sa.recursionDepth sb.recursionDepth + 1
        derivationDepth := max sa.derivationDepth sb.derivationDepth }
  | .derive _ c =>
      let sc := c.signature
      { sc with
        derivationDepth := sc.derivationDepth + 1
        recursionDepth := sc.recursionDepth + 1 }

@[simp] theorem signature_atom (s : String) :
    (atom s).signature.level = 1 := rfl

@[simp] theorem signature_compose_level (a b : Concept) :
    (compose a b).signature.level = max a.signature.level b.signature.level := rfl

@[simp] theorem signature_square_level (a b : Concept) :
    (square a b).signature.level = 2 * max a.signature.level b.signature.level := rfl

@[simp] theorem signature_modal_level (v : Shi) (c : Concept) :
    (modal v c).signature.level = max c.signature.level 2 := rfl

@[simp] theorem signature_hom_level (a b : Concept) :
    (hom a b).signature.level = max (2 * max a.signature.level b.signature.level) 4 := rfl

@[simp] theorem signature_derive_level (r : Nat) (c : Concept) :
    (derive r c).signature.level = c.signature.level := rfl

/-! ## § 3 `signatureLevel` and the agreement theorem -/

/-- The signature-derived level: the level reconstructed from the
    invariants extracted by `signature`. -/
def signatureLevel (c : Concept) : Nat := c.signature.toLevel

@[simp] theorem signatureLevel_def (c : Concept) :
    c.signatureLevel = c.signature.level := rfl

/-- The signature's `level` field equals `Concept.level`. -/
theorem signature_level (c : Concept) :
    c.signature.level = c.level := by
  induction c with
  | atom s => rfl
  | compose a b iha ihb =>
      show max a.signature.level b.signature.level = max a.level b.level
      rw [iha, ihb]
  | square a b iha ihb =>
      show 2 * max a.signature.level b.signature.level = 2 * max a.level b.level
      rw [iha, ihb]
  | modal v c ihc =>
      show max c.signature.level 2 = max c.level 2
      rw [ihc]
  | hom a b iha ihb =>
      show max (2 * max a.signature.level b.signature.level) 4
              = max (2 * max a.level b.level) 4
      rw [iha, ihb]
  | derive r c ihc =>
      show c.signature.level = c.level
      exact ihc

/-- **Strategy A ↔ Strategy B agreement.**  For every concept, the
    signature-locator returns the same level as the direct locator. -/
theorem signature_level_eq (c : Concept) :
    c.signatureLevel = c.level := signature_level c

/-! ## § 4 Structural flag lemmas -/

/-- Atoms have all flags `false`. -/
@[simp] theorem signature_atom_flags (s : String) :
    (atom s).signature.modalActive = false ∧
    (atom s).signature.homInternalised = false ∧
    (atom s).signature.squaredEver = false := ⟨rfl, rfl, rfl⟩

/-- A `modal`-wrapped concept always has `modalActive = true`. -/
@[simp] theorem signature_modal_flag (v : Shi) (c : Concept) :
    (modal v c).signature.modalActive = true := rfl

/-- A `hom`-wrapped concept always has `homInternalised = true`. -/
@[simp] theorem signature_hom_flag (a b : Concept) :
    (hom a b).signature.homInternalised = true := rfl

/-- A `square`-wrapped concept always has `squaredEver = true`. -/
@[simp] theorem signature_square_flag (a b : Concept) :
    (square a b).signature.squaredEver = true := rfl

/-! ## § 5 Worked examples — signature inspection -/

example : (atom "x").signature = ConceptSignature.atomic := rfl

example : (modal Shi.dao (atom "x")).signature.modalActive = true := rfl
example : (modal Shi.dao (atom "x")).signature.level = 2 := rfl

example : (square (atom "x") (atom "x")).signature.squaredEver = true := rfl
example : (square (atom "x") (atom "x")).signature.level = 2 := rfl

example : (hom (atom "x") (atom "x")).signature.homInternalised = true := rfl
example : (hom (atom "x") (atom "x")).signature.level = 4 := rfl

/-- Signature-locator agrees with direct locator on representative cases. -/
example : signatureLevel (atom "x") = (atom "x").level := signature_level_eq _
example : signatureLevel (modal Shi.dao (atom "x")) = (modal Shi.dao (atom "x")).level :=
  signature_level_eq _
example : signatureLevel (square (atom "x") (atom "x"))
            = (square (atom "x") (atom "x")).level := signature_level_eq _
example : signatureLevel (hom (atom "x") (atom "x")) = (hom (atom "x") (atom "x")).level :=
  signature_level_eq _

end Concept

end SSBX.Foundation.Representation
