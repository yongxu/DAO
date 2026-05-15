/-
# `SSBX.Foundation.Wen.X2CodesUniqueness` — partial discharge of Open Problem #2

Companion to `X2Codes.lean` (existence) and `docs-next/10_formal_形式/wen-substrate.md`
§4.7bis.5 (Open Problem #2: uniqueness of UG candidate).

## What this file does

* Defines `UGCandidate.Hom` and `UGCandidate.Iso` — structure-preserving
  maps and equivalences between UG candidates (preserve `dual` and `atom`).
* Proves the **cardinality half** of uniqueness: any `UGCandidate` with
  `axes = 8` has carrier `Equiv`-equivalent to `WenCode` as a finite type
  (`carrier_equiv_wenCode`).
* Extends `UGCandidate` to `UGCandidateRich`, which additionally carries
  the palindrome and comp-palindrome involutions and witnesses the
  $(\mathbb{Z}/2)^2$ duality action — capturing condition (2) in its
  full strength.  `wenCodeUGRich` extends `wenCodeUG` to this richer
  spec, again with no sorry.
* States the full uniqueness conjecture as `Prop`
  (`OpenProblem2.uniqueness_conjecture`) so that future work can target
  it directly.  Resolving it requires axiomatising minimality and
  naming-density, sketched in §4.7bis.5.

## What this file does **not** do (open work)

* Prove the full uniqueness conjecture.  Doing so requires:
  (a) a precise minimality clause forcing `axes = 8` from semantic
      necessity (the 4+4 本/征 split has to be forced from the
      structure, not assumed);
  (b) a coverage / naming-density predicate (古文 seed positions
      forced by palindrome ∩ X² and X² ∩ compPal symmetry corners);
  (c) the F₂-forcing chain from `wen-substrate.md` §8.4 to fix the
      field of the basis.

  These are research tasks, not mechanical Lean exercises.  This file
  prepares the formal scaffold so each can be plugged in as it lands.
-/
import SSBX.Foundation.Wen.X2Codes
import Mathlib.Data.Fintype.Card

namespace SSBX.Foundation.Wen.X2Codes

/-! ## §1  Homomorphisms and isomorphisms of UG candidates -/

/-- A `UGCandidate.Hom U V` is a `Carrier`-level map that intertwines
the `dual` involutions and preserves the `atom` partial naming. -/
structure UGCandidate.Hom (U V : UGCandidate) where
  map : U.Carrier → V.Carrier
  dual_comm : ∀ c, map (U.dual c) = V.dual (map c)
  atom_comm : ∀ c, V.atom (map c) = U.atom c

/-- A `UGCandidate.Iso U V` is a structure-preserving equivalence. -/
structure UGCandidate.Iso (U V : UGCandidate) where
  toFun  : U.Carrier → V.Carrier
  invFun : V.Carrier → U.Carrier
  left_inv  : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  dual_comm : ∀ c, toFun (U.dual c) = V.dual (toFun c)
  atom_comm : ∀ c, V.atom (toFun c) = U.atom c

namespace UGCandidate.Iso

/-- Reflexivity: every `UGCandidate` is isomorphic to itself. -/
def refl (U : UGCandidate) : UGCandidate.Iso U U where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  dual_comm := fun _ => rfl
  atom_comm := fun _ => rfl

/-- Symmetry. -/
def symm {U V : UGCandidate} (h : UGCandidate.Iso U V) :
    UGCandidate.Iso V U where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv
  dual_comm := by
    intro c
    have key : h.toFun (U.dual (h.invFun c)) = V.dual c := by
      rw [h.dual_comm, h.right_inv]
    have : h.invFun (h.toFun (U.dual (h.invFun c))) = h.invFun (V.dual c) :=
      congrArg h.invFun key
    rw [h.left_inv] at this
    exact this.symm
  atom_comm := by
    intro c
    have := h.atom_comm (h.invFun c)
    rw [h.right_inv] at this
    exact this.symm

/-- Transitivity. -/
def trans {U V W : UGCandidate}
    (h₁ : UGCandidate.Iso U V) (h₂ : UGCandidate.Iso V W) :
    UGCandidate.Iso U W where
  toFun := h₂.toFun ∘ h₁.toFun
  invFun := h₁.invFun ∘ h₂.invFun
  left_inv := by
    intro c
    simp only [Function.comp_apply]
    rw [h₂.left_inv, h₁.left_inv]
  right_inv := by
    intro c
    simp only [Function.comp_apply]
    rw [h₁.right_inv, h₂.right_inv]
  dual_comm := by
    intro c
    simp only [Function.comp_apply]
    rw [h₁.dual_comm, h₂.dual_comm]
  atom_comm := by
    intro c
    simp only [Function.comp_apply]
    rw [h₂.atom_comm, h₁.atom_comm]

end UGCandidate.Iso

/-! ## §2  Cardinality half of uniqueness

For any `UGCandidate` with `axes = 8`, the carrier has cardinality `256`,
hence is `Equiv`-equivalent to `WenCode = Fin 256` as a finite type.
This is the *type-level* uniqueness; lifting it to a `UGCandidate.Iso`
requires further structural constraints (handled by `UGCandidateRich`
below). -/

theorem carrier_card_eq_256 (U : UGCandidate) (h : U.axes = 8) :
    Fintype.card U.Carrier = 256 := by
  rw [U.card_eq, h]; decide

theorem carrier_equiv_wenCode (U : UGCandidate) (h : U.axes = 8) :
    Nonempty (U.Carrier ≃ WenCode) := by
  have hcard : Fintype.card U.Carrier = Fintype.card WenCode := by
    rw [carrier_card_eq_256 U h]
    simp [Fintype.card_fin]
  exact ⟨Fintype.equivOfCardEq hcard⟩

/-! ## §3  `UGCandidateRich` — closure under all three involutions

Strengthens `UGCandidate` (which only requires `dual`) to additionally
demand `palindrome` and `compPal`, with the commutativity that makes
`{id, dual, palindrome, compPal}` a $(\mathbb{Z}/2)^2$ group action. -/

structure UGCandidateRich extends UGCandidate where
  /-- Mirror involution (axis-reversal analogue). -/
  palindrome : Carrier → Carrier
  palindrome_involutive : Function.Involutive palindrome
  /-- Anti-mirror = dual ∘ palindrome. -/
  compPal : Carrier → Carrier
  compPal_eq : ∀ c, compPal c = dual (palindrome c)
  /-- `dual` and `palindrome` commute. -/
  dual_palindrome_comm : ∀ c, dual (palindrome c) = palindrome (dual c)

namespace UGCandidateRich

/-- `compPal` is automatically involutive from `dual` ∘ `palindrome`
commutativity and the involutivity of each factor. -/
theorem compPal_involutive (U : UGCandidateRich) :
    Function.Involutive U.compPal := by
  intro c
  rw [U.compPal_eq, U.compPal_eq, U.dual_palindrome_comm,
      U.dual_involutive, U.palindrome_involutive]

end UGCandidateRich

/-- `wenCodeUG` extends to a `UGCandidateRich`. -/
def wenCodeUGRich : UGCandidateRich where
  toUGCandidate := wenCodeUG
  palindrome := WenCode.palindrome
  palindrome_involutive := WenCode.palindrome_involutive
  compPal := WenCode.compPal
  compPal_eq := fun _ => rfl
  dual_palindrome_comm := WenCode.dual_palindrome_comm

/-! ## §4  Open Problem #2 — the full uniqueness statement

We state — but do not prove — the conjecture.  Resolving it requires
(a) minimality, (b) naming-density, (c) the F₂-forcing chain; see
`wen-substrate.md` §4.7bis.5 for the route. -/

namespace OpenProblem2

/-- A `UGCandidateRich` is **8-axis** iff its underlying `axes = 8`. -/
def IsEightAxis (U : UGCandidateRich) : Prop := U.axes = 8

/-- A `UGCandidateRich` has **seeded naming** iff at least 8 cells are
named — matching the minimum-information atom seed used in
`X2Codes.lean` (the 4 max-symmetric corners + the 4 Walsh basis cells). -/
def HasSeededNaming (U : UGCandidateRich) : Prop :=
  ∃ S : Finset U.Carrier, S.card = 8 ∧ ∀ c ∈ S, U.atom c ≠ none

/-- The uniqueness conjecture (Open Problem #2):
every 8-axis `UGCandidateRich` with seeded naming is `UGCandidate.Iso`-
equivalent to `wenCodeUGRich` at the underlying `UGCandidate` level.

This is **not** proved here; resolving it requires the work outlined
in `wen-substrate.md` §4.7bis.5. -/
def uniqueness_conjecture : Prop :=
  ∀ U : UGCandidateRich,
    IsEightAxis U → HasSeededNaming U →
    Nonempty (UGCandidate.Iso U.toUGCandidate wenCodeUGRich.toUGCandidate)

/-- The cardinality precondition of the conjecture is *already* settled:
under `IsEightAxis`, the carrier is type-equivalent to `WenCode`.  What
remains is to upgrade this type-level equivalence to a structure-
preserving `UGCandidate.Iso`. -/
theorem cardinality_precondition_discharged :
    ∀ U : UGCandidateRich, IsEightAxis U →
      Nonempty (U.Carrier ≃ WenCode) := by
  intro U h
  exact carrier_equiv_wenCode U.toUGCandidate h

end OpenProblem2

/-! ## §5  Self-test -/

example : (UGCandidate.Iso.refl wenCodeUG).toFun = id := rfl
example : wenCodeUGRich.toUGCandidate = wenCodeUG := rfl
example : wenCodeUGRich.palindrome = WenCode.palindrome := rfl
example : OpenProblem2.IsEightAxis wenCodeUGRich := rfl

end SSBX.Foundation.Wen.X2Codes
