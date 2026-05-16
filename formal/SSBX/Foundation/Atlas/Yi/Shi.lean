/-
# Foundation.Atlas.Yi.Shi — Atlas-layer naming on R 2 (one core: R-family)

Per `wen-substrate.md` v1.4 §3.7.8 (distinction monism), R-family is the
**one mathematical core**.  `Shi := R 2` is the canonical algebraic-class
realisation (δ = Bool) at level 2; this file provides the **Atlas-layer
semantic overlay** assigning the temporal-modality names {dao, ji, jin, wei}
to the four bit-pattern elements of R 2 (= oo / xo / xx / ox).

| Name  | Han | Bit pattern (s 0, s 1) | Reading                |
|-------|-----|------------------------|------------------------|
| `dao` | 道  | (false, false)         | identity (V₄ unit)     |
| `ji`  | 已  | (true,  false)         | P-like (past closed)   |
| `jin` | 今  | (true,  true)          | PT (now)               |
| `wei` | 未  | (false, true)          | T-like (future open)   |

Convention `o = false`, `x = true` — same as the rest of `Atlas/Yi/`.

The naming overlay is given by:

* `complement` (印, P-like axis flip): `dao ↔ ji, jin ↔ wei`.
* `reverse`    (投, T-like axis flip): `dao ↔ wei, ji ↔ jin`.
* `cuoZong = complement ∘ reverse`   : `dao ↔ jin, ji ↔ wei` (PT).

All three are involutions; `complement` and `reverse` commute; together
with the identity they form the Klein four-group V₄.

## Doctrinal anchor

* R 2 carries the Klein-four-group structure as its native AddCommGroup
  under XOR; see wen-substrate v1.4 chapter 01 'P6 — temporal/causal modality'.
* `v4-foundation.md` v0.5 §4 (Shi V₄), §15.2 (Shi binding).
-/

import SSBX.Foundation.Atlas.Yi.Names

namespace SSBX.Foundation.Atlas.Yi

open SSBX.Foundation.R

namespace Shi

/-! ## § 1 The four named V₄ elements -/

/-- 道 (Dào) — V₄ identity, `(false, false)`. -/
@[match_pattern] def dao : Shi := fun _ => false

/-- 已 (Yǐ) — "past-closed", `(true, false)`. -/
@[match_pattern] def ji : Shi := fun i => decide (i.val = 0)

/-- 今 (Jīn) — "now / PT", `(true, true)`. -/
@[match_pattern] def jin : Shi := fun _ => true

/-- 未 (Wèi) — "future-open", `(false, true)`. -/
@[match_pattern] def wei : Shi := fun i => decide (i.val = 1)

/-- The four 时态 elements in canonical order. -/
def all : List Shi := [dao, ji, jin, wei]

theorem all_length : all.length = 4 := rfl

/-! ## § 2 Encoding to a 2-bit `Nat` (for distinctness proofs) -/

/-- Encode a Shi as a 2-bit `Nat` in 0..3 (s 0 is the high bit). -/
def toNat (s : Shi) : Nat :=
  (if s ⟨0, by decide⟩ then 2 else 0) + (if s ⟨1, by decide⟩ then 1 else 0)

@[simp] theorem toNat_dao : toNat dao = 0 := rfl
@[simp] theorem toNat_ji  : toNat ji  = 2 := rfl
@[simp] theorem toNat_jin : toNat jin = 3 := rfl
@[simp] theorem toNat_wei : toNat wei = 1 := rfl

/-- The 4 named Shi values are distinct. -/
theorem all_nodup : all.Nodup := by
  have : (all.map toNat).Nodup := by
    show ([0, 2, 3, 1] : List Nat).Nodup
    decide
  exact List.Nodup.of_map _ this

/-! ## § 3 The V₄ operators -/

/-- 印 (yìn), V₄ "P-like" axis flip: toggles s 0.
    On the named elements: `dao ↔ ji, jin ↔ wei`. -/
def complement (s : Shi) : Shi := fun i =>
  match i with
  | ⟨0, _⟩ => !(s ⟨0, by decide⟩)
  | ⟨1, _⟩ => s ⟨1, by decide⟩

/-- 投 (tóu), V₄ "T-like" axis flip: toggles s 1.
    On the named elements: `dao ↔ wei, ji ↔ jin`. -/
def reverse (s : Shi) : Shi := fun i =>
  match i with
  | ⟨0, _⟩ => s ⟨0, by decide⟩
  | ⟨1, _⟩ => !(s ⟨1, by decide⟩)

/-- 错综 = complement ∘ reverse (V₄ "PT" central element).
    On the named elements: `dao ↔ jin, ji ↔ wei`. -/
def cuoZong (s : Shi) : Shi := complement (reverse s)

/-! ## § 4 Named-element computations -/

@[simp] theorem complement_dao : complement dao = ji := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem complement_ji : complement ji = dao := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem complement_jin : complement jin = wei := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem complement_wei : complement wei = jin := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem reverse_dao : reverse dao = wei := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem reverse_ji : reverse ji = jin := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem reverse_jin : reverse jin = ji := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem reverse_wei : reverse wei = dao := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-! ## § 5 V₄ group laws -/

/-- complement is involutive. -/
theorem complement_involutive (s : Shi) : complement (complement s) = s := by
  funext i
  match i with
  | ⟨0, _⟩ => simp [complement]
  | ⟨1, _⟩ => rfl

/-- reverse is involutive. -/
theorem reverse_involutive (s : Shi) : reverse (reverse s) = s := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => simp [reverse]

/-- complement and reverse commute. -/
theorem complement_reverse_comm (s : Shi) :
    complement (reverse s) = reverse (complement s) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- cuoZong (= P∘T = T∘P) is involutive. -/
theorem cuoZong_involutive (s : Shi) : cuoZong (cuoZong s) = s := by
  unfold cuoZong
  rw [← complement_reverse_comm, complement_involutive, reverse_involutive]

/-- cuoZong = reverse ∘ complement (commuted form). -/
theorem cuoZong_eq_reverse_complement (s : Shi) :
    cuoZong s = reverse (complement s) := by
  unfold cuoZong; exact complement_reverse_comm s

end Shi

end SSBX.Foundation.Atlas.Yi
