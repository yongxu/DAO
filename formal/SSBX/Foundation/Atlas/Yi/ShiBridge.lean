/-
# Foundation.Atlas.Yi.ShiBridge — bridge between legacy `Shi := Bool × Bool` and new `Shi := R 2`

Per `wen-algebra` v0.6 §9 and `v4-foundation` v0.5 §15:

    legacy: Shi := YinBit × GuoBit  =  Bool × Bool   (Foundation/Atlas/Yi/Classical/Cells/R8.lean)
    new:    Shi := R 2              =  Fin 2 → Bool  (Foundation/Atlas/Yi/Names.lean)

Both encodings carry the same Klein four-group `{道, 已, 今, 未}`
(the Atlas-naming surface over `R 2`) with the same bit-pattern
convention:

| Name  | Han | Legacy (yin, guo) | New (s 0, s 1) |
|-------|-----|-------------------|----------------|
| `dao` | 道  | (false, false)    | (false, false) |
| `ji`  | 已  | (true,  false)    | (true,  false) |
| `jin` | 今  | (true,  true)     | (true,  true)  |
| `wei` | 未  | (false, true)     | (false, true)  |

This module is a **pure overlay**: it imports the new `Shi` (`Names.lean`
+ `Shi.lean`) and exposes the legacy `Bool × Bool` shape so consumer
files can migrate without modifying their pattern-matches.  No existing
module is touched; this module is additive.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9 (Atlas separation, encoding-independence).
* `v4-foundation.md` v0.5 §15.2 (Shi binding, dual encodings).
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Shi

namespace SSBX.Foundation.Atlas.Yi.ShiBridge

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 The two encodings -/

/-- Legacy Shi encoding: `Bool × Bool` (= YinBit × GuoBit per the
    Classical/Cells/R8.lean definition). -/
abbrev ShiLegacy : Type := Bool × Bool

/-- New Shi encoding: `R 2 = Fin 2 → Bool` (per Names.lean). -/
abbrev ShiNew : Type := Atlas.Yi.Shi

/-! ## § 2 Bijection between the two encodings -/

/-- Map legacy `(y, g)` to new `R 2` shape: `s 0 = y, s 1 = g`. -/
def toNew : ShiLegacy → ShiNew := fun yg => fun i =>
  match i with
  | ⟨0, _⟩ => yg.1
  | ⟨1, _⟩ => yg.2

/-- Map new `R 2` shape back to legacy pair `(s 0, s 1)`. -/
def fromNew : ShiNew → ShiLegacy := fun s =>
  (s ⟨0, by decide⟩, s ⟨1, by decide⟩)

/-- `toNew ∘ fromNew = id` (new round-trip). -/
@[simp] theorem toNew_fromNew (s : ShiNew) : toNew (fromNew s) = s := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- `fromNew ∘ toNew = id` (legacy round-trip). -/
@[simp] theorem fromNew_toNew (yg : ShiLegacy) : fromNew (toNew yg) = yg := by
  rcases yg with ⟨y, g⟩
  rfl

/-! ## § 3 Named V₄ values — legacy ↔ new

The four named values match on both sides per the table in the file
header.  We expose the legacy 4-tag constructors here so consumer files
that still pattern-match on `(true, false)` etc. have explicit names. -/

namespace Legacy

/-- Legacy 道 (V₄ identity). -/
@[match_pattern] def dao : ShiLegacy := (false, false)
/-- Legacy 已 (P-like). -/
@[match_pattern] def ji  : ShiLegacy := (true,  false)
/-- Legacy 今 (PT). -/
@[match_pattern] def jin : ShiLegacy := (true,  true)
/-- Legacy 未 (T-like). -/
@[match_pattern] def wei : ShiLegacy := (false, true)

end Legacy

/-! ### § 3.1 `toNew` on legacy named values = new named values -/

@[simp] theorem toNew_dao : toNew Legacy.dao = Shi.dao := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem toNew_ji : toNew Legacy.ji = Shi.ji := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem toNew_jin : toNew Legacy.jin = Shi.jin := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

@[simp] theorem toNew_wei : toNew Legacy.wei = Shi.wei := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-! ### § 3.2 `fromNew` on new named values = legacy named values -/

@[simp] theorem fromNew_dao : fromNew Shi.dao = Legacy.dao := rfl
@[simp] theorem fromNew_ji  : fromNew Shi.ji  = Legacy.ji  := rfl
@[simp] theorem fromNew_jin : fromNew Shi.jin = Legacy.jin := rfl
@[simp] theorem fromNew_wei : fromNew Shi.wei = Legacy.wei := rfl

/-! ## § 4 Atlas-naming operators on the legacy side, mirroring `Shi.lean`

These are the legacy 4-case definitions, so we can prove they commute
with the bridge.  All three are involutions; together with the identity
they form the Klein four-group on `Shi`. -/

namespace Legacy

/-- Legacy 印 (P-like, toggles YinBit): `dao ↔ ji, jin ↔ wei`. -/
def complement : ShiLegacy → ShiLegacy
  | (y, g) => (!y, g)

/-- Legacy 投 (T-like, toggles GuoBit): `dao ↔ wei, ji ↔ jin`. -/
def reverse : ShiLegacy → ShiLegacy
  | (y, g) => (y, !g)

/-- Legacy 错综 = complement ∘ reverse (PT). -/
def cuoZong (s : ShiLegacy) : ShiLegacy := complement (reverse s)

@[simp] theorem complement_dao : complement dao = ji := rfl
@[simp] theorem complement_ji  : complement ji  = dao := rfl
@[simp] theorem complement_jin : complement jin = wei := rfl
@[simp] theorem complement_wei : complement wei = jin := rfl

@[simp] theorem reverse_dao : reverse dao = wei := rfl
@[simp] theorem reverse_ji  : reverse ji  = jin := rfl
@[simp] theorem reverse_jin : reverse jin = ji  := rfl
@[simp] theorem reverse_wei : reverse wei = dao := rfl

theorem complement_involutive (s : ShiLegacy) : complement (complement s) = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

theorem reverse_involutive (s : ShiLegacy) : reverse (reverse s) = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

theorem complement_reverse_comm (s : ShiLegacy) :
    complement (reverse s) = reverse (complement s) := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

end Legacy

/-! ## § 5 V₄ ops commute with the bridge

The legacy and new V₄ ops are naturally isomorphic via `toNew / fromNew`.
This is the central justification for using either encoding
interchangeably in consumer code. -/

/-- 印 commutes with `toNew`: legacy `complement` then `toNew` =
    `toNew` then new `Shi.complement`. -/
theorem toNew_complement (s : ShiLegacy) :
    toNew (Legacy.complement s) = Shi.complement (toNew s) := by
  rcases s with ⟨y, g⟩
  funext i
  match i with
  | ⟨0, _⟩ => cases y <;> rfl
  | ⟨1, _⟩ => cases g <;> rfl

/-- 投 commutes with `toNew`. -/
theorem toNew_reverse (s : ShiLegacy) :
    toNew (Legacy.reverse s) = Shi.reverse (toNew s) := by
  rcases s with ⟨y, g⟩
  funext i
  match i with
  | ⟨0, _⟩ => cases y <;> rfl
  | ⟨1, _⟩ => cases g <;> rfl

/-- 错综 commutes with `toNew`. -/
theorem toNew_cuoZong (s : ShiLegacy) :
    toNew (Legacy.cuoZong s) = Shi.cuoZong (toNew s) := by
  unfold Legacy.cuoZong Shi.cuoZong
  rw [toNew_complement, toNew_reverse]

/-- 印 commutes with `fromNew` (the reverse direction). -/
theorem fromNew_complement (s : ShiNew) :
    fromNew (Shi.complement s) = Legacy.complement (fromNew s) := by
  rcases s ⟨0, by decide⟩ <;> rcases s ⟨1, by decide⟩ <;>
    simp [fromNew, Legacy.complement, Shi.complement]

/-- 投 commutes with `fromNew`. -/
theorem fromNew_reverse (s : ShiNew) :
    fromNew (Shi.reverse s) = Legacy.reverse (fromNew s) := by
  rcases s ⟨0, by decide⟩ <;> rcases s ⟨1, by decide⟩ <;>
    simp [fromNew, Legacy.reverse, Shi.reverse]

/-- 错综 commutes with `fromNew`. -/
theorem fromNew_cuoZong (s : ShiNew) :
    fromNew (Shi.cuoZong s) = Legacy.cuoZong (fromNew s) := by
  unfold Shi.cuoZong Legacy.cuoZong
  rw [fromNew_complement, fromNew_reverse]

/-! ## § 6 Public summary -/

/-- Bridge correctness: bijection + 4 named values + 3 V₄ ops commute. -/
theorem shiBridge_summary :
    -- bijection laws
    (∀ s : ShiNew, toNew (fromNew s) = s)
    ∧ (∀ yg : ShiLegacy, fromNew (toNew yg) = yg)
    -- 4 named values match under `toNew`
    ∧ toNew Legacy.dao = Shi.dao
    ∧ toNew Legacy.ji  = Shi.ji
    ∧ toNew Legacy.jin = Shi.jin
    ∧ toNew Legacy.wei = Shi.wei
    -- 3 V₄ ops commute with `toNew`
    ∧ (∀ s : ShiLegacy, toNew (Legacy.complement s) = Shi.complement (toNew s))
    ∧ (∀ s : ShiLegacy, toNew (Legacy.reverse s)    = Shi.reverse    (toNew s))
    ∧ (∀ s : ShiLegacy, toNew (Legacy.cuoZong s)    = Shi.cuoZong    (toNew s)) :=
  ⟨toNew_fromNew, fromNew_toNew,
   toNew_dao, toNew_ji, toNew_jin, toNew_wei,
   toNew_complement, toNew_reverse, toNew_cuoZong⟩

end SSBX.Foundation.Atlas.Yi.ShiBridge
