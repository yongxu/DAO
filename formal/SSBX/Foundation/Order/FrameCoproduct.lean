/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Path C γ.4 — Phase A frame-coproduct skeleton

# Foundation.Order.FrameCoproduct — the Joyal-Tierney frame coproduct

**Phase A deliverable** (per `Foundation/Order/FrameBimorphism.lean` §6
Mathlib upstream PR roadmap): the **general** Joyal-Tierney frame
coproduct `frameCoprod F₁ F₂` for arbitrary frames `F₁`, `F₂`, with
its `Order.Frame` instance, canonical bilinear pairing
`frameCoprodPairing`, and universal property.

This is the **foundational** file — it imports only Mathlib
infrastructure (no SSBX doctrine), so that sibling files
(`FrameBimorphism.lean`, `Doctrine/Instance/Topological.lean`) can later
specialise it without circularity.

## Construction — saturated downsets (Picado–Pultr Ch IV §3 /
   Joyal–Tierney 1984 §VI)

`Saturated F₁ F₂` is the type of **saturated downsets** of `F₁ × F₂`:
subsets closed under componentwise descent and under joins separately
in each component.  Order by ⊆.  Then:

* `inf` (`⊓`) = set intersection (proven saturated);
* `sInf` = arbitrary intersection (proven saturated);
* `sSup S` = intersection of all saturated sets containing ⋃ S
  (saturation closure of the union);
* `⊤` = the full set `Set.univ`;
* `⊥` = the saturation of `∅`;
* `frameCoprodPairing a b` = `sat {(a, b)}` (the *principal*
  saturated downset cut by `(a, b)`).

The `Order.Frame` instance is built via `Order.Frame.ofMinimalAxioms`,
which reduces the obligation to a single distributivity lemma
`inf_sSup_le_iSup_inf` on saturated downsets.

## Universal property (§9)

For any frame `F₃` and any `IsJTFrameBilinear φ : F₁ → F₂ → F₃`, there
is a **unique** frame morphism `u : frameCoprod F₁ F₂ → F₃` with
`u ∘ frameCoprodPairing = φ`.  Explicitly,
`u S = sSup { φ a b | (a, b) ∈ S.carrier }`.

## Scope (Phase A vs Phase B)

* **Phase A (this file)**: the construction is **fully defined** with
  no axioms.  The `CompleteLattice` instance is **fully proved**.
  The `Order.Frame` instance reduces to a single distributivity
  lemma recorded as a documented `sorry` (the JT 1984 §VI core).
  The universal-property *statement* is fully recorded; the
  *factorisation* + *uniqueness* halves carry documented `sorry`s.

* **Phase B (future)**: integrate with the existing
  `FrameBimorphism.lean` (replacing its `cubePairing` ad-hoc
  construction with a specialisation of this general one) and with
  `Doctrine/Instance/Topological.lean`.  This file deliberately
  introduces **no modification** to any sibling.

## Notes on `IsJTFrameBilinear`

The predicate `IsJTFrameBilinear` is also defined (with the same
fields) in `Foundation/Order/FrameBimorphism.lean`.  To keep this file
foundational (no GUT-doctrine dependency), the predicate is
**re-declared here** under the same namespace `SSBX.Foundation.Order`
but as `IsJTFrameBilinear'` to avoid collisions.  Phase B will
unify these two predicates and refactor `FrameBimorphism.lean` to
re-export from here.

## References

* Joyal–Tierney 1984, *An extension of the Galois theory of
  Grothendieck*, Memoirs AMS 309, §VI.
* Picado–Pultr 2012, *Frames and Locales* (Birkhäuser), Ch IV §3.
* Vickers 1989, *Topology via Logic*, Cambridge.
-/

import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Hom.CompleteLattice

namespace SSBX.Foundation.Order

universe u₁ u₂ u₃

/-! ## §1 The Joyal-Tierney bilinearity predicate (local copy) -/

section Bilinear

variable {F₁ : Type u₁} {F₂ : Type u₂} {F₃ : Type u₃}
  [Order.Frame F₁] [Order.Frame F₂] [Order.Frame F₃]

/-- `IsJTFrameBilinear' φ`: the Joyal-Tierney bimorphism property —
`φ : F₁ → F₂ → F₃` preserves arbitrary joins and finite meets in each
argument separately, the bi-unit `(⊤,⊤)`, and the **mixed-meet
identity** (Phase B 2026-05-18 refinement, see B-1/B-2 notes below).

**B-1 note** — top axiom: in the canonical JT saturated-downsets
construction `pairing ⊤ ⊤ = ⊤_{Sat}` (the full universe), so any
`FrameHom` factorisation `u` would force
`φ ⊤ ⊤ = u(pairing ⊤ ⊤) = u(⊤_{Sat}) = ⊤_{F₃}`.  The constant `φ ≡ ⊥`
map satisfies the original four join/meet axioms but violates this top-
preservation, so the original `frameCoprod_universal` was **provably
false** without `map_top_top`.  Adding it makes the universal property
non-vacuously sensible.

**B-2 note** — mixed-meet axiom: even with `map_top_top`, the four
"separable" axioms (sSup-left/right + inf-left/right) are insufficient
to force `u(S ⊓ T) = u(S) ⊓ u(T)`.  Explicit counter-example
(Phase B 2026-05-18 audit, F₁ = F₂ = F₃ = 3-chain {⊥, m, ⊤}):
take `φ(m, m) = ⊥, φ(m, ⊤) = m, φ(⊤, m) = ⊤, φ(⊤, ⊤) = ⊤` (and
`φ ⊥ _ = φ _ ⊥ = ⊥`); the four separable axioms + `map_top_top` all
hold, but `φ(m, ⊤) ⊓ φ(⊤, m) = m ⊓ ⊤ = m` while
`φ(m ⊓ ⊤, ⊤ ⊓ m) = φ(m, m) = ⊥`, giving
`u(pairing m ⊤) ⊓ u(pairing ⊤ m) = m > ⊥ = u(pairing m ⊤ ⊓ pairing ⊤ m)`.
The missing constraint is the **mixed-meet identity**
`φ x y ⊓ φ x' y' = φ(x ⊓ x')(y ⊓ y')` — equivalently, that φ factors
as `φ(x, y) = f(x) ⊓ g(y)` for frame morphisms `f`, `g` (the standard
locale-theoretic "bilinear-of-frame-morphisms" form, which corresponds
to a morphism of locales out of a locale product).  The canonical
pairing on `Saturated` satisfies this (proven in §9 via the explicit
characterization `mem_frameCoprodPairing'`).

(Primed name to avoid collision with the version in `FrameBimorphism.lean`;
Phase B will unify them.) -/
structure IsJTFrameBilinear' (φ : F₁ → F₂ → F₃) : Prop where
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
  /-- Preserves the unit `(⊤, ⊤)` (JT 1984 §VI unit axiom — added 2026-05-18). -/
  map_top_top : φ ⊤ ⊤ = ⊤
  /-- **Mixed-meet identity** (Phase B 2026-05-18) — the "fully
  bilinear" condition that pins down `φ` as a frame-bimorphism in the
  locale-product sense.  Without this, `u(S ⊓ T) ≠ u(S) ⊓ u(T)` in
  general (see B-2 note above for the explicit counter-example). -/
  map_inf_mixed : ∀ (x x' : F₁) (y y' : F₂),
    φ x y ⊓ φ x' y' = φ (x ⊓ x') (y ⊓ y')

end Bilinear

/-! ## §2 Saturated downsets — the carrier of the frame coproduct -/

variable (F₁ : Type u₁) (F₂ : Type u₂) [Order.Frame F₁] [Order.Frame F₂]

/-- `Saturated F₁ F₂` — a **saturated downset** of `F₁ × F₂`:

* downward-closed componentwise (`a' ≤ a`, `b' ≤ b`);
* closed under arbitrary joins on the left at any fixed right point;
* closed under arbitrary joins on the right at any fixed left point.

These are precisely the elements of the Joyal-Tierney frame coproduct
`frameCoprod F₁ F₂`. -/
structure Saturated where
  /-- The underlying subset of `F₁ × F₂`. -/
  carrier : Set (F₁ × F₂)
  /-- Closed under componentwise descent. -/
  downward_closed : ∀ {a a' : F₁} {b b' : F₂}, a' ≤ a → b' ≤ b →
                    (a, b) ∈ carrier → (a', b') ∈ carrier
  /-- For each fixed `b : F₂`, the left-slice is closed under arbitrary joins. -/
  sup_stable_left : ∀ (s : Set F₁) (b : F₂),
                    (∀ a ∈ s, (a, b) ∈ carrier) → (sSup s, b) ∈ carrier
  /-- For each fixed `a : F₁`, the right-slice is closed under arbitrary joins. -/
  sup_stable_right : ∀ (a : F₁) (s : Set F₂),
                     (∀ b ∈ s, (a, b) ∈ carrier) → (a, sSup s) ∈ carrier

namespace Saturated

variable {F₁ F₂}

/-- Membership via the underlying carrier. -/
instance : Membership (F₁ × F₂) (Saturated F₁ F₂) where
  mem S p := p ∈ S.carrier

@[simp] lemma mem_mk (carrier : Set (F₁ × F₂)) (h₁ h₂ h₃) (p : F₁ × F₂) :
    p ∈ (⟨carrier, h₁, h₂, h₃⟩ : Saturated F₁ F₂) ↔ p ∈ carrier := Iff.rfl

@[simp] lemma mem_carrier {S : Saturated F₁ F₂} {p : F₁ × F₂} :
    p ∈ S.carrier ↔ p ∈ S := Iff.rfl

@[ext] lemma ext_carrier {S T : Saturated F₁ F₂} (h : S.carrier = T.carrier) : S = T := by
  cases S; cases T; congr

/-! ## §3 The order on saturated downsets -/

instance : LE (Saturated F₁ F₂) where
  le S T := S.carrier ⊆ T.carrier

instance : LT (Saturated F₁ F₂) where
  lt S T := S ≤ T ∧ ¬ T ≤ S

lemma le_def {S T : Saturated F₁ F₂} : S ≤ T ↔ S.carrier ⊆ T.carrier := Iff.rfl

instance : Preorder (Saturated F₁ F₂) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl S := by intro _ hp; exact hp
  le_trans S T U hST hTU := fun _ hp => hTU (hST hp)
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

instance : PartialOrder (Saturated F₁ F₂) where
  le_antisymm S T hST hTS := by
    apply ext_carrier
    exact Set.Subset.antisymm hST hTS

/-! ## §4 Saturation closure (the key construction) -/

/-- An *intersection* of saturated downsets is saturated.  This is
the workhorse closure property; it gives us both `sInf` and (via
intersection-of-supersets) `sSup`. -/
def sInfFun (𝒮 : Set (Saturated F₁ F₂)) : Saturated F₁ F₂ where
  carrier := { p | ∀ S ∈ 𝒮, p ∈ S }
  downward_closed := by
    intro a a' b b' ha hb hp S hS
    exact S.downward_closed ha hb (hp S hS)
  sup_stable_left := by
    intro s b hs S hS
    exact S.sup_stable_left s b (fun a ha => hs a ha S hS)
  sup_stable_right := by
    intro a s hs S hS
    exact S.sup_stable_right a s (fun b hb => hs b hb S hS)

@[simp] lemma mem_sInfFun {𝒮 : Set (Saturated F₁ F₂)} {p : F₁ × F₂} :
    p ∈ sInfFun 𝒮 ↔ ∀ S ∈ 𝒮, p ∈ S := Iff.rfl

lemma sInfFun_le {𝒮 : Set (Saturated F₁ F₂)} {S : Saturated F₁ F₂}
    (hS : S ∈ 𝒮) : sInfFun 𝒮 ≤ S := by
  intro p hp
  exact hp S hS

lemma le_sInfFun {𝒮 : Set (Saturated F₁ F₂)} {T : Saturated F₁ F₂}
    (h : ∀ S ∈ 𝒮, T ≤ S) : T ≤ sInfFun 𝒮 := by
  intro p hp S hS
  exact h S hS hp

/-- The **saturation closure** of an arbitrary subset `X ⊆ F₁ × F₂`:
the smallest saturated downset containing `X`.  Constructed as the
intersection of all saturated downsets containing `X`. -/
def sat (X : Set (F₁ × F₂)) : Saturated F₁ F₂ :=
  sInfFun { S | X ⊆ S.carrier }

lemma subset_sat (X : Set (F₁ × F₂)) : X ⊆ (sat X).carrier := by
  intro p hp S hS
  exact hS hp

lemma sat_le {X : Set (F₁ × F₂)} {S : Saturated F₁ F₂}
    (h : X ⊆ S.carrier) : sat X ≤ S :=
  sInfFun_le (𝒮 := { T | X ⊆ T.carrier }) h

lemma sat_mono {X Y : Set (F₁ × F₂)} (h : X ⊆ Y) : sat X ≤ sat Y :=
  sat_le (fun _ hp => subset_sat Y (h hp))

lemma sat_eq_self {S : Saturated F₁ F₂} : sat S.carrier = S := by
  apply le_antisymm
  · exact sat_le (le_refl _)
  · intro p hp
    -- hp : p ∈ S.carrier; want: p ∈ sat S.carrier
    exact subset_sat S.carrier hp

lemma le_sat_iff {X : Set (F₁ × F₂)} {S : Saturated F₁ F₂} :
    sat X ≤ S ↔ X ⊆ S.carrier :=
  ⟨fun h _ hp => h (subset_sat X hp), sat_le⟩

/-! ## §5 The complete-lattice structure (all sorry-free) -/

/-- Set-theoretic intersection of two saturated downsets. -/
def interSat (S T : Saturated F₁ F₂) : Saturated F₁ F₂ where
  carrier := S.carrier ∩ T.carrier
  downward_closed := fun ha hb hp =>
    ⟨S.downward_closed ha hb hp.1, T.downward_closed ha hb hp.2⟩
  sup_stable_left := fun s b hs =>
    ⟨S.sup_stable_left s b (fun a ha => (hs a ha).1),
     T.sup_stable_left s b (fun a ha => (hs a ha).2)⟩
  sup_stable_right := fun a s hs =>
    ⟨S.sup_stable_right a s (fun b hb => (hs b hb).1),
     T.sup_stable_right a s (fun b hb => (hs b hb).2)⟩

@[simp] lemma carrier_interSat (S T : Saturated F₁ F₂) :
    (interSat S T).carrier = S.carrier ∩ T.carrier := rfl

/-- Saturation of the union: the join in the saturated-downset lattice. -/
def supSat (S T : Saturated F₁ F₂) : Saturated F₁ F₂ :=
  sat (S.carrier ∪ T.carrier)

/-- Arbitrary join via saturation of the union of carriers. -/
def sSupFun (𝒮 : Set (Saturated F₁ F₂)) : Saturated F₁ F₂ :=
  sat (⋃ S ∈ 𝒮, S.carrier)

lemma le_sSupFun {𝒮 : Set (Saturated F₁ F₂)} {S : Saturated F₁ F₂}
    (hS : S ∈ 𝒮) : S ≤ sSupFun 𝒮 := by
  intro p hp
  apply subset_sat
  exact Set.mem_iUnion₂.mpr ⟨S, hS, hp⟩

lemma sSupFun_le {𝒮 : Set (Saturated F₁ F₂)} {T : Saturated F₁ F₂}
    (h : ∀ S ∈ 𝒮, S ≤ T) : sSupFun 𝒮 ≤ T := by
  apply sat_le
  intro p hp
  rcases Set.mem_iUnion₂.mp hp with ⟨S, hS, hpS⟩
  exact h S hS hpS

/-- The full set, trivially saturated — the top element. -/
def topSat : Saturated F₁ F₂ where
  carrier := Set.univ
  downward_closed := fun _ _ _ => trivial
  sup_stable_left := fun _ _ _ => trivial
  sup_stable_right := fun _ _ _ => trivial

/-- Saturation closure of `∅` — the bottom element. -/
def botSat : Saturated F₁ F₂ := sat ∅

lemma le_topSat (S : Saturated F₁ F₂) : S ≤ topSat := fun _ _ => trivial

lemma botSat_le (S : Saturated F₁ F₂) : botSat ≤ S := by
  intro p hp
  exact hp S (by intro _ h; exact h.elim)

/-! ### §5.1 Bundled SupSet / InfSet instances -/

instance : SupSet (Saturated F₁ F₂) where
  sSup := sSupFun

instance : InfSet (Saturated F₁ F₂) where
  sInf := sInfFun

instance : Top (Saturated F₁ F₂) where
  top := topSat

instance : Bot (Saturated F₁ F₂) where
  bot := botSat

instance : Min (Saturated F₁ F₂) where
  min := interSat

instance : Max (Saturated F₁ F₂) where
  max := supSat

@[simp] lemma carrier_top : (⊤ : Saturated F₁ F₂).carrier = Set.univ := rfl

@[simp] lemma mem_top (p : F₁ × F₂) : p ∈ (⊤ : Saturated F₁ F₂) := trivial

@[simp] lemma carrier_inf (S T : Saturated F₁ F₂) :
    (S ⊓ T).carrier = S.carrier ∩ T.carrier := rfl

@[simp] lemma mem_inf {S T : Saturated F₁ F₂} {p : F₁ × F₂} :
    p ∈ S ⊓ T ↔ p ∈ S ∧ p ∈ T := Iff.rfl

@[simp] lemma carrier_sInf (𝒮 : Set (Saturated F₁ F₂)) :
    (sInf 𝒮 : Saturated F₁ F₂).carrier = { p | ∀ S ∈ 𝒮, p ∈ S } := rfl

@[simp] lemma mem_sInf {𝒮 : Set (Saturated F₁ F₂)} {p : F₁ × F₂} :
    p ∈ (sInf 𝒮 : Saturated F₁ F₂) ↔ ∀ S ∈ 𝒮, p ∈ S := Iff.rfl

/-! ### §5.2 The CompleteLattice instance — fully proved -/

instance instCompleteLattice : CompleteLattice (Saturated F₁ F₂) where
  inf := (· ⊓ ·)
  inf_le_left S T := fun _ hp => hp.1
  inf_le_right S T := fun _ hp => hp.2
  le_inf S T U hST hSU := fun _ hp => ⟨hST hp, hSU hp⟩
  sup := (· ⊔ ·)
  le_sup_left S T := by
    -- S ≤ sat (S ∪ T)
    intro p hp
    exact subset_sat (S.carrier ∪ T.carrier) (Or.inl hp)
  le_sup_right S T := by
    intro p hp
    exact subset_sat (S.carrier ∪ T.carrier) (Or.inr hp)
  sup_le S T U hSU hTU := by
    -- sat (S ∪ T) ≤ U
    apply sat_le
    rintro p (hpS | hpT)
    · exact hSU hpS
    · exact hTU hpT
  top := ⊤
  bot := ⊥
  le_top S := le_topSat S
  bot_le S := botSat_le S
  sSup := sSup
  sInf := sInf
  isLUB_sSup 𝒮 := by
    refine ⟨?_, ?_⟩
    · intro S hS
      exact le_sSupFun hS
    · intro T hT
      exact sSupFun_le hT
  isGLB_sInf 𝒮 := by
    refine ⟨?_, ?_⟩
    · intro S hS
      exact sInfFun_le hS
    · intro T hT
      exact le_sInfFun hT

/-! ## §6 The `Order.Frame` instance via `ofMinimalAxioms`

For a frame coproduct built from saturated downsets, the
distributivity law `a ⊓ sSup S ≤ ⨆ b ∈ S, a ⊓ b` is the *defining*
content of the construction.  It reduces to: the set

  { U : Saturated | S ⊓ U ≤ ⨆ T ∈ 𝒮, S ⊓ T }

is closed under the saturation closure — every saturated downset
generated from `𝒮` satisfies it.  This is the heart of
Picado–Pultr Ch IV §3 / Joyal–Tierney 1984 §VI.

For Phase A we record the statement; the full proof is recorded as a
documented `sorry`.  Phase B will discharge it (~50-150 LOC of
saturation-closure manipulation). -/

/-- **Distributivity** of `⊓` over `sSup` on saturated downsets — the
JT 1984 §VI core lemma.

**Phase B proof (2026-05-18)**: by the "downward-stable indicator
saturated set" trick.  Let `Q := sat(⋃ T∈𝒮, (S ⊓ T).carrier)` (which
equals `(⨆ T ∈ 𝒮, S ⊓ T)` as a saturated set).  Define
  `V.carrier := { p | ∀ p' ≤ p, p' ∈ S.carrier → p' ∈ Q.carrier }`.
*V is saturated*: downward closure is immediate (transitivity of `≤`);
sup-stability uses **frame distributivity in F₁ / F₂** —
`x ⊓ sSup s = sSup (x ⊓ ·) '' s` — to reduce a sup-stable-left
membership-test for `(sSup s, b)` to per-α tests at `(x ⊓ α, y)`, each
of which lies in `Q` by induction (each `(α, b) ∈ V`) and downward
closure of S.  Then `Q`'s own `sup_stable_left` recombines.  *V contains
⋃ T∈𝒮 T.carrier*: by `T`-downward-closure and `(S ∩ T) ⊆ Q`.  Hence
`sat(⋃ T) ≤ V`, and applying V's defining condition at `p ≤ p` to
`p ∈ S ⊓ sSup 𝒮` yields `p ∈ Q`. -/
lemma inf_sSup_le_iSup_inf_aux (S : Saturated F₁ F₂) (𝒮 : Set (Saturated F₁ F₂)) :
    S ⊓ sSup 𝒮 ≤ ⨆ T ∈ 𝒮, S ⊓ T := by
  -- Q is the RHS as a `Saturated F₁ F₂`, built directly via `sSupFun`.
  let Q : Saturated F₁ F₂ := sSupFun ((fun T => S ⊓ T) '' 𝒮)
  -- Step 0: `Q ≤ ⨆ T ∈ 𝒮, S ⊓ T` (the goal RHS) — this follows from
  -- `Q`'s definition as the sSup of the image family.
  have Q_le_RHS : Q ≤ (⨆ T ∈ 𝒮, S ⊓ T) := by
    apply sSupFun_le
    rintro U ⟨T, hT, rfl⟩
    -- Goal: S ⊓ T ≤ ⨆ T ∈ 𝒮, S ⊓ T
    exact le_iSup₂ (f := fun T (_ : T ∈ 𝒮) => S ⊓ T) T hT
  -- Step 1: build the "downward-stable indicator" set V.
  let Vcarr : Set (F₁ × F₂) :=
    { p | ∀ p' : F₁ × F₂, p' ≤ p → p' ∈ S.carrier → p' ∈ Q.carrier }
  -- Step 2: show V is saturated.
  let V : Saturated F₁ F₂ :=
    { carrier := Vcarr
      downward_closed := by
        intro a a' b b' ha hb hp p' hp'le hp'S
        -- p' ≤ (a', b') ≤ (a, b), so p' ≤ (a, b); apply hp.
        have hle : p' ≤ (a, b) := le_trans hp'le (Prod.mk_le_mk.mpr ⟨ha, hb⟩)
        exact hp p' hle hp'S
      sup_stable_left := by
        intro s b hs p' hp'le hp'S
        -- p' = (x', y') ≤ (sSup s, b).
        obtain ⟨x', y'⟩ := p'
        have hx'le : x' ≤ sSup s := hp'le.1
        have hy'le : y' ≤ b := hp'le.2
        -- Key: x' = sSup {x' ⊓ α | α ∈ s} by frame distributivity in F₁.
        -- For each α ∈ s, (x' ⊓ α, y') ≤ (α, b), and ∈ S (since (x',y') ∈ S
        -- and we descend), so by hs α, (x' ⊓ α, y') ∈ Q.
        -- Then Q.sup_stable_left {x' ⊓ α | α ∈ s} y' gives
        --   (sSup {x' ⊓ α | α ∈ s}, y') ∈ Q,
        -- which equals (x' ⊓ sSup s, y') = (x', y') by x' ≤ sSup s.
        have hpoint : ∀ α ∈ s, (x' ⊓ α, y') ∈ Q.carrier := by
          intro α hα
          have hα_in_V : (α, b) ∈ Vcarr := hs α hα
          -- (x' ⊓ α, y') ≤ (α, b)
          have hle₁ : (x' ⊓ α, y') ≤ (α, b) :=
            Prod.mk_le_mk.mpr ⟨inf_le_right, hy'le⟩
          -- (x' ⊓ α, y') ∈ S by downward closure from (x', y') ∈ S
          have hS₁ : (x' ⊓ α, y') ∈ S.carrier :=
            S.downward_closed (inf_le_left : x' ⊓ α ≤ x') (le_refl y') hp'S
          exact hα_in_V (x' ⊓ α, y') hle₁ hS₁
        -- Now apply Q.sup_stable_left.
        have hQsup : (sSup ((fun α => x' ⊓ α) '' s), y') ∈ Q.carrier := by
          apply Q.sup_stable_left ((fun α => x' ⊓ α) '' s) y'
          rintro a ⟨α, hα, rfl⟩
          exact hpoint α hα
        -- sSup {x' ⊓ α | α ∈ s} = x' ⊓ sSup s by frame distributivity in F₁.
        have hdist : sSup ((fun α => x' ⊓ α) '' s) = x' ⊓ sSup s := by
          rw [inf_sSup_eq, sSup_image]
        -- x' ⊓ sSup s = x' since x' ≤ sSup s.
        have hxeq : x' ⊓ sSup s = x' := inf_eq_left.mpr hx'le
        rw [hdist, hxeq] at hQsup
        exact hQsup
      sup_stable_right := by
        intro a s hs p' hp'le hp'S
        obtain ⟨x', y'⟩ := p'
        have hx'le : x' ≤ a := hp'le.1
        have hy'le : y' ≤ sSup s := hp'le.2
        have hpoint : ∀ β ∈ s, (x', y' ⊓ β) ∈ Q.carrier := by
          intro β hβ
          have hβ_in_V : (a, β) ∈ Vcarr := hs β hβ
          have hle₁ : (x', y' ⊓ β) ≤ (a, β) :=
            Prod.mk_le_mk.mpr ⟨hx'le, inf_le_right⟩
          have hS₁ : (x', y' ⊓ β) ∈ S.carrier :=
            S.downward_closed (le_refl x') (inf_le_left : y' ⊓ β ≤ y') hp'S
          exact hβ_in_V (x', y' ⊓ β) hle₁ hS₁
        have hQsup : (x', sSup ((fun β => y' ⊓ β) '' s)) ∈ Q.carrier := by
          apply Q.sup_stable_right x' ((fun β => y' ⊓ β) '' s)
          rintro b ⟨β, hβ, rfl⟩
          exact hpoint β hβ
        have hdist : sSup ((fun β => y' ⊓ β) '' s) = y' ⊓ sSup s := by
          rw [inf_sSup_eq, sSup_image]
        have hyeq : y' ⊓ sSup s = y' := inf_eq_left.mpr hy'le
        rw [hdist, hyeq] at hQsup
        exact hQsup }
  -- Step 3: V contains ⋃ T∈𝒮, T.carrier.
  have hV_contains : (⋃ T ∈ 𝒮, T.carrier) ⊆ V.carrier := by
    intro p hp
    rcases Set.mem_iUnion₂.mp hp with ⟨T, hT, hpT⟩
    intro p' hp'le hp'S
    -- p' ≤ p ∈ T, and T saturated/downward, so p' ∈ T.
    obtain ⟨a, b⟩ := p
    obtain ⟨x', y'⟩ := p'
    have hp'T : (x', y') ∈ T.carrier := T.downward_closed hp'le.1 hp'le.2 hpT
    -- p' ∈ S ∩ T ⊆ ⋃ T'∈𝒮, (S ⊓ T').carrier ⊆ sat(...) = Q.
    have hp'_inST : (x', y') ∈ (S ⊓ T).carrier := ⟨hp'S, hp'T⟩
    -- (S ⊓ T) ≤ Q (= sSupFun image): use le_sSupFun.
    have hST_in_Q : S ⊓ T ≤ Q := le_sSupFun ⟨T, hT, rfl⟩
    exact hST_in_Q hp'_inST
  -- Step 4: sat(⋃ T) ≤ V, hence sSup 𝒮 ≤ V (carrier-wise).
  have h_sSup_le_V : (sSup 𝒮 : Saturated F₁ F₂).carrier ⊆ V.carrier := by
    -- sSup 𝒮 = sSupFun 𝒮 = sat(⋃ T∈𝒮, T.carrier).
    -- We need sat(⋃ T) ≤ V, i.e., sat(⋃ T).carrier ⊆ V.carrier.
    -- This follows from `sat_le` applied to hV_contains.
    show (sSupFun 𝒮).carrier ⊆ V.carrier
    have : sSupFun 𝒮 ≤ V := sat_le hV_contains
    exact this
  -- Step 5: combine.
  intro p hp
  -- hp : p ∈ S ⊓ sSup 𝒮 = S.carrier ∩ (sSup 𝒮).carrier.
  have hpS : p ∈ S.carrier := hp.1
  have hpSup : p ∈ (sSup 𝒮 : Saturated F₁ F₂).carrier := hp.2
  have hpV : p ∈ V.carrier := h_sSup_le_V hpSup
  -- Apply V's condition at p' = p (using p ≤ p).
  have hpQ : p ∈ Q.carrier := hpV p (le_refl p) hpS
  -- Q ≤ RHS, so p ∈ RHS.carrier.
  exact Q_le_RHS hpQ

instance instFrame : Order.Frame (Saturated F₁ F₂) :=
  Order.Frame.ofMinimalAxioms
    { __ := instCompleteLattice
      inf_sSup_le_iSup_inf := fun S 𝒮 => inf_sSup_le_iSup_inf_aux S 𝒮 }

end Saturated

/-! ## §7 The frame coproduct type -/

/-- **The Joyal-Tierney frame coproduct** of two frames. -/
def frameCoprod : Type max u₁ u₂ := Saturated F₁ F₂

namespace frameCoprod

variable {F₁ F₂}

instance instFrame : Order.Frame (frameCoprod F₁ F₂) := Saturated.instFrame

end frameCoprod

/-! ## §8 The canonical bilinear pairing -/

namespace Saturated

variable {F₁ F₂}

/-- **The canonical pairing**: saturation closure of the singleton
`{(a, b)}`.  This is the unique JT-bilinear pairing
`F₁ → F₂ → frameCoprod F₁ F₂` characterised by the frame-coproduct
universal property.

The naive principal downset `{(x,y) | x ≤ a ∧ y ≤ b}` is NOT
saturated on the nose: the `sup_stable_left ∅` axiom forces
`(⊥, y') ∈ carrier` for every `y'`, but the naive principal downset
rejects `y' > b`.  Hence the saturation-closure formulation. -/
def frameCoprodPairing' (a : F₁) (b : F₂) : Saturated F₁ F₂ :=
  sat ({(a, b)} : Set (F₁ × F₂))

@[simp] lemma frameCoprodPairing'_le_iff {a : F₁} {b : F₂}
    {S : Saturated F₁ F₂} :
    frameCoprodPairing' a b ≤ S ↔ (a, b) ∈ S := by
  rw [frameCoprodPairing', le_sat_iff]
  constructor
  · intro h; exact h rfl
  · intro h p hp; rcases hp with rfl; exact h

lemma mem_frameCoprodPairing'_self (a : F₁) (b : F₂) :
    (a, b) ∈ frameCoprodPairing' a b :=
  subset_sat _ rfl

/-- **Explicit characterization** of the pairing carrier (Phase B,
2026-05-18).

The saturation closure `sat({(a, b)})` is *not* the naive principal
downset — it must also contain `(⊥, y')` and `(x', ⊥)` for arbitrary
`y'`, `x'` because of the `sup_stable_left ∅` and `sup_stable_right ∅`
axioms (sSup of empty = ⊥).  We prove that adding precisely these
"axis-strips" gives the saturation:

  `pairing a b = {(x, y) | (x ≤ a ∧ y ≤ b) ∨ x = ⊥ ∨ y = ⊥}`.

This characterization is the workhorse for §9 `inf_left/right` and
§10 `Lift_pairing` proofs. -/
lemma mem_frameCoprodPairing' (a : F₁) (b : F₂) (x : F₁) (y : F₂) :
    (x, y) ∈ frameCoprodPairing' a b ↔
      (x ≤ a ∧ y ≤ b) ∨ x = ⊥ ∨ y = ⊥ := by
  classical
  -- Define the explicit set as a Saturated structure.
  let P : Saturated F₁ F₂ :=
    { carrier := {p | (p.1 ≤ a ∧ p.2 ≤ b) ∨ p.1 = ⊥ ∨ p.2 = ⊥}
      downward_closed := by
        rintro a₀ a₀' b₀ b₀' ha hb hp
        rcases hp with ⟨ha₀, hb₀⟩ | hx | hy
        · exact Or.inl ⟨le_trans ha ha₀, le_trans hb hb₀⟩
        · -- a₀ = ⊥, so a₀' ≤ ⊥, so a₀' = ⊥.
          refine Or.inr (Or.inl ?_)
          exact le_antisymm (hx ▸ ha) bot_le
        · refine Or.inr (Or.inr ?_)
          exact le_antisymm (hy ▸ hb) bot_le
      sup_stable_left := by
        intro s b₀ hs
        -- Goal: (sSup s, b₀) ∈ P.carrier
        -- Case-split on whether b₀ ≤ b or b₀ = ⊥ or otherwise.
        by_cases hb_bot : b₀ = ⊥
        · exact Or.inr (Or.inr hb_bot)
        by_cases hb_le : b₀ ≤ b
        · -- All α ∈ s have α ≤ a (the only branch giving (α, b₀) ∈ P).
          have hall : ∀ α ∈ s, α ≤ a := by
            intro α hα
            rcases hs α hα with ⟨h₁, _⟩ | hbot | hb_b
            · exact h₁
            · -- (α, b₀).1 = ⊥ means α = ⊥, so α ≤ a.
              simp only at hbot
              exact hbot ▸ bot_le
            · -- (α, b₀).2 = ⊥ contradicts hb_bot.
              simp only at hb_b
              exact absurd hb_b hb_bot
          have hsSup : sSup s ≤ a := sSup_le hall
          exact Or.inl ⟨hsSup, hb_le⟩
        · -- b₀ is neither ⊥ nor ≤ b; each (α, b₀) ∈ P forces α = ⊥.
          have hall : ∀ α ∈ s, α = ⊥ := by
            intro α hα
            rcases hs α hα with ⟨_, hb_b⟩ | hbot | hb_b
            · exact absurd hb_b hb_le
            · simp only at hbot; exact hbot
            · simp only at hb_b; exact absurd hb_b hb_bot
          have hsSup_bot : sSup s = ⊥ := by
            apply le_antisymm _ bot_le
            apply sSup_le
            intro α hα
            rw [hall α hα]
          exact Or.inr (Or.inl hsSup_bot)
      sup_stable_right := by
        intro a₀ s hs
        by_cases ha_bot : a₀ = ⊥
        · exact Or.inr (Or.inl ha_bot)
        by_cases ha_le : a₀ ≤ a
        · have hall : ∀ β ∈ s, β ≤ b := by
            intro β hβ
            rcases hs β hβ with ⟨_, h₂⟩ | ha_a | hbot
            · exact h₂
            · simp only at ha_a; exact absurd ha_a ha_bot
            · simp only at hbot; exact hbot ▸ bot_le
          have hsSup : sSup s ≤ b := sSup_le hall
          exact Or.inl ⟨ha_le, hsSup⟩
        · have hall : ∀ β ∈ s, β = ⊥ := by
            intro β hβ
            rcases hs β hβ with ⟨ha_a, _⟩ | ha_a' | hbot
            · exact absurd ha_a ha_le
            · simp only at ha_a'; exact absurd ha_a' ha_bot
            · simp only at hbot; exact hbot
          have hsSup_bot : sSup s = ⊥ := by
            apply le_antisymm _ bot_le
            apply sSup_le
            intro β hβ
            rw [hall β hβ]
          exact Or.inr (Or.inr hsSup_bot) }
  -- pairing a b ≤ P (smallest saturated set containing (a, b)).
  have h_pair_le_P : frameCoprodPairing' a b ≤ P := by
    rw [frameCoprodPairing'_le_iff]
    -- (a, b) ∈ P: take the first branch.
    exact Or.inl ⟨le_refl a, le_refl b⟩
  -- P.carrier ⊆ pairing a b.carrier: case-split on which clause.
  have h_P_le_pair : P.carrier ⊆ (frameCoprodPairing' a b).carrier := by
    rintro ⟨x', y'⟩ hp
    rcases hp with ⟨hx, hy⟩ | hx_bot | hy_bot
    · -- (x', y') ≤ (a, b), descend from (a, b) ∈ pairing.
      exact (frameCoprodPairing' a b).downward_closed hx hy
        (mem_frameCoprodPairing'_self a b)
    · -- x' = ⊥: from sup_stable_left ∅ with b = y'.
      simp only at hx_bot
      have heq : (x', y') = ((⊥ : F₁), y') := by rw [hx_bot]
      rw [heq, show (⊥ : F₁) = sSup (∅ : Set F₁) from sSup_empty.symm]
      exact (frameCoprodPairing' a b).sup_stable_left ∅ y'
        (fun α hα => absurd hα (Set.notMem_empty α))
    · -- y' = ⊥: from sup_stable_right ∅ with a = x'.
      simp only at hy_bot
      have heq : (x', y') = (x', (⊥ : F₂)) := by rw [hy_bot]
      rw [heq, show (⊥ : F₂) = sSup (∅ : Set F₂) from sSup_empty.symm]
      exact (frameCoprodPairing' a b).sup_stable_right x' ∅
        (fun β hβ => absurd hβ (Set.notMem_empty β))
  constructor
  · intro hxy
    -- hxy : (x, y) ∈ pairing a b; want P-condition.
    -- pairing ≤ P, so pairing.carrier ⊆ P.carrier.
    exact h_pair_le_P hxy
  · intro hxy
    -- hxy : P-condition; want (x, y) ∈ pairing.
    exact h_P_le_pair hxy

end Saturated

/-- Public alias: the canonical bilinear pairing for the frame coproduct. -/
def frameCoprodPairing {F₁ : Type u₁} {F₂ : Type u₂}
    [Order.Frame F₁] [Order.Frame F₂]
    (a : F₁) (b : F₂) : frameCoprod F₁ F₂ :=
  Saturated.frameCoprodPairing' a b

/-! ## §9 `frameCoprodPairing` is JT-bilinear -/

namespace Saturated

variable {F₁ F₂}

/-- The pairing preserves arbitrary joins in the left argument.

Proof sketch: by antisymmetry.
* `≤`: `sat {(sSup s, b)} ≤ sSup {sat {(a, b)} | a ∈ s}` because the
  RHS, being a saturated downset, contains all `(a, b)` for `a ∈ s`,
  hence by `sup_stable_left` contains `(sSup s, b)`.
* `≥`: each `sat {(a, b)}` is `≤ sat {(sSup s, b)}` by
  `frameCoprodPairing'_le_iff` and downward-closure (`a ≤ sSup s`).

Both directions are mechanical given the saturation API. -/
lemma frameCoprodPairing'_sSup_left (s : Set F₁) (b : F₂) :
    frameCoprodPairing' (sSup s) b =
      sSup ((fun a => frameCoprodPairing' a b) '' s) := by
  apply le_antisymm
  · -- ≤: show LHS ≤ RHS, equivalently (sSup s, b) ∈ RHS.
    rw [frameCoprodPairing'_le_iff]
    -- Goal: (sSup s, b) ∈ (sSup ((fun a => frameCoprodPairing' a b) '' s) : Saturated _ _)
    apply (sSup ((fun a => frameCoprodPairing' a b) '' s) :
      Saturated F₁ F₂).sup_stable_left s b
    intro a ha
    have hpair_le : frameCoprodPairing' a b ≤
        (sSup ((fun a' => frameCoprodPairing' a' b) '' s) : Saturated F₁ F₂) :=
      le_sSup ⟨a, ha, rfl⟩
    exact hpair_le (mem_frameCoprodPairing'_self a b)
  · -- ≥
    apply sSup_le
    rintro T ⟨a, ha, rfl⟩
    rw [frameCoprodPairing'_le_iff]
    exact (frameCoprodPairing' (sSup s) b).downward_closed
      (le_sSup ha) (le_refl b)
      (mem_frameCoprodPairing'_self (sSup s) b)

/-- Symmetric: preserves joins in the right argument. -/
lemma frameCoprodPairing'_sSup_right (a : F₁) (s : Set F₂) :
    frameCoprodPairing' a (sSup s) =
      sSup ((fun b => frameCoprodPairing' a b) '' s) := by
  apply le_antisymm
  · rw [frameCoprodPairing'_le_iff]
    apply (sSup ((fun b => frameCoprodPairing' a b) '' s) :
      Saturated F₁ F₂).sup_stable_right a s
    intro b hb
    have hpair_le : frameCoprodPairing' a b ≤
        (sSup ((fun b' => frameCoprodPairing' a b') '' s) : Saturated F₁ F₂) :=
      le_sSup ⟨b, hb, rfl⟩
    exact hpair_le (mem_frameCoprodPairing'_self a b)
  · apply sSup_le
    rintro T ⟨b, hb, rfl⟩
    rw [frameCoprodPairing'_le_iff]
    exact (frameCoprodPairing' a (sSup s)).downward_closed
      (le_refl a) (le_sSup hb)
      (mem_frameCoprodPairing'_self a (sSup s))

/-- The pairing preserves finite meets in the left argument.

**Phase B proof (2026-05-18)**: by carrier extensionality, using the
explicit characterization `mem_frameCoprodPairing'`.  Both sides have
the same membership predicate after case analysis on which clause of
the disjunction `(p ≤ _ ∧ q ≤ y) ∨ p = ⊥ ∨ q = ⊥` is selected. -/
lemma frameCoprodPairing'_inf_left (y : F₂) (a b : F₁) :
    frameCoprodPairing' (a ⊓ b) y =
      frameCoprodPairing' a y ⊓ frameCoprodPairing' b y := by
  apply ext_carrier
  ext ⟨p, q⟩
  rw [carrier_inf, Set.mem_inter_iff, mem_carrier, mem_carrier, mem_carrier,
      mem_frameCoprodPairing', mem_frameCoprodPairing',
      mem_frameCoprodPairing']
  constructor
  · rintro (⟨hp, hq⟩ | hp_bot | hq_bot)
    · refine ⟨Or.inl ⟨?_, hq⟩, Or.inl ⟨?_, hq⟩⟩
      · exact le_trans hp inf_le_left
      · exact le_trans hp inf_le_right
    · exact ⟨Or.inr (Or.inl hp_bot), Or.inr (Or.inl hp_bot)⟩
    · exact ⟨Or.inr (Or.inr hq_bot), Or.inr (Or.inr hq_bot)⟩
  · rintro ⟨h₁, h₂⟩
    rcases h₁ with ⟨hp_a, hq⟩ | hp_bot | hq_bot
    · rcases h₂ with ⟨hp_b, _⟩ | hp_bot' | hq_bot'
      · exact Or.inl ⟨le_inf hp_a hp_b, hq⟩
      · exact Or.inr (Or.inl hp_bot')
      · exact Or.inr (Or.inr hq_bot')
    · exact Or.inr (Or.inl hp_bot)
    · exact Or.inr (Or.inr hq_bot)

/-- Symmetric: preserves finite meets in the right argument. -/
lemma frameCoprodPairing'_inf_right (x : F₁) (a b : F₂) :
    frameCoprodPairing' x (a ⊓ b) =
      frameCoprodPairing' x a ⊓ frameCoprodPairing' x b := by
  apply ext_carrier
  ext ⟨p, q⟩
  rw [carrier_inf, Set.mem_inter_iff, mem_carrier, mem_carrier, mem_carrier,
      mem_frameCoprodPairing', mem_frameCoprodPairing',
      mem_frameCoprodPairing']
  constructor
  · rintro (⟨hp, hq⟩ | hp_bot | hq_bot)
    · refine ⟨Or.inl ⟨hp, ?_⟩, Or.inl ⟨hp, ?_⟩⟩
      · exact le_trans hq inf_le_left
      · exact le_trans hq inf_le_right
    · exact ⟨Or.inr (Or.inl hp_bot), Or.inr (Or.inl hp_bot)⟩
    · exact ⟨Or.inr (Or.inr hq_bot), Or.inr (Or.inr hq_bot)⟩
  · rintro ⟨h₁, h₂⟩
    rcases h₁ with ⟨hp, hq_a⟩ | hp_bot | hq_bot
    · rcases h₂ with ⟨_, hq_b⟩ | hp_bot' | hq_bot'
      · exact Or.inl ⟨hp, le_inf hq_a hq_b⟩
      · exact Or.inr (Or.inl hp_bot')
      · exact Or.inr (Or.inr hq_bot')
    · exact Or.inr (Or.inl hp_bot)
    · exact Or.inr (Or.inr hq_bot)

/-- The pairing satisfies the unit axiom `pairing ⊤ ⊤ = ⊤_{Sat}`.
**Phase B (2026-05-18)**.  By characterization, the carrier of
`pairing ⊤ ⊤` is `{(x,y) | (x ≤ ⊤ ∧ y ≤ ⊤) ∨ ...} = Set.univ`. -/
lemma frameCoprodPairing'_top_top :
    frameCoprodPairing' (⊤ : F₁) (⊤ : F₂) = ⊤ := by
  apply ext_carrier
  ext ⟨p, q⟩
  simp only [carrier_top, Set.mem_univ, iff_true]
  rw [mem_carrier, mem_frameCoprodPairing']
  exact Or.inl ⟨le_top, le_top⟩

/-- The pairing satisfies the **mixed-meet identity** (Phase B 2026-05-18).
`pairing x y ⊓ pairing x' y' = pairing(x ⊓ x')(y ⊓ y')` — this is the
specialised "fully bilinear" axiom needed for the universal property
to deliver a `FrameHom` (not merely an `sSupHom`).  Proof via carrier
characterization: both sides have membership
`(p ≤ x ⊓ x' ∧ q ≤ y ⊓ y') ∨ p = ⊥ ∨ q = ⊥`. -/
lemma frameCoprodPairing'_inf_mixed (x x' : F₁) (y y' : F₂) :
    frameCoprodPairing' x y ⊓ frameCoprodPairing' x' y' =
      frameCoprodPairing' (x ⊓ x') (y ⊓ y') := by
  apply ext_carrier
  ext ⟨p, q⟩
  rw [carrier_inf, Set.mem_inter_iff, mem_carrier, mem_carrier, mem_carrier,
      mem_frameCoprodPairing', mem_frameCoprodPairing',
      mem_frameCoprodPairing']
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases h₁ with ⟨hpx, hqy⟩ | hp_bot | hq_bot
    · rcases h₂ with ⟨hpx', hqy'⟩ | hp_bot | hq_bot
      · exact Or.inl ⟨le_inf hpx hpx', le_inf hqy hqy'⟩
      · exact Or.inr (Or.inl hp_bot)
      · exact Or.inr (Or.inr hq_bot)
    · exact Or.inr (Or.inl hp_bot)
    · exact Or.inr (Or.inr hq_bot)
  · rintro (⟨hpxx, hqyy⟩ | hp_bot | hq_bot)
    · refine ⟨Or.inl ⟨?_, ?_⟩, Or.inl ⟨?_, ?_⟩⟩
      · exact le_trans hpxx inf_le_left
      · exact le_trans hqyy inf_le_left
      · exact le_trans hpxx inf_le_right
      · exact le_trans hqyy inf_le_right
    · exact ⟨Or.inr (Or.inl hp_bot), Or.inr (Or.inl hp_bot)⟩
    · exact ⟨Or.inr (Or.inr hq_bot), Or.inr (Or.inr hq_bot)⟩

/-- **`frameCoprodPairing` is JT-bilinear** — the six preservation
axioms packaged (including the JT 1984 §VI unit axiom `map_top_top`
and the mixed-meet identity `map_inf_mixed`, added Phase B 2026-05-18). -/
theorem frameCoprodPairing'_isJTBilinear :
    IsJTFrameBilinear' (frameCoprodPairing' (F₁ := F₁) (F₂ := F₂)) where
  map_sSup_left := fun y s => frameCoprodPairing'_sSup_left s y
  map_sSup_right := frameCoprodPairing'_sSup_right
  map_inf_left := frameCoprodPairing'_inf_left
  map_inf_right := frameCoprodPairing'_inf_right
  map_top_top := frameCoprodPairing'_top_top
  map_inf_mixed := frameCoprodPairing'_inf_mixed

end Saturated

/-- **`frameCoprodPairing` is JT-bilinear** (public alias). -/
theorem frameCoprodPairing_isJTBilinear
    {F₁ : Type u₁} {F₂ : Type u₂} [Order.Frame F₁] [Order.Frame F₂] :
    IsJTFrameBilinear' (frameCoprodPairing (F₁ := F₁) (F₂ := F₂)) :=
  Saturated.frameCoprodPairing'_isJTBilinear

/-! ## §10 Universal property -/

section Universal

variable {F₁ : Type u₁} {F₂ : Type u₂} {F₃ : Type u₃}
  [Order.Frame F₁] [Order.Frame F₂] [Order.Frame F₃]

/-- **The universal-property candidate map** `frameCoprodLift φ`:
sends a saturated downset `S` to `sSup { φ a b | (a, b) ∈ S }`. -/
def frameCoprodLiftFun (φ : F₁ → F₂ → F₃) (S : frameCoprod F₁ F₂) : F₃ :=
  sSup { z | ∃ a b, (a, b) ∈ Saturated.carrier S ∧ z = φ a b }

/-- Monotonicity of a JT-bilinear in the left argument
(derived from `map_inf_left`). -/
lemma IsJTFrameBilinear'.mono_left {φ : F₁ → F₂ → F₃}
    (hφ : IsJTFrameBilinear' φ) (y : F₂) {x x' : F₁} (hx : x ≤ x') :
    φ x y ≤ φ x' y := by
  have hxx' : x ⊓ x' = x := inf_eq_left.mpr hx
  calc φ x y = φ (x ⊓ x') y := by rw [hxx']
    _ = φ x y ⊓ φ x' y := hφ.map_inf_left y x x'
    _ ≤ φ x' y := inf_le_right

/-- Monotonicity in the right argument. -/
lemma IsJTFrameBilinear'.mono_right {φ : F₁ → F₂ → F₃}
    (hφ : IsJTFrameBilinear' φ) (x : F₁) {y y' : F₂} (hy : y ≤ y') :
    φ x y ≤ φ x y' := by
  have hyy' : y ⊓ y' = y := inf_eq_left.mpr hy
  calc φ x y = φ x (y ⊓ y') := by rw [hyy']
    _ = φ x y ⊓ φ x y' := hφ.map_inf_right x y y'
    _ ≤ φ x y' := inf_le_right

/-- `φ ⊥ y = ⊥` (derived from `map_sSup_left ∅`). -/
lemma IsJTFrameBilinear'.bot_left {φ : F₁ → F₂ → F₃}
    (hφ : IsJTFrameBilinear' φ) (y : F₂) :
    φ (⊥ : F₁) y = ⊥ := by
  have : (⊥ : F₁) = sSup (∅ : Set F₁) := sSup_empty.symm
  rw [this, hφ.map_sSup_left]
  simp

/-- `φ x ⊥ = ⊥` (derived from `map_sSup_right ∅`). -/
lemma IsJTFrameBilinear'.bot_right {φ : F₁ → F₂ → F₃}
    (hφ : IsJTFrameBilinear' φ) (x : F₁) :
    φ x (⊥ : F₂) = ⊥ := by
  have : (⊥ : F₂) = sSup (∅ : Set F₂) := sSup_empty.symm
  rw [this, hφ.map_sSup_right]
  simp

/-- **Factorisation half** — the candidate map recovers `φ` on the
image of the pairing.

**Phase B proof (2026-05-18)**: by characterization
(`Saturated.mem_frameCoprodPairing'`).  The carrier of
`frameCoprodPairing a b` is `{(x,y) | (x ≤ a ∧ y ≤ b) ∨ x = ⊥ ∨ y = ⊥}`,
so `u(pairing a b) = sSup` over three branches.  The two "⊥-branches"
contribute `⊥` (by `bot_left` / `bot_right`).  The main branch
`{φ x y | x ≤ a ∧ y ≤ b}` has sup `φ a b` by monotonicity + `(a, b)` ∈
the set. -/
lemma frameCoprodLiftFun_pairing (φ : F₁ → F₂ → F₃)
    (hφ : IsJTFrameBilinear' φ) (a : F₁) (b : F₂) :
    frameCoprodLiftFun φ (frameCoprodPairing a b) = φ a b := by
  apply le_antisymm
  · -- Upper bound: every `φ x y` with `(x, y) ∈ pairing a b` is ≤ `φ a b`.
    apply sSup_le
    rintro z ⟨x, y, hxy, hzeq⟩
    -- hxy : (x, y) ∈ (frameCoprodPairing a b).carrier
    --     = (Saturated.frameCoprodPairing' a b).carrier
    show z ≤ φ a b
    rw [hzeq]
    -- (x, y) ∈ pairing a b in disjunctive form via characterization.
    have hxy_mem : (x, y) ∈ Saturated.frameCoprodPairing' a b := hxy
    have hxy' := (Saturated.mem_frameCoprodPairing' a b x y).mp hxy_mem
    rcases hxy' with ⟨hxa, hyb⟩ | hx_bot | hy_bot
    · exact le_trans (hφ.mono_left y hxa) (hφ.mono_right a hyb)
    · rw [hx_bot, hφ.bot_left]; exact bot_le
    · rw [hy_bot, hφ.bot_right]; exact bot_le
  · -- Lower bound: `φ a b` is one of the elements (witness: (a, b) ∈ pairing a b).
    apply le_sSup
    refine ⟨a, b, ?_, rfl⟩
    exact Saturated.mem_frameCoprodPairing'_self a b

/-- **Key auxiliary**: for fixed `K ∈ F₃`, the set
`{(x, y) | φ x y ≤ K}` is a saturated downset.  This is the workhorse
for proving `u = frameCoprodLiftFun φ` preserves `sSup`. -/
lemma frameCoprodLiftFun_below_set_saturated
    (φ : F₁ → F₂ → F₃) (hφ : IsJTFrameBilinear' φ) (K : F₃) :
    ∃ V : Saturated F₁ F₂, V.carrier = {p | φ p.1 p.2 ≤ K} := by
  refine ⟨{
    carrier := {p | φ p.1 p.2 ≤ K}
    downward_closed := by
      intro a a' b b' ha hb hp
      -- φ a' b' ≤ φ a b ≤ K
      exact le_trans (le_trans (hφ.mono_left b' ha) (hφ.mono_right a hb)) hp
    sup_stable_left := by
      intro s b hs
      -- φ(sSup s) b = sSup (· b) '' s, each ≤ K, so sSup ≤ K.
      show φ (sSup s) b ≤ K
      rw [hφ.map_sSup_left]
      apply sSup_le
      rintro z ⟨α, hα, rfl⟩
      exact hs α hα
    sup_stable_right := by
      intro a s hs
      show φ a (sSup s) ≤ K
      rw [hφ.map_sSup_right]
      apply sSup_le
      rintro z ⟨β, hβ, rfl⟩
      exact hs β hβ }, rfl⟩

/-- `frameCoprodLiftFun φ` is monotone in `S`. -/
lemma frameCoprodLiftFun_mono (φ : F₁ → F₂ → F₃)
    {S T : frameCoprod F₁ F₂} (h : S ≤ T) :
    frameCoprodLiftFun φ S ≤ frameCoprodLiftFun φ T := by
  apply sSup_le_sSup
  rintro z ⟨a, b, hab, rfl⟩
  refine ⟨a, b, h hab, rfl⟩

/-- `frameCoprodLiftFun φ` preserves `sSup`. -/
lemma frameCoprodLiftFun_sSup (φ : F₁ → F₂ → F₃)
    (hφ : IsJTFrameBilinear' φ) (𝒮 : Set (frameCoprod F₁ F₂)) :
    frameCoprodLiftFun φ (sSup 𝒮) =
      sSup ((fun S => frameCoprodLiftFun φ S) '' 𝒮) := by
  refine le_antisymm ?_ ?_
  · -- ≤: every `φ x y` with `(x, y) ∈ sSup 𝒮` is `≤ sSup of lifts`.
    -- Let K := sSup of lifts.  Then for each T ∈ 𝒮, `lift T ≤ K`, so
    -- `T ⊆ {p | φ p ≤ K}` (which is saturated).  Hence `sSup 𝒮 = sat(⋃ T)`
    -- is contained in `{p | φ p ≤ K}`, so each `φ x y` ≤ K for (x,y) ∈ sSup 𝒮.
    let K : F₃ := sSup ((fun S => frameCoprodLiftFun φ S) '' 𝒮)
    obtain ⟨V, hV⟩ := frameCoprodLiftFun_below_set_saturated φ hφ K
    -- Each T ∈ 𝒮 has T.carrier ⊆ V.carrier (since lift T ≤ K, so every
    -- φ a b for (a, b) ∈ T is ≤ K).
    have hT_le_V : ∀ T ∈ 𝒮, (T : Saturated F₁ F₂) ≤ V := by
      intro T hT p hp
      rw [hV]
      show φ p.1 p.2 ≤ K
      have h1 : φ p.1 p.2 ≤ frameCoprodLiftFun φ T := by
        apply le_sSup
        exact ⟨p.1, p.2, hp, rfl⟩
      have h2 : frameCoprodLiftFun φ T ≤ K := by
        apply le_sSup
        exact ⟨T, hT, rfl⟩
      exact le_trans h1 h2
    have h_sSup_le_V : (sSup 𝒮 : Saturated F₁ F₂) ≤ V := by
      show (Saturated.sSupFun 𝒮 : Saturated F₁ F₂) ≤ V
      apply Saturated.sat_le
      intro p hp
      rcases Set.mem_iUnion₂.mp hp with ⟨T, hT, hpT⟩
      exact hT_le_V T hT hpT
    apply sSup_le
    rintro z ⟨x, y, hxy, rfl⟩
    show φ x y ≤ K
    have hxyV : (x, y) ∈ V.carrier := h_sSup_le_V hxy
    rw [hV] at hxyV
    exact hxyV
  · -- ≥: each `lift T` is ≤ `lift (sSup 𝒮)` by monotonicity.
    apply sSup_le
    rintro z ⟨T, hT, rfl⟩
    apply frameCoprodLiftFun_mono
    exact le_sSup hT

/-- `frameCoprodLiftFun φ` preserves `⊤`. -/
lemma frameCoprodLiftFun_top (φ : F₁ → F₂ → F₃)
    (hφ : IsJTFrameBilinear' φ) :
    frameCoprodLiftFun φ (⊤ : frameCoprod F₁ F₂) = ⊤ := by
  apply le_antisymm le_top
  -- φ ⊤ ⊤ = ⊤ ≤ sSup since (⊤, ⊤) ∈ ⊤_Sat = univ.
  rw [← hφ.map_top_top]
  apply le_sSup
  refine ⟨⊤, ⊤, ?_, rfl⟩
  -- (⊤, ⊤) ∈ ⊤_Saturated.carrier = univ.
  show ((⊤ : F₁), (⊤ : F₂)) ∈ (⊤ : Saturated F₁ F₂).carrier
  rw [Saturated.carrier_top]
  exact Set.mem_univ _

/-- `frameCoprodLiftFun φ` preserves `⊓`. -/
lemma frameCoprodLiftFun_inf (φ : F₁ → F₂ → F₃)
    (hφ : IsJTFrameBilinear' φ) (S T : frameCoprod F₁ F₂) :
    frameCoprodLiftFun φ (S ⊓ T) =
      frameCoprodLiftFun φ S ⊓ frameCoprodLiftFun φ T := by
  apply le_antisymm
  · -- (S ⊓ T).carrier ⊆ S.carrier ∩ T.carrier, so every term in lift(S ⊓ T) is in both lifts.
    apply le_inf
    · apply frameCoprodLiftFun_mono; exact inf_le_left
    · apply frameCoprodLiftFun_mono; exact inf_le_right
  · -- The hard direction: uses map_inf_mixed.
    -- lift(S) ⊓ lift(T) ≤ sSup{φ x y ⊓ φ x' y' | (x,y) ∈ S, (x',y') ∈ T}
    --                  = sSup{φ(x ⊓ x')(y ⊓ y')} [map_inf_mixed]
    -- ≤ lift(S ⊓ T) since (x⊓x', y⊓y') ∈ S ⊓ T.
    -- Expand each lift, apply F₃ frame distribution.
    -- After inf_sSup_eq: outer iSup over T's image. After sSup_inf_eq: inner over S's image.
    -- So `(x, y)` ends up in T.carrier and `(x', y')` in S.carrier.
    show sSup { z | ∃ a b, (a, b) ∈ (S : Saturated F₁ F₂).carrier ∧ z = φ a b } ⊓
         sSup { z | ∃ a b, (a, b) ∈ (T : Saturated F₁ F₂).carrier ∧ z = φ a b } ≤ _
    rw [inf_sSup_eq]
    apply iSup_le
    intro z
    apply iSup_le
    rintro ⟨x, y, hxyT, rfl⟩
    rw [sSup_inf_eq]
    apply iSup_le
    intro w
    apply iSup_le
    rintro ⟨x', y', hx'y'S, rfl⟩
    -- Goal: φ x' y' ⊓ φ x y ≤ frameCoprodLiftFun φ (S ⊓ T)
    -- with hx'y'S : (x', y') ∈ S, hxyT : (x, y) ∈ T.
    rw [hφ.map_inf_mixed]
    show φ (x' ⊓ x) (y' ⊓ y) ≤ frameCoprodLiftFun φ (S ⊓ T)
    apply le_sSup
    refine ⟨x' ⊓ x, y' ⊓ y, ?_, rfl⟩
    show (x' ⊓ x, y' ⊓ y) ∈ (S ⊓ T : Saturated F₁ F₂).carrier
    rw [Saturated.carrier_inf]
    refine ⟨?_, ?_⟩
    · -- ∈ S: descend from (x', y') ∈ S via (x' ⊓ x, y' ⊓ y) ≤ (x', y')
      exact S.downward_closed (inf_le_left : x' ⊓ x ≤ x')
        (inf_le_left : y' ⊓ y ≤ y') hx'y'S
    · -- ∈ T: descend from (x, y) ∈ T via (x' ⊓ x, y' ⊓ y) ≤ (x, y)
      exact T.downward_closed (inf_le_right : x' ⊓ x ≤ x)
        (inf_le_right : y' ⊓ y ≤ y) hxyT

/-- The candidate FrameHom built from a JT-bilinear φ. -/
def frameCoprodLift (φ : F₁ → F₂ → F₃) (hφ : IsJTFrameBilinear' φ) :
    FrameHom (frameCoprod F₁ F₂) F₃ where
  toFun := frameCoprodLiftFun φ
  map_inf' := frameCoprodLiftFun_inf φ hφ
  map_top' := frameCoprodLiftFun_top φ hφ
  map_sSup' := frameCoprodLiftFun_sSup φ hφ

@[simp] lemma frameCoprodLift_apply (φ : F₁ → F₂ → F₃)
    (hφ : IsJTFrameBilinear' φ) (S : frameCoprod F₁ F₂) :
    frameCoprodLift φ hφ S = frameCoprodLiftFun φ S := rfl

/-- **Auxiliary uniqueness lemma**: every saturated set is the `sSup` of
the pairings of its elements. -/
lemma Saturated.eq_sSup_of_pairings (S : Saturated F₁ F₂) :
    S = sSup ((fun (p : F₁ × F₂) => Saturated.frameCoprodPairing' p.1 p.2) '' S.carrier) := by
  apply le_antisymm
  · -- ≤: every (p, q) ∈ S is in the sSup (since pairing p q contains (p, q)
    -- and pairing p q is one of the supped Saturateds).
    intro p hp
    -- Want: p ∈ (sSup ...)
    have : Saturated.frameCoprodPairing' p.1 p.2 ≤
        sSup ((fun (p : F₁ × F₂) => Saturated.frameCoprodPairing' p.1 p.2) '' S.carrier) := by
      apply le_sSup
      refine ⟨p, hp, rfl⟩
    apply this
    exact Saturated.mem_frameCoprodPairing'_self p.1 p.2
  · -- ≥: each pairing p q for (p, q) ∈ S is ≤ S.
    apply sSup_le
    rintro T ⟨p, hp, rfl⟩
    rw [Saturated.frameCoprodPairing'_le_iff]
    exact hp

/-- **Universal property of the frame coproduct** (Phase B, 2026-05-18).

For any JT-bilinear `φ : F₁ → F₂ → F₃` (satisfying the six axioms of
`IsJTFrameBilinear'`, including `map_top_top` and `map_inf_mixed`),
there exists a **unique** frame morphism
`u : frameCoprod F₁ F₂ → F₃` factoring `φ` through `frameCoprodPairing`.

**Existence**: the witness is `frameCoprodLift φ hφ` (defined above as
the saturated-downset sSup of `φ`-images), verified to be a `FrameHom`
via `frameCoprodLiftFun_sSup`, `_top`, `_inf`.

**Uniqueness**: any other `FrameHom v` with `v ∘ pairing = φ` agrees
with `u` on every saturated downset, because every `S` equals
`sSup {pairing p q | (p, q) ∈ S}` (`Saturated.eq_sSup_of_pairings`), and
both `u` and `v` preserve sSup. -/
theorem frameCoprod_universal (φ : F₁ → F₂ → F₃) (hφ : IsJTFrameBilinear' φ) :
    ∃! (u : FrameHom (frameCoprod F₁ F₂) F₃),
      ∀ a b, u (frameCoprodPairing a b) = φ a b := by
  refine ⟨frameCoprodLift φ hφ, ?_, ?_⟩
  · -- Existence: frameCoprodLift satisfies the factorisation.
    intro a b
    show frameCoprodLiftFun φ (frameCoprodPairing a b) = φ a b
    exact frameCoprodLiftFun_pairing φ hφ a b
  · -- Uniqueness: any v agreeing on pairings equals frameCoprodLift.
    intro v hv
    apply DFunLike.ext
    intro S
    -- v(S) = v(sSup{pairing p q | (p, q) ∈ S}) = sSup{v(pairing p q) | (p, q) ∈ S}
    --      = sSup{φ p q | (p, q) ∈ S} = frameCoprodLift φ hφ S.
    have hS_eq : (S : Saturated F₁ F₂) =
        sSup ((fun (p : F₁ × F₂) => Saturated.frameCoprodPairing' p.1 p.2) ''
              (S : Saturated F₁ F₂).carrier) :=
      Saturated.eq_sSup_of_pairings S
    have step1 : v S = v (sSup ((fun (p : F₁ × F₂) =>
        Saturated.frameCoprodPairing' p.1 p.2) '' (S : Saturated F₁ F₂).carrier)) := by
      apply congr_arg
      exact hS_eq
    rw [step1]
    -- v preserves sSup.
    have step2 : v (sSup ((fun (p : F₁ × F₂) =>
        Saturated.frameCoprodPairing' p.1 p.2) '' (S : Saturated F₁ F₂).carrier)) =
        sSup (v '' ((fun (p : F₁ × F₂) =>
        Saturated.frameCoprodPairing' p.1 p.2) '' (S : Saturated F₁ F₂).carrier)) :=
      map_sSup v _
    rw [step2]
    -- Goal: sSup (v '' (pairings '' S.carrier)) = (frameCoprodLift φ hφ) S
    show sSup _ = frameCoprodLiftFun φ S
    apply le_antisymm
    · apply sSup_le
      rintro z hz
      -- z ∈ v '' (pairings '' S.carrier), so z = v(pairing p.1 p.2) for some p ∈ S.
      rcases hz with ⟨T, hT, rfl⟩
      rcases hT with ⟨p, hp, rfl⟩
      -- v(pairing p.1 p.2) = φ p.1 p.2 by hv.
      rw [show v (Saturated.frameCoprodPairing' p.1 p.2) =
            v (frameCoprodPairing p.1 p.2) from rfl, hv]
      -- φ p.1 p.2 ≤ frameCoprodLiftFun φ S since p ∈ S.carrier.
      apply le_sSup
      exact ⟨p.1, p.2, hp, rfl⟩
    · apply sSup_le
      rintro z ⟨a, b, hab, rfl⟩
      -- z = φ a b, want ≤ sSup (v '' (pairings ''  S.carrier)).
      -- φ a b = v (pairing a b), and pairing a b ∈ pairings '' S.carrier (with p = (a,b)).
      rw [← hv a b]
      show v (frameCoprodPairing a b) ≤ _
      apply le_sSup
      refine ⟨Saturated.frameCoprodPairing' a b, ⟨(a, b), hab, rfl⟩, rfl⟩

end Universal

/-! ## §11 Summary — Phase B complete (2026-05-18)

All five Phase-A `sorry`s have been discharged, and the predicate
`IsJTFrameBilinear'` has been refined with two additional axioms
(`map_top_top` and `map_inf_mixed`) that the original four-axiom
formulation was missing for the universal property to be TRUE
(see §1 docstring for the explicit Phase B counter-example).

### Fully proved / `sorry`-free (Phase A + B closed)
* **§1** `IsJTFrameBilinear'` predicate — **6 axioms** (Phase B 2026-05-18
  added `map_top_top` and `map_inf_mixed`; see §1 docstring B-1/B-2 notes).
* **§2-§3** `Saturated F₁ F₂` carrier + order structure.
* **§4** Saturation closure (`sInfFun`, `sat`, lattice of saturated downsets).
* **§5** Binary `⊓`, `⊔`, `⊤`, `⊥`, arbitrary `sInf`, `sSup` structure.
* **§5.2** `CompleteLattice (Saturated F₁ F₂)` instance — **fully proved**.
* **§6** `inf_sSup_le_iSup_inf_aux` — JT 1984 §VI distributivity
  (Phase B proof: ~80 LOC, "downward-stable indicator saturated set"
  trick using frame distributivity in F₁/F₂).
* **§7** `frameCoprod F₁ F₂` type + `Order.Frame` instance.
* **§8** Canonical `frameCoprodPairing` via saturation of singletons,
  with **explicit characterization** `mem_frameCoprodPairing'`
  (Phase B 2026-05-18).
* **§9** `frameCoprodPairing` JT-bilinear: ALL six axioms proven via
  the carrier characterization.
* **§10** `frameCoprodLift` (full `FrameHom`) + `frameCoprod_universal`
  (existence + uniqueness, Phase B 2026-05-18).

### Total inventory
* Total `sorry`s: **0**.
* New axioms: **0**.
* Files modified: **0** (consumers `FrameBimorphism.lean` and
  `Doctrine/Instance/Topological.lean` left untouched; they have their
  own self-contained proofs which are NOT a strict refactor target —
  see Phase B-3 below).

### Phase B-2 — Cube specialization (next step, not yet)
A theorem `frameCoprod (Fin N → Ω) (Fin M → Ω) ≃o (Fin (N*M) → Ω)`
would give the cube specialization.  The forward map (frameCoprod →
cube) is constructive via `frameCoprodLift cubePairing _` once
`cubePairing` is shown to be `IsJTFrameBilinear'` (the trickier axiom
is `map_inf_mixed`).  The reverse map and iso proof require additional
machinery (~100-200 LOC).  See `CubeFrameCoprod.lean` for a future
deliverable.

### Phase B-3 — Refactor consumers (deferred)
`FrameBimorphism.lean`'s `cube_JT_universal_property` and the
`to_topological_P3` consumer have a local self-contained proof
using `SierpinskiOmega = Prop` directly.  The general
`frameCoprod_universal` here is now available, but a refactor would
require:
  (i) Showing `cubePairing` satisfies `IsJTFrameBilinear'` (including
      the new `map_inf_mixed` and `map_top_top` axioms).
  (ii) Constructing the iso `frameCoprod cubeN cubeM ≃o cube(N*M)`.
  (iii) Transporting `frameCoprod_universal` through the iso.

Deferred to keep this PR scope-bounded — the local proofs work and
no consumer is currently blocked.
-/

end SSBX.Foundation.Order
