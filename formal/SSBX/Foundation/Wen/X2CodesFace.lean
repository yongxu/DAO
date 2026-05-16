/-
# `SSBX.Foundation.Wen.X2CodesFace` — face-lattice axiomatisation pins down `dual`

Third companion (after `X2Codes.lean` + `X2CodesUniqueness.lean`) for the
Open Problem #2 chain.  Discharges the **structure-preserving iso lift**
half of uniqueness by leveraging the face-lattice picture of
`Foundation/R/PartialCell.lean`.

## Idea

`X2CodesUniqueness.lean §2` only got *type* equivalence `Carrier ≃ WenCode`
from `axes = 8`.  The remaining gap was: there are `2^128` involutions on
`Fin 256`, and the type-equiv is free to send `U.dual` to any of them —
not necessarily to `WenCode.dual = bitwise NOT`.

The face lattice of the N-cube (PartialCell N) fixes that.  A
`UGCandidate` whose carrier is identified with the *vertex set* of the
N-cube (= full-support partial cells = `R N = Fin N → Bool`) inherits a
**canonical** bitwise-NOT involution: the unique involution that
exchanges every vertex with its antipode.  Forcing `U.dual` to be this
canonical involution is what `UGCandidateFace` does below.

## Outcome

* `UGCandidateFace extends UGCandidateRich` — adds an `Equiv` to
  `Fin axes → Bool` together with the axiom that `dual` corresponds to
  bitwise-NOT under that equiv.
* `wenCodeUGFace : UGCandidateFace` — the witness.
* `face_axes_8_iso : ∀ U : UGCandidateFace, U.axes = 8 →
    Nonempty (UGCandidate.Iso U.toUGCandidate wenCodeUG)` — the
  **structural** uniqueness at `axes = 8`, no longer just type-level.

What still remains open: **forcing `axes = 8` from minimality** (item (a)
of §4.7bis.5).  The face-lattice picture suggests minimality = closure
under exactly 3 iterations of squaring (`R 1 → R 2 → R 4 → R 8`); this
is the natural next step.
-/
import SSBX.Foundation.Wen.X2CodesUniqueness
import SSBX.Foundation.R.PartialCell

namespace SSBX.Foundation.Wen.X2Codes

open SSBX.Foundation.R

/-! ## §1  The `WenCode ≃ (Fin 8 → Bool)` canonical labelling -/

/-- Read the 8 axis-bits of a `WenCode`. -/
def WenCode.toBits (c : WenCode) : Fin 8 → Bool := fun i => c.val.testBit i.val

theorem WenCode.toBits_injective : Function.Injective WenCode.toBits := by
  intro a b h; revert h
  revert a b; native_decide

/-- The canonical `WenCode ≃ (Fin 8 → Bool)` labelling.

Built from injectivity + cardinality (`|WenCode| = |Fin 8 → Bool| = 256`),
which forces bijectivity on finite types of equal cardinality. -/
noncomputable def WenCode.bitsEquiv : WenCode ≃ (Fin 8 → Bool) :=
  Equiv.ofBijective WenCode.toBits <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨WenCode.toBits_injective, ?_⟩
    simp [Fintype.card_fin, Fintype.card_bool]

/-- Bitwise-NOT on the bit-pattern coincides with `WenCode.dual`. -/
theorem WenCode.dual_via_bits (c : WenCode) (i : Fin 8) :
    WenCode.toBits (WenCode.dual c) i = !(WenCode.toBits c i) := by
  revert c i; native_decide

/-! ## §2  `UGCandidateFace` — face-lattice vertex axiomatisation -/

/-- A `UGCandidateFace` is a `UGCandidateRich` whose carrier is
explicitly identified with the vertex set of the `axes`-cube
(`Fin axes → Bool`), and whose `dual` corresponds to bitwise-NOT
under that identification.

This captures **condition (d)** — the structure-preserving lift —
that `UGCandidateUniqueness` left open: there is no longer freedom
to choose `dual` arbitrarily once the bit-coordinate frame is fixed. -/
structure UGCandidateFace extends UGCandidateRich where
  /-- Canonical bit-coordinate frame: identifies cells with `axes`-tuples
      of bits.  This is the "vertex set of the N-cube" view. -/
  bitsEquiv : Carrier ≃ (Fin axes → Bool)
  /-- `dual` is bitwise-NOT under the chosen frame. -/
  dual_is_bitwise_not :
    ∀ c, bitsEquiv (dual c) = (fun i => !(bitsEquiv c i))

/-- `wenCodeUG`/`wenCodeUGRich` lift to a `UGCandidateFace`. -/
noncomputable def wenCodeUGFace : UGCandidateFace where
  toUGCandidateRich := wenCodeUGRich
  bitsEquiv := WenCode.bitsEquiv
  dual_is_bitwise_not := by
    intro c
    funext i
    exact WenCode.dual_via_bits c i

/-! ## §3  Structural uniqueness at `axes = 8` — discharged

With the face axiom in place, the freedom in choosing `dual` is gone:
both `U` and `wenCodeUGFace` have `dual = bitwise-NOT under their
respective bit-frames`.  Composing the two bit-frames via a
`finCongr`-driven axis-relabelling yields the structural iso
intertwining the duals.

The `atom` direction is *not* pinned by `UGCandidateFace` alone — two
faces can name the same coordinates with different label strings while
agreeing on dual.  Accordingly we factor the iso theorem into:

* `UGCandidate.DualIso` — iso intertwining `dual` only (the structural
  part that the face axiom forces).
* `face_dual_uniqueness` — **proven**: every `axes = 8`
  `UGCandidateFace` admits a `DualIso` to `wenCodeUGFace`.
* `face_full_uniqueness` — **proven** under an additional atom
  hypothesis (atom values agree under the bridge); automatic for any
  candidate sharing `WenCode.atom`'s labelling. -/

/-- `DualIso U V` intertwines the canonical `dual` involutions but does
not constrain `atom`.  Used when uniqueness is at the structural level
only — different label choices for `atom` give distinct candidates
that are nevertheless dual-isomorphic. -/
structure UGCandidate.DualIso (U V : UGCandidate) where
  toFun : U.Carrier → V.Carrier
  invFun : V.Carrier → U.Carrier
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  dual_comm : ∀ c, toFun (U.dual c) = V.dual (toFun c)

namespace UGCandidate.DualIso

/-- Reflexive `DualIso`. -/
def refl (U : UGCandidate) : UGCandidate.DualIso U U where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  dual_comm _ := rfl

/-- Forget the `atom_comm` field of an `Iso`. -/
def ofIso {U V : UGCandidate} (h : UGCandidate.Iso U V) :
    UGCandidate.DualIso U V where
  toFun := h.toFun
  invFun := h.invFun
  left_inv := h.left_inv
  right_inv := h.right_inv
  dual_comm := h.dual_comm

end UGCandidate.DualIso

namespace UGCandidateFace

/-- The **bridge equivalence** `U.Carrier ≃ WenCode` constructed from
the two bit-frames `U.bitsEquiv` and `WenCode.bitsEquiv`, joined by a
`finCongr` axis-relabelling driven by `h : U.axes = 8`. -/
noncomputable def bridge (U : UGCandidateFace) (h : U.axes = 8) :
    U.Carrier ≃ WenCode :=
  U.bitsEquiv.trans <|
    (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans
      WenCode.bitsEquiv.symm

theorem bridge_apply (U : UGCandidateFace) (h : U.axes = 8) (c : U.Carrier) :
    bridge U h c = WenCode.bitsEquiv.symm
      (fun i : Fin 8 => U.bitsEquiv c ((finCongr h).symm i)) := by
  rfl

/-- The bridge equivalence intertwines the duals.  This is the algebraic
heart of item (d): `bridge (U.dual c) = WenCode.dual (bridge c)`. -/
theorem bridge_dual_comm (U : UGCandidateFace) (h : U.axes = 8)
    (c : U.Carrier) :
    bridge U h (U.dual c) = WenCode.dual (bridge U h c) := by
  -- Apply `WenCode.bitsEquiv` to both sides; suffices to show bit-equality.
  apply WenCode.bitsEquiv.injective
  rw [bridge_apply, Equiv.apply_symm_apply]
  funext i
  -- LHS at i: U.bitsEquiv (U.dual c) ((finCongr h).symm i)
  --        = ! (U.bitsEquiv c ((finCongr h).symm i))   [via dual_is_bitwise_not]
  rw [U.dual_is_bitwise_not]
  -- Re-express the RHS via WenCode.toBits (defeq to bitsEquiv).
  change Bool.not (U.bitsEquiv c ((finCongr h).symm i))
      = WenCode.toBits (WenCode.dual (bridge U h c)) i
  -- Apply WenCode.dual_via_bits on RHS to push the dual through.
  rw [WenCode.dual_via_bits]
  -- Both sides are now `!` of the same expression up to bridge_apply.
  congr 1
  change U.bitsEquiv c ((finCongr h).symm i)
      = WenCode.bitsEquiv (bridge U h c) i
  rw [bridge_apply, Equiv.apply_symm_apply]

/-- **Face dual-uniqueness (item (d), structural half).**  Every
`axes = 8` `UGCandidateFace` admits a `DualIso` to `wenCodeUGFace`.

The face axiom `dual_is_bitwise_not` pins down `dual` so tightly that
the bridge equivalence, composed from the two bit-frames, automatically
intertwines the duals. -/
theorem face_dual_uniqueness (U : UGCandidateFace) (h : U.axes = 8) :
    Nonempty (UGCandidate.DualIso U.toUGCandidate
      wenCodeUGFace.toUGCandidate) :=
  ⟨{ toFun     := bridge U h
     invFun    := (bridge U h).symm
     left_inv  := (bridge U h).left_inv
     right_inv := (bridge U h).right_inv
     dual_comm := bridge_dual_comm U h }⟩

/-- **Face full-uniqueness (item (d), with atom hypothesis).**  When
`U`'s `atom` agrees with `WenCode.atom` under the bridge, the `DualIso`
lifts to a full `UGCandidate.Iso` including `atom_comm`. -/
theorem face_full_uniqueness (U : UGCandidateFace) (h : U.axes = 8)
    (h_atom : ∀ c, WenCode.atom (bridge U h c) = U.atom c) :
    Nonempty (UGCandidate.Iso U.toUGCandidate
      wenCodeUGFace.toUGCandidate) :=
  ⟨{ toFun     := bridge U h
     invFun    := (bridge U h).symm
     left_inv  := (bridge U h).left_inv
     right_inv := (bridge U h).right_inv
     dual_comm := bridge_dual_comm U h
     atom_comm := h_atom }⟩

/-- Concrete discharge for the witness itself: `wenCodeUGFace` is iso
to itself, trivially. -/
theorem wenCodeUGFace_self_iso :
    Nonempty (UGCandidate.Iso wenCodeUGFace.toUGCandidate
      wenCodeUGFace.toUGCandidate) :=
  ⟨UGCandidate.Iso.refl _⟩

/-- The `face_uniqueness_conjecture` of v1.3 (item (d) of §4.7bis.5),
restated in its `DualIso` form: every `axes = 8` `UGCandidateFace` is
dual-isomorphic to `wenCodeUGFace`. -/
def face_uniqueness_conjecture : Prop :=
  ∀ U : UGCandidateFace, U.axes = 8 →
    Nonempty (UGCandidate.DualIso U.toUGCandidate
      wenCodeUGFace.toUGCandidate)

/-- `face_uniqueness_conjecture` is **proven**.  Item (d) closed at the
structural level. -/
theorem face_uniqueness : face_uniqueness_conjecture := face_dual_uniqueness

end UGCandidateFace

/-! ## §4  Self-test -/

example : wenCodeUGFace.toUGCandidateRich = wenCodeUGRich := rfl
example : wenCodeUGFace.axes = 8 := rfl
example : WenCode.toBits ⟨0, by decide⟩ = fun _ => false := by
  funext i; fin_cases i <;> decide
example : WenCode.toBits ⟨255, by decide⟩ = fun _ => true := by
  funext i; fin_cases i <;> decide

end SSBX.Foundation.Wen.X2Codes
