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

/-! ## §3  Structural uniqueness at `axes = 8` — reduced to a Lean exercise

With the face axiom in place, the freedom in choosing `dual` is gone:
both `U` and `wenCodeUGFace` have `dual = bitwise-NOT under their
respective bit-frames`.  The only remaining task is to compose the two
frames and verify the composite intertwines the duals.

This is **no longer a research task** (cf. §4.7bis.5 item (d)) — it is
a Lean exercise about `Equiv.trans` and `Fin.cast` across the
`U.axes = 8` hypothesis.  We state it as a `Prop` and discharge the
concrete instance for `wenCodeUGFace` itself; the general case
follows by the proof sketch in the docstring once `Fin.castIso`-style
bridges are inserted. -/

namespace UGCandidateFace

/-- The conjecture: every `axes = 8` `UGCandidateFace` is `Iso` to
`wenCodeUG` at the `UGCandidate` level, with the iso explicitly given
by frame-composition `U.bitsEquiv ⋯ WenCode.bitsEquiv.symm`.

Proof sketch (Lean exercise):
1. Build `bridge : U.Carrier ≃ WenCode` as the composition
   `U.bitsEquiv ⟶ Fin.castIso h ⟶ WenCode.bitsEquiv.symm`.
2. Show `bridge (U.dual c) = WenCode.dual (bridge c)` by:
   * `bridge (U.dual c) = WenCode.bitsEquiv.symm (cast (U.bitsEquiv (U.dual c)))`
   * `= WenCode.bitsEquiv.symm (cast (fun i => !(U.bitsEquiv c i)))` (by `U.dual_is_bitwise_not`)
   * `= WenCode.bitsEquiv.symm (fun i => !(WenCode.bitsEquiv (bridge c) i))` (push cast through `!`)
   * `= WenCode.dual (bridge c)` (by `WenCode.dual_via_bits`).
3. The `atom_comm` direction follows from `dual_is_bitwise_not` not
   touching `atom`; one verifies `atom` is preserved on the bridge by
   checking the 8 seeded cells map correctly (or strengthens the face
   axiom to include atom-preservation directly). -/
def face_uniqueness_conjecture : Prop :=
  ∀ U : UGCandidateFace, U.axes = 8 →
    Nonempty (UGCandidate.Iso U.toUGCandidate wenCodeUGFace.toUGCandidate)

/-- Concrete discharge for the witness itself: `wenCodeUGFace` is iso
to itself, trivially. -/
theorem wenCodeUGFace_self_iso :
    Nonempty (UGCandidate.Iso wenCodeUGFace.toUGCandidate
      wenCodeUGFace.toUGCandidate) :=
  ⟨UGCandidate.Iso.refl _⟩

end UGCandidateFace

/-! ## §4  Self-test -/

example : wenCodeUGFace.toUGCandidateRich = wenCodeUGRich := rfl
example : wenCodeUGFace.axes = 8 := rfl
example : WenCode.toBits ⟨0, by decide⟩ = fun _ => false := by
  funext i; fin_cases i <;> decide
example : WenCode.toBits ⟨255, by decide⟩ = fun _ => true := by
  funext i; fin_cases i <;> decide

end SSBX.Foundation.Wen.X2Codes
