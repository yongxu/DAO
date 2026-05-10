/-
# WenyanQuineKleene — quotation/Kleene route boundary

This file records the minimal interface needed to connect a proper Wenyan
quotation route to the existing Kleene fixed-point route.

The key boundary is intentional:

* `KleeneInternal.KleeneFixedPointExists` is a halting-behavior fixed point:
  `Halts D h ↔ HaltsWith F h (ProgEnc.encProg D)`.
* A Wenyan quine target is stronger/different data: a concrete run whose
  `history` is exactly `ProgEnc.encProg D`.

No full Kleene quine construction is claimed here.
-/
import SSBX.Foundation.Wen.WenyanQuineSpec
import SSBX.Foundation.Bagua.KleeneInternal
import SSBX.Foundation.Wen.WenyanSelfInterp

namespace SSBX.Foundation.Wen.WenyanQuineKleene

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.GodelLi
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanQuineSpec

/-! ## Quotation interface -/

/-- A quotation compiler turns a Wenyan program `P` into a closed program that,
when run from an ordinary initial state, emits exactly `ProgEnc.encProg P` into
history for some finite fuel.

This is a history-equality specification, not a halting-behavior fixed point. -/
def QuoterSpec (quote : List YiInstr → List YiInstr) : Prop :=
  ∀ (P : List YiInstr) (h : Hexagram),
    ∃ fuel : Nat, QuineRunSpec P (YiState.init h (quote P)) fuel

/-- If a quoter satisfies `QuoterSpec`, its witness is exactly the raw
`ProgEnc.encProg` history target from `WenyanQuineSpec`. -/
theorem quoterSpec_outputs_encProg
    {quote : List YiInstr → List YiInstr}
    (hquote : QuoterSpec quote)
    (P : List YiInstr) (h : Hexagram) :
    ∃ fuel : Nat,
      ((YiState.init h (quote P)).runFuel fuel).history = ProgEnc.encProg P := by
  exact hquote P h

/-! ## Self-application interface -/

/-- Halting-only self-application for a particular one-input program `F` and
closed fixed point `D`.

This is exactly the shape used by `KleeneInternal.KleeneFixedPointExists`. -/
def SelfApplicationHaltingSpec (F D : List YiInstr) : Prop :=
  ∀ h : Hexagram, Halts D h ↔ HaltsWith F h (ProgEnc.encProg D)

/-- Functional form of the halting self-application interface.  It is useful as
a compiler target, while `KleeneFixedPointExists` keeps the existential form. -/
def SelfApplicationSpec (selfApply : List YiInstr → List YiInstr) : Prop :=
  ∀ F : List YiInstr, SelfApplicationHaltingSpec F (selfApply F)

/-- Existential halting self-application is definitionally the current Kleene
fixed-point interface.  This marker is the formal reminder that the existing
interface talks about halting behavior only. -/
def HaltingSelfApplicationExists : Prop :=
  ∀ F : List YiInstr, ∃ D : List YiInstr, SelfApplicationHaltingSpec F D

theorem haltingSelfApplicationExists_iff_kleeneFixedPointExists :
    HaltingSelfApplicationExists ↔ KleeneFixedPointExists := by
  rfl

/-- A functional self-application compiler is enough to satisfy the existing
halting-only Kleene fixed-point interface. -/
theorem selfApplicationSpec_to_kleeneFixedPointExists
    {selfApply : List YiInstr → List YiInstr}
    (hself : SelfApplicationSpec selfApply) :
    KleeneFixedPointExists := by
  intro F
  exact ⟨selfApply F, hself F⟩

/-! ## Stronger payload needed for a quine-style Kleene result -/

/-- A payload for the stronger "Kleene quine" target for a one-input program
`F`: it contains both the halting fixed-point behavior and an explicit
history-equality run of the fixed-point source.

The `init_runs_fixedPoint` field records that the history theorem is about a
run of the same closed program `fixedPoint`, rather than an unrelated emitter. -/
structure KleeneQuinePayload (F : List YiInstr) where
  fixedPoint : List YiInstr
  init : YiState
  fuel : Nat
  init_runs_fixedPoint : init.prog = fixedPoint
  haltingSpec : SelfApplicationHaltingSpec F fixedPoint
  historySpec : QuineRunSpec fixedPoint init fuel

/-- The payload projects to the current halting-only Kleene fixed-point data. -/
theorem KleeneQuinePayload.to_selfApplicationHaltingSpec
    {F : List YiInstr} (payload : KleeneQuinePayload F) :
    SelfApplicationHaltingSpec F payload.fixedPoint :=
  payload.haltingSpec

/-- The payload also carries the Wenyan quine history target. -/
theorem KleeneQuinePayload.to_quineRunSpec
    {F : List YiInstr} (payload : KleeneQuinePayload F) :
    QuineRunSpec payload.fixedPoint payload.init payload.fuel :=
  payload.historySpec

/-- Existence of the stronger history-equality payload for every `F`.  This is
not proved here; it is the intended target for a proper quotation construction. -/
def HistoryEqualityFixedPointExists : Prop :=
  ∀ F : List YiInstr, Nonempty (KleeneQuinePayload F)

/-- A history-equality Kleene payload would imply the existing halting-only
`KleeneFixedPointExists`.  The reverse direction is deliberately not stated:
halting behavior alone does not provide a `history = encProg` run. -/
theorem historyEqualityFixedPointExists_to_kleeneFixedPointExists
    (hpayload : HistoryEqualityFixedPointExists) :
    KleeneFixedPointExists := by
  intro F
  rcases hpayload F with ⟨payload⟩
  exact ⟨payload.fixedPoint, payload.haltingSpec⟩

/-- Public summary of what this file proves: quotation is stated as a
history-equality interface; current Kleene fixed points are halting-only; a
stronger payload would bridge from history equality back to the existing
halting interface. -/
theorem wenyanQuineKleene_summary :
    (∀ quote, QuoterSpec quote →
      ∀ P h, ∃ fuel,
        ((YiState.init h (quote P)).runFuel fuel).history = ProgEnc.encProg P)
    ∧ (HaltingSelfApplicationExists ↔ KleeneFixedPointExists)
    ∧ (∀ selfApply, SelfApplicationSpec selfApply → KleeneFixedPointExists)
    ∧ (HistoryEqualityFixedPointExists → KleeneFixedPointExists) := by
  exact ⟨fun _ hquote P h => quoterSpec_outputs_encProg hquote P h,
    haltingSelfApplicationExists_iff_kleeneFixedPointExists,
    fun _ hself => selfApplicationSpec_to_kleeneFixedPointExists hself,
    historyEqualityFixedPointExists_to_kleeneFixedPointExists⟩

end SSBX.Foundation.Wen.WenyanQuineKleene
