import SSBX.Foundation.Wen.WenyanQuineKleene

/-!
# WenyanLambdaRoute

The nontrivial Tier 3 route is not the literal emitter route: that route is
blocked by `WenyanQuineConcreteSearch.literal_emitter_fixed_point_obstruction`.

The viable route is to build a computational calculus on top of YiInstr and
give it a quotation/self-application backend.  This file separates the raw
history target from the stronger Kleene halting target, so the Tier 3 quine
route does not depend on halting equivalence.
-/

namespace SSBX.Foundation.Wen.WenyanLambdaRoute

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanQuineSpec
open SSBX.Foundation.Wen.WenyanQuineKleene

/-- The raw Tier 3 target as an existence statement. -/
def Tier3QuineExists : Prop :=
  ∃ (P : List YiInstr) (init : YiState) (fuel : Nat),
    init.prog = P ∧ (init.runFuel fuel).history = ProgEnc.encProg P

/-- Pure Tier 3 target for the lambda route: for every parameter program `F`,
the backend produces a closed source whose run emits its own raw encoding.

This is intentionally history-only.  It does not claim the stronger Kleene
halting equivalence. -/
def LambdaHistoryFixedPointExists : Prop :=
  ∀ _F : List YiInstr,
    Tier3QuineExists

theorem lambdaHistoryFixedPointExists_to_tier3QuineExists
    (h : LambdaHistoryFixedPointExists) :
    Tier3QuineExists :=
  h []

/-- A minimal lambda backend sufficient for the raw Tier 3 history quine. -/
structure LambdaHistoryBackend where
  Term : Type
  compile : Term → List YiInstr
  selfApply : List YiInstr → Term
  initOf : List YiInstr → YiState
  fuelOf : List YiInstr → Nat
  init_runs_compiled :
    ∀ F : List YiInstr, (initOf F).prog = compile (selfApply F)
  historySpec :
    ∀ F : List YiInstr,
      QuineRunSpec (compile (selfApply F)) (initOf F) (fuelOf F)

namespace LambdaHistoryBackend

/-- A history backend yields a concrete raw Tier 3 quine source for each
parameter program. -/
theorem concrete_quine_for
    (backend : LambdaHistoryBackend) (F : List YiInstr) :
    ∃ (P : List YiInstr) (init : YiState) (fuel : Nat),
      init.prog = P ∧ (init.runFuel fuel).history = ProgEnc.encProg P := by
  refine ⟨backend.compile (backend.selfApply F), backend.initOf F, backend.fuelOf F,
    backend.init_runs_compiled F, ?_⟩
  exact backend.historySpec F

theorem to_historyFixedPointExists
    (backend : LambdaHistoryBackend) :
    LambdaHistoryFixedPointExists := by
  intro F
  exact backend.concrete_quine_for F

theorem to_tier3QuineExists
    (backend : LambdaHistoryBackend) :
    Tier3QuineExists :=
  lambdaHistoryFixedPointExists_to_tier3QuineExists
    backend.to_historyFixedPointExists

end LambdaHistoryBackend

/-- A lambda/quotation backend sufficient for a Tier 3 history quine plus the
stronger Kleene halting fixed-point interface.

The fields are intentionally Yi-facing:
* `compile` lowers backend terms to `YiInstr`;
* `selfApply` constructs the backend fixed point for a one-input Yi program;
* `haltingSpec` gives the halting self-application behavior;
* `historySpec` gives the exact raw-history quine run.

Constructing this backend is the substantive lambda-calculus engineering
remaining after the literal-emitter route is ruled out. -/
structure LambdaQuotationBackend where
  Term : Type
  compile : Term → List YiInstr
  selfApply : List YiInstr → Term
  initOf : List YiInstr → YiState
  fuelOf : List YiInstr → Nat
  init_runs_compiled :
    ∀ F : List YiInstr, (initOf F).prog = compile (selfApply F)
  haltingSpec :
    ∀ F : List YiInstr, SelfApplicationHaltingSpec F (compile (selfApply F))
  historySpec :
    ∀ F : List YiInstr,
      QuineRunSpec (compile (selfApply F)) (initOf F) (fuelOf F)

namespace LambdaQuotationBackend

def toHistoryBackend (backend : LambdaQuotationBackend) :
    LambdaHistoryBackend :=
  { Term := backend.Term
  , compile := backend.compile
  , selfApply := backend.selfApply
  , initOf := backend.initOf
  , fuelOf := backend.fuelOf
  , init_runs_compiled := backend.init_runs_compiled
  , historySpec := backend.historySpec }

/-- A lambda quotation backend gives the stronger Kleene-quine payload. -/
def payload (backend : LambdaQuotationBackend) (F : List YiInstr) :
    KleeneQuinePayload F :=
  { fixedPoint := backend.compile (backend.selfApply F)
  , init := backend.initOf F
  , fuel := backend.fuelOf F
  , init_runs_fixedPoint := backend.init_runs_compiled F
  , haltingSpec := backend.haltingSpec F
  , historySpec := backend.historySpec F }

theorem to_historyEqualityFixedPointExists
    (backend : LambdaQuotationBackend) :
    HistoryEqualityFixedPointExists := by
  intro F
  exact ⟨backend.payload F⟩

theorem to_kleeneFixedPointExists
    (backend : LambdaQuotationBackend) :
    KleeneFixedPointExists :=
  historyEqualityFixedPointExists_to_kleeneFixedPointExists
    (to_historyEqualityFixedPointExists backend)

/-- A backend also yields one concrete raw Tier 3 source for any chosen
one-input program `F`: the compiled self-application term. -/
theorem concrete_quine_for
    (backend : LambdaQuotationBackend) (F : List YiInstr) :
    ∃ (P : List YiInstr) (init : YiState) (fuel : Nat),
      init.prog = P ∧ (init.runFuel fuel).history = ProgEnc.encProg P := by
  refine ⟨backend.compile (backend.selfApply F), backend.initOf F, backend.fuelOf F,
    backend.init_runs_compiled F, ?_⟩
  exact backend.historySpec F

end LambdaQuotationBackend

/-- Public route theorem: finishing the history-only lambda backend is enough
to finish the raw Tier 3 quine target. -/
theorem lambda_history_backend_finishes_tier3
    (backend : LambdaHistoryBackend) :
    LambdaHistoryFixedPointExists :=
  backend.to_historyFixedPointExists

theorem lambda_history_backend_gives_tier3_quine
    (backend : LambdaHistoryBackend) :
    Tier3QuineExists :=
  backend.to_tier3QuineExists

/-- Public route theorem: finishing the stronger quotation backend is enough
to finish both the raw Tier 3 quine target and the Kleene fixed-point route. -/
theorem lambda_backend_finishes_tier3
    (backend : LambdaQuotationBackend) :
    LambdaHistoryFixedPointExists ∧ HistoryEqualityFixedPointExists ∧
      KleeneFixedPointExists := by
  exact ⟨backend.toHistoryBackend.to_historyFixedPointExists,
    backend.to_historyEqualityFixedPointExists,
    backend.to_kleeneFixedPointExists⟩

end SSBX.Foundation.Wen.WenyanLambdaRoute
