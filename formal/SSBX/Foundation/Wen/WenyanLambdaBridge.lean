import SSBX.Foundation.Jian.JianSTLC
import SSBX.Foundation.Wen.WenyanLambdaRoute
import SSBX.Foundation.Wen.WenyanQuineWitness

/-!
# WenyanLambdaBridge

The project already contains an untyped lambda calculus (`JianSTLC.Lam`) with
substitution and β-simulation into the Wen syntax layer.  This file connects
that existing calculus to the Tier 3 quine route:

* quote Yi instructions/programs as lambda data;
* restate the existing β-simulation theorem at the quine-route boundary;
* state the compiler/self-application backends for `JianSTLC.Lam`;
* prove that such backends instantiate the Tier 3 route interfaces.

No universal interpreter is claimed here.  This is the next engineering boundary:
implement the compiler fields for the existing lambda calculus.
-/

namespace SSBX.Foundation.Wen.WenyanLambdaBridge

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanQuineSpec
open SSBX.Foundation.Wen.WenyanQuineKleene
open SSBX.Foundation.Wen.WenyanLambdaRoute

namespace LamRoute

abbrev Lam := SSBX.Foundation.Jian.JianSTLC.Lam

def sym (s : String) : Lam := SSBX.Foundation.Jian.JianSTLC.Lam.var s

def app (f x : Lam) : Lam := SSBX.Foundation.Jian.JianSTLC.Lam.app f x

def app2 (f x y : Lam) : Lam := app (app f x) y
def app3 (f x y z : Lam) : Lam := app (app2 f x y) z
def app4 (f w x y z : Lam) : Lam := app (app3 f w x y) z

def quoteNat (n : Nat) : Lam :=
  app (sym "nat") (sym (toString n))

def quoteFin6 (i : Fin 6) : Lam := quoteNat i.val

def quoteShi (s : Shi) : Lam :=
  match s with
  | Shi.dao => sym "shi.dao"
  | Shi.ji => sym "shi.ji"
  | Shi.jin => sym "shi.jin"
  | Shi.wei => sym "shi.wei"

def quoteCell (c : Cell256) : Lam :=
  app2 (sym "cell") (quoteNat (cellToIdx c).val) (quoteShi c.2)

/-- Quote a Yi instruction as lambda data.  The encoding is intentionally
structural and constructor-tagged, not executable by itself. -/
def quoteInstr : YiInstr → Lam
  | .nop => sym "YiInstr.nop"
  | .setShi s => app (sym "YiInstr.setShi") (quoteShi s)
  | .flipYao i => app (sym "YiInstr.flipYao") (quoteFin6 i)
  | .hu => sym "YiInstr.hu"
  | .cuo => sym "YiInstr.cuo"
  | .zong => sym "YiInstr.zong"
  | .branchYaoEq i j target =>
      app3 (sym "YiInstr.branchYaoEq") (quoteFin6 i) (quoteFin6 j) (quoteNat target)
  | .branchShiEq s target =>
      app2 (sym "YiInstr.branchShiEq") (quoteShi s) (quoteNat target)
  | .jump target => app (sym "YiInstr.jump") (quoteNat target)
  | .push => sym "YiInstr.push"
  | .pop => sym "YiInstr.pop"
  | .halt => sym "YiInstr.halt"

def quoteList : List Lam → Lam
  | [] => sym "List.nil"
  | x :: xs => app2 (sym "List.cons") x (quoteList xs)

def quoteProg (p : List YiInstr) : Lam :=
  quoteList (p.map quoteInstr)

theorem quoteProg_nil :
    quoteProg [] = sym "List.nil" := rfl

theorem quoteProg_cons (i : YiInstr) (p : List YiInstr) :
    quoteProg (i :: p) = app2 (sym "List.cons") (quoteInstr i) (quoteProg p) := rfl

theorem quoteInstr_push_ne_setShi_jin :
    quoteInstr YiInstr.push ≠ quoteInstr (YiInstr.setShi Shi.jin) := by
  native_decide

theorem quoteProg_push_ne_setShi_push :
    quoteProg [YiInstr.push] ≠ quoteProg [YiInstr.setShi Shi.jin, YiInstr.push] := by
  native_decide

/-- The existing lambda calculus already has β-simulation into the Wen syntax
layer.  The missing part for Tier 3 is compilation from these lambda terms down
to executable `YiInstr`, not the lambda calculus itself. -/
theorem beta_step_simulates_wen {t u : Lam}
    (h : SSBX.Foundation.Jian.JianSTLC.Lam.Beta t u) :
    SSBX.Foundation.Jian.JianSTLC.Step.star
      (SSBX.Foundation.Jian.JianSTLC.enc t)
      (SSBX.Foundation.Jian.JianSTLC.enc u) :=
  SSBX.Foundation.Jian.JianSTLC.simulation h

/-- The history-only backend contract when using the existing `JianSTLC.Lam`
as the lambda calculus.  Filling these fields is enough for the raw Tier 3
history quine target. -/
structure JianLambdaHistoryBackend where
  compileLam : Lam → List YiInstr
  selfApplyLam : List YiInstr → Lam
  initOf : List YiInstr → YiState
  fuelOf : List YiInstr → Nat
  init_runs_compiled :
    ∀ F : List YiInstr, (initOf F).prog = compileLam (selfApplyLam F)
  historySpec :
    ∀ F : List YiInstr,
      QuineRunSpec (compileLam (selfApplyLam F)) (initOf F) (fuelOf F)

namespace JianLambdaHistoryBackend

def toLambdaHistoryBackend (backend : JianLambdaHistoryBackend) :
    LambdaHistoryBackend :=
  { Term := Lam
  , compile := backend.compileLam
  , selfApply := backend.selfApplyLam
  , initOf := backend.initOf
  , fuelOf := backend.fuelOf
  , init_runs_compiled := backend.init_runs_compiled
  , historySpec := backend.historySpec }

theorem finishes_tier3 (backend : JianLambdaHistoryBackend) :
    LambdaHistoryFixedPointExists :=
  lambda_history_backend_finishes_tier3 backend.toLambdaHistoryBackend

theorem gives_tier3_quine (backend : JianLambdaHistoryBackend) :
    Tier3QuineExists :=
  lambda_history_backend_gives_tier3_quine backend.toLambdaHistoryBackend

end JianLambdaHistoryBackend

/-- The stronger concrete backend contract when using the existing
`JianSTLC.Lam` as the lambda calculus.  Filling these fields gives the raw
Tier 3 target and the Kleene halting fixed-point route. -/
structure JianLambdaQuotationBackend where
  compileLam : Lam → List YiInstr
  selfApplyLam : List YiInstr → Lam
  initOf : List YiInstr → YiState
  fuelOf : List YiInstr → Nat
  init_runs_compiled :
    ∀ F : List YiInstr, (initOf F).prog = compileLam (selfApplyLam F)
  haltingSpec :
    ∀ F : List YiInstr, SelfApplicationHaltingSpec F (compileLam (selfApplyLam F))
  historySpec :
    ∀ F : List YiInstr,
      QuineRunSpec (compileLam (selfApplyLam F)) (initOf F) (fuelOf F)

namespace JianLambdaQuotationBackend

def toHistoryBackend (backend : JianLambdaQuotationBackend) :
    JianLambdaHistoryBackend :=
  { compileLam := backend.compileLam
  , selfApplyLam := backend.selfApplyLam
  , initOf := backend.initOf
  , fuelOf := backend.fuelOf
  , init_runs_compiled := backend.init_runs_compiled
  , historySpec := backend.historySpec }

def toLambdaQuotationBackend (backend : JianLambdaQuotationBackend) :
    LambdaQuotationBackend :=
  { Term := Lam
  , compile := backend.compileLam
  , selfApply := backend.selfApplyLam
  , initOf := backend.initOf
  , fuelOf := backend.fuelOf
  , init_runs_compiled := backend.init_runs_compiled
  , haltingSpec := backend.haltingSpec
  , historySpec := backend.historySpec }

theorem finishes_tier3 (backend : JianLambdaQuotationBackend) :
    LambdaHistoryFixedPointExists ∧ HistoryEqualityFixedPointExists ∧
      SSBX.Foundation.Bagua.KleeneInternal.KleeneFixedPointExists :=
  lambda_backend_finishes_tier3 backend.toLambdaQuotationBackend

theorem gives_tier3_quine (backend : JianLambdaQuotationBackend) :
    Tier3QuineExists :=
  lambda_history_backend_gives_tier3_quine
    backend.toHistoryBackend.toLambdaHistoryBackend

end JianLambdaQuotationBackend

/-! ## Constant-compile JianLambdaHistoryBackend instance

  The existing 16-instr push-only Tier 3 witness (`pushQuineSource 16` /
  `wenyan_tier3_quine_complete`) already meets the raw history-quine
  spec: starting from `pushQuineInit 16`, after `pushQuineFuel 16` steps,
  history equals `ProgEnc.encProg (pushQuineSource 16)`.

  We can package that witness as a **constant** `JianLambdaHistoryBackend`:
  `compileLam` and `selfApplyLam` ignore their `F` argument, so the
  resulting quine source does not vary with the parameter program. This
  closes the backend interface (the `JianLambdaHistoryBackend` structure
  is non-empty) and via `lambda_history_backend_finishes_tier3` discharges
  `Tier3QuineExists` and `LambdaHistoryFixedPointExists` through the
  abstract route.

  This **does not** count as a "meaningful lambda compiler". A real
  compileLam — one that produces a *different* concrete YiInstr program
  per Lam input — remains the substantive engineering target. The
  artifact below is an existence proof at the route-interface level: it
  shows the backend type is inhabited, freeing downstream theorems to be
  stated against the abstract backend rather than ad hoc on the concrete
  push quine.

  For the stronger `JianLambdaQuotationBackend` (which carries the
  Kleene-halting `haltingSpec`), no constant instance is given here:
  `SelfApplicationHaltingSpec F D` says `Halts D h ↔ HaltsWith F h
  (ProgEnc.encProg D)`, which depends nontrivially on `F` and cannot be
  satisfied by a constant `D`. The quotation backend is the real
  Kleene-bridging target. -/

open SSBX.Foundation.Wen.WenyanQuineWitness in
def constJianLambdaHistoryBackend : JianLambdaHistoryBackend where
  compileLam   := fun _ => pushQuineSource 16
  selfApplyLam := fun _ => sym "_constLambdaQuine"
  initOf       := fun _ => pushQuineInit 16
  fuelOf       := fun _ => pushQuineFuel 16
  init_runs_compiled := fun _ => rfl
  historySpec  := fun _ => wenyan_tier3_quine_complete

/-- The constant lambda backend instantiates the raw Tier 3 quine route. -/
theorem constJianLambdaHistoryBackend_gives_tier3_quine : Tier3QuineExists :=
  constJianLambdaHistoryBackend.gives_tier3_quine

theorem constJianLambdaHistoryBackend_finishes_tier3 :
    LambdaHistoryFixedPointExists :=
  constJianLambdaHistoryBackend.finishes_tier3

end LamRoute

end SSBX.Foundation.Wen.WenyanLambdaBridge
