/-
# Wen.RKernel.LispMetaInterp -- bridge to restored meta-interpreter frontier

This module connects compiled Lisp fragments to the existing restored
meta-interpreter contract.  It does not discharge the R4-carry semantic loop
obligations, and it does not claim full arbitrary Lisp self-hosting.
-/

import SSBX.Foundation.Wen.MetaInterp.UniversalRestorePlan
import SSBX.Foundation.Wen.RKernel.LispCompile

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.UniversalRestorePlan

/--
If the restored meta-interpreter loop obligations are supplied, any supported
compiled Lisp fragment can be fed to the restored META program as its `YiInstr`
program.
-/
theorem compiledExpr_to_restored_meta_frontier
    (O : RestoredSemanticLoopObligations)
    (h : Hexagram)
    (expr : Expr)
    (result : CompileResult expr)
    (n : Nat) :
    let P := result.prog
    let simResult := (YiState.init h P).runFuel n
    let metaResult := (restoredMetaStart h P).runFuel (restoredExactMetaFuel n)
    metaResult.history = encMetaHistory h simResult ∧
      metaResult.halted = simResult.halted :=
  restoredMetaInterpProg_simulates_from_loop O h result.prog n

theorem compiledExpr_lisp_eval_frontier
    (expr : Expr)
    (result : CompileResult expr) :
    evalFuel result.fuel [] expr = some result.value :=
  result.eval_ok

theorem lisp_meta_interp_summary :
    (RestoredSemanticLoopObligations →
      ∀ h expr (result : CompileResult expr) n,
        let P := result.prog
        let simResult := (YiState.init h P).runFuel n
        let metaResult := (restoredMetaStart h P).runFuel (restoredExactMetaFuel n)
        metaResult.history = encMetaHistory h simResult ∧
          metaResult.halted = simResult.halted)
    ∧ (∀ expr (result : CompileResult expr),
        evalFuel result.fuel [] expr = some result.value) :=
  ⟨compiledExpr_to_restored_meta_frontier, compiledExpr_lisp_eval_frontier⟩

end SSBX.Foundation.Wen.RKernel
