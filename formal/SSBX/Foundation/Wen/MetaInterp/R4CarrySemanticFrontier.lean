/-
# R4CarrySemanticFrontier -- final contract stack for universal compose

This module is the executable frontier for the R4-squared carry roadmap.  It
does not prove the concrete restored interpreter yet; instead it states the
minimal contracts that remain after the structural carry, dispatch, operand
route, and exact-block layers have been separated.

The important theorem is one-way and honest: if the concrete implementation
supplies the frontier contracts, then the existing restored universal-compose
surface follows.
-/
import SSBX.Foundation.Wen.MetaInterp.R4CarryParamDecodeObligations
import SSBX.Foundation.Wen.MetaInterp.R4CarryBlockPrePost
import SSBX.Foundation.Wen.MetaInterp.R4CarryUniversalPlan

namespace SSBX.Foundation.Wen.MetaInterp.R4CarrySemanticFrontier

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
open SSBX.Foundation.Wen.MetaInterp.R4Carry
open SSBX.Foundation.Wen.MetaInterp.R4CarryRestore
open SSBX.Foundation.Wen.MetaInterp.R4CarryBridge
open SSBX.Foundation.Wen.MetaInterp.R4CarryFetchObligations
open SSBX.Foundation.Wen.MetaInterp.R4CarryAssemblyPlan
open SSBX.Foundation.Wen.MetaInterp.R4CarryBlockContracts
open SSBX.Foundation.Wen.MetaInterp.R4CarryBlockPrePost
open SSBX.Foundation.Wen.MetaInterp.R4CarryParamDecodeObligations
open SSBX.Foundation.Wen.MetaInterp.R4CarryUniversalPlan
open SSBX.Foundation.Wen.MetaInterp.UniversalRestorePlan

/-! ## Concrete remaining contracts -/

/-- The restored program contains the generated carry-row restore region at the
selected offsets.  This is stronger than the standalone row proof in
`R4CarryAssemblyPlan` because it speaks about `restoredMetaInterpProg`. -/
structure EmbeddedCarryRowsContract
    (restoreOffsetOf : RestoreOffsetOf)
    (bodyOffsetOf : BodyOffsetOf) : Prop where
  rowSegment :
    ∀ row j,
      j < (carryRowProgram bodyOffsetOf row).length →
        restoredMetaInterpProg[restoreOffsetOf row.1 row.2 + j]? =
          (carryRowProgram bodyOffsetOf row)[j]?
  rowLength :
    ∀ row, (carryRowProgram bodyOffsetOf row).length = 8

/-- One exact restored iteration, proved by composing the concrete fetch walker,
dispatch, embedded carry restore, parameter route, and exact block body. -/
structure RestoredCarryIterationContract
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (carryBodyOffsetOf : CarryBodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf)
    (bodyFuelOf : BodyFuelOf)
    (carryBodyFuelOf : CarryBodyFuelOf) : Prop where
  steadyState :
    ∀ regHex sim,
      sim.halted = false →
        (restoredLoopStateOf regHex sim).runFuel restoredLoopFuelPerIter =
          restoredLoopStateOf regHex sim.step
  firstState :
    ∀ regHex sim,
      sim.halted = false →
        (metaStateOf regHex sim restoredMetaInterpProg outerLoopOffset).runFuel
          restoredLoopFuelPerIter =
          restoredLoopStateOf regHex sim.step

/-- Full frontier after structural R4 carry has been chosen.

`exactStep` is the composed state-equality result that later files prove from
the contracts above.  Keeping it explicit prevents this frontier from claiming
that the current placeholder blocks already implement encoded-history mutation. -/
structure R4CarrySemanticFrontierContracts
    (restoreOffsetOf : RestoreOffsetOf)
    (paramDecodeOffsetOf : ParamDecodeOffsetOf)
    (bodyOffsetOf : BodyOffsetOf)
    (carryBodyOffsetOf : CarryBodyOffsetOf)
    (paramDecodeFuelOf : ParamDecodeFuelOf)
    (bodyFuelOf : BodyFuelOf)
    (carryBodyFuelOf : CarryBodyFuelOf) : Prop where
  fetch :
    RestoredR4CarryFetchObligations
  bridge :
    R4CarryBridgeObligations paramDecodeOffsetOf
  rows :
    EmbeddedCarryRowsContract restoreOffsetOf paramDecodeOffsetOf
  params :
    R4CarryParamDecodeContracts paramDecodeOffsetOf bodyOffsetOf
      paramDecodeFuelOf
  blocks :
    R4CarryExactBlockContracts bodyOffsetOf bodyFuelOf
  carryBlocks :
    R4CarryIndexedBlockContracts carryBodyOffsetOf carryBodyFuelOf
  iteration :
    RestoredCarryIterationContract paramDecodeOffsetOf bodyOffsetOf
      carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf carryBodyFuelOf
  haltedPadding :
    ∀ regHex sim extraFuel,
      sim.halted = true →
        let μ := metaStateOf regHex sim restoredMetaInterpProg outerLoopOffset
        let μ' := μ.runFuel (restoredLoopFuelPerIter + extraFuel)
        μ'.history = encMetaHistory regHex sim ∧ μ'.halted = true

def R4CarrySemanticFrontierContracts.toExactStep
    {restoreOffsetOf : RestoreOffsetOf}
    {paramDecodeOffsetOf : ParamDecodeOffsetOf}
    {bodyOffsetOf : BodyOffsetOf}
    {carryBodyOffsetOf : CarryBodyOffsetOf}
    {paramDecodeFuelOf : ParamDecodeFuelOf}
    {bodyFuelOf : BodyFuelOf}
    {carryBodyFuelOf : CarryBodyFuelOf}
    (F :
      R4CarrySemanticFrontierContracts restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf
        carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf carryBodyFuelOf) :
    R4CarryExactStepObligations where
  firstState := F.iteration.firstState
  steadyState := F.iteration.steadyState
  haltedPadding := F.haltedPadding

def R4CarrySemanticFrontierContracts.toLoop
    {restoreOffsetOf : RestoreOffsetOf}
    {paramDecodeOffsetOf : ParamDecodeOffsetOf}
    {bodyOffsetOf : BodyOffsetOf}
    {carryBodyOffsetOf : CarryBodyOffsetOf}
    {paramDecodeFuelOf : ParamDecodeFuelOf}
    {bodyFuelOf : BodyFuelOf}
    {carryBodyFuelOf : CarryBodyFuelOf}
    (F :
      R4CarrySemanticFrontierContracts restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf
        carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf carryBodyFuelOf) :
    RestoredSemanticLoopObligations :=
  F.toExactStep.toLoop

def R4CarrySemanticFrontierContracts.toCompose
    {restoreOffsetOf : RestoreOffsetOf}
    {paramDecodeOffsetOf : ParamDecodeOffsetOf}
    {bodyOffsetOf : BodyOffsetOf}
    {carryBodyOffsetOf : CarryBodyOffsetOf}
    {paramDecodeFuelOf : ParamDecodeFuelOf}
    {bodyFuelOf : BodyFuelOf}
    {carryBodyFuelOf : CarryBodyFuelOf}
    (F :
      R4CarrySemanticFrontierContracts restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf
        carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf carryBodyFuelOf) :
    RestoredSemanticComposeObligations :=
  F.toExactStep.toCompose

theorem r4_carry_semantic_frontier_summary :
    ∀ restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf carryBodyOffsetOf
      paramDecodeFuelOf bodyFuelOf carryBodyFuelOf,
      R4CarrySemanticFrontierContracts restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf
        carryBodyOffsetOf paramDecodeFuelOf bodyFuelOf carryBodyFuelOf →
        RestoredSemanticLoopObligations ∧
        RestoredSemanticComposeObligations ∧
        (∀ regHex P n,
          let simResult := (YiState.init regHex P).runFuel n
          let metaResult :=
            (restoredMetaStart regHex P).runFuel (restoredExactMetaFuel n)
          metaResult.history = encMetaHistory regHex simResult ∧
            metaResult.halted = simResult.halted) := by
  intro restoreOffsetOf paramDecodeOffsetOf bodyOffsetOf carryBodyOffsetOf
    paramDecodeFuelOf bodyFuelOf carryBodyFuelOf F
  exact
    ⟨ F.toLoop
    , F.toCompose
    , restoredMetaInterpProg_simulates_from_loop F.toLoop
    ⟩

end SSBX.Foundation.Wen.MetaInterp.R4CarrySemanticFrontier
