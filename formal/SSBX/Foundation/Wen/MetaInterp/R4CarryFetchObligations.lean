/-
# R4CarryFetchObligations -- carry-native fetch frontier

This sidecar is the R4-squared replacement for the old saved-current-cell fetch
frontier.  A future concrete fetch walker must decode the opcode tag into
`META.cur` while carrying the original current cell as `R4 x R4` proof/control
data.  The bridge then routes through the existing 12-opcode dispatch tree and
recovers the existing `BlockPre` contract via the carry restore fragment.

This phase is structural only.  It does not embed carry rows into the global
program and therefore does not claim full `BlockPost` or universal-compose
execution.
-/
import SSBX.Foundation.Wen.MetaInterp.R4CarryBridge

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryFetchObligations

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
open SSBX.Foundation.Wen.MetaInterp.R4Carry
open SSBX.Foundation.Wen.MetaInterp.R4CarryRestore
open SSBX.Foundation.Wen.MetaInterp.R4CarryBridge
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

/-! ## Carry-native fetch obligation -/

/-- Minimal running-arm evidence expected from the future real carry-aware fetch
walker.  The saved current is carried structurally as `R4 x R4`; canonical
history remains unprefixed. -/
structure RestoredR4CarryFetchObligations : Prop where
  running :
    ∀ regHex sim instr,
      sim.halted = false →
      sim.prog[sim.pc]? = some instr →
        ∃ fetchFuel,
          R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset
            (carryOfCell sim.cur)
            ((Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
              fetchFuel)

theorem restoredR4CarryFetch_dispatch_tag_at_fuel
    (O : RestoredR4CarryFetchObligations)
    (regHex : Hexagram) (sim : YiState) (instr : YiInstr)
    (h_alive : sim.halted = false)
    (h_get : sim.prog[sim.pc]? = some instr) :
    ∃ fetchFuel,
      let μ :=
        (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
          fetchFuel
      μ.cur = dispatchTagOfInstr instr := by
  obtain ⟨fetchFuel, h_fetch⟩ := O.running regHex sim instr h_alive h_get
  refine ⟨fetchFuel, ?_⟩
  exact
    r4CarryFetchOutcome_cur_eq_dispatchTag
      regHex sim
      ((Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
        fetchFuel)
      instr (carryOfCell sim.cur) h_fetch h_get

/-- Carry-aware fetch plus existing dispatch preserves the canonical dispatch
state while threading the R4-squared carry unchanged. -/
theorem restoredR4CarryFetch_dispatch_routes_at_fuel
    (O : RestoredR4CarryFetchObligations)
    (regHex : Hexagram) (sim : YiState) (instr : YiInstr)
    (h_alive : sim.halted = false)
    (h_get : sim.prog[sim.pc]? = some instr) :
    ∃ fetchFuel,
      let μ :=
        (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
          fetchFuel
      let μ' := μ.runFuel (dispatchFuelOfInstr instr)
      μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
        ∧ μ'.cur = dispatchTagOfInstr instr
        ∧ μ'.history = encMetaHistory regHex sim
        ∧ μ'.prog = restoredMetaInterpProg
        ∧ μ'.halted = false
        ∧ carryOfCell sim.cur = carryOfCell sim.cur := by
  obtain ⟨fetchFuel, h_fetch⟩ := O.running regHex sim instr h_alive h_get
  refine ⟨fetchFuel, ?_⟩
  exact
    r4CarryFetch_dispatch_routes_to_restore
      regHex sim
      ((Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
        fetchFuel)
      instr (carryOfCell sim.cur) h_fetch h_get

/-- Structural composition frontier: after carry-aware fetch and existing
dispatch, the selected standalone carry restore fragment yields the existing
`BlockPre` contract.  The fragment is not embedded into the global program in
this phase, so this is intentionally not a full runFuel path theorem. -/
theorem restoredR4CarryFetch_dispatch_restore_yields_BlockPre
    (O : RestoredR4CarryFetchObligations)
    (regHex : Hexagram) (sim : YiState) (instr : YiInstr) (bodyOffset : Nat)
    (h_alive : sim.halted = false)
    (h_get : sim.prog[sim.pc]? = some instr) :
    ∃ fetchFuel,
      let μ :=
        (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
          fetchFuel
      let μ' := μ.runFuel (dispatchFuelOfInstr instr)
      μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
        ∧ μ'.cur = dispatchTagOfInstr instr
        ∧ μ'.history = encMetaHistory regHex sim
        ∧ μ'.prog = restoredMetaInterpProg
        ∧ μ'.halted = false
        ∧ BlockPre regHex sim bodyOffset
            (restoreCarryProg8 (dispatchTagOfInstr instr) (carryOfCell sim.cur) bodyOffset)
            (({ cur := dispatchTagOfInstr instr
              , history := encMetaHistory regHex sim
              , pc := 0
              , prog :=
                  restoreCarryProg8 (dispatchTagOfInstr instr) (carryOfCell sim.cur)
                    bodyOffset
              , halted := false } : YiState).runFuel
                (restoreCarryProg8 (dispatchTagOfInstr instr) (carryOfCell sim.cur)
                  bodyOffset).length) := by
  obtain ⟨fetchFuel, h_fetch⟩ := O.running regHex sim instr h_alive h_get
  refine ⟨fetchFuel, ?_⟩
  exact
    r4CarryFetch_dispatch_restore_yields_BlockPre
      regHex sim
      ((Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
        fetchFuel)
      instr (carryOfCell sim.cur) bodyOffset h_fetch h_get

theorem restoredR4CarryFetch_nop_restore_yields_BlockPre
    (O : RestoredR4CarryFetchObligations)
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_nop : sim.prog[sim.pc]? = some .nop) :
    ∃ fetchFuel,
      let μ :=
        (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
          fetchFuel
      let μ' := μ.runFuel (dispatchFuelOfInstr .nop)
      μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets .nop
        ∧ μ'.cur = dispatchTagOfInstr .nop
        ∧ μ'.history = encMetaHistory regHex sim
        ∧ μ'.prog = restoredMetaInterpProg
        ∧ μ'.halted = false
        ∧ BlockPre regHex sim (bodyOffset block_nop_offset)
            (restoreCarryProg8 (dispatchTagOfInstr .nop) (carryOfCell sim.cur)
              (bodyOffset block_nop_offset))
            (({ cur := dispatchTagOfInstr .nop
              , history := encMetaHistory regHex sim
              , pc := 0
              , prog :=
                  restoreCarryProg8 (dispatchTagOfInstr .nop) (carryOfCell sim.cur)
                    (bodyOffset block_nop_offset)
              , halted := false } : YiState).runFuel
                (restoreCarryProg8 (dispatchTagOfInstr .nop) (carryOfCell sim.cur)
                  (bodyOffset block_nop_offset)).length) := by
  exact
    restoredR4CarryFetch_dispatch_restore_yields_BlockPre
      O regHex sim .nop (bodyOffset block_nop_offset) h_alive h_nop

/-! ## Public summary -/

theorem r4_carry_fetch_obligation_frontier_summary :
    (RestoredR4CarryFetchObligations →
      ∀ regHex sim instr,
        sim.halted = false →
        sim.prog[sim.pc]? = some instr →
          ∃ fetchFuel,
            let μ :=
              (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
                fetchFuel
            μ.cur = dispatchTagOfInstr instr)
    ∧ (RestoredR4CarryFetchObligations →
      ∀ regHex sim instr,
        sim.halted = false →
        sim.prog[sim.pc]? = some instr →
          ∃ fetchFuel,
            let μ :=
              (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
                fetchFuel
            let μ' := μ.runFuel (dispatchFuelOfInstr instr)
            μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
              ∧ μ'.cur = dispatchTagOfInstr instr
              ∧ μ'.history = encMetaHistory regHex sim
              ∧ μ'.prog = restoredMetaInterpProg
              ∧ μ'.halted = false
              ∧ carryOfCell sim.cur = carryOfCell sim.cur)
    ∧ (RestoredR4CarryFetchObligations →
      ∀ regHex sim,
        sim.halted = false →
        sim.prog[sim.pc]? = some .nop →
          ∃ fetchFuel,
            let μ :=
              (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
                fetchFuel
            let μ' := μ.runFuel (dispatchFuelOfInstr .nop)
            μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets .nop
              ∧ μ'.cur = dispatchTagOfInstr .nop
              ∧ μ'.history = encMetaHistory regHex sim
              ∧ μ'.prog = restoredMetaInterpProg
              ∧ μ'.halted = false
              ∧ BlockPre regHex sim (bodyOffset block_nop_offset)
                  (restoreCarryProg8 (dispatchTagOfInstr .nop) (carryOfCell sim.cur)
                    (bodyOffset block_nop_offset))
                  (({ cur := dispatchTagOfInstr .nop
                    , history := encMetaHistory regHex sim
                    , pc := 0
                    , prog :=
                        restoreCarryProg8 (dispatchTagOfInstr .nop) (carryOfCell sim.cur)
                          (bodyOffset block_nop_offset)
                    , halted := false } : YiState).runFuel
                      (restoreCarryProg8 (dispatchTagOfInstr .nop) (carryOfCell sim.cur)
                        (bodyOffset block_nop_offset)).length)) := by
  exact
    ⟨ restoredR4CarryFetch_dispatch_tag_at_fuel
    , restoredR4CarryFetch_dispatch_routes_at_fuel
    , restoredR4CarryFetch_nop_restore_yields_BlockPre
    ⟩

end SSBX.Foundation.Wen.MetaInterp.R4CarryFetchObligations
