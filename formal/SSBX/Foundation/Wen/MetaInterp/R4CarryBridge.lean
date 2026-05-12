/-
# R4CarryBridge -- structural bridge from R4-squared carry fetch to dispatch

This is the preferred structural saved-current bridge for the meta-interpreter.
It connects the R4 x R4 carry contract to the existing 12-opcode dispatch
router, without generating a concrete carry-row layout and without assigning
new word choices above R4.

The old saved-cell/pop path remains as a transitional witness.  This module is
only the contract bridge: real fetch walking, embedded carry-row assembly, and
arbitrary-current block exactness remain separate phases.
-/
import SSBX.Foundation.Wen.MetaInterp.R4CarryRestore
import SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryBridge

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
open SSBX.Foundation.Wen.MetaInterp.R4Carry
open SSBX.Foundation.Wen.MetaInterp.R4CarryRestore
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

/-! ## Fetch outcome to dispatch tag -/

/-- A carry-aware fetch outcome exposes exactly the instruction dispatch tag.
The carried current remains outside `META.history`; it is proof/control data. -/
theorem r4CarryFetchOutcome_cur_eq_dispatchTag
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr) (carry : SavedCurrentCarry)
    (h_fetch :
      R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset carry μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    μ.cur = dispatchTagOfInstr instr := by
  have h_mem := h_fetch.cur_is_tag instr h_get
  rw [encInstr_head?_eq_dispatchTagOfInstr] at h_mem
  simpa using h_mem.symm

theorem r4CarryFetchOutcome_carry_eq
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (carry : SavedCurrentCarry)
    (h_fetch :
      R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset carry μ) :
    carry = carryOfCell sim.cur :=
  h_fetch.carry_eq

/-- Field equality form for the carry-aware dispatch entry. -/
theorem r4CarryFetchOutcome_eq_dispatchEntry
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr) (carry : SavedCurrentCarry)
    (h_fetch :
      R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset carry μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    μ =
      { cur := dispatchTagOfInstr instr
      , history := encMetaHistory regHex sim
      , pc := dispatchOffset
      , prog := restoredMetaInterpProg
      , halted := false } := by
  have h_cur :=
    r4CarryFetchOutcome_cur_eq_dispatchTag regHex sim μ instr carry h_fetch h_get
  cases μ with
  | mk cur history pc prog halted =>
      have h_history := h_fetch.history
      have h_pc := h_fetch.pc
      have h_prog := h_fetch.prog
      have h_halted := h_fetch.halted
      simp at h_cur h_history h_pc h_prog h_halted
      subst cur
      subst history
      subst pc
      subst prog
      subst halted
      rfl

/-! ## Carry-aware dispatch route -/

/-- Existing 12-opcode dispatch routes the tag while preserving canonical
history.  The R4 x R4 carry is unchanged as proof/control data. -/
theorem r4CarryFetch_dispatch_routes_to_restore
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr) (carry : SavedCurrentCarry)
    (h_fetch :
      R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset carry μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    let μ' := μ.runFuel (dispatchFuelOfInstr instr)
    μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
      ∧ μ'.cur = dispatchTagOfInstr instr
      ∧ μ'.history = encMetaHistory regHex sim
      ∧ μ'.prog = restoredMetaInterpProg
      ∧ μ'.halted = false
      ∧ carry = carryOfCell sim.cur := by
  have h_entry :=
    r4CarryFetchOutcome_eq_dispatchEntry regHex sim μ instr carry h_fetch h_get
  rw [h_entry]
  have h_route :=
    restoredMetaInterpProg_dispatch_routes_instr_at_fuel
      (encMetaHistory regHex sim) instr
  exact
    ⟨ h_route.1
    , h_route.2.1
    , h_route.2.2.1
    , h_route.2.2.2.1
    , h_route.2.2.2.2
    , h_fetch.carry_eq
    ⟩

/-- Dispatch followed by the selected carry-restore fragment yields the existing
`BlockPre` contract.  The restore fragment is not embedded into the global
program in this phase; `bodyOffset` stays explicit. -/
theorem r4CarryFetch_dispatch_restore_yields_BlockPre
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr) (carry : SavedCurrentCarry) (bodyOffset : Nat)
    (h_fetch :
      R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset carry μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    let μ' := μ.runFuel (dispatchFuelOfInstr instr)
    μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
      ∧ μ'.cur = dispatchTagOfInstr instr
      ∧ μ'.history = encMetaHistory regHex sim
      ∧ μ'.prog = restoredMetaInterpProg
      ∧ μ'.halted = false
      ∧ BlockPre regHex sim bodyOffset
          (restoreCarryProg8 (dispatchTagOfInstr instr) carry bodyOffset)
          (({ cur := dispatchTagOfInstr instr
            , history := encMetaHistory regHex sim
            , pc := 0
            , prog := restoreCarryProg8 (dispatchTagOfInstr instr) carry bodyOffset
            , halted := false } : YiState).runFuel
              (restoreCarryProg8 (dispatchTagOfInstr instr) carry bodyOffset).length) := by
  have h_route :=
    r4CarryFetch_dispatch_routes_to_restore
      regHex sim μ instr carry h_fetch h_get
  exact
    ⟨ h_route.1
    , h_route.2.1
    , h_route.2.2.1
    , h_route.2.2.2.1
    , h_route.2.2.2.2.1
    , restoreCarryProg8_yields_BlockPre
        regHex sim (dispatchTagOfInstr instr) carry bodyOffset h_fetch.carry_eq
    ⟩

/-! ## Bridge obligation surface -/

/-- Structural bridge obligation for future carry-row assembly.

`bodyOffsetOf` is deliberately external: this phase does not choose the final
embedded layout or any word table above R4. -/
structure R4CarryBridgeObligations (bodyOffsetOf : YiInstr → Nat) : Prop where
  running :
    ∀ regHex sim μ instr carry,
      R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset carry μ →
      sim.prog[sim.pc]? = some instr →
        let μ' := μ.runFuel (dispatchFuelOfInstr instr)
        μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
          ∧ μ'.cur = dispatchTagOfInstr instr
          ∧ μ'.history = encMetaHistory regHex sim
          ∧ μ'.prog = restoredMetaInterpProg
          ∧ μ'.halted = false
          ∧ BlockPre regHex sim (bodyOffsetOf instr)
              (restoreCarryProg8 (dispatchTagOfInstr instr) carry (bodyOffsetOf instr))
              (({ cur := dispatchTagOfInstr instr
                , history := encMetaHistory regHex sim
                , pc := 0
                , prog :=
                    restoreCarryProg8 (dispatchTagOfInstr instr) carry
                      (bodyOffsetOf instr)
                , halted := false } : YiState).runFuel
                  (restoreCarryProg8 (dispatchTagOfInstr instr) carry
                    (bodyOffsetOf instr)).length)

theorem r4_carry_bridge_obligations (bodyOffsetOf : YiInstr → Nat) :
    R4CarryBridgeObligations bodyOffsetOf where
  running := by
    intro regHex sim μ instr carry h_fetch h_get
    exact
      r4CarryFetch_dispatch_restore_yields_BlockPre
        regHex sim μ instr carry (bodyOffsetOf instr) h_fetch h_get

/-! ## Public summary -/

theorem r4_carry_bridge_summary :
    (∀ regHex sim μ instr carry,
      R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset carry μ →
      sim.prog[sim.pc]? = some instr →
        μ.cur = dispatchTagOfInstr instr)
    ∧ (∀ regHex sim μ instr carry,
      R4CarryFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset carry μ →
      sim.prog[sim.pc]? = some instr →
        let μ' := μ.runFuel (dispatchFuelOfInstr instr)
        μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
          ∧ μ'.cur = dispatchTagOfInstr instr
          ∧ μ'.history = encMetaHistory regHex sim
          ∧ μ'.prog = restoredMetaInterpProg
          ∧ μ'.halted = false
          ∧ carry = carryOfCell sim.cur)
    ∧ (∀ bodyOffsetOf : YiInstr → Nat,
        R4CarryBridgeObligations bodyOffsetOf) := by
  exact
    ⟨ r4CarryFetchOutcome_cur_eq_dispatchTag
    , r4CarryFetch_dispatch_routes_to_restore
    , r4_carry_bridge_obligations
    ⟩

end SSBX.Foundation.Wen.MetaInterp.R4CarryBridge
