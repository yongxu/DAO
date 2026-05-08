/-
# TargetContract -- exact Lean target before Wenyan witnesses

This module fixes the proof target for the YiInstr/CIC discussion.

It deliberately does not claim a strict equivalence between YiInstr and CIC.
The target is a Lean-checked bridge:

* Lean defines and checks the YiInstr operational semantics.
* Program encodings round-trip under explicit hypotheses.
* Universal interpretation, s-m-n, diagonal compilers, and cuo-restricted
  Church-Turing remain explicit target propositions.
* Wenyan programs are next-phase witnesses for those propositions, not the root
  proof system.
-/
import SSBX.Foundation.Wen.MetaInterp
import SSBX.Foundation.Wen.WenyanFramedProg
import SSBX.Foundation.Wen.WenyanQuineKleene

namespace SSBX.Foundation.Wen.MetaInterp.TargetContract

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.GodelLi
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.WenyanSelfInterp

/-! ## Phase order -/

/-- The intended order: first pin down the Lean target, then prove Lean-side
    witnesses, then use Wenyan programs as checked witnesses. -/
inductive ProofPhase : Type
  | leanTarget
  | leanWitnesses
  | wenyanWitness
  deriving Repr, DecidableEq

def proofPhaseRank : ProofPhase → Nat
  | .leanTarget => 0
  | .leanWitnesses => 1
  | .wenyanWitness => 2

theorem lean_target_before_wenyan_witness :
    proofPhaseRank .leanTarget < proofPhaseRank .wenyanWitness := by
  decide

/-! ## Claim status ledger -/

inductive TargetStatus : Type
  | machineChecked
  | target
  | nonGoal
  deriving Repr, DecidableEq

inductive TargetItem : Type
  | yiOperationalSemantics
  | rawProgramEncoding
  | framedProgramEncoding
  | boundedMetaInterpreter
  | fullUniversalInterpreter
  | smnCompiler
  | diagonalCompilers
  | cuoRestrictedChurchTuring
  | wenyanWitness
  | strictYiInstrCICEquivalence
  deriving Repr, DecidableEq

/-- Phase 1 classifies the bridge pieces without pretending they are all done. -/
def targetStatus : TargetItem → TargetStatus
  | .yiOperationalSemantics => .machineChecked
  | .rawProgramEncoding => .machineChecked
  | .framedProgramEncoding => .machineChecked
  | .boundedMetaInterpreter => .target
  | .fullUniversalInterpreter => .target
  | .smnCompiler => .target
  | .diagonalCompilers => .target
  | .cuoRestrictedChurchTuring => .target
  | .wenyanWitness => .target
  | .strictYiInstrCICEquivalence => .nonGoal

theorem strict_yiinstr_cic_equivalence_is_non_goal :
    targetStatus .strictYiInstrCICEquivalence = .nonGoal := rfl

theorem bounded_meta_interpreter_remains_target :
    targetStatus .boundedMetaInterpreter = .target := rfl

theorem full_universal_interpreter_remains_target :
    targetStatus .fullUniversalInterpreter = .target := rfl

/-! ## Already checked anchors -/

/-- Lean-side operational anchor: custom empty input agrees with the ordinary
    YiInstr halting predicate. -/
def LeanChecksYiSemantics : Prop :=
  ∀ (P : List YiInstr) (h : Hexagram), HaltsWith P h [] ↔ Halts P h

theorem lean_checks_yi_semantics : LeanChecksYiSemantics := by
  intro P h
  exact haltsWith_empty P h

/-- Raw `ProgEnc` round-trip: the decoder needs the instruction count and
    per-instruction encodability. -/
def ProgramEncodingRoundTrip : Prop :=
  ∀ P : List YiInstr,
    ProgEnc.AllEncodable P →
      ProgEnc.decInstrs P.length (ProgEnc.encProg P) = some (P, [])

theorem program_encoding_roundtrip : ProgramEncodingRoundTrip := by
  intro P h_enc
  exact progEnc_decodes_self P h_enc

/-- Length-framed program input round-trips under the explicit bounded-length
    and encodability hypotheses. -/
def FramedProgramRoundTrip : Prop :=
  ∀ P : List YiInstr,
    ProgLenBounded P →
      ProgEnc.AllEncodable P →
        SSBX.Foundation.Wen.WenyanFramedProg.decFramedProg
          (SSBX.Foundation.Wen.WenyanFramedProg.encFramedProg P) =
            some (P, [])

theorem framed_program_roundtrip : FramedProgramRoundTrip := by
  intro P h_len h_enc
  exact SSBX.Foundation.Wen.WenyanFramedProg.decFramedProg_encFramedProg_self
    P h_len h_enc

/-! ## Explicit target propositions -/

/-- Full universal-interpreter target from `KleeneInternal`. -/
def UniversalInterpreterTarget : Prop := UniversalInterpExists

/-- Realisable restricted variant: pure YiInstr witnesses only need to cover the
    bounded program class stated in `KleeneInternal`. -/
def BoundedUniversalInterpreterTarget : Prop := UniversalInterpExistsBounded

/-- Current `MetaInterp` construction target: a concrete bounded universal
    interpreter program. -/
def MetaInterpTargetSpec (W : List YiInstr) : Prop :=
  UniversalInterpSpecBounded W

/-- Length-framed engineering target.  This is the parser-friendly lane; it is
    deliberately separate from `KleeneInternal.UniversalInterpSpec`, which still
    uses raw `ProgEnc.encProg` input. -/
def FramedMetaInterpTargetSpec (W : List YiInstr) : Prop :=
  ∀ (P : List YiInstr) (h : Hexagram),
    ProgBounded P →
      ProgEnc.AllEncodable P →
        (Halts P h ↔ HaltsWith W h
          (SSBX.Foundation.Wen.WenyanFramedProg.encFramedProg P))

/-- s-m-n target from `KleeneInternal`. -/
def SmnCompilerTarget : Prop := SmnExists

/-- Fixed-point and Boolean-inverter compiler target. -/
def DiagonalCompilerTarget : Prop := KleeneFromPrimitives

/-- Current Church-Turing target, restricted to cuo-invariant deciders. -/
def CuoRestrictedChurchTuringTarget : Prop := AllDecidersAreYiComputable

/-- A next-phase Wenyan witness is a concrete YiInstr program satisfying the
    universal interpreter spec; Wenyan supplies the witness, Lean checks it. -/
def WenyanUniversalWitnessTarget (W : List YiInstr) : Prop :=
  UniversalInterpSpec W

/-- Bounded version for the current pure-YiInstr engineering route. -/
def WenyanBoundedUniversalWitnessTarget (W : List YiInstr) : Prop :=
  UniversalInterpSpecBounded W

/-- Stronger history-equality fixed-point target from the Wenyan quine route. -/
def WenyanHistoryFixedPointTarget : Prop :=
  SSBX.Foundation.Wen.WenyanQuineKleene.HistoryEqualityFixedPointExists

/-- The full target package whose proof would remove `kleene_recursion_axiom`
    by reusing `KleeneInternal.path_to_zero_axiom`. -/
def FullBridgeTarget : Prop :=
  UniversalInterpreterTarget ∧
  SmnCompilerTarget ∧
  DiagonalCompilerTarget ∧
  CuoRestrictedChurchTuringTarget

theorem full_bridge_target_implies_kleene_inverter :
    FullBridgeTarget → KleeneInverter := by
  intro h
  exact path_to_zero_axiom h.1 h.2.1 h.2.2.1 h.2.2.2

theorem full_universal_target_implies_bounded_target :
    UniversalInterpreterTarget → BoundedUniversalInterpreterTarget :=
  universalInterpExists_to_bounded

theorem full_universal_witness_satisfies_meta_interp_target
    {W : List YiInstr} :
    UniversalInterpSpec W → MetaInterpTargetSpec W :=
  universalInterpSpec_to_bounded

theorem wenyan_history_target_implies_halting_fixedpoint :
    WenyanHistoryFixedPointTarget → KleeneFixedPointExists := by
  intro h
  exact
    SSBX.Foundation.Wen.WenyanQuineKleene.historyEqualityFixedPointExists_to_kleeneFixedPointExists
      h

/-! ## Public Phase 1 summary -/

/-- Phase 1 public contract: the current bridge has checked semantic/encoding
    anchors, exact target propositions for the missing witnesses, an assembly
    theorem to the existing Kleene interface, and an explicit non-goal marker
    for strict YiInstr/CIC equivalence. -/
theorem target_contract_phase1_summary :
    LeanChecksYiSemantics
    ∧ ProgramEncodingRoundTrip
    ∧ FramedProgramRoundTrip
    ∧ (UniversalInterpreterTarget → BoundedUniversalInterpreterTarget)
    ∧ (FullBridgeTarget → KleeneInverter)
    ∧ (WenyanHistoryFixedPointTarget → KleeneFixedPointExists)
    ∧ targetStatus .strictYiInstrCICEquivalence = .nonGoal
    ∧ proofPhaseRank .leanTarget < proofPhaseRank .wenyanWitness := by
  exact ⟨lean_checks_yi_semantics,
    program_encoding_roundtrip,
    framed_program_roundtrip,
    full_universal_target_implies_bounded_target,
    full_bridge_target_implies_kleene_inverter,
    wenyan_history_target_implies_halting_fixedpoint,
    strict_yiinstr_cic_equivalence_is_non_goal,
    lean_target_before_wenyan_witness⟩

end SSBX.Foundation.Wen.MetaInterp.TargetContract
