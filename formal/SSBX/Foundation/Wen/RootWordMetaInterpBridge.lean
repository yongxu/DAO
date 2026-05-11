/-
# RootWordMetaInterpBridge -- registry programs as META input

This sidecar connects rooted-word registries to the existing R8 VM encoding
boundary. It extracts optional Yi instructions from registry entries, encodes
them with `ProgEnc.encProg`, and builds the META starting state used by the
universal-interpreter work. It does not prove the universal simulation theorem.
-/

import SSBX.Foundation.Wen.RootWordRegistry
import SSBX.Foundation.Wen.RootRuleInstructionBridge
import SSBX.Foundation.Wen.MetaInterp.Assembly

namespace SSBX.Foundation.Wen.RootWordMetaInterpBridge

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Hierarchy.RootLanguageTree
open SSBX.Foundation.Wen.R8ProjectionCalculus
open SSBX.Foundation.Wen.RootRuleKernel
open SSBX.Foundation.Wen.RootRuleInstructionBridge
open SSBX.Foundation.Wen.RootWord
open SSBX.Foundation.Wen.RootWordRegistry
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp.Assembly

/-! ## Registry extraction -/

/-- Extract the executable VM target program from a registry. Entries without a
Yi target remain semantic/root entries but do not contribute an opcode. -/
def instructionTargets (registry : RootWordRegistry) : List YiInstr :=
  registry.filterMap (fun entry => entry.word.yiInstr?)

/-- Encoded VM input carried by a rooted-word registry. -/
def encodedProgramOfRegistry (registry : RootWordRegistry) : List R8 :=
  ProgEnc.encProg (instructionTargets registry)

/-- Predicate required by the existing decoder round-trip. -/
def registryProgramEncodable (registry : RootWordRegistry) : Prop :=
  ProgEnc.AllEncodable (instructionTargets registry)

/-- META starting state for a rooted-word registry program. -/
def metaStartOfRegistry (h : Hexagram) (registry : RootWordRegistry) : YiState :=
  RunWith h metaInterpProg (encodedProgramOfRegistry registry)

theorem encodedProgramOfRegistry_eq_flatten (registry : RootWordRegistry) :
    encodedProgramOfRegistry registry =
      ((instructionTargets registry).map YiInstrEnc.encInstr).flatten := by
  rfl

theorem instructionTargets_have_root_readback (registry : RootWordRegistry) :
    ∀ instr ∈ instructionTargets registry,
      ∃ c : R8, visibleR8 (primitiveSemantics (rootRuleOfInstr instr)) = c := by
  intro instr _
  exact rootRuleOfInstr_has_visible_projection instr

theorem instructionTargets_have_core_loss_ledger (registry : RootWordRegistry) :
    ∀ instr ∈ instructionTargets registry,
      ∃ loss : ProjectionLoss, CoreForm.loss emptyEnv (rootCoreOfInstr instr) = loss := by
  intro instr _
  exact rootCoreOfInstr_has_loss_ledger instr

theorem decode_encodedProgramOfRegistry
    (registry : RootWordRegistry)
    (h_enc : registryProgramEncodable registry)
    (rest : List R8) :
    ProgEnc.decInstrs (instructionTargets registry).length
      (encodedProgramOfRegistry registry ++ rest) =
        some (instructionTargets registry, rest) := by
  exact ProgEnc.decInstrs_encProg (instructionTargets registry) h_enc rest

theorem metaStartOfRegistry_history
    (h : Hexagram) (registry : RootWordRegistry) :
    (metaStartOfRegistry h registry).history = encodedProgramOfRegistry registry := rfl

theorem metaStartOfRegistry_prog
    (h : Hexagram) (registry : RootWordRegistry) :
    (metaStartOfRegistry h registry).prog = metaInterpProg := rfl

theorem metaStartOfRegistry_pc
    (h : Hexagram) (registry : RootWordRegistry) :
    (metaStartOfRegistry h registry).pc = 0 := rfl

theorem metaStartOfRegistry_running
    (h : Hexagram) (registry : RootWordRegistry) :
    (metaStartOfRegistry h registry).halted = false := rfl

/-! ## Seed registry facts -/

theorem seedRegistry_instructionTargets :
    instructionTargets seedRegistry = [] := rfl

theorem seedRegistry_encodedProgram :
    encodedProgramOfRegistry seedRegistry = [] := rfl

theorem seedRegistry_encodable :
    registryProgramEncodable seedRegistry := by
  rw [registryProgramEncodable, seedRegistry_instructionTargets]
  intro instr h
  cases h

/-! ## Public summary -/

theorem root_word_meta_interp_bridge_summary :
    instructionTargets seedRegistry = []
    ∧ encodedProgramOfRegistry seedRegistry = []
    ∧ registryProgramEncodable seedRegistry
    ∧ (∀ registry : RootWordRegistry,
        ∀ instr ∈ instructionTargets registry,
          ∃ c : R8, visibleR8 (primitiveSemantics (rootRuleOfInstr instr)) = c)
    ∧ (∀ registry : RootWordRegistry,
        ∀ instr ∈ instructionTargets registry,
          ∃ loss : ProjectionLoss, CoreForm.loss emptyEnv (rootCoreOfInstr instr) = loss)
    ∧ (∀ registry : RootWordRegistry, ∀ h : Hexagram,
        (metaStartOfRegistry h registry).history = encodedProgramOfRegistry registry)
    ∧ (∀ registry : RootWordRegistry, ∀ h : Hexagram,
        (metaStartOfRegistry h registry).prog = metaInterpProg)
    ∧ (∀ registry : RootWordRegistry, ∀ h : Hexagram,
        (metaStartOfRegistry h registry).halted = false) := by
  exact
    ⟨ seedRegistry_instructionTargets
    , seedRegistry_encodedProgram
    , seedRegistry_encodable
    , instructionTargets_have_root_readback
    , instructionTargets_have_core_loss_ledger
    , fun registry h => metaStartOfRegistry_history h registry
    , fun registry h => metaStartOfRegistry_prog h registry
    , fun registry h => metaStartOfRegistry_running h registry
    ⟩

end SSBX.Foundation.Wen.RootWordMetaInterpBridge
