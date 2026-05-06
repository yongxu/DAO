/-
Attention layer.

Claim formalized here:
- 聚焦 is a formation process: focus forms a 子.
- 子 is the structural/result item formed by 聚焦.
- 注意 / Attention is a mechanism/dynamics concept: dynamic weighting,
  gating, maintenance, shifting, inhibition, and auditable reflection over focus.
- 聚焦 and 注意 share substrate but are not the same registered concept.
- 注意 can be aligned toward 生 and can support 做人 without making control the goal.
-/
import SSBX.Foundation.HumanAlignment

namespace SSBX.Foundation.Attention

open SSBX.Roster
open SSBX.Foundation.HumanAlignment

inductive ConceptLayer where
  | structure
  | formation
  | mechanism
  | reflective
  | normative
  | modelInterface
  deriving DecidableEq, Repr

namespace ConceptLayer

def label : ConceptLayer -> String
  | .structure => "结构/结果"
  | .formation => "成子/聚焦"
  | .mechanism => "机制/动态"
  | .reflective => "回观/可识"
  | .normative => "规范/意图"
  | .modelInterface => "模型接口"

end ConceptLayer

def conceptLayer : Symbol -> Option ConceptLayer
  | Symbol.generated .«子» => some .structure
  | Symbol.generated .«聚焦» => some .formation
  | Symbol.generated .«注意» => some .mechanism
  | Symbol.generated .«意识» => some .reflective
  | Symbol.generated .«意图» => some .normative
  | Symbol.primitive .«权» => some .modelInterface
  | _ => none

structure AttentionDefinition where
  child_registered : (G .«子») ∈ allSymbols
  focus_registered : (G .«聚焦») ∈ allSymbols
  attention_registered : (G .«注意») ∈ allSymbols
  weight_interface_registered : (P .«权») ∈ allSymbols
  attention_mechanism_registered : (G .«注意机制») ∈ allSymbols
  child_depends_on_focus :
    (entryOf (G .«子»)).deps = [G .«聚焦»]
  attention_depends_on_focus_and_mechanism :
    (entryOf (G .«注意»)).deps = [G .«聚焦», G .«注意机制»]
  mechanism_components :
    (entryOf (G .«注意机制»)).deps =
      [G .«动态权重分配», G .«门控», G .«维持», G .«转焦», G .«抑制», G .«回观可校»]
  child_is_structure : conceptLayer (G .«子») = some .structure
  focus_is_formation : conceptLayer (G .«聚焦») = some .formation
  attention_is_mechanism : conceptLayer (G .«注意») = some .mechanism
  weight_interface_is_model_interface : conceptLayer (P .«权») = some .modelInterface

def attentionDefinition : AttentionDefinition :=
  { child_registered := by decide
    focus_registered := by decide
    attention_registered := by decide
    weight_interface_registered := by decide
    attention_mechanism_registered := by decide
    child_depends_on_focus := rfl
    attention_depends_on_focus_and_mechanism := rfl
    mechanism_components := rfl
    child_is_structure := rfl
    focus_is_formation := rfl
    attention_is_mechanism := rfl
    weight_interface_is_model_interface := rfl }

theorem attention_depends_on_focus :
    G .«聚焦» ∈ (entryOf (G .«注意»)).deps := by
  decide

theorem focus_forms_child :
    (entryOf (G .«子»)).deps = [G .«聚焦»] :=
  attentionDefinition.child_depends_on_focus

theorem attention_mechanism_has_components :
    (entryOf (G .«注意机制»)).deps =
      [G .«动态权重分配», G .«门控», G .«维持», G .«转焦», G .«抑制», G .«回观可校»] :=
  attentionDefinition.mechanism_components

theorem focus_not_identical_attention : G .«聚焦» ≠ G .«注意» := by
  decide

theorem focus_and_attention_have_different_layers :
    conceptLayer (G .«聚焦») ≠ conceptLayer (G .«注意») := by
  simp [conceptLayer]

def sharedSubstrate : List Symbol :=
  [A .«场», A .«焦», A .«感», A .«识», A .«择», A .«权», A .«重», A .«阈»,
   A .«扰», A .«稳», A .«回», A .«观», G .«意图»]

def focusSubstrate : List Symbol :=
  sharedSubstrate ++ [G .«聚焦», G .«子», G .«聚焦基底»]

def attentionSubstrate : List Symbol :=
  sharedSubstrate ++ [G .«注意», G .«注意基底»]

theorem attention_and_focus_share_substrate :
    ∀ s, s ∈ sharedSubstrate -> s ∈ focusSubstrate ∧ s ∈ attentionSubstrate := by
  intro s hs
  exact ⟨List.mem_append_left _ hs, List.mem_append_left _ hs⟩

theorem focus_substrate_registered : (G .«聚焦基底») ∈ allSymbols := by
  decide

theorem attention_substrate_registered : (G .«注意基底») ∈ allSymbols := by
  decide

theorem focus_and_attention_share_same_base_marker :
    G .«同基» ∈ (entryOf (G .«聚焦基底»)).deps ∧
    G .«同基» ∈ (entryOf (G .«注意基底»)).deps := by
  decide

inductive CognitiveAttentionPattern where
  | bottomUpSalience
  | topDownAttention
  | selectiveAttention
  | sustainedAttention
  | attentionalShift
  | executiveControl
  | workingMemory
  | consciousAccess
  | alignedAttention
  deriving DecidableEq, Repr

namespace CognitiveAttentionPattern

def label : CognitiveAttentionPattern -> String
  | .bottomUpSalience => "bottom-up salience / 自下而上注意"
  | .topDownAttention => "top-down attention / 自上而下注意"
  | .selectiveAttention => "selective attention / 择注意"
  | .sustainedAttention => "sustained attention / 持续注意"
  | .attentionalShift => "attentional shift / 转焦"
  | .executiveControl => "executive control / 执行控制"
  | .workingMemory => "working memory / 工作记忆"
  | .consciousAccess => "conscious access / 意识通达"
  | .alignedAttention => "aligned attention / 注意向齐生"

def symbol : CognitiveAttentionPattern -> Symbol
  | .bottomUpSalience => G .«自下而上注意»
  | .topDownAttention => G .«自上而下注意»
  | .selectiveAttention => G .«择注意»
  | .sustainedAttention => G .«持续注意»
  | .attentionalShift => G .«转焦»
  | .executiveControl => G .«执行控制»
  | .workingMemory => G .«工作记忆»
  | .consciousAccess => G .«意识通达»
  | .alignedAttention => G .«注意向齐生»

end CognitiveAttentionPattern

def allCognitiveAttentionPatterns : List CognitiveAttentionPattern :=
  [.bottomUpSalience, .topDownAttention, .selectiveAttention, .sustainedAttention,
   .attentionalShift, .executiveControl, .workingMemory, .consciousAccess,
   .alignedAttention]

theorem cognitive_attention_patterns_complete (p : CognitiveAttentionPattern) :
    p ∈ allCognitiveAttentionPatterns := by
  cases p <;> decide

theorem cognitive_attention_patterns_registered (p : CognitiveAttentionPattern) :
    CognitiveAttentionPattern.symbol p ∈ allSymbols := by
  cases p <;> native_decide

theorem bottom_up_attention_depends_on_salience_and_attention :
    (entryOf (G .«自下而上注意»)).deps = [G .«显著», A .«扰», A .«变», G .«注意»] :=
  rfl

theorem top_down_attention_depends_on_intention_goal_and_attention :
    (entryOf (G .«自上而下注意»)).deps = [G .«意图», G .«目标», G .«注意»] :=
  rfl

theorem selective_attention_depends_on_filtering_choice_inhibition_release :
    (entryOf (G .«择注意»)).deps = [A .«筛», A .«择», A .«抑», A .«放», G .«注意»] :=
  rfl

theorem sustained_attention_depends_on_stability_and_continuation :
    (entryOf (G .«持续注意»)).deps = [A .«稳», A .«续», G .«注意»] :=
  rfl

theorem executive_control_is_local_attention_mechanism :
    (entryOf (G .«执行控制»)).deps = [G .«控制», A .«阈», G .«审校不败»] :=
  rfl

theorem working_memory_depends_on_store_continue_recognize_reflect :
    (entryOf (G .«工作记忆»)).deps = [A .«存», A .«续», A .«识», G .«回观»] :=
  rfl

theorem conscious_access_depends_on_awareness_reflection_recognizability :
    (entryOf (G .«意识通达»)).deps = [G .«意识», G .«回观», G .«可识»] :=
  rfl

theorem attention_can_be_aligned_to_life :
    (entryOf (G .«注意向齐生»)).deps = [G .«注意», G .«向齐生»] :=
  rfl

theorem aligned_attention_supports_doing_human :
    (entryOf (G .«做人注意»)).deps = [G .«做人», G .«注意向齐生»] :=
  rfl

theorem control_can_be_local_mechanism_but_not_doing_goal :
    (entryOf (G .«执行控制»)).deps = [G .«控制», A .«阈», G .«审校不败»] ∧
    G .«控制» ∉ (entryOf (G .«做人»)).deps :=
  ⟨executive_control_is_local_attention_mechanism, doing_human_not_control_by_registry⟩

inductive AttentionStage where
  | focus
  | mechanism
  | attention
  | bottomUp
  | topDown
  | selective
  | sustained
  | shift
  | executive
  | memory
  | conscious
  | aligned
  | doingSupport
  deriving DecidableEq, Repr

namespace AttentionStage

def label : AttentionStage -> String
  | .focus => "聚焦"
  | .mechanism => "注意机制"
  | .attention => "注意"
  | .bottomUp => "自下而上注意"
  | .topDown => "自上而下注意"
  | .selective => "择注意"
  | .sustained => "持续注意"
  | .shift => "转焦"
  | .executive => "执行控制"
  | .memory => "工作记忆"
  | .conscious => "意识通达"
  | .aligned => "注意向齐生"
  | .doingSupport => "做人注意"

end AttentionStage

def predecessors : AttentionStage -> List AttentionStage
  | .focus => []
  | .mechanism => []
  | .attention => [.focus, .mechanism]
  | .bottomUp => [.attention]
  | .topDown => [.attention]
  | .selective => [.attention]
  | .sustained => [.attention]
  | .shift => [.attention]
  | .executive => [.attention]
  | .memory => [.attention]
  | .conscious => [.attention]
  | .aligned => [.attention]
  | .doingSupport => [.aligned]

def allAttentionStages : List AttentionStage :=
  [.focus, .mechanism, .attention, .bottomUp, .topDown, .selective, .sustained,
   .shift, .executive, .memory, .conscious, .aligned, .doingSupport]

theorem attention_stage_complete (s : AttentionStage) : s ∈ allAttentionStages := by
  cases s <;> decide

def rank : AttentionStage -> Nat
  | .focus => 0
  | .mechanism => 0
  | .attention => 1
  | .bottomUp => 2
  | .topDown => 2
  | .selective => 2
  | .sustained => 2
  | .shift => 2
  | .executive => 2
  | .memory => 2
  | .conscious => 2
  | .aligned => 3
  | .doingSupport => 4

theorem predecessor_rank_lt {p s : AttentionStage} (h : p ∈ predecessors s) :
    rank p < rank s := by
  cases s <;> cases p <;> simp [predecessors, rank] at h ⊢

end SSBX.Foundation.Attention
