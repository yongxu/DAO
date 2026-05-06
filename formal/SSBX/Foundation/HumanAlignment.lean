/-
Human alignment layer.

Claim formalized here:
- 子：聚焦所成之项。
- 天之子：天中经聚焦成子而成之项。
- 人：天之子，并意识此天之子。
- 做人：不是以控制为目标，而是在意图层面向齐生。

This module proves the claim as a definitional construction inside the SSBX
registry. It does not claim an empirical psychology theorem from no premises.
-/
import SSBX.Foundation.Monism

namespace SSBX.Foundation.HumanAlignment

open SSBX.Roster

inductive AimKind where
  | control
  | alignLife
  deriving DecidableEq, Repr

namespace AimKind

def label : AimKind -> String
  | .control => "控制"
  | .alignLife => "意图向齐生"

end AimKind

/-- `人` is registered as heaven-child-with-awareness. -/
structure HumanDefinition where
  heaven_registered : (G .«天») ∈ allSymbols
  child_registered : (G .«子») ∈ allSymbols
  formed_child_registered : (G .«成子») ∈ allSymbols
  focus_formed_child_registered : (G .«聚焦成子») ∈ allSymbols
  heaven_child_registered : (G .«天之子») ∈ allSymbols
  human_registered : (G .«人») ∈ allSymbols
  world_registered : (G .«世界») ∈ allSymbols
  self_registered : (G .«自身») ∈ allSymbols
  focus_registered : (G .«聚焦») ∈ allSymbols
  awareness_registered : (G .«意识») ∈ allSymbols
  child_depends_on_focus :
    (entryOf (G .«子»)).deps = [G .«聚焦»]
  focus_forms_child :
    (entryOf (G .«聚焦成子»)).deps = [G .«聚焦», G .«成子»]
  heaven_child_depends_on_heaven_and_focus_formed_child :
    (entryOf (G .«天之子»)).deps = [G .«天», G .«聚焦成子»]
  human_depends_on_heaven_child_awareness :
    (entryOf (G .«人»)).deps = [G .«天之子», G .«意识»]

/-- `做人` is registered as intentional alignment toward life. -/
structure DoingHumanDefinition where
  doing_registered : (G .«做人») ∈ allSymbols
  intention_registered : (G .«意图») ∈ allSymbols
  alignment_registered : (G .«向齐生») ∈ allSymbols
  intentional_alignment_registered : (G .«意图向齐生») ∈ allSymbols
  control_registered : (G .«控制») ∈ allSymbols
  doing_depends_on_intentional_alignment :
    (entryOf (G .«做人»)).deps = [G .«意图向齐生»]
  intentional_alignment_depends_on_intention_and_life_alignment :
    (entryOf (G .«意图向齐生»)).deps = [G .«意图», G .«向齐生»]
  life_alignment_targets_life : A .«生» ∈ (entryOf (G .«向齐生»)).deps
  control_not_doing_goal : G .«控制» ∉ (entryOf (G .«做人»)).deps

def humanDefinition : HumanDefinition :=
  { heaven_registered := by decide
    child_registered := by decide
    formed_child_registered := by decide
    focus_formed_child_registered := by decide
    heaven_child_registered := by decide
    human_registered := by decide
    world_registered := by decide
    self_registered := by decide
    focus_registered := by decide
    awareness_registered := by decide
    child_depends_on_focus := rfl
    focus_forms_child := rfl
    heaven_child_depends_on_heaven_and_focus_formed_child := rfl
    human_depends_on_heaven_child_awareness := rfl }

def doingHumanDefinition : DoingHumanDefinition :=
  { doing_registered := by decide
    intention_registered := by decide
    alignment_registered := by decide
    intentional_alignment_registered := by decide
    control_registered := by decide
    doing_depends_on_intentional_alignment := rfl
    intentional_alignment_depends_on_intention_and_life_alignment := rfl
    life_alignment_targets_life := by decide
    control_not_doing_goal := by decide }

def canonicalDoingHumanAim : AimKind := .alignLife

def DoingHumanAim (aim : AimKind) : Prop :=
  aim = .alignLife

theorem doing_human_is_alignment : DoingHumanAim canonicalDoingHumanAim :=
  rfl

theorem control_is_not_alignment : ¬ DoingHumanAim .control := by
  intro h
  cases h

theorem doing_human_goal_not_control : canonicalDoingHumanAim ≠ .control := by
  decide

theorem child_is_focus_formed :
    (entryOf (G .«子»)).deps = [G .«聚焦»] ∧
    (entryOf (G .«聚焦成子»)).deps = [G .«聚焦», G .«成子»] :=
  ⟨humanDefinition.child_depends_on_focus,
   humanDefinition.focus_forms_child⟩

theorem heaven_child_is_heaven_focus_formed_child :
    (entryOf (G .«天之子»)).deps = [G .«天», G .«聚焦成子»] :=
  humanDefinition.heaven_child_depends_on_heaven_and_focus_formed_child

theorem human_returns_to_heaven_child_with_awareness :
    (entryOf (G .«人»)).deps = [G .«天之子», G .«意识»] :=
  humanDefinition.human_depends_on_heaven_child_awareness

theorem doing_human_is_intentional_life_alignment :
    (entryOf (G .«做人»)).deps = [G .«意图向齐生»] ∧
    (entryOf (G .«意图向齐生»)).deps = [G .«意图», G .«向齐生»] :=
  ⟨doingHumanDefinition.doing_depends_on_intentional_alignment,
   doingHumanDefinition.intentional_alignment_depends_on_intention_and_life_alignment⟩

theorem doing_human_not_control_by_registry :
    G .«控制» ∉ (entryOf (G .«做人»)).deps :=
  doingHumanDefinition.control_not_doing_goal

inductive HumanAlignmentStage where
  | heaven
  | world
  | self
  | focus
  | child
  | formedChild
  | heavenChild
  | awareness
  | human
  | intention
  | lifeAlignment
  | doingHuman
  deriving DecidableEq, Repr

namespace HumanAlignmentStage

def label : HumanAlignmentStage -> String
  | .heaven => "天"
  | .world => "世界"
  | .self => "自身"
  | .focus => "聚焦"
  | .child => "子"
  | .formedChild => "聚焦成子"
  | .heavenChild => "天之子"
  | .awareness => "意识"
  | .human => "人"
  | .intention => "意图"
  | .lifeAlignment => "向齐生"
  | .doingHuman => "做人"

def symbol : HumanAlignmentStage -> Symbol
  | .heaven => G .«天»
  | .world => G .«世界»
  | .self => G .«自身»
  | .focus => G .«聚焦»
  | .child => G .«子»
  | .formedChild => G .«聚焦成子»
  | .heavenChild => G .«天之子»
  | .awareness => G .«意识»
  | .human => G .«人»
  | .intention => G .«意图»
  | .lifeAlignment => G .«向齐生»
  | .doingHuman => G .«做人»

end HumanAlignmentStage

/-- Construction DAG for the human-alignment subtheory. -/
def predecessors : HumanAlignmentStage -> List HumanAlignmentStage
  | .heaven => []
  | .world => []
  | .self => []
  | .focus => [.world, .self]
  | .child => [.focus]
  | .formedChild => [.focus, .child]
  | .heavenChild => [.heaven, .formedChild]
  | .awareness => [.heavenChild]
  | .human => [.heavenChild, .awareness]
  | .intention => [.human]
  | .lifeAlignment => [.intention]
  | .doingHuman => [.intention, .lifeAlignment]

def allHumanAlignmentStages : List HumanAlignmentStage :=
  [.heaven, .world, .self, .focus, .child, .formedChild, .heavenChild,
   .awareness, .human, .intention, .lifeAlignment, .doingHuman]

theorem human_alignment_stage_complete (s : HumanAlignmentStage) :
    s ∈ allHumanAlignmentStages := by
  cases s <;> decide

def rank : HumanAlignmentStage -> Nat
  | .heaven => 0
  | .world => 0
  | .self => 0
  | .focus => 1
  | .child => 2
  | .formedChild => 3
  | .heavenChild => 4
  | .awareness => 5
  | .human => 6
  | .intention => 7
  | .lifeAlignment => 8
  | .doingHuman => 9

theorem predecessor_rank_lt {p s : HumanAlignmentStage} (h : p ∈ predecessors s) :
    rank p < rank s := by
  cases s <;> cases p <;> simp [predecessors, rank] at h ⊢

end SSBX.Foundation.HumanAlignment
