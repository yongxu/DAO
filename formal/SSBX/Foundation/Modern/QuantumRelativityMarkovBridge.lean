/-
# QuantumRelativityMarkovBridge — Markov/因果桥的最小验证构造

Companion: `义理/Markov因果桥 · 大统一最小验证构造.md`

本文件只形式化一个很薄的可验证骨架：

1. 一个有限过程结构可以提供 Markov 读法：状态、一步支持、路径；
2. 同一个过程结构可以提供因果读法：事件与 before 关系；
3. 终端状态可以同时读成测量候选与事件记录；
4. 这仍不是现成 tagged 量子/相对论语言的直接相加，而是上一层 `mediatedBridge`
   方向的一个最小中介候选；它不否定 `192 × 371` 文构造覆盖路线。
-/
import SSBX.Foundation.Modern.QuantumRelativityIntegration

namespace SSBX.Foundation.Modern.QuantumRelativityMarkovBridge

open SSBX.Foundation.Modern.QuantumSpacetime
open SSBX.Foundation.Modern.QuantumRelativityNoGo
open SSBX.Foundation.Modern.QuantumRelativityIntegration

/-! ## § 1 Finite process carrier -/

/-- 最小有限过程：状态、一个到有界自然数编码的有限性见证、初态、终端谓词、一步转移关系。 -/
structure FiniteProcess where
  State : Type
  stateCode : State → Nat
  stateBound : Nat
  stateCode_lt_bound : ∀ s : State, stateCode s < stateBound
  stateCode_injective : ∀ {a b : State}, stateCode a = stateCode b → a = b
  initial : State
  terminal : State → Prop
  step : State → State → Prop

/-- 每个状态都有落在有限界内的编码。 -/
theorem state_code_within_bound (P : FiniteProcess) (s : P.State) :
    P.stateCode s < P.stateBound :=
  P.stateCode_lt_bound s

/-- 路径骨架：只保留起点、终点、有效性谓词。 -/
structure ProcessPath (P : FiniteProcess) where
  start : P.State
  stop : P.State
  valid : Prop

/-- 可达关系的最小读法：一步可达，或存在有效路径骨架。 -/
def Reachable (P : FiniteProcess) (a b : P.State) : Prop :=
  P.step a b ∨ ∃ p : ProcessPath P, p.start = a ∧ p.stop = b ∧ p.valid

/-- 每条有效路径都给出可达关系。 -/
theorem path_implies_reachable {P : FiniteProcess} (p : ProcessPath P) :
    p.valid → Reachable P p.start p.stop := by
  intro hv
  exact Or.inr ⟨p, rfl, rfl, hv⟩

/-- 终端状态作为测量候选。 -/
structure MeasurementCandidate (P : FiniteProcess) where
  state : P.State
  isTerminal : P.terminal state

/-- 终端状态可以被读成候选测量结果。 -/
def terminalAsMeasurementCandidate {P : FiniteProcess}
    (s : P.State) (hs : P.terminal s) : MeasurementCandidate P :=
  ⟨s, hs⟩

/-- `terminalAsMeasurementCandidate` 保留底层状态。 -/
theorem terminal_as_measurement_candidate {P : FiniteProcess}
    (s : P.State) (hs : P.terminal s) :
    (terminalAsMeasurementCandidate s hs).state = s :=
  rfl

/-! ## § 2 Markov reading -/

/-- Markov kernel 的最小骨架：只记录一步支持与自然数权重。 -/
structure MarkovKernelSkeleton (P : FiniteProcess) where
  support : P.State → P.State → Prop
  weight : P.State → P.State → Nat
  support_iff_positive : ∀ a b : P.State, support a b ↔ weight a b ≠ 0
  support_implies_step : ∀ a b : P.State, support a b → P.step a b

/-- 有 Markov 投影：当前骨架只要求存在一个 kernel skeleton。 -/
def HasMarkovProjection (P : FiniteProcess) : Prop :=
  Nonempty (MarkovKernelSkeleton P)

/-- 正权重推出一步转移。 -/
theorem positive_weight_implies_step {P : FiniteProcess}
    (K : MarkovKernelSkeleton P) {a b : P.State} :
    K.weight a b ≠ 0 → P.step a b := by
  intro hw
  exact K.support_implies_step a b ((K.support_iff_positive a b).mpr hw)

/-- 路径权重接口：第一轮只给占位定义，不证明概率归一化。 -/
def pathWeight {P : FiniteProcess} (_K : MarkovKernelSkeleton P)
    (_p : ProcessPath P) : Nat :=
  1

/-! ## § 3 Causal reading -/

/-- 因果事件：同一过程状态的事件读法。 -/
structure CausalEvent (P : FiniteProcess) where
  state : P.State

/-- 因果 before：当前最小读法直接用可达关系。 -/
def causalBefore {P : FiniteProcess} (a b : CausalEvent P) : Prop :=
  Reachable P a.state b.state

/-- 有因果投影：任意过程状态都可读为事件。 -/
def HasCausalProjection (P : FiniteProcess) : Prop :=
  ∀ _s : P.State, Nonempty (CausalEvent P)

/-- 任意一步转移都给出因果 before。 -/
theorem step_implies_causal_before {P : FiniteProcess}
    {a b : P.State} (h : P.step a b) :
    causalBefore (P := P) ⟨a⟩ ⟨b⟩ := by
  exact Or.inl h

/-! ## § 4 Measurement-event alignment -/

/-- 测量-事件桥：测量候选与事件记录共享同一个底层终端状态。 -/
structure MeasurementEventBridge (P : FiniteProcess) where
  terminalState : P.State
  isTerminal : P.terminal terminalState

namespace MeasurementEventBridge

/-- 桥的测量读法。 -/
def measurementCandidate {P : FiniteProcess}
    (b : MeasurementEventBridge P) : MeasurementCandidate P :=
  ⟨b.terminalState, b.isTerminal⟩

/-- 桥的事件读法。 -/
def eventRecord {P : FiniteProcess}
    (b : MeasurementEventBridge P) : CausalEvent P :=
  ⟨b.terminalState⟩

/-- 将测量-事件桥读作上一层的 tag-level `BridgeTerm`。 -/
def toBridgeTerm {P : FiniteProcess}
    (_b : MeasurementEventBridge P) : BridgeTerm :=
  { quantumProjection := .measurement
    relativityProjection := .event }

end MeasurementEventBridge

/-- 测量候选与事件记录对齐在同一个终端状态上。 -/
def MeasurementEventsAlign {P : FiniteProcess}
    (b : MeasurementEventBridge P) : Prop :=
  b.measurementCandidate.state = b.eventRecord.state

/-- 同一终端状态在测量投影与因果事件投影下对齐。 -/
theorem measurement_event_alignment {P : FiniteProcess}
    (b : MeasurementEventBridge P) :
    MeasurementEventsAlign b :=
  rfl

/-- 测量-事件桥可投到上一层桥项，并保留量子/相对论两面。 -/
theorem measurement_event_bridge_term_keeps_faces {P : FiniteProcess}
    (b : MeasurementEventBridge P) :
    b.toBridgeTerm.quantumFace = .quantumSpace
    ∧ b.toBridgeTerm.relativityFace = .relativisticSpacetime :=
  bridge_keeps_two_faces b.toBridgeTerm

/-! ## § 5 Bridge to the previous integration layer -/

/-- Markov/因果桥作为上一层 mediated-bridge 路线的一个候选。 -/
def MarkovCausalRoute : IntegrationRoute :=
  .mediatedBridge

/-- Markov/因果桥走的是上一层唯一认可的中介桥路线。 -/
theorem markov_causal_route_is_framework_route :
    isFrameworkRoute MarkovCausalRoute = true :=
  rfl

/-- Markov/因果桥保留量子读法与相对论读法这两面。 -/
theorem markov_bridge_keeps_quantum_and_relativity_faces :
    keepsQuantumFace MarkovCausalRoute = true
    ∧ keepsRelativityFace MarkovCausalRoute = true :=
  ⟨rfl, rfl⟩

/-- Markov/因果桥继续服从“同根但非当前 face identity”的边界。 -/
theorem markov_bridge_same_one_not_identity :
    sameOne .quantumSpace .relativisticSpacetime
    ∧ ¬ CurrentPhysicalUnity .quantumSpace .relativisticSpacetime :=
  quantum_spacetime_complementary_faces

/-- Markov/因果桥不取消 tagged-language 非坍缩边界。 -/
theorem markov_bridge_not_direct_language_addition :
    ¬ DirectUnificationByAddition :=
  no_direct_unification_by_addition

/-! ## § 6 Public summary -/

/-- 公开摘要：
    若给定一个有限过程、一个 Markov kernel skeleton、一个终端桥状态，
    则该结构有 Markov 投影、因果投影、测量-事件对齐；同时保留上一层
    tagged physical-language noncollapse 边界。 -/
theorem markov_causal_bridge_summary
    (P : FiniteProcess)
    (K : MarkovKernelSkeleton P)
    (b : MeasurementEventBridge P) :
    HasMarkovProjection P
    ∧ HasCausalProjection P
    ∧ MeasurementEventsAlign b
    ∧ keepsQuantumFace MarkovCausalRoute = true
    ∧ keepsRelativityFace MarkovCausalRoute = true
    ∧ sameOne .quantumSpace .relativisticSpacetime
    ∧ ¬ CurrentPhysicalUnity .quantumSpace .relativisticSpacetime
    ∧ ¬ DirectUnificationByAddition :=
  ⟨⟨K⟩,
   fun s => ⟨⟨s⟩⟩,
   measurement_event_alignment b,
   markov_bridge_keeps_quantum_and_relativity_faces.left,
   markov_bridge_keeps_quantum_and_relativity_faces.right,
   markov_bridge_same_one_not_identity.left,
   markov_bridge_same_one_not_identity.right,
   markov_bridge_not_direct_language_addition⟩

end SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
