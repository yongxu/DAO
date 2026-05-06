/-
Construction layer: a content-construction DAG for SSBX.

This is intentionally different from the roster DAG and from MonadRoot.  The
roster DAG proves that registered vocabulary is covered and acyclic.  MonadRoot
keeps a formal single-root discipline at `一元`.  This module records the
content spine: Γ as the current field of concern, 三本 as 物/動/間,
三显 as 位/場/際, 三征 as 幾/勢/機, and the 開/閉 gate plus composite
forms as the event and topology layer.
-/
import SSBX.Roster
import SSBX.Truth.Absolute
import SSBX.Model.Adequacy

namespace SSBX.Foundation.Core.Monism

open SSBX.Roster
open SSBX.Truth
open SSBX.Truth.Absolute
open SSBX.Model.Adequacy

inductive ConstructionId where
  | gammaFieldRoot
  | jianRoot
  | aspectTriad
  | yuanTriad
  | systemDynamics
  | universalProofPrinciple
  | openCloseCore
  | auditCore
  | valueCore
  | actionCore
  | attentionCore
  | humanAlignmentCore
  | modelAdequacyCore
  | truthCore
  | cicAsFormalModel
  | ssbxTheory
  deriving DecidableEq, Repr

namespace ConstructionId

def label : ConstructionId -> String
  | .gammaFieldRoot => "Γ / territory 当前论域"
  | .jianRoot => "三本 / 物-動-間"
  | .aspectTriad => "三显 / 位-場-際"
  | .yuanTriad => "三征 / 幾-勢-機"
  | .systemDynamics => "開閉闸口与網體流合成"
  | .universalProofPrinciple => "普遍证明理"
  | .openCloseCore => "开闭核心"
  | .auditCore => "审校核心"
  | .valueCore => "价值核心"
  | .actionCore => "行核心"
  | .attentionCore => "注意/聚焦机制核心"
  | .humanAlignmentCore => "做人/对齐核心"
  | .modelAdequacyCore => "模型充分性核心"
  | .truthCore => "真理核心"
  | .cicAsFormalModel => "CIC 作为形式模"
  | .ssbxTheory => "生生不息论"

/-- Where a construction stage has a direct registered symbol, expose it. -/
def symbol : ConstructionId -> Option Symbol
  | .gammaFieldRoot => some (A .«场»)
  | .jianRoot => some (A .«间»)
  | .aspectTriad => some (A .«位»)
  | .yuanTriad => some (A .«几»)
  | .systemDynamics => some (A .«机»)
  | .universalProofPrinciple => some (G .«普遍证明理»)
  | .openCloseCore => some (R .«开»)
  | .auditCore => some (G .«审校不败»)
  | .valueCore => some (R .«道»)
  | .actionCore => some (A .«行»)
  | .attentionCore => some (G .«注意»)
  | .humanAlignmentCore => some (G .«做人»)
  | .modelAdequacyCore => none
  | .truthCore => some (R .«真»)
  | .cicAsFormalModel => some (G .«归纳构造演算»)
  | .ssbxTheory => some (G .«生生不息»)

end ConstructionId

/--
Proof-construction dependencies. Direction: predecessor -> stage.
This is the graph the theory should be read as when constructing from one root.
-/
def predecessors : ConstructionId -> List ConstructionId
  | .gammaFieldRoot => []
  | .jianRoot => [.gammaFieldRoot]
  | .aspectTriad => [.gammaFieldRoot, .jianRoot]
  | .yuanTriad => [.aspectTriad]
  | .systemDynamics => [.jianRoot, .yuanTriad]
  | .universalProofPrinciple => [.gammaFieldRoot]
  | .openCloseCore => [.systemDynamics]
  | .auditCore => [.universalProofPrinciple, .aspectTriad]
  | .valueCore => [.openCloseCore, .auditCore]
  | .actionCore => [.yuanTriad, .systemDynamics, .openCloseCore]
  | .attentionCore => [.aspectTriad, .openCloseCore, .auditCore]
  | .humanAlignmentCore => [.actionCore, .attentionCore, .openCloseCore, .auditCore]
  | .modelAdequacyCore => [.gammaFieldRoot, .universalProofPrinciple, .auditCore]
  | .truthCore => [.valueCore, .modelAdequacyCore, .auditCore]
  | .cicAsFormalModel => [.universalProofPrinciple, .modelAdequacyCore]
  | .ssbxTheory => [.truthCore, .valueCore, .actionCore, .attentionCore, .humanAlignmentCore, .modelAdequacyCore, .cicAsFormalModel]

def allConstructionIds : List ConstructionId :=
  [.gammaFieldRoot, .jianRoot, .aspectTriad, .yuanTriad, .systemDynamics,
   .universalProofPrinciple, .openCloseCore, .auditCore, .valueCore, .actionCore,
   .attentionCore, .humanAlignmentCore, .modelAdequacyCore, .truthCore,
   .cicAsFormalModel, .ssbxTheory]

theorem construction_ledger_complete (id : ConstructionId) : id ∈ allConstructionIds := by
  cases id <;> decide

/-- A rank function witnessing that the construction dependency graph is acyclic. -/
def rank : ConstructionId -> Nat
  | .gammaFieldRoot => 0
  | .jianRoot => 1
  | .aspectTriad => 2
  | .yuanTriad => 3
  | .systemDynamics => 4
  | .universalProofPrinciple => 1
  | .openCloseCore => 5
  | .auditCore => 3
  | .valueCore => 6
  | .actionCore => 6
  | .attentionCore => 6
  | .humanAlignmentCore => 7
  | .modelAdequacyCore => 4
  | .truthCore => 7
  | .cicAsFormalModel => 5
  | .ssbxTheory => 8

theorem predecessor_rank_lt {p id : ConstructionId} (h : p ∈ predecessors id) :
    rank p < rank id := by
  cases id <;> cases p <;> simp [predecessors, rank] at h ⊢

structure ContentRoot where
  gamma_atom_registered : (A .«场») ∈ allSymbols
  interval_atom_registered : (A .«间») ∈ allSymbols

def contentRoot : ContentRoot :=
  { gamma_atom_registered := by decide
    interval_atom_registered := by decide }

abbrev MonismRoot := ContentRoot

def monismRoot : MonismRoot :=
  contentRoot

/--
The universal proof principle is explicit: it is not hidden as a Lean axiom.
It says that a construction stage can be proved once all its predecessors are
proved, with the content root Γ supplied as the initial proof.
-/
structure UniversalProvePrinciple where
  proves : ConstructionId -> Prop
  proves_root : proves .gammaFieldRoot
  proves_step : ∀ id, (∀ p, p ∈ predecessors id -> proves p) -> proves id

theorem universal_prove_constructs_all (P : UniversalProvePrinciple) :
    ∀ id : ConstructionId, P.proves id := by
  have h : ∀ n, ∀ id : ConstructionId, rank id ≤ n -> P.proves id := by
    intro n
    induction n with
    | zero =>
        intro id hle
        cases id <;> simp [rank] at hle
        exact P.proves_root
    | succ n ih =>
        intro id hle
        apply P.proves_step
        intro p hp
        apply ih
        have hlt : rank p < rank id := predecessor_rank_lt hp
        have hlt' : rank p < Nat.succ n := Nat.lt_of_lt_of_le hlt hle
        exact Nat.le_of_lt_succ hlt'
  intro id
  exact h (rank id) id (Nat.le_refl _)

def MonismConstructsSSBX (P : UniversalProvePrinciple) : Prop :=
  P.proves .ssbxTheory

abbrev ContentConstructsSSBX := MonismConstructsSSBX

theorem ssbx_constructed_from_monism (P : UniversalProvePrinciple) :
    MonismConstructsSSBX P :=
  universal_prove_constructs_all P .ssbxTheory

theorem ssbx_constructed_from_content (P : UniversalProvePrinciple) :
    ContentConstructsSSBX P :=
  ssbx_constructed_from_monism P

/--
If model-grounded truth is already supplied by the model layer, the monism
construction can be paired with it. This keeps construction and truth distinct.
-/
structure MonismSSBXCertificate where
  root : MonismRoot
  universal_prove : UniversalProvePrinciple
  constructs_theory : MonismConstructsSSBX universal_prove
  model_grounded_truth : ModelGroundedTruth SSBXTheory

def certificateFromModelGroundedTruth
    (P : UniversalProvePrinciple)
    (H : ModelGroundedTruth SSBXTheory) : MonismSSBXCertificate :=
  { root := monismRoot
    universal_prove := P
    constructs_theory := ssbx_constructed_from_monism P
    model_grounded_truth := H }

end SSBX.Foundation.Core.Monism
