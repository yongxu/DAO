import SSBX.Text.WenyanOperators

/-!
# OperatorCellCandidateSemantics — conservative candidate audit ledger

This module records debated catalogue-to-`Cell192` binding candidates that are
not enabled as executable row semantics in this round.  It is deliberately a
ledger only: it imports no cell-semantic denotation module and exposes no
function consumed by `OperatorCellSemantics`.
-/

namespace SSBX.Text.OperatorCellCandidateSemantics

open SSBX.Text.WenyanOperators

/-- Coarse audit category for a debated catalogue-to-cell binding candidate. -/
inductive CandidateCellBindingCategory where
  | lineFlip
  | timeEdge
  | xuGuaIndex
  | kingWenIndex
  deriving Repr, DecidableEq

/--
One candidate audit row.  These rows are documentary only; `id` is a catalogue
operator id and `category` describes the debated cell-binding shape.
-/
structure OperatorCellCandidateBinding where
  surface : String
  id : OperatorId
  category : CandidateCellBindingCategory
  note : String
  deriving Repr

/--
Debated candidates kept out of executable `Cell192` row semantics this round.

The rows intentionally include no denotation, target cell, or transform.
-/
def operatorCellCandidateBindings : List OperatorCellCandidateBinding :=
  [ { surface := "动", id := .F_10, category := .lineFlip,
      note := "movement/startup reading debated as local line-change trigger" }
  , { surface := "化", id := .T_1, category := .timeEdge,
      note := "transformation reading debated as before/after cell edge" }
  , { surface := "变", id := .T_2, category := .lineFlip,
      note := "change reading debated as local line-flip witness" }
  , { surface := "推", id := .T_10, category := .xuGuaIndex,
      note := "push/advance reading debated against Xu Gua ordering" }
  , { surface := "复", id := .T_7, category := .kingWenIndex,
      note := "return reading debated against King Wen recurrence/indexing" }
  , { surface := "损", id := .T_12, category := .kingWenIndex,
      note := "decrease reading debated against King Wen catalogue position" }
  , { surface := "益", id := .T_13, category := .kingWenIndex,
      note := "increase reading debated against King Wen catalogue position" }
  ]

/-- The candidate ids, separated for concise audit statements. -/
def operatorCellCandidateIds : List OperatorId :=
  operatorCellCandidateBindings.map (fun row => row.id)

/--
Operator ids that already have executable row semantics, plus `T_6`, which is
explicitly excluded from this conservative candidate ledger.
-/
def enabledExecutableCellSemanticIds : List OperatorId :=
  [.Z_5, .Z_6, .Z_3, .T_6]

theorem operatorCellCandidateBindings_length :
    operatorCellCandidateBindings.length = 7 := by
  native_decide

theorem operatorCellCandidateIds_eq :
    operatorCellCandidateIds = [.F_10, .T_1, .T_2, .T_10, .T_7, .T_12, .T_13] := by
  native_decide

theorem operatorCellCandidateIds_length :
    operatorCellCandidateIds.length = 7 := by
  rw [operatorCellCandidateIds, List.length_map, operatorCellCandidateBindings_length]

theorem operatorCellCandidateIds_catalogue_members :
    operatorCellCandidateIds.all (fun id => decide (id ∈ allOperatorIds)) = true := by
  native_decide

theorem operatorCellCandidateIds_no_enabled_executable_ids :
    operatorCellCandidateIds.all
      (fun id => decide (id ∉ enabledExecutableCellSemanticIds)) = true := by
  native_decide

/--
Summary: the conservative audit ledger has seven catalogue-backed candidates
and none of its candidate ids are executable row-semantic ids this round.
-/
theorem operator_cell_candidate_audit_summary :
    operatorCellCandidateBindings.length = 7
    ∧ operatorCellCandidateIds.length = 7
    ∧ operatorCellCandidateIds.all (fun id => decide (id ∈ allOperatorIds)) = true
    ∧ operatorCellCandidateIds.all
        (fun id => decide (id ∉ enabledExecutableCellSemanticIds)) = true := by
  exact
    ⟨ operatorCellCandidateBindings_length
    , operatorCellCandidateIds_length
    , operatorCellCandidateIds_catalogue_members
    , operatorCellCandidateIds_no_enabled_executable_ids
    ⟩

end SSBX.Text.OperatorCellCandidateSemantics
