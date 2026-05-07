import SSBX.Foundation.Bagua.Cell192
import SSBX.Text.OperatorFamilySemantics
import SSBX.Text.OperatorSignatures

/-!
# OperatorCellSemantics — theorem-level coverage rows for operator-cell pairs

This file gives every `OperatorId × Cell192` pair a machine-checkable semantic
row.  It does not hand-write 71,232 denotational theorems.  Each row carries the
total text-level signature coverage, plus executable `Cell192` transform data
when the operator family is one of the currently exact cell transforms.
-/

namespace SSBX.Text.OperatorCellSemantics

open SSBX.Foundation.Bagua.Cell192
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorFamilySemantics
open SSBX.Text.OperatorSignatures

/-- Semantic evidence attached to one operator-cell pair. -/
inductive OperatorCellSemanticEvidence where
  | executableCellTransform
  | exactSignatureShape
  | groupDefaultSignatureShape
  deriving Repr, DecidableEq, BEq

structure OperatorCellSemanticRow where
  id : OperatorId
  cell : Cell192
  signature : CoveredOperatorSignature
  cellTransform? : Option Cell192
  evidence : OperatorCellSemanticEvidence
  deriving Repr

def semanticEvidenceFor (id : OperatorId) (cell : Cell192) :
    OperatorCellSemanticEvidence :=
  match applyCellTransformForOperator? id cell with
  | some _ => .executableCellTransform
  | none =>
      match (fullSignatureFor id).evidence with
      | .seedOverride => .exactSignatureShape
      | .groupDefault => .groupDefaultSignatureShape

def operatorCellSemanticRow (id : OperatorId) (cell : Cell192) :
    OperatorCellSemanticRow :=
  { id := id
  , cell := cell
  , signature := fullSignatureFor id
  , cellTransform? := applyCellTransformForOperator? id cell
  , evidence := semanticEvidenceFor id cell }

def operatorCellSemanticRowsFor (id : OperatorId) : List OperatorCellSemanticRow :=
  Cell192.all.map (operatorCellSemanticRow id)

/-- Total semantic coverage table for the 371 × 192 operator-cell grid. -/
def allOperatorCellSemanticRows : List OperatorCellSemanticRow :=
  allOperatorIds.flatMap operatorCellSemanticRowsFor

def allOperatorCellSemanticPairs : List (OperatorId × Cell192) :=
  allOperatorCellSemanticRows.map (fun row => (row.id, row.cell))

def executableCellTransformRows : List OperatorCellSemanticRow :=
  allOperatorCellSemanticRows.filter
    (fun row => row.evidence == OperatorCellSemanticEvidence.executableCellTransform)

def exactSignatureShapeRows : List OperatorCellSemanticRow :=
  allOperatorCellSemanticRows.filter
    (fun row => row.evidence == OperatorCellSemanticEvidence.exactSignatureShape)

def groupDefaultSignatureShapeRows : List OperatorCellSemanticRow :=
  allOperatorCellSemanticRows.filter
    (fun row => row.evidence == OperatorCellSemanticEvidence.groupDefaultSignatureShape)

theorem operatorCellSemanticRowsFor_length (id : OperatorId) :
    (operatorCellSemanticRowsFor id).length = 192 := by
  rw [operatorCellSemanticRowsFor, List.length_map, Cell192.all_length]

theorem allOperatorCellSemanticRows_length :
    allOperatorCellSemanticRows.length = 71232 := by
  native_decide

theorem allOperatorCellSemanticPairs_length :
    allOperatorCellSemanticPairs.length = 71232 := by
  rw [allOperatorCellSemanticPairs, List.length_map, allOperatorCellSemanticRows_length]

theorem executableCellTransformRows_length :
    executableCellTransformRows.length = 576 := by
  native_decide

theorem exactSignatureShapeRows_length :
    exactSignatureShapeRows.length = 2112 := by
  native_decide

theorem groupDefaultSignatureShapeRows_length :
    groupDefaultSignatureShapeRows.length = 68544 := by
  native_decide

theorem operatorCellSemanticStatus_counts_sum :
    executableCellTransformRows.length
      + exactSignatureShapeRows.length
      + groupDefaultSignatureShapeRows.length
      = allOperatorCellSemanticRows.length := by
  rw [executableCellTransformRows_length, exactSignatureShapeRows_length,
    groupDefaultSignatureShapeRows_length, allOperatorCellSemanticRows_length]

theorem operatorCellSemanticRow_signature_id (id : OperatorId) (cell : Cell192) :
    (operatorCellSemanticRow id cell).signature.id = id := by
  exact fullSignatureFor_id id

theorem operatorCellSemanticRows_complete_pair (id : OperatorId) (cell : Cell192) :
    ∃ row, row ∈ allOperatorCellSemanticRows ∧ row.id = id ∧ row.cell = cell := by
  refine ⟨operatorCellSemanticRow id cell, ?_, rfl, rfl⟩
  unfold allOperatorCellSemanticRows operatorCellSemanticRowsFor
  exact List.mem_flatMap.mpr
    ⟨id, allOperatorIds_complete id,
      List.mem_map.mpr ⟨cell, Cell192.mem_all cell, rfl⟩⟩

theorem operatorCellSemanticRows_signature_complete
    (id : OperatorId) (cell : Cell192) :
    ∃ row, row ∈ allOperatorCellSemanticRows
      ∧ row.id = id
      ∧ row.cell = cell
      ∧ row.signature.id = id := by
  refine ⟨operatorCellSemanticRow id cell, ?_, rfl, rfl, ?_⟩
  · unfold allOperatorCellSemanticRows operatorCellSemanticRowsFor
    exact List.mem_flatMap.mpr
      ⟨id, allOperatorIds_complete id,
        List.mem_map.mpr ⟨cell, Cell192.mem_all cell, rfl⟩⟩
  · exact operatorCellSemanticRow_signature_id id cell

theorem operatorCellSemanticRows_cuo_executable (cell : Cell192) :
    (operatorCellSemanticRow .Z_5 cell).evidence =
      OperatorCellSemanticEvidence.executableCellTransform
      ∧ (operatorCellSemanticRow .Z_5 cell).cellTransform? = some (Cell192.hexCuo cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_zong_executable (cell : Cell192) :
    (operatorCellSemanticRow .Z_6 cell).evidence =
      OperatorCellSemanticEvidence.executableCellTransform
      ∧ (operatorCellSemanticRow .Z_6 cell).cellTransform? = some (Cell192.hexZong cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_hu_executable (cell : Cell192) :
    (operatorCellSemanticRow .Z_3 cell).evidence =
      OperatorCellSemanticEvidence.executableCellTransform
      ∧ (operatorCellSemanticRow .Z_3 cell).cellTransform? = some (Cell192.hexHu cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_R_1_signature_only (cell : Cell192) :
    (operatorCellSemanticRow .R_1 cell).evidence =
      OperatorCellSemanticEvidence.groupDefaultSignatureShape := by
  rfl

/--
Summary: all 71,232 pairs have theorem-level semantic coverage rows; exact
cell execution is attached only where a current cell-transform family exists.
The remaining rows split between exact seed-signature obligations and
group-default signature-shape obligations.
-/
theorem operator_cell_semantic_coverage_summary :
    allOperatorCellSemanticRows.length = 71232
    ∧ allOperatorCellSemanticPairs.length = 71232
    ∧ executableCellTransformRows.length = 576
    ∧ exactSignatureShapeRows.length = 2112
    ∧ groupDefaultSignatureShapeRows.length = 68544
    ∧ executableCellTransformRows.length
        + exactSignatureShapeRows.length
        + groupDefaultSignatureShapeRows.length
        = allOperatorCellSemanticRows.length
    ∧ (∀ id : OperatorId, (operatorCellSemanticRowsFor id).length = 192)
    ∧ (∀ id : OperatorId, ∀ cell : Cell192,
        ∃ row, row ∈ allOperatorCellSemanticRows
          ∧ row.id = id
          ∧ row.cell = cell
          ∧ row.signature.id = id)
    ∧ (∀ cell : Cell192,
        (operatorCellSemanticRow .Z_5 cell).cellTransform? = some (Cell192.hexCuo cell))
    ∧ (∀ cell : Cell192,
        (operatorCellSemanticRow .Z_6 cell).cellTransform? = some (Cell192.hexZong cell))
    ∧ (∀ cell : Cell192,
        (operatorCellSemanticRow .Z_3 cell).cellTransform? = some (Cell192.hexHu cell)) := by
  exact
    ⟨ allOperatorCellSemanticRows_length
    , allOperatorCellSemanticPairs_length
    , executableCellTransformRows_length
    , exactSignatureShapeRows_length
    , groupDefaultSignatureShapeRows_length
    , operatorCellSemanticStatus_counts_sum
    , operatorCellSemanticRowsFor_length
    , operatorCellSemanticRows_signature_complete
    , fun cell => (operatorCellSemanticRows_cuo_executable cell).2
    , fun cell => (operatorCellSemanticRows_zong_executable cell).2
    , fun cell => (operatorCellSemanticRows_hu_executable cell).2
    ⟩

end SSBX.Text.OperatorCellSemantics
