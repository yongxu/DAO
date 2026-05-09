import SSBX.Foundation.Bagua.Cell192
import SSBX.Text.OperatorFamilySemantics
import SSBX.Text.OperatorSignatures

/-!
# OperatorCellSemantics — theorem-level coverage rows for operator-cell pairs

This file gives every `OperatorId × Cell192` pair a machine-checkable semantic
row.  It does not hand-write 71,232 denotational theorems.  Each row carries the
total text-level signature coverage and a conservative machine denotation. Exact
`Cell192` transform operators carry their concrete output cell; every remaining
operator carries a signature-preserving support-cell carrier, intentionally
weaker than a domain-specific meaning.
-/

namespace SSBX.Text.OperatorCellSemantics

open SSBX.Foundation.Bagua.Cell192
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorFamilySemantics
open SSBX.Text.OperatorSignatures

/-- Machine-denotation kind attached to one operator-cell pair. -/
inductive OperatorCellDenotationKind where
  | exactCellTransform
  | signatureCarrier
  deriving Repr, DecidableEq, BEq

/--
Total denotation evidence for one operator-cell pair.

Exact transform rows record both the input and output cell. Signature-carrier
rows keep only a support cell plus the operator's signature kind; they are total
machine support over the Bagua grid, not a claim of richer domain semantics.
-/
inductive OperatorCellDenotation where
  | exactTransform (kind : CellTransformKind) (input output : Cell192)
  | signatureCarrier (signatureKind : SignatureKind) (supportCell : Cell192)
  deriving Repr, DecidableEq

namespace OperatorCellDenotation

def kind : OperatorCellDenotation → OperatorCellDenotationKind
  | .exactTransform .. => .exactCellTransform
  | .signatureCarrier .. => .signatureCarrier

def supportCell : OperatorCellDenotation → Cell192
  | .exactTransform _ input _ => input
  | .signatureCarrier _ supportCell => supportCell

def transformedCell? : OperatorCellDenotation → Option Cell192
  | .exactTransform _ _ output => some output
  | .signatureCarrier .. => none

def isExactTransform (denotation : OperatorCellDenotation) : Bool :=
  denotation.kind == OperatorCellDenotationKind.exactCellTransform

def isSignatureCarrier (denotation : OperatorCellDenotation) : Bool :=
  denotation.kind == OperatorCellDenotationKind.signatureCarrier

end OperatorCellDenotation

structure OperatorCellSemanticRow where
  id : OperatorId
  cell : Cell192
  signature : CoveredOperatorSignature
  denotation : OperatorCellDenotation
  cellTransform? : Option Cell192
  denotationKind : OperatorCellDenotationKind
  deriving Repr

def operatorCellDenotationFor (id : OperatorId) (cell : Cell192) :
    OperatorCellDenotation :=
  match cellTransformForOperator? id with
  | some kind =>
      .exactTransform kind cell (kind.apply cell)
  | none => .signatureCarrier (fullSignatureFor id).kind cell

/-- Compatibility wrapper for callers that still expect an optional denotation. -/
def operatorCellDenotationFor? (id : OperatorId) (cell : Cell192) :
    Option OperatorCellDenotation :=
  some (operatorCellDenotationFor id cell)

def operatorCellDenotationKindFor (id : OperatorId) (cell : Cell192) :
    OperatorCellDenotationKind :=
  (operatorCellDenotationFor id cell).kind

def operatorCellSemanticRow (id : OperatorId) (cell : Cell192) :
    OperatorCellSemanticRow :=
  let denotation := operatorCellDenotationFor id cell
  { id := id
  , cell := cell
  , signature := fullSignatureFor id
  , denotation := denotation
  , cellTransform? := denotation.transformedCell?
  , denotationKind := denotation.kind }

def operatorCellSemanticRowsFor (id : OperatorId) : List OperatorCellSemanticRow :=
  Cell192.all.map (operatorCellSemanticRow id)

/-- Total semantic coverage table for the 371 × 192 operator-cell grid. -/
def allOperatorCellSemanticRows : List OperatorCellSemanticRow :=
  allOperatorIds.flatMap operatorCellSemanticRowsFor

def allOperatorCellSemanticPairs : List (OperatorId × Cell192) :=
  allOperatorCellSemanticRows.map (fun row => (row.id, row.cell))

def exactCellTransformDenotationRows : List OperatorCellSemanticRow :=
  allOperatorCellSemanticRows.filter
    (fun row => row.denotationKind == OperatorCellDenotationKind.exactCellTransform)

/-- Legacy alias: exact cell-transform rows were formerly called family-backed. -/
def familyBackedDenotationRows : List OperatorCellSemanticRow :=
  exactCellTransformDenotationRows

def signatureCarrierDenotationRows : List OperatorCellSemanticRow :=
  allOperatorCellSemanticRows.filter
    (fun row => row.denotationKind == OperatorCellDenotationKind.signatureCarrier)

def machineDenotationRows : List OperatorCellSemanticRow :=
  allOperatorCellSemanticRows

def executableCellTransformRows : List OperatorCellSemanticRow :=
  exactCellTransformDenotationRows

/-- Legacy empty list: shape-only rows are no longer part of the core denotation API. -/
def exactSignatureShapeRows : List OperatorCellSemanticRow :=
  []

/-- Legacy empty list: shape-only rows are no longer part of the core denotation API. -/
def catalogueSignatureShapeRows : List OperatorCellSemanticRow :=
  []

theorem operatorCellSemanticRowsFor_length (id : OperatorId) :
    (operatorCellSemanticRowsFor id).length = 192 := by
  rw [operatorCellSemanticRowsFor, List.length_map, Cell192.all_length]

theorem allOperatorCellSemanticRows_length :
    allOperatorCellSemanticRows.length = 71232 := by
  native_decide

theorem allOperatorCellSemanticPairs_length :
    allOperatorCellSemanticPairs.length = 71232 := by
  rw [allOperatorCellSemanticPairs, List.length_map, allOperatorCellSemanticRows_length]

theorem exactCellTransformDenotationRows_length :
    exactCellTransformDenotationRows.length = 8256 := by
  native_decide

theorem familyBackedDenotationRows_length :
    familyBackedDenotationRows.length = 8256 := by
  rw [familyBackedDenotationRows, exactCellTransformDenotationRows_length]

theorem signatureCarrierDenotationRows_length :
    signatureCarrierDenotationRows.length = 62976 := by
  native_decide

theorem machineDenotationRows_length :
    machineDenotationRows.length = 71232 := by
  rw [machineDenotationRows, allOperatorCellSemanticRows_length]

theorem executableCellTransformRows_length :
    executableCellTransformRows.length = 8256 := by
  rw [executableCellTransformRows, exactCellTransformDenotationRows_length]

theorem exactSignatureShapeRows_length :
    exactSignatureShapeRows.length = 0 := by
  native_decide

theorem catalogueSignatureShapeRows_length :
    catalogueSignatureShapeRows.length = 0 := by
  native_decide

theorem operatorCellDenotationKind_partition_counts :
    exactCellTransformDenotationRows.length
      + signatureCarrierDenotationRows.length
      = allOperatorCellSemanticRows.length := by
  rw [exactCellTransformDenotationRows_length, signatureCarrierDenotationRows_length,
    allOperatorCellSemanticRows_length]

theorem operatorCellSemanticStatus_counts_sum :
    executableCellTransformRows.length
      + signatureCarrierDenotationRows.length
      = allOperatorCellSemanticRows.length := by
  rw [executableCellTransformRows_length, signatureCarrierDenotationRows_length,
    allOperatorCellSemanticRows_length]

theorem operatorCellSemanticRow_denotation_supportCell
    (id : OperatorId) (cell : Cell192) :
    (operatorCellSemanticRow id cell).denotation.supportCell = cell := by
  unfold operatorCellSemanticRow operatorCellDenotationFor
  split <;> rfl

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

theorem operatorCellSemanticRows_denotation_complete
    (id : OperatorId) (cell : Cell192) :
    ∃ row, row ∈ allOperatorCellSemanticRows
      ∧ row.id = id
      ∧ row.cell = cell
      ∧ row.denotation.supportCell = cell := by
  refine ⟨operatorCellSemanticRow id cell, ?_, rfl, rfl, ?_⟩
  · unfold allOperatorCellSemanticRows operatorCellSemanticRowsFor
    exact List.mem_flatMap.mpr
      ⟨id, allOperatorIds_complete id,
        List.mem_map.mpr ⟨cell, Cell192.mem_all cell, rfl⟩⟩
  · exact operatorCellSemanticRow_denotation_supportCell id cell

theorem operatorCellSemanticRows_cuo_executable (cell : Cell192) :
    (operatorCellSemanticRow .Z_5 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .Z_5 cell).cellTransform? = some (Cell192.hexCuo cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_zong_executable (cell : Cell192) :
    (operatorCellSemanticRow .Z_6 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .Z_6 cell).cellTransform? = some (Cell192.hexZong cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_hu_executable (cell : Cell192) :
    (operatorCellSemanticRow .Z_3 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .Z_3 cell).cellTransform? = some (Cell192.hexHu cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_fan_executable (cell : Cell192) :
    (operatorCellSemanticRow .T_6 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_6 cell).cellTransform? = some (Cell192.hexCuo cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_tui_executable (cell : Cell192) :
    (operatorCellSemanticRow .T_10 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_10 cell).cellTransform? =
          some (SSBX.Foundation.Yi.YiCore.«生» cell.1, cell.2) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_sun_executable (cell : Cell192) :
    (operatorCellSemanticRow .T_12 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_12 cell).cellTransform? =
          some (SSBX.Foundation.Yi.YiCore.«加» SSBX.Foundation.Yi.Yi.Hexagram.kun cell.1, cell.2) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_hua_executable (cell : Cell192) :
    (operatorCellSemanticRow .T_1 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_1 cell).cellTransform? = some (Cell192.flip2 cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_bian_executable (cell : Cell192) :
    (operatorCellSemanticRow .T_2 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_2 cell).cellTransform? = some (Cell192.flip3 cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_fanOperator_executable (cell : Cell192) :
    (operatorCellSemanticRow .Z_31 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .Z_31 cell).cellTransform? = some (Cell192.hexCuo cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_fan_denotation (cell : Cell192) :
    (operatorCellSemanticRow .T_6 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform := by
  rfl

theorem operatorCellSemanticRows_R_1_signature_carrier (cell : Cell192) :
    (operatorCellSemanticRow .R_1 cell).denotationKind =
      OperatorCellDenotationKind.signatureCarrier
      ∧ (operatorCellSemanticRow .R_1 cell).denotation.supportCell = cell := by
  constructor <;> rfl

/--
Summary: all 71,232 pairs have theorem-level semantic coverage rows and total
machine denotations. Exact cell execution is attached only where a current
cell-transform family exists; the remaining rows are support-cell
signature-carrier denotations.
-/
theorem operator_cell_semantic_coverage_summary :
    allOperatorCellSemanticRows.length = 71232
    ∧ allOperatorCellSemanticPairs.length = 71232
    ∧ machineDenotationRows.length = 71232
    ∧ exactCellTransformDenotationRows.length = 8256
    ∧ signatureCarrierDenotationRows.length = 62976
    ∧ executableCellTransformRows.length = 8256
    ∧ exactCellTransformDenotationRows.length
        + signatureCarrierDenotationRows.length
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
        (operatorCellSemanticRow .Z_3 cell).cellTransform? = some (Cell192.hexHu cell))
    ∧ (∀ cell : Cell192,
        (operatorCellSemanticRow .T_6 cell).cellTransform? = some (Cell192.hexCuo cell)) := by
  exact
    ⟨ allOperatorCellSemanticRows_length
    , allOperatorCellSemanticPairs_length
    , machineDenotationRows_length
    , exactCellTransformDenotationRows_length
    , signatureCarrierDenotationRows_length
    , executableCellTransformRows_length
    , operatorCellDenotationKind_partition_counts
    , operatorCellSemanticRowsFor_length
    , operatorCellSemanticRows_signature_complete
    , fun cell => (operatorCellSemanticRows_cuo_executable cell).2
    , fun cell => (operatorCellSemanticRows_zong_executable cell).2
    , fun cell => (operatorCellSemanticRows_hu_executable cell).2
    , fun cell => (operatorCellSemanticRows_fan_executable cell).2
    ⟩

theorem operatorCellDenotation_total_summary :
    allOperatorCellSemanticRows.length = 71232
    ∧ machineDenotationRows.length = 71232
    ∧ exactCellTransformDenotationRows.length = 8256
    ∧ signatureCarrierDenotationRows.length = 62976
    ∧ exactCellTransformDenotationRows.length
        + signatureCarrierDenotationRows.length
        = machineDenotationRows.length
    ∧ (∀ id : OperatorId, ∀ cell : Cell192,
        ∃ row, row ∈ allOperatorCellSemanticRows
          ∧ row.id = id
          ∧ row.cell = cell
          ∧ row.denotation.supportCell = cell) := by
  exact
    ⟨ allOperatorCellSemanticRows_length
    , machineDenotationRows_length
    , exactCellTransformDenotationRows_length
    , signatureCarrierDenotationRows_length
    , by
        rw [exactCellTransformDenotationRows_length,
          signatureCarrierDenotationRows_length, machineDenotationRows_length]
    , operatorCellSemanticRows_denotation_complete
    ⟩

end SSBX.Text.OperatorCellSemantics
