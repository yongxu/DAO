import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8
import SSBX.Text.OperatorFamilySemantics
import SSBX.Text.OperatorSignatures

/-!
# OperatorCellSemantics — theorem-level coverage rows for operator-cell pairs

This file gives every `OperatorId × R8` pair a machine-checkable semantic
row.  It does not hand-write 94,976 denotational theorems.  Each row carries the
total text-level signature coverage and a conservative machine denotation. Exact
`R8` transform operators carry their concrete output cell; every remaining
operator carries a signature-preserving support-cell carrier, intentionally
weaker than a domain-specific meaning.
-/

namespace SSBX.Text.OperatorCellSemantics

open SSBX.Foundation.Bagua.R8
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorFamilySemantics
open SSBX.Text.OperatorSignatures

/--
Local R8 dispatch for `CellTransformKind`.

The upstream `CellTransformKind.apply` is typed for `Cell192`. Because R8
mirrors the same hex/shi product (with `Shi` upgraded to V₄), the same kinds
have direct R8 analogues, dispatched here without touching the upstream.
-/
def applyKindOnCell256 : CellTransformKind → R8 → R8
  | .id, c => c
  | .next64, c => (SSBX.Foundation.Yi.YiCore.«生» c.1, c.2)
  | .prev64, c => (SSBX.Foundation.Yi.YiCore.«加» SSBX.Foundation.Yi.Yi.Hexagram.earth c.1, c.2)
  | .complement, c => R8.hexCuo c
  | .reverse, c => R8.hexZong c
  | .interlace, c => R8.hexHu c
  | .complementReverse, c => (c.1.complementReverse, c.2)
  | .flip1, c => R8.flip1 c
  | .flip2, c => R8.flip2 c
  | .flip3, c => R8.flip3 c

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
  | exactTransform (kind : CellTransformKind) (input output : R8)
  | signatureCarrier (signatureKind : SignatureKind) (supportCell : R8)
  deriving Repr, DecidableEq

namespace OperatorCellDenotation

def kind : OperatorCellDenotation → OperatorCellDenotationKind
  | .exactTransform .. => .exactCellTransform
  | .signatureCarrier .. => .signatureCarrier

def supportCell : OperatorCellDenotation → R8
  | .exactTransform _ input _ => input
  | .signatureCarrier _ supportCell => supportCell

def transformedCell? : OperatorCellDenotation → Option R8
  | .exactTransform _ _ output => some output
  | .signatureCarrier .. => none

def isExactTransform (denotation : OperatorCellDenotation) : Bool :=
  denotation.kind == OperatorCellDenotationKind.exactCellTransform

def isSignatureCarrier (denotation : OperatorCellDenotation) : Bool :=
  denotation.kind == OperatorCellDenotationKind.signatureCarrier

end OperatorCellDenotation

structure OperatorCellSemanticRow where
  id : OperatorId
  cell : R8
  signature : CoveredOperatorSignature
  denotation : OperatorCellDenotation
  cellTransform? : Option R8
  denotationKind : OperatorCellDenotationKind
  deriving Repr

def operatorCellDenotationFor (id : OperatorId) (cell : R8) :
    OperatorCellDenotation :=
  match cellTransformForOperator? id with
  | some kind =>
      .exactTransform kind cell (applyKindOnCell256 kind cell)
  | none => .signatureCarrier (fullSignatureFor id).kind cell

/-- Compatibility wrapper for callers that still expect an optional denotation. -/
def operatorCellDenotationFor? (id : OperatorId) (cell : R8) :
    Option OperatorCellDenotation :=
  some (operatorCellDenotationFor id cell)

def operatorCellDenotationKindFor (id : OperatorId) (cell : R8) :
    OperatorCellDenotationKind :=
  (operatorCellDenotationFor id cell).kind

def operatorCellSemanticRow (id : OperatorId) (cell : R8) :
    OperatorCellSemanticRow :=
  let denotation := operatorCellDenotationFor id cell
  { id := id
  , cell := cell
  , signature := fullSignatureFor id
  , denotation := denotation
  , cellTransform? := denotation.transformedCell?
  , denotationKind := denotation.kind }

def operatorCellSemanticRowsFor (id : OperatorId) : List OperatorCellSemanticRow :=
  R8.all.map (operatorCellSemanticRow id)

/-- Total semantic coverage table for the 371 × 256 operator-cell grid. -/
def allOperatorCellSemanticRows : List OperatorCellSemanticRow :=
  allOperatorIds.flatMap operatorCellSemanticRowsFor

def allOperatorCellSemanticPairs : List (OperatorId × R8) :=
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
    (operatorCellSemanticRowsFor id).length = 256 := by
  rw [operatorCellSemanticRowsFor, List.length_map, R8.all_length]

theorem allOperatorCellSemanticRows_length :
    allOperatorCellSemanticRows.length = 94976 := by
  native_decide

theorem allOperatorCellSemanticPairs_length :
    allOperatorCellSemanticPairs.length = 94976 := by
  rw [allOperatorCellSemanticPairs, List.length_map, allOperatorCellSemanticRows_length]

theorem exactCellTransformDenotationRows_length :
    exactCellTransformDenotationRows.length = 11008 := by
  native_decide

theorem familyBackedDenotationRows_length :
    familyBackedDenotationRows.length = 11008 := by
  rw [familyBackedDenotationRows, exactCellTransformDenotationRows_length]

theorem signatureCarrierDenotationRows_length :
    signatureCarrierDenotationRows.length = 83968 := by
  native_decide

theorem machineDenotationRows_length :
    machineDenotationRows.length = 94976 := by
  rw [machineDenotationRows, allOperatorCellSemanticRows_length]

theorem executableCellTransformRows_length :
    executableCellTransformRows.length = 11008 := by
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
    (id : OperatorId) (cell : R8) :
    (operatorCellSemanticRow id cell).denotation.supportCell = cell := by
  unfold operatorCellSemanticRow operatorCellDenotationFor
  split <;> rfl

theorem operatorCellSemanticRow_signature_id (id : OperatorId) (cell : R8) :
    (operatorCellSemanticRow id cell).signature.id = id := by
  exact fullSignatureFor_id id

theorem operatorCellSemanticRows_complete_pair (id : OperatorId) (cell : R8) :
    ∃ row, row ∈ allOperatorCellSemanticRows ∧ row.id = id ∧ row.cell = cell := by
  refine ⟨operatorCellSemanticRow id cell, ?_, rfl, rfl⟩
  unfold allOperatorCellSemanticRows operatorCellSemanticRowsFor
  exact List.mem_flatMap.mpr
    ⟨id, allOperatorIds_complete id,
      List.mem_map.mpr ⟨cell, R8.mem_all cell, rfl⟩⟩

theorem operatorCellSemanticRows_signature_complete
    (id : OperatorId) (cell : R8) :
    ∃ row, row ∈ allOperatorCellSemanticRows
      ∧ row.id = id
      ∧ row.cell = cell
      ∧ row.signature.id = id := by
  refine ⟨operatorCellSemanticRow id cell, ?_, rfl, rfl, ?_⟩
  · unfold allOperatorCellSemanticRows operatorCellSemanticRowsFor
    exact List.mem_flatMap.mpr
      ⟨id, allOperatorIds_complete id,
        List.mem_map.mpr ⟨cell, R8.mem_all cell, rfl⟩⟩
  · exact operatorCellSemanticRow_signature_id id cell

theorem operatorCellSemanticRows_denotation_complete
    (id : OperatorId) (cell : R8) :
    ∃ row, row ∈ allOperatorCellSemanticRows
      ∧ row.id = id
      ∧ row.cell = cell
      ∧ row.denotation.supportCell = cell := by
  refine ⟨operatorCellSemanticRow id cell, ?_, rfl, rfl, ?_⟩
  · unfold allOperatorCellSemanticRows operatorCellSemanticRowsFor
    exact List.mem_flatMap.mpr
      ⟨id, allOperatorIds_complete id,
        List.mem_map.mpr ⟨cell, R8.mem_all cell, rfl⟩⟩
  · exact operatorCellSemanticRow_denotation_supportCell id cell

theorem operatorCellSemanticRows_cuo_executable (cell : R8) :
    (operatorCellSemanticRow .Z_5 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .Z_5 cell).cellTransform? = some (R8.hexCuo cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_zong_executable (cell : R8) :
    (operatorCellSemanticRow .Z_6 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .Z_6 cell).cellTransform? = some (R8.hexZong cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_hu_executable (cell : R8) :
    (operatorCellSemanticRow .Z_3 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .Z_3 cell).cellTransform? = some (R8.hexHu cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_fan_executable (cell : R8) :
    (operatorCellSemanticRow .T_6 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_6 cell).cellTransform? = some (R8.hexCuo cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_tui_executable (cell : R8) :
    (operatorCellSemanticRow .T_10 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_10 cell).cellTransform? =
          some (SSBX.Foundation.Yi.YiCore.«生» cell.1, cell.2) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_sun_executable (cell : R8) :
    (operatorCellSemanticRow .T_12 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_12 cell).cellTransform? =
          some (SSBX.Foundation.Yi.YiCore.«加» SSBX.Foundation.Yi.Yi.Hexagram.earth cell.1, cell.2) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_hua_executable (cell : R8) :
    (operatorCellSemanticRow .T_1 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_1 cell).cellTransform? = some (R8.flip2 cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_bian_executable (cell : R8) :
    (operatorCellSemanticRow .T_2 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .T_2 cell).cellTransform? = some (R8.flip3 cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_fanOperator_executable (cell : R8) :
    (operatorCellSemanticRow .Z_31 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform
      ∧ (operatorCellSemanticRow .Z_31 cell).cellTransform? = some (R8.hexCuo cell) := by
  constructor <;> rfl

theorem operatorCellSemanticRows_fan_denotation (cell : R8) :
    (operatorCellSemanticRow .T_6 cell).denotationKind =
      OperatorCellDenotationKind.exactCellTransform := by
  rfl

theorem operatorCellSemanticRows_R_1_signature_carrier (cell : R8) :
    (operatorCellSemanticRow .R_1 cell).denotationKind =
      OperatorCellDenotationKind.signatureCarrier
      ∧ (operatorCellSemanticRow .R_1 cell).denotation.supportCell = cell := by
  constructor <;> rfl

/--
Summary: all 94,976 pairs have theorem-level semantic coverage rows and total
machine denotations. Exact cell execution is attached only where a current
cell-transform family exists; the remaining rows are support-cell
signature-carrier denotations.
-/
theorem operator_cell_semantic_coverage_summary :
    allOperatorCellSemanticRows.length = 94976
    ∧ allOperatorCellSemanticPairs.length = 94976
    ∧ machineDenotationRows.length = 94976
    ∧ exactCellTransformDenotationRows.length = 11008
    ∧ signatureCarrierDenotationRows.length = 83968
    ∧ executableCellTransformRows.length = 11008
    ∧ exactCellTransformDenotationRows.length
        + signatureCarrierDenotationRows.length
        = allOperatorCellSemanticRows.length
    ∧ (∀ id : OperatorId, (operatorCellSemanticRowsFor id).length = 256)
    ∧ (∀ id : OperatorId, ∀ cell : R8,
        ∃ row, row ∈ allOperatorCellSemanticRows
          ∧ row.id = id
          ∧ row.cell = cell
          ∧ row.signature.id = id)
    ∧ (∀ cell : R8,
        (operatorCellSemanticRow .Z_5 cell).cellTransform? = some (R8.hexCuo cell))
    ∧ (∀ cell : R8,
        (operatorCellSemanticRow .Z_6 cell).cellTransform? = some (R8.hexZong cell))
    ∧ (∀ cell : R8,
        (operatorCellSemanticRow .Z_3 cell).cellTransform? = some (R8.hexHu cell))
    ∧ (∀ cell : R8,
        (operatorCellSemanticRow .T_6 cell).cellTransform? = some (R8.hexCuo cell)) := by
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
    allOperatorCellSemanticRows.length = 94976
    ∧ machineDenotationRows.length = 94976
    ∧ exactCellTransformDenotationRows.length = 11008
    ∧ signatureCarrierDenotationRows.length = 83968
    ∧ exactCellTransformDenotationRows.length
        + signatureCarrierDenotationRows.length
        = machineDenotationRows.length
    ∧ (∀ id : OperatorId, ∀ cell : R8,
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
