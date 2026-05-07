import SSBX.Text.OperatorReadings
import SSBX.Text.OperatorAnchors

/-!
# OperatorCellMap — 371 文言算子 × 192 八卦单元

This file records the total indexing layer between the text catalogue and the
Bagua cell space.  It is deliberately weaker than a semantic interpretation:
every `OperatorId` is paired with every `Cell192`, while the stronger meaning
claims remain in the specialized anchor/semantics files.
-/

namespace SSBX.Text.OperatorCellMap

open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Text.OperatorAnchors
open SSBX.Foundation.Bagua.Cell192

/-! ## § 1 Total operator-cell index -/

/-- A catalogue operator at one concrete 64-hexagram × 3-time cell. -/
abbrev OperatorCell : Type := OperatorId × Cell192

/--
The total 371 × 192 index.  This is a coverage grid, not a claim that each
operator has a distinct theorem-level semantics at each cell.
-/
def allOperatorCells : List OperatorCell :=
  allOperatorIds.flatMap fun id =>
    Cell192.all.map fun c => (id, c)

theorem allOperatorIds_length : allOperatorIds.length = 371 := by
  native_decide

theorem allOperatorIds_nodup : allOperatorIds.Nodup := by
  native_decide

theorem allOperatorCells_length : allOperatorCells.length = 71232 := by
  native_decide

theorem allOperatorCells_length_product :
    allOperatorCells.length = allOperatorIds.length * Cell192.all.length := by
  rw [allOperatorCells_length, allOperatorIds_length, Cell192.all_length]

theorem allOperatorCells_complete (p : OperatorCell) :
    p ∈ allOperatorCells := by
  rcases p with ⟨id, c⟩
  unfold allOperatorCells
  exact List.mem_flatMap.mpr
    ⟨id, allOperatorIds_complete id,
      List.mem_map.mpr ⟨c, Cell192.mem_all c, rfl⟩⟩

theorem allOperatorCells_complete_pair (id : OperatorId) (c : Cell192) :
    (id, c) ∈ allOperatorCells := by
  exact allOperatorCells_complete (id, c)

/-- The row fiber of the total grid at a fixed operator. -/
def cellsForOperator (id : OperatorId) : List OperatorCell :=
  Cell192.all.map fun c => (id, c)

/-- The column fiber of the total grid at a fixed Bagua cell. -/
def operatorsForCell (cell : Cell192) : List OperatorCell :=
  allOperatorIds.map fun id => (id, cell)

/-- Projection of the total index at a fixed operator. -/
def indexedCellsForOperator (_id : OperatorId) : List Cell192 :=
  Cell192.all

/-- Projection of the total index at a fixed Bagua cell. -/
def indexedOperatorsForCell (_cell : Cell192) : List OperatorId :=
  allOperatorIds

theorem cellsForOperator_length (id : OperatorId) :
    (cellsForOperator id).length = 192 := by
  rw [cellsForOperator, List.length_map, Cell192.all_length]

theorem operatorsForCell_length (cell : Cell192) :
    (operatorsForCell cell).length = 371 := by
  rw [operatorsForCell, List.length_map, allOperatorIds_length]

theorem indexedCellsForOperator_length (id : OperatorId) :
    (indexedCellsForOperator id).length = 192 := by
  rw [indexedCellsForOperator, Cell192.all_length]

theorem indexedOperatorsForCell_length (cell : Cell192) :
    (indexedOperatorsForCell cell).length = 371 := by
  rw [indexedOperatorsForCell, allOperatorIds_length]

theorem indexedCellsForOperator_complete (id : OperatorId) (cell : Cell192) :
    cell ∈ indexedCellsForOperator id
      ∧ (id, cell) ∈ allOperatorCells := by
  exact ⟨Cell192.mem_all cell, allOperatorCells_complete_pair id cell⟩

theorem cellsForOperator_complete (id : OperatorId) (cell : Cell192) :
    (id, cell) ∈ cellsForOperator id
      ∧ (id, cell) ∈ allOperatorCells := by
  exact
    ⟨List.mem_map.mpr ⟨cell, Cell192.mem_all cell, rfl⟩,
      allOperatorCells_complete_pair id cell⟩

theorem indexedOperatorsForCell_complete (cell : Cell192) (id : OperatorId) :
    id ∈ indexedOperatorsForCell cell
      ∧ (id, cell) ∈ allOperatorCells := by
  exact ⟨allOperatorIds_complete id, allOperatorCells_complete_pair id cell⟩

theorem operatorsForCell_complete (cell : Cell192) (id : OperatorId) :
    (id, cell) ∈ operatorsForCell cell
      ∧ (id, cell) ∈ allOperatorCells := by
  exact
    ⟨List.mem_map.mpr ⟨id, allOperatorIds_complete id, rfl⟩,
      allOperatorCells_complete_pair id cell⟩

theorem allOperatorCells_operator_mem (p : OperatorCell) :
    p ∈ allOperatorCells → p.1 ∈ allOperatorIds := by
  intro h
  rcases p with ⟨op, cell⟩
  unfold allOperatorCells at h
  rcases List.mem_flatMap.mp h with ⟨id, hid, hp⟩
  rcases List.mem_map.mp hp with ⟨c, _hc, hpair⟩
  cases hpair
  exact hid

theorem allOperatorCells_cell_mem (p : OperatorCell) :
    p ∈ allOperatorCells → p.2 ∈ Cell192.all := by
  intro h
  rcases p with ⟨op, cell⟩
  unfold allOperatorCells at h
  rcases List.mem_flatMap.mp h with ⟨id, _hid, hp⟩
  rcases List.mem_map.mp hp with ⟨c, hc, hpair⟩
  cases hpair
  exact hc

/-! ## § 2 Bagua coverage summary -/

/--
Machine-checkable summary for the text/Bagua bridge:

* 371 catalogue operator ids are registered.
* 192 Bagua cells are enumerated.
* the total coverage grid has 71,232 rows.
* every operator-cell pair is present in that grid.
* the more specific `OperatorAnchors` layer still covers every `Cell192`.
-/
theorem operator_cell_bagua_summary :
    allOperatorIds.length = 371
    ∧ Cell192.all.length = 192
    ∧ allOperatorCells.length = 71232
    ∧ allOperatorIds.Nodup
    ∧ Cell192.all.Nodup
    ∧ (∀ id : OperatorId, id ∈ allOperatorIds)
    ∧ (∀ c : Cell192, c ∈ Cell192.all)
    ∧ (∀ id : OperatorId, ∀ c : Cell192, (id, c) ∈ allOperatorCells)
    ∧ (∀ id : OperatorId, (cellsForOperator id).length = 192)
    ∧ (∀ cell : Cell192, (operatorsForCell cell).length = 371)
    ∧ (∀ c : Cell192, cellCovered c = true) := by
  exact
    ⟨ allOperatorIds_length
    , Cell192.all_length
    , allOperatorCells_length
    , allOperatorIds_nodup
    , Cell192.all_nodup
    , allOperatorIds_complete
    , Cell192.mem_all
    , allOperatorCells_complete_pair
    , cellsForOperator_length
    , operatorsForCell_length
    , cellOperatorAnchors_cover_all
    ⟩

/-! ## § 3 Completion-level status -/

/-- Coarse layers used to distinguish coverage from semantic interpretation. -/
inductive CompletionLayer where
  | catalogueOperators
  | baguaCells
  | operatorCellIndex
  | baguaAnchors
  | homographReadings
  | hexagramGapPolicies
  | exactOperatorSignatures
  | theoremLevelCellSemantics
  deriving Repr, DecidableEq, BEq

/-- Whether a layer is complete, explicitly tracked, or still pending. -/
inductive CompletionMark where
  | complete
  | tracked
  | pending
  deriving Repr, DecidableEq, BEq

/--
A compact status row.  `scope` is the size of the layer being described, not a
claim that pending rows have already been semantically proved.
-/
structure CompletionRow where
  layer : CompletionLayer
  mark : CompletionMark
  scope : Nat
  deriving Repr, DecidableEq

/--
Functional completion ledger for the current text/Bagua bridge.

The first five rows are complete for the current catalogue and Bagua universe.
The gap-policy row is tracked but not promoted into exact catalogue ids.  The
last two rows are intentionally pending: exact signatures and theorem-level
cell semantics are stronger claims than enumeration.
-/
def functionalCompletionRows : List CompletionRow :=
  [ { layer := .catalogueOperators, mark := .complete, scope := 371 }
  , { layer := .baguaCells, mark := .complete, scope := 192 }
  , { layer := .operatorCellIndex, mark := .complete, scope := 71232 }
  , { layer := .baguaAnchors, mark := .complete, scope := 192 }
  , { layer := .homographReadings, mark := .complete, scope := 81 }
  , { layer := .hexagramGapPolicies, mark := .tracked, scope := 31 }
  , { layer := .exactOperatorSignatures, mark := .pending, scope := 371 }
  , { layer := .theoremLevelCellSemantics, mark := .pending, scope := 71232 }
  ]

def functionalCompletionCompleteRows : List CompletionRow :=
  functionalCompletionRows.filter (fun row => row.mark == CompletionMark.complete)

def functionalCompletionTrackedRows : List CompletionRow :=
  functionalCompletionRows.filter (fun row => row.mark == CompletionMark.tracked)

def functionalCompletionPendingRows : List CompletionRow :=
  functionalCompletionRows.filter (fun row => row.mark == CompletionMark.pending)

theorem functionalCompletionRows_length :
    functionalCompletionRows.length = 8 := by
  native_decide

theorem functionalCompletionCompleteRows_length :
    functionalCompletionCompleteRows.length = 5 := by
  native_decide

theorem functionalCompletionTrackedRows_length :
    functionalCompletionTrackedRows.length = 1 := by
  native_decide

theorem functionalCompletionPendingRows_length :
    functionalCompletionPendingRows.length = 2 := by
  native_decide

theorem functionalCompletionCompleteRows_eq :
    functionalCompletionCompleteRows =
      [ { layer := .catalogueOperators, mark := .complete, scope := 371 }
      , { layer := .baguaCells, mark := .complete, scope := 192 }
      , { layer := .operatorCellIndex, mark := .complete, scope := 71232 }
      , { layer := .baguaAnchors, mark := .complete, scope := 192 }
      , { layer := .homographReadings, mark := .complete, scope := 81 }
      ] := by
  native_decide

theorem functionalCompletionTrackedRows_eq :
    functionalCompletionTrackedRows =
      [ { layer := .hexagramGapPolicies, mark := .tracked, scope := 31 } ] := by
  native_decide

theorem functionalCompletionPendingRows_eq :
    functionalCompletionPendingRows =
      [ { layer := .exactOperatorSignatures, mark := .pending, scope := 371 }
      , { layer := .theoremLevelCellSemantics, mark := .pending, scope := 71232 }
      ] := by
  native_decide

theorem functionalCompletionLayers_nodup :
    (functionalCompletionRows.map (·.layer)).Nodup := by
  native_decide

theorem functionalCompletionCompleteLayers_eq :
    functionalCompletionCompleteRows.map (·.layer) =
      [ .catalogueOperators
      , .baguaCells
      , .operatorCellIndex
      , .baguaAnchors
      , .homographReadings
      ] := by
  native_decide

theorem functionalCompletionTrackedLayers_eq :
    functionalCompletionTrackedRows.map (·.layer) =
      [ .hexagramGapPolicies ] := by
  native_decide

theorem functionalCompletionPendingLayers_eq :
    functionalCompletionPendingRows.map (·.layer) =
      [ .exactOperatorSignatures
      , .theoremLevelCellSemantics
      ] := by
  native_decide

theorem functional_completion_summary :
    allOperatorIds.length = 371
    ∧ Cell192.all.length = 192
    ∧ allOperatorCells.length = 71232
    ∧ allOperatorIds.Nodup
    ∧ Cell192.all.Nodup
    ∧ (functionalCompletionRows.map (·.layer)).Nodup
    ∧ (∀ id : OperatorId, (indexedCellsForOperator id).length = 192)
    ∧ (∀ cell : Cell192, (indexedOperatorsForCell cell).length = 371)
    ∧ (∀ id : OperatorId, (cellsForOperator id).length = 192)
    ∧ (∀ cell : Cell192, (operatorsForCell cell).length = 371)
    ∧ cellOperatorAnchors.length = 192
    ∧ catalogueHomographReadings.length = 81
    ∧ allSurfaceReadings.length = 82
    ∧ (allSurfaceReadings.map (fun e => e.readings.length)).foldl Nat.add 0 = 193
    ∧ hexagramMissingPolicies.length = 31
    ∧ hexagramNearMissAnchors.length = 7
    ∧ functionalCompletionCompleteRows.length = 5
    ∧ functionalCompletionTrackedRows.length = 1
    ∧ functionalCompletionPendingRows.length = 2 := by
  exact
    ⟨ allOperatorIds_length
    , Cell192.all_length
    , allOperatorCells_length
    , allOperatorIds_nodup
    , Cell192.all_nodup
    , functionalCompletionLayers_nodup
    , indexedCellsForOperator_length
    , indexedOperatorsForCell_length
    , cellsForOperator_length
    , operatorsForCell_length
    , cellOperatorAnchors_length
    , catalogue_homograph_surface_count
    , all_surface_readings_count
    , all_surface_total_reading_count
    , hexagramMissingPolicies_length
    , hexagramNearMissAnchors_length
    , functionalCompletionCompleteRows_length
    , functionalCompletionTrackedRows_length
    , functionalCompletionPendingRows_length
    ⟩

end SSBX.Text.OperatorCellMap
