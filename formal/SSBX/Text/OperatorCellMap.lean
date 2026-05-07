import SSBX.Text.OperatorReadings
import SSBX.Text.OperatorSignatures
import SSBX.Text.OperatorFamilySemantics
import SSBX.Text.OperatorCellSemantics
import SSBX.Text.OperatorAnchors

/-!
# OperatorCellMap — 396 文言算子 × 192 八卦单元

This file records the total indexing layer between the text catalogue and the
Bagua cell space.  It is deliberately weaker than a semantic interpretation:
every `OperatorId` is paired with every `Cell192`, while the stronger meaning
claims remain in the specialized anchor/semantics files.
-/

namespace SSBX.Text.OperatorCellMap

open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Text.OperatorSignatures
open SSBX.Text.OperatorFamilySemantics
open SSBX.Text.OperatorCellSemantics
open SSBX.Text.OperatorAnchors
open SSBX.Foundation.Bagua.Cell192

/-! ## § 1 Total operator-cell index -/

/-- A catalogue operator at one concrete 64-hexagram × 3-time cell. -/
abbrev OperatorCell : Type := OperatorId × Cell192

/--
The total 396 × 192 index.  This is a coverage grid, not a claim that each
operator has a distinct theorem-level semantics at each cell.
-/
def allOperatorCells : List OperatorCell :=
  allOperatorIds.flatMap fun id =>
    Cell192.all.map fun c => (id, c)

theorem allOperatorIds_length : allOperatorIds.length = 396 := by
  native_decide

theorem allOperatorIds_nodup : allOperatorIds.Nodup := by
  native_decide

theorem allOperatorCells_length : allOperatorCells.length = 76032 := by
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
    (operatorsForCell cell).length = 396 := by
  rw [operatorsForCell, List.length_map, allOperatorIds_length]

theorem indexedCellsForOperator_length (id : OperatorId) :
    (indexedCellsForOperator id).length = 192 := by
  rw [indexedCellsForOperator, Cell192.all_length]

theorem indexedOperatorsForCell_length (cell : Cell192) :
    (indexedOperatorsForCell cell).length = 396 := by
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

* 396 catalogue operator ids are registered.
* 192 Bagua cells are enumerated.
* the total coverage grid has 76,032 rows.
* every operator-cell pair is present in that grid.
* the more specific `OperatorAnchors` layer still covers every `Cell192`.
-/
theorem operator_cell_bagua_summary :
    allOperatorIds.length = 396
    ∧ Cell192.all.length = 192
    ∧ allOperatorCells.length = 76032
    ∧ allOperatorIds.Nodup
    ∧ Cell192.all.Nodup
    ∧ (∀ id : OperatorId, id ∈ allOperatorIds)
    ∧ (∀ c : Cell192, c ∈ Cell192.all)
    ∧ (∀ id : OperatorId, ∀ c : Cell192, (id, c) ∈ allOperatorCells)
    ∧ (∀ id : OperatorId, (cellsForOperator id).length = 192)
    ∧ (∀ cell : Cell192, (operatorsForCell cell).length = 396)
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
  | hexagramGapPromotions
  | exactSignatureSeeds
  | cellTransformFamilyLaws
  | semanticLowerBoundAudit
  | exactOperatorSignatures
  | operatorCellSemanticRows
  deriving Repr, DecidableEq, BEq

/-- Whether a layer is complete, explicitly tracked, or still pending. -/
inductive CompletionMark where
  | complete
  | tracked
  | pending
  deriving Repr, DecidableEq, BEq

/-! ## § 3a Semantic proof-obligation lower bounds -/

/--
Finite audit targets for semantic proof obligations.  These are intentionally
not the 396 × 192 pair grid: the pair grid is an index, while semantics should
be proved by parameterized families and generators.
-/
inductive SemanticLowerBoundKind where
  | exactCellTransformFamilies
  | cell192ReachabilityGenerators
  | l0InstructionClauses
  | coreTextSemanticFamilies
  deriving Repr, DecidableEq, BEq

structure SemanticLowerBoundRow where
  kind : SemanticLowerBoundKind
  scope : Nat
  deriving Repr, DecidableEq

/--
Current lower-bound audit for theorem families:

* 3 exact catalogue cell transforms: 错 / 综 / 互.
* 7 concrete `Cell192` reachability generators: six line flips plus one time edge.
* 12 BaguaWen L0 instruction clauses.
* 27 core text-level semantic families from the parameterized kernel draft.
-/
def semanticLowerBoundRows : List SemanticLowerBoundRow :=
  [ { kind := .exactCellTransformFamilies, scope := 3 }
  , { kind := .cell192ReachabilityGenerators, scope := 7 }
  , { kind := .l0InstructionClauses, scope := 12 }
  , { kind := .coreTextSemanticFamilies, scope := 27 }
  ]

theorem semanticLowerBoundRows_length :
    semanticLowerBoundRows.length = 4 := by
  native_decide

theorem semanticLowerBoundRows_scopes :
    semanticLowerBoundRows.map (·.scope) = [3, 7, 12, 27] := by
  native_decide

theorem parameterizedSemanticFamilies_lt_operatorCellGrid :
    27 < allOperatorCells.length := by
  rw [allOperatorCells_length]
  native_decide

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
The tracked rows retain seed / policy subledgers.  The requested completion
rows are explicit: all 396 operators have conservative signature coverage, all
76,032 operator-cell pairs have semantic rows, and the 25 formerly general
hexagram gap words have admitted catalogue ids while 6 gaps remain tracked.
-/
def functionalCompletionRows : List CompletionRow :=
  [ { layer := .catalogueOperators, mark := .complete, scope := 396 }
  , { layer := .baguaCells, mark := .complete, scope := 192 }
  , { layer := .operatorCellIndex, mark := .complete, scope := 76032 }
  , { layer := .baguaAnchors, mark := .complete, scope := 192 }
  , { layer := .homographReadings, mark := .complete, scope := 83 }
  , { layer := .exactOperatorSignatures, mark := .complete, scope := 396 }
  , { layer := .operatorCellSemanticRows, mark := .complete, scope := 76032 }
  , { layer := .hexagramGapPromotions, mark := .complete, scope := 25 }
  , { layer := .hexagramGapPolicies, mark := .tracked, scope := 6 }
  , { layer := .exactSignatureSeeds, mark := .tracked, scope := 14 }
  , { layer := .cellTransformFamilyLaws, mark := .tracked, scope := 3 }
  , { layer := .semanticLowerBoundAudit, mark := .tracked, scope := 4 }
  ]

def functionalCompletionCompleteRows : List CompletionRow :=
  functionalCompletionRows.filter (fun row => row.mark == CompletionMark.complete)

def functionalCompletionTrackedRows : List CompletionRow :=
  functionalCompletionRows.filter (fun row => row.mark == CompletionMark.tracked)

def functionalCompletionPendingRows : List CompletionRow :=
  functionalCompletionRows.filter (fun row => row.mark == CompletionMark.pending)

theorem functionalCompletionRows_length :
    functionalCompletionRows.length = 12 := by
  native_decide

theorem functionalCompletionCompleteRows_length :
    functionalCompletionCompleteRows.length = 8 := by
  native_decide

theorem functionalCompletionTrackedRows_length :
    functionalCompletionTrackedRows.length = 4 := by
  native_decide

theorem functionalCompletionPendingRows_length :
    functionalCompletionPendingRows.length = 0 := by
  native_decide

theorem functionalCompletionCompleteRows_eq :
    functionalCompletionCompleteRows =
      [ { layer := .catalogueOperators, mark := .complete, scope := 396 }
      , { layer := .baguaCells, mark := .complete, scope := 192 }
      , { layer := .operatorCellIndex, mark := .complete, scope := 76032 }
      , { layer := .baguaAnchors, mark := .complete, scope := 192 }
      , { layer := .homographReadings, mark := .complete, scope := 83 }
      , { layer := .exactOperatorSignatures, mark := .complete, scope := 396 }
      , { layer := .operatorCellSemanticRows, mark := .complete, scope := 76032 }
      , { layer := .hexagramGapPromotions, mark := .complete, scope := 25 }
      ] := by
  native_decide

theorem functionalCompletionTrackedRows_eq :
    functionalCompletionTrackedRows =
      [ { layer := .hexagramGapPolicies, mark := .tracked, scope := 6 }
      , { layer := .exactSignatureSeeds, mark := .tracked, scope := 14 }
      , { layer := .cellTransformFamilyLaws, mark := .tracked, scope := 3 }
      , { layer := .semanticLowerBoundAudit, mark := .tracked, scope := 4 }
      ] := by
  native_decide

theorem functionalCompletionPendingRows_eq :
    functionalCompletionPendingRows = [] := by
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
      , .exactOperatorSignatures
      , .operatorCellSemanticRows
      , .hexagramGapPromotions
      ] := by
  native_decide

theorem functionalCompletionTrackedLayers_eq :
    functionalCompletionTrackedRows.map (·.layer) =
      [ .hexagramGapPolicies
      , .exactSignatureSeeds
      , .cellTransformFamilyLaws
      , .semanticLowerBoundAudit
      ] := by
  native_decide

theorem functionalCompletionPendingLayers_eq :
    functionalCompletionPendingRows.map (·.layer) = [] := by
  native_decide

theorem functional_completion_summary :
    allOperatorIds.length = 396
    ∧ Cell192.all.length = 192
    ∧ allOperatorCells.length = 76032
    ∧ allOperatorIds.Nodup
    ∧ Cell192.all.Nodup
    ∧ (functionalCompletionRows.map (·.layer)).Nodup
    ∧ (∀ id : OperatorId, (indexedCellsForOperator id).length = 192)
    ∧ (∀ cell : Cell192, (indexedOperatorsForCell cell).length = 396)
    ∧ (∀ id : OperatorId, (cellsForOperator id).length = 192)
    ∧ (∀ cell : Cell192, (operatorsForCell cell).length = 396)
    ∧ cellOperatorAnchors.length = 192
    ∧ catalogueHomographReadings.length = 83
    ∧ allSurfaceReadings.length = 84
    ∧ (allSurfaceReadings.map (fun e => e.readings.length)).foldl Nat.add 0 = 197
    ∧ hexagramMissingPolicies.length = 6
    ∧ hexagramGapPromotions.length = 25
    ∧ hexagramUnpromotedGapForms = ["丽", "井", "鼎", "震", "大", "小"]
    ∧ hexagramNearMissAnchors.length = 7
    ∧ exactSignatureSeed.length = 14
    ∧ signedOperatorIds.Nodup
    ∧ fullOperatorSignatures.length = 396
    ∧ seedOverrideSignatureRows.length = 14
    ∧ groupDefaultSignatureRows.length = 382
    ∧ cellTransformKinds.length = 3
    ∧ cellTransformOperatorIds.all (fun id => decide (id ∈ signedOperatorIds)) = true
    ∧ allOperatorCellSemanticRows.length = 76032
    ∧ executableCellTransformRows.length = 576
    ∧ exactSignatureShapeRows.length = 2112
    ∧ groupDefaultSignatureShapeRows.length = 73344
    ∧ semanticLowerBoundRows.length = 4
    ∧ semanticLowerBoundRows.map (·.scope) = [3, 7, 12, 27]
    ∧ 27 < allOperatorCells.length
    ∧ functionalCompletionCompleteRows.length = 8
    ∧ functionalCompletionTrackedRows.length = 4
    ∧ functionalCompletionPendingRows.length = 0 := by
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
    , hexagramGapPromotions_length
    , hexagramUnpromotedGapForms_eq
    , hexagramNearMissAnchors_length
    , exactSignatureSeed_length
    , signedOperatorIds_nodup
    , fullOperatorSignatures_length
    , seedOverrideSignatureRows_length
    , groupDefaultSignatureRows_length
    , cellTransformKinds_length
    , cellTransformOperatorIds_have_signature_seed
    , allOperatorCellSemanticRows_length
    , executableCellTransformRows_length
    , exactSignatureShapeRows_length
    , groupDefaultSignatureShapeRows_length
    , semanticLowerBoundRows_length
    , semanticLowerBoundRows_scopes
    , parameterizedSemanticFamilies_lt_operatorCellGrid
    , functionalCompletionCompleteRows_length
    , functionalCompletionTrackedRows_length
    , functionalCompletionPendingRows_length
    ⟩

end SSBX.Text.OperatorCellMap
