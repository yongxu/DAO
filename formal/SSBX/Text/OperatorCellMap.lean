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
    ∧ (∀ id : OperatorId, id ∈ allOperatorIds)
    ∧ (∀ c : Cell192, c ∈ Cell192.all)
    ∧ (∀ id : OperatorId, ∀ c : Cell192, (id, c) ∈ allOperatorCells)
    ∧ (∀ c : Cell192, cellCovered c = true) := by
  exact
    ⟨ allOperatorIds_length
    , Cell192.all_length
    , allOperatorCells_length
    , allOperatorIds_complete
    , Cell192.mem_all
    , allOperatorCells_complete_pair
    , cellOperatorAnchors_cover_all
    ⟩

end SSBX.Text.OperatorCellMap
