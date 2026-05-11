/-
# ExactCellTransformGenerator -- generated exact rows, not ontology tables

This file makes explicit the roadmap boundary:

* exact cell transforms are generated from parameterized operator families;
* the checked exact row count is 43 operator ids x 256 R8 cells = 11008;
* the 94976 operator-cell grid is coverage, not an ontology of exact meaning.
-/

import SSBX.Text.OperatorCellSemantics

namespace SSBX.Text.ExactCellTransformGenerator

open SSBX.Foundation.Bagua.R8
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorFamilySemantics
open SSBX.Text.OperatorCellSemantics

/-! ## Generated exact rows -/

/-- Generated exact row keys: exact-transform operator id paired with each R8 cell. -/
def generatedExactCellTransformKeys : List (OperatorId × R8) :=
  cellTransformOperatorIds.flatMap fun id =>
    R8.all.map fun cell => (id, cell)

/-- Generate the exact denotation for an exact-transform row key. -/
def generatedExactCellTransformDenotation (id : OperatorId) (cell : R8) :
    Option OperatorCellDenotation :=
  match cellTransformForOperator? id with
  | some kind => some (.exactTransform kind cell (applyKindOnCell256 kind cell))
  | none => none

theorem generatedExactCellTransformKeys_length :
    generatedExactCellTransformKeys.length = 11008 := by
  native_decide

theorem exact_transform_operator_id_count :
    cellTransformOperatorIds.length = 43 := by
  exact cellTransformOperatorIds_length

theorem exact_transform_cell_count :
    R8.all.length = 256 := by
  exact R8.all_length

theorem exact_transform_product_count :
    cellTransformOperatorIds.length * R8.all.length = 11008 := by
  rw [cellTransformOperatorIds_length, R8.all_length]

theorem checked_exact_rows_match_generated_count :
    exactCellTransformDenotationRows.length =
      cellTransformOperatorIds.length * R8.all.length := by
  rw [exactCellTransformDenotationRows_length, cellTransformOperatorIds_length, R8.all_length]

theorem checked_exact_rows_count :
    exactCellTransformDenotationRows.length = 11008 := by
  exact exactCellTransformDenotationRows_length

theorem coverage_grid_count :
    allOperatorCellSemanticRows.length = 94976 := by
  exact allOperatorCellSemanticRows_length

theorem signature_carrier_count :
    signatureCarrierDenotationRows.length = 83968 := by
  exact signatureCarrierDenotationRows_length

theorem exact_plus_signature_partition :
    exactCellTransformDenotationRows.length
      + signatureCarrierDenotationRows.length
      = allOperatorCellSemanticRows.length := by
  exact operatorCellDenotationKind_partition_counts

/-- Every listed exact-transform operator id has a generator. -/
theorem exact_transform_operator_ids_have_generators :
    cellTransformOperatorIds.all (fun id => (cellTransformForOperator? id).isSome) = true := by
  native_decide

/-- Summary theorem: exact rows are generated; the larger grid remains coverage. -/
theorem exact_cell_transform_generator_summary :
    cellTransformOperatorIds.length = 43
    ∧ R8.all.length = 256
    ∧ cellTransformOperatorIds.length * R8.all.length = 11008
    ∧ generatedExactCellTransformKeys.length = 11008
    ∧ exactCellTransformDenotationRows.length = 11008
    ∧ signatureCarrierDenotationRows.length = 83968
    ∧ allOperatorCellSemanticRows.length = 94976
    ∧ exactCellTransformDenotationRows.length
        + signatureCarrierDenotationRows.length
        = allOperatorCellSemanticRows.length
    ∧ cellTransformOperatorIds.all (fun id => (cellTransformForOperator? id).isSome) = true := by
  exact
    ⟨ exact_transform_operator_id_count
    , exact_transform_cell_count
    , exact_transform_product_count
    , generatedExactCellTransformKeys_length
    , checked_exact_rows_count
    , signature_carrier_count
    , coverage_grid_count
    , exact_plus_signature_partition
    , exact_transform_operator_ids_have_generators
    ⟩

end SSBX.Text.ExactCellTransformGenerator
