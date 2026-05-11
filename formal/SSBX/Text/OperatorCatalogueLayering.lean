/-
# OperatorCatalogueLayering -- 371 catalogue ids as interpretation layer

This file records the catalogue-layer boundary:

* 371 is the Wen operator catalogue size;
* 43 ids currently have exact R8 cell-transform generators;
* the remaining 328 ids are conservative signature/domain-pending carriers;
* row counts are products with the 256-cell R8 carrier.
-/

import SSBX.Text.ExactCellTransformGenerator

namespace SSBX.Text.OperatorCatalogueLayering

open SSBX.Foundation.Bagua.R8
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorFamilySemantics
open SSBX.Text.OperatorCellSemantics
open SSBX.Text.ExactCellTransformGenerator

/-! ## Catalogue-layer partitions -/

/-- Catalogue ids that do not currently have exact R8 cell-transform semantics. -/
def nonExactCatalogueOperatorIds : List OperatorId :=
  allOperatorIds.filter (fun id => (cellTransformForOperator? id).isNone)

theorem catalogue_operator_count :
    allOperatorIds.length = 371 := by
  native_decide

theorem exact_catalogue_operator_count :
    cellTransformOperatorIds.length = 43 := by
  exact cellTransformOperatorIds_length

theorem nonExactCatalogueOperatorIds_length :
    nonExactCatalogueOperatorIds.length = 328 := by
  native_decide

theorem catalogue_operator_partition_count :
    cellTransformOperatorIds.length + nonExactCatalogueOperatorIds.length =
      allOperatorIds.length := by
  rw [cellTransformOperatorIds_length, nonExactCatalogueOperatorIds_length,
    catalogue_operator_count]

theorem non_exact_row_product_count :
    nonExactCatalogueOperatorIds.length * R8.all.length = 83968 := by
  rw [nonExactCatalogueOperatorIds_length, R8.all_length]

theorem exact_row_product_count :
    cellTransformOperatorIds.length * R8.all.length = 11008 := by
  exact exact_transform_product_count

theorem catalogue_row_product_count :
    allOperatorIds.length * R8.all.length = 94976 := by
  rw [catalogue_operator_count, R8.all_length]

theorem signature_carrier_rows_match_non_exact_product :
    signatureCarrierDenotationRows.length =
      nonExactCatalogueOperatorIds.length * R8.all.length := by
  rw [signatureCarrierDenotationRows_length, nonExactCatalogueOperatorIds_length,
    R8.all_length]

theorem exact_rows_match_exact_product :
    exactCellTransformDenotationRows.length =
      cellTransformOperatorIds.length * R8.all.length := by
  exact checked_exact_rows_match_generated_count

theorem all_semantic_rows_match_catalogue_product :
    allOperatorCellSemanticRows.length =
      allOperatorIds.length * R8.all.length := by
  rw [allOperatorCellSemanticRows_length, catalogue_operator_count, R8.all_length]

/-- Summary theorem for the 371 catalogue layering boundary. -/
theorem operator_catalogue_layering_summary :
    allOperatorIds.length = 371
    ∧ cellTransformOperatorIds.length = 43
    ∧ nonExactCatalogueOperatorIds.length = 328
    ∧ cellTransformOperatorIds.length + nonExactCatalogueOperatorIds.length =
        allOperatorIds.length
    ∧ exactCellTransformDenotationRows.length =
        cellTransformOperatorIds.length * R8.all.length
    ∧ signatureCarrierDenotationRows.length =
        nonExactCatalogueOperatorIds.length * R8.all.length
    ∧ allOperatorCellSemanticRows.length =
        allOperatorIds.length * R8.all.length := by
  exact
    ⟨ catalogue_operator_count
    , exact_catalogue_operator_count
    , nonExactCatalogueOperatorIds_length
    , catalogue_operator_partition_count
    , exact_rows_match_exact_product
    , signature_carrier_rows_match_non_exact_product
    , all_semantic_rows_match_catalogue_product
    ⟩

end SSBX.Text.OperatorCatalogueLayering
