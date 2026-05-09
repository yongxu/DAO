/-
# WenSurface.Coverage — surface-facing catalogue coverage checks

This module does not duplicate the text catalogue proofs.  It imports the
existing coverage ledgers and exposes the counts that matter to WenSurface:
surface readings are resolvable/diagnosable, all 371 operator ids have total
signatures, and only registry-marked rows are executable.
-/
import SSBX.Foundation.Wen.WenSurface.Semantics
import SSBX.Foundation.Wen.WenSurface.Reading
import SSBX.Text.OperatorCellMap
import SSBX.Text.OperatorCellSemantics

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Text.OperatorSignatures
open SSBX.Text.OperatorAnchors
open SSBX.Text.OperatorCellMap
open SSBX.Text.OperatorCellSemantics

/-! ## § 1 Catalogue counts surfaced to WenSurface -/

theorem wenSurface_reading_catalogue_counts :
    allSurfaceReadings.length = 82
      ∧ (allSurfaceReadings.map (fun e => e.readings.length)).foldl Nat.add 0 = 193 := by
  exact ⟨all_surface_readings_count, all_surface_total_reading_count⟩

theorem wenSurface_hex_literal_counts :
    canonicalHexNames.length = 64
      ∧ canonicalHexNameRows.length = 64
      ∧ canonicalHexNameRows.map Prod.snd = SSBX.Foundation.Bagua.Cell192.xuGua
      ∧ hexagramGapPromotions.length = 25
      ∧ hexagramUnpromotedGapForms = ["丽", "井", "鼎", "震", "大", "小"]
      ∧ (canonicalHexNames.filter (fun s => decide (s.toList.length > 1))).all
          lexesAsSingleSurface = true
      ∧ ((hexNameAliases.map Prod.fst).filter (fun s => decide (s.toList.length > 1))).all
          lexesAsSingleSurface = true := by
  exact
    ⟨ canonicalHexNames_length
    , canonicalHexNameRows_length
    , canonicalHexNameRows_hexagrams_eq_xuGua
    , hexagramGapPromotions_length
    , hexagramUnpromotedGapForms_eq
    , canonicalMultiHexNames_lex_as_single
    , hexNameAliasSurfaces_lex_as_single
    ⟩

theorem coverage_counts :
    allSurfaceReadings.length = 82
      ∧ (allSurfaceReadings.map (fun e => e.readings.length)).foldl Nat.add 0 = 193
      ∧ allOperatorIds.length = 371
      ∧ SSBX.Text.OperatorCellMap.allOperatorCells.length = 71232
      ∧ allOperatorCellSemanticRows.length = 71232 := by
  exact
    ⟨ all_surface_readings_count
    , all_surface_total_reading_count
    , allOperatorIds_length
    , allOperatorCells_length
    , allOperatorCellSemanticRows_length
    ⟩

theorem wenSurface_operator_catalogue_counts :
    fullOperatorSignatures.length = 371
      ∧ operatorRegistryEntries.length = 371
      ∧ executableRegistryEntries.length = 371
      ∧ theoremBackedOperatorIds.length = 317
      ∧ exactTheoremBackedStrongOperatorIds.length = 139
      ∧ exactStructuralHelperOperatorIds.length = 19
      ∧ structuralCarrierOperatorIds.length = 178
      ∧ catalogueNormalFormOperatorIds.length = 54
      ∧ allOperatorIds.all (fun id => !(operatorForms id).isEmpty) = true := by
  exact
    ⟨ fullOperatorSignatures_length
    , operatorRegistryEntries_length
    , executableRegistryEntries_length
    , theoremBackedOperatorIds_length
    , exactTheoremBackedStrongOperatorIds_length
    , exactStructuralHelperOperatorIds_length
    , structuralCarrierOperatorIds_length
    , catalogueNormalFormOperatorIds_length
    , by native_decide
    ⟩

theorem wenSurface_operator_compound_surface_lex_coverage :
    (operatorCompoundSurfaceIds.map Prod.fst).all lexesAsSingleSurface = true :=
  operatorCompoundSurfaces_lex_as_single

theorem wenSurface_operator_cell_catalogue_counts :
    allOperatorCellSemanticRows.length = 71232
      ∧ allOperatorCellSemanticPairs.length = 71232 := by
  exact
    ⟨ allOperatorCellSemanticRows_length
    , allOperatorCellSemanticPairs_length
    ⟩

/-! ## § 2 Complete-but-gated execution contract -/

theorem wenSurface_registry_total_signature (id : OperatorId) :
    (operatorRegistryEntryFor id).signature.id = id :=
  operatorRegistryEntryFor_signature_id id

theorem wenSurface_registry_summary :
    allSurfaceReadings.length = 82
      ∧ (allSurfaceReadings.map (fun e => e.readings.length)).foldl Nat.add 0 = 193
      ∧ fullOperatorSignatures.length = 371
      ∧ allOperatorCellSemanticRows.length = 71232
      ∧ operatorRegistryEntries.length = 371
      ∧ executableRegistryEntries.length = 371
      ∧ theoremBackedOperatorIds.length = 317
      ∧ exactTheoremBackedStrongOperatorIds.length = 139
      ∧ exactStructuralHelperOperatorIds.length = 19
      ∧ structuralCarrierOperatorIds.length = 178
      ∧ catalogueNormalFormOperatorIds.length = 54
      ∧ allOperatorIds.all (fun id => !(operatorForms id).isEmpty) = true
      ∧ executableOperatorIds.all isCatalogueOperator = true
      ∧ (∀ id : OperatorId, (operatorRegistryEntryFor id).signature.id = id) := by
  exact
    ⟨ all_surface_readings_count
    , all_surface_total_reading_count
    , fullOperatorSignatures_length
    , allOperatorCellSemanticRows_length
    , operatorRegistryEntries_length
    , executableRegistryEntries_length
    , theoremBackedOperatorIds_length
    , exactTheoremBackedStrongOperatorIds_length
    , exactStructuralHelperOperatorIds_length
    , structuralCarrierOperatorIds_length
    , catalogueNormalFormOperatorIds_length
    , by native_decide
    , executableOperatorIds_registered
    , wenSurface_registry_total_signature
    ⟩

theorem wenSurface_reuses_bagua_grid_summary :
    allOperatorIds.length = 371
      ∧ SSBX.Foundation.Bagua.Cell192.Cell192.all.length = 192
      ∧ SSBX.Text.OperatorCellMap.allOperatorCells.length = 71232 :=
  ⟨ allOperatorIds_length
  , SSBX.Foundation.Bagua.Cell192.Cell192.all_length
  , allOperatorCells_length
  ⟩

theorem wenSurface_reuses_operator_cell_semantic_summary :
    allOperatorCellSemanticRows.length = 71232
      ∧ allOperatorCellSemanticPairs.length = 71232
      ∧ familyBackedDenotationRows.length = 8256 :=
  ⟨ (operator_cell_semantic_coverage_summary).1
  , (operator_cell_semantic_coverage_summary).2.1
  , (operator_cell_semantic_coverage_summary).2.2.1
  ⟩

/-! ## § 3 Current execution examples -/

example : (operatorRegistryEntryFor .T_10).executable?.isSome = true := by native_decide
example : (operatorRegistryEntryFor .Z_5).executable?.isSome = true := by native_decide
example : (operatorRegistryEntryFor .R_1).executable?.isSome = true := by native_decide
example : isTheoremBackedOperator .R_1 = true := by native_decide
example : (operatorRegistryEntryFor .S_1).signature.arity = 2 := by native_decide

end SSBX.Foundation.Wen.WenSurface
