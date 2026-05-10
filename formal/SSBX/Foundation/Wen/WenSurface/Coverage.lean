/-
# WenSurface.Coverage — surface-facing catalogue coverage checks

This module does not duplicate the text catalogue proofs.  It imports the
existing coverage ledgers and exposes the counts that matter to WenSurface:
surface readings are resolvable/diagnosable, all 371 operator ids have total
signatures, every operator-cell row has a conservative machine denotation, and
exact cell transforms remain separately counted.
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
      ∧ canonicalHexNameRows.map Prod.snd = SSBX.Foundation.Bagua.Cell256.xuGua
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
      ∧ SSBX.Text.OperatorCellMap.allOperatorCells.length = 94976
      ∧ allOperatorCellSemanticRows.length = 94976 := by
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
      ∧ theoremBackedOperatorIds.length = 371
      ∧ exactTheoremBackedStrongOperatorIds.length = 371
      ∧ exactStructuralHelperStrongOperatorIds.length = 0
      ∧ structuralCarrierOperatorIds.length = 0
      ∧ catalogueNormalFormOperatorIds.length = 0
      ∧ domainGapOperatorIds.length = 0
      ∧ (domainGapKindOperatorIds .applicationHelperOnly).length = 0
      ∧ (domainGapKindOperatorIds .identityNoopOnly).length = 0
      ∧ (domainGapKindOperatorIds .projectionAnchorOnly).length = 0
      ∧ (domainGapKindOperatorIds .carrierConstructorOnly).length = 0
      ∧ (domainGapKindOperatorIds .predicateAnchorOnly).length = 0
      ∧ (domainGapKindOperatorIds .truthMarkerOnly).length = 0
      ∧ (domainGapKindOperatorIds .catalogueShapeOnly).length = 0
      ∧ (domainGapDetailKindOperatorIds .applicationMechanic).length = 0
      ∧ (domainGapDetailKindOperatorIds .identityNoop).length = 0
      ∧ (domainGapDetailKindOperatorIds .projectionModel).length = 0
      ∧ (domainGapDetailKindOperatorIds .pairCarrierLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .facetCarrierLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .singletonAggregateLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .binaryAggregateLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .ternaryAggregateLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .listProjectionLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .predicateModel).length = 0
      ∧ (domainGapDetailKindOperatorIds .truthMarkerModel).length = 0
      ∧ (domainGapDetailKindOperatorIds .catalogueShape).length = 0
      ∧ domainLawOperatorIds.length = 364
      ∧ domainCaveatOperatorIds.length = 0
      ∧ (domainCaveatKindOperatorIds .identityNoop).length = 0
      ∧ (domainCaveatKindOperatorIds .projectionAnchor).length = 0
      ∧ (domainCaveatKindOperatorIds .pairCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .duplicateFacetCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .singletonAggregateCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .binaryAggregateCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .ternaryAggregateCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .listProjectionCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .applicationCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .predicateAnchor).length = 0
      ∧ (domainCaveatKindOperatorIds .truthMarker).length = 0
      ∧ (domainCaveatKindOperatorIds .catalogueNormalForm).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .stateTransition).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .domainProcess).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .domainRule).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .assignment).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .trajectory).length = 0
      ∧ allOperatorIds.all (fun id => !(operatorForms id).isEmpty) = true := by
  exact
    ⟨ fullOperatorSignatures_length
    , operatorRegistryEntries_length
    , executableRegistryEntries_length
    , theoremBackedOperatorIds_length
    , exactTheoremBackedStrongOperatorIds_length
    , exactStructuralHelperStrongOperatorIds_length
    , structuralCarrierOperatorIds_length
    , catalogueNormalFormOperatorIds_length
    , domainGapOperatorIds_length
    , domainGap_applicationHelperOnly_length
    , domainGap_identityNoopOnly_length
    , domainGap_projectionAnchorOnly_length
    , domainGap_carrierConstructorOnly_length
    , domainGap_predicateAnchorOnly_length
    , domainGap_truthMarkerOnly_length
    , domainGap_catalogueShapeOnly_length
    , domainGapDetail_applicationMechanic_length
    , domainGapDetail_identityNoop_length
    , domainGapDetail_projectionModel_length
    , domainGapDetail_pairCarrierLaw_length
    , domainGapDetail_facetCarrierLaw_length
    , domainGapDetail_singletonAggregateLaw_length
    , domainGapDetail_binaryAggregateLaw_length
    , domainGapDetail_ternaryAggregateLaw_length
    , domainGapDetail_listProjectionLaw_length
    , domainGapDetail_predicateModel_length
    , domainGapDetail_truthMarkerModel_length
    , domainGapDetail_catalogueShape_length
    , domainLawOperatorIds_length
    , domainCaveatOperatorIds_length
    , domainCaveat_identityNoop_length
    , domainCaveat_projectionAnchor_length
    , domainCaveat_pairCarrier_length
    , domainCaveat_duplicateFacetCarrier_length
    , domainCaveat_singletonAggregateCarrier_length
    , domainCaveat_binaryAggregateCarrier_length
    , domainCaveat_ternaryAggregateCarrier_length
    , domainCaveat_listProjectionCarrier_length
    , domainCaveat_applicationCarrier_length
    , domainCaveat_predicateAnchor_length
    , domainCaveat_truthMarker_length
    , domainCaveat_catalogueNormalForm_length
    , catalogueShape_stateTransition_length
    , catalogueShape_domainProcess_length
    , catalogueShape_domainRule_length
    , catalogueShape_assignment_length
    , catalogueShape_trajectory_length
    , by native_decide
    ⟩

theorem wenSurface_operator_compound_surface_lex_coverage :
    (operatorCompoundSurfaceIds.map Prod.fst).all lexesAsSingleSurface = true :=
  operatorCompoundSurfaces_lex_as_single

theorem wenSurface_operator_cell_catalogue_counts :
    allOperatorCellSemanticRows.length = 94976
      ∧ allOperatorCellSemanticPairs.length = 94976 := by
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
      ∧ allOperatorCellSemanticRows.length = 94976
      ∧ operatorRegistryEntries.length = 371
      ∧ executableRegistryEntries.length = 371
      ∧ theoremBackedOperatorIds.length = 371
      ∧ exactTheoremBackedStrongOperatorIds.length = 371
      ∧ exactStructuralHelperStrongOperatorIds.length = 0
      ∧ structuralCarrierOperatorIds.length = 0
      ∧ catalogueNormalFormOperatorIds.length = 0
      ∧ domainGapOperatorIds.length = 0
      ∧ (domainGapKindOperatorIds .applicationHelperOnly).length = 0
      ∧ (domainGapKindOperatorIds .identityNoopOnly).length = 0
      ∧ (domainGapKindOperatorIds .projectionAnchorOnly).length = 0
      ∧ (domainGapKindOperatorIds .carrierConstructorOnly).length = 0
      ∧ (domainGapKindOperatorIds .predicateAnchorOnly).length = 0
      ∧ (domainGapKindOperatorIds .truthMarkerOnly).length = 0
      ∧ (domainGapKindOperatorIds .catalogueShapeOnly).length = 0
      ∧ (domainGapDetailKindOperatorIds .applicationMechanic).length = 0
      ∧ (domainGapDetailKindOperatorIds .identityNoop).length = 0
      ∧ (domainGapDetailKindOperatorIds .projectionModel).length = 0
      ∧ (domainGapDetailKindOperatorIds .pairCarrierLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .facetCarrierLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .singletonAggregateLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .binaryAggregateLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .ternaryAggregateLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .listProjectionLaw).length = 0
      ∧ (domainGapDetailKindOperatorIds .predicateModel).length = 0
      ∧ (domainGapDetailKindOperatorIds .truthMarkerModel).length = 0
      ∧ (domainGapDetailKindOperatorIds .catalogueShape).length = 0
      ∧ domainLawOperatorIds.length = 364
      ∧ domainCaveatOperatorIds.length = 0
      ∧ (domainCaveatKindOperatorIds .identityNoop).length = 0
      ∧ (domainCaveatKindOperatorIds .projectionAnchor).length = 0
      ∧ (domainCaveatKindOperatorIds .pairCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .duplicateFacetCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .singletonAggregateCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .binaryAggregateCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .ternaryAggregateCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .listProjectionCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .applicationCarrier).length = 0
      ∧ (domainCaveatKindOperatorIds .predicateAnchor).length = 0
      ∧ (domainCaveatKindOperatorIds .truthMarker).length = 0
      ∧ (domainCaveatKindOperatorIds .catalogueNormalForm).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .stateTransition).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .domainProcess).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .domainRule).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .assignment).length = 0
      ∧ (catalogueShapeSignatureKindOperatorIds .trajectory).length = 0
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
    , exactStructuralHelperStrongOperatorIds_length
    , structuralCarrierOperatorIds_length
    , catalogueNormalFormOperatorIds_length
    , domainGapOperatorIds_length
    , domainGap_applicationHelperOnly_length
    , domainGap_identityNoopOnly_length
    , domainGap_projectionAnchorOnly_length
    , domainGap_carrierConstructorOnly_length
    , domainGap_predicateAnchorOnly_length
    , domainGap_truthMarkerOnly_length
    , domainGap_catalogueShapeOnly_length
    , domainGapDetail_applicationMechanic_length
    , domainGapDetail_identityNoop_length
    , domainGapDetail_projectionModel_length
    , domainGapDetail_pairCarrierLaw_length
    , domainGapDetail_facetCarrierLaw_length
    , domainGapDetail_singletonAggregateLaw_length
    , domainGapDetail_binaryAggregateLaw_length
    , domainGapDetail_ternaryAggregateLaw_length
    , domainGapDetail_listProjectionLaw_length
    , domainGapDetail_predicateModel_length
    , domainGapDetail_truthMarkerModel_length
    , domainGapDetail_catalogueShape_length
    , domainLawOperatorIds_length
    , domainCaveatOperatorIds_length
    , domainCaveat_identityNoop_length
    , domainCaveat_projectionAnchor_length
    , domainCaveat_pairCarrier_length
    , domainCaveat_duplicateFacetCarrier_length
    , domainCaveat_singletonAggregateCarrier_length
    , domainCaveat_binaryAggregateCarrier_length
    , domainCaveat_ternaryAggregateCarrier_length
    , domainCaveat_listProjectionCarrier_length
    , domainCaveat_applicationCarrier_length
    , domainCaveat_predicateAnchor_length
    , domainCaveat_truthMarker_length
    , domainCaveat_catalogueNormalForm_length
    , catalogueShape_stateTransition_length
    , catalogueShape_domainProcess_length
    , catalogueShape_domainRule_length
    , catalogueShape_assignment_length
    , catalogueShape_trajectory_length
    , by native_decide
    , executableOperatorIds_registered
    , wenSurface_registry_total_signature
    ⟩

theorem wenSurface_reuses_bagua_grid_summary :
    allOperatorIds.length = 371
      ∧ SSBX.Foundation.Bagua.Cell256.Cell256.all.length = 256
      ∧ SSBX.Text.OperatorCellMap.allOperatorCells.length = 94976 :=
  ⟨ allOperatorIds_length
  , SSBX.Foundation.Bagua.Cell256.Cell256.all_length
  , allOperatorCells_length
  ⟩

theorem wenSurface_reuses_operator_cell_semantic_summary :
    allOperatorCellSemanticRows.length = 94976
      ∧ allOperatorCellSemanticPairs.length = 94976
      ∧ machineDenotationRows.length = 94976
      ∧ exactCellTransformDenotationRows.length = 11008
      ∧ executableCellTransformRows.length = 11008
      ∧ signatureCarrierDenotationRows.length = 83968 :=
  ⟨ allOperatorCellSemanticRows_length
  , allOperatorCellSemanticPairs_length
  , machineDenotationRows_length
  , exactCellTransformDenotationRows_length
  , executableCellTransformRows_length
  , signatureCarrierDenotationRows_length
  ⟩

/-! ## § 3 Current execution examples -/

example : (operatorRegistryEntryFor .T_10).executable?.isSome = true := by native_decide
example : (operatorRegistryEntryFor .Z_5).executable?.isSome = true := by native_decide
example : (operatorRegistryEntryFor .R_1).executable?.isSome = true := by native_decide
example : isTheoremBackedOperator .R_1 = true := by native_decide
example : (operatorRegistryEntryFor .S_1).signature.arity = 2 := by native_decide

end SSBX.Foundation.Wen.WenSurface
