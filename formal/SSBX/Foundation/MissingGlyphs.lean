/-
Recovered missing glyph admission ledger.

This file separates structural recovery from semantic admission.
`recovered_missing_glyphs_return_to_root` only proves root reachability.
It is not a proof that the provisional core/face choice is semantically
justified.  Pending classes below make that gap machine-visible.
-/
import SSBX.Foundation.MonadRoot
import SSBX.Foundation.MathAxiomMap
import SSBX.Text.Completeness
import SSBX.Truth.Adequacy

namespace SSBX.Foundation.MissingGlyphs

open SSBX.Roster
open SSBX.Foundation.MonadRoot
open SSBX.Foundation.MathAxiomMap
open SSBX.Text.Glyph
open SSBX.Truth
open SSBX.Truth.ClaimLedger

def recoveredMissingGlyphs : List AtomName := [
  .«七», .«三», .«不», .«与», .«中», .«乃», .«九», .«事», .«二», .«五», .«亦», .«仍», .«以», .«件»,
  .«位», .«例», .«保», .«值», .«全», .«八», .«六», .«其», .«册», .«冒», .«准», .«凡», .«出», .«判»,
  .«别», .«前», .«十», .«卷», .«原», .«口», .«古», .«句», .«只», .«名», .«含», .«四», .«型», .«增»,
  .«始», .«字», .«守», .«完», .«导», .«尺», .«常», .«式», .«当», .«录», .«律», .«得», .«微», .«德»,
  .«指», .«推», .«收», .«故», .«整», .«文», .«易», .«有», .«本», .«束», .«极», .«染», .«根», .«此»,
  .«渲», .«版», .«皆», .«空», .«立», .«箱», .«篇», .«籍», .«类», .«终», .«经», .«缺», .«美», .«背»,
  .«致», .«补», .«表», .«见», .«言», .«语», .«诸», .«谓», .«象», .«连», .«述», .«递», .«遇», .«量»,
  .«锚», .«随», .«非», .«项», .«高», .«黑»
]

def mathInterfaceGlyphs : List AtomName := [
  .«七», .«三», .«九», .«二», .«五», .«位», .«值», .«全», .«八», .«六», .«十», .«四», .«尺», .«极»,
  .«量»
]

def proofLanguagePendingGlyphs : List AtomName := [
  .«冒», .«准», .«判», .«原», .«始», .«名», .«型», .«完», .«导», .«式», .«录», .«律», .«得», .«指»,
  .«推», .«收», .«整», .«束», .«根», .«立», .«籍», .«见», .«谓», .«述», .«递», .«锚», .«项»
]

def valueAxiomPendingGlyphs : List AtomName := [
  .«中», .«保», .«常», .«德», .«美», .«背»
]

def textOnlyPendingGlyphs : List AtomName := [
  .«染», .«渲», .«册», .«箱», .«黑»
]

def textOperatorOrRecordGlyphs : List AtomName := [
  .«不», .«与», .«乃», .«亦», .«仍», .«以», .«其», .«凡», .«别», .«前», .«卷», .«口», .«古», .«句»,
  .«只», .«含», .«字», .«守», .«当», .«故», .«文», .«有», .«本», .«此», .«版», .«皆», .«篇», .«缺»,
  .«补», .«表», .«言», .«语», .«诸», .«非»
]

def modelOrObjectPendingGlyphs : List AtomName := [
  .«事», .«件», .«例», .«出», .«增», .«微», .«易», .«空», .«类», .«终», .«经», .«致», .«象», .«连»,
  .«遇», .«随», .«高»
]

def classifiedRecoveredGlyphs : List AtomName :=
  mathInterfaceGlyphs ++ proofLanguagePendingGlyphs ++ valueAxiomPendingGlyphs ++
  textOnlyPendingGlyphs ++ textOperatorOrRecordGlyphs ++ modelOrObjectPendingGlyphs

inductive GlyphAdmissionKind where
  | mathInterface
  | proofLanguagePending
  | valueAxiomPending
  | textOnlyPending
  | textOperatorOrRecord
  | modelOrObjectPending
  | semanticProved
  deriving DecidableEq, Repr

def admissionKind (a : AtomName) : GlyphAdmissionKind :=
  if a ∈ mathInterfaceGlyphs then .mathInterface
  else if a ∈ proofLanguagePendingGlyphs then .proofLanguagePending
  else if a ∈ valueAxiomPendingGlyphs then .valueAxiomPending
  else if a ∈ textOnlyPendingGlyphs then .textOnlyPending
  else if a ∈ textOperatorOrRecordGlyphs then .textOperatorOrRecord
  else if a ∈ modelOrObjectPendingGlyphs then .modelOrObjectPending
  else .textOperatorOrRecord

def HasObjectSemanticProof (a : AtomName) : Prop :=
  admissionKind a = .semanticProved

instance hasObjectSemanticProofDecidable (a : AtomName) :
    Decidable (HasObjectSemanticProof a) := by
  unfold HasObjectSemanticProof
  infer_instance

def StructuralProofAvailable (a : AtomName) : Prop :=
  a ∈ allAtoms ∧
  CoveredSymbol (Symbol.atom a) ∧
  Reachable «一元» (.atom a)

def naturalNumberGlyphs : List AtomName := [
  .«七», .«三», .«九», .«二», .«五», .«八», .«六», .«十», .«四»
]

def mathInterfaceFamily (a : AtomName) : AxiomFamily :=
  if a ∈ naturalNumberGlyphs then .naturalNumber else .algebra

def proofLanguageAnchor (_ : AtomName) : ClaimId :=
  .semanticAdequacyClaim

def valueAxiomAnchor : AtomName -> ClaimId
  | .«背» => .wrongDefinition
  | _ => .openValueAxiomClaim

def recoveredMissingGlyphRootSummary : List (AtomName × CoreAtom × Face) :=
  recoveredMissingGlyphs.map (fun a => (a, atomCore a, atomPrimaryFace a))

theorem recovered_missing_glyphs_registered {a : AtomName} :
    a ∈ recoveredMissingGlyphs -> a ∈ allAtoms := by
  intro _
  cases a <;> native_decide

theorem recovered_classification_complete {a : AtomName} :
    a ∈ recoveredMissingGlyphs -> a ∈ classifiedRecoveredGlyphs := by
  cases a <;> native_decide

theorem recovered_classification_sound {a : AtomName} :
    a ∈ classifiedRecoveredGlyphs -> a ∈ recoveredMissingGlyphs := by
  cases a <;> native_decide

theorem recovered_classification_has_no_duplicates :
    classifiedRecoveredGlyphs.Nodup := by
  native_decide

theorem recovered_missing_glyphs_return_to_root {a : AtomName} :
    a ∈ recoveredMissingGlyphs ->
      Reachable «一元» (.core (atomCore a)) ∧
      DirectEdge (.core (atomCore a)) (.atom a) ∧
      Reachable «一元» (.atom a) := by
  intro _
  exact all_atoms_return_through_core a

theorem recovered_missing_glyphs_structural_proof {a : AtomName} :
    a ∈ recoveredMissingGlyphs -> StructuralProofAvailable a := by
  intro h
  exact ⟨
    recovered_missing_glyphs_registered h,
    SSBX.Text.Completeness.roster_text_complete (Symbol.atom a),
    (all_atoms_return_through_core a).2.2
  ⟩

theorem math_interface_connected {a : AtomName} :
    a ∈ mathInterfaceGlyphs ->
      admissionKind a = .mathInterface ∧
      hasRootOrMap (entry (mathInterfaceFamily a)) ∧
      contractReady (entry (mathInterfaceFamily a)) := by
  intro h
  have hk : a ∈ mathInterfaceGlyphs -> admissionKind a = .mathInterface := by
    cases a <;> native_decide
  exact ⟨hk h, math_axiom_interfaces_have_root_or_map (mathInterfaceFamily a),
    math_axiom_contracts_ready (mathInterfaceFamily a)⟩

theorem proof_language_layer_ready :
    hasRootOrMap (entry .proofLegality) ∧
    contractReady (entry .proofLegality) := by
  exact ⟨math_axiom_interfaces_have_root_or_map .proofLegality,
    math_axiom_contracts_ready .proofLegality⟩

theorem proof_language_pending_connected {a : AtomName} :
    a ∈ proofLanguagePendingGlyphs ->
      admissionKind a = .proofLanguagePending ∧
      claimEntry (proofLanguageAnchor a) ∈ allClaims := by
  intro h
  have hk : a ∈ proofLanguagePendingGlyphs -> admissionKind a = .proofLanguagePending := by
    cases a <;> native_decide
  exact ⟨hk h, all_claims_have_entries (proofLanguageAnchor a)⟩

theorem value_pending_connected_to_value_axioms {a : AtomName} :
    a ∈ valueAxiomPendingGlyphs ->
      admissionKind a = .valueAxiomPending ∧
      atomPrimaryFace a = .«价值面» ∧
      claimEntry (valueAxiomAnchor a) ∈ allClaims := by
  intro h
  have hk : a ∈ valueAxiomPendingGlyphs -> admissionKind a = .valueAxiomPending := by
    cases a <;> native_decide
  have hf : a ∈ valueAxiomPendingGlyphs -> atomPrimaryFace a = .«价值面» := by
    cases a <;> native_decide
  exact ⟨hk h, hf h, all_claims_have_entries (valueAxiomAnchor a)⟩

theorem text_only_pending_kept_textual {a : AtomName} :
    a ∈ textOnlyPendingGlyphs ->
      admissionKind a = .textOnlyPending ∧
      atomCore a = .«法» ∧
      atomPrimaryFace a = .«文面» ∧
      ¬ HasObjectSemanticProof a := by
  cases a <;> native_decide

theorem proof_language_pending_not_semantically_proved {a : AtomName} :
    a ∈ proofLanguagePendingGlyphs -> ¬ HasObjectSemanticProof a := by
  cases a <;> native_decide

theorem value_pending_not_semantically_proved {a : AtomName} :
    a ∈ valueAxiomPendingGlyphs -> ¬ HasObjectSemanticProof a := by
  cases a <;> native_decide

theorem model_or_object_pending_not_semantically_proved {a : AtomName} :
    a ∈ modelOrObjectPendingGlyphs -> ¬ HasObjectSemanticProof a := by
  cases a <;> native_decide

theorem recovered_missing_glyphs_have_no_object_semantic_proof {a : AtomName} :
    a ∈ recoveredMissingGlyphs -> ¬ HasObjectSemanticProof a := by
  cases a <;> native_decide

end SSBX.Foundation.MissingGlyphs
