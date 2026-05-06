/-
Truth and adequacy core types. Philosophical and empirical premises are explicit ledger fields.
-/
import SSBX.Text.Completeness
import SSBX.Core

namespace SSBX.Truth

inductive ClaimId where
  | openDefinition | closeDefinition | rightDefinition | wrongDefinition | goodDefinition | badDefinition | freedomDefinition | flourishingDefinition | yiDefinition | shanDefinition | renDefinition | daoDefinition | trueDaoDefinition | auditUnbrokenDefinition | omegaInterface | omegaBInterface | piOpenInterface | thresholdProtocol | triValueConservativity | generatedRootsDiscipline | recursiveSemanticsDiscipline | rosterTextComplete | wenyanOperatorTableComplete | sourceTextClaimMapping | openValueAxiomClaim | auditReliabilityAxiomClaim | omegaAdequacyAxiomClaim | omegaBAdequacyAxiomClaim | piOpenAdequacyAxiomClaim | truthPathAxiomClaim | recommendationI1Evil | recommendationI2Right | recommendationI2Ren | recommendationI2CandidateTrueDao | recommendationI3ProtectiveClosure | semanticAdequacyClaim | absoluteTruthClaim | rootToSsbxLiClaim
  deriving DecidableEq, Repr

inductive ClaimKind where
  | definition | proved | axiomBacked | modelInterface | caseResult | registry
  deriving DecidableEq, Repr

inductive TruthStatus where
  | machineChecked | ledgerDependent | modelComputed | registryChecked | pending
  deriving DecidableEq, Repr

structure Theory where
  name : String
  deriving DecidableEq, Repr

def SSBXTheory : Theory := { name := "生生不息论" }

structure SSBXAxiomLedger where
  open_value_axiom : Prop
  open_value_holds : open_value_axiom
  audit_reliability_axiom : Prop
  audit_reliability_holds : audit_reliability_axiom
  omega_adequacy_axiom : Prop
  omega_adequacy_holds : omega_adequacy_axiom
  omegaB_adequacy_axiom : Prop
  omegaB_adequacy_holds : omegaB_adequacy_axiom
  pi_open_adequacy_axiom : Prop
  pi_open_adequacy_holds : pi_open_adequacy_axiom
  threshold_reliability_axiom : Prop
  threshold_reliability_holds : threshold_reliability_axiom
  truth_path_axiom : Prop
  truth_path_holds : truth_path_axiom
  text_adequacy_axiom : Prop
  text_adequacy_holds : text_adequacy_axiom
  case_data_reliability_axiom : Prop
  case_data_reliability_holds : case_data_reliability_axiom

structure LedgerAxiomsHold (L : SSBXAxiomLedger) where
  open_value : L.open_value_axiom
  audit_reliability : L.audit_reliability_axiom
  omega_adequacy : L.omega_adequacy_axiom
  omegaB_adequacy : L.omegaB_adequacy_axiom
  pi_open_adequacy : L.pi_open_adequacy_axiom
  threshold_reliability : L.threshold_reliability_axiom
  truth_path : L.truth_path_axiom
  text_adequacy : L.text_adequacy_axiom
  case_data_reliability : L.case_data_reliability_axiom

def ledger_axioms_hold (L : SSBXAxiomLedger) : LedgerAxiomsHold L :=
  { open_value := L.open_value_holds,
    audit_reliability := L.audit_reliability_holds,
    omega_adequacy := L.omega_adequacy_holds,
    omegaB_adequacy := L.omegaB_adequacy_holds,
    pi_open_adequacy := L.pi_open_adequacy_holds,
    threshold_reliability := L.threshold_reliability_holds,
    truth_path := L.truth_path_holds,
    text_adequacy := L.text_adequacy_holds,
    case_data_reliability := L.case_data_reliability_holds }

structure SemanticAdequacy (id : ClaimId) where
  formal_semantics : Prop
  formal_semantics_holds : formal_semantics
  text_mapping : Prop
  text_mapping_holds : text_mapping

inductive ActionId where
  | i1 | i2 | i3
  deriving DecidableEq, Repr

inductive CaseVerdict where
  | evilAction | rightAction | renAction | candidateTrueDao | protectiveClosure
  deriving DecidableEq, Repr

def recommendationVerdict : ActionId -> CaseVerdict -> SSBX.Core.Tri
  | .i1, .evilAction => .top
  | .i2, .rightAction => .top
  | .i2, .renAction => .top
  | .i2, .candidateTrueDao => .top
  | .i3, .protectiveClosure => .top
  | _, _ => .unk

structure RecommendationCaseTruth where
  one_evil : recommendationVerdict .i1 .evilAction = SSBX.Core.Tri.top
  two_right : recommendationVerdict .i2 .rightAction = SSBX.Core.Tri.top
  two_ren : recommendationVerdict .i2 .renAction = SSBX.Core.Tri.top
  two_candidate_true_dao : recommendationVerdict .i2 .candidateTrueDao = SSBX.Core.Tri.top
  three_protective_closure : recommendationVerdict .i3 .protectiveClosure = SSBX.Core.Tri.top

structure AbsoluteTruthCertificate (T : Theory) where
  ledger : SSBXAxiomLedger
  ledger_holds : LedgerAxiomsHold ledger
  all_claims_semantically_adequate : ∀ id : ClaimId, Nonempty (SemanticAdequacy id)
  roster_text_complete : ∀ s : SSBX.Roster.Symbol, SSBX.Text.Glyph.CoveredSymbol s
  operator_table_complete :
    ∀ id : SSBX.Text.WenyanOperators.OperatorId, SSBX.Text.WenyanOperators.CoveredOperator id
  recommendation_case : RecommendationCaseTruth

def AbsoluteTruth (T : Theory) : Prop :=
  Nonempty (AbsoluteTruthCertificate T)

end SSBX.Truth
