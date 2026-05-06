/-
Model adequacy principles: good models as auditable channels for experience.
-/
import SSBX.Truth.Absolute

namespace SSBX.Model.Adequacy

open SSBX.Core
open SSBX.Truth
open SSBX.Truth.Absolute

inductive ModelPrinciple where
  | predictive
  | falsifiable
  | reproducible
  | boundedError
  | comparable
  | crossSampleStable
  | interventionCapable
  | domainBounded
  | anomalyRecording
  | updatable
  | auditable
  | nonSelfSealing
  | pluralCheck
  deriving DecidableEq, Repr

structure ModelAdequacy (M : Model) where
  predictive : Prop
  predictive_holds : predictive
  falsifiable : Prop
  falsifiable_holds : falsifiable
  reproducible : Prop
  reproducible_holds : reproducible
  bounded_error : Prop
  bounded_error_holds : bounded_error
  comparable : Prop
  comparable_holds : comparable
  cross_sample_stable : Prop
  cross_sample_stable_holds : cross_sample_stable
  intervention_capable : Prop
  intervention_capable_holds : intervention_capable
  domain_bounded : Prop
  domain_bounded_holds : domain_bounded
  anomaly_recording : Prop
  anomaly_recording_holds : anomaly_recording
  updatable : Prop
  updatable_holds : updatable
  auditable : Prop
  auditable_holds : auditable
  non_self_sealing : Prop
  non_self_sealing_holds : non_self_sealing
  plural_check : Prop
  plural_check_holds : plural_check

structure AdequateModel where
  model : Model
  adequacy : ModelAdequacy model

structure ModelPrinciplesHold (M : Model) (A : ModelAdequacy M) where
  predictive : A.predictive
  falsifiable : A.falsifiable
  reproducible : A.reproducible
  bounded_error : A.bounded_error
  comparable : A.comparable
  cross_sample_stable : A.cross_sample_stable
  intervention_capable : A.intervention_capable
  domain_bounded : A.domain_bounded
  anomaly_recording : A.anomaly_recording
  updatable : A.updatable
  auditable : A.auditable
  non_self_sealing : A.non_self_sealing
  plural_check : A.plural_check

def model_principles_hold (M : Model) (A : ModelAdequacy M) : ModelPrinciplesHold M A :=
  { predictive := A.predictive_holds
    falsifiable := A.falsifiable_holds
    reproducible := A.reproducible_holds
    bounded_error := A.bounded_error_holds
    comparable := A.comparable_holds
    cross_sample_stable := A.cross_sample_stable_holds
    intervention_capable := A.intervention_capable_holds
    domain_bounded := A.domain_bounded_holds
    anomaly_recording := A.anomaly_recording_holds
    updatable := A.updatable_holds
    auditable := A.auditable_holds
    non_self_sealing := A.non_self_sealing_holds
    plural_check := A.plural_check_holds }

def principleSatisfied (A : AdequateModel) : ModelPrinciple -> Prop
  | .predictive => A.adequacy.predictive
  | .falsifiable => A.adequacy.falsifiable
  | .reproducible => A.adequacy.reproducible
  | .boundedError => A.adequacy.bounded_error
  | .comparable => A.adequacy.comparable
  | .crossSampleStable => A.adequacy.cross_sample_stable
  | .interventionCapable => A.adequacy.intervention_capable
  | .domainBounded => A.adequacy.domain_bounded
  | .anomalyRecording => A.adequacy.anomaly_recording
  | .updatable => A.adequacy.updatable
  | .auditable => A.adequacy.auditable
  | .nonSelfSealing => A.adequacy.non_self_sealing
  | .pluralCheck => A.adequacy.plural_check

theorem adequate_model_satisfies_principles (A : AdequateModel) :
    ∀ p : ModelPrinciple, principleSatisfied A p := by
  intro p
  cases p <;> exact (by
    first
    | exact A.adequacy.predictive_holds
    | exact A.adequacy.falsifiable_holds
    | exact A.adequacy.reproducible_holds
    | exact A.adequacy.bounded_error_holds
    | exact A.adequacy.comparable_holds
    | exact A.adequacy.cross_sample_stable_holds
    | exact A.adequacy.intervention_capable_holds
    | exact A.adequacy.domain_bounded_holds
    | exact A.adequacy.anomaly_recording_holds
    | exact A.adequacy.updatable_holds
    | exact A.adequacy.auditable_holds
    | exact A.adequacy.non_self_sealing_holds
    | exact A.adequacy.plural_check_holds)

structure ModelSupportsLedger (A : AdequateModel) (L : SSBXAxiomLedger) where
  supports_open_value : A.adequacy.intervention_capable -> L.open_value_axiom
  supports_audit : A.adequacy.auditable -> L.audit_reliability_axiom
  supports_omega : A.adequacy.predictive -> L.omega_adequacy_axiom
  supports_omegaB : A.adequacy.plural_check -> L.omegaB_adequacy_axiom
  supports_pi_open : A.adequacy.comparable -> L.pi_open_adequacy_axiom
  supports_threshold : A.adequacy.bounded_error -> L.threshold_reliability_axiom
  supports_truth_path : A.adequacy.cross_sample_stable -> L.truth_path_axiom
  supports_text_mapping : A.adequacy.domain_bounded -> L.text_adequacy_axiom
  supports_case_data : A.adequacy.reproducible -> L.case_data_reliability_axiom

def ledger_from_adequate_model (A : AdequateModel) (L : SSBXAxiomLedger)
    (S : ModelSupportsLedger A L) : LedgerAxiomsHold L :=
  { open_value := S.supports_open_value A.adequacy.intervention_capable_holds
    audit_reliability := S.supports_audit A.adequacy.auditable_holds
    omega_adequacy := S.supports_omega A.adequacy.predictive_holds
    omegaB_adequacy := S.supports_omegaB A.adequacy.plural_check_holds
    pi_open_adequacy := S.supports_pi_open A.adequacy.comparable_holds
    threshold_reliability := S.supports_threshold A.adequacy.bounded_error_holds
    truth_path := S.supports_truth_path A.adequacy.cross_sample_stable_holds
    text_adequacy := S.supports_text_mapping A.adequacy.domain_bounded_holds
    case_data_reliability := S.supports_case_data A.adequacy.reproducible_holds }

structure ModelGroundedTruthCertificate (T : Theory) where
  adequate_model : AdequateModel
  ledger : SSBXAxiomLedger
  supports_ledger : ModelSupportsLedger adequate_model ledger
  absolute_truth : AbsoluteTruth T
  ledger_grounded : LedgerAxiomsHold ledger

def ModelGroundedTruth (T : Theory) : Prop :=
  Nonempty (ModelGroundedTruthCertificate T)

def model_grounded_truth_certificate (A : AdequateModel) (L : SSBXAxiomLedger)
    (S : ModelSupportsLedger A L) : ModelGroundedTruthCertificate SSBXTheory :=
  { adequate_model := A
    ledger := L
    supports_ledger := S
    absolute_truth := truth_depends_on_ledger L
    ledger_grounded := ledger_from_adequate_model A L S }

theorem truth_from_good_model (A : AdequateModel) (L : SSBXAxiomLedger)
    (S : ModelSupportsLedger A L) : ModelGroundedTruth SSBXTheory :=
  ⟨model_grounded_truth_certificate A L S⟩

theorem adequate_model_implies_ledger_truth (A : AdequateModel) (L : SSBXAxiomLedger)
    (S : ModelSupportsLedger A L) : AbsoluteTruth SSBXTheory :=
  (model_grounded_truth_certificate A L S).absolute_truth

end SSBX.Model.Adequacy
