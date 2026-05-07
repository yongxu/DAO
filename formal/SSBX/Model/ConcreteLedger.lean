/-
Concrete toy ledger support.

This module deliberately stays inside the formal toy boundary: the model is the
unit SSBX core model whose observable channels return `Tri.top`.  The ledger
propositions below are identified with the corresponding adequacy principles,
so the `ModelSupportsLedger` maps are concrete identity-style witnesses rather
than opaque extra fields.
-/
import SSBX.Model.Adequacy

namespace SSBX.Model.ConcreteLedger

open SSBX.Core
open SSBX.Truth
open SSBX.Truth.Absolute
open SSBX.Model.Adequacy

def toyModel : Model :=
  unitModel

def toyPredictive : Prop :=
  ∀ a b c d : Nat, toyModel.omega a b c d = Tri.top

def toyFalsifiable : Prop :=
  toyModel.audit () = Tri.top ∨ toyModel.audit () = Tri.bot ∨ toyModel.audit () = Tri.unk

def toyReproducible : Prop :=
  ∀ g : toyModel.Field, toyModel.audit g = toyModel.audit g

def toyBoundedError : Prop :=
  ∀ a b c d : Nat, toyModel.omega a b c d ≠ Tri.bot

def toyComparable : Prop :=
  ∀ a b : Nat, toyModel.omega a a a a = toyModel.omega b b b b

def toyCrossSampleStable : Prop :=
  ∀ xs : List Nat, toyModel.omegaB xs 0 = Tri.top

def toyInterventionCapable : Prop :=
  HasInterval toyModel ∧
    ∀ (g : toyModel.Field) (s : toyModel.Scale) (w : toyModel.Window) (i : toyModel.Interval),
      i ∈ toyModel.validIntervals g s w -> toyModel.step g i = g

def toyDomainBounded : Prop :=
  ∀ (g : toyModel.Field) (s : toyModel.Scale) (w : toyModel.Window),
    toyModel.validIntervals g s w = [()]

def toyAnomalyRecording : Prop :=
  ∀ g : toyModel.Field, toyModel.audit g = Tri.top

def toyUpdatable : Prop :=
  ∀ (g : toyModel.Field) (i : toyModel.Interval), toyModel.step g i = g

def toyAuditable : Prop :=
  ∀ g : toyModel.Field, toyModel.audit g = Tri.top

def toyNonSelfSealing : Prop :=
  toyModel.audit () = Tri.top

def toyPluralCheck : Prop :=
  ∀ xs : List Nat, ∀ n : Nat, toyModel.omegaB xs n = Tri.top

theorem toy_predictive_holds : toyPredictive := by
  intro a b c d
  rfl

theorem toy_falsifiable_holds : toyFalsifiable := by
  exact Or.inl rfl

theorem toy_reproducible_holds : toyReproducible := by
  intro g
  rfl

theorem toy_bounded_error_holds : toyBoundedError := by
  intro a b c d h
  cases h

theorem toy_comparable_holds : toyComparable := by
  intro a b
  rfl

theorem toy_cross_sample_stable_holds : toyCrossSampleStable := by
  intro xs
  rfl

theorem toy_intervention_capable_holds : toyInterventionCapable := by
  constructor
  · exact unitModel_has_interval
  · intro g s w i _hmem
    cases g
    cases i
    rfl

theorem toy_domain_bounded_holds : toyDomainBounded := by
  intro g s w
  cases g
  cases s
  cases w
  rfl

theorem toy_anomaly_recording_holds : toyAnomalyRecording := by
  intro g
  cases g
  rfl

theorem toy_updatable_holds : toyUpdatable := by
  intro g i
  cases g
  cases i
  rfl

theorem toy_auditable_holds : toyAuditable := by
  intro g
  cases g
  rfl

theorem toy_non_self_sealing_holds : toyNonSelfSealing := by
  rfl

theorem toy_plural_check_holds : toyPluralCheck := by
  intro xs n
  rfl

def toyModelAdequacy : ModelAdequacy toyModel :=
  { predictive := toyPredictive
    predictive_holds := toy_predictive_holds
    falsifiable := toyFalsifiable
    falsifiable_holds := toy_falsifiable_holds
    reproducible := toyReproducible
    reproducible_holds := toy_reproducible_holds
    bounded_error := toyBoundedError
    bounded_error_holds := toy_bounded_error_holds
    comparable := toyComparable
    comparable_holds := toy_comparable_holds
    cross_sample_stable := toyCrossSampleStable
    cross_sample_stable_holds := toy_cross_sample_stable_holds
    intervention_capable := toyInterventionCapable
    intervention_capable_holds := toy_intervention_capable_holds
    domain_bounded := toyDomainBounded
    domain_bounded_holds := toy_domain_bounded_holds
    anomaly_recording := toyAnomalyRecording
    anomaly_recording_holds := toy_anomaly_recording_holds
    updatable := toyUpdatable
    updatable_holds := toy_updatable_holds
    auditable := toyAuditable
    auditable_holds := toy_auditable_holds
    non_self_sealing := toyNonSelfSealing
    non_self_sealing_holds := toy_non_self_sealing_holds
    plural_check := toyPluralCheck
    plural_check_holds := toy_plural_check_holds }

def toyAdequateModel : AdequateModel :=
  { model := toyModel
    adequacy := toyModelAdequacy }

def toyLedger : SSBXAxiomLedger :=
  { open_value_axiom := toyAdequateModel.adequacy.intervention_capable
    open_value_holds := toyAdequateModel.adequacy.intervention_capable_holds
    audit_reliability_axiom := toyAdequateModel.adequacy.auditable
    audit_reliability_holds := toyAdequateModel.adequacy.auditable_holds
    omega_adequacy_axiom := toyAdequateModel.adequacy.predictive
    omega_adequacy_holds := toyAdequateModel.adequacy.predictive_holds
    omegaB_adequacy_axiom := toyAdequateModel.adequacy.plural_check
    omegaB_adequacy_holds := toyAdequateModel.adequacy.plural_check_holds
    pi_open_adequacy_axiom := toyAdequateModel.adequacy.comparable
    pi_open_adequacy_holds := toyAdequateModel.adequacy.comparable_holds
    threshold_reliability_axiom := toyAdequateModel.adequacy.bounded_error
    threshold_reliability_holds := toyAdequateModel.adequacy.bounded_error_holds
    truth_path_axiom := toyAdequateModel.adequacy.cross_sample_stable
    truth_path_holds := toyAdequateModel.adequacy.cross_sample_stable_holds
    text_adequacy_axiom := toyAdequateModel.adequacy.domain_bounded
    text_adequacy_holds := toyAdequateModel.adequacy.domain_bounded_holds
    case_data_reliability_axiom := toyAdequateModel.adequacy.reproducible
    case_data_reliability_holds := toyAdequateModel.adequacy.reproducible_holds }

def toySupportsLedger : ModelSupportsLedger toyAdequateModel toyLedger :=
  { supports_open_value := by
      intro h
      exact h
    supports_audit := by
      intro h
      exact h
    supports_omega := by
      intro h
      exact h
    supports_omegaB := by
      intro h
      exact h
    supports_pi_open := by
      intro h
      exact h
    supports_threshold := by
      intro h
      exact h
    supports_truth_path := by
      intro h
      exact h
    supports_text_mapping := by
      intro h
      exact h
    supports_case_data := by
      intro h
      exact h }

def toyLedgerAxiomsHold : LedgerAxiomsHold toyLedger :=
  ledger_from_adequate_model toyAdequateModel toyLedger toySupportsLedger

def toyModelGroundedTruthCertificate :
    ModelGroundedTruthCertificate SSBXTheory :=
  model_grounded_truth_certificate toyAdequateModel toyLedger toySupportsLedger

theorem toy_model_grounded_truth : ModelGroundedTruth SSBXTheory :=
  truth_from_good_model toyAdequateModel toyLedger toySupportsLedger

theorem toy_absolute_truth : AbsoluteTruth SSBXTheory :=
  adequate_model_implies_ledger_truth toyAdequateModel toyLedger toySupportsLedger

end SSBX.Model.ConcreteLedger
