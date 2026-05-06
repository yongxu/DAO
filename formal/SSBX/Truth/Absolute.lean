/-
Ledger-dependent absolute-truth certificate theorem. No hidden Lean axioms.
-/
import SSBX.Truth.Adequacy

namespace SSBX.Truth.Absolute

open SSBX.Truth
open SSBX.Truth.Adequacy

def recommendation_case_truth (_L : SSBXAxiomLedger) : RecommendationCaseTruth :=
  { one_evil := (rfl)
    two_right := (rfl)
    two_ren := (rfl)
    two_candidate_true_dao := (rfl)
    three_protective_closure := (rfl) }

def absolute_truth_certificate (L : SSBXAxiomLedger) : AbsoluteTruthCertificate SSBXTheory :=
  { ledger := L,
    ledger_holds := ledger_axioms_hold L,
    all_claims_semantically_adequate := semantic_adequacy_complete,
    roster_text_complete := SSBX.Text.Completeness.roster_text_complete,
    operator_table_complete := SSBX.Text.Completeness.operator_table_complete,
    recommendation_case := recommendation_case_truth L }

theorem truth_depends_on_ledger (L : SSBXAxiomLedger) : AbsoluteTruth SSBXTheory :=
  ⟨absolute_truth_certificate L⟩

theorem ssbx_absolute_truth : SSBXAxiomLedger -> AbsoluteTruth SSBXTheory :=
  truth_depends_on_ledger

end SSBX.Truth.Absolute
