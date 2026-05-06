/-
Formal semantic interface for registered claims.
-/
import SSBX.Truth.ClaimLedger

namespace SSBX.Truth.Semantics

open SSBX.Truth
open SSBX.Truth.ClaimLedger

inductive SemanticsSource where
  | definitional
  | machineTheorem
  | axiomBacked
  | modelInterface
  | registryTheorem
  | finiteCase
  | uninterpreted
  deriving DecidableEq, Repr

inductive SemanticTerm where
  | predicate : String -> SemanticTerm
  | interface : String -> SemanticTerm
  | theoremRef : String -> SemanticTerm
  | caseJudgement : ActionId -> CaseVerdict -> SemanticTerm
  deriving DecidableEq, Repr

structure FormalSemantics where
  id : ClaimId
  source : SemanticsSource
  term : SemanticTerm
  value : SSBX.Core.Tri
  deriving DecidableEq, Repr

def sourceOfKind : ClaimKind -> SemanticsSource
  | .definition => .definitional
  | .proved => .machineTheorem
  | .axiomBacked => .axiomBacked
  | .modelInterface => .modelInterface
  | .caseResult => .finiteCase
  | .registry => .registryTheorem

def semanticTermOf (id : ClaimId) : SemanticTerm :=
  match id with
  | .recommendationI1Evil => .caseJudgement .i1 .evilAction
  | .recommendationI2Right => .caseJudgement .i2 .rightAction
  | .recommendationI2Ren => .caseJudgement .i2 .renAction
  | .recommendationI2CandidateTrueDao => .caseJudgement .i2 .candidateTrueDao
  | .recommendationI3ProtectiveClosure => .caseJudgement .i3 .protectiveClosure
  | .omegaInterface => .interface "Ω"
  | .omegaBInterface => .interface "Ω_B"
  | .piOpenInterface => .interface "Π_开"
  | .thresholdProtocol => .interface "Θ"
  | .triValueConservativity => .theoremRef "SSBX.Core.Tri.unk_not_assertable"
  | .generatedRootsDiscipline => .theoremRef "SSBX.Roster.generated_entries_have_roots"
  | .recursiveSemanticsDiscipline => .theoremRef "SSBX.Roster.recursive_entries_have_semantics"
  | .rosterTextComplete => .theoremRef "SSBX.Text.Completeness.roster_text_complete"
  | .wenyanOperatorTableComplete => .theoremRef "SSBX.Text.Completeness.operator_table_complete"
  | .semanticAdequacyClaim => .theoremRef "SSBX.Truth.Adequacy.semantic_adequacy_complete"
  | .absoluteTruthClaim => .theoremRef "SSBX.Truth.Absolute.ssbx_absolute_truth"
  | .rootToSsbxLiClaim => .theoremRef "SSBX.Foundation.Core.Li.shengsheng_buxi_is_li_from_ledger"
  | other => .predicate (claimEntry other).label

def semanticValueOf (id : ClaimId) : SSBX.Core.Tri :=
  match semanticTermOf id with
  | .caseJudgement a v => recommendationVerdict a v
  | _ => .unk

def formalSemantics (id : ClaimId) : FormalSemantics :=
  { id := id,
    source := sourceOfKind (claimEntry id).kind,
    term := semanticTermOf id,
    value := semanticValueOf id }

def HasFormalSemantics (id : ClaimId) : Prop :=
  (formalSemantics id).id = id ∧ (formalSemantics id).source ≠ SemanticsSource.uninterpreted

instance hasFormalSemanticsDecidable (id : ClaimId) : Decidable (HasFormalSemantics id) := by
  unfold HasFormalSemantics
  infer_instance

def SourceClaimMapped (id : ClaimId) : Prop :=
  (claimEntry id).sourceRef ≠ ""

instance sourceClaimMappedDecidable (id : ClaimId) : Decidable (SourceClaimMapped id) := by
  unfold SourceClaimMapped
  infer_instance

theorem claim_has_semantics (id : ClaimId) : HasFormalSemantics id := by
  cases id <;> native_decide

theorem source_claim_mapped (id : ClaimId) : SourceClaimMapped id := by
  cases id <;> native_decide

theorem no_placeholder_semantics (id : ClaimId) :
    (formalSemantics id).source ≠ SemanticsSource.uninterpreted :=
  (claim_has_semantics id).2

end SSBX.Truth.Semantics
