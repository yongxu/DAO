/-
Semantic adequacy proofs for registered claims.
-/
import SSBX.Truth.Semantics

namespace SSBX.Truth.Adequacy

open SSBX.Truth
open SSBX.Truth.Semantics
open SSBX.Truth.ClaimLedger

def semanticAdequacyOf (id : ClaimId) : SemanticAdequacy id :=
  { formal_semantics := HasFormalSemantics id,
    formal_semantics_holds := claim_has_semantics id,
    text_mapping := SourceClaimMapped id,
    text_mapping_holds := source_claim_mapped id }

def SemanticallyAdequate (id : ClaimId) : Prop :=
  Nonempty (SemanticAdequacy id)

theorem semantic_adequacy_complete (id : ClaimId) : SemanticallyAdequate id :=
  ⟨semanticAdequacyOf id⟩

theorem all_claims_semantically_covered :
    ∀ id : ClaimId, SemanticallyAdequate id :=
  semantic_adequacy_complete

theorem every_registered_claim_has_semantics (id : ClaimId) :
    claimEntry id ∈ allClaims ∧ HasFormalSemantics id :=
  ⟨all_claims_have_entries id, claim_has_semantics id⟩

theorem no_unregistered_formal_claim {c : ClaimEntry} :
    FormalClaim c -> c ∈ allClaims :=
  no_unregistered_claim

end SSBX.Truth.Adequacy
