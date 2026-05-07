/-
Finite claim ledger for the core claims admitted by the theory.
-/
import SSBX.Truth.Basic

namespace SSBX.Truth.ClaimLedger

open SSBX.Truth

structure ClaimEntry where
  id : ClaimId
  label : String
  kind : ClaimKind
  status : TruthStatus
  sourceRef : String
  deriving DecidableEq, Repr

def claimEntry : ClaimId -> ClaimEntry
  | .openDefinition => { id := .openDefinition, label := "开定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷六/卷十五：开_F" }
  | .closeDefinition => { id := .closeDefinition, label := "闭定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷六/卷十五：闭_F" }
  | .rightDefinition => { id := .rightDefinition, label := "正定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八/卷十五：正_F" }
  | .wrongDefinition => { id := .wrongDefinition, label := "邪定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八/卷十五：邪_F" }
  | .goodDefinition => { id := .goodDefinition, label := "好定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八：好_F" }
  | .badDefinition => { id := .badDefinition, label := "坏定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八：坏_F" }
  | .freedomDefinition => { id := .freedomDefinition, label := "自由定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八：自由" }
  | .flourishingDefinition => { id := .flourishingDefinition, label := "繁荣定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八：繁荣_F" }
  | .yiDefinition => { id := .yiDefinition, label := "义定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八：义_F" }
  | .shanDefinition => { id := .shanDefinition, label := "善定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八：善_F" }
  | .renDefinition => { id := .renDefinition, label := "仁定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八：仁_F" }
  | .daoDefinition => { id := .daoDefinition, label := "道定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷八：道_F" }
  | .trueDaoDefinition => { id := .trueDaoDefinition, label := "真道定义", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "卷八：真道_F" }
  | .auditUnbrokenDefinition => { id := .auditUnbrokenDefinition, label := "审校不败定义", kind := .definition, status := .ledgerDependent, sourceRef := "卷七：审校不败全拆式" }
  | .omegaInterface => { id := .omegaInterface, label := "Ω 接口", kind := .modelInterface, status := .ledgerDependent, sourceRef := "补篇〇：Ω" }
  | .omegaBInterface => { id := .omegaBInterface, label := "Ω_B 接口", kind := .modelInterface, status := .ledgerDependent, sourceRef := "补篇〇：Ω_B" }
  | .piOpenInterface => { id := .piOpenInterface, label := "Π_开 接口", kind := .modelInterface, status := .ledgerDependent, sourceRef := "补篇〇：Π_开" }
  | .thresholdProtocol => { id := .thresholdProtocol, label := "阈值协议", kind := .modelInterface, status := .ledgerDependent, sourceRef := "补篇〇：阈值设定法" }
  | .triValueConservativity => { id := .triValueConservativity, label := "三值保守性", kind := .proved, status := .machineChecked, sourceRef := "Core Tri unknown conservativity" }
  | .generatedRootsDiscipline => { id := .generatedRootsDiscipline, label := "生成项有根", kind := .proved, status := .machineChecked, sourceRef := "Roster generated_entries_have_roots" }
  | .recursiveSemanticsDiscipline => { id := .recursiveSemanticsDiscipline, label := "递归项有语义", kind := .proved, status := .machineChecked, sourceRef := "Roster recursive_entries_have_semantics" }
  | .rosterTextComplete => { id := .rosterTextComplete, label := "名册文字完备", kind := .registry, status := .machineChecked, sourceRef := "Text.Completeness roster_text_complete" }
  | .wenyanOperatorTableComplete => { id := .wenyanOperatorTableComplete, label := "文言算子表完备", kind := .registry, status := .machineChecked, sourceRef := "Text.Completeness operator_table_complete" }
  | .sourceTextClaimMapping => { id := .sourceTextClaimMapping, label := "文本 claim 映射", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "三本文完整版核心公式对应" }
  | .openValueAxiomClaim => { id := .openValueAxiomClaim, label := "开价值公理", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "公理账本：open_value_axiom" }
  | .auditReliabilityAxiomClaim => { id := .auditReliabilityAxiomClaim, label := "审校可靠公理", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "公理账本：audit_reliability_axiom" }
  | .omegaAdequacyAxiomClaim => { id := .omegaAdequacyAxiomClaim, label := "Ω 充分性公理", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "公理账本：omega_adequacy_axiom" }
  | .omegaBAdequacyAxiomClaim => { id := .omegaBAdequacyAxiomClaim, label := "Ω_B 充分性公理", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "公理账本：omegaB_adequacy_axiom" }
  | .piOpenAdequacyAxiomClaim => { id := .piOpenAdequacyAxiomClaim, label := "Π_开 充分性公理", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "公理账本：pi_open_adequacy_axiom" }
  | .truthPathAxiomClaim => { id := .truthPathAxiomClaim, label := "真道路径公理", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "公理账本：truth_path_axiom" }
  | .recommendationI1Evil => { id := .recommendationI1Evil, label := "推荐案例 i1 邪行", kind := .caseResult, status := .modelComputed, sourceRef := "补篇〇：推荐系统案例 i1" }
  | .recommendationI2Right => { id := .recommendationI2Right, label := "推荐案例 i2 正行", kind := .caseResult, status := .modelComputed, sourceRef := "补篇〇：推荐系统案例 i2 正行" }
  | .recommendationI2Ren => { id := .recommendationI2Ren, label := "推荐案例 i2 仁", kind := .caseResult, status := .modelComputed, sourceRef := "补篇〇：推荐系统案例 i2 仁" }
  | .recommendationI2CandidateTrueDao => { id := .recommendationI2CandidateTrueDao, label := "推荐案例 i2 候选真道", kind := .caseResult, status := .ledgerDependent, sourceRef := "补篇〇：推荐系统案例 i2 候选真道" }
  | .recommendationI3ProtectiveClosure => { id := .recommendationI3ProtectiveClosure, label := "推荐案例 i3 护闭", kind := .caseResult, status := .modelComputed, sourceRef := "补篇〇：推荐系统案例 i3" }
  | .semanticAdequacyClaim => { id := .semanticAdequacyClaim, label := "语义充分性总 claim", kind := .proved, status := .machineChecked, sourceRef := "Truth.Adequacy semantic_adequacy_complete" }
  | .absoluteTruthClaim => { id := .absoluteTruthClaim, label := "体系内绝对真理 claim", kind := .axiomBacked, status := .ledgerDependent, sourceRef := "Truth.Absolute ssbx_absolute_truth" }
  | .rootToSsbxLiClaim => { id := .rootToSsbxLiClaim, label := "根至生生不息成理 claim", kind := .proved, status := .machineChecked, sourceRef := "Foundation.Li shengsheng_buxi_is_li_from_ledger" }

def allClaimIds : List ClaimId := [
  .openDefinition, .closeDefinition, .rightDefinition, .wrongDefinition, .goodDefinition, .badDefinition,
  .freedomDefinition, .flourishingDefinition, .yiDefinition, .shanDefinition, .renDefinition, .daoDefinition,
  .trueDaoDefinition, .auditUnbrokenDefinition, .omegaInterface, .omegaBInterface, .piOpenInterface, .thresholdProtocol,
  .triValueConservativity, .generatedRootsDiscipline, .recursiveSemanticsDiscipline, .rosterTextComplete, .wenyanOperatorTableComplete, .sourceTextClaimMapping,
  .openValueAxiomClaim, .auditReliabilityAxiomClaim, .omegaAdequacyAxiomClaim, .omegaBAdequacyAxiomClaim, .piOpenAdequacyAxiomClaim, .truthPathAxiomClaim,
  .recommendationI1Evil, .recommendationI2Right, .recommendationI2Ren, .recommendationI2CandidateTrueDao, .recommendationI3ProtectiveClosure, .semanticAdequacyClaim,
  .absoluteTruthClaim, .rootToSsbxLiClaim,
]

def allClaims : List ClaimEntry :=
  allClaimIds.map claimEntry

/-- Claims whose current status is checked directly by Lean theorems. -/
def machineCheckedClaims : List ClaimId := [
  .triValueConservativity,
  .generatedRootsDiscipline,
  .recursiveSemanticsDiscipline,
  .rosterTextComplete,
  .wenyanOperatorTableComplete,
  .semanticAdequacyClaim,
  .rootToSsbxLiClaim,
]

/-- Claims whose current status depends on the explicit axiom/model/text ledger. -/
def ledgerDependentClaims : List ClaimId := [
  .openDefinition,
  .closeDefinition,
  .rightDefinition,
  .wrongDefinition,
  .goodDefinition,
  .badDefinition,
  .freedomDefinition,
  .flourishingDefinition,
  .yiDefinition,
  .shanDefinition,
  .renDefinition,
  .daoDefinition,
  .trueDaoDefinition,
  .auditUnbrokenDefinition,
  .omegaInterface,
  .omegaBInterface,
  .piOpenInterface,
  .thresholdProtocol,
  .sourceTextClaimMapping,
  .openValueAxiomClaim,
  .auditReliabilityAxiomClaim,
  .omegaAdequacyAxiomClaim,
  .omegaBAdequacyAxiomClaim,
  .piOpenAdequacyAxiomClaim,
  .truthPathAxiomClaim,
  .recommendationI2CandidateTrueDao,
  .absoluteTruthClaim,
]

/-- Claims whose current status is a finite model/case computation. -/
def modelComputedClaims : List ClaimId := [
  .recommendationI1Evil,
  .recommendationI2Right,
  .recommendationI2Ren,
  .recommendationI3ProtectiveClosure,
]

/-- Reserved status class; currently no registered claim uses it. -/
def registryCheckedClaims : List ClaimId := []

/-- Reserved status class; currently no registered claim uses it. -/
def pendingClaims : List ClaimId := []

def ClaimsWithStatus : TruthStatus -> List ClaimId
  | .machineChecked => machineCheckedClaims
  | .ledgerDependent => ledgerDependentClaims
  | .modelComputed => modelComputedClaims
  | .registryChecked => registryCheckedClaims
  | .pending => pendingClaims

/-- The hand-maintained `machineCheckedClaims` list matches `claimEntry`. -/
theorem machineCheckedClaims_exact (id : ClaimId) :
    id ∈ machineCheckedClaims ↔ (claimEntry id).status = .machineChecked := by
  cases id <;> decide

/-- The hand-maintained `ledgerDependentClaims` list matches `claimEntry`. -/
theorem ledgerDependentClaims_exact (id : ClaimId) :
    id ∈ ledgerDependentClaims ↔ (claimEntry id).status = .ledgerDependent := by
  cases id <;> decide

/-- The hand-maintained `modelComputedClaims` list matches `claimEntry`. -/
theorem modelComputedClaims_exact (id : ClaimId) :
    id ∈ modelComputedClaims ↔ (claimEntry id).status = .modelComputed := by
  cases id <;> decide

/-- `registryChecked` is intentionally unused by the current claim ledger. -/
theorem registryCheckedClaims_exact (id : ClaimId) :
    id ∈ registryCheckedClaims ↔ (claimEntry id).status = .registryChecked := by
  cases id <;> decide

/-- `pending` is intentionally unused by the current claim ledger. -/
theorem pendingClaims_exact (id : ClaimId) :
    id ∈ pendingClaims ↔ (claimEntry id).status = .pending := by
  cases id <;> decide

/-- Every current `ClaimId` lands in one of the three status classes used today. -/
theorem claimEntry_status_current (id : ClaimId) :
    (claimEntry id).status = .machineChecked ∨
      (claimEntry id).status = .ledgerDependent ∨
      (claimEntry id).status = .modelComputed := by
  cases id <;> decide

/-- Every current `ClaimId` is listed by one of the three nonempty status ledgers. -/
theorem currentStatusClaims_complete (id : ClaimId) :
    id ∈ machineCheckedClaims ∨ id ∈ ledgerDependentClaims ∨ id ∈ modelComputedClaims := by
  cases id <;> decide

/-- No registered claim currently has `registryChecked` status. -/
theorem no_registryChecked_claimEntry (id : ClaimId) :
    (claimEntry id).status ≠ .registryChecked := by
  cases id <;> decide

/-- No registered claim currently has `pending` status. -/
theorem no_pending_claimEntry (id : ClaimId) :
    (claimEntry id).status ≠ .pending := by
  cases id <;> decide

/-- A formal claim is admitted exactly when it is present in the v17 ledger. -/
def FormalClaim (c : ClaimEntry) : Prop :=
  c ∈ allClaims

theorem claim_ledger_complete (id : ClaimId) : id ∈ allClaimIds := by
  cases id <;> decide

theorem all_claims_have_entries (id : ClaimId) : claimEntry id ∈ allClaims := by
  unfold allClaims
  exact List.mem_map.mpr ⟨id, claim_ledger_complete id, rfl⟩

theorem no_unregistered_claim {c : ClaimEntry} : FormalClaim c -> c ∈ allClaims :=
  fun h => h

theorem no_unregistered_claim_entry (id : ClaimId) : FormalClaim (claimEntry id) :=
  all_claims_have_entries id

theorem formal_claim_status_current {c : ClaimEntry} (h : FormalClaim c) :
    c.status = .machineChecked ∨ c.status = .ledgerDependent ∨ c.status = .modelComputed := by
  unfold FormalClaim allClaims at h
  rcases List.mem_map.mp h with ⟨id, _hid, rfl⟩
  exact claimEntry_status_current id

theorem no_formal_claim_registryChecked {c : ClaimEntry} (h : FormalClaim c) :
    c.status ≠ .registryChecked := by
  unfold FormalClaim allClaims at h
  rcases List.mem_map.mp h with ⟨id, _hid, rfl⟩
  exact no_registryChecked_claimEntry id

theorem no_formal_claim_pending {c : ClaimEntry} (h : FormalClaim c) :
    c.status ≠ .pending := by
  unfold FormalClaim allClaims at h
  rcases List.mem_map.mp h with ⟨id, _hid, rfl⟩
  exact no_pending_claimEntry id

end SSBX.Truth.ClaimLedger
