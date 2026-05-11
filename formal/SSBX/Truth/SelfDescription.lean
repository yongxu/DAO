/-
Self-description certificates for claims, operators, and bit/position terms.

This module connects the text-facing description layer to already proved Lean
facts.  In particular, bit/position vocabulary is no longer just glyph-covered:
each position object is tied to the finite Yi/Bagua/HexagramPosition theorems
that give it mathematical content.
-/
import SSBX.Truth.Adequacy
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Bagua.Cell256
import SSBX.Foundation.Modern.HexagramPosition

namespace SSBX.Truth.SelfDescription

open SSBX.Roster
open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators
open SSBX.Truth
open SSBX.Truth.ClaimLedger
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.Yi.Trigram
open SSBX.Foundation.Yi.Yi.Hexagram
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Modern.HexagramPosition

/-! ## § 1 Objects of self-description -/

inductive BitPositionObject where
  | yin | yang
  | yaoOne | yaoTwo | yaoThree | yaoFour | yaoFive | yaoSix
  | trigram | hexagram | cell256
  | shiEternal | shiPast | shiPresent | shiFuture
  | wellPosition | centralPosition | responsePosition | neighborPosition
  | supportPosition | ridingPosition
  deriving DecidableEq, Repr

inductive DescriptionSubject where
  | claim : ClaimId -> DescriptionSubject
  | wenyanOperator : OperatorId -> DescriptionSubject
  | primitiveOperator : PrimName -> DescriptionSubject
  | derivedInterface : DerivedInterface -> DescriptionSubject
  | bitPosition : BitPositionObject -> DescriptionSubject
  deriving DecidableEq, Repr

/-! ## § 2 Glyph-level descriptions -/

def claimStatusPhrase : TruthStatus -> String
  | .machineChecked => "机校证"
  | .ledgerDependent => "册校证"
  | .modelComputed => "模算证"
  | .registryChecked => "册校证"
  | .pending => "待校证"

def claimKindPhrase : ClaimKind -> String
  | .definition => "定义"
  | .proved => "已证"
  | .axiomBacked => "理基"
  | .modelInterface => "模面"
  | .caseResult => "例证"
  | .registry => "册证"

/-- Claim descriptions use status/kind words, not unchecked theorem names. -/
def claimDescriptionForms (id : ClaimId) : List GlyphSense :=
  textToSenses (claimKindPhrase (claimEntry id).kind ++ claimStatusPhrase (claimEntry id).status)

def bitPositionForms : BitPositionObject -> List GlyphSense
  | .yin => textToSenses "阴"
  | .yang => textToSenses "阳"
  | .yaoOne => textToSenses "一位"
  | .yaoTwo => textToSenses "二位"
  | .yaoThree => textToSenses "三位"
  | .yaoFour => textToSenses "四位"
  | .yaoFive => textToSenses "五位"
  | .yaoSix => textToSenses "六位"
  | .trigram => textToSenses "三位八象"
  | .hexagram => textToSenses "六位六十四象"
  | .cell256 => textToSenses "格六十四四期"
  | .shiEternal => textToSenses "道期"
  | .shiPast => textToSenses "已期"
  | .shiPresent => textToSenses "中期"
  | .shiFuture => textToSenses "未期"
  | .wellPosition => textToSenses "当位"
  | .centralPosition => textToSenses "中位"
  | .responsePosition => textToSenses "应位"
  | .neighborPosition => textToSenses "比位"
  | .supportPosition => textToSenses "承位"
  | .ridingPosition => textToSenses "乘位"

def descriptionForms : DescriptionSubject -> List GlyphSense
  | .claim id => claimDescriptionForms id
  | .wenyanOperator id => (operatorEntry id).forms
  | .primitiveOperator p => primitiveGlyphAliases p
  | .derivedInterface i => i.lhsToken :: i.rhsGlyphs
  | .bitPosition b => bitPositionForms b

def SelfDescribed (s : DescriptionSubject) : Prop :=
  CoveredForms (descriptionForms s)

instance selfDescribedDecidable (s : DescriptionSubject) : Decidable (SelfDescribed s) := by
  unfold SelfDescribed
  infer_instance

theorem claim_descriptions_covered (id : ClaimId) :
    SelfDescribed (.claim id) := by
  cases id <;> native_decide

theorem wenyan_operator_descriptions_covered (id : OperatorId) :
    SelfDescribed (.wenyanOperator id) := by
  unfold SelfDescribed descriptionForms CoveredForms
  exact ⟨(SSBX.Text.Completeness.operator_table_complete id).2.1,
    (SSBX.Text.Completeness.operator_table_complete id).2.2.1⟩

theorem primitive_operator_descriptions_covered (p : PrimName) :
    SelfDescribed (.primitiveOperator p) := by
  exact SSBX.Text.Completeness.primitive_aliases_complete p

theorem derived_interface_descriptions_covered (i : DerivedInterface) :
    SelfDescribed (.derivedInterface i) := by
  cases i <;> native_decide

theorem bit_position_descriptions_covered (b : BitPositionObject) :
    SelfDescribed (.bitPosition b) := by
  cases b <;> native_decide

theorem self_descriptions_covered (s : DescriptionSubject) :
    SelfDescribed s := by
  cases s with
  | claim id => exact claim_descriptions_covered id
  | wenyanOperator id => exact wenyan_operator_descriptions_covered id
  | primitiveOperator p => exact primitive_operator_descriptions_covered p
  | derivedInterface i => exact derived_interface_descriptions_covered i
  | bitPosition b => exact bit_position_descriptions_covered b

/-! ## § 3 Bit/position vocabulary tied to actual theorems -/

def BitPositionVerified : BitPositionObject -> Prop
  | .yin => Yao.yin ≠ Yao.yang
  | .yang => Yao.yang ≠ Yao.yin
  | .yaoOne => ∀ h : Hexagram, atPos h ⟨0, by decide⟩ = h.y1
  | .yaoTwo => ∀ h : Hexagram, atPos h ⟨1, by decide⟩ = h.y2
  | .yaoThree => ∀ h : Hexagram, atPos h ⟨2, by decide⟩ = h.y3
  | .yaoFour => ∀ h : Hexagram, atPos h ⟨3, by decide⟩ = h.y4
  | .yaoFive => ∀ h : Hexagram, atPos h ⟨4, by decide⟩ = h.y5
  | .yaoSix => ∀ h : Hexagram, atPos h ⟨5, by decide⟩ = h.y6
  | .trigram => Trigram.all.length = 8 ∧ ∀ t : Trigram, t ∈ Trigram.all
  | .hexagram => Hexagram.allHex.length = 64 ∧ ∀ h : Hexagram, h ∈ Hexagram.allHex
  | .cell256 => Cell256.all.length = 256 ∧ ∀ c : Cell256, c ∈ Cell256.all
  | .shiEternal => Shi.dao ∈ Shi.all
  | .shiPast => Shi.ji ∈ Shi.all
  | .shiPresent => Shi.jin ∈ Shi.all
  | .shiFuture => Shi.wei ∈ Shi.all
  | .wellPosition =>
      wellPosCount complete = 6 ∧ wellPosCount incomplete = 0
        ∧ wellPosCountAt 0 + wellPosCountAt 1 + wellPosCountAt 2 + wellPosCountAt 3
            + wellPosCountAt 4 + wellPosCountAt 5 + wellPosCountAt 6 = 64
        ∧ ∀ h : Hexagram, ∀ i : Fin 6, wellPos h.cuo i = !(wellPos h i)
  | .centralPosition =>
      Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yang, Yao.yang))) = 16
        ∧ Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yang, Yao.yin))) = 16
        ∧ Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yin, Yao.yang))) = 16
        ∧ Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yin, Yao.yin))) = 16
        ∧ Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yang, Yao.yang)))
          + Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yang, Yao.yin)))
          + Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yin, Yao.yang)))
          + Hexagram.allHex.countP (fun h => decide (centralYaos h = (Yao.yin, Yao.yin))) = 64
  | .responsePosition =>
      respondsCountAt 0 = 8 ∧ respondsCountAt 1 = 24
        ∧ respondsCountAt 2 = 24 ∧ respondsCountAt 3 = 8
        ∧ respondsCountAt 0 + respondsCountAt 1 + respondsCountAt 2 + respondsCountAt 3 = 64
        ∧ (∀ h : Hexagram, respondsCount h.cuo = respondsCount h)
        ∧ (∀ h : Hexagram, respondsCount h.zong = respondsCount h)
  | .neighborPosition =>
      biCountAt 0 = 2 ∧ biCountAt 5 = 2
        ∧ biCountAt 0 + biCountAt 1 + biCountAt 2 + biCountAt 3
            + biCountAt 4 + biCountAt 5 = 64
        ∧ (∀ h : Hexagram, biCount h.cuo = biCount h)
        ∧ (∀ h : Hexagram, biCount h.zong = biCount h)
  | .supportPosition =>
      chenCount complete = 2 ∧ chenCount incomplete = 3
        ∧ (∀ h : Hexagram, chenCount h + chengCount h + biCount h = 5)
        ∧ (∀ h : Hexagram, chenCount h.cuo = chengCount h)
  | .ridingPosition =>
      chengCount complete = 3 ∧ chengCount incomplete = 2
        ∧ (∀ h : Hexagram, chenCount h + chengCount h + biCount h = 5)
        ∧ (∀ h : Hexagram, chengCount h.cuo = chenCount h)

theorem bit_position_verified (b : BitPositionObject) :
    BitPositionVerified b := by
  cases b with
  | yin =>
      intro h
      cases h
  | yang =>
      intro h
      cases h
  | yaoOne =>
      intro h
      cases h
      rfl
  | yaoTwo =>
      intro h
      cases h
      rfl
  | yaoThree =>
      intro h
      cases h
      rfl
  | yaoFour =>
      intro h
      cases h
      rfl
  | yaoFive =>
      intro h
      cases h
      rfl
  | yaoSix =>
      intro h
      cases h
      rfl
  | trigram =>
      exact ⟨rfl, trigram_mem_all⟩
  | hexagram =>
      exact ⟨Hexagram.allHex_count, hexagram_mem_allHex⟩
  | cell256 =>
      exact ⟨Cell256.all_length, Cell256.mem_all⟩
  | shiEternal =>
      change Shi.dao ∈ Shi.all
      simp [Shi.all]
  | shiPast =>
      change Shi.ji ∈ Shi.all
      simp [Shi.all]
  | shiPresent =>
      change Shi.jin ∈ Shi.all
      simp [Shi.all]
  | shiFuture =>
      change Shi.wei ∈ Shi.all
      simp [Shi.all]
  | wellPosition =>
      exact ⟨wellPosCount_jiji, wellPosCount_weiji, wellPosCountAt_total,
        cuo_flips_wellPos⟩
  | centralPosition =>
      exact ⟨centralYaos_each_16_yy, centralYaos_each_16_yYin,
        centralYaos_each_16_YinY, centralYaos_each_16_YinYin,
        centralYaos_partition_total⟩
  | responsePosition =>
      exact ⟨respondsCountAt_0, respondsCountAt_1, respondsCountAt_2,
        respondsCountAt_3, respondsCountAt_total, respondsCount_cuo_invariant,
        respondsCount_zong_invariant⟩
  | neighborPosition =>
      exact ⟨biCountAt_0, biCountAt_5, biCountAt_total, biCount_cuo_invariant,
        biCount_zong_invariant⟩
  | supportPosition =>
      exact ⟨chenCount_jiji, chenCount_weiji, chen_cheng_complement,
        chen_cuo_eq_cheng⟩
  | ridingPosition =>
      exact ⟨chengCount_jiji, chengCount_weiji, chen_cheng_complement,
        cheng_cuo_eq_chen⟩

def PositionSemanticsComplete : Prop :=
  ∀ b : BitPositionObject, CoveredForms (bitPositionForms b) ∧ BitPositionVerified b

theorem position_semantics_complete : PositionSemanticsComplete := by
  intro b
  exact ⟨bit_position_descriptions_covered b, bit_position_verified b⟩

/-! ## § 4 Finite completeness of the self-description registry -/

def allBitPositionObjects : List BitPositionObject := [
  .yin, .yang,
  .yaoOne, .yaoTwo, .yaoThree, .yaoFour, .yaoFive, .yaoSix,
  .trigram, .hexagram, .cell256,
  .shiEternal, .shiPast, .shiPresent, .shiFuture,
  .wellPosition, .centralPosition, .responsePosition, .neighborPosition,
  .supportPosition, .ridingPosition
]

def allDescriptionSubjects : List DescriptionSubject :=
  (allClaimIds.map DescriptionSubject.claim) ++
  (allOperatorIds.map DescriptionSubject.wenyanOperator) ++
  (allPrimitives.map DescriptionSubject.primitiveOperator) ++
  (allDerivedInterfaces.map DescriptionSubject.derivedInterface) ++
  (allBitPositionObjects.map DescriptionSubject.bitPosition)

theorem allBitPositionObjects_complete (b : BitPositionObject) :
    b ∈ allBitPositionObjects := by
  cases b <;> decide

theorem allDescriptionSubjects_complete (s : DescriptionSubject) :
    s ∈ allDescriptionSubjects := by
  cases s with
  | claim id => cases id <;> native_decide
  | wenyanOperator id => cases id <;> native_decide
  | primitiveOperator p => cases p <;> native_decide
  | derivedInterface i => cases i <;> native_decide
  | bitPosition b => cases b <;> native_decide

def CompleteSelfDescription : Prop :=
  ∀ s : DescriptionSubject, s ∈ allDescriptionSubjects ∧ SelfDescribed s

theorem complete_self_description : CompleteSelfDescription := by
  intro s
  exact ⟨allDescriptionSubjects_complete s, self_descriptions_covered s⟩

/-! ## § 5 Position-aware complete operator set -/

def TrigramOperatorComplete : Prop :=
  (∀ a b : Trigram, ∃ f : Trigram → Trigram, f a = b)
    ∧ (∀ t : Trigram, guiyi t = ())
    ∧ (∀ t : Trigram, Trigram.cuo t = motion (hua (bian t)))
    ∧ (∀ s : SiXiang, ∀ y : Yao, heShang (fenToTrigram s y) = s)
    ∧ (∀ y1 y2 y3 : Yao, grandCycle y1 y2 y3 = ())

def HexagramOperatorComplete : Prop :=
  (∀ h : Hexagram, Hexagram.cuo h
      = dongInner (huaInner (bianInner (dongOuter (huaOuter (bianOuter h))))))
    ∧ (∀ a b : Hexagram, ∃ f : Hexagram → Hexagram, f a = b)
    ∧ (∀ a b : Hexagram, hexHammingDist a b ≤ 6)

def Cell256OperatorComplete : Prop :=
  ∀ a b : Cell256, ∃ f : Cell256 → Cell256, f a = b

def OperatorCatalogueComplete : Prop :=
  (∀ id : OperatorId, CoveredOperator id)
    ∧ (∀ p : PrimName, CoveredPrimitiveAlias p)
    ∧ (∀ i : DerivedInterface, CoveredDerivedInterface i)
    ∧ TrigramOperatorComplete
    ∧ HexagramOperatorComplete
    ∧ Cell256OperatorComplete

def PositionAwareCompleteOperatorSet : Prop :=
  PositionSemanticsComplete ∧ OperatorCatalogueComplete

theorem trigram_operator_complete : TrigramOperatorComplete :=
  bagua_algebra_complete

theorem hexagram_operator_complete : HexagramOperatorComplete :=
  hex_algebra_complete

theorem shi_operator_complete (a b : Shi) :
    ∃ f : Shi → Shi, f a = b := by
  -- For any pair (a, b) of V₄ elements there exists a constant function
  -- s ↦ b. This is the trivial witness (V₄ is finite, so any pointwise
  -- mapping is realizable).
  exact ⟨fun _ => b, rfl⟩

theorem cell256_operator_complete : Cell256OperatorComplete := by
  intro a b
  rcases a with ⟨ha, sa⟩
  rcases b with ⟨hb, sb⟩
  obtain ⟨fh, hfh⟩ := hex_intercommunication ha hb
  obtain ⟨fs, hfs⟩ := shi_operator_complete sa sb
  refine ⟨fun c => (fh c.1, fs c.2), ?_⟩
  simp [hfh, hfs]

theorem operator_catalogue_complete : OperatorCatalogueComplete :=
  ⟨SSBX.Text.Completeness.operator_table_complete,
    SSBX.Text.Completeness.primitive_aliases_complete,
    SSBX.Text.Completeness.derived_interfaces_complete,
    trigram_operator_complete,
    hexagram_operator_complete,
    cell256_operator_complete⟩

theorem position_aware_complete_operator_set :
    PositionAwareCompleteOperatorSet :=
  ⟨position_semantics_complete, operator_catalogue_complete⟩

/-! ## § 6 Truth boundary retained by self-description -/

def ClaimBoundary (id : ClaimId) : TruthStatus :=
  (claimEntry id).status

theorem claim_boundary_current (id : ClaimId) :
    ClaimBoundary id = .machineChecked ∨
      ClaimBoundary id = .ledgerDependent ∨
      ClaimBoundary id = .modelComputed := by
  exact claimEntry_status_current id

theorem machine_checked_claims_described_as_machine_checked (id : ClaimId) :
    id ∈ machineCheckedClaims ↔ ClaimBoundary id = .machineChecked := by
  exact machineCheckedClaims_exact id

theorem ledger_dependent_claims_described_as_ledger_dependent (id : ClaimId) :
    id ∈ ledgerDependentClaims ↔ ClaimBoundary id = .ledgerDependent := by
  exact ledgerDependentClaims_exact id

theorem model_computed_claims_described_as_model_computed (id : ClaimId) :
    id ∈ modelComputedClaims ↔ ClaimBoundary id = .modelComputed := by
  exact modelComputedClaims_exact id

theorem self_description_summary :
    CompleteSelfDescription
      ∧ PositionSemanticsComplete
      ∧ PositionAwareCompleteOperatorSet
      ∧ (∀ id : ClaimId, ClaimBoundary id = .machineChecked ∨
          ClaimBoundary id = .ledgerDependent ∨ ClaimBoundary id = .modelComputed) :=
  ⟨complete_self_description, position_semantics_complete,
    position_aware_complete_operator_set, claim_boundary_current⟩

end SSBX.Truth.SelfDescription
