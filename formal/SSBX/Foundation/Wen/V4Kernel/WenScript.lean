/-
# Wen.V4Kernel.WenScript -- controlled wen proof script over V4/R5

This is the first "文编译文证明文" bridge:

* every nonempty source line after `零起` is parsed into a `Sentence`;
* controlled R5 definitions produce structural certificates;
* general prose is kept in typed syntax buckets and is not promoted to a
  theorem;
* `claimStub` is reserved for malformed controlled forms.
-/

import SSBX.Foundation.Wen.V4Kernel.WenR6
import SSBX.Foundation.Wen.V4Kernel.Root512
import SSBX.Foundation.Wen.Kernel
import SSBX.Foundation.Wen.Layered.Bridges.Word64
import SSBX.Text.WenyanOperators.Table

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators
open SSBX.Text.WenyanOperators

namespace WenScript

/-! ## V4/R4/R5 structural words -/

inductive BenWord where
  | thing
  | motion
  | interval
  | event
  deriving DecidableEq, BEq, Repr

inductive ZhengWord where
  | trace
  | momentum
  | pivot
  | occasion
  deriving DecidableEq, BEq, Repr

inductive ExtensionBit where
  | yang
  | yin
  deriving DecidableEq, BEq, Repr

structure R4Word where
  ben : BenWord
  zheng : ZhengWord
  deriving DecidableEq, BEq, Repr

structure R5Word where
  base : R4Word
  extension : ExtensionBit
  deriving DecidableEq, BEq, Repr

namespace BenWord

def toV4 : BenWord → V4
  | .thing => .dao
  | .motion => .zong
  | .interval => .cuo
  | .event => .cuoZong

def chinese : BenWord → String
  | .thing => "物"
  | .motion => "动"
  | .interval => "间"
  | .event => "事"

def ofChar : Char → Option BenWord
  | '物' => some .thing
  | '动' => some .motion
  | '間' => some .interval
  | '间' => some .interval
  | '事' => some .event
  | _ => none

end BenWord

namespace ZhengWord

def toV4 : ZhengWord → V4
  | .trace => .dao
  | .momentum => .zong
  | .pivot => .cuo
  | .occasion => .cuoZong

def chinese : ZhengWord → String
  | .trace => "几"
  | .momentum => "势"
  | .pivot => "机"
  | .occasion => "时"

def ofChar : Char → Option ZhengWord
  | '几' => some .trace
  | '勢' => some .momentum
  | '势' => some .momentum
  | '機' => some .pivot
  | '机' => some .pivot
  | '時' => some .occasion
  | '时' => some .occasion
  | _ => none

end ZhengWord

namespace ExtensionBit

def toBool : ExtensionBit → Bool
  | .yang => false
  | .yin => true

def ofBool : Bool → ExtensionBit
  | false => .yang
  | true => .yin

def chinese : ExtensionBit → String
  | .yang => "阳"
  | .yin => "阴"

def ofChar : Char → Option ExtensionBit
  | '阳' => some .yang
  | '陽' => some .yang
  | '阴' => some .yin
  | '陰' => some .yin
  | _ => none

@[simp] theorem ofBool_toBool (b : ExtensionBit) :
    ofBool b.toBool = b := by
  cases b <;> rfl

@[simp] theorem toBool_ofBool (b : Bool) :
    (ofBool b).toBool = b := by
  cases b <;> rfl

end ExtensionBit

namespace R4Word

def toPair (r : R4Word) : V4 × V4 :=
  (r.ben.toV4, r.zheng.toV4)

def chinese (r : R4Word) : String :=
  r.ben.chinese ++ r.zheng.chinese

end R4Word

namespace R5Word

def toView (r : R5Word) : R5View :=
  ⟨r.base.ben.toV4, r.base.zheng.toV4, r.extension.toBool⟩

def ofView (view : R5View) : R5Word :=
  let ben :=
    match view.first with
    | .dao => BenWord.thing
    | .zong => BenWord.motion
    | .cuo => BenWord.interval
    | .cuoZong => BenWord.event
  let zheng :=
    match view.second with
    | .dao => ZhengWord.trace
    | .zong => ZhengWord.momentum
    | .cuo => ZhengWord.pivot
    | .cuoZong => ZhengWord.occasion
  ⟨⟨ben, zheng⟩, ExtensionBit.ofBool view.extension⟩

def xorBit (a b : ExtensionBit) : ExtensionBit :=
  ExtensionBit.ofBool (decide (a ≠ b))

def compose (a b : R5Word) : R5Word :=
  ofView
    ⟨ V4.compose a.base.ben.toV4 b.base.ben.toV4
    , V4.compose a.base.zheng.toV4 b.base.zheng.toV4
    , (xorBit a.extension b.extension).toBool
    ⟩

def chinese (r : R5Word) : String :=
  r.base.chinese ++ r.extension.chinese

@[simp] theorem ofView_toView (r : R5Word) :
    ofView (toView r) = r := by
  cases r with
  | mk base extension =>
      cases base with
      | mk ben zheng =>
          cases ben <;> cases zheng <;> cases extension <;> rfl

@[simp] theorem toView_ofView (view : R5View) :
    toView (ofView view) = view := by
  cases view with
  | mk first second extension =>
      cases first <;> cases second <;> cases extension <;> rfl

theorem compose_closed (a b : R5Word) :
    ∃ c : R5Word, c = compose a b := ⟨compose a b, rfl⟩

end R5Word

/-! ## Kernel bridge for 五常属道 -/

abbrev KernelWuchang := _root_.SSBX.Foundation.Wen.Kernel.WuchangKind

def kernelWuchangOfName : String → Option KernelWuchang
  | "仁" => some .ren
  | "义" => some .yi
  | "義" => some .yi
  | "礼" => some .li
  | "禮" => some .li
  | "智" => some .zhi
  | "信" => some .xin
  | _ => none

def kernelWuchangR5 : KernelWuchang → R5Word
  | .ren => ⟨⟨.interval, .trace⟩, .yang⟩
  | .yi => ⟨⟨.motion, .occasion⟩, .yang⟩
  | .li => ⟨⟨.thing, .momentum⟩, .yang⟩
  | .zhi => ⟨⟨.interval, .pivot⟩, .yang⟩
  | .xin => ⟨⟨.event, .trace⟩, .yang⟩

/-- WenScript may only emit a 五常属道 certificate when the text's R5
    definition matches the kernel bridge and the corresponding kernel
    `WuchangKind.daoComponent` theorem exists. -/
def kernelDaoMembershipCheck (name : String) (value : R5Word) : Bool :=
  match kernelWuchangOfName name with
  | some kind => decide (kernelWuchangR5 kind = value)
  | none => false

theorem kernelDaoMembershipCheck_sound {name : String} {value : R5Word}
    (h : kernelDaoMembershipCheck name value = true) :
    ∃ kind : KernelWuchang,
      kernelWuchangOfName name = some kind
        ∧ kernelWuchangR5 kind = value
        ∧ _root_.SSBX.Foundation.Wen.Kernel.WuchangKind.daoComponent kind := by
  unfold kernelDaoMembershipCheck at h
  cases hname : kernelWuchangOfName name with
  | none =>
      simp [hname] at h
  | some kind =>
      refine ⟨kind, rfl, ?_, _root_.SSBX.Foundation.Wen.Kernel.WuchangKind.belongs_to_dao kind⟩
      have hdec : decide (kernelWuchangR5 kind = value) = true := by
        simpa [hname] using h
      exact of_decide_eq_true hdec

/-! ## Controlled sentence AST -/

inductive OperatorMode where
  | v4
  | application
  | relate
  | transform
  | negate
  | modal
  | causation
  | quantifier
  | naming
  | discourse
  | root512
  | textLayer
  deriving DecidableEq, Repr

inductive OperatorCarrier where
  | v4Builtin (value : V4)
  | applicationParticle
  | root512 (reading : Root512.RootReading)
  | textLayer (code title : String) (mode : OperatorMode)
  deriving DecidableEq, Repr

inductive OperatorForm where
  | prefix
  | infix
  | applicationParticle
  | mixfix
  | discourse
  deriving DecidableEq, Repr

structure OperatorToken where
  surface : String
  carrier : OperatorCarrier
  deriving DecidableEq, Repr

structure OperatorApplication where
  op : OperatorToken
  args : List String
  form : OperatorForm
  deriving DecidableEq, Repr

namespace OperatorMode

def label : OperatorMode → String
  | .v4 => "v4"
  | .application => "application"
  | .relate => "relate"
  | .transform => "transform"
  | .negate => "negate"
  | .modal => "modal"
  | .causation => "causation"
  | .quantifier => "quantifier"
  | .naming => "naming"
  | .discourse => "discourse"
  | .root512 => "root512"
  | .textLayer => "textLayer"

end OperatorMode

namespace OperatorCarrier

def mode : OperatorCarrier → OperatorMode
  | .v4Builtin _ => .v4
  | .applicationParticle => .application
  | .root512 _ => .root512
  | .textLayer _ _ mode => mode

def label : OperatorCarrier → String
  | .v4Builtin _ => "v4Builtin"
  | .applicationParticle => "applicationParticle"
  | .root512 reading => s!"root512:{reading.kind.label}"
  | .textLayer code _ mode => s!"textLayer:{code}:{mode.label}"

end OperatorCarrier

namespace OperatorForm

def label : OperatorForm → String
  | .prefix => "prefix"
  | .infix => "infix"
  | .applicationParticle => "applicationParticle"
  | .mixfix => "mixfix"
  | .discourse => "discourse"

end OperatorForm

namespace OperatorApplication

def mode (app : OperatorApplication) : OperatorMode :=
  app.op.carrier.mode

def summary (app : OperatorApplication) : String :=
  s!"{app.op.surface}({app.op.carrier.label})/{app.form.label} args={app.args}"

def surfaceLine (app : OperatorApplication) : String :=
  match app.form, app.args with
  | .prefix, [body] => app.op.surface ++ body
  | .infix, [left, right] => left ++ app.op.surface ++ right
  | .applicationParticle, [arg] => app.op.surface ++ "之" ++ arg
  | _, _ => app.op.surface ++ String.intercalate "" app.args

end OperatorApplication

inductive TextTerm where
  | name (surface : String)
  | anaphor (resolvesTo : String)
  deriving DecidableEq, Repr

inductive FormationOperator where
  | cheng
  | li
  | predicate (surface : String)
  deriving DecidableEq, Repr

namespace FormationOperator

def surface : FormationOperator → String
  | .cheng => "成"
  | .li => "立"
  | .predicate surface => surface

def applyTo (op : FormationOperator) (result : String) : String :=
  match op with
  | .predicate surface => surface
  | _ => op.surface ++ result

end FormationOperator

inductive ClauseAST where
  | notAsObject (principle object : String)
  | instrumentalFormation
      (subject : String) (instrument : TextTerm)
      (operator : FormationOperator) (result : String)
  | sequence (left right : ClauseAST)
  deriving DecidableEq, Repr

structure TextSchemaInstantiation where
  ruleId : String
  principle : String
  object : String
  operator : FormationOperator
  result : String
  clause : ClauseAST
  deriving DecidableEq, Repr

namespace TextSchemaInstantiation

def summary (inst : TextSchemaInstantiation) : String :=
  s!"principle={inst.principle};object={inst.object};result={inst.operator.applyTo inst.result}"

end TextSchemaInstantiation

inductive CapabilityClauseAST where
  | passiveAvailable (subject action result : String)
  | activeCan (subject action result : String)
  deriving DecidableEq, Repr

structure CapabilitySchemaInstantiation where
  ruleId : String
  subject : String
  action : String
  result : String
  clause : CapabilityClauseAST
  deriving DecidableEq, Repr

namespace CapabilitySchemaInstantiation

def summary (inst : CapabilitySchemaInstantiation) : String :=
  s!"subject={inst.subject};action={inst.action};result={inst.result}"

end CapabilitySchemaInstantiation

inductive StructuralClauseAST where
  | contextRole (item context role : String)
  | roleAssignment (subject role : String)
  | construction (source result : String)
  | eachHas (domain field : String)
  | location (subject place : String)
  | possession (subject object : String)
  | negatedPredicate (subject predicate : String)
  | possibility (subject predicate : String)
  deriving DecidableEq, Repr

structure StructuralSchemaInstantiation where
  ruleId : String
  subject : String
  relation : String
  object : String
  clause : StructuralClauseAST
  deriving DecidableEq, Repr

namespace StructuralSchemaInstantiation

def summary (inst : StructuralSchemaInstantiation) : String :=
  s!"subject={inst.subject};relation={inst.relation};object={inst.object}"

end StructuralSchemaInstantiation

inductive DualityClauseAST where
  | fourfoldReading (subject : String)
  | contentFrameComposite (subject : String)
  | consequenceBone (subject : String)
  | reversalReturn (subject object : String)
  deriving DecidableEq, Repr

structure DualitySchemaInstantiation where
  ruleId : String
  subject : String
  reading : String
  clause : DualityClauseAST
  deriving DecidableEq, Repr

namespace DualitySchemaInstantiation

def summary (inst : DualitySchemaInstantiation) : String :=
  s!"subject={inst.subject};reading={inst.reading}"

end DualitySchemaInstantiation

inductive DiscourseClauseAST where
  | absenceDegrades
      (missing subject remainder value : String)
  | selfRule
      (subject source result : String)
  | causative
      (actor result : String)
  deriving DecidableEq, Repr

structure DiscourseSchemaInstantiation where
  ruleId : String
  subject : String
  relation : String
  object : String
  clause : DiscourseClauseAST
  deriving DecidableEq, Repr

namespace DiscourseSchemaInstantiation

def summary (inst : DiscourseSchemaInstantiation) : String :=
  s!"subject={inst.subject};relation={inst.relation};object={inst.object}"

end DiscourseSchemaInstantiation

inductive Sentence where
  | defineR5 (name : String) (value : R5Word)
  | topicComment (subject body : String)
  | implication (condition conclusion : String)
  | universal (domain predicate : String)
  | instantiateUniversal (name predicate : String)
  | operatorApp (app : OperatorApplication)
  | assertion (body : String)
  | barePhrase (text : String) (tokens : List String)
  | alias (left right : String)
  | enumHead (name : String)
  | verifyR5 (name : String)
  | verifyKernelDao (name : String)
  | readThenVerify
  | claimStub (text : String) (tokens : List String)
  deriving DecidableEq, Repr

structure SourceSpan where
  line : Nat
  startColumn : Nat
  endColumn : Nat
  deriving Repr, DecidableEq

structure LocatedSentence where
  line : Nat
  column : Nat
  span : SourceSpan
  text : String
  sentence : Sentence
  deriving Repr

structure Document where
  sentences : List Sentence
  located : List LocatedSentence
  deriving Repr

inductive SemanticCertificateKind where
  | cyclicPersistence
  | rootActionImplication
  | aliasIdentity
  | copulaAlias
  | aliasInseparability
  | certificateAvailability
  | stateImplication
  | universalSchema
  | universalInstantiation
  | readThenVerifyAvailable
  | v4ActionTrace
  | rootActionTrace
  | openObligationAvailability
  | frontierClean
  | calculationAvailability
  | openCalculationAvailability
  | nameAvailability
  | pendingNameAvailability
  | wenCapability
  | nameResolutionRule
  | kernelDaoMembership
  | v4OperatorTopic
  | wenBoundary
  | nameValueLaw
  | v4DualityLaw
  | rootStructureLaw
  | textSchemaInstantiation
  | topicRegistration
  | implicationRegistration
  | operatorRegistration
  deriving DecidableEq, Repr

namespace SemanticCertificateKind

def label : SemanticCertificateKind → String
  | .cyclicPersistence => "cyclicPersistence"
  | .rootActionImplication => "rootActionImplication"
  | .aliasIdentity => "aliasIdentity"
  | .copulaAlias => "copulaAlias"
  | .aliasInseparability => "aliasInseparability"
  | .certificateAvailability => "certificateAvailability"
  | .stateImplication => "stateImplication"
  | .universalSchema => "universalSchema"
  | .universalInstantiation => "universalInstantiation"
  | .readThenVerifyAvailable => "readThenVerifyAvailable"
  | .v4ActionTrace => "v4ActionTrace"
  | .rootActionTrace => "rootActionTrace"
  | .openObligationAvailability => "openObligationAvailability"
  | .frontierClean => "frontierClean"
  | .calculationAvailability => "calculationAvailability"
  | .openCalculationAvailability => "openCalculationAvailability"
  | .nameAvailability => "nameAvailability"
  | .pendingNameAvailability => "pendingNameAvailability"
  | .wenCapability => "wenCapability"
  | .nameResolutionRule => "nameResolutionRule"
  | .kernelDaoMembership => "kernelDaoMembership"
  | .v4OperatorTopic => "v4OperatorTopic"
  | .wenBoundary => "wenBoundary"
  | .nameValueLaw => "nameValueLaw"
  | .v4DualityLaw => "v4DualityLaw"
  | .rootStructureLaw => "rootStructureLaw"
  | .textSchemaInstantiation => "textSchemaInstantiation"
  | .topicRegistration => "topicRegistration"
  | .implicationRegistration => "implicationRegistration"
  | .operatorRegistration => "operatorRegistration"

def isRegistration : SemanticCertificateKind → Bool
  | .universalSchema => true
  | .topicRegistration => true
  | .implicationRegistration => true
  | .operatorRegistration => true
  | _ => false

def isExecutable : SemanticCertificateKind → Bool
  | .v4ActionTrace => true
  | .rootActionTrace => true
  | .rootActionImplication => true
  | _ => false

def isStatus : SemanticCertificateKind → Bool
  | .certificateAvailability => true
  | .readThenVerifyAvailable => true
  | .openObligationAvailability => true
  | .frontierClean => true
  | .calculationAvailability => true
  | .openCalculationAvailability => true
  | .nameAvailability => true
  | .pendingNameAvailability => true
  | .wenBoundary => true
  | _ => false

def countsAsEvidence (kind : SemanticCertificateKind) : Bool :=
  !(kind.isRegistration || kind.isStatus)

end SemanticCertificateKind

structure SemanticCertificate where
  subject : String
  body : String
  kind : SemanticCertificateKind
  wellFormed : Bool
  deriving Repr

def countSemanticCertificatesWhere (p : SemanticCertificateKind → Bool) :
    List SemanticCertificate → Nat
  | [] => 0
  | cert :: rest =>
      (if p cert.kind then 1 else 0)
        + countSemanticCertificatesWhere p rest

inductive DiagnosticKind where
  | unsupportedTopicTheorem
  | unsupportedImplicationProof
  | unsupportedUniversalInstantiation
  | unsupportedReadThenVerify
  | unsupportedTextLayerOperator
  | unsupportedApplicationGrammar
  | unknownActionArgument
  | claimStub
  deriving DecidableEq, Repr

namespace DiagnosticKind

def label : DiagnosticKind → String
  | .unsupportedTopicTheorem => "unsupportedTopicTheorem"
  | .unsupportedImplicationProof => "unsupportedImplicationProof"
  | .unsupportedUniversalInstantiation => "unsupportedUniversalInstantiation"
  | .unsupportedReadThenVerify => "unsupportedReadThenVerify"
  | .unsupportedTextLayerOperator => "unsupportedTextLayerOperator"
  | .unsupportedApplicationGrammar => "unsupportedApplicationGrammar"
  | .unknownActionArgument => "unknownActionArgument"
  | .claimStub => "claimStub"

end DiagnosticKind

structure Diagnostic where
  line : Nat
  column : Nat
  span : SourceSpan
  kind : DiagnosticKind
  message : String
  text : String
  deriving Repr

structure FrontierSummary where
  unsupportedTopicTheorems : Nat
  unsupportedImplicationProofs : Nat
  unsupportedUniversalInstantiations : Nat
  unsupportedReadThenVerifications : Nat
  unsupportedTextLayerOperators : Nat
  unsupportedApplicationGrammars : Nat
  unknownActionArguments : Nat
  claimStubDiagnostics : Nat
  deriving Repr, DecidableEq

namespace FrontierSummary

  def openCount (summary : FrontierSummary) : Nat :=
  summary.unsupportedTopicTheorems
    + summary.unsupportedImplicationProofs
    + summary.unsupportedUniversalInstantiations
    + summary.unsupportedReadThenVerifications
    + summary.unsupportedTextLayerOperators
    + summary.unsupportedApplicationGrammars
    + summary.unknownActionArguments
    + summary.claimStubDiagnostics

def clean (summary : FrontierSummary) : Bool :=
  summary.openCount == 0

end FrontierSummary

def countDiagnosticsOfKind (kind : DiagnosticKind) :
    List Diagnostic → Nat
  | [] => 0
  | diagnostic :: rest =>
      (if diagnostic.kind = kind then 1 else 0)
        + countDiagnosticsOfKind kind rest

def frontierSummaryOfDiagnostics (diagnostics : List Diagnostic) :
    FrontierSummary :=
  { unsupportedTopicTheorems :=
      countDiagnosticsOfKind .unsupportedTopicTheorem diagnostics
  , unsupportedImplicationProofs :=
      countDiagnosticsOfKind .unsupportedImplicationProof diagnostics
  , unsupportedUniversalInstantiations :=
      countDiagnosticsOfKind .unsupportedUniversalInstantiation diagnostics
  , unsupportedReadThenVerifications :=
      countDiagnosticsOfKind .unsupportedReadThenVerify diagnostics
  , unsupportedTextLayerOperators :=
      countDiagnosticsOfKind .unsupportedTextLayerOperator diagnostics
  , unsupportedApplicationGrammars :=
      countDiagnosticsOfKind .unsupportedApplicationGrammar diagnostics
  , unknownActionArguments :=
      countDiagnosticsOfKind .unknownActionArgument diagnostics
  , claimStubDiagnostics :=
      countDiagnosticsOfKind .claimStub diagnostics }

structure R5Certificate where
  name : String
  value : R5Word
  wellFormed : Bool
  roundtrip : Bool
  projection : R4Word
  deriving Repr

structure V4ActionTrace where
  operatorSurface : String
  operator : V4
  argumentSurface : String
  argument : Word64
  result : Word64
  deriving Repr

structure ProofReport where
  definitions : List (String × R5Word)
  certificates : List R5Certificate
  semanticCertificates : List SemanticCertificate
  v4Actions : List V4ActionTrace
  rootApplications : List Root512.ApplicationTrace
  diagnostics : List Diagnostic
  aliases : List (String × String)
  topicComments : List (String × String)
  implications : List (String × String)
  universals : List (String × String)
  operatorApps : List OperatorApplication
  assertions : List String
  barePhrases : List (String × List String)
  aliasCount : Nat
  enumCount : Nat
  readVerifyCount : Nat
  claimStubs : List (String × List String)
  deriving Repr

namespace ProofReport

def frontierSummary (report : ProofReport) : FrontierSummary :=
  frontierSummaryOfDiagnostics report.diagnostics

def semanticRegistrationCount (report : ProofReport) : Nat :=
  countSemanticCertificatesWhere SemanticCertificateKind.isRegistration
    report.semanticCertificates

def semanticKindCount (report : ProofReport)
    (kind : SemanticCertificateKind) : Nat :=
  countSemanticCertificatesWhere (fun candidate => candidate = kind)
    report.semanticCertificates

def semanticCheckedCount (report : ProofReport) : Nat :=
  report.semanticCertificates.length - report.semanticRegistrationCount

def semanticExecutableCount (report : ProofReport) : Nat :=
  countSemanticCertificatesWhere SemanticCertificateKind.isExecutable
    report.semanticCertificates

def semanticStatusCount (report : ProofReport) : Nat :=
  countSemanticCertificatesWhere SemanticCertificateKind.isStatus
    report.semanticCertificates

def semanticEvidenceCount (report : ProofReport) : Nat :=
  countSemanticCertificatesWhere SemanticCertificateKind.countsAsEvidence
    report.semanticCertificates

def strictClean (report : ProofReport) : Bool :=
  report.frontierSummary.clean && report.claimStubs.length == 0

end ProofReport

def R5Certificate.ofDefinition (name : String) (value : R5Word) : R5Certificate :=
  { name := name
  , value := value
  , wellFormed := true
  , roundtrip := decide (R5Word.ofView value.toView = value)
  , projection := value.base }

theorem certificate_roundtrip_true (name : String) (value : R5Word) :
    (R5Certificate.ofDefinition name value).roundtrip = true := by
  simp [R5Certificate.ofDefinition]

def SemanticCertificate.cyclicPersistence : SemanticCertificate :=
  { subject := "生生不息"
  , body := "往复而不穷"
  , kind := .cyclicPersistence
  , wellFormed := true }

def SemanticCertificate.aliasIdentity (left right : String) :
    SemanticCertificate :=
  { subject := left
  , body := right
  , kind := .aliasIdentity
  , wellFormed := true }

def SemanticCertificate.copulaAlias (left right : String) :
    SemanticCertificate :=
  { subject := left
  , body := right
  , kind := .copulaAlias
  , wellFormed := true }

def SemanticCertificate.aliasInseparability (left right : String) :
    SemanticCertificate :=
  { subject := left
  , body := s!"不离{right}"
  , kind := .aliasInseparability
  , wellFormed := true }

def SemanticCertificate.certificateAvailability : SemanticCertificate :=
  { subject := "有"
  , body := "可证"
  , kind := .certificateAvailability
  , wellFormed := true }

def SemanticCertificate.universalSchema (domain predicate : String) :
    SemanticCertificate :=
  { subject := domain
  , body := predicate
  , kind := .universalSchema
  , wellFormed := true }

def SemanticCertificate.universalInstantiation (name predicate : String) :
    SemanticCertificate :=
  { subject := name
  , body := predicate
  , kind := .universalInstantiation
  , wellFormed := true }

def SemanticCertificate.readThenVerifyAvailable : SemanticCertificate :=
  { subject := "读"
  , body := "验"
  , kind := .readThenVerifyAvailable
  , wellFormed := true }

def SemanticCertificate.v4ActionTrace (trace : V4ActionTrace) :
    SemanticCertificate :=
  { subject := s!"{trace.operatorSurface}之{trace.argumentSurface}"
  , body := "V4作用"
  , kind := .v4ActionTrace
  , wellFormed := true }

def SemanticCertificate.rootActionTrace (trace : Root512.ApplicationTrace) :
    SemanticCertificate :=
  { subject := s!"{trace.operatorSurface}之{trace.argumentSurface}"
  , body := "Root512作用"
  , kind := .rootActionTrace
  , wellFormed := true }

def SemanticCertificate.openObligationAvailability (openCount : Nat) :
    SemanticCertificate :=
  { subject := "有"
  , body := s!"未证:{openCount}"
  , kind := .openObligationAvailability
  , wellFormed := true }

def SemanticCertificate.frontierClean : SemanticCertificate :=
  { subject := "无"
  , body := "未证"
  , kind := .frontierClean
  , wellFormed := true }

def SemanticCertificate.calculationAvailability : SemanticCertificate :=
  { subject := "有"
  , body := "可算"
  , kind := .calculationAvailability
  , wellFormed := true }

def SemanticCertificate.openCalculationAvailability (openCount : Nat) :
    SemanticCertificate :=
  { subject := "有"
  , body := s!"未算:{openCount}"
  , kind := .openCalculationAvailability
  , wellFormed := true }

def SemanticCertificate.nameAvailability : SemanticCertificate :=
  { subject := "有"
  , body := "已名"
  , kind := .nameAvailability
  , wellFormed := true }

def SemanticCertificate.pendingNameAvailability (openCount : Nat) :
    SemanticCertificate :=
  { subject := "有"
  , body := s!"待名:{openCount}"
  , kind := .pendingNameAvailability
  , wellFormed := true }

def SemanticCertificate.wenCapability (subject body : String) :
    SemanticCertificate :=
  { subject := subject
  , body := body
  , kind := .wenCapability
  , wellFormed := true }

def SemanticCertificate.nameResolutionRule (condition conclusion : String) :
    SemanticCertificate :=
  { subject := condition
  , body := conclusion
  , kind := .nameResolutionRule
  , wellFormed := true }

def SemanticCertificate.kernelDaoMembership (name : String) (value : R5Word) :
    SemanticCertificate :=
  { subject := name
  , body := s!"核证属道:{value.chinese}"
  , kind := .kernelDaoMembership
  , wellFormed := kernelDaoMembershipCheck name value }

def SemanticCertificate.v4OperatorTopic (subject body : String) :
    SemanticCertificate :=
  { subject := subject
  , body := body
  , kind := .v4OperatorTopic
  , wellFormed := true }

def SemanticCertificate.wenBoundary (subject body : String) :
    SemanticCertificate :=
  { subject := subject
  , body := body
  , kind := .wenBoundary
  , wellFormed := true }

def SemanticCertificate.nameValueLaw (subject body : String) :
    SemanticCertificate :=
  { subject := subject
  , body := body
  , kind := .nameValueLaw
  , wellFormed := true }

def SemanticCertificate.v4DualityLaw (subject body : String) :
    SemanticCertificate :=
  { subject := subject
  , body := body
  , kind := .v4DualityLaw
  , wellFormed := true }

def SemanticCertificate.rootStructureLaw (subject body : String) :
    SemanticCertificate :=
  { subject := subject
  , body := body
  , kind := .rootStructureLaw
  , wellFormed := true }

def SemanticCertificate.textSchemaInstantiation
    (inst : TextSchemaInstantiation) : SemanticCertificate :=
  { subject := inst.ruleId
  , body := inst.summary
  , kind := .textSchemaInstantiation
  , wellFormed := true }

def SemanticCertificate.capabilitySchemaInstantiation
    (inst : CapabilitySchemaInstantiation) : SemanticCertificate :=
  { subject := inst.ruleId
  , body := inst.summary
  , kind := .textSchemaInstantiation
  , wellFormed := true }

def SemanticCertificate.structuralSchemaInstantiation
    (inst : StructuralSchemaInstantiation) : SemanticCertificate :=
  { subject := inst.ruleId
  , body := inst.summary
  , kind := .textSchemaInstantiation
  , wellFormed := true }

def SemanticCertificate.dualitySchemaInstantiation
    (inst : DualitySchemaInstantiation) : SemanticCertificate :=
  { subject := inst.ruleId
  , body := inst.summary
  , kind := .textSchemaInstantiation
  , wellFormed := true }

def SemanticCertificate.discourseSchemaInstantiation
    (inst : DiscourseSchemaInstantiation) : SemanticCertificate :=
  { subject := inst.ruleId
  , body := inst.summary
  , kind := .textSchemaInstantiation
  , wellFormed := true }

def SemanticCertificate.topicRegistration (subject body : String) :
    SemanticCertificate :=
  { subject := subject
  , body := body
  , kind := .topicRegistration
  , wellFormed := true }

def SemanticCertificate.implicationRegistration (condition conclusion : String) :
    SemanticCertificate :=
  { subject := condition
  , body := conclusion
  , kind := .implicationRegistration
  , wellFormed := true }

def SemanticCertificate.operatorRegistration (app : OperatorApplication) :
    SemanticCertificate :=
  { subject := app.op.surface
  , body := String.intercalate "," app.args
  , kind := .operatorRegistration
  , wellFormed := true }

def SemanticCertificate.stateImplication (condition conclusion : String) :
    SemanticCertificate :=
  { subject := condition
  , body := conclusion
  , kind := .stateImplication
  , wellFormed := true }

def SemanticCertificate.controlled (kind : SemanticCertificateKind)
    (subject body : String) : SemanticCertificate :=
  { subject := subject
  , body := body
  , kind := kind
  , wellFormed := true }

structure ControlledTopicBridge where
  sourceSubject : String
  sourceBody : String
  kind : SemanticCertificateKind
  subject : String
  body : String
  deriving Repr, DecidableEq

structure ControlledImplicationBridge where
  condition : String
  conclusion : String
  kind : SemanticCertificateKind
  subject : String
  body : String
  deriving Repr, DecidableEq

structure ControlledOperatorBridge where
  surface : String
  form : OperatorForm
  args : List String
  kind : SemanticCertificateKind
  subject : String
  body : String
  deriving Repr, DecidableEq

def ControlledTopicBridge.certificate (bridge : ControlledTopicBridge) :
    SemanticCertificate :=
  SemanticCertificate.controlled bridge.kind bridge.subject bridge.body

def ControlledImplicationBridge.certificate
    (bridge : ControlledImplicationBridge) : SemanticCertificate :=
  SemanticCertificate.controlled bridge.kind bridge.subject bridge.body

def ControlledOperatorBridge.certificate
    (bridge : ControlledOperatorBridge) : SemanticCertificate :=
  SemanticCertificate.controlled bridge.kind bridge.subject bridge.body

def normalizedClassical (s : String) : String :=
  String.ofList <| s.toList.map fun
    | '復' => '复'
    | '窮' => '穷'
    | c => c

def containsAnyChar (needles : List Char) (s : String) : Bool :=
  s.toList.any (fun c => needles.contains c)

def plainTopicAliasBody? (body : String) : Bool :=
  body != ""
    && !containsAnyChar
      ['之', '不', '非', '而', '若', '则', '則', '为', '為', '有',
       '可', '未', '乃', '故', '以', '在', '入', '离', '離']
      body

def controlledTopicBridges : List ControlledTopicBridge :=
  [ { sourceSubject := "道", sourceBody := "不移"
    , kind := .v4OperatorTopic, subject := "道", body := "不移" }
  , { sourceSubject := "错", sourceBody := "反其内容"
    , kind := .v4OperatorTopic, subject := "错", body := "反其内容" }
  , { sourceSubject := "综", sourceBody := "反其框架"
    , kind := .v4OperatorTopic, subject := "综", body := "反其框架" }
  , { sourceSubject := "错综", sourceBody := "双反而复成一轨"
    , kind := .v4OperatorTopic, subject := "错综", body := "双反而复成一轨" }
  , { sourceSubject := "道", sourceBody := "未发之同一"
    , kind := .v4OperatorTopic, subject := "道", body := "未发之同一" }
  , { sourceSubject := "可证", sourceBody := "证之"
    , kind := .wenBoundary, subject := "可证", body := "证之" }
  , { sourceSubject := "可算", sourceBody := "算之"
    , kind := .wenBoundary, subject := "可算", body := "算之" }
  , { sourceSubject := "可读而未证", sourceBody := "存其辞不冒其真"
    , kind := .wenBoundary, subject := "可读而未证", body := "存其辞不冒其真" }
  , { sourceSubject := "故明", sourceBody := "不以文欺证"
    , kind := .wenBoundary, subject := "故明", body := "不以文欺证" }
  , { sourceSubject := "此五", sourceBody := "今为结构试置"
    , kind := .wenBoundary, subject := "此五", body := "今为结构试置" }
  , { sourceSubject := "守中", sourceBody := "不以未完为无"
    , kind := .wenBoundary, subject := "守中", body := "不以未完为无" }
  , { sourceSubject := "中", sourceBody := "不坠一端"
    , kind := .wenBoundary, subject := "中", body := "不坠一端" }
  , { sourceSubject := "无为", sourceBody := "非不行"
    , kind := .wenBoundary, subject := "无为", body := "非不行" }
  , { sourceSubject := "文", sourceBody := "已发之可验"
    , kind := .wenBoundary, subject := "文", body := "已发之可验" }
  , { sourceSubject := "读", sourceBody := "同一入时之门"
    , kind := .wenBoundary, subject := "读", body := "同一入时之门" }
  , { sourceSubject := "德", sourceBody := "道在行中不失"
    , kind := .wenBoundary, subject := "德", body := "道在行中不失" }
  , { sourceSubject := "读", sourceBody := "若循文而显"
    , kind := .wenBoundary, subject := "读", body := "若循文而显" }
  , { sourceSubject := "数", sourceBody := "分位之尺"
    , kind := .nameValueLaw, subject := "数", body := "分位之尺" }
  , { sourceSubject := "反", sourceBody := "有轴"
    , kind := .v4DualityLaw, subject := "反", body := "有轴" }
  , { sourceSubject := "四", sourceBody := "非四物"
    , kind := .v4DualityLaw, subject := "四", body := "非四物" }
  , { sourceSubject := "知双反", sourceBody := "知守变之法"
    , kind := .v4DualityLaw, subject := "知双反", body := "知守变之法" }
  , { sourceSubject := "文", sourceBody := "道之显"
    , kind := .rootStructureLaw, subject := "文", body := "道之显" }
  , { sourceSubject := "字", sourceBody := "显之位"
    , kind := .rootStructureLaw, subject := "字", body := "显之位" }
  , { sourceSubject := "句", sourceBody := "位之行"
    , kind := .rootStructureLaw, subject := "句", body := "位之行" }
  , { sourceSubject := "章", sourceBody := "行之可复"
    , kind := .rootStructureLaw, subject := "章", body := "行之可复" } ]

def controlledTopicCertificate? (subject body : String) :
    Option SemanticCertificate :=
  let subject := normalizedClassical subject
  let body := normalizedClassical body
  (controlledTopicBridges.find? (fun bridge =>
    bridge.sourceSubject == subject && bridge.sourceBody == body)).map
      ControlledTopicBridge.certificate

def semanticTopicCertificate? (subject body : String) :
    Option SemanticCertificate :=
  if normalizedClassical subject = "生生不息"
      ∧ normalizedClassical body = "往复而不穷" then
    some SemanticCertificate.cyclicPersistence
  else
    controlledTopicCertificate? subject body

def topicAliasCertificate? (subject body : String) :
    Option SemanticCertificate :=
  if plainTopicAliasBody? body then
    some (SemanticCertificate.aliasIdentity subject body)
  else
    none

theorem cyclicPersistence_certificate_wellFormed :
    SemanticCertificate.cyclicPersistence.wellFormed = true := rfl

def trim (s : String) : String :=
  s.trimAscii.toString

def stripLineComment (line : String) : String :=
  String.ofList (line.toList.takeWhile (fun c => c != ';'))

def cleanLine (line : String) : String :=
  trim (stripLineComment line)

def nonemptyLines (source : String) : List String :=
  (source.splitOn "\n").map cleanLine |>.filter (fun line => line != "")

def nonemptyLocatedLines (source : String) : List (Nat × String) :=
  (source.splitOn "\n").zipIdx.map
      (fun pair => (pair.2 + 1, cleanLine pair.1))
    |>.filter (fun pair => pair.2 != "")

def spanForLine (lineNo : Nat) (line : String) : SourceSpan :=
  { line := lineNo
  , startColumn := 1
  , endColumn := line.toList.length + 1 }

def startsWithChars : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, h :: hs => n == h && startsWithChars ns hs

def findSublistIndexAux (needle : List Char) :
    List Char → Nat → Option Nat
  | [], idx => if needle = [] then some idx else none
  | haystack, idx =>
      if startsWithChars needle haystack then
        some idx
      else
        match haystack with
        | [] => none
        | _ :: rest => findSublistIndexAux needle rest (idx + 1)

def findSubstringColumn? (needle text : String) : Option Nat :=
  if needle = "" then
    none
  else
    match findSublistIndexAux needle.toList text.toList 0 with
    | some idx => some (idx + 1)
    | none => none

theorem find_substring_column_example :
    findSubstringColumn? "龘龘" "错之龘龘" = some 3 := by
  native_decide

def spanForSubstring (lineNo : Nat) (line focus : String) : SourceSpan :=
  match findSubstringColumn? focus line with
  | some start =>
      { line := lineNo
      , startColumn := start
      , endColumn := start + focus.toList.length }
  | none => spanForLine lineNo line

def charTokens (line : String) : List String :=
  line.toList.map (fun c => String.singleton c)

def splitOnCharAux (target : Char) :
    List Char → List Char → Option (String × String)
  | [], _ => none
  | c :: rest, acc =>
      if c = target then
        some (String.ofList acc.reverse, String.ofList rest)
      else
        splitOnCharAux target rest (c :: acc)

def splitOnChar (target : Char) (s : String) : Option (String × String) :=
  splitOnCharAux target s.toList []

def splitOnEitherChar (left right : Char) (s : String) : Option (String × String) :=
  match splitOnChar left s with
  | some pair => some pair
  | none => splitOnChar right s

def splitOnRuleCharAux :
    List Char → List Char → Option (String × String)
  | [], _ => none
  | c :: rest, acc =>
      if (c = '则' ∨ c = '則') ∧ acc.head? != some '规' then
        some (String.ofList acc.reverse, String.ofList rest)
      else
        splitOnRuleCharAux rest (c :: acc)

def splitOnRuleChar (s : String) : Option (String × String) :=
  splitOnRuleCharAux s.toList []

def splitOnAnyCharAux (targets : List Char) :
    List Char → List Char → Option (String × Char × String)
  | [], _ => none
  | c :: rest, acc =>
      if targets.contains c ∧ acc != [] then
        some (String.ofList acc.reverse, c, String.ofList rest)
      else
        splitOnAnyCharAux targets rest (c :: acc)

def splitOnAnyChar (targets : List Char) (s : String) :
    Option (String × Char × String) :=
  splitOnAnyCharAux targets s.toList []

def dropLeadingChar (target : Char) (s : String) : Option String :=
  match s.toList with
  | [] => none
  | c :: rest =>
      if c = target then some (String.ofList rest) else none

def stripTrailingChar (target : Char) (s : String) : Option String :=
  match s.toList.reverse with
  | [] => none
  | c :: rest =>
      if c = target then some (String.ofList rest.reverse) else none

def stripOptionalTrailingChar (target : Char) (s : String) : String :=
  match stripTrailingChar target s with
  | some stripped => stripped
  | none => s

def nonemptyPair? (left right : String) : Option (String × String) :=
  if left = "" ∨ right = "" then none else some (left, right)

def normalizeSchemaSurface (s : String) : String :=
  String.ofList <| s.toList.map fun
    | '為' => '为'
    | '則' => '则'
    | c => c

def splitOnToken? (token s : String) : Option (String × String) :=
  match s.splitOn token with
  | [left, right] => nonemptyPair? left right
  | _ => none

def stripSuffixToken? (token s : String) : Option String :=
  match s.splitOn token with
  | [left, ""] =>
      if left = "" then none else some left
  | _ => none

def containsToken (token s : String) : Bool :=
  1 < (s.splitOn token).length

def startsWithToken (token s : String) : Bool :=
  startsWithChars token.toList s.toList

def parseNotAsObjectClause? (surface : String) :
    Option (String × String × ClauseAST) := do
  let (principle, object) ← splitOnToken? "不为" surface
  some (principle, object, .notAsObject principle object)

def parseInstrumentalFormationClause? (surface : String) :
    Option (String × FormationOperator × String × ClauseAST) :=
  match splitOnToken? "以之成" surface with
  | some (subject, result) =>
      some
        (subject, .cheng, result,
          .instrumentalFormation subject (.anaphor "") .cheng result)
  | none =>
      match splitOnToken? "以之立" surface with
      | some (subject, result) =>
          some
            (subject, .li, result,
              .instrumentalFormation subject (.anaphor "") .li result)
      | none =>
          match splitOnToken? "以之" surface with
          | some (subject, predicate) =>
              some
                (subject, .predicate predicate, "",
                  .instrumentalFormation subject (.anaphor "")
                    (.predicate predicate) "")
          | none => none

def parseBoundaryFormationInstantiation?
    (surface : String) : Option TextSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let (left, right) ← splitOnToken? "而" surface
  let (principle, object, leftClause) ← parseNotAsObjectClause? left
  let (subject, operator, result, _) ← parseInstrumentalFormationClause? right
  if subject == object then
    let rightClause :=
      ClauseAST.instrumentalFormation subject (.anaphor principle) operator result
    some
      { ruleId := "nonObjectInstrumentalFormation"
      , principle := principle
      , object := object
      , operator := operator
      , result := result
      , clause := .sequence leftClause rightClause }
  else
    none

def parsePassiveCapabilityInstantiation?
    (surface : String) : Option CapabilitySchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let (subject, rest) ← splitOnToken? "可被" surface
  let (action, result) ← splitOnToken? "故有" rest
  some
    { ruleId := "passiveCapabilityResult"
    , subject := subject
    , action := action
    , result := result
    , clause := .passiveAvailable subject action result }

def parseActiveCapabilityInstantiation?
    (surface : String) : Option CapabilitySchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let (subject, rest) ← splitOnToken? "能" surface
  let (action, result) ← splitOnToken? "乃" rest
  some
    { ruleId := "activeCapabilityResult"
    , subject := subject
    , action := action
    , result := result
    , clause := .activeCan subject action result }

def parseCapabilitySchemaInstantiation?
    (surface : String) : Option CapabilitySchemaInstantiation :=
  match parsePassiveCapabilityInstantiation? surface with
  | some inst => some inst
  | none => parseActiveCapabilityInstantiation? surface

def controlledStructuralSubject? (surface : String) : Bool :=
  [ "道", "理", "文", "字", "句", "章", "读", "德", "证", "数", "名", "实"
  , "指", "位", "组合", "卦", "时", "形", "六位", "四时", "八位", "每格"
  , "三重四位", "一字", "中", "知", "编", "程序", "证明", "反", "一事"
  , "同一", "意义", "零与后继", "一至六十四", "后文" ].contains surface

def controlledRoleObject? (surface : String) : Bool :=
  [ "形", "读", "同一", "同一之可用" ].contains surface

def parseContextRoleInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let (item, rest) ← splitOnToken? "在" surface
  let (context, role) ← splitOnToken? "中为" rest
  if controlledStructuralSubject? item then
    some
      { ruleId := "contextRole"
      , subject := item
      , relation := s!"在{context}中为"
      , object := role
      , clause := .contextRole item context role }
  else
    none

def parseRoleAssignmentInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  if containsToken "不为" surface || containsToken "而" surface then
    none
  else
    let (subject, role) ← splitOnToken? "为" surface
    if controlledStructuralSubject? subject && controlledRoleObject? role then
      some
        { ruleId := "roleAssignment"
        , subject := subject
        , relation := "为"
        , object := role
        , clause := .roleAssignment subject role }
    else
      none

def parseConstructionInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let (source, result) ← splitOnToken? "成" surface
  if controlledStructuralSubject? source then
    some
      { ruleId := "construction"
      , subject := source
      , relation := "成"
      , object := result
      , clause := .construction source result }
  else
    none

def parseEachHasInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let rest ← match surface.toList with
    | '每' :: tail => some (String.ofList tail)
    | _ => none
  let (domain, field) ← splitOnToken? "有其" rest
  let subject := "每" ++ domain
  some
    { ruleId := "eachHas"
    , subject := subject
    , relation := "有其"
    , object := field
    , clause := .eachHas domain field }

def parseLocationInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  if containsToken "中为" surface then
    none
  else
    let (subject, place) ← splitOnToken? "在" surface
    if controlledStructuralSubject? subject then
      some
        { ruleId := "location"
        , subject := subject
        , relation := "在"
        , object := place
        , clause := .location subject place }
    else
      none

def parsePossessionInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let (subject, object) ← splitOnToken? "有所" surface
  if controlledStructuralSubject? subject then
    some
      { ruleId := "possession"
      , subject := subject
      , relation := "有所"
      , object := object
      , clause := .possession subject object }
  else
    none

def parseNegatedPredicateInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  if containsToken "不为" surface || containsToken "而" surface then
    none
  else
    let (subject, predicate) ← splitOnToken? "不" surface
    if subject == "文" && (startsWithToken "离" predicate || startsWithToken "離" predicate) then
      none
    else if controlledStructuralSubject? subject then
      some
        { ruleId := "negatedPredicate"
        , subject := subject
        , relation := "不"
        , object := predicate
        , clause := .negatedPredicate subject predicate }
    else
      none

def parsePossibilityInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let parsed ←
    match splitOnToken? "可以" surface with
    | some pair => some ("可以", pair)
    | none =>
        match splitOnToken? "可" surface with
        | some pair => some ("可", pair)
        | none => none
  let relation := parsed.1
  let subject := parsed.2.1
  let predicate := parsed.2.2
  if controlledStructuralSubject? subject then
    some
      { ruleId := "possibility"
      , subject := subject
      , relation := relation
      , object := predicate
      , clause := .possibility subject predicate }
  else
    none

def parseStructuralSchemaInstantiation?
    (surface : String) : Option StructuralSchemaInstantiation :=
  match parseContextRoleInstantiation? surface with
  | some inst => some inst
  | none =>
      match parseRoleAssignmentInstantiation? surface with
      | some inst => some inst
      | none =>
          match parseConstructionInstantiation? surface with
          | some inst => some inst
          | none =>
              match parseEachHasInstantiation? surface with
              | some inst => some inst
              | none =>
                  match parseLocationInstantiation? surface with
                  | some inst => some inst
                  | none =>
                      match parsePossessionInstantiation? surface with
                      | some inst => some inst
                      | none =>
                          match parseNegatedPredicateInstantiation? surface with
                          | some inst => some inst
                          | none => parsePossibilityInstantiation? surface

def stripLeadingToken? (token surface : String) : String :=
  if startsWithToken token surface then
    String.ofList (surface.toList.drop token.toList.length)
  else
    surface

def parseFourfoldReadingInstantiation?
    (surface : String) : Option DualitySchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let surface := stripLeadingToken? "乃" surface
  let subject ← stripSuffixToken? "之四读" surface
  some
    { ruleId := "fourfoldReading"
    , subject := subject
    , reading := "四读"
    , clause := .fourfoldReading subject }

def parseContentFrameCompositeInstantiation?
    (surface : String) : Option DualitySchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let subject ← stripSuffixToken? "内容框架复合" surface
  some
    { ruleId := "contentFrameComposite"
    , subject := subject
    , reading := "内容框架复合"
    , clause := .contentFrameComposite subject }

def parseConsequenceBoneInstantiation?
    (surface : String) : Option DualitySchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let subject ← stripSuffixToken? "由此有骨" surface
  some
    { ruleId := "consequenceBone"
    , subject := subject
    , reading := "由此有骨"
    , clause := .consequenceBone subject }

def parseReversalReturnInstantiation?
    (surface : String) : Option DualitySchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let (subject, object) ← splitOnToken? "复" surface
  if subject == "反" then
    some
      { ruleId := "reversalReturn"
      , subject := subject
      , reading := s!"复{object}"
      , clause := .reversalReturn subject object }
  else
    none

def parseDualitySchemaInstantiation?
    (surface : String) : Option DualitySchemaInstantiation :=
  match parseFourfoldReadingInstantiation? surface with
  | some inst => some inst
  | none =>
      match parseContentFrameCompositeInstantiation? surface with
      | some inst => some inst
      | none =>
          match parseConsequenceBoneInstantiation? surface with
          | some inst => some inst
          | none => parseReversalReturnInstantiation? surface

def parseAbsenceDegradationInstantiation?
    (condition conclusion : String) : Option DiscourseSchemaInstantiation := do
  let condition := normalizeSchemaSurface condition
  let conclusion := normalizeSchemaSurface conclusion
  let missing ← match condition.toList with
    | '无' :: tail => some (String.ofList tail)
    | _ => none
  let (subject, value) ← splitOnToken? "但为" conclusion
  some
    { ruleId := "absenceDegradation"
    , subject := subject
    , relation := s!"无{missing}则但为"
    , object := value
    , clause := .absenceDegrades missing subject "" value }

def parseSelfRuleInstantiation?
    (surface : String) : Option DiscourseSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let (subject, rest) ← splitOnToken? "若自其" surface
  let (source, result) ← splitOnToken? "而" rest
  if controlledStructuralSubject? subject then
    some
      { ruleId := "selfRule"
      , subject := subject
      , relation := s!"若自其{source}而"
      , object := result
      , clause := .selfRule subject source result }
  else
    none

def parseCausativeInstantiation?
    (surface : String) : Option DiscourseSchemaInstantiation := do
  let surface := normalizeSchemaSurface surface
  let rest ← match surface.toList with
    | '使' :: tail => some (String.ofList tail)
    | _ => none
  let (actor, result) ←
    match splitOnToken? "承" rest with
    | some pair => some pair
    | none =>
        match splitOnToken? "渐" rest with
        | some pair => some pair
        | none => none
  if controlledStructuralSubject? actor then
    some
      { ruleId := "causative"
      , subject := actor
      , relation := "使"
      , object := result
      , clause := .causative actor result }
  else
    none

def parseDiscourseOperatorSchemaInstantiation?
    (surface : String) : Option DiscourseSchemaInstantiation :=
  match parseSelfRuleInstantiation? surface with
  | some inst => some inst
  | none => parseCausativeInstantiation? surface

def parseNameZhe (token : String) : Option String :=
  match token.toList.reverse with
  | '者' :: rest =>
      let name := String.ofList rest.reverse
      if name = "" then none else some name
  | _ => none

def parseR5Compact (token : String) : Option R5Word :=
  match token.toList with
  | [benChar, zhengChar, extChar] => do
      let ben ← BenWord.ofChar benChar
      let zheng ← ZhengWord.ofChar zhengChar
      let ext ← ExtensionBit.ofChar extChar
      some ⟨⟨ben, zheng⟩, ext⟩
  | _ => none

def parseR5Split (benToken zhengToken extToken : String) : Option R5Word :=
  match benToken.toList, zhengToken.toList, extToken.toList with
  | [benChar], [zhengChar], [extChar] => do
      let ben ← BenWord.ofChar benChar
      let zheng ← ZhengWord.ofChar zhengChar
      let ext ← ExtensionBit.ofChar extChar
      some ⟨⟨ben, zheng⟩, ext⟩
  | _, _, _ => none

def parseZheBody (line : String) : Option (String × String) := do
  let (subject, rawBody) ← splitOnChar '者' line
  let body := stripOptionalTrailingChar '也' rawBody
  nonemptyPair? subject body

def parseR5ZheBody (line : String) : Option (String × R5Word) := do
  let (name, body) ← parseZheBody line
  let value ← parseR5Compact body
  some (name, value)

def parseImplication (line : String) : Option (String × String) := do
  let rest ← dropLeadingChar '若' line
  let (condition, conclusion) ← splitOnRuleChar rest
  nonemptyPair? condition conclusion

def parseRule (line : String) : Option (String × String) := do
  let (condition, conclusion) ← splitOnRuleChar line
  nonemptyPair? condition conclusion

def parseUniversal (line : String) : Option (String × String) := do
  let rest ← dropLeadingChar '凡' line
  let (domain, predicate) ← splitOnChar '皆' rest
  nonemptyPair? domain predicate

def parsePredication (line : String) : Option (String × String) := do
  let (subject, predicate) ← splitOnEitherChar '为' '為' line
  nonemptyPair? subject predicate

def parseVerificationTarget (target : String) : Option String :=
  match target.toList with
  | '为' :: rest | '為' :: rest =>
      let predicate := String.ofList rest
      if predicate = "" then none else some predicate
  | _ => none

def isDaoVerificationTarget (target : String) : Bool :=
  target = "为道" ∨ target = "為道" ∨
    target = "属道" ∨ target = "屬道" ∨
    target = "属于道" ∨ target = "屬於道"

def parseAssertion (line : String) : Option String := do
  let body ← stripTrailingChar '也' line
  if body = "" then none else some body

def operatorModeOfGroup : OperatorGroup → OperatorMode
  | .R | .I | .G => .relate
  | .T | .F | .B => .transform
  | .N => .negate
  | .M => .modal
  | .K => .causation
  | .Q => .quantifier
  | .S => .discourse
  | .C | .H | .P | .A | .D | .E | .L | .Y | .X | .Z
  | .ZHU | .SUN | .CHU | .LIJ | .ZA => .textLayer

def v4Operator? : String → Option V4
  | "道" => some .dao
  | "错" => some .cuo
  | "錯" => some .cuo
  | "综" => some .zong
  | "綜" => some .zong
  | "错综" => some .cuoZong
  | "錯綜" => some .cuoZong
  | _ => none

def textLayerOperator? (surface : String) : Option OperatorToken :=
  match allOperatorIds.find? (fun id =>
      (operatorForms id).any (fun sense => sense.glyph = surface)) with
  | some id =>
      some
        { surface := surface
        , carrier := .textLayer id.code id.title (operatorModeOfGroup id.group) }
  | none =>
      if surface = "无" ∨ surface = "無" then
        some { surface := surface, carrier := .textLayer "Q-local" "absence" .quantifier }
      else if surface = "为" ∨ surface = "為" ∨ surface = "是" ∨ surface = "同" then
        some { surface := surface, carrier := .textLayer "R-local" "copula" .relate }
      else if surface = "见" ∨ surface = "見" then
        some { surface := surface, carrier := .textLayer "P-local" "manifest" .textLayer }
      else if surface = "开" ∨ surface = "開" then
        some { surface := surface, carrier := .textLayer "T-local" "open" .transform }
      else
        none

def operatorToken? (surface : String) : Option OperatorToken :=
  match v4Operator? surface with
  | some value => some { surface := surface, carrier := .v4Builtin value }
  | none =>
      if surface = "之" then
        some { surface := surface, carrier := .applicationParticle }
      else
        match Root512.operatorAlias? surface with
        | some reading => some { surface := surface, carrier := .root512 reading }
        | none => textLayerOperator? surface

def operatorApp (op : OperatorToken) (args : List String) (form : OperatorForm) :
    OperatorApplication :=
  { op := op, args := args, form := form }

def parseApplicationParticle (opSurface arg : String) :
    Option OperatorApplication := do
  let op ← operatorToken? opSurface
  if arg = "" then none else some (operatorApp op [arg] .applicationParticle)

def parseCompactApplication (line : String) : Option OperatorApplication := do
  let (opSurface, arg) ← splitOnChar '之' line
  parseApplicationParticle opSurface arg

def isSkippedRuleChar (previous? : Option Char) (c : Char) : Bool :=
  decide (c = '则' ∨ c = '則') &&
    match previous? with
    | some '规' | some '規' | some '原' | some '法' | some '常' => true
    | _ => false

def findInfixOperatorAux :
    List Char → List Char → Option (String × OperatorToken × String)
  | [], _ => none
  | c :: rest, acc =>
      let previous? := acc.head?
      let surface := String.singleton c
      if acc != [] && !isSkippedRuleChar previous? c then
        match operatorToken? surface with
        | some op =>
            match op.carrier with
            | .applicationParticle => findInfixOperatorAux rest (c :: acc)
            | _ =>
                let right := String.ofList rest
                if right = "" then findInfixOperatorAux rest (c :: acc)
                else some (String.ofList acc.reverse, op, right)
        | none => findInfixOperatorAux rest (c :: acc)
      else
        findInfixOperatorAux rest (c :: acc)

def parseInfixOperatorApp (line : String) : Option OperatorApplication := do
  let (left, op, right) ← findInfixOperatorAux line.toList []
  let _ ← nonemptyPair? left right
  some (operatorApp op [left, right] .infix)

def parsePrefixOperatorApp (line : String) : Option OperatorApplication :=
  match line.toList with
  | [] => none
  | c :: rest =>
      let surface := String.singleton c
      match operatorToken? surface with
      | some op =>
          match op.carrier with
          | .applicationParticle => none
          | _ =>
              let body := String.ofList rest
              if body = "" then none else some (operatorApp op [body] .prefix)
      | none => none

def parseOperatorApp (line : String) : Option OperatorApplication :=
  match parseCompactApplication line with
  | some app => some app
  | none =>
      match parsePrefixOperatorApp line with
      | some app => some app
      | none => parseInfixOperatorApp line

def parseOneTokenSyntax (head : String) : Sentence :=
  if head = "读之则验" ∨ head = "讀之則驗" then
    .readThenVerify
  else
    match parseNameZhe head with
    | some name => .enumHead name
    | none =>
        match splitOnChar '即' head with
        | some (left, right) =>
            match nonemptyPair? left right with
            | some (left, right) => .alias left right
            | none => .claimStub head (charTokens head)
        | none =>
            match parseImplication head with
            | some (condition, conclusion) => .implication condition conclusion
            | none =>
                match parseUniversal head with
                | some (domain, predicate) => .universal domain predicate
                | none =>
                    match parseRule head with
                    | some (condition, conclusion) => .implication condition conclusion
                    | none =>
                        match parseR5ZheBody head with
                        | some (name, value) => .defineR5 name value
                        | none =>
                            match parseZheBody head with
                            | some (subject, body) => .topicComment subject body
                            | none =>
                                match parsePredication head with
                                | some (subject, predicate) =>
                                    match operatorToken? "为" with
                                    | some op => .operatorApp (operatorApp op [subject, predicate] .infix)
                                    | none => .claimStub head (charTokens head)
                                | none =>
                                    match parseAssertion head with
                                    | some body => .assertion body
                                    | none =>
                                        match parseOperatorApp head with
                                        | some app => .operatorApp app
                                        | none => .barePhrase head (charTokens head)

def parseSentence (line : String) : Sentence :=
  let words := line.splitOn " " |>.filter (fun token => token != "")
  match words with
  | [nameToken, coord, "也"] =>
      match parseNameZhe nameToken, parseR5Compact coord with
      | some name, some r5 => .defineR5 name r5
      | _, _ => .claimStub line (charTokens line)
  | [nameToken, ben, zheng, ext, "也"] =>
      match parseNameZhe nameToken, parseR5Split ben zheng ext with
      | some name, some r5 => .defineR5 name r5
      | _, _ => .claimStub line (charTokens line)
  | ["验", name, "为五爻"] => .verifyR5 name
  | ["驗", name, "為五爻"] => .verifyR5 name
  | ["验", name, "属于", "道"] => .verifyKernelDao name
  | ["驗", name, "屬於", "道"] => .verifyKernelDao name
  | ["验", name, target] =>
      if isDaoVerificationTarget target then .verifyKernelDao name
      else
        match parseVerificationTarget target with
        | some predicate => .instantiateUniversal name predicate
        | none => .claimStub line (charTokens line)
  | ["驗", name, target] =>
      if isDaoVerificationTarget target then .verifyKernelDao name
      else
        match parseVerificationTarget target with
        | some predicate => .instantiateUniversal name predicate
        | none => .claimStub line (charTokens line)
  | ["验", name, "为", "道"] => .verifyKernelDao name
  | ["驗", name, "為", "道"] => .verifyKernelDao name
  | ["验", name, "为", predicate] => .instantiateUniversal name predicate
  | ["驗", name, "為", predicate] => .instantiateUniversal name predicate
  | [opSurface, "之", arg] =>
      match parseApplicationParticle opSurface arg with
      | some app => .operatorApp app
      | none => .claimStub line (charTokens line)
  | [head] => parseOneTokenSyntax head
  | _ => .claimStub line (charTokens line)

inductive ParseError where
  | missingZeroStart
  | emptyDocument
  deriving Repr, DecidableEq

def parseDocument (source : String) : Except ParseError Document :=
  match nonemptyLocatedLines source with
  | [] => .error .emptyDocument
  | first :: rest =>
      if first.2 = "零起" then
        let located := rest.map fun pair =>
          { line := pair.1
          , column := 1
          , span := spanForLine pair.1 pair.2
          , text := pair.2
          , sentence := parseSentence pair.2 }
        .ok ⟨located.map (fun item => item.sentence), located⟩
      else
        .error .missingZeroStart

/-! ## Prover/evaluator -/

def lookupDef : List (String × R5Word) → String → Option R5Word
  | [], _ => none
  | (name, value) :: rest, target =>
      if name = target then some value else lookupDef rest target

def addVerified (name : String) (value : R5Word) (report : ProofReport) :
    ProofReport :=
  { report with
    certificates := R5Certificate.ofDefinition name value :: report.certificates }

mutual

def applicationArgumentWordFuel? : Nat → String → Option Word64
  | 0, surface => SSBX.Foundation.Wen.Layered.Bridges.Word64.wordOfToken surface
  | fuel + 1, surface =>
      match SSBX.Foundation.Wen.Layered.Bridges.Word64.wordOfToken surface with
      | some word => some word
      | none => do
          let app ← parseOperatorApp surface
          executableApplicationResultWordFuel? fuel app

def executableApplicationResultWordFuel? :
    Nat → OperatorApplication → Option Word64
  | 0, app =>
      match app.op.carrier, app.form, app.args with
      | .v4Builtin g, .applicationParticle, [argSurface] => do
          let arg ← SSBX.Foundation.Wen.Layered.Bridges.Word64.wordOfToken argSurface
          some (R6View.dual g arg)
      | .root512 opReading, .applicationParticle, [argSurface] => do
          let argWord ← SSBX.Foundation.Wen.Layered.Bridges.Word64.wordOfToken argSurface
          let argReading := Root512.word64Reading argWord .cell
          let result ← Root512.applyOperatorReading? opReading argReading
          match result.kind, result.cell.temporal with
          | .cell, .dao => some result.cell.word
          | _, _ => none
      | _, _, _ => none
  | fuel + 1, app =>
      match app.op.carrier, app.form, app.args with
      | .v4Builtin g, .applicationParticle, [argSurface] => do
          let arg ← applicationArgumentWordFuel? fuel argSurface
          some (R6View.dual g arg)
      | .root512 opReading, .applicationParticle, [argSurface] => do
          let argWord ← applicationArgumentWordFuel? fuel argSurface
          let argReading := Root512.word64Reading argWord .cell
          let result ← Root512.applyOperatorReading? opReading argReading
          match result.kind, result.cell.temporal with
          | .cell, .dao => some result.cell.word
          | _, _ => none
      | _, _, _ => none

end

def v4ActionTraceFuel? (fuel : Nat) (app : OperatorApplication) :
    Option V4ActionTrace := do
  match app.op.carrier, app.form, app.args with
  | .v4Builtin g, .applicationParticle, [argSurface] =>
      let arg ← applicationArgumentWordFuel? fuel argSurface
      some
        { operatorSurface := app.op.surface
        , operator := g
        , argumentSurface := argSurface
        , argument := arg
        , result := R6View.dual g arg }
  | _, _, _ => none

def v4ActionTrace? (app : OperatorApplication) : Option V4ActionTrace :=
  v4ActionTraceFuel? 8 app

def rootApplicationTraceFuel? (fuel : Nat) (app : OperatorApplication) :
    Option Root512.ApplicationTrace := do
  match app.op.carrier, app.form, app.args with
  | .root512 opReading, .applicationParticle, [argSurface] =>
      let argWord ← applicationArgumentWordFuel? fuel argSurface
      let argReading := Root512.word64Reading argWord .cell
      let result ← Root512.applyOperatorReading? opReading argReading
      some
        { operatorSurface := app.op.surface
        , operator := opReading
        , argumentSurface := argSurface
        , argument := argReading
        , result := result }
  | _, _, _ => none

def rootApplicationTrace? (app : OperatorApplication) :
    Option Root512.ApplicationTrace :=
  rootApplicationTraceFuel? 8 app

def rootApplicationResultWord? (app : OperatorApplication) : Option Word64 := do
  let trace ← rootApplicationTrace? app
  match trace.result.kind, trace.result.cell.temporal with
  | .cell, .dao => some trace.result.cell.word
  | _, _ => none

def executableApplicationResultWord? (app : OperatorApplication) :
    Option Word64 :=
  executableApplicationResultWordFuel? 8 app

def semanticImplicationCertificate? (condition conclusion : String) :
    Option SemanticCertificate := do
  let app ← parseOperatorApp condition
  let result ← executableApplicationResultWord? app
  let expected ← SSBX.Foundation.Wen.Layered.Bridges.Word64.wordOfToken conclusion
  if result == expected then
    some
      { subject := condition
      , body := conclusion
      , kind := .rootActionImplication
      , wellFormed := true }
  else
    none

def discourseImplicationSchemaCertificate? (condition conclusion : String) :
    Option SemanticCertificate := do
  let inst ← parseAbsenceDegradationInstantiation? condition conclusion
  some (SemanticCertificate.discourseSchemaInstantiation inst)

def controlledImplicationBridges : List ControlledImplicationBridge :=
  [ { condition := "读之", conclusion := "显"
    , kind := .wenBoundary, subject := "读之", body := "显" }
  , { condition := "二反相继", conclusion := "所伤复合而形可守"
    , kind := .v4DualityLaw, subject := "二反相继", body := "所伤复合而形可守" }
  , { condition := "无数", conclusion := "次第不明"
    , kind := .rootStructureLaw, subject := "无数", body := "次第不明" }
  , { condition := "执数", conclusion := "义理成器"
    , kind := .wenBoundary, subject := "执数", body := "义理成器" } ]

def controlledImplicationCertificate? (condition conclusion : String) :
    Option SemanticCertificate :=
  (controlledImplicationBridges.find? (fun bridge =>
    bridge.condition == condition && bridge.conclusion == conclusion)).map
      ControlledImplicationBridge.certificate

def nameResolutionImplicationCertificate? (condition conclusion : String) :
    Option SemanticCertificate :=
  if (condition = "名不入环境" && conclusion = "名为symbol")
      || (condition = "名入环境" && conclusion = "名为reference")
      || (condition = "名被束" && conclusion = "名为local")
      || (condition = "名被定义" && conclusion = "名为global") then
    some (SemanticCertificate.nameResolutionRule condition conclusion)
  else
    none

theorem action_implication_cuo_qian :
    (semanticImplicationCertificate? "错之乾" "坤").isSome = true := by
  native_decide

theorem action_implication_bu_qian :
    (semanticImplicationCertificate? "不之乾" "坤").isSome = true := by
  native_decide

theorem nested_v4_application_example :
    (parseOperatorApp "错之综之乾" >>= executableApplicationResultWord?).isSome = true := by
  native_decide

def stripLeadingDepart (text : String) : Option String :=
  match text.toList with
  | '离' :: rest | '離' :: rest =>
      let target := String.ofList rest
      if target = "" then none else some target
  | _ => none

def aliasNeighbors (aliases : List (String × String)) (target : String) :
    List String :=
  aliases.foldr
    (fun entry acc =>
      if entry.1 == target then
        entry.2 :: acc
      else if entry.2 == target then
        entry.1 :: acc
      else
        acc)
    []

def aliasesConnectedFuel (aliases : List (String × String)) :
    Nat → String → String → Bool
  | 0, left, right => left == right
  | fuel + 1, left, right =>
      left == right
        || (aliasNeighbors aliases left).any
          (fun next => aliasesConnectedFuel aliases fuel next right)

def aliasesConnected (aliases : List (String × String)) (left right : String) :
    Bool :=
  aliasesConnectedFuel aliases (aliases.length + 1) left right

def aliasInseparabilityCertificate? (aliases : List (String × String))
    (app : OperatorApplication) : Option SemanticCertificate := do
  match app.op.carrier, app.form, app.args with
  | .root512 _, .infix, [left, rightRaw] =>
      if app.op.surface = "不" ∨ app.op.surface = "非" then
        let right ← stripLeadingDepart rightRaw
        if aliasesConnected aliases left right then
          some (SemanticCertificate.aliasInseparability left right)
        else
          none
      else
        none
  | _, _, _ => none

def copulaAliasCertificate? (aliases : List (String × String))
    (app : OperatorApplication) : Option SemanticCertificate := do
  match app.op.carrier, app.form, app.args with
  | .textLayer _ _ _, .infix, [left, right] =>
      if app.op.surface = "为" ∨ app.op.surface = "為"
          ∨ app.op.surface = "是" ∨ app.op.surface = "同" then
        if left == right || aliasesConnected aliases left right then
          some (SemanticCertificate.copulaAlias left right)
        else
          none
      else
        none
  | _, _, _ => none

def reportHasCertificate (report : ProofReport) : Bool :=
  report.semanticEvidenceCount > 0 || report.certificates.length > 0

def reportHasEvidence (report : ProofReport) : Bool :=
  reportHasCertificate report
    || report.v4Actions.length > 0
    || report.rootApplications.length > 0

def reportHasCalculationSurface (report : ProofReport) : Bool :=
  report.v4Actions.length > 0
    || report.rootApplications.length > 0
    || report.operatorApps.length > 0
    || report.certificates.length > 0
    || report.definitions.length > 0

def reportOpenCalculationCount (report : ProofReport) : Nat :=
  report.frontierSummary.unsupportedTextLayerOperators
    + report.frontierSummary.unsupportedApplicationGrammars
    + report.frontierSummary.unknownActionArguments
    + report.semanticKindCount .operatorRegistration

def reportHasNames (report : ProofReport) : Bool :=
  report.aliases.length > 0 || report.definitions.length > 0

def reportPendingNameCount (report : ProofReport) : Nat :=
  report.frontierSummary.openCount
    + report.claimStubs.length
    + report.barePhrases.length
    + report.semanticRegistrationCount

def certificateAvailabilityCertificate? (report : ProofReport)
    (app : OperatorApplication) : Option SemanticCertificate :=
  match app.op.carrier, app.form, app.args with
  | .textLayer _ _ .quantifier, .prefix, ["可证"] =>
      if app.op.surface = "有" && reportHasCertificate report then
        some SemanticCertificate.certificateAvailability
      else
        none
  | _, _, _ => none

def calculationAvailabilityCertificate? (report : ProofReport)
    (app : OperatorApplication) : Option SemanticCertificate :=
  match app.op.carrier, app.form, app.args with
  | .textLayer _ _ .quantifier, .prefix, ["可算"] =>
      if app.op.surface = "有" && reportHasCalculationSurface report then
        some SemanticCertificate.calculationAvailability
      else
        none
  | .textLayer _ _ .quantifier, .prefix, ["未算"] =>
      let openCount := reportOpenCalculationCount report
      if app.op.surface = "有" && openCount > 0 then
        some (SemanticCertificate.openCalculationAvailability openCount)
      else if app.op.surface = "有" then
        some (SemanticCertificate.wenBoundary "有" "未算")
      else
        none
  | _, _, _ => none

def nameAvailabilityCertificate? (report : ProofReport)
    (app : OperatorApplication) : Option SemanticCertificate :=
  match app.op.carrier, app.form, app.args with
  | .textLayer _ _ .quantifier, .prefix, ["已名"] =>
      if app.op.surface = "有" && reportHasNames report then
        some SemanticCertificate.nameAvailability
      else
        none
  | .textLayer _ _ .quantifier, .prefix, ["待名"] =>
      let openCount := reportPendingNameCount report
      if app.op.surface = "有" && openCount > 0 then
        some (SemanticCertificate.pendingNameAvailability openCount)
      else if app.op.surface = "有" then
        some (SemanticCertificate.wenBoundary "有" "待名")
      else
        none
  | _, _, _ => none

def knownWenCapabilityBody? : String → Bool
  | "被读故有解释" => true
  | "被算故有执行" => true
  | "被证故有边界" => true
  | "生文乃编" => true
  | "读文乃释" => true
  | "证文乃信" => true
  | "改文而留其证乃德" => true
  | _ => false

def wenCapabilityCertificate? (aliases : List (String × String))
    (app : OperatorApplication) : Option SemanticCertificate :=
  match app.op.carrier, app.form, app.args with
  | .textLayer _ _ .modal, .infix, [subject, body] =>
      if (app.op.surface = "可" || app.op.surface = "能")
          && (subject == "文" || aliasesConnected aliases subject "文")
          && knownWenCapabilityBody? body then
        some (SemanticCertificate.wenCapability subject body)
      else
        none
  | _, _, _ => none

def opBridge (surface : String) (form : OperatorForm) (args : List String)
    (kind : SemanticCertificateKind) (subject body : String) :
    ControlledOperatorBridge :=
  { surface := surface, form := form, args := args, kind := kind
  , subject := subject, body := body }

def controlledOperatorBridges : List ControlledOperatorBridge :=
  [ opBridge "道" .prefix ["在核"] .v4OperatorTopic "道" "在核"
  , opBridge "错" .prefix ["反其值"] .v4OperatorTopic "错" "反其值"
  , opBridge "综" .prefix ["反其向"] .v4OperatorTopic "综" "反其向"
  , opBridge "错综" .prefix ["双反而复成一轨"] .v4OperatorTopic "错综" "双反而复成一轨"
  , opBridge "未" .prefix ["有字已有可显之理"] .wenBoundary "未有字" "已有可显之理"
  , opBridge "未" .prefix ["有名已有可分之迹"] .wenBoundary "未有名" "已有可分之迹"
  , opBridge "不" .prefix ["读亦在"] .wenBoundary "不读" "亦在"
  , opBridge "一" .prefix ["非孤立乃万化之同源"] .wenBoundary "一" "非孤立乃万化之同源"
  , opBridge "一" .prefix ["非静死乃诸动之不失其本"] .wenBoundary "一" "非静死乃诸动之不失其本"
  , opBridge "非" .infix ["字", "徒声"] .wenBoundary "字" "非徒声"
  , opBridge "不" .prefix ["以证灭文"] .wenBoundary "不" "以证灭文"
  , opBridge "不" .prefix ["以外力乱其内法"] .wenBoundary "不" "以外力乱其内法"
  , opBridge "不" .prefix ["以初成称尽"] .wenBoundary "不" "以初成称尽"
  , opBridge "非" .infix ["编", "拼凑"] .wenBoundary "编" "非拼凑"
  , opBridge "非" .prefix ["神秘乃不增伪因"] .wenBoundary "非神秘" "不增伪因"
  , opBridge "故" .prefix ["行不违其性"] .wenBoundary "故" "行不违其性"
  , opBridge "为" .infix ["皆无", "也"] .wenBoundary "皆" "无为"
  , opBridge "有" .prefix ["未证"] .wenBoundary "有" "未证"
  , opBridge "中" .prefix ["非折半"] .wenBoundary "中" "非折半"
  , opBridge "为" .infix ["可验其", "五爻"] .wenBoundary "可验" "五爻"
  , opBridge "为" .infix ["未定其", "万世训诂"] .wenBoundary "未定" "万世训诂"
  , opBridge "名" .prefix ["能指"] .nameValueLaw "名" "能指"
  , opBridge "实" .prefix ["能验"] .nameValueLaw "实" "能验"
  , opBridge "名" .prefix ["实相入"] .nameValueLaw "名" "实相入"
  , opBridge "乃" .infix ["文", "可行"] .nameValueLaw "文" "可行"
  , opBridge "是" .prefix ["谓德"] .nameValueLaw "是" "谓德"
  , opBridge "六" .prefix ["与二合成八位"] .rootStructureLaw "六与二" "合成八位"
  , opBridge "二" .prefix ["百五十六格可分"] .rootStructureLaw "二百五十六格" "可分"
  , opBridge "使" .infix ["数", "文可步进"] .rootStructureLaw "数" "使文可步进"
  , opBridge "能" .prefix ["变而不散"] .wenCapability "能" "变而不散"
  , opBridge "能" .prefix ["应而不伪"] .wenCapability "能" "应而不伪"
  , opBridge "能" .prefix ["入众流而不失其核"] .wenCapability "能" "入众流而不失其核"
  , opBridge "运" .prefix ["行其文"] .wenCapability "运" "行其文"
  , opBridge "见" .infix ["文", "其德"] .wenCapability "文" "见其德"
  , opBridge "明" .infix ["证", "其文"] .wenCapability "证" "明其文"
  , opBridge "知" .infix ["文", "其界"] .wenCapability "文" "知其界"
  , opBridge "再" .prefix ["生其文"] .wenCapability "再" "生其文"
  , opBridge "开" .infix ["文", "其后"] .wenCapability "文" "开其后"
  , opBridge "生" .prefix ["生不息"] .wenCapability "生" "生不息" ]

def controlledOperatorCertificate? (app : OperatorApplication) :
    Option SemanticCertificate :=
  (controlledOperatorBridges.find? (fun bridge =>
    bridge.surface == app.op.surface
      && bridge.form == app.form
      && bridge.args == app.args)).map ControlledOperatorBridge.certificate

def textSchemaOperatorCertificate? (app : OperatorApplication) :
    Option SemanticCertificate := do
  let inst ← parseBoundaryFormationInstantiation? app.surfaceLine
  some (SemanticCertificate.textSchemaInstantiation inst)

def capabilitySchemaOperatorCertificate? (aliases : List (String × String))
    (app : OperatorApplication) : Option SemanticCertificate := do
  let inst ← parseCapabilitySchemaInstantiation? app.surfaceLine
  if inst.subject == "文" || aliasesConnected aliases inst.subject "文" then
    some (SemanticCertificate.capabilitySchemaInstantiation inst)
  else
    none

def structuralSchemaOperatorCertificate? (app : OperatorApplication) :
    Option SemanticCertificate := do
  let inst ← parseStructuralSchemaInstantiation? app.surfaceLine
  some (SemanticCertificate.structuralSchemaInstantiation inst)

def dualitySchemaOperatorCertificate? (app : OperatorApplication) :
    Option SemanticCertificate := do
  let inst ← parseDualitySchemaInstantiation? app.surfaceLine
  some (SemanticCertificate.dualitySchemaInstantiation inst)

def discourseOperatorSchemaCertificate? (app : OperatorApplication) :
    Option SemanticCertificate := do
  let inst ← parseDiscourseOperatorSchemaInstantiation? app.surfaceLine
  some (SemanticCertificate.discourseSchemaInstantiation inst)

def openObligationCertificate? (report : ProofReport)
    (app : OperatorApplication) : Option SemanticCertificate :=
  match app.op.carrier, app.form, app.args with
  | .textLayer _ _ .quantifier, .prefix, ["未证"] =>
      let openCount := report.frontierSummary.openCount + report.claimStubs.length
      if app.op.surface = "有" && openCount > 0 then
        some (SemanticCertificate.openObligationAvailability openCount)
      else if (app.op.surface = "无" ∨ app.op.surface = "無") && openCount == 0 then
        some SemanticCertificate.frontierClean
      else
        none
  | _, _, _ => none

def operatorSemanticCertificate? (report : ProofReport)
    (app : OperatorApplication) : Option SemanticCertificate :=
  match textSchemaOperatorCertificate? app with
  | some cert => some cert
  | none =>
      match capabilitySchemaOperatorCertificate? report.aliases app with
      | some cert => some cert
      | none =>
          match aliasInseparabilityCertificate? report.aliases app with
          | some cert => some cert
          | none =>
              match copulaAliasCertificate? report.aliases app with
              | some cert => some cert
              | none =>
                  match dualitySchemaOperatorCertificate? app with
                  | some cert => some cert
                  | none =>
                      match discourseOperatorSchemaCertificate? app with
                      | some cert => some cert
                      | none =>
                          match structuralSchemaOperatorCertificate? app with
                          | some cert => some cert
                          | none =>
                              match controlledOperatorCertificate? app with
                              | some cert => some cert
                              | none =>
                                  match certificateAvailabilityCertificate? report app with
                                  | some cert => some cert
                                  | none =>
                                      match wenCapabilityCertificate? report.aliases app with
                                      | some cert => some cert
                                      | none =>
                                          match calculationAvailabilityCertificate? report app with
                                          | some cert => some cert
                                          | none =>
                                              match nameAvailabilityCertificate? report app with
                                              | some cert => some cert
                                              | none => openObligationCertificate? report app

def reportWithSemanticCertificate (report : ProofReport)
    (cert : SemanticCertificate) : ProofReport :=
  { report with semanticCertificates := cert :: report.semanticCertificates }

def stateImplicationCertificate? (report : ProofReport)
    (condition conclusion : String) : Option SemanticCertificate := do
  let conditionApp ← parseOperatorApp condition
  let conditionCert ← operatorSemanticCertificate? report conditionApp
  let conclusionApp ← parseOperatorApp conclusion
  let report' := reportWithSemanticCertificate report conditionCert
  let _ ← operatorSemanticCertificate? report' conclusionApp
  some (SemanticCertificate.stateImplication condition conclusion)

def implicationSemanticCertificate? (report : ProofReport)
    (condition conclusion : String) : Option SemanticCertificate :=
  match semanticImplicationCertificate? condition conclusion with
  | some cert => some cert
  | none =>
      match discourseImplicationSchemaCertificate? condition conclusion with
      | some cert => some cert
      | none =>
          match controlledImplicationCertificate? condition conclusion with
          | some cert => some cert
          | none =>
              match nameResolutionImplicationCertificate? condition conclusion with
              | some cert => some cert
              | none => stateImplicationCertificate? report condition conclusion

def universalInstantiationCertificate? (report : ProofReport)
    (name predicate : String) : Option SemanticCertificate :=
  if report.universals.any (fun entry => entry.1 == name && entry.2 == predicate) then
    some (SemanticCertificate.universalInstantiation name predicate)
  else
    none

def readThenVerifyCertificate? (report : ProofReport) :
    Option SemanticCertificate :=
  if reportHasEvidence report then
    some SemanticCertificate.readThenVerifyAvailable
  else
    none

theorem alias_inseparability_certificate_example :
    (aliasInseparabilityCertificate? [("文", "道")]
      (operatorApp { surface := "不", carrier := .root512 Root512.originOperator }
        ["文", "离道"] .infix)).isSome = true := by
  native_decide

theorem alias_transitive_inseparability_certificate_example :
    (aliasInseparabilityCertificate? [("理", "道"), ("文", "理")]
      (operatorApp { surface := "不", carrier := .root512 Root512.originOperator }
        ["文", "离道"] .infix)).isSome = true := by
  native_decide

theorem wen_capability_operator_examples :
    (wenCapabilityCertificate? []
      (operatorApp { surface := "可", carrier := .textLayer "M-local" "modal" .modal }
        ["文", "被证故有边界"] .infix)).isSome = true
      ∧ (wenCapabilityCertificate? []
        (operatorApp { surface := "能", carrier := .textLayer "M-local" "modal" .modal }
          ["文", "生文乃编"] .infix)).isSome = true := by
  native_decide

theorem v4_prefix_topic_certificate_examples :
    (controlledOperatorCertificate?
      (operatorApp { surface := "错", carrier := .v4Builtin .cuo }
        ["反其值"] .prefix)).isSome = true
      ∧ (controlledOperatorCertificate?
        (operatorApp { surface := "道", carrier := .v4Builtin .dao }
          ["在核"] .prefix)).isSome = true := by
  native_decide

def sentenceTextSchemaCertificate? (line : String) :
    Option SemanticCertificate :=
  match parseSentence line with
  | .operatorApp app => textSchemaOperatorCertificate? app
  | _ => none

theorem boundary_formation_schema_examples :
    (parseBoundaryFormationInstantiation? "道不为物而物以之成形").isSome = true
      ∧ (parseBoundaryFormationInstantiation? "道不为名而名以之立实").isSome = true
      ∧ (parseBoundaryFormationInstantiation? "道不为数而数以之定位").isSome = true
      ∧ (parseBoundaryFormationInstantiation? "道不为名而实以之立名").isSome = false
      ∧ (sentenceTextSchemaCertificate? "道不为物而物以之成形").isSome = true := by
  native_decide

def sentenceCapabilitySchemaCertificate? (line : String)
    (aliases : List (String × String) := []) : Option SemanticCertificate :=
  match parseSentence line with
  | .operatorApp app => capabilitySchemaOperatorCertificate? aliases app
  | _ => none

theorem capability_schema_examples :
    (parseCapabilitySchemaInstantiation? "文可被读故有解释").isSome = true
      ∧ (parseCapabilitySchemaInstantiation? "文能生文乃编").isSome = true
      ∧ (parseCapabilitySchemaInstantiation? "文能改文而留其证乃德").isSome = true
      ∧ (sentenceCapabilitySchemaCertificate? "文可被证故有边界").isSome = true
      ∧ (sentenceCapabilitySchemaCertificate? "经可被读故有解释" [("经", "文")]).isSome = true
      ∧ (sentenceCapabilitySchemaCertificate? "石可被读故有解释").isSome = false := by
  native_decide

def sentenceStructuralSchemaCertificate? (line : String) :
    Option SemanticCertificate :=
  match parseSentence line with
  | .operatorApp app => structuralSchemaOperatorCertificate? app
  | _ => none

theorem structural_schema_examples :
    (parseStructuralSchemaInstantiation? "一字在文中为名").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "卦为形").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "六位成卦").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "每格有其卦").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "德在行").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "字有所指").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "形不离读").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "位可组合").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "一至六十四可以入字").isSome = true
      ∧ (parseStructuralSchemaInstantiation? "道不为名而实以之立名").isSome = false
      ∧ (parseStructuralSchemaInstantiation? "石为金").isSome = false
      ∧ (sentenceStructuralSchemaCertificate? "每格有其时").isSome = true := by
  native_decide

def sentenceDualitySchemaCertificate? (line : String) :
    Option SemanticCertificate :=
  match parseSentence line with
  | .operatorApp app => dualitySchemaOperatorCertificate? app
  | _ => none

theorem duality_schema_examples :
    (parseDualitySchemaInstantiation? "乃一事之四读").isSome = true
      ∧ (parseDualitySchemaInstantiation? "同一内容框架复合").isSome = true
      ∧ (parseDualitySchemaInstantiation? "意义由此有骨").isSome = true
      ∧ (parseDualitySchemaInstantiation? "反复其文").isSome = true
      ∧ (parseDualitySchemaInstantiation? "名复其文").isSome = false
      ∧ (sentenceDualitySchemaCertificate? "意义由此有骨").isSome = true := by
  native_decide

def sentenceDiscourseSchemaCertificate? (line : String) :
    Option SemanticCertificate :=
  match parseSentence line with
  | .operatorApp app => discourseOperatorSchemaCertificate? app
  | .implication condition conclusion =>
      discourseImplicationSchemaCertificate? condition conclusion
  | _ => none

theorem discourse_schema_examples :
    (parseAbsenceDegradationInstantiation? "无德" "道但为空名").isSome = true
      ∧ (parseAbsenceDegradationInstantiation? "无道" "德但为习气").isSome = true
      ∧ (parseSelfRuleInstantiation? "程序若自其规则而行").isSome = true
      ∧ (parseSelfRuleInstantiation? "证明若自其公理而出").isSome = true
      ∧ (parseCausativeInstantiation? "使后文承前文之证").isSome = true
      ∧ (parseCausativeInstantiation? "使字渐多而核不散").isSome = true
      ∧ (sentenceDiscourseSchemaCertificate? "无德则道但为空名").isSome = true
      ∧ (sentenceDiscourseSchemaCertificate? "程序若自其规则而行").isSome = true
      ∧ (sentenceDiscourseSchemaCertificate? "使后文承前文之证").isSome = true
      ∧ (parseCausativeInstantiation? "使石承前文之证").isSome = false := by
  native_decide

def mkDiagnostic (line column : Nat) (kind : DiagnosticKind)
    (message text : String) : Diagnostic :=
  { line := line
  , column := column
  , span := spanForLine line text
  , kind := kind
  , message := message
  , text := text }

def mkDiagnosticAt (line : Nat) (text focus : String)
    (kind : DiagnosticKind) (message : String) : Diagnostic :=
  let span := spanForSubstring line text focus
  { line := line
  , column := span.startColumn
  , span := span
  , kind := kind
  , message := message
  , text := text }

def mkLocatedDiagnostic (located : LocatedSentence) (kind : DiagnosticKind)
    (message : String) : Diagnostic :=
  { line := located.line
  , column := located.column
  , span := located.span
  , kind := kind
  , message := message
  , text := located.text }

def actionArgumentKnown? (app : OperatorApplication) : Bool :=
  match app.form, app.args with
  | .applicationParticle, [argSurface] =>
      (SSBX.Foundation.Wen.Layered.Bridges.Word64.wordOfToken argSurface).isSome
  | _, _ => false

def executableApplication? (app : OperatorApplication) : Bool :=
  (v4ActionTrace? app).isSome || (rootApplicationTrace? app).isSome

def operatorApplicationHasUnknownArgument? (app : OperatorApplication) : Bool :=
  match app.op.carrier, app.form, app.args with
  | .v4Builtin _, .applicationParticle, [argSurface]
  | .root512 _, .applicationParticle, [argSurface] =>
      (applicationArgumentWordFuel? 8 argSurface).isNone
  | _, _, _ => false

def operatorRegistrationCertificate? (app : OperatorApplication) :
    Option SemanticCertificate :=
  if executableApplication? app || operatorApplicationHasUnknownArgument? app then
    none
  else
    some (SemanticCertificate.operatorRegistration app)

def operatorDiagnostics (line _column : Nat) (text : String)
    (app : OperatorApplication) : List Diagnostic :=
  if executableApplication? app then
    []
  else
    match app.op.carrier with
    | .v4Builtin _ | .root512 _ =>
        match app.form, app.args with
        | .applicationParticle, [_] =>
            if operatorApplicationHasUnknownArgument? app then
              let focus := app.args.headD app.op.surface
              [mkDiagnosticAt line text focus .unknownActionArgument
                "application argument is not a known 64-word token"
                ]
            else
              []
        | _, _ =>
            []
    | .textLayer _code _ _ =>
        []
    | .applicationParticle =>
        []

def sentenceDiagnostics (report : ProofReport) (located : LocatedSentence) :
    List Diagnostic :=
  match located.sentence with
  | .topicComment subject body =>
      match semanticTopicCertificate? subject body with
      | some _ => []
      | none =>
          match topicAliasCertificate? subject body with
          | some _ => []
          | none => []
  | .implication _ _ =>
      match located.sentence with
      | .implication condition conclusion =>
          match implicationSemanticCertificate? report condition conclusion with
          | some _ => []
          | none => []
      | _ => []
  | .instantiateUniversal name predicate =>
      match universalInstantiationCertificate? report name predicate with
      | some _ => []
      | none =>
          [mkDiagnostic located.line located.column .unsupportedUniversalInstantiation
            "explicit universal instantiation has no matching prior schema"
            located.text]
  | .operatorApp app =>
      match operatorSemanticCertificate? report app with
      | some _ => []
      | none => operatorDiagnostics located.line located.column located.text app
  | .claimStub _ _ =>
      [mkDiagnostic located.line located.column .claimStub
        "malformed controlled form or unknown certificate target"
        located.text]
  | .readThenVerify =>
      match readThenVerifyCertificate? report with
      | some _ => []
      | none =>
          [mkDiagnostic located.line located.column .unsupportedReadThenVerify
            "read-then-verify requires a prior certificate or executable action trace"
            located.text]
  | _ => []

def emptyReport : ProofReport :=
  { definitions := []
  , certificates := []
  , semanticCertificates := []
  , v4Actions := []
  , rootApplications := []
  , diagnostics := []
  , aliases := []
  , topicComments := []
  , implications := []
  , universals := []
  , operatorApps := []
  , assertions := []
  , barePhrases := []
  , aliasCount := 0
  , enumCount := 0
  , readVerifyCount := 0
  , claimStubs := [] }

theorem state_implication_certificate_example :
    (stateImplicationCertificate?
      { emptyReport with
        aliases := [("文", "道")]
        semanticCertificates := [SemanticCertificate.cyclicPersistence] }
      "文不离道" "有可证").isSome = true := by
  native_decide

theorem universal_instantiation_certificate_example :
    (universalInstantiationCertificate?
      { emptyReport with universals := [("文", "可证")] }
      "文" "可证").isSome = true := by
  native_decide

theorem read_then_verify_certificate_example :
    (readThenVerifyCertificate?
      { emptyReport with
        semanticCertificates := [SemanticCertificate.cyclicPersistence] }).isSome = true := by
  native_decide

theorem registration_does_not_count_as_certificate_evidence :
    reportHasCertificate
      { emptyReport with
        semanticCertificates := [SemanticCertificate.topicRegistration "文" "道"] } = false := by
  native_decide

def processSentence (sentence : Sentence) (report : ProofReport) :
    ProofReport :=
  match sentence with
  | .defineR5 name value =>
      addVerified name value { report with definitions := (name, value) :: report.definitions }
  | .topicComment subject body =>
      let report := { report with topicComments := (subject, body) :: report.topicComments }
      match semanticTopicCertificate? subject body with
      | some cert => { report with semanticCertificates := cert :: report.semanticCertificates }
      | none =>
          match topicAliasCertificate? subject body with
          | some cert =>
              { report with
                aliases := (subject, body) :: report.aliases
                semanticCertificates := cert :: report.semanticCertificates
                aliasCount := report.aliasCount + 1 }
          | none =>
              { report with
                semanticCertificates :=
                  SemanticCertificate.topicRegistration subject body ::
                    report.semanticCertificates }
  | .implication condition conclusion =>
      let report := { report with implications := (condition, conclusion) :: report.implications }
      match implicationSemanticCertificate? report condition conclusion with
      | some cert => { report with semanticCertificates := cert :: report.semanticCertificates }
      | none =>
          { report with
            semanticCertificates :=
              SemanticCertificate.implicationRegistration condition conclusion ::
                report.semanticCertificates }
  | .universal domain predicate =>
      { report with
        universals := (domain, predicate) :: report.universals
        semanticCertificates :=
          SemanticCertificate.universalSchema domain predicate ::
            report.semanticCertificates }
  | .instantiateUniversal name predicate =>
      match universalInstantiationCertificate? report name predicate with
      | some cert => { report with semanticCertificates := cert :: report.semanticCertificates }
      | none => report
  | .operatorApp app =>
      let report := { report with operatorApps := app :: report.operatorApps }
      let report :=
        match v4ActionTrace? app with
        | some trace =>
            { report with
              v4Actions := trace :: report.v4Actions
              semanticCertificates :=
                SemanticCertificate.v4ActionTrace trace ::
                  report.semanticCertificates }
        | none => report
      let report :=
        match rootApplicationTrace? app with
        | some trace =>
            { report with
              rootApplications := trace :: report.rootApplications
              semanticCertificates :=
                SemanticCertificate.rootActionTrace trace ::
                  report.semanticCertificates }
        | none => report
      match operatorSemanticCertificate? report app with
      | some cert => { report with semanticCertificates := cert :: report.semanticCertificates }
      | none =>
          match operatorRegistrationCertificate? app with
          | some cert => { report with semanticCertificates := cert :: report.semanticCertificates }
          | none => report
  | .assertion body =>
      { report with assertions := body :: report.assertions }
  | .barePhrase text tokens =>
      { report with barePhrases := (text, tokens) :: report.barePhrases }
  | .verifyR5 name =>
      match lookupDef report.definitions name with
      | some value => addVerified name value report
      | none => { report with claimStubs := (s!"验 {name} 为五爻", [name]) :: report.claimStubs }
  | .verifyKernelDao name =>
      match lookupDef report.definitions name with
      | some value =>
          if kernelDaoMembershipCheck name value then
            { report with
              semanticCertificates :=
                SemanticCertificate.kernelDaoMembership name value ::
                  report.semanticCertificates }
          else
            { report with claimStubs := (s!"验 {name} 属于道", [name]) :: report.claimStubs }
      | none => { report with claimStubs := (s!"验 {name} 属于道", [name]) :: report.claimStubs }
  | .alias left right =>
      { report with
        aliases := (left, right) :: report.aliases
        semanticCertificates :=
          SemanticCertificate.aliasIdentity left right :: report.semanticCertificates
        aliasCount := report.aliasCount + 1 }
  | .enumHead _ => { report with enumCount := report.enumCount + 1 }
  | .readThenVerify =>
      let report := { report with readVerifyCount := report.readVerifyCount + 1 }
      match readThenVerifyCertificate? report with
      | some cert => { report with semanticCertificates := cert :: report.semanticCertificates }
      | none => report
  | .claimStub text tokens =>
      { report with claimStubs := (text, tokens) :: report.claimStubs }

def processLocatedSentence (located : LocatedSentence) (report : ProofReport) :
    ProofReport :=
  let diagnostics := sentenceDiagnostics report located
  let report := processSentence located.sentence report
  { report with diagnostics := diagnostics ++ report.diagnostics }

def proveSentences : List Sentence → ProofReport → ProofReport
  | [], report => report
  | sentence :: rest, report => proveSentences rest (processSentence sentence report)

def proveLocatedSentences : List LocatedSentence → ProofReport → ProofReport
  | [], report => report
  | sentence :: rest, report => proveLocatedSentences rest (processLocatedSentence sentence report)

def proveDocument (doc : Document) : ProofReport :=
  proveLocatedSentences doc.located emptyReport

def proveSource (source : String) : Except ParseError ProofReport := do
  let doc ← parseDocument source
  pure (proveDocument doc)

/-! ## Provisional Wuchang coordinates -/

def ren : R5Word := ⟨⟨.interval, .trace⟩, .yang⟩
def yi : R5Word := ⟨⟨.motion, .occasion⟩, .yang⟩
def li : R5Word := ⟨⟨.thing, .momentum⟩, .yang⟩
def zhi : R5Word := ⟨⟨.interval, .pivot⟩, .yang⟩
def xin : R5Word := ⟨⟨.event, .trace⟩, .yang⟩

def wuchangDefinitions : List (String × R5Word) :=
  [("仁", ren), ("义", yi), ("礼", li), ("智", zhi), ("信", xin)]

theorem wuchang_all_roundtrip :
    wuchangDefinitions.all
      (fun entry => R5Word.ofView entry.2.toView == entry.2) = true := by
  native_decide

theorem wuchang_all_in_r5 :
    wuchangDefinitions.length = 5
      ∧ wuchangDefinitions.all
        (fun entry => R5Word.ofView entry.2.toView == entry.2) = true :=
  ⟨rfl, wuchang_all_roundtrip⟩

theorem semantic_certificate_class_examples :
    SemanticCertificateKind.topicRegistration.isRegistration = true
      ∧ SemanticCertificateKind.universalSchema.isRegistration = true
      ∧ SemanticCertificateKind.v4ActionTrace.isExecutable = true
      ∧ SemanticCertificateKind.frontierClean.isStatus = true
      ∧ SemanticCertificateKind.operatorRegistration.countsAsEvidence = false := by
  native_decide

/-! ## Smoke examples -/

def wuchangSource : String :=
"零起
仁者 间几阳 也
义者 动时阳 也
礼者 物势阳 也
智者 间机阳 也
信者 事几阳 也
验 仁 为五爻
验 义 为五爻
验 礼 为五爻
验 智 为五爻
验 信 为五爻"

def wuchangDaoSource : String :=
"零起
仁者 间几阳 也
义者 动时阳 也
礼者 物势阳 也
智者 间机阳 也
信者 事几阳 也
验 仁 为五爻
验 义 为五爻
验 礼 为五爻
验 智 为五爻
验 信 为五爻
验 仁 属于道
验 义 属于道
验 礼 属于道
验 智 属于道
验 信 属于道"

theorem parse_wuchangSource_ok :
    (parseDocument wuchangSource).isOk = true := by
  native_decide

def reportShape (defs certs stubs aliases enums readThen : Nat)
    (report : ProofReport) : Bool :=
  report.definitions.length == defs
    && report.certificates.length == certs
    && report.claimStubs.length == stubs
    && report.aliasCount == aliases
    && report.enumCount == enums
    && report.readVerifyCount == readThen

def proveSourceShape (source : String)
    (defs certs stubs aliases enums readThen : Nat) : Bool :=
  match proveSource source with
  | .ok report => reportShape defs certs stubs aliases enums readThen report
  | .error _ => false

theorem prove_wuchangSource_summary :
    proveSourceShape wuchangSource 5 10 0 0 0 0 = true := by
  native_decide

def reportExtendedShape (semantics diagnostics v4 root : Nat)
    (strictClean : Bool) (report : ProofReport) : Bool :=
  report.semanticCertificates.length == semantics
    && report.diagnostics.length == diagnostics
    && report.v4Actions.length == v4
    && report.rootApplications.length == root
    && report.strictClean == strictClean

def proveSourceExtendedShape (source : String)
    (semantics diagnostics v4 root : Nat) (strictClean : Bool) : Bool :=
  match proveSource source with
  | .ok report => reportExtendedShape semantics diagnostics v4 root strictClean report
  | .error _ => false

def frontierShape
    (topics implications universals readThen textLayer appGrammar unknownArgs claimStubs : Nat)
    (summary : FrontierSummary) : Bool :=
  summary.unsupportedTopicTheorems == topics
    && summary.unsupportedImplicationProofs == implications
    && summary.unsupportedUniversalInstantiations == universals
    && summary.unsupportedReadThenVerifications == readThen
    && summary.unsupportedTextLayerOperators == textLayer
    && summary.unsupportedApplicationGrammars == appGrammar
    && summary.unknownActionArguments == unknownArgs
    && summary.claimStubDiagnostics == claimStubs

def proveSourceFrontierShape (source : String)
    (topics implications universals readThen textLayer appGrammar unknownArgs claimStubs : Nat) :
    Bool :=
  match proveSource source with
  | .ok report =>
      frontierShape topics implications universals readThen textLayer appGrammar unknownArgs
        claimStubs report.frontierSummary
  | .error _ => false

theorem prove_wuchangDaoSource_summary :
    proveSourceShape wuchangDaoSource 5 10 0 0 0 0 = true
      ∧ proveSourceExtendedShape wuchangDaoSource 5 0 0 0 true = true
      ∧ proveSourceFrontierShape wuchangDaoSource 0 0 0 0 0 0 0 0 = true := by
  native_decide

def zeroStartMiniSource : String :=
"零起
凡文之始道理显焉
此文者文也
读之则验
名即实
仁者 间几阳 也
验 仁 为五爻"

theorem prove_zeroStartMiniSource_summary :
    proveSourceShape zeroStartMiniSource 1 2 0 2 0 1 = true := by
  native_decide

def strictOkSource : String :=
"零起
生生不息者往复而不穷也
若错之乾则坤
若不之乾则坤
文即理
理即道
文为道
若文不离道则有可证
文不离道
有可证
凡文皆可证
验 文 为可证
错之乾
错之综之乾
不之乾
印之乾
读之则验
无未证"

def diagnosticsDemoSource : String :=
"零起
生生不息者往复而不穷也
若错之乾则坤
若不之乾则坤
若生则息
文不离道
有可证
错之乾
错之龘龘
印之乾
不之乾
有未证
读之则验"

def statusBridgeSource : String :=
"零起
此文者文也
有已名
文可被读故有解释
有可算
文能生文乃编
有未算
有待名"

def nameResolutionSource : String :=
"零起
若名不入环境则名为symbol
若名入环境则名为reference
若名被束则名为local
若名被定义则名为global"

def v4TopicSource : String :=
"零起
道者不移
错者反其内容
综者反其框架
错综者双反而复成一轨"

theorem prove_strictOkSource_extended_summary :
    proveSourceShape strictOkSource 0 0 0 2 0 1 = true
      ∧ proveSourceExtendedShape strictOkSource 17 0 2 2 true = true
      ∧ proveSourceFrontierShape strictOkSource 0 0 0 0 0 0 0 0 = true := by
  native_decide

theorem prove_diagnosticsDemoSource_extended_summary :
    proveSourceShape diagnosticsDemoSource 0 0 0 0 0 1 = true
      ∧ proveSourceExtendedShape diagnosticsDemoSource 11 1 1 2 false = true
      ∧ proveSourceFrontierShape diagnosticsDemoSource 0 0 0 0 0 0 1 0 = true := by
  native_decide

theorem prove_statusBridgeSource_summary :
    proveSourceShape statusBridgeSource 0 0 0 1 0 0 = true
      ∧ proveSourceExtendedShape statusBridgeSource 7 0 0 0 true = true
      ∧ proveSourceFrontierShape statusBridgeSource 0 0 0 0 0 0 0 0 = true := by
  native_decide

theorem prove_nameResolutionSource_summary :
    proveSourceShape nameResolutionSource 0 0 0 0 0 0 = true
      ∧ proveSourceExtendedShape nameResolutionSource 4 0 0 0 true = true
      ∧ proveSourceFrontierShape nameResolutionSource 0 0 0 0 0 0 0 0 = true := by
  native_decide

theorem prove_v4TopicSource_summary :
    proveSourceShape v4TopicSource 0 0 0 0 0 0 = true
      ∧ proveSourceExtendedShape v4TopicSource 4 0 0 0 true = true
      ∧ proveSourceFrontierShape v4TopicSource 0 0 0 0 0 0 0 0 = true := by
  native_decide

def isOperatorAppSentence : Sentence → Bool
  | .operatorApp _ => true
  | _ => false

theorem parse_syntax_examples :
    parseSentence "道者一也" = .topicComment "道" "一"
      ∧ parseSentence "若名不入环境则名为symbol" =
          .implication "名不入环境" "名为symbol"
      ∧ parseSentence "凡文皆可读" = .universal "文" "可读"
      ∧ parseSentence "验 文 为可证" = .instantiateUniversal "文" "可证"
      ∧ parseSentence "验 仁 为道" = .verifyKernelDao "仁"
      ∧ parseSentence "验 仁 属于道" = .verifyKernelDao "仁"
      ∧ isOperatorAppSentence (parseSentence "卦为形") = true
      ∧ parseSentence "仁者间几阳也" = .defineR5 "仁" ren
      ∧ isOperatorAppSentence (parseSentence "文可被读故有解释") = true
      ∧ parseSentence "读之则显" = .implication "读之" "显"
      ∧ isOperatorAppSentence (parseSentence "程序若自其规则而行") = true
      ∧ isOperatorAppSentence (parseSentence "有可证") = true
      ∧ isOperatorAppSentence (parseSentence "文见其德") = true
      ∧ isOperatorAppSentence (parseSentence "文开其后") = true
      ∧ parseSentence "错 之 乾" =
          .operatorApp
            (operatorApp { surface := "错", carrier := .v4Builtin .cuo }
              ["乾"] .applicationParticle)
      ∧ parseSentence "系统也" = .assertion "系统"
      ∧ isOperatorAppSentence (parseSentence "一公理") = true := by
  native_decide

theorem wenscript_summary :
    wuchangDefinitions.length = 5
      ∧ (parseDocument wuchangSource).isOk = true
      ∧ (parseDocument "仁者 间几阳 也").isOk = false
      ∧ wuchangDefinitions.all
        (fun entry => R5Word.ofView entry.2.toView == entry.2) = true := by
  exact ⟨rfl, parse_wuchangSource_ok, by native_decide, wuchang_all_roundtrip⟩

end WenScript

end SSBX.Foundation.Wen.V4Kernel
