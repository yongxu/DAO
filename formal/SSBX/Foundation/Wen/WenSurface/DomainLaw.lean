/-
# WenSurface.DomainLaw -- first-wave domain-law registry

This module records domain laws that are stronger than "this row has an exact
carrier body" but still intentionally narrow.  The evaluator stays unchanged:
these laws certify that a set of carrier/anchor rows now has a small typed
domain interface, so they no longer need to appear in the domain-caveat ledger.
-/
import SSBX.Foundation.Wen.WenDefEval
import SSBX.Text.WenyanOperators

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Foundation.Yi.Yi
open SSBX.Text.WenyanOperators

/-! ## Domain-law kinds -/

inductive DomainLawKind where
  | spatialFrameAccessor
  | aspectMarkerAccessor
  | nameObjectAccessor
  | medicineFrameAccessor
  | divinationCognitionAccessor
  | institutionFrameAccessor
  | pairRelationCore
  | directedRelation
  | namingMeasureRelation
  | protocolRelation
  | zhuangziRelation
  | identityNoopLaw
  | applicationWrapperLaw
  | predicateAnchorLaw
  | truthMarkerLaw
  | facet2Core
  | partitionFacet
  | selfFacet
  | collectionSeed
  | institutionalAggregate
  | medicalCosmologicalAggregate
  | aggregateFoldProjection
deriving Repr, DecidableEq

namespace DomainLawKind

def key : DomainLawKind → String
  | .spatialFrameAccessor => "spatial-frame-accessor"
  | .aspectMarkerAccessor => "aspect-marker-accessor"
  | .nameObjectAccessor => "name-object-accessor"
  | .medicineFrameAccessor => "medicine-frame-accessor"
  | .divinationCognitionAccessor => "divination-cognition-accessor"
  | .institutionFrameAccessor => "institution-frame-accessor"
  | .pairRelationCore => "pair-relation-core"
  | .directedRelation => "directed-relation"
  | .namingMeasureRelation => "naming-measure-relation"
  | .protocolRelation => "protocol-relation"
  | .zhuangziRelation => "zhuangzi-relation"
  | .identityNoopLaw => "identity-noop-law"
  | .applicationWrapperLaw => "application-wrapper-law"
  | .predicateAnchorLaw => "predicate-anchor-law"
  | .truthMarkerLaw => "truth-marker-law"
  | .facet2Core => "facet2-core"
  | .partitionFacet => "partition-facet"
  | .selfFacet => "self-facet"
  | .collectionSeed => "collection-seed"
  | .institutionalAggregate => "institutional-aggregate"
  | .medicalCosmologicalAggregate => "medical-cosmological-aggregate"
  | .aggregateFoldProjection => "aggregate-fold-projection"

def label : DomainLawKind → String
  | .spatialFrameAccessor => "spatial frame accessor"
  | .aspectMarkerAccessor => "aspect marker/accessor"
  | .nameObjectAccessor => "name/object accessor"
  | .medicineFrameAccessor => "medicine frame accessor"
  | .divinationCognitionAccessor => "divination/cognition accessor"
  | .institutionFrameAccessor => "institution/text/strategy accessor"
  | .pairRelationCore => "pair relation core"
  | .directedRelation => "directed relation"
  | .namingMeasureRelation => "naming/measure relation"
  | .protocolRelation => "protocol relation"
  | .zhuangziRelation => "Zhuangzi relation"
  | .identityNoopLaw => "identity/no-op law"
  | .applicationWrapperLaw => "application wrapper law"
  | .predicateAnchorLaw => "predicate anchor law"
  | .truthMarkerLaw => "truth marker law"
  | .facet2Core => "Facet2 core"
  | .partitionFacet => "partition facet"
  | .selfFacet => "self facet"
  | .collectionSeed => "collection seed"
  | .institutionalAggregate => "institutional aggregate"
  | .medicalCosmologicalAggregate => "medical/cosmological aggregate"
  | .aggregateFoldProjection => "aggregate fold/projection"

def note : DomainLawKind → String
  | .spatialFrameAccessor =>
      "domain law: projection/accessor rows preserve the Hex carrier in a spatial frame"
  | .aspectMarkerAccessor =>
      "domain law: aspect/particle rows preserve the Hex carrier as typed markers"
  | .nameObjectAccessor =>
      "domain law: name/object rows preserve the Hex carrier as typed ontology/name accessors"
  | .medicineFrameAccessor =>
      "domain law: medicine rows preserve the Hex carrier as typed physiology/diagnostic accessors"
  | .divinationCognitionAccessor =>
      "domain law: divination/cognition rows preserve the Hex carrier as typed omen/observation accessors"
  | .institutionFrameAccessor =>
      "domain law: institution/text/strategy rows preserve the Hex carrier as typed accessor anchors"
  | .pairRelationCore =>
      "domain law: relation rows denote the ordered Hex pair relation core"
  | .directedRelation =>
      "domain law: directed rows denote source/target Hex pair relations"
  | .namingMeasureRelation =>
      "domain law: naming/measure rows denote referent/value Hex pair relations"
  | .protocolRelation =>
      "domain law: protocol rows denote ordered Hex pair relations for institutional roles"
  | .zhuangziRelation =>
      "domain law: Zhuangzi rows denote ordered Hex pair relations without reducing their doctrine"
  | .identityNoopLaw =>
      "domain law: identity/no-op rows preserve the Hex carrier exactly"
  | .applicationWrapperLaw =>
      "domain law: application wrapper rows use exact Hex endomap application mechanics"
  | .predicateAnchorLaw =>
      "domain law: predicate-anchor rows denote a typed Hex predicate anchor"
  | .truthMarkerLaw =>
      "domain law: truth-marker rows preserve Bool values exactly"
  | .facet2Core =>
      "domain law: two-facet rows duplicate one Hex into left/right facets"
  | .partitionFacet =>
      "domain law: partition rows use the same two-facet interface with domain labels"
  | .selfFacet =>
      "domain law: self-facet row uses the two-facet interface without generalizing it"
  | .collectionSeed =>
      "domain law: collection rows seed a singleton Hex collection"
  | .institutionalAggregate =>
      "domain law: institutional rows seed singleton aggregate carriers"
  | .medicalCosmologicalAggregate =>
      "domain law: medical/cosmological aggregate rows seed finite-family carriers"
  | .aggregateFoldProjection =>
      "domain law: fold/projection rows use exact list2/list3/head mechanics"

end DomainLawKind

def allDomainLawKinds : List DomainLawKind :=
  [ .spatialFrameAccessor
  , .aspectMarkerAccessor
  , .nameObjectAccessor
  , .medicineFrameAccessor
  , .divinationCognitionAccessor
  , .institutionFrameAccessor
  , .pairRelationCore
  , .directedRelation
  , .namingMeasureRelation
  , .protocolRelation
  , .zhuangziRelation
  , .identityNoopLaw
  , .applicationWrapperLaw
  , .predicateAnchorLaw
  , .truthMarkerLaw
  , .facet2Core
  , .partitionFacet
  , .selfFacet
  , .collectionSeed
  , .institutionalAggregate
  , .medicalCosmologicalAggregate
  , .aggregateFoldProjection
  ]

/-! ## Spatial frame accessors -/

inductive SpatialAccessor where
  | center
  | containmentMiddle
  | outside
  | inside
  | surface
  | interior
  | begin
  | finish
  | extreme
deriving Repr, DecidableEq

def SpatialAccessor.operatorId : SpatialAccessor → OperatorId
  | .center => .R_5
  | .containmentMiddle => .C_4
  | .outside => .C_5
  | .inside => .C_6
  | .surface => .C_7
  | .interior => .C_8
  | .begin => .B_1
  | .finish => .B_2
  | .extreme => .B_7

def spatialFrameAccessorOperatorIds : List OperatorId :=
  [.R_5, .C_4, .C_5, .C_6, .C_7, .C_8, .B_1, .B_2, .B_7]

def spatialAccess (_a : SpatialAccessor) (h : Hexagram) : Hexagram := h

theorem spatialAccess_denotes_hex_id (a : SpatialAccessor) (h : Hexagram) :
    denoteHexFun Stdlib.hexIdBody h = some (spatialAccess a h) :=
  hexIdBody_eq_id h

/-! ## Aspect and particle markers -/

inductive AspectMarker where
  | gradual
  | sudden
  | abrupt
  | frequent
  | intensify
  | increase
  | slowSoak
  | additive
  | completedAdverb
  | notYetAdverb
  | prospectiveAdverb
  | progressiveAdverb
  | experientialAdverb
  | completed
  | prospective
  | progressive
  | experiential
  | binderParticle
  | predicationParticle
  | nominalizer
  | notYet
  | already
deriving Repr, DecidableEq

def AspectMarker.operatorId : AspectMarker → OperatorId
  | .gradual => .A_1
  | .sudden => .A_2
  | .abrupt => .A_3
  | .frequent => .A_7
  | .intensify => .A_8
  | .increase => .A_9
  | .slowSoak => .A_10
  | .additive => .A_15
  | .completedAdverb => .A_16
  | .notYetAdverb => .A_17
  | .prospectiveAdverb => .A_18
  | .progressiveAdverb => .A_19
  | .experientialAdverb => .A_20
  | .completed => .S_9
  | .prospective => .S_10
  | .progressive => .S_11
  | .experiential => .S_12
  | .binderParticle => .S_13
  | .predicationParticle => .S_14
  | .nominalizer => .S_16
  | .notYet => .S_17
  | .already => .S_18

def aspectMarkerAccessorOperatorIds : List OperatorId :=
  [.A_1, .A_2, .A_3, .A_7, .A_8, .A_9, .A_10, .A_15,
   .A_16, .A_17, .A_18, .A_19, .A_20,
   .S_9, .S_10, .S_11, .S_12, .S_13, .S_14, .S_16, .S_17, .S_18]

def aspectMarker (_a : AspectMarker) (h : Hexagram) : Hexagram := h

theorem aspectMarker_denotes_hex_id (a : AspectMarker) (h : Hexagram) :
    denoteHexFun Stdlib.hexIdBody h = some (aspectMarker a h) :=
  hexIdBody_eq_id h

/-! ## Name, object, and ontology accessors -/

inductive NameObjectAccessor where
  | dao
  | principle
  | tendency
  | mechanism
  | image
  | name
  | part
  | duration
  | extent
  | endpoint
  | middle
  | model
  | nameClass
  | textContent
  | classKind
  | object
  | actuality
  | position
deriving Repr, DecidableEq

def NameObjectAccessor.operatorId : NameObjectAccessor → OperatorId
  | .dao => .H_1
  | .principle => .H_2
  | .tendency => .H_3
  | .mechanism => .H_4
  | .image => .H_6
  | .name => .H_7
  | .part => .P_2
  | .duration => .P_6
  | .extent => .P_7
  | .endpoint => .P_10
  | .middle => .P_12
  | .model => .P_18
  | .nameClass => .P_19
  | .textContent => .P_21
  | .classKind => .P_24
  | .object => .G_2
  | .actuality => .G_4
  | .position => .G_5

def nameObjectAccessorOperatorIds : List OperatorId :=
  [.H_1, .H_2, .H_3, .H_4, .H_6, .H_7,
   .P_2, .P_6, .P_7, .P_10, .P_12, .P_18, .P_19, .P_21, .P_24,
   .G_2, .G_4, .G_5]

def nameObjectAccess (_a : NameObjectAccessor) (h : Hexagram) : Hexagram := h

theorem nameObjectAccess_denotes_hex_id (a : NameObjectAccessor) (h : Hexagram) :
    denoteHexFun Stdlib.hexIdBody h = some (nameObjectAccess a h) :=
  hexIdBody_eq_id h

/-! ## Medicine and diagnostic accessors -/

inductive MedicineAccessor where
  | qi
  | blood
  | essence
  | riseFall
  | openClosePivot
  | channelNetwork
  | exteriorInterior
  | coldHeat
  | deficiencyExcess
  | patencyStagnation
  | fiveMovementsSixQi
  | practitionerGrade
  | ingressEgress
  | diagnosticQuery
deriving Repr, DecidableEq

def MedicineAccessor.operatorId : MedicineAccessor → OperatorId
  | .qi => .Y_6
  | .blood => .Y_7
  | .essence => .Y_8
  | .riseFall => .Y_10
  | .openClosePivot => .Y_11
  | .channelNetwork => .Y_12
  | .exteriorInterior => .Y_13
  | .coldHeat => .Y_14
  | .deficiencyExcess => .Y_15
  | .patencyStagnation => .Y_23
  | .fiveMovementsSixQi => .Y_24
  | .practitionerGrade => .Y_25
  | .ingressEgress => .Y_26
  | .diagnosticQuery => .Y_27

def medicineFrameAccessorOperatorIds : List OperatorId :=
  [.Y_6, .Y_7, .Y_8, .Y_10, .Y_11, .Y_12, .Y_13, .Y_14,
   .Y_15, .Y_23, .Y_24, .Y_25, .Y_26, .Y_27]

def medicineAccess (_a : MedicineAccessor) (h : Hexagram) : Hexagram := h

theorem medicineAccess_denotes_hex_id (a : MedicineAccessor) (h : Hexagram) :
    denoteHexFun Stdlib.hexIdBody h = some (medicineAccess a h) :=
  hexIdBody_eq_id h

/-! ## Divination, cognition, and poetic vantage accessors -/

inductive DivinationCognitionAccessor where
  | sprout
  | omen
  | divination
  | milfoil
  | observe
  | inspect
  | realize
  | heavenlyPattern
  | directionMethod
  | ascent
deriving Repr, DecidableEq

def DivinationCognitionAccessor.operatorId : DivinationCognitionAccessor → OperatorId
  | .sprout => .Z_23
  | .omen => .Z_24
  | .divination => .Z_26
  | .milfoil => .Z_27
  | .observe => .Z_34
  | .inspect => .Z_35
  | .realize => .Z_38
  | .heavenlyPattern => .ZHU_9
  | .directionMethod => .ZHU_10
  | .ascent => .CHU_4

def divinationCognitionAccessorOperatorIds : List OperatorId :=
  [.Z_23, .Z_24, .Z_26, .Z_27, .Z_34, .Z_35, .Z_38, .ZHU_9, .ZHU_10, .CHU_4]

def divinationCognitionAccess (_a : DivinationCognitionAccessor) (h : Hexagram) : Hexagram := h

theorem divinationCognitionAccess_denotes_hex_id
    (a : DivinationCognitionAccessor) (h : Hexagram) :
    denoteHexFun Stdlib.hexIdBody h = some (divinationCognitionAccess a h) :=
  hexIdBody_eq_id h

/-! ## Institution, textual, ritual, and strategy accessors -/

inductive InstitutionAccessor where
  | textRecord
  | tabooText
  | critiqueText
  | recognitionText
  | deletionText
  | inscriptionText
  | appraisalText
  | powerPosition
  | benefit
  | measure
  | nature
  | transformedNature
  | ritualPosition
  | ritualForm
  | ritualCentrality
  | solitude
  | militaryForm
  | tacticalEmpty
  | tacticalFull
  | irregular
  | indirect
  | direct
  | heartRuler
  | innerEssence
  | seasonTime
  | ordinance
  | supervision
deriving Repr, DecidableEq

def InstitutionAccessor.operatorId : InstitutionAccessor → OperatorId
  | .textRecord => .E_1
  | .tabooText => .E_4
  | .critiqueText => .E_5
  | .recognitionText => .E_6
  | .deletionText => .E_7
  | .inscriptionText => .E_8
  | .appraisalText => .E_9
  | .powerPosition => .L_3
  | .benefit => .L_12
  | .measure => .L_15
  | .nature => .X_1
  | .transformedNature => .X_3
  | .ritualPosition => .LIJ_4
  | .ritualForm => .LIJ_5
  | .ritualCentrality => .LIJ_7
  | .solitude => .LIJ_11
  | .militaryForm => .SUN_1
  | .tacticalEmpty => .SUN_3
  | .tacticalFull => .SUN_4
  | .irregular => .SUN_5
  | .indirect => .SUN_7
  | .direct => .SUN_8
  | .heartRuler => .ZA_3
  | .innerEssence => .ZA_5
  | .seasonTime => .ZA_6
  | .ordinance => .ZA_7
  | .supervision => .ZA_11

def institutionFrameAccessorOperatorIds : List OperatorId :=
  [.E_1, .E_4, .E_5, .E_6, .E_7, .E_8, .E_9,
   .L_3, .L_12, .L_15,
   .X_1, .X_3, .LIJ_4, .LIJ_5, .LIJ_7, .LIJ_11,
   .SUN_1, .SUN_3, .SUN_4, .SUN_5, .SUN_7, .SUN_8,
   .ZA_3, .ZA_5, .ZA_6, .ZA_7, .ZA_11]

def institutionAccess (_a : InstitutionAccessor) (h : Hexagram) : Hexagram := h

theorem institutionAccess_denotes_hex_id (a : InstitutionAccessor) (h : Hexagram) :
    denoteHexFun Stdlib.hexIdBody h = some (institutionAccess a h) :=
  hexIdBody_eq_id h

/-! ## Pair relation core -/

inductive PairRelationCore where
  | couple
  | parallel
  | with
  | together
  | contain
  | distinguish
  | combine
  | merge
  | remainder
deriving Repr, DecidableEq

def PairRelationCore.operatorId : PairRelationCore → OperatorId
  | .couple => .R_12
  | .parallel => .R_13
  | .with => .R_14
  | .together => .R_15
  | .contain => .C_2
  | .distinguish => .N_8
  | .combine => .I_7
  | .merge => .G_8
  | .remainder => .D_8

def pairRelationCoreOperatorIds : List OperatorId :=
  [.R_12, .R_13, .R_14, .R_15, .C_2, .N_8, .I_7, .G_8, .D_8]

def pairRelation (_r : PairRelationCore) (a b : Hexagram) : Hexagram × Hexagram :=
  (a, b)

theorem pairRelation_denotes_pair (r : PairRelationCore) (a b : Hexagram) :
    denoteHexPair (.app (.app Stdlib.pairHBody (.hexLit a)) (.hexLit b)) =
      some (pairRelation r a b) :=
  pairHBody_eq_pair a b

def directedRelationOperatorIds : List OperatorId :=
  [.T_3, .T_11, .K_5, .H_5, .P_8, .L_2, .Y_16, .Y_19, .Y_28,
   .X_2, .X_13, .X_15, .Z_20, .Z_25, .Z_28, .ZHU_6, .ZHU_7, .ZHU_8,
   .SUN_2, .SUN_9, .SUN_10, .SUN_11, .SUN_13,
   .CHU_1, .CHU_3, .CHU_5, .CHU_6, .CHU_7, .ZA_10]

def directedRelation (_id : OperatorId) (source target : Hexagram) : Hexagram × Hexagram :=
  (source, target)

theorem directedRelation_denotes_pair (id : OperatorId) (source target : Hexagram) :
    denoteHexPair (.app (.app Stdlib.pairHBody (.hexLit source)) (.hexLit target)) =
      some (directedRelation id source target) :=
  pairHBody_eq_pair source target

def namingMeasureRelationOperatorIds : List OperatorId :=
  [.P_11, .P_13, .P_22, .G_1, .G_7, .G_11, .E_2, .E_3]

def namingMeasureRelation (_id : OperatorId) (referent value : Hexagram) : Hexagram × Hexagram :=
  (referent, value)

theorem namingMeasureRelation_denotes_pair (id : OperatorId) (referent value : Hexagram) :
    denoteHexPair (.app (.app Stdlib.pairHBody (.hexLit referent)) (.hexLit value)) =
      some (namingMeasureRelation id referent value) :=
  pairHBody_eq_pair referent value

def protocolRelationOperatorIds : List OperatorId :=
  [.L_1, .L_8, .L_16, .X_7, .X_10,
   .LIJ_1, .LIJ_2, .LIJ_3, .LIJ_8, .LIJ_10, .LIJ_12, .LIJ_13, .LIJ_14,
   .SUN_14, .CHU_8, .ZA_1, .ZA_8]

def protocolRelation (_id : OperatorId) (left right : Hexagram) : Hexagram × Hexagram :=
  (left, right)

theorem protocolRelation_denotes_pair (id : OperatorId) (left right : Hexagram) :
    denoteHexPair (.app (.app Stdlib.pairHBody (.hexLit left)) (.hexLit right)) =
      some (protocolRelation id left right) :=
  pairHBody_eq_pair left right

def zhuangziRelationOperatorIds : List OperatorId :=
  [.ZHU_3, .ZHU_4, .ZHU_11, .ZHU_12]

def zhuangziRelation (_id : OperatorId) (left right : Hexagram) : Hexagram × Hexagram :=
  (left, right)

theorem zhuangziRelation_denotes_pair (id : OperatorId) (left right : Hexagram) :
    denoteHexPair (.app (.app Stdlib.pairHBody (.hexLit left)) (.hexLit right)) =
      some (zhuangziRelation id left right) :=
  pairHBody_eq_pair left right

/-! ## Remaining narrow carrier laws -/

def identityNoopLawOperatorIds : List OperatorId :=
  [.R_6, .R_11, .T_7, .T_8, .B_4, .F_11, .I_2, .D_1, .P_9,
   .L_9, .L_10, .L_11, .Y_17, .Y_18, .ZA_2, .SUN_6, .Z_12, .Z_13,
   .B_5, .B_6]

def identityNoop (_id : OperatorId) (h : Hexagram) : Hexagram := h

theorem identityNoop_denotes_hex_id (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.hexIdBody h = some (identityNoop id h) :=
  hexIdBody_eq_id h

def applicationWrapperLawOperatorIds : List OperatorId :=
  [.Z_29, .Z_32, .S_1, .S_19, .F_1, .F_2, .F_7, .F_8, .K_6, .K_7, .K_8, .L_7]

def applicationWrapper (_id : OperatorId) (h : Hexagram) : Hexagram := h

theorem applicationWrapper_denotes_hex_id (id : OperatorId) (h : Hexagram) :
    denoteHex (.app (.app Stdlib.hexApplyBody Stdlib.hexIdBody) (.hexLit h)) =
      some (applicationWrapper id h) := by
  unfold applicationWrapper
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

def predicateAnchorLawOperatorIds : List OperatorId :=
  [.B_8, .G_3, .G_6, .D_5, .D_6, .D_7, .Z_39, .ZA_13, .ZA_14]

def predicateAnchorBody : Tm :=
  .abs "x" .hex (.boolLit true)

def predicateAnchor (_id : OperatorId) (_h : Hexagram) : Bool := true

theorem predicateAnchor_denotes_true (id : OperatorId) (h : Hexagram) :
    denoteBool (.app predicateAnchorBody (.hexLit h)) = some (predicateAnchor id h) := by
  unfold predicateAnchor
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

def truthMarkerLawOperatorIds : List OperatorId :=
  [.S_4, .S_5, .S_6, .S_8]

def truthMarker (_id : OperatorId) (b : Bool) : Bool := b

theorem truthMarker_denotes_bool_id (id : OperatorId) (b : Bool) :
    denoteBool (.app Stdlib.boolMarkerBody (.boolLit b)) = some (truthMarker id b) :=
  boolMarkerBody_eq_id b

/-! ## Aggregate, facet, and list laws -/

def facet2CoreOperatorIds : List OperatorId :=
  [.H_8, .D_4, .L_6, .Y_1, .Y_21, .Y_22]

def partitionFacetOperatorIds : List OperatorId :=
  [.G_9, .X_5, .X_8, .X_12, .SUN_12, .ZA_4]

def selfFacetOperatorIds : List OperatorId :=
  [.ZHU_5]

def collectionSeedOperatorIds : List OperatorId :=
  [.P_3, .X_4, .Z_7, .Z_16, .Z_17, .Z_21, .Z_30, .CHU_9]

def institutionalAggregateOperatorIds : List OperatorId :=
  [.L_5, .L_13, .L_14, .X_6, .X_9, .ZA_9, .ZA_12]

def medicalCosmologicalAggregateOperatorIds : List OperatorId :=
  [.Y_2, .Y_9]

def aggregateFoldProjectionOperatorIds : List OperatorId :=
  [.X_14, .Z_19, .X_11, .X_16, .ZHU_2, .CHU_2, .Z_18]

def facet2 (_id : OperatorId) (h : Hexagram) : Hexagram × Hexagram := (h, h)

theorem facet2_denotes_dup (id : OperatorId) (h : Hexagram) :
    denoteHexPair (.app Stdlib.dupHBody (.hexLit h)) = some (facet2 id h) :=
  dupHBody_eq_dup h

def collectionSeed (_id : OperatorId) (h : Hexagram) : List Hexagram := [h]

theorem collectionSeed_denotes_singleton (id : OperatorId) (h : Hexagram) :
    denoteHexList (.app Stdlib.list1HBody (.hexLit h)) = some (collectionSeed id h) :=
  list1HBody_eq_singleton h

def binaryAggregate (_id : OperatorId) (a b : Hexagram) : List Hexagram := [a, b]

theorem binaryAggregate_denotes_list2 (id : OperatorId) (a b : Hexagram) :
    denoteHexList (.app (.app Stdlib.list2HBody (.hexLit a)) (.hexLit b)) =
      some (binaryAggregate id a b) :=
  list2HBody_eq_pairList a b

def ternaryAggregate (_id : OperatorId) (a b c : Hexagram) : List Hexagram := [a, b, c]

theorem ternaryAggregate_denotes_list3 (id : OperatorId) (a b c : Hexagram) :
    denoteHexList (.app (.app (.app Stdlib.list3HBody (.hexLit a)) (.hexLit b)) (.hexLit c)) =
      some (ternaryAggregate id a b c) :=
  list3HBody_eq_tripleList a b c

def listProjectionHead (_id : OperatorId) (h : Hexagram) : Hexagram := h

theorem listProjectionHead_denotes_head_singleton (id : OperatorId) (h : Hexagram) :
    denoteHex (.app Stdlib.headHBody (.app Stdlib.list1HBody (.hexLit h))) =
      some (listProjectionHead id h) :=
  headHBody_list1_eq_id h

/-! ## Registry -/

def domainLawKindOperatorIds : DomainLawKind → List OperatorId
  | .spatialFrameAccessor => spatialFrameAccessorOperatorIds
  | .aspectMarkerAccessor => aspectMarkerAccessorOperatorIds
  | .nameObjectAccessor => nameObjectAccessorOperatorIds
  | .medicineFrameAccessor => medicineFrameAccessorOperatorIds
  | .divinationCognitionAccessor => divinationCognitionAccessorOperatorIds
  | .institutionFrameAccessor => institutionFrameAccessorOperatorIds
  | .pairRelationCore => pairRelationCoreOperatorIds
  | .directedRelation => directedRelationOperatorIds
  | .namingMeasureRelation => namingMeasureRelationOperatorIds
  | .protocolRelation => protocolRelationOperatorIds
  | .zhuangziRelation => zhuangziRelationOperatorIds
  | .identityNoopLaw => identityNoopLawOperatorIds
  | .applicationWrapperLaw => applicationWrapperLawOperatorIds
  | .predicateAnchorLaw => predicateAnchorLawOperatorIds
  | .truthMarkerLaw => truthMarkerLawOperatorIds
  | .facet2Core => facet2CoreOperatorIds
  | .partitionFacet => partitionFacetOperatorIds
  | .selfFacet => selfFacetOperatorIds
  | .collectionSeed => collectionSeedOperatorIds
  | .institutionalAggregate => institutionalAggregateOperatorIds
  | .medicalCosmologicalAggregate => medicalCosmologicalAggregateOperatorIds
  | .aggregateFoldProjection => aggregateFoldProjectionOperatorIds

def operatorDomainLawKind? (id : OperatorId) : Option DomainLawKind :=
  if decide (id ∈ spatialFrameAccessorOperatorIds) then
    some .spatialFrameAccessor
  else if decide (id ∈ aspectMarkerAccessorOperatorIds) then
    some .aspectMarkerAccessor
  else if decide (id ∈ nameObjectAccessorOperatorIds) then
    some .nameObjectAccessor
  else if decide (id ∈ medicineFrameAccessorOperatorIds) then
    some .medicineFrameAccessor
  else if decide (id ∈ divinationCognitionAccessorOperatorIds) then
    some .divinationCognitionAccessor
  else if decide (id ∈ institutionFrameAccessorOperatorIds) then
    some .institutionFrameAccessor
  else if decide (id ∈ pairRelationCoreOperatorIds) then
    some .pairRelationCore
  else if decide (id ∈ directedRelationOperatorIds) then
    some .directedRelation
  else if decide (id ∈ namingMeasureRelationOperatorIds) then
    some .namingMeasureRelation
  else if decide (id ∈ protocolRelationOperatorIds) then
    some .protocolRelation
  else if decide (id ∈ zhuangziRelationOperatorIds) then
    some .zhuangziRelation
  else if decide (id ∈ identityNoopLawOperatorIds) then
    some .identityNoopLaw
  else if decide (id ∈ applicationWrapperLawOperatorIds) then
    some .applicationWrapperLaw
  else if decide (id ∈ predicateAnchorLawOperatorIds) then
    some .predicateAnchorLaw
  else if decide (id ∈ truthMarkerLawOperatorIds) then
    some .truthMarkerLaw
  else if decide (id ∈ facet2CoreOperatorIds) then
    some .facet2Core
  else if decide (id ∈ partitionFacetOperatorIds) then
    some .partitionFacet
  else if decide (id ∈ selfFacetOperatorIds) then
    some .selfFacet
  else if decide (id ∈ collectionSeedOperatorIds) then
    some .collectionSeed
  else if decide (id ∈ institutionalAggregateOperatorIds) then
    some .institutionalAggregate
  else if decide (id ∈ medicalCosmologicalAggregateOperatorIds) then
    some .medicalCosmologicalAggregate
  else if decide (id ∈ aggregateFoldProjectionOperatorIds) then
    some .aggregateFoldProjection
  else
    none

def domainLawOperatorIds : List OperatorId :=
  allOperatorIds.filter (fun id => (operatorDomainLawKind? id).isSome)

theorem allDomainLawKinds_length :
    allDomainLawKinds.length = 22 := by native_decide

theorem spatialFrameAccessorOperatorIds_length :
    spatialFrameAccessorOperatorIds.length = 9 := by native_decide

theorem aspectMarkerAccessorOperatorIds_length :
    aspectMarkerAccessorOperatorIds.length = 22 := by native_decide

theorem nameObjectAccessorOperatorIds_length :
    nameObjectAccessorOperatorIds.length = 18 := by native_decide

theorem medicineFrameAccessorOperatorIds_length :
    medicineFrameAccessorOperatorIds.length = 14 := by native_decide

theorem divinationCognitionAccessorOperatorIds_length :
    divinationCognitionAccessorOperatorIds.length = 10 := by native_decide

theorem institutionFrameAccessorOperatorIds_length :
    institutionFrameAccessorOperatorIds.length = 27 := by native_decide

theorem pairRelationCoreOperatorIds_length :
    pairRelationCoreOperatorIds.length = 9 := by native_decide

theorem directedRelationOperatorIds_length :
    directedRelationOperatorIds.length = 29 := by native_decide

theorem namingMeasureRelationOperatorIds_length :
    namingMeasureRelationOperatorIds.length = 8 := by native_decide

theorem protocolRelationOperatorIds_length :
    protocolRelationOperatorIds.length = 17 := by native_decide

theorem zhuangziRelationOperatorIds_length :
    zhuangziRelationOperatorIds.length = 4 := by native_decide

theorem identityNoopLawOperatorIds_length :
    identityNoopLawOperatorIds.length = 20 := by native_decide

theorem applicationWrapperLawOperatorIds_length :
    applicationWrapperLawOperatorIds.length = 12 := by native_decide

theorem predicateAnchorLawOperatorIds_length :
    predicateAnchorLawOperatorIds.length = 9 := by native_decide

theorem truthMarkerLawOperatorIds_length :
    truthMarkerLawOperatorIds.length = 4 := by native_decide

theorem facet2CoreOperatorIds_length :
    facet2CoreOperatorIds.length = 6 := by native_decide

theorem partitionFacetOperatorIds_length :
    partitionFacetOperatorIds.length = 6 := by native_decide

theorem selfFacetOperatorIds_length :
    selfFacetOperatorIds.length = 1 := by native_decide

theorem collectionSeedOperatorIds_length :
    collectionSeedOperatorIds.length = 8 := by native_decide

theorem institutionalAggregateOperatorIds_length :
    institutionalAggregateOperatorIds.length = 7 := by native_decide

theorem medicalCosmologicalAggregateOperatorIds_length :
    medicalCosmologicalAggregateOperatorIds.length = 2 := by native_decide

theorem aggregateFoldProjectionOperatorIds_length :
    aggregateFoldProjectionOperatorIds.length = 7 := by native_decide

theorem domainLawOperatorIds_length :
    domainLawOperatorIds.length = 249 := by native_decide

theorem domainLawOperatorIds_nodup :
    domainLawOperatorIds.Nodup := by native_decide

theorem domainLawKindPartition_counts :
    (domainLawKindOperatorIds .spatialFrameAccessor).length
      + (domainLawKindOperatorIds .aspectMarkerAccessor).length
      + (domainLawKindOperatorIds .nameObjectAccessor).length
      + (domainLawKindOperatorIds .medicineFrameAccessor).length
      + (domainLawKindOperatorIds .divinationCognitionAccessor).length
      + (domainLawKindOperatorIds .institutionFrameAccessor).length
      + (domainLawKindOperatorIds .pairRelationCore).length
      + (domainLawKindOperatorIds .directedRelation).length
      + (domainLawKindOperatorIds .namingMeasureRelation).length
      + (domainLawKindOperatorIds .protocolRelation).length
      + (domainLawKindOperatorIds .zhuangziRelation).length
      + (domainLawKindOperatorIds .identityNoopLaw).length
      + (domainLawKindOperatorIds .applicationWrapperLaw).length
      + (domainLawKindOperatorIds .predicateAnchorLaw).length
      + (domainLawKindOperatorIds .truthMarkerLaw).length
      + (domainLawKindOperatorIds .facet2Core).length
      + (domainLawKindOperatorIds .partitionFacet).length
      + (domainLawKindOperatorIds .selfFacet).length
      + (domainLawKindOperatorIds .collectionSeed).length
      + (domainLawKindOperatorIds .institutionalAggregate).length
      + (domainLawKindOperatorIds .medicalCosmologicalAggregate).length
      + (domainLawKindOperatorIds .aggregateFoldProjection).length =
        domainLawOperatorIds.length := by
  native_decide

example : operatorDomainLawKind? .R_5 = some .spatialFrameAccessor := by native_decide
example : operatorDomainLawKind? .A_1 = some .aspectMarkerAccessor := by native_decide
example : operatorDomainLawKind? .S_13 = some .aspectMarkerAccessor := by native_decide
example : operatorDomainLawKind? .H_1 = some .nameObjectAccessor := by native_decide
example : operatorDomainLawKind? .P_24 = some .nameObjectAccessor := by native_decide
example : operatorDomainLawKind? .Y_6 = some .medicineFrameAccessor := by native_decide
example : operatorDomainLawKind? .Y_27 = some .medicineFrameAccessor := by native_decide
example : operatorDomainLawKind? .Z_26 = some .divinationCognitionAccessor := by native_decide
example : operatorDomainLawKind? .ZHU_9 = some .divinationCognitionAccessor := by native_decide
example : operatorDomainLawKind? .E_1 = some .institutionFrameAccessor := by native_decide
example : operatorDomainLawKind? .SUN_1 = some .institutionFrameAccessor := by native_decide
example : operatorDomainLawKind? .R_12 = some .pairRelationCore := by native_decide
example : operatorDomainLawKind? .T_3 = some .directedRelation := by native_decide
example : operatorDomainLawKind? .E_2 = some .namingMeasureRelation := by native_decide
example : operatorDomainLawKind? .LIJ_1 = some .protocolRelation := by native_decide
example : operatorDomainLawKind? .ZHU_3 = some .zhuangziRelation := by native_decide
example : operatorDomainLawKind? .R_6 = some .identityNoopLaw := by native_decide
example : operatorDomainLawKind? .S_1 = some .applicationWrapperLaw := by native_decide
example : operatorDomainLawKind? .B_8 = some .predicateAnchorLaw := by native_decide
example : operatorDomainLawKind? .S_4 = some .truthMarkerLaw := by native_decide
example : operatorDomainLawKind? .H_8 = some .facet2Core := by native_decide
example : operatorDomainLawKind? .G_9 = some .partitionFacet := by native_decide
example : operatorDomainLawKind? .ZHU_5 = some .selfFacet := by native_decide
example : operatorDomainLawKind? .Z_16 = some .collectionSeed := by native_decide
example : operatorDomainLawKind? .L_13 = some .institutionalAggregate := by native_decide
example : operatorDomainLawKind? .Y_2 = some .medicalCosmologicalAggregate := by native_decide
example : operatorDomainLawKind? .Z_18 = some .aggregateFoldProjection := by native_decide

end SSBX.Foundation.Wen.WenSurface
