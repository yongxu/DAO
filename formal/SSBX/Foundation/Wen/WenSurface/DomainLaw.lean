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
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.BaguaAlgebra
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
  | exactHexTransform
  | boolRelationPredicate
  | hexEqualityLaw
  | hexDisequalityLaw
  | boolNegationLaw
  | boolImplicationLaw
  | boolConjunctionLaw
  | boolDiscriminationLaw
  | finiteQuantifierLaw
  | finiteModalPredicateLaw
  | contextPredicateApplicationLaw
  | endomapControlLaw
  | focusUniqueQuantifierLaw
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
  | .exactHexTransform => "exact-hex-transform"
  | .boolRelationPredicate => "bool-relation-predicate"
  | .hexEqualityLaw => "hex-equality-law"
  | .hexDisequalityLaw => "hex-disequality-law"
  | .boolNegationLaw => "bool-negation-law"
  | .boolImplicationLaw => "bool-implication-law"
  | .boolConjunctionLaw => "bool-conjunction-law"
  | .boolDiscriminationLaw => "bool-discrimination-law"
  | .finiteQuantifierLaw => "finite-quantifier-law"
  | .finiteModalPredicateLaw => "finite-modal-predicate-law"
  | .contextPredicateApplicationLaw => "context-predicate-application-law"
  | .endomapControlLaw => "endomap-control-law"
  | .focusUniqueQuantifierLaw => "focus-unique-quantifier-law"
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
  | .exactHexTransform => "exact Hex transform"
  | .boolRelationPredicate => "Bool relation/predicate"
  | .hexEqualityLaw => "Hex equality law"
  | .hexDisequalityLaw => "Hex disequality law"
  | .boolNegationLaw => "Bool negation law"
  | .boolImplicationLaw => "Bool implication law"
  | .boolConjunctionLaw => "Bool conjunction law"
  | .boolDiscriminationLaw => "Bool discrimination law"
  | .finiteQuantifierLaw => "finite quantifier law"
  | .finiteModalPredicateLaw => "finite modal predicate law"
  | .contextPredicateApplicationLaw => "context predicate application law"
  | .endomapControlLaw => "Hex endomap control law"
  | .focusUniqueQuantifierLaw => "focus/unique quantifier law"
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
  | .exactHexTransform =>
      "domain law: exact unary Hex transform rows denote their registered finite Hex transform"
  | .boolRelationPredicate =>
      "domain law: relation/predicate rows denote the exact Bool relation package"
  | .hexEqualityLaw =>
      "domain law: equality rows denote exact Hex equality"
  | .hexDisequalityLaw =>
      "domain law: disequality rows denote exact Hex disequality"
  | .boolNegationLaw =>
      "domain law: negation rows denote exact Bool negation"
  | .boolImplicationLaw =>
      "domain law: implication rows denote exact truth-functional implication"
  | .boolConjunctionLaw =>
      "domain law: conjunction rows denote exact truth-functional conjunction"
  | .boolDiscriminationLaw =>
      "domain law: discrimination rows denote exact truth-functional exclusive-or"
  | .finiteQuantifierLaw =>
      "domain law: quantifier rows denote exact finite Hex predicate quantifiers"
  | .finiteModalPredicateLaw =>
      "domain law: non-edge modal predicate rows denote exact finite Hex predicate quantifiers"
  | .contextPredicateApplicationLaw =>
      "domain law: context rows denote exact Hex predicate application, not full binder grammar"
  | .endomapControlLaw =>
      "domain law: control rows denote exact Hex endomap composition/repetition"
  | .focusUniqueQuantifierLaw =>
      "domain law: focus row denotes exact finite unique-existence over Hex predicates"
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
  , .exactHexTransform
  , .boolRelationPredicate
  , .hexEqualityLaw
  , .hexDisequalityLaw
  , .boolNegationLaw
  , .boolImplicationLaw
  , .boolConjunctionLaw
  , .boolDiscriminationLaw
  , .finiteQuantifierLaw
  , .finiteModalPredicateLaw
  , .contextPredicateApplicationLaw
  , .endomapControlLaw
  , .focusUniqueQuantifierLaw
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
  | terminus
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
  | .terminus => .B_7

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
  | center
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
  | .center => .P_12
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

/-! ## Exact Hex transform laws -/

def hexIncrementTransformOperatorIds : List OperatorId :=
  [.T_10, .T_15, .B_3, .Y_3, .Z_9, .F_3, .F_5, .F_9, .F_10, .Z_11, .Z_36]

def hexBenefitIncrementTransformOperatorIds : List OperatorId :=
  [.T_13]

def hexDecrementTransformOperatorIds : List OperatorId :=
  [.T_12, .T_14, .Y_4, .Y_5, .Z_8, .Z_22, .F_4, .F_6, .Z_10, .Z_37]

def hexCuoTransformOperatorIds : List OperatorId :=
  [.T_4, .Z_5, .Z_31]

def hexFanReverseTransformOperatorIds : List OperatorId :=
  [.T_6]

def hexZongTransformOperatorIds : List OperatorId :=
  [.T_9, .Z_6]

def hexHuTransformOperatorIds : List OperatorId :=
  [.I_6, .Z_2, .Z_3]

def hexCuoZongTransformOperatorIds : List OperatorId :=
  [.I_8, .Z_33]

def hexFlip1TransformOperatorIds : List OperatorId :=
  [.T_5]

def hexFlip2TransformOperatorIds : List OperatorId :=
  [.T_1]

def hexFlip3TransformOperatorIds : List OperatorId :=
  [.T_2]

def exactHexTransformOperatorIds : List OperatorId :=
  hexIncrementTransformOperatorIds
    ++ hexBenefitIncrementTransformOperatorIds
    ++ hexDecrementTransformOperatorIds
    ++ hexCuoTransformOperatorIds
    ++ hexFanReverseTransformOperatorIds
    ++ hexZongTransformOperatorIds
    ++ hexHuTransformOperatorIds
    ++ hexCuoZongTransformOperatorIds
    ++ hexFlip1TransformOperatorIds
    ++ hexFlip2TransformOperatorIds
    ++ hexFlip3TransformOperatorIds

def hexIncrementTransform (_id : OperatorId) (h : Hexagram) : Hexagram := «生» h

theorem hexIncrementTransform_denotes_tui (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.tuiBody h = some (hexIncrementTransform id h) := by
  unfold hexIncrementTransform
  exact tui_eq_sheng h

def hexBenefitIncrementTransform (_id : OperatorId) (h : Hexagram) : Hexagram := «生» h

theorem hexBenefitIncrementTransform_denotes_yiBenefit (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.yiBenefitBody h = some (hexBenefitIncrementTransform id h) := by
  unfold hexBenefitIncrementTransform
  exact yiBenefit_eq_sheng h

def hexDecrementTransform (_id : OperatorId) (h : Hexagram) : Hexagram :=
  «加» Hexagram.earth h

theorem hexDecrementTransform_denotes_sun (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.sunBody h = some (hexDecrementTransform id h) := by
  unfold hexDecrementTransform
  exact sun_eq_decrement h

def hexCuoTransform (_id : OperatorId) (h : Hexagram) : Hexagram := h.complement

theorem hexCuoTransform_denotes_cuo (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.cuoBody h = some (hexCuoTransform id h) := by
  unfold hexCuoTransform
  exact cuoBody_eq_cuo h

def hexFanReverseTransform (_id : OperatorId) (h : Hexagram) : Hexagram := h.complement

theorem hexFanReverseTransform_denotes_cuo (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.fanReverseBody h = some (hexFanReverseTransform id h) := by
  unfold hexFanReverseTransform
  exact fanReverseBody_eq_cuo h

def hexZongTransform (_id : OperatorId) (h : Hexagram) : Hexagram := h.reverse

theorem hexZongTransform_denotes_zong (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.zongBody h = some (hexZongTransform id h) := by
  unfold hexZongTransform
  exact zongBody_eq_zong h

def hexHuTransform (_id : OperatorId) (h : Hexagram) : Hexagram := h.interlace

theorem hexHuTransform_denotes_hu (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.huBody h = some (hexHuTransform id h) := by
  unfold hexHuTransform
  exact huBody_eq_hu h

def hexCuoZongTransform (_id : OperatorId) (h : Hexagram) : Hexagram := h.complementReverse

theorem hexCuoZongTransform_denotes_cuoZong (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.cuoZongBody h = some (hexCuoZongTransform id h) := by
  unfold hexCuoZongTransform
  exact cuoZongBody_eq_cuoZong h

def hexFlip1Transform (_id : OperatorId) (h : Hexagram) : Hexagram := dongInner h

theorem hexFlip1Transform_denotes_flip1 (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.flip1Body h = some (hexFlip1Transform id h) := by
  unfold hexFlip1Transform
  exact flip1Body_eq_dongInner h

def hexFlip2Transform (_id : OperatorId) (h : Hexagram) : Hexagram := middleFlipInner h

theorem hexFlip2Transform_denotes_flip2 (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.flip2Body h = some (hexFlip2Transform id h) := by
  unfold hexFlip2Transform
  exact flip2Body_eq_huaInner h

def hexFlip3Transform (_id : OperatorId) (h : Hexagram) : Hexagram := topFlipInner h

theorem hexFlip3Transform_denotes_flip3 (id : OperatorId) (h : Hexagram) :
    denoteHexFun Stdlib.flip3Body h = some (hexFlip3Transform id h) := by
  unfold hexFlip3Transform
  exact flip3Body_eq_bianInner h

/-! ## Exact Bool relation and connective laws -/

def boolRelationPredicateOperatorIds : List OperatorId :=
  [.R_1, .R_2, .R_3, .R_4, .R_7, .R_9, .R_10,
   .C_1, .C_3, .F_12, .K_2, .K_3, .K_4, .I_9,
   .P_1, .P_14, .P_15, .P_16, .P_17, .P_20,
   .G_10, .L_4, .Y_20, .Z_4, .Z_14, .Z_15, .Z_40,
   .ZHU_1, .CHU_10, .LIJ_6, .LIJ_9,
   .ZA_15, .ZA_16, .ZA_17, .ZA_18, .ZA_19, .ZA_20]

def hexEqualityLawOperatorIds : List OperatorId :=
  [.R_8, .I_1, .I_3, .I_4, .I_5, .P_4]

def hexDisequalityLawOperatorIds : List OperatorId :=
  [.N_2, .N_7, .P_5]

def boolNegationLawOperatorIds : List OperatorId :=
  [.N_1, .N_3, .N_4, .N_5, .N_6]

def boolImplicationLawOperatorIds : List OperatorId :=
  [.K_1, .S_3, .S_7, .A_4, .Z_1]

def boolConjunctionLawOperatorIds : List OperatorId :=
  [.A_11, .A_12, .A_13]

def boolDiscriminationLawOperatorIds : List OperatorId :=
  [.P_23]

def boolRelationPredicate (_id : OperatorId) (a b : Hexagram) : Bool :=
  decide (a = b)

set_option maxHeartbeats 2000000 in
theorem boolRelationPredicate_denotes_eqHex (id : OperatorId) (a b : Hexagram) :
    denoteHexRel Stdlib.tongBody a b = some (boolRelationPredicate id a b) := by
  unfold boolRelationPredicate
  have hae : a = Hexagram.mk a.y1 a.y2 a.y3 a.y4 a.y5 a.y6 := by apply Hexagram.ext <;> rfl
  have hbe : b = Hexagram.mk b.y1 b.y2 b.y3 b.y4 b.y5 b.y6 := by apply Hexagram.ext <;> rfl
  rw [hae, hbe]
  cases a.y1 <;> cases a.y2 <;> cases a.y3 <;> cases a.y4 <;> cases a.y5 <;> cases a.y6 <;>
  cases b.y1 <;> cases b.y2 <;> cases b.y3 <;> cases b.y4 <;> cases b.y5 <;> cases b.y6 <;>
  native_decide

def hexEqualityLaw (_id : OperatorId) (a b : Hexagram) : Bool :=
  decide (a = b)

set_option maxHeartbeats 2000000 in
theorem hexEqualityLaw_denotes_tong (id : OperatorId) (a b : Hexagram) :
    denoteHexRel Stdlib.tongBody a b = some (hexEqualityLaw id a b) := by
  unfold hexEqualityLaw
  have hae : a = Hexagram.mk a.y1 a.y2 a.y3 a.y4 a.y5 a.y6 := by apply Hexagram.ext <;> rfl
  have hbe : b = Hexagram.mk b.y1 b.y2 b.y3 b.y4 b.y5 b.y6 := by apply Hexagram.ext <;> rfl
  rw [hae, hbe]
  cases a.y1 <;> cases a.y2 <;> cases a.y3 <;> cases a.y4 <;> cases a.y5 <;> cases a.y6 <;>
  cases b.y1 <;> cases b.y2 <;> cases b.y3 <;> cases b.y4 <;> cases b.y5 <;> cases b.y6 <;>
  native_decide

set_option maxHeartbeats 2000000 in
theorem hexEqualityLaw_denotes_bi (id : OperatorId) (a b : Hexagram) :
    denoteHexRel Stdlib.biBody a b = some (hexEqualityLaw id a b) := by
  unfold hexEqualityLaw
  have hae : a = Hexagram.mk a.y1 a.y2 a.y3 a.y4 a.y5 a.y6 := by apply Hexagram.ext <;> rfl
  have hbe : b = Hexagram.mk b.y1 b.y2 b.y3 b.y4 b.y5 b.y6 := by apply Hexagram.ext <;> rfl
  rw [hae, hbe]
  cases a.y1 <;> cases a.y2 <;> cases a.y3 <;> cases a.y4 <;> cases a.y5 <;> cases a.y6 <;>
  cases b.y1 <;> cases b.y2 <;> cases b.y3 <;> cases b.y4 <;> cases b.y5 <;> cases b.y6 <;>
  native_decide

def hexDisequalityLaw (_id : OperatorId) (a b : Hexagram) : Bool :=
  decide (a ≠ b)

set_option maxHeartbeats 2000000 in
theorem hexDisequalityLaw_denotes_neq (id : OperatorId) (a b : Hexagram) :
    denoteHexRel Stdlib.neqHexBody a b = some (hexDisequalityLaw id a b) := by
  unfold hexDisequalityLaw
  have hae : a = Hexagram.mk a.y1 a.y2 a.y3 a.y4 a.y5 a.y6 := by apply Hexagram.ext <;> rfl
  have hbe : b = Hexagram.mk b.y1 b.y2 b.y3 b.y4 b.y5 b.y6 := by apply Hexagram.ext <;> rfl
  rw [hae, hbe]
  cases a.y1 <;> cases a.y2 <;> cases a.y3 <;> cases a.y4 <;> cases a.y5 <;> cases a.y6 <;>
  cases b.y1 <;> cases b.y2 <;> cases b.y3 <;> cases b.y4 <;> cases b.y5 <;> cases b.y6 <;>
  native_decide

def boolNegationLaw (_id : OperatorId) (b : Bool) : Bool := !b

theorem boolNegationLaw_denotes_not (id : OperatorId) (b : Bool) :
    denoteBool (.app Stdlib.buBody (.boolLit b)) = some (boolNegationLaw id b) := by
  unfold boolNegationLaw
  cases b <;> native_decide

def boolImplicationLaw (_id : OperatorId) (p q : Bool) : Bool := (!p) || q

theorem boolImplicationLaw_denotes_imp (id : OperatorId) (p q : Bool) :
    denoteBool (.app (.app Stdlib.impBody (.boolLit p)) (.boolLit q)) =
      some (boolImplicationLaw id p q) := by
  unfold boolImplicationLaw
  cases p <;> cases q <;> native_decide

def boolConjunctionLaw (_id : OperatorId) (p q : Bool) : Bool := p && q

theorem boolConjunctionLaw_denotes_and (id : OperatorId) (p q : Bool) :
    denoteBool (.app (.app .andB (.boolLit p)) (.boolLit q)) =
      some (boolConjunctionLaw id p q) := by
  unfold boolConjunctionLaw
  cases p <;> cases q <;> native_decide

def boolDiscriminationLaw (_id : OperatorId) (p q : Bool) : Bool :=
  (p && !q) || (!p && q)

theorem boolDiscriminationLaw_denotes_xor (id : OperatorId) (p q : Bool) :
    denoteBool (.app (.app Stdlib.xorBBody (.boolLit p)) (.boolLit q)) =
      some (boolDiscriminationLaw id p q) := by
  unfold boolDiscriminationLaw
  cases p <;> cases q <;> native_decide

/-! ## Finite quantifier and endomap-control laws -/

def finiteQuantifierLawOperatorIds : List OperatorId :=
  [.Q_1, .Q_2, .Q_4, .Q_5, .Q_6, .Q_7, .Q_8, .D_3, .D_9, .D_10]

def finiteModalPredicateLawOperatorIds : List OperatorId :=
  [.M_1, .M_2]

def contextPredicateApplicationLawOperatorIds : List OperatorId :=
  [.S_15, .S_20]

def endomapControlLawOperatorIds : List OperatorId :=
  [.S_2, .A_5, .A_6, .D_2]

def focusUniqueQuantifierLawOperatorIds : List OperatorId :=
  [.A_14]

def finiteQuantifierLawBodyFor? : OperatorId → Option Tm
  | .Q_1 => some Stdlib.fanBody
  | .Q_2 => some Stdlib.fanBody
  | .Q_4 => some Stdlib.noneHBody
  | .Q_5 => some Stdlib.existsHBody
  | .Q_6 => some Stdlib.existsHBody
  | .Q_7 => some Stdlib.noneHBody
  | .Q_8 => some Stdlib.uniqueHBody
  | .D_3 => some Stdlib.exactly3HBody
  | .D_9 => some Stdlib.fanBody
  | .D_10 => some Stdlib.majorityHBody
  | _ => none

def finiteModalPredicateLawBodyFor? : OperatorId → Option Tm
  | .M_1 => some Stdlib.biModalBody
  | .M_2 => some Stdlib.existsHBody
  | _ => none

def contextPredicateApplicationLawBodyFor? : OperatorId → Option Tm
  | .S_15 => some Stdlib.hexPredApplyBody
  | .S_20 => some Stdlib.hexPredApplyBody
  | _ => none

def endomapControlLawBodyFor? : OperatorId → Option Tm
  | .S_2 => some Stdlib.endoCompBody
  | .A_5 => some Stdlib.repeatOnceBody
  | .A_6 => some Stdlib.repeatOnceBody
  | .D_2 => some Stdlib.repeatOnceBody
  | _ => none

def focusUniqueQuantifierLawBodyFor? : OperatorId → Option Tm
  | .A_14 => some Stdlib.uniqueHBody
  | _ => none

def finiteHexPredicateQuantifierTy : Ty :=
  .arr (.arr .hex .bool) .bool

def hexPredicateApplicationTy : Ty :=
  .arr (.arr .hex .bool) (.arr .hex .bool)

def hexEndomapTy : Ty :=
  .arr .hex .hex

def hexEndomapRepeatTy : Ty :=
  .arr hexEndomapTy hexEndomapTy

def hexEndomapCompositionTy : Ty :=
  .arr hexEndomapTy (.arr hexEndomapTy hexEndomapTy)

theorem finiteQuantifierLawBodies_typed :
    finiteQuantifierLawOperatorIds.all
      (fun id =>
        match finiteQuantifierLawBodyFor? id with
        | some body => decide (typeCheck [] body = some finiteHexPredicateQuantifierTy)
        | none => false) = true := by
  native_decide

theorem finiteModalPredicateLawBodies_typed :
    finiteModalPredicateLawOperatorIds.all
      (fun id =>
        match finiteModalPredicateLawBodyFor? id with
        | some body => decide (typeCheck [] body = some finiteHexPredicateQuantifierTy)
        | none => false) = true := by
  native_decide

theorem contextPredicateApplicationLawBodies_typed :
    contextPredicateApplicationLawOperatorIds.all
      (fun id =>
        match contextPredicateApplicationLawBodyFor? id with
        | some body => decide (typeCheck [] body = some hexPredicateApplicationTy)
        | none => false) = true := by
  native_decide

theorem endomapControlLawBodies_typed :
    endomapControlLawOperatorIds.all
      (fun id =>
        match endomapControlLawBodyFor? id with
        | some body =>
            if decide (id = .S_2) then
              decide (typeCheck [] body = some hexEndomapCompositionTy)
            else
              decide (typeCheck [] body = some hexEndomapRepeatTy)
        | none => false) = true := by
  native_decide

theorem focusUniqueQuantifierLawBodies_typed :
    focusUniqueQuantifierLawOperatorIds.all
      (fun id =>
        match focusUniqueQuantifierLawBodyFor? id with
        | some body => decide (typeCheck [] body = some finiteHexPredicateQuantifierTy)
        | none => false) = true := by
  native_decide

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
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

def predicateAnchorLawOperatorIds : List OperatorId :=
  [.B_8, .G_3, .G_6, .D_5, .D_6, .D_7, .Z_39, .ZA_13, .ZA_14]

def predicateAnchorBody : Tm :=
  .abs "x" .hex (.boolLit true)

def predicateAnchor (_id : OperatorId) (_h : Hexagram) : Bool := true

theorem predicateAnchor_denotes_true (id : OperatorId) (h : Hexagram) :
    denoteBool (.app predicateAnchorBody (.hexLit h)) = some (predicateAnchor id h) := by
  unfold predicateAnchor
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

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
  | .exactHexTransform => exactHexTransformOperatorIds
  | .boolRelationPredicate => boolRelationPredicateOperatorIds
  | .hexEqualityLaw => hexEqualityLawOperatorIds
  | .hexDisequalityLaw => hexDisequalityLawOperatorIds
  | .boolNegationLaw => boolNegationLawOperatorIds
  | .boolImplicationLaw => boolImplicationLawOperatorIds
  | .boolConjunctionLaw => boolConjunctionLawOperatorIds
  | .boolDiscriminationLaw => boolDiscriminationLawOperatorIds
  | .finiteQuantifierLaw => finiteQuantifierLawOperatorIds
  | .finiteModalPredicateLaw => finiteModalPredicateLawOperatorIds
  | .contextPredicateApplicationLaw => contextPredicateApplicationLawOperatorIds
  | .endomapControlLaw => endomapControlLawOperatorIds
  | .focusUniqueQuantifierLaw => focusUniqueQuantifierLawOperatorIds
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
  else if decide (id ∈ exactHexTransformOperatorIds) then
    some .exactHexTransform
  else if decide (id ∈ boolRelationPredicateOperatorIds) then
    some .boolRelationPredicate
  else if decide (id ∈ hexEqualityLawOperatorIds) then
    some .hexEqualityLaw
  else if decide (id ∈ hexDisequalityLawOperatorIds) then
    some .hexDisequalityLaw
  else if decide (id ∈ boolNegationLawOperatorIds) then
    some .boolNegationLaw
  else if decide (id ∈ boolImplicationLawOperatorIds) then
    some .boolImplicationLaw
  else if decide (id ∈ boolConjunctionLawOperatorIds) then
    some .boolConjunctionLaw
  else if decide (id ∈ boolDiscriminationLawOperatorIds) then
    some .boolDiscriminationLaw
  else if decide (id ∈ finiteQuantifierLawOperatorIds) then
    some .finiteQuantifierLaw
  else if decide (id ∈ finiteModalPredicateLawOperatorIds) then
    some .finiteModalPredicateLaw
  else if decide (id ∈ contextPredicateApplicationLawOperatorIds) then
    some .contextPredicateApplicationLaw
  else if decide (id ∈ endomapControlLawOperatorIds) then
    some .endomapControlLaw
  else if decide (id ∈ focusUniqueQuantifierLawOperatorIds) then
    some .focusUniqueQuantifierLaw
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
    allDomainLawKinds.length = 35 := by native_decide

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

theorem exactHexTransformOperatorIds_length :
    exactHexTransformOperatorIds.length = 36 := by native_decide

theorem exactHexTransformOperatorIds_nodup :
    exactHexTransformOperatorIds.Nodup := by native_decide

theorem boolRelationPredicateOperatorIds_length :
    boolRelationPredicateOperatorIds.length = 37 := by native_decide

theorem boolRelationPredicateOperatorIds_nodup :
    boolRelationPredicateOperatorIds.Nodup := by native_decide

theorem hexEqualityLawOperatorIds_length :
    hexEqualityLawOperatorIds.length = 6 := by native_decide

theorem hexEqualityLawOperatorIds_nodup :
    hexEqualityLawOperatorIds.Nodup := by native_decide

theorem hexDisequalityLawOperatorIds_length :
    hexDisequalityLawOperatorIds.length = 3 := by native_decide

theorem hexDisequalityLawOperatorIds_nodup :
    hexDisequalityLawOperatorIds.Nodup := by native_decide

theorem boolNegationLawOperatorIds_length :
    boolNegationLawOperatorIds.length = 5 := by native_decide

theorem boolNegationLawOperatorIds_nodup :
    boolNegationLawOperatorIds.Nodup := by native_decide

theorem boolImplicationLawOperatorIds_length :
    boolImplicationLawOperatorIds.length = 5 := by native_decide

theorem boolImplicationLawOperatorIds_nodup :
    boolImplicationLawOperatorIds.Nodup := by native_decide

theorem boolConjunctionLawOperatorIds_length :
    boolConjunctionLawOperatorIds.length = 3 := by native_decide

theorem boolConjunctionLawOperatorIds_nodup :
    boolConjunctionLawOperatorIds.Nodup := by native_decide

theorem boolDiscriminationLawOperatorIds_length :
    boolDiscriminationLawOperatorIds.length = 1 := by native_decide

theorem finiteQuantifierLawOperatorIds_length :
    finiteQuantifierLawOperatorIds.length = 10 := by native_decide

theorem finiteQuantifierLawOperatorIds_nodup :
    finiteQuantifierLawOperatorIds.Nodup := by native_decide

theorem finiteModalPredicateLawOperatorIds_length :
    finiteModalPredicateLawOperatorIds.length = 2 := by native_decide

theorem finiteModalPredicateLawOperatorIds_nodup :
    finiteModalPredicateLawOperatorIds.Nodup := by native_decide

theorem contextPredicateApplicationLawOperatorIds_length :
    contextPredicateApplicationLawOperatorIds.length = 2 := by native_decide

theorem contextPredicateApplicationLawOperatorIds_nodup :
    contextPredicateApplicationLawOperatorIds.Nodup := by native_decide

theorem endomapControlLawOperatorIds_length :
    endomapControlLawOperatorIds.length = 4 := by native_decide

theorem endomapControlLawOperatorIds_nodup :
    endomapControlLawOperatorIds.Nodup := by native_decide

theorem focusUniqueQuantifierLawOperatorIds_length :
    focusUniqueQuantifierLawOperatorIds.length = 1 := by native_decide

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
    domainLawOperatorIds.length = 364 := by native_decide

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
      + (domainLawKindOperatorIds .exactHexTransform).length
      + (domainLawKindOperatorIds .boolRelationPredicate).length
      + (domainLawKindOperatorIds .hexEqualityLaw).length
      + (domainLawKindOperatorIds .hexDisequalityLaw).length
      + (domainLawKindOperatorIds .boolNegationLaw).length
      + (domainLawKindOperatorIds .boolImplicationLaw).length
      + (domainLawKindOperatorIds .boolConjunctionLaw).length
      + (domainLawKindOperatorIds .boolDiscriminationLaw).length
      + (domainLawKindOperatorIds .finiteQuantifierLaw).length
      + (domainLawKindOperatorIds .finiteModalPredicateLaw).length
      + (domainLawKindOperatorIds .contextPredicateApplicationLaw).length
      + (domainLawKindOperatorIds .endomapControlLaw).length
      + (domainLawKindOperatorIds .focusUniqueQuantifierLaw).length
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
example : operatorDomainLawKind? .T_10 = some .exactHexTransform := by native_decide
example : operatorDomainLawKind? .T_13 = some .exactHexTransform := by native_decide
example : operatorDomainLawKind? .Z_5 = some .exactHexTransform := by native_decide
example : operatorDomainLawKind? .T_1 = some .exactHexTransform := by native_decide
example : operatorDomainLawKind? .R_1 = some .boolRelationPredicate := by native_decide
example : operatorDomainLawKind? .I_1 = some .hexEqualityLaw := by native_decide
example : operatorDomainLawKind? .N_2 = some .hexDisequalityLaw := by native_decide
example : operatorDomainLawKind? .N_1 = some .boolNegationLaw := by native_decide
example : operatorDomainLawKind? .K_1 = some .boolImplicationLaw := by native_decide
example : operatorDomainLawKind? .A_12 = some .boolConjunctionLaw := by native_decide
example : operatorDomainLawKind? .P_23 = some .boolDiscriminationLaw := by native_decide
example : operatorDomainLawKind? .Q_1 = some .finiteQuantifierLaw := by native_decide
example : operatorDomainLawKind? .M_1 = some .finiteModalPredicateLaw := by native_decide
example : operatorDomainLawKind? .S_15 = some .contextPredicateApplicationLaw := by native_decide
example : operatorDomainLawKind? .S_2 = some .endomapControlLaw := by native_decide
example : operatorDomainLawKind? .A_14 = some .focusUniqueQuantifierLaw := by native_decide
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
