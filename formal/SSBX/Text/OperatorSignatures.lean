import SSBX.Text.WenyanOperators

/-!
# OperatorSignatures — conservative signature coverage ledger

This file records text-level signature shapes for catalogue operators.  These
rows are not executable interpretations; they are conservative arity/type-shape
commitments that can later be connected to concrete semantics.

The `exactSignatureSeed` layer remains the small high-value seed set already
used by downstream audits.  The `fullOperatorSignatures` layer gives total
all-396 coverage by applying explicit seed overrides over per-operator
catalogue-shape rows.
-/

namespace SSBX.Text.OperatorSignatures

open SSBX.Text.WenyanOperators

/-- Coarse type-shape of an operator signature, without giving semantics. -/
inductive SignatureKind where
  | app
  | endoComp
  | propImp
  | instrument
  | objectEndo
  | propUnary
  | opUnary
  | relation
  | containment
  | flow
  | boundary
  | quantifier
  | identity
  | syntax
  | concept
  | predicate
  | modifier
  | degree
  | textAct
  | domainRule
  | domainProcess
  | objectMap
  | binaryObject
  | binaryPoint
  | extractor
  | constructor
  | decomposer
  | propConnective
  | binaryModal
  | binder
  | aspect
  | stateProjection
  | stateTransition
  | aggregate
  | assignment
  | query
  | protocol
  | quotient
  | trajectory
  | debind
  | response
  | partition
  | signal
  | binding
  | invariant
  | supervision
  | integration
  | limit
  | dialectic
  | distinction
  deriving Repr, DecidableEq, BEq

/-- A seed exact signature row for one catalogue operator id. -/
structure ExactOperatorSignature where
  id : OperatorId
  kind : SignatureKind
  arity : Nat
  note : String
  deriving Repr, DecidableEq

/-- Conservative first-pass exact signature seeds for high-value operators. -/
def exactSignatureSeed : List ExactOperatorSignature :=
  [ { id := .S_1,  kind := .app,        arity := 2, note := "之: application/projection shape" }
  , { id := .S_2,  kind := .endoComp,   arity := 2, note := "而: endomap sequencing shape" }
  , { id := .K_8,  kind := .instrument, arity := 2, note := "以: instrumental application shape" }
  , { id := .K_1,  kind := .propImp,    arity := 2, note := "故: causal connective shape" }
  , { id := .S_7,  kind := .propImp,    arity := 2, note := "故: therefore connective shape" }
  , { id := .T_6,  kind := .objectEndo, arity := 1, note := "反: object-level reversal shape only" }
  , { id := .N_6,  kind := .propUnary,  arity := 1, note := "反: proposition-level dual/negative shape only" }
  , { id := .Z_31, kind := .opUnary,    arity := 1, note := "反: operator-transformer shape only" }
  , { id := .T_7,  kind := .objectEndo, arity := 1, note := "复/復: return shape only" }
  , { id := .Z_5,  kind := .opUnary,    arity := 1, note := "错/錯: operator/cell transform shape only" }
  , { id := .Z_6,  kind := .opUnary,    arity := 1, note := "综/綜: operator/cell transform shape only" }
  , { id := .Z_3,  kind := .opUnary,    arity := 1, note := "互: mutual-transform shape only" }
  , { id := .T_12, kind := .objectEndo, arity := 1, note := "损/損: decrement/loss shape only" }
  , { id := .T_13, kind := .objectEndo, arity := 1, note := "益: increment/gain shape only" }
  ]

def signedOperatorIds : List OperatorId :=
  exactSignatureSeed.map (·.id)

def signatureFor? (id : OperatorId) : Option ExactOperatorSignature :=
  exactSignatureSeed.find? (fun sig => decide (sig.id = id))

/-! ## Total catalogue coverage by catalogue shapes plus seed overrides -/

/-- Provenance for a total signature row. -/
inductive SignatureEvidence where
  | seedOverride
  | catalogueShape
  deriving Repr, DecidableEq, BEq

/--
A conservative signature row for one catalogue operator.

`evidence = catalogueShape` means a per-operator arity/type shape has been
audited from the catalogue, but it is still not an executable denotation.
-/
structure CoveredOperatorSignature where
  id : OperatorId
  kind : SignatureKind
  arity : Nat
  evidence : SignatureEvidence
  note : String
  deriving Repr, DecidableEq

/-- Per-operator catalogue shape, intentionally weaker than executable semantics. -/
def catalogueSignatureShapeFor : OperatorId → SignatureKind × Nat
  | .R_1 => (.relation, 2)
  | .R_2 => (.relation, 2)
  | .R_3 => (.binaryPoint, 2)
  | .R_4 => (.binaryPoint, 2)
  | .R_5 => (.extractor, 1)
  | .R_6 => (.objectEndo, 1)
  | .R_7 => (.relation, 2)
  | .R_8 => (.relation, 2)
  | .R_9 => (.relation, 2)
  | .R_10 => (.relation, 2)
  | .R_11 => (.objectEndo, 1)
  | .R_12 => (.binaryObject, 2)
  | .R_13 => (.binaryObject, 2)
  | .R_14 => (.binaryObject, 2)
  | .R_15 => (.binaryObject, 2)
  | .R_16 => (.relation, 2)
  | .R_17 => (.relation, 2)
  | .R_18 => (.relation, 2)
  | .R_19 => (.response, 2)
  | .R_20 => (.relation, 2)
  | .C_1 => (.containment, 2)
  | .C_2 => (.binaryObject, 2)
  | .C_3 => (.containment, 2)
  | .C_4 => (.extractor, 1)
  | .C_5 => (.extractor, 1)
  | .C_6 => (.extractor, 1)
  | .C_7 => (.extractor, 1)
  | .C_8 => (.extractor, 1)
  | .T_1 => (.objectMap, 1)
  | .T_2 => (.objectMap, 1)
  | .T_3 => (.binaryObject, 2)
  | .T_4 => (.objectMap, 1)
  | .T_5 => (.objectEndo, 1)
  | .T_6 => (.objectEndo, 1)
  | .T_7 => (.objectEndo, 1)
  | .T_8 => (.objectEndo, 1)
  | .T_9 => (.objectEndo, 1)
  | .T_10 => (.objectEndo, 1)
  | .T_11 => (.binaryObject, 2)
  | .T_12 => (.objectEndo, 1)
  | .T_13 => (.objectEndo, 1)
  | .T_14 => (.objectEndo, 1)
  | .T_15 => (.objectEndo, 1)
  | .T_16 => (.stateTransition, 1)
  | .T_17 => (.stateTransition, 1)
  | .T_18 => (.objectEndo, 1)
  | .T_19 => (.objectEndo, 1)
  | .T_20 => (.objectEndo, 1)
  | .T_21 => (.stateTransition, 1)
  | .T_22 => (.binaryObject, 2)
  | .T_23 => (.objectEndo, 1)
  | .T_24 => (.objectEndo, 1)
  | .T_25 => (.stateTransition, 1)
  | .T_26 => (.response, 1)
  | .F_1 => (.flow, 2)
  | .F_2 => (.flow, 2)
  | .F_3 => (.flow, 1)
  | .F_4 => (.flow, 1)
  | .F_5 => (.flow, 1)
  | .F_6 => (.flow, 1)
  | .F_7 => (.flow, 2)
  | .F_8 => (.flow, 2)
  | .F_9 => (.flow, 1)
  | .F_10 => (.flow, 1)
  | .F_11 => (.flow, 1)
  | .F_12 => (.relation, 2)
  | .F_13 => (.flow, 2)
  | .F_14 => (.flow, 1)
  | .F_15 => (.flow, 2)
  | .F_16 => (.relation, 2)
  | .F_17 => (.flow, 1)
  | .B_1 => (.extractor, 1)
  | .B_2 => (.extractor, 1)
  | .B_3 => (.objectEndo, 1)
  | .B_4 => (.objectEndo, 1)
  | .B_5 => (.objectEndo, 1)
  | .B_6 => (.objectEndo, 1)
  | .B_7 => (.extractor, 1)
  | .B_8 => (.boundary, 1)
  | .Q_1 => (.quantifier, 1)
  | .Q_2 => (.quantifier, 1)
  | .Q_3 => (.quantifier, 2)
  | .Q_4 => (.quantifier, 1)
  | .Q_5 => (.quantifier, 1)
  | .Q_6 => (.quantifier, 1)
  | .Q_7 => (.quantifier, 1)
  | .Q_8 => (.quantifier, 1)
  | .K_1 => (.propImp, 2)
  | .K_2 => (.relation, 2)
  | .K_3 => (.relation, 2)
  | .K_4 => (.relation, 2)
  | .K_5 => (.binaryObject, 2)
  | .K_6 => (.instrument, 2)
  | .K_7 => (.instrument, 2)
  | .K_8 => (.instrument, 2)
  | .M_1 => (.propUnary, 1)
  | .M_2 => (.propUnary, 1)
  | .M_3 => (.binaryModal, 2)
  | .M_4 => (.binaryModal, 2)
  | .M_5 => (.propUnary, 1)
  | .M_6 => (.binaryModal, 2)
  | .M_7 => (.binaryModal, 2)
  | .M_8 => (.propUnary, 1)
  | .M_9 => (.propUnary, 1)
  | .M_10 => (.propUnary, 1)
  | .M_11 => (.binaryModal, 2)
  | .M_12 => (.propUnary, 1)
  | .N_1 => (.propUnary, 1)
  | .N_2 => (.relation, 2)
  | .N_3 => (.propUnary, 1)
  | .N_4 => (.propUnary, 1)
  | .N_5 => (.propUnary, 1)
  | .N_6 => (.propUnary, 1)
  | .N_7 => (.relation, 2)
  | .N_8 => (.binaryObject, 2)
  | .I_1 => (.identity, 2)
  | .I_2 => (.objectEndo, 1)
  | .I_3 => (.identity, 2)
  | .I_4 => (.identity, 2)
  | .I_5 => (.identity, 2)
  | .I_6 => (.objectMap, 1)
  | .I_7 => (.binaryObject, 2)
  | .I_8 => (.objectMap, 1)
  | .I_9 => (.relation, 2)
  | .S_1 => (.app, 2)
  | .S_2 => (.endoComp, 2)
  | .S_3 => (.propImp, 2)
  | .S_4 => (.propUnary, 1)
  | .S_5 => (.propUnary, 1)
  | .S_6 => (.propUnary, 1)
  | .S_7 => (.propImp, 2)
  | .S_8 => (.propUnary, 1)
  | .S_9 => (.aspect, 1)
  | .S_10 => (.aspect, 1)
  | .S_11 => (.aspect, 1)
  | .S_12 => (.aspect, 1)
  | .S_13 => (.binder, 1)
  | .S_14 => (.binder, 1)
  | .S_15 => (.binder, 2)
  | .S_16 => (.binder, 1)
  | .S_17 => (.aspect, 1)
  | .S_18 => (.aspect, 1)
  | .S_19 => (.binder, 2)
  | .S_20 => (.binder, 2)
  | .H_1 => (.extractor, 1)
  | .H_2 => (.extractor, 1)
  | .H_3 => (.extractor, 1)
  | .H_4 => (.extractor, 1)
  | .H_5 => (.constructor, 2)
  | .H_6 => (.extractor, 1)
  | .H_7 => (.assignment, 1)
  | .H_8 => (.decomposer, 1)
  | .P_1 => (.relation, 2)
  | .P_2 => (.extractor, 1)
  | .P_3 => (.aggregate, 1)
  | .P_4 => (.relation, 2)
  | .P_5 => (.relation, 2)
  | .P_6 => (.extractor, 1)
  | .P_7 => (.extractor, 1)
  | .P_8 => (.stateTransition, 2)
  | .P_9 => (.objectEndo, 1)
  | .P_10 => (.extractor, 1)
  | .P_11 => (.constructor, 2)
  | .P_12 => (.extractor, 1)
  | .P_13 => (.constructor, 2)
  | .P_14 => (.relation, 2)
  | .P_15 => (.relation, 2)
  | .P_16 => (.relation, 2)
  | .P_17 => (.relation, 2)
  | .P_18 => (.extractor, 1)
  | .P_19 => (.assignment, 1)
  | .P_20 => (.relation, 2)
  | .P_21 => (.textAct, 1)
  | .P_22 => (.constructor, 2)
  | .P_23 => (.propConnective, 2)
  | .P_24 => (.extractor, 1)
  | .G_1 => (.assignment, 2)
  | .G_2 => (.concept, 1)
  | .G_3 => (.relation, 1)
  | .G_4 => (.concept, 1)
  | .G_5 => (.extractor, 1)
  | .G_6 => (.relation, 1)
  | .G_7 => (.decomposer, 2)
  | .G_8 => (.constructor, 2)
  | .G_9 => (.decomposer, 1)
  | .G_10 => (.predicate, 2)
  | .G_11 => (.assignment, 2)
  | .A_1 => (.aspect, 1)
  | .A_2 => (.aspect, 1)
  | .A_3 => (.aspect, 1)
  | .A_4 => (.propImp, 2)
  | .A_5 => (.aspect, 1)
  | .A_6 => (.aspect, 1)
  | .A_7 => (.aspect, 1)
  | .A_8 => (.modifier, 1)
  | .A_9 => (.modifier, 1)
  | .A_10 => (.aspect, 1)
  | .A_11 => (.propConnective, 2)
  | .A_12 => (.propConnective, 2)
  | .A_13 => (.propConnective, 2)
  | .A_14 => (.modifier, 1)
  | .A_15 => (.modifier, 1)
  | .A_16 => (.aspect, 1)
  | .A_17 => (.aspect, 1)
  | .A_18 => (.aspect, 1)
  | .A_19 => (.aspect, 1)
  | .A_20 => (.aspect, 1)
  | .D_1 => (.objectEndo, 1)
  | .D_2 => (.aspect, 1)
  | .D_3 => (.quantifier, 1)
  | .D_4 => (.decomposer, 1)
  | .D_5 => (.degree, 1)
  | .D_6 => (.degree, 1)
  | .D_7 => (.identity, 1)
  | .D_8 => (.constructor, 2)
  | .D_9 => (.quantifier, 1)
  | .D_10 => (.quantifier, 1)
  | .E_1 => (.textAct, 1)
  | .E_2 => (.textAct, 2)
  | .E_3 => (.assignment, 2)
  | .E_4 => (.textAct, 1)
  | .E_5 => (.textAct, 1)
  | .E_6 => (.textAct, 1)
  | .E_7 => (.textAct, 1)
  | .E_8 => (.textAct, 1)
  | .E_9 => (.textAct, 1)
  | .L_1 => (.domainRule, 2)
  | .L_2 => (.domainProcess, 2)
  | .L_3 => (.extractor, 1)
  | .L_4 => (.relation, 2)
  | .L_5 => (.aggregate, 1)
  | .L_6 => (.stateTransition, 1)
  | .L_7 => (.instrument, 2)
  | .L_8 => (.assignment, 2)
  | .L_9 => (.objectEndo, 1)
  | .L_10 => (.objectEndo, 1)
  | .L_11 => (.domainProcess, 1)
  | .L_12 => (.extractor, 1)
  | .L_13 => (.aggregate, 1)
  | .L_14 => (.constructor, 1)
  | .L_15 => (.extractor, 1)
  | .L_16 => (.stateTransition, 2)
  | .Y_1 => (.decomposer, 1)
  | .Y_2 => (.constructor, 1)
  | .Y_3 => (.objectEndo, 1)
  | .Y_4 => (.objectEndo, 1)
  | .Y_5 => (.objectEndo, 1)
  | .Y_6 => (.stateProjection, 1)
  | .Y_7 => (.stateProjection, 1)
  | .Y_8 => (.stateProjection, 1)
  | .Y_9 => (.aggregate, 1)
  | .Y_10 => (.stateProjection, 1)
  | .Y_11 => (.stateProjection, 1)
  | .Y_12 => (.stateProjection, 1)
  | .Y_13 => (.stateProjection, 1)
  | .Y_14 => (.stateProjection, 1)
  | .Y_15 => (.stateProjection, 1)
  | .Y_16 => (.stateTransition, 2)
  | .Y_17 => (.objectEndo, 1)
  | .Y_18 => (.objectEndo, 1)
  | .Y_19 => (.stateTransition, 2)
  | .Y_20 => (.relation, 2)
  | .Y_21 => (.decomposer, 1)
  | .Y_22 => (.decomposer, 1)
  | .Y_23 => (.stateProjection, 1)
  | .Y_24 => (.stateProjection, 1)
  | .Y_25 => (.stateProjection, 1)
  | .Y_26 => (.stateProjection, 1)
  | .Y_27 => (.query, 1)
  | .Y_28 => (.stateTransition, 2)
  | .X_1 => (.stateProjection, 1)
  | .X_2 => (.stateTransition, 2)
  | .X_3 => (.stateTransition, 1)
  | .X_4 => (.aggregate, 1)
  | .X_5 => (.decomposer, 1)
  | .X_6 => (.constructor, 1)
  | .X_7 => (.domainRule, 2)
  | .X_8 => (.decomposer, 1)
  | .X_9 => (.constructor, 1)
  | .X_10 => (.modifier, 2)
  | .X_11 => (.stateTransition, 3)
  | .X_12 => (.decomposer, 1)
  | .X_13 => (.stateTransition, 2)
  | .X_14 => (.aggregate, 2)
  | .X_15 => (.stateTransition, 2)
  | .X_16 => (.stateTransition, 3)
  | .Z_1 => (.propImp, 2)
  | .Z_2 => (.opUnary, 1)
  | .Z_3 => (.opUnary, 1)
  | .Z_4 => (.relation, 2)
  | .Z_5 => (.opUnary, 1)
  | .Z_6 => (.opUnary, 1)
  | .Z_7 => (.aggregate, 1)
  | .Z_8 => (.objectEndo, 1)
  | .Z_9 => (.objectEndo, 1)
  | .Z_10 => (.stateTransition, 1)
  | .Z_11 => (.stateTransition, 1)
  | .Z_12 => (.objectEndo, 1)
  | .Z_13 => (.objectEndo, 1)
  | .Z_14 => (.relation, 2)
  | .Z_15 => (.relation, 2)
  | .Z_16 => (.aggregate, 1)
  | .Z_17 => (.aggregate, 1)
  | .Z_18 => (.decomposer, 1)
  | .Z_19 => (.aggregate, 2)
  | .Z_20 => (.stateTransition, 2)
  | .Z_21 => (.aggregate, 1)
  | .Z_22 => (.objectEndo, 1)
  | .Z_23 => (.concept, 1)
  | .Z_24 => (.extractor, 1)
  | .Z_25 => (.stateTransition, 2)
  | .Z_26 => (.query, 1)
  | .Z_27 => (.query, 1)
  | .Z_28 => (.stateTransition, 2)
  | .Z_29 => (.opUnary, 2)
  | .Z_30 => (.constructor, 1)
  | .Z_31 => (.opUnary, 1)
  | .Z_32 => (.opUnary, 2)
  | .Z_33 => (.opUnary, 1)
  | .Z_34 => (.query, 1)
  | .Z_35 => (.query, 1)
  | .Z_36 => (.stateTransition, 1)
  | .Z_37 => (.stateTransition, 1)
  | .Z_38 => (.stateTransition, 1)
  | .Z_39 => (.predicate, 1)
  | .Z_40 => (.relation, 2)
  | .ZHU_1 => (.quotient, 2)
  | .ZHU_2 => (.trajectory, 3)
  | .ZHU_3 => (.domainProcess, 2)
  | .ZHU_4 => (.debind, 2)
  | .ZHU_5 => (.debind, 1)
  | .ZHU_6 => (.domainProcess, 2)
  | .ZHU_7 => (.domainProcess, 2)
  | .ZHU_8 => (.partition, 2)
  | .ZHU_9 => (.extractor, 1)
  | .ZHU_10 => (.modifier, 1)
  | .ZHU_11 => (.response, 2)
  | .ZHU_12 => (.debind, 2)
  | .SUN_1 => (.signal, 1)
  | .SUN_2 => (.extractor, 2)
  | .SUN_3 => (.extractor, 1)
  | .SUN_4 => (.extractor, 1)
  | .SUN_5 => (.domainProcess, 1)
  | .SUN_6 => (.domainProcess, 1)
  | .SUN_7 => (.trajectory, 1)
  | .SUN_8 => (.trajectory, 1)
  | .SUN_9 => (.signal, 2)
  | .SUN_10 => (.signal, 2)
  | .SUN_11 => (.domainProcess, 2)
  | .SUN_12 => (.partition, 1)
  | .SUN_13 => (.modifier, 2)
  | .SUN_14 => (.extractor, 2)
  | .CHU_1 => (.response, 2)
  | .CHU_2 => (.trajectory, 3)
  | .CHU_3 => (.trajectory, 2)
  | .CHU_4 => (.extractor, 1)
  | .CHU_5 => (.extractor, 2)
  | .CHU_6 => (.domainProcess, 2)
  | .CHU_7 => (.trajectory, 2)
  | .CHU_8 => (.binding, 2)
  | .CHU_9 => (.aggregate, 1)
  | .CHU_10 => (.invariant, 2)
  | .LIJ_1 => (.protocol, 2)
  | .LIJ_2 => (.protocol, 2)
  | .LIJ_3 => (.textAct, 2)
  | .LIJ_4 => (.extractor, 1)
  | .LIJ_5 => (.protocol, 1)
  | .LIJ_6 => (.boundary, 2)
  | .LIJ_7 => (.extractor, 1)
  | .LIJ_8 => (.domainProcess, 2)
  | .LIJ_9 => (.identity, 2)
  | .LIJ_10 => (.domainRule, 2)
  | .LIJ_11 => (.extractor, 1)
  | .LIJ_12 => (.domainProcess, 2)
  | .LIJ_13 => (.domainRule, 2)
  | .LIJ_14 => (.domainRule, 2)
  | .ZA_1 => (.debind, 2)
  | .ZA_2 => (.objectEndo, 1)
  | .ZA_3 => (.supervision, 1)
  | .ZA_4 => (.partition, 1)
  | .ZA_5 => (.domainProcess, 1)
  | .ZA_6 => (.extractor, 1)
  | .ZA_7 => (.domainRule, 1)
  | .ZA_8 => (.domainRule, 2)
  | .ZA_9 => (.integration, 1)
  | .ZA_10 => (.response, 2)
  | .ZA_11 => (.supervision, 1)
  | .ZA_12 => (.integration, 1)
  | .ZA_13 => (.limit, 1)
  | .ZA_14 => (.limit, 1)
  | .ZA_15 => (.limit, 2)
  | .ZA_16 => (.distinction, 2)
  | .ZA_17 => (.dialectic, 2)
  | .ZA_18 => (.distinction, 2)
  | .ZA_19 => (.distinction, 2)
  | .ZA_20 => (.distinction, 2)

/-- Explanatory note for per-operator catalogue-shape rows. -/
def catalogueSignatureNote (id : OperatorId) : String :=
  "catalogue shape for " ++ id.code ++ " " ++ id.title ++ "; not executable semantics"

/--
Total conservative signature for one operator.  Explicit seed rows override
the per-operator catalogue-shape audit.
-/
def fullSignatureFor (id : OperatorId) : CoveredOperatorSignature :=
  match signatureFor? id with
  | some sig =>
      { id := id, kind := sig.kind, arity := sig.arity,
        evidence := .seedOverride, note := sig.note }
  | none =>
      let shape := catalogueSignatureShapeFor id
      { id := id, kind := shape.1, arity := shape.2,
        evidence := .catalogueShape, note := catalogueSignatureNote id }

/-- Total all-396 signature coverage layer. -/
def fullOperatorSignatures : List CoveredOperatorSignature :=
  allOperatorIds.map fullSignatureFor

def fullSignatureOperatorIds : List OperatorId :=
  fullOperatorSignatures.map (·.id)

def fullSignatureFor? (id : OperatorId) : Option CoveredOperatorSignature :=
  fullOperatorSignatures.find? (fun sig => decide (sig.id = id))

def seedOverrideSignatureRows : List CoveredOperatorSignature :=
  fullOperatorSignatures.filter (fun sig => sig.evidence == SignatureEvidence.seedOverride)

def catalogueShapeSignatureRows : List CoveredOperatorSignature :=
  fullOperatorSignatures.filter (fun sig => sig.evidence == SignatureEvidence.catalogueShape)

theorem exactSignatureSeed_length :
    exactSignatureSeed.length = 14 := by
  native_decide

theorem signedOperatorIds_nodup :
    signedOperatorIds.Nodup := by
  native_decide

theorem exactSignatureSeed_catalogue_members :
    exactSignatureSeed.all (fun sig => decide (sig.id ∈ allOperatorIds)) = true := by
  native_decide

theorem exactSignatureSeed_arities_positive :
    exactSignatureSeed.all (fun sig => decide (0 < sig.arity)) = true := by
  native_decide

theorem signatureFor?_S_1 :
    (signatureFor? .S_1).map (·.kind) = some SignatureKind.app
      ∧ (signatureFor? .S_1).map (·.arity) = some 2 := by
  native_decide

theorem signatureFor?_T_6 :
    (signatureFor? .T_6).map (·.kind) = some SignatureKind.objectEndo
      ∧ (signatureFor? .T_6).map (·.arity) = some 1 := by
  native_decide

theorem signatureFor?_Z_5 :
    (signatureFor? .Z_5).map (·.kind) = some SignatureKind.opUnary
      ∧ (signatureFor? .Z_5).map (·.arity) = some 1 := by
  native_decide

theorem catalogueSignatureShapeFor_arities_positive :
    allOperatorIds.all (fun id => decide (0 < (catalogueSignatureShapeFor id).2)) = true := by
  native_decide

theorem fullOperatorSignatures_length :
    fullOperatorSignatures.length = 396 := by
  native_decide

theorem fullSignatureOperatorIds_eq :
    fullSignatureOperatorIds = allOperatorIds := by
  native_decide

theorem fullSignatureOperatorIds_nodup :
    fullSignatureOperatorIds.Nodup := by
  native_decide

theorem fullOperatorSignatures_catalogue_members :
    fullOperatorSignatures.all (fun sig => decide (sig.id ∈ allOperatorIds)) = true := by
  native_decide

theorem fullOperatorSignatures_arities_positive :
    fullOperatorSignatures.all (fun sig => decide (0 < sig.arity)) = true := by
  native_decide

theorem seedOverrideSignatureRows_length :
    seedOverrideSignatureRows.length = 14 := by
  native_decide

theorem catalogueShapeSignatureRows_length :
    catalogueShapeSignatureRows.length = 382 := by
  native_decide

theorem fullSignatureFor_id (id : OperatorId) :
    (fullSignatureFor id).id = id := by
  cases id <;> native_decide

theorem fullSignatureFor?_complete (id : OperatorId) :
    (fullSignatureFor? id).isSome = true := by
  cases id <;> native_decide

theorem fullSignatureFor_S_1_seed :
    (fullSignatureFor .S_1).evidence = SignatureEvidence.seedOverride
      ∧ (fullSignatureFor .S_1).kind = SignatureKind.app
      ∧ (fullSignatureFor .S_1).arity = 2 := by
  native_decide

theorem fullSignatureFor_R_1_catalogueShape :
    (fullSignatureFor .R_1).evidence = SignatureEvidence.catalogueShape
      ∧ (fullSignatureFor .R_1).kind = SignatureKind.relation
      ∧ (fullSignatureFor .R_1).arity = 2 := by
  native_decide

theorem fullOperatorSignatureCoverage_summary :
    fullOperatorSignatures.length = 396
    ∧ fullSignatureOperatorIds = allOperatorIds
    ∧ fullSignatureOperatorIds.Nodup
    ∧ fullOperatorSignatures.all (fun sig => decide (sig.id ∈ allOperatorIds)) = true
    ∧ fullOperatorSignatures.all (fun sig => decide (0 < sig.arity)) = true
    ∧ seedOverrideSignatureRows.length = 14
    ∧ catalogueShapeSignatureRows.length = 382
    ∧ (∀ id : OperatorId, (fullSignatureFor id).id = id) := by
  exact
    ⟨ fullOperatorSignatures_length
    , fullSignatureOperatorIds_eq
    , fullSignatureOperatorIds_nodup
    , fullOperatorSignatures_catalogue_members
    , fullOperatorSignatures_arities_positive
    , seedOverrideSignatureRows_length
    , catalogueShapeSignatureRows_length
    , fullSignatureFor_id
    ⟩

end SSBX.Text.OperatorSignatures
