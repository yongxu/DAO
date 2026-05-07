import SSBX.Text.WenyanOperators

/-!
# OperatorSignatures — conservative signature coverage ledger

This file records text-level signature shapes for catalogue operators.  These
rows are not executable interpretations; they are conservative arity/type-shape
commitments that can later be connected to concrete semantics.

The `exactSignatureSeed` layer remains the small high-value seed set already
used by downstream audits.  The `fullOperatorSignatures` layer gives total
all-371 coverage by applying explicit seed overrides over honest group-level
defaults.
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

/-! ## Total catalogue coverage by group defaults plus seed overrides -/

/-- Provenance for a total signature row. -/
inductive SignatureEvidence where
  | seedOverride
  | groupDefault
  deriving Repr, DecidableEq, BEq

/--
A conservative signature row for one catalogue operator.

`evidence = groupDefault` means only the group-level arity/type shape is known
here.  It is not an executable denotation and should not be read as one.
-/
structure CoveredOperatorSignature where
  id : OperatorId
  kind : SignatureKind
  arity : Nat
  evidence : SignatureEvidence
  note : String
  deriving Repr, DecidableEq

/-- Group-level default type shape, used only when no explicit seed exists. -/
def defaultSignatureKindForGroup : OperatorGroup → SignatureKind
  | .R => .relation
  | .C => .containment
  | .T => .objectEndo
  | .F => .flow
  | .B => .boundary
  | .Q => .quantifier
  | .K => .propImp
  | .M => .propUnary
  | .N => .propUnary
  | .I => .identity
  | .S => .syntax
  | .H => .concept
  | .P => .predicate
  | .G => .relation
  | .A => .modifier
  | .D => .degree
  | .E => .textAct
  | .L => .domainRule
  | .Y => .domainProcess
  | .X => .domainRule
  | .Z => .opUnary
  | .ZHU => .domainProcess
  | .SUN => .domainProcess
  | .CHU => .domainProcess
  | .LIJ => .domainRule
  | .ZA => .concept

/-- Group-level default arity, used only when no explicit seed exists. -/
def defaultSignatureArityForGroup : OperatorGroup → Nat
  | .R => 2
  | .C => 2
  | .T => 1
  | .F => 1
  | .B => 1
  | .Q => 1
  | .K => 2
  | .M => 1
  | .N => 1
  | .I => 2
  | .S => 2
  | .H => 1
  | .P => 1
  | .G => 2
  | .A => 1
  | .D => 1
  | .E => 2
  | .L => 1
  | .Y => 2
  | .X => 1
  | .Z => 1
  | .ZHU => 1
  | .SUN => 1
  | .CHU => 1
  | .LIJ => 1
  | .ZA => 1

/-- Explanatory note for group-default rows. -/
def defaultSignatureNoteForGroup (g : OperatorGroup) : String :=
  "group default signature shape for " ++ reprStr g ++ "; not executable semantics"

/--
Total conservative signature for one operator.  Explicit seed rows override
group defaults; every other row is clearly marked as a group default.
-/
def fullSignatureFor (id : OperatorId) : CoveredOperatorSignature :=
  match signatureFor? id with
  | some sig =>
      { id := id, kind := sig.kind, arity := sig.arity,
        evidence := .seedOverride, note := sig.note }
  | none =>
      let g := id.group
      { id := id, kind := defaultSignatureKindForGroup g,
        arity := defaultSignatureArityForGroup g,
        evidence := .groupDefault, note := defaultSignatureNoteForGroup g }

/-- Total all-371 signature coverage layer. -/
def fullOperatorSignatures : List CoveredOperatorSignature :=
  allOperatorIds.map fullSignatureFor

def fullSignatureOperatorIds : List OperatorId :=
  fullOperatorSignatures.map (·.id)

def fullSignatureFor? (id : OperatorId) : Option CoveredOperatorSignature :=
  fullOperatorSignatures.find? (fun sig => decide (sig.id = id))

def seedOverrideSignatureRows : List CoveredOperatorSignature :=
  fullOperatorSignatures.filter (fun sig => sig.evidence == SignatureEvidence.seedOverride)

def groupDefaultSignatureRows : List CoveredOperatorSignature :=
  fullOperatorSignatures.filter (fun sig => sig.evidence == SignatureEvidence.groupDefault)

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

theorem defaultSignatureArities_positive :
    [ OperatorGroup.R, .C, .T, .F, .B, .Q, .K, .M, .N, .I, .S, .H, .P,
      .G, .A, .D, .E, .L, .Y, .X, .Z, .ZHU, .SUN, .CHU, .LIJ, .ZA ].all
        (fun g => decide (0 < defaultSignatureArityForGroup g)) = true := by
  native_decide

theorem fullOperatorSignatures_length :
    fullOperatorSignatures.length = 371 := by
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

theorem groupDefaultSignatureRows_length :
    groupDefaultSignatureRows.length = 357 := by
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

theorem fullSignatureFor_R_1_default :
    (fullSignatureFor .R_1).evidence = SignatureEvidence.groupDefault
      ∧ (fullSignatureFor .R_1).kind = SignatureKind.relation
      ∧ (fullSignatureFor .R_1).arity = 2 := by
  native_decide

theorem fullOperatorSignatureCoverage_summary :
    fullOperatorSignatures.length = 371
    ∧ fullSignatureOperatorIds = allOperatorIds
    ∧ fullSignatureOperatorIds.Nodup
    ∧ fullOperatorSignatures.all (fun sig => decide (sig.id ∈ allOperatorIds)) = true
    ∧ fullOperatorSignatures.all (fun sig => decide (0 < sig.arity)) = true
    ∧ seedOverrideSignatureRows.length = 14
    ∧ groupDefaultSignatureRows.length = 357
    ∧ (∀ id : OperatorId, (fullSignatureFor id).id = id) := by
  exact
    ⟨ fullOperatorSignatures_length
    , fullSignatureOperatorIds_eq
    , fullSignatureOperatorIds_nodup
    , fullOperatorSignatures_catalogue_members
    , fullOperatorSignatures_arities_positive
    , seedOverrideSignatureRows_length
    , groupDefaultSignatureRows_length
    , fullSignatureFor_id
    ⟩

end SSBX.Text.OperatorSignatures
