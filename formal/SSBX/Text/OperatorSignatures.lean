import SSBX.Text.WenyanOperators

/-!
# OperatorSignatures — seed exact signature ledger

This file records text-level signature shapes for a small high-value subset of
operators.  These rows are not executable interpretations; they are conservative
arity/type-shape commitments that can later be connected to concrete semantics.
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

end SSBX.Text.OperatorSignatures
