/-
# WenSurface.Semantics — executable semantics registry

This module separates catalogue/signature coverage from executable denotation.
Every `OperatorId` can be described by the text catalogue, but only rows with
theorem-backed `WenDef.Tm` bodies are allowed to run.
-/
import SSBX.Foundation.Wen.WenDef
import SSBX.Text.OperatorSignatures
import SSBX.Text.WenyanOperators

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Wen.WenDef
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorSignatures

/-! ## § 1 Executable registry -/

/-- A denotation that can be elaborated into `WenDef.Tm`. -/
structure ExecutableSemantics where
  id : OperatorId
  body : Tm
  arity : Nat
  note : String
deriving Repr, DecidableEq

/-- Public registry API: catalogue operator id → executable denotation, if any. -/
abbrev OperatorSemanticsRegistry := OperatorId → Option ExecutableSemantics

/--
Executable operator registry.  Anything not listed here may still be known to
the catalogue, but it must not be evaluated by the surface interpreter.
-/
def executableSemanticsFor? : OperatorSemanticsRegistry
  | .T_10 => some ⟨.T_10, Stdlib.tuiBody, 1, "推: Hex increment / 生"⟩
  | .R_8  => some ⟨.R_8,  Stdlib.biBody, 2, "比: current v1 equality approximation"⟩
  | .N_1  => some ⟨.N_1,  Stdlib.buBody, 1, "不: Bool negation"⟩
  | .M_1  => some ⟨.M_1,  Stdlib.biModalBody, 1, "必: finite forall over Hex"⟩
  | .I_1  => some ⟨.I_1,  Stdlib.tongBody, 2, "同: Hex equality"⟩
  | .Q_1  => some ⟨.Q_1,  Stdlib.fanBody, 1, "凡: finite forall over Hex"⟩
  | .T_12 => some ⟨.T_12, Stdlib.sunBody, 1, "損/损: mod-64 decrement"⟩
  | .T_13 => some ⟨.T_13, Stdlib.yiBenefitBody, 1, "益: mod-64 increment"⟩
  | .Z_5  => some ⟨.Z_5,  Stdlib.cuoBody, 1, "错/錯: Hexagram.cuo"⟩
  | .Z_6  => some ⟨.Z_6,  Stdlib.zongBody, 1, "综/綜: Hexagram.zong"⟩
  | .Z_3  => some ⟨.Z_3,  Stdlib.huBody, 1, "互: Hexagram.hu"⟩
  | .T_6  => some ⟨.T_6,  Stdlib.fanReverseBody, 1, "反: object-level reversal as cuo"⟩
  | _     => none

/-- Default theorem-backed execution registry used by WenSurface. -/
def operatorSemanticsRegistry : OperatorSemanticsRegistry :=
  executableSemanticsFor?

def executableOperatorIds : List OperatorId :=
  [.T_10, .R_8, .N_1, .M_1, .I_1, .Q_1, .T_12, .T_13, .Z_5, .Z_6, .Z_3, .T_6]

def isExecutableOperator (id : OperatorId) : Bool :=
  (executableSemanticsFor? id).isSome

/-- Arity for parsing: executable registry first, total catalogue signatures as fallback. -/
def parseArityFor (id : OperatorId) : Nat :=
  match executableSemanticsFor? id with
  | some sem => sem.arity
  | none     => (fullSignatureFor id).arity

/-- Whether an operator is registered in the total catalogue. -/
def isCatalogueOperator (id : OperatorId) : Bool :=
  decide (id ∈ allOperatorIds)

/-! ## § 2 Total registry view -/

/--
One registry row for a catalogue operator.  `signature` is total for all 371
operator ids; `executable?` is present only for theorem-backed denotations.
-/
structure OperatorRegistryEntry where
  id : OperatorId
  signature : CoveredOperatorSignature
  executable? : Option ExecutableSemantics
deriving Repr, DecidableEq

def operatorRegistryEntryFor (id : OperatorId) : OperatorRegistryEntry :=
  { id := id, signature := fullSignatureFor id, executable? := executableSemanticsFor? id }

def operatorRegistryEntries : List OperatorRegistryEntry :=
  allOperatorIds.map operatorRegistryEntryFor

def executableRegistryEntries : List OperatorRegistryEntry :=
  operatorRegistryEntries.filter (fun entry => entry.executable?.isSome)

theorem executableOperatorIds_length :
    executableOperatorIds.length = 12 := by native_decide

theorem executableOperatorIds_registered :
    executableOperatorIds.all isCatalogueOperator = true := by native_decide

theorem operatorRegistryEntries_length :
    operatorRegistryEntries.length = 371 := by
  native_decide

theorem operatorRegistryEntryFor_id (id : OperatorId) :
    (operatorRegistryEntryFor id).id = id := rfl

theorem operatorRegistryEntryFor_signature_id (id : OperatorId) :
    (operatorRegistryEntryFor id).signature.id = id := by
  exact fullSignatureFor_id id

theorem executableRegistryEntries_length :
    executableRegistryEntries.length = 12 := by native_decide

theorem operatorRegistryCoverage_summary :
    operatorRegistryEntries.length = 371
      ∧ executableRegistryEntries.length = 12
      ∧ executableOperatorIds.length = 12
      ∧ executableOperatorIds.all isCatalogueOperator = true
      ∧ (∀ id : OperatorId, (operatorRegistryEntryFor id).id = id)
      ∧ (∀ id : OperatorId, (operatorRegistryEntryFor id).signature.id = id) := by
  exact
    ⟨ operatorRegistryEntries_length
    , executableRegistryEntries_length
    , executableOperatorIds_length
    , executableOperatorIds_registered
    , operatorRegistryEntryFor_id
    , operatorRegistryEntryFor_signature_id
    ⟩

example : (executableSemanticsFor? .Z_5).isSome = true := by native_decide
example : (executableSemanticsFor? .S_1).isSome = false := by native_decide
example : (operatorSemanticsRegistry .T_10).isSome = true := by native_decide
example : parseArityFor .S_1 = 2 := by native_decide

end SSBX.Foundation.Wen.WenSurface
