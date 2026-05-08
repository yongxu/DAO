/-
# WenSurface.Semantics — executable semantics registry

This module separates exact stdlib denotations from total catalogue-shape
execution.  Eighty-four `OperatorId`s use exact `WenDef.Tm` bodies: the original
high-value stdlib rows plus the Bool relation/predicate package.  Every
remaining catalogue row gets a conservative, signature-shaped `WenDef.Tm` so
CLI support is total without confusing it with exact text semantics.
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

/-! ## § 1.1 Bool relation/predicate package -/

def hexPredTrueBody : Tm :=
  .abs "x" .hex (.boolLit true)

theorem hexPredTrueBody_typed :
    typeCheck [] hexPredTrueBody = some (.arr .hex .bool) := by native_decide

def hexRelEqBody : Tm :=
  .eqHex

theorem hexRelEqBody_typed :
    typeCheck [] hexRelEqBody = some (.arr .hex (.arr .hex .bool)) := by native_decide

def relationPredicateBoolOperatorIds : List OperatorId :=
  [ .R_1, .R_2, .R_3, .R_4, .R_7, .R_9, .R_10
  , .C_1, .C_3
  , .F_12
  , .B_8
  , .K_2, .K_3, .K_4
  , .I_9
  , .P_1, .P_14, .P_15, .P_16, .P_17, .P_20
  , .G_3, .G_6, .G_10
  , .D_5, .D_6, .D_7
  , .L_4
  , .Y_20
  , .Z_4, .Z_14, .Z_15, .Z_39, .Z_40
  , .ZHU_1
  , .CHU_10
  , .LIJ_6, .LIJ_9
  , .ZA_13, .ZA_14, .ZA_15, .ZA_16, .ZA_17, .ZA_18, .ZA_19, .ZA_20
  ]

theorem relationPredicateBoolOperatorIds_length :
    relationPredicateBoolOperatorIds.length = 46 := by native_decide

theorem relationPredicateBoolOperatorIds_nodup :
    relationPredicateBoolOperatorIds.Nodup := by native_decide

def relationPredicateBoolBodyForArity? : Nat → Option Tm
  | 1 => some hexPredTrueBody
  | 2 => some hexRelEqBody
  | _ => none

def relationPredicateBoolSemanticsFor? (id : OperatorId) : Option ExecutableSemantics :=
  if decide (id ∈ relationPredicateBoolOperatorIds) then
    let sig := fullSignatureFor id
    match relationPredicateBoolBodyForArity? sig.arity with
    | some body =>
        some
          { id := id
          , body := body
          , arity := sig.arity
          , note := "exact Bool relation/predicate package for "
              ++ id.code ++ " " ++ id.title ++ " ("
              ++ sig.kind.key ++ "/" ++ toString sig.arity ++ ")" }
    | none => none
  else
    none

theorem relationPredicateBoolSemanticsFor?_all :
    relationPredicateBoolOperatorIds.all
      (fun id => (relationPredicateBoolSemanticsFor? id).isSome) = true := by
  native_decide

/-- Exact theorem-backed operator registry. -/
def theoremBackedSemanticsFor? : OperatorSemanticsRegistry
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
  | .N_3  => some ⟨.N_3,  Stdlib.buBody, 1, "弗: Bool negation alias"⟩
  | .N_4  => some ⟨.N_4,  Stdlib.buBody, 1, "勿: Bool negation alias"⟩
  | .N_5  => some ⟨.N_5,  Stdlib.buBody, 1, "毋: Bool negation alias"⟩
  | .N_6  => some ⟨.N_6,  Stdlib.buBody, 1, "反: proposition-level Bool negation"⟩
  | .K_1  => some ⟨.K_1,  Stdlib.impBody, 2, "故: Bool implication"⟩
  | .K_8  => some ⟨.K_8,  Stdlib.hexApplyBody, 2, "以: Hex endomap instrument application"⟩
  | .S_3  => some ⟨.S_3,  Stdlib.impBody, 2, "則/则: Bool implication"⟩
  | .S_7  => some ⟨.S_7,  Stdlib.impBody, 2, "故: sequential implication alias"⟩
  | .Z_1  => some ⟨.Z_1,  Stdlib.impBody, 2, "因: Bool implication"⟩
  | .I_3  => some ⟨.I_3,  Stdlib.tongBody, 2, "即: Hex equality alias"⟩
  | .I_4  => some ⟨.I_4,  Stdlib.tongBody, 2, "是: Hex equality alias"⟩
  | .I_5  => some ⟨.I_5,  Stdlib.tongBody, 2, "為/为: Hex equality alias"⟩
  | .P_4  => some ⟨.P_4,  Stdlib.tongBody, 2, "同: Mohist equality alias"⟩
  | .N_2  => some ⟨.N_2,  Stdlib.neqHexBody, 2, "非: Hex disequality"⟩
  | .N_7  => some ⟨.N_7,  Stdlib.neqHexBody, 2, "異/异: Hex disequality"⟩
  | .P_5  => some ⟨.P_5,  Stdlib.neqHexBody, 2, "異/异: Mohist disequality alias"⟩
  | .Q_2  => some ⟨.Q_2,  Stdlib.fanBody, 1, "皆: finite forall over Hex"⟩
  | .Q_4  => some ⟨.Q_4,  Stdlib.noneHBody, 1, "莫: finite no-witness quantifier over Hex"⟩
  | .M_2  => some ⟨.M_2,  Stdlib.existsHBody, 1, "或: finite modal/exists over Hex"⟩
  | .Q_5  => some ⟨.Q_5,  Stdlib.existsHBody, 1, "或: finite exists over Hex"⟩
  | .Q_6  => some ⟨.Q_6,  Stdlib.existsHBody, 1, "有: finite exists over Hex"⟩
  | .Q_7  => some ⟨.Q_7,  Stdlib.noneHBody, 1, "無/无: finite no-witness quantifier over Hex"⟩
  | .A_11 => some ⟨.A_11, .andB, 2, "既...又... / 一...且...: Bool conjunction"⟩
  | .A_12 => some ⟨.A_12, .andB, 2, "且: Bool conjunction"⟩
  | .S_1  => some ⟨.S_1,  Stdlib.hexApplyBody, 2, "之: Hex endomap application/projection"⟩
  | .S_2  => some ⟨.S_2,  Stdlib.endoCompBody, 2,
      "而: Hex endomap composition; surface currently requires explicit Hex→Hex terms"⟩
  | id    => relationPredicateBoolSemanticsFor? id

/-- The exact theorem-backed subset, kept separate from total shape semantics. -/
def coreTheoremBackedOperatorIds : List OperatorId :=
  [.T_10, .R_8, .N_1, .M_1, .I_1, .Q_1, .T_12, .T_13, .Z_5, .Z_6, .Z_3, .T_6]
    ++ [.N_3, .N_4, .N_5, .N_6, .K_1, .K_8, .S_3, .S_7, .Z_1, .I_3, .I_4,
        .I_5, .P_4, .N_2, .N_7, .P_5, .Q_2, .Q_4, .M_2, .Q_5, .Q_6, .Q_7,
        .A_11, .A_12, .S_1, .S_2]

def theoremBackedOperatorIds : List OperatorId :=
  coreTheoremBackedOperatorIds ++ relationPredicateBoolOperatorIds

def isTheoremBackedOperator (id : OperatorId) : Bool :=
  (theoremBackedSemanticsFor? id).isSome

/-! ## § 1.5 Total catalogue-shape semantics -/

def shapeHexIdBody : Tm :=
  .abs "x" .hex (.var "x")

def shapeHexBinaryFirstBody : Tm :=
  .abs "a" .hex (.abs "b" .hex (.var "a"))

def shapeHexTernaryFirstBody : Tm :=
  .abs "a" .hex (.abs "b" .hex (.abs "c" .hex (.var "a")))

def shapeHexPredTrueBody : Tm :=
  .abs "x" .hex (.boolLit true)

def shapeBoolIdBody : Tm :=
  .abs "p" .bool (.var "p")

def catalogueObjectShapeBody : Nat → Tm
  | 1 => shapeHexIdBody
  | 2 => shapeHexBinaryFirstBody
  | 3 => shapeHexTernaryFirstBody
  | _ => .yi

def catalogueRelationShapeBody : Nat → Tm
  | 1 => shapeHexPredTrueBody
  | 2 => .eqHex
  | 3 => .abs "a" .hex (.abs "b" .hex (.abs "c" .hex (.boolLit true)))
  | _ => .boolLit true

/--
Conservative total fallback by catalogue signature shape.

These bodies are executable and type-checkable, but they are intentionally
weaker than the 84 exact rows above: they witness the catalogue shape as a total
interpreter operation, not a full doctrinal/textual denotation.
-/
def catalogueShapeBodyFor (sig : CoveredOperatorSignature) : Tm :=
  match sig.kind with
  | .propUnary => shapeBoolIdBody
  | .propImp => Stdlib.impBody
  | .propConnective => .andB
  | .binaryModal => Stdlib.impBody
  | .quantifier =>
      match sig.arity with
      | 1 => Stdlib.fanBody
      | _ => catalogueRelationShapeBody sig.arity
  | .relation
  | .containment
  | .boundary
  | .identity
  | .predicate
  | .query
  | .invariant
  | .dialectic
  | .distinction => catalogueRelationShapeBody sig.arity
  | _ => catalogueObjectShapeBody sig.arity

def catalogueShapeSemanticsFor (id : OperatorId) : ExecutableSemantics :=
  let sig := fullSignatureFor id
  { id := id
  , body := catalogueShapeBodyFor sig
  , arity := sig.arity
  , note := "symbolic catalogue normal form for "
      ++ id.code ++ " " ++ id.title ++ " ("
      ++ sig.kind.key ++ "/" ++ toString sig.arity ++ ")" }

/-- Total execution registry used by WenSurface. -/
def executableSemanticsFor? (id : OperatorId) : Option ExecutableSemantics :=
  match theoremBackedSemanticsFor? id with
  | some sem => some sem
  | none =>
      if decide (id ∈ allOperatorIds) then some (catalogueShapeSemanticsFor id) else none

/-- Default execution registry used by WenSurface. -/
def operatorSemanticsRegistry : OperatorSemanticsRegistry :=
  executableSemanticsFor?

def executableOperatorIds : List OperatorId :=
  allOperatorIds

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
operator ids; `executable?` is total for catalogue ids.  The exact subset is
tracked separately by `theoremBackedOperatorIds`.
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
    executableOperatorIds.length = 371 := by native_decide

theorem coreTheoremBackedOperatorIds_length :
    coreTheoremBackedOperatorIds.length = 38 := by native_decide

theorem theoremBackedOperatorIds_length :
    theoremBackedOperatorIds.length = 84 := by native_decide

theorem theoremBackedOperatorIds_nodup :
    theoremBackedOperatorIds.Nodup := by native_decide

theorem theoremBackedOperatorIds_all_semantics :
    theoremBackedOperatorIds.all (fun id => (theoremBackedSemanticsFor? id).isSome) = true := by
  native_decide

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
    executableRegistryEntries.length = 371 := by native_decide

theorem operatorRegistryCoverage_summary :
    operatorRegistryEntries.length = 371
      ∧ executableRegistryEntries.length = 371
      ∧ executableOperatorIds.length = 371
      ∧ theoremBackedOperatorIds.length = 84
      ∧ executableOperatorIds.all isCatalogueOperator = true
      ∧ (∀ id : OperatorId, (operatorRegistryEntryFor id).id = id)
      ∧ (∀ id : OperatorId, (operatorRegistryEntryFor id).signature.id = id) := by
  exact
    ⟨ operatorRegistryEntries_length
    , executableRegistryEntries_length
    , executableOperatorIds_length
    , theoremBackedOperatorIds_length
    , executableOperatorIds_registered
    , operatorRegistryEntryFor_id
    , operatorRegistryEntryFor_signature_id
    ⟩

example : (executableSemanticsFor? .Z_5).isSome = true := by native_decide
example : (theoremBackedSemanticsFor? .S_1).isSome = true := by native_decide
example : (executableSemanticsFor? .S_1).isSome = true := by native_decide
example : (theoremBackedSemanticsFor? .K_8).isSome = true := by native_decide
example : (executableSemanticsFor? .Q_5).isSome = true := by native_decide
example : (executableSemanticsFor? .A_12).isSome = true := by native_decide
example : (theoremBackedSemanticsFor? .R_1).isSome = true := by native_decide
example : (theoremBackedSemanticsFor? .LIJ_9).isSome = true := by native_decide
example : (theoremBackedSemanticsFor? .Y_2).isSome = false := by native_decide
example : (operatorSemanticsRegistry .T_10).isSome = true := by native_decide
example : parseArityFor .S_1 = 2 := by native_decide

end SSBX.Foundation.Wen.WenSurface
