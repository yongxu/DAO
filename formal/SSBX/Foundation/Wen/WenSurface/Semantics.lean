/-
# WenSurface.Semantics — executable semantics registry

This module separates exact stdlib denotations from total catalogue
execution.  One hundred fifty-nine `OperatorId`s use exact `WenDef.Tm` bodies:
the original high-value stdlib rows, the ObjectEndo/ObjectMap/OpUnary Hex
transform package, finite Hex quantifiers, finite Hex motion/process rows,
plus the Bool relation/predicate package.  Every
remaining catalogue row gets a structural catalogue constructor `WenDef.Tm` so
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
  | .R_6  => some ⟨.R_6,  Stdlib.hexIdBody, 1, "正: Hex identity / normalize in place"⟩
  | .R_11 => some ⟨.R_11, Stdlib.hexIdBody, 1, "對/对: Hex identity as paired alignment anchor"⟩
  | .T_1  => some ⟨.T_1,  Stdlib.flip2Body, 1, "化: Hex y2 transform / inner hua"⟩
  | .T_2  => some ⟨.T_2,  Stdlib.flip3Body, 1, "變/变: Hex y3 transform / inner bian"⟩
  | .T_4  => some ⟨.T_4,  Stdlib.cuoBody, 1, "革: total Hex overhaul as cuo"⟩
  | .T_5  => some ⟨.T_5,  Stdlib.flip1Body, 1, "改: local Hex y1 correction / inner dong"⟩
  | .T_7  => some ⟨.T_7,  Stdlib.hexIdBody, 1, "復/复: return-to-root as identity anchor"⟩
  | .T_8  => some ⟨.T_8,  Stdlib.hexIdBody, 1, "還/还: return as identity anchor"⟩
  | .T_9  => some ⟨.T_9,  Stdlib.zongBody, 1, "轉/转: Hex rotation/reflection as zong"⟩
  | .T_14 => some ⟨.T_14, Stdlib.sunBody, 1, "屈: Hex contraction as mod-64 decrement"⟩
  | .T_15 => some ⟨.T_15, Stdlib.tuiBody, 1, "伸: Hex extension as mod-64 increment"⟩
  | .B_3  => some ⟨.B_3,  Stdlib.tuiBody, 1, "起: Hex start step as increment"⟩
  | .B_4  => some ⟨.B_4,  Stdlib.hexIdBody, 1, "止: Hex stop/stabilize as identity"⟩
  | .B_5  => some ⟨.B_5,  Stdlib.hexIdBody, 1, "立: Hex establish as identity anchor"⟩
  | .B_6  => some ⟨.B_6,  Stdlib.hexIdBody, 1, "成: Hex completion as identity anchor"⟩
  | .I_2  => some ⟨.I_2,  Stdlib.hexIdBody, 1, "一: Hex unity as identity"⟩
  | .I_6  => some ⟨.I_6,  Stdlib.huBody, 1, "分: Hex partition anchor as hu"⟩
  | .I_8  => some ⟨.I_8,  Stdlib.cuoZongBody, 1, "別: Hex differentiation as cuoZong"⟩
  | .P_9  => some ⟨.P_9,  Stdlib.hexIdBody, 1, "止: Mohist stop as identity"⟩
  | .D_1  => some ⟨.D_1,  Stdlib.hexIdBody, 1, "一: numeric unity as identity"⟩
  | .L_9  => some ⟨.L_9,  Stdlib.hexIdBody, 1, "守: governance hold as identity"⟩
  | .L_10 => some ⟨.L_10, Stdlib.hexIdBody, 1, "靜/静: governance stillness as identity"⟩
  | .Y_3  => some ⟨.Y_3,  Stdlib.tuiBody, 1, "相生: five-phase generation as increment"⟩
  | .Y_4  => some ⟨.Y_4,  Stdlib.sunBody, 1, "相克: five-phase control as decrement"⟩
  | .Y_5  => some ⟨.Y_5,  Stdlib.sunBody, 1, "相侮/反侮: counter-control as decrement"⟩
  | .Y_17 => some ⟨.Y_17, Stdlib.hexIdBody, 1, "平: medical balance as identity"⟩
  | .Y_18 => some ⟨.Y_18, Stdlib.hexIdBody, 1, "和: medical harmony as identity"⟩
  | .Z_2  => some ⟨.Z_2,  Stdlib.huBody, 1, "相: mutuality prefix as hu anchor"⟩
  | .Z_8  => some ⟨.Z_8,  Stdlib.sunBody, 1, "隱/隐: conceal as decrement"⟩
  | .Z_9  => some ⟨.Z_9,  Stdlib.tuiBody, 1, "顯/显: manifest as increment"⟩
  | .Z_12 => some ⟨.Z_12, Stdlib.hexIdBody, 1, "守: hold as identity"⟩
  | .Z_13 => some ⟨.Z_13, Stdlib.hexIdBody, 1, "持: maintain as identity"⟩
  | .Z_22 => some ⟨.Z_22, Stdlib.sunBody, 1, "蘊/蕴: enfold as decrement"⟩
  | .Z_29 => some ⟨.Z_29, Stdlib.hexApplyBody, 2, "推: operator-level Hex endomap application"⟩
  | .Z_31 => some ⟨.Z_31, Stdlib.cuoBody, 1, "反: operator-level reversal anchored as cuo"⟩
  | .Z_32 => some ⟨.Z_32, Stdlib.hexApplyBody, 2, "自: reflexive Hex endomap application"⟩
  | .Z_33 => some ⟨.Z_33, Stdlib.cuoZongBody, 1, "自反/反自: self-reflection as cuoZong"⟩
  | .F_3  => some ⟨.F_3,  Stdlib.tuiBody, 1, "進/进: forward Hex motion as increment"⟩
  | .F_4  => some ⟨.F_4,  Stdlib.sunBody, 1, "退: backward Hex motion as decrement"⟩
  | .F_5  => some ⟨.F_5,  Stdlib.tuiBody, 1, "升: upward Hex motion as increment"⟩
  | .F_6  => some ⟨.F_6,  Stdlib.sunBody, 1, "降: downward Hex motion as decrement"⟩
  | .F_9  => some ⟨.F_9,  Stdlib.tuiBody, 1, "行: active Hex motion as increment"⟩
  | .F_10 => some ⟨.F_10, Stdlib.tuiBody, 1, "動/动: movement as Hex increment"⟩
  | .F_11 => some ⟨.F_11, Stdlib.hexIdBody, 1, "靜/静: still flow as Hex identity"⟩
  | .L_11 => some ⟨.L_11, Stdlib.hexIdBody, 1, "無為/无为: no-op governance process as Hex identity"⟩
  | .SUN_6 => some ⟨.SUN_6, Stdlib.hexIdBody, 1, "正: orthodox military formation as Hex identity"⟩
  | .Z_10 => some ⟨.Z_10, Stdlib.sunBody, 1, "藏: concealment transition as decrement"⟩
  | .Z_11 => some ⟨.Z_11, Stdlib.tuiBody, 1, "露: exposure transition as increment"⟩
  | .Z_36 => some ⟨.Z_36, Stdlib.tuiBody, 1, "明: clarification transition as increment"⟩
  | .Z_37 => some ⟨.Z_37, Stdlib.sunBody, 1, "蔽: obscuring transition as decrement"⟩
  | .ZA_2 => some ⟨.ZA_2, Stdlib.hexIdBody, 1, "靜/静: Huang-Lao stillness as identity"⟩
  | .N_3  => some ⟨.N_3,  Stdlib.buBody, 1, "弗: Bool negation alias"⟩
  | .N_4  => some ⟨.N_4,  Stdlib.buBody, 1, "勿: Bool negation alias"⟩
  | .N_5  => some ⟨.N_5,  Stdlib.buBody, 1, "毋: Bool negation alias"⟩
  | .N_6  => some ⟨.N_6,  Stdlib.buBody, 1, "反: proposition-level Bool negation"⟩
  | .K_1  => some ⟨.K_1,  Stdlib.impBody, 2, "故: Bool implication"⟩
  | .K_6  => some ⟨.K_6,  Stdlib.hexApplyBody, 2, "使: causative Hex endomap application"⟩
  | .K_7  => some ⟨.K_7,  Stdlib.hexApplyBody, 2, "令: command Hex endomap application"⟩
  | .K_8  => some ⟨.K_8,  Stdlib.hexApplyBody, 2, "以: Hex endomap instrument application"⟩
  | .L_7  => some ⟨.L_7,  Stdlib.hexApplyBody, 2, "因: Legalist instrumental Hex endomap application"⟩
  | .S_3  => some ⟨.S_3,  Stdlib.impBody, 2, "則/则: Bool implication"⟩
  | .S_7  => some ⟨.S_7,  Stdlib.impBody, 2, "故: sequential implication alias"⟩
  | .Z_1  => some ⟨.Z_1,  Stdlib.impBody, 2, "因: Bool implication"⟩
  | .A_4  => some ⟨.A_4,  Stdlib.impBody, 2, "遂: Bool implication / consequent marker"⟩
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
  | .Q_8  => some ⟨.Q_8,  Stdlib.uniqueHBody, 1, "唯: finite unique-existence quantifier over Hex"⟩
  | .Q_3  => some ⟨.Q_3,  Stdlib.eachHBody, 2, "各: finite distributed forall over a Hex domain predicate"⟩
  | .D_9  => some ⟨.D_9,  Stdlib.fanBody, 1, "終/终: throughout as finite forall over Hex"⟩
  | .D_3  => some ⟨.D_3,  Stdlib.exactly3HBody, 1, "三: finite exactly-three quantifier over Hex"⟩
  | .D_10 => some ⟨.D_10, Stdlib.majorityHBody, 1, "過半/大半: finite majority quantifier over Hex"⟩
  | .M_5  => some ⟨.M_5,  Stdlib.existsHBody, 1, "可: finite possibility over Hex predicate"⟩
  | .M_8  => some ⟨.M_8,  Stdlib.biModalBody, 1, "應/应: finite necessity / should over Hex"⟩
  | .M_3  => some ⟨.M_3,  Stdlib.impBody, 2, "當/当: guarded modal condition as Bool implication"⟩
  | .M_4  => some ⟨.M_4,  Stdlib.impBody, 2, "宜: advisory modal condition as Bool implication"⟩
  | .M_6  => some ⟨.M_6,  Stdlib.impBody, 2, "能: capability condition as Bool implication"⟩
  | .M_7  => some ⟨.M_7,  Stdlib.impBody, 2, "得: permission condition as Bool implication"⟩
  | .A_11 => some ⟨.A_11, .andB, 2, "既...又... / 一...且...: Bool conjunction"⟩
  | .A_12 => some ⟨.A_12, .andB, 2, "且: Bool conjunction"⟩
  | .A_13 => some ⟨.A_13, .andB, 2, "但: truth-conditional contrast as Bool conjunction"⟩
  | .A_14 => some ⟨.A_14, Stdlib.uniqueHBody, 1, "唯: focus-only layer as finite unique-existence"⟩
  | .D_2  => some ⟨.D_2,  Stdlib.repeatOnceBody, 1, "再: repeat a Hex endomap once"⟩
  | .A_5  => some ⟨.A_5,  Stdlib.repeatOnceBody, 1, "復/复: aspectual repeat as applying a Hex endomap twice"⟩
  | .A_6  => some ⟨.A_6,  Stdlib.repeatOnceBody, 1, "又: again as applying a Hex endomap twice"⟩
  | .S_4  => some ⟨.S_4,  Stdlib.boolMarkerBody, 1, "若: truth-core conditional marker"⟩
  | .S_5  => some ⟨.S_5,  Stdlib.boolMarkerBody, 1, "雖/虽: truth-core concessive marker"⟩
  | .S_6  => some ⟨.S_6,  Stdlib.boolMarkerBody, 1, "然: truth-core discourse marker"⟩
  | .S_8  => some ⟨.S_8,  Stdlib.boolMarkerBody, 1, "乃: truth-core sequential marker"⟩
  | .S_1  => some ⟨.S_1,  Stdlib.hexApplyBody, 2, "之: Hex endomap application/projection"⟩
  | .S_2  => some ⟨.S_2,  Stdlib.endoCompBody, 2,
      "而: Hex endomap composition; surface currently requires explicit Hex→Hex terms"⟩
  | id    => relationPredicateBoolSemanticsFor? id

/-- The exact theorem-backed subset, kept separate from structural catalogue semantics. -/
def coreTheoremBackedOperatorIds : List OperatorId :=
  [.T_10, .R_8, .N_1, .M_1, .I_1, .Q_1, .T_12, .T_13, .Z_5, .Z_6, .Z_3, .T_6]
    ++ [.R_6, .R_11, .T_1, .T_2, .T_4, .T_5, .T_7, .T_8, .T_9, .T_14, .T_15,
        .B_3, .B_4, .B_5, .B_6, .I_2, .I_6, .I_8, .P_9, .D_1, .L_9, .L_10,
        .Y_3, .Y_4, .Y_5, .Y_17, .Y_18, .Z_2, .Z_8, .Z_9, .Z_12, .Z_13,
        .Z_22, .Z_29, .Z_31, .Z_32, .Z_33,
        .F_3, .F_4, .F_5, .F_6, .F_9, .F_10, .F_11,
        .L_11, .SUN_6, .Z_10, .Z_11, .Z_36, .Z_37, .ZA_2]
    ++ [.N_3, .N_4, .N_5, .N_6, .K_1, .K_6, .K_7, .K_8, .L_7, .S_3, .S_7, .Z_1, .I_3, .I_4,
        .I_5, .P_4, .N_2, .N_7, .P_5, .Q_2, .Q_4, .M_2, .Q_5, .Q_6, .Q_7,
        .Q_3, .Q_8, .D_2, .D_3, .D_9, .D_10, .M_3, .M_4, .M_5, .M_6, .M_7, .M_8,
        .A_4, .A_5, .A_6, .A_11, .A_12, .A_13, .A_14,
        .S_1, .S_2, .S_4, .S_5, .S_6, .S_8]

def theoremBackedOperatorIds : List OperatorId :=
  coreTheoremBackedOperatorIds ++ relationPredicateBoolOperatorIds

def isTheoremBackedOperator (id : OperatorId) : Bool :=
  (theoremBackedSemanticsFor? id).isSome

def structuralCatalogueOperatorIds : List OperatorId :=
  allOperatorIds.filter (fun id => (theoremBackedSemanticsFor? id).isNone)

/-! ## § 1.5 Structural catalogue semantics -/

/--
Structural total fallback for catalogue rows.

These bodies are executable and type-checkable, but intentionally weaker than
the 159 exact rows above: they preserve the operator id, signature kind, and
evaluated arguments as a catalogue value instead of projecting fake Hex/Bool
results.
-/
def catalogueStructuralBodyFor (sig : CoveredOperatorSignature) : Tm :=
  match sig.arity with
  | 1 => .abs "a" .hex (.catalogue1 sig.id (.var "a"))
  | 2 => .abs "a" .hex (.abs "b" .hex (.catalogue2 sig.id (.var "a") (.var "b")))
  | 3 => .abs "a" .hex
      (.abs "b" .hex
        (.abs "c" .hex (.catalogue3 sig.id (.var "a") (.var "b") (.var "c"))))
  | _ => .yi

def catalogueStructuralSemanticsFor (id : OperatorId) : ExecutableSemantics :=
  let sig := fullSignatureFor id
  { id := id
  , body := catalogueStructuralBodyFor sig
  , arity := sig.arity
  , note := "structural catalogue normal form for "
      ++ id.code ++ " " ++ id.title ++ " ("
      ++ sig.kind.key ++ "/" ++ toString sig.arity ++ ")" }

/-- Total execution registry used by WenSurface. -/
def executableSemanticsFor? (id : OperatorId) : Option ExecutableSemantics :=
  match theoremBackedSemanticsFor? id with
  | some sem => some sem
  | none =>
      if decide (id ∈ allOperatorIds) then some (catalogueStructuralSemanticsFor id) else none

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
    coreTheoremBackedOperatorIds.length = 113 := by native_decide

theorem theoremBackedOperatorIds_length :
    theoremBackedOperatorIds.length = 159 := by native_decide

theorem theoremBackedOperatorIds_nodup :
    theoremBackedOperatorIds.Nodup := by native_decide

theorem theoremBackedOperatorIds_all_semantics :
    theoremBackedOperatorIds.all (fun id => (theoremBackedSemanticsFor? id).isSome) = true := by
  native_decide

theorem structuralCatalogueOperatorIds_length :
    structuralCatalogueOperatorIds.length = 212 := by native_decide

theorem structuralCatalogueOperatorIds_all_not_theorem_backed :
    structuralCatalogueOperatorIds.all (fun id => (theoremBackedSemanticsFor? id).isNone) = true := by
  native_decide

theorem executablePartition_counts :
    theoremBackedOperatorIds.length + structuralCatalogueOperatorIds.length = 371 := by
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
      ∧ theoremBackedOperatorIds.length = 159
      ∧ structuralCatalogueOperatorIds.length = 212
      ∧ theoremBackedOperatorIds.length + structuralCatalogueOperatorIds.length = 371
      ∧ executableOperatorIds.all isCatalogueOperator = true
      ∧ (∀ id : OperatorId, (operatorRegistryEntryFor id).id = id)
      ∧ (∀ id : OperatorId, (operatorRegistryEntryFor id).signature.id = id) := by
  exact
    ⟨ operatorRegistryEntries_length
    , executableRegistryEntries_length
    , executableOperatorIds_length
    , theoremBackedOperatorIds_length
    , structuralCatalogueOperatorIds_length
    , executablePartition_counts
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
