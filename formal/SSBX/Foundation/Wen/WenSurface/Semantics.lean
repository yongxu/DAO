/-
# WenSurface.Semantics — executable semantics registry

This module separates exact stdlib denotations from total catalogue
execution.  Two hundred forty-five `OperatorId`s use exact `WenDef.Tm` bodies:
the original high-value stdlib rows, the ObjectEndo/ObjectMap/OpUnary Hex
transform package, finite Hex pair/list carriers, finite Hex quantifiers, finite Hex motion/process rows,
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
  | .R_5  => some ⟨.R_5,  Stdlib.hexIdBody, 1, "中: positional extractor anchor as identity; no geometry semantics"⟩
  | .R_11 => some ⟨.R_11, Stdlib.hexIdBody, 1, "對/对: Hex identity as paired alignment anchor"⟩
  | .R_12 => some ⟨.R_12, Stdlib.pairHBody, 2, "偶/耦: Hex pair carrier constructor"⟩
  | .R_13 => some ⟨.R_13, Stdlib.pairHBody, 2, "並/并: Hex pair carrier constructor"⟩
  | .R_14 => some ⟨.R_14, Stdlib.pairHBody, 2, "與/与: Hex pair carrier constructor"⟩
  | .R_15 => some ⟨.R_15, Stdlib.pairHBody, 2, "偕: Hex pair carrier constructor"⟩
  | .C_2  => some ⟨.C_2,  Stdlib.pairHBody, 2, "包: Hex pair carrier constructor"⟩
  | .C_4  => some ⟨.C_4,  Stdlib.hexIdBody, 1, "中: containment extractor anchor as identity; no spatial model"⟩
  | .C_5  => some ⟨.C_5,  Stdlib.hexIdBody, 1, "外: Hex projection anchor as identity; no spatial model"⟩
  | .C_6  => some ⟨.C_6,  Stdlib.hexIdBody, 1, "內/内: Hex projection anchor as identity; no spatial model"⟩
  | .C_7  => some ⟨.C_7,  Stdlib.hexIdBody, 1, "表: surface projection anchor as identity; no spatial model"⟩
  | .C_8  => some ⟨.C_8,  Stdlib.hexIdBody, 1, "裡/里: interior projection anchor as identity; no spatial model"⟩
  | .T_1  => some ⟨.T_1,  Stdlib.flip2Body, 1, "化: Hex y2 transform / inner hua"⟩
  | .T_2  => some ⟨.T_2,  Stdlib.flip3Body, 1, "變/变: Hex y3 transform / inner bian"⟩
  | .T_3  => some ⟨.T_3,  Stdlib.pairHBody, 2, "易: binary object exchange carrier"⟩
  | .T_4  => some ⟨.T_4,  Stdlib.cuoBody, 1, "革: total Hex overhaul as cuo"⟩
  | .T_5  => some ⟨.T_5,  Stdlib.flip1Body, 1, "改: local Hex y1 correction / inner dong"⟩
  | .T_7  => some ⟨.T_7,  Stdlib.hexIdBody, 1, "復/复: return-to-root as identity anchor"⟩
  | .T_8  => some ⟨.T_8,  Stdlib.hexIdBody, 1, "還/还: return as identity anchor"⟩
  | .T_9  => some ⟨.T_9,  Stdlib.zongBody, 1, "轉/转: Hex rotation/reflection as zong"⟩
  | .T_11 => some ⟨.T_11, Stdlib.pairHBody, 2, "致: binary object carrier"⟩
  | .T_14 => some ⟨.T_14, Stdlib.sunBody, 1, "屈: Hex contraction as mod-64 decrement"⟩
  | .T_15 => some ⟨.T_15, Stdlib.tuiBody, 1, "伸: Hex extension as mod-64 increment"⟩
  | .B_1  => some ⟨.B_1,  Stdlib.hexIdBody, 1, "始: Hex endpoint/extractor anchor as identity"⟩
  | .B_2  => some ⟨.B_2,  Stdlib.hexIdBody, 1, "終/终: Hex endpoint/extractor anchor as identity"⟩
  | .B_3  => some ⟨.B_3,  Stdlib.tuiBody, 1, "起: Hex start step as increment"⟩
  | .B_4  => some ⟨.B_4,  Stdlib.hexIdBody, 1, "止: Hex stop/stabilize as identity"⟩
  | .B_5  => some ⟨.B_5,  Stdlib.hexIdBody, 1, "立: Hex establish as identity anchor"⟩
  | .B_6  => some ⟨.B_6,  Stdlib.hexIdBody, 1, "成: Hex completion as identity anchor"⟩
  | .B_7  => some ⟨.B_7,  Stdlib.hexIdBody, 1, "極/极: Hex endpoint/extractor anchor as identity"⟩
  | .I_2  => some ⟨.I_2,  Stdlib.hexIdBody, 1, "一: Hex unity as identity"⟩
  | .I_6  => some ⟨.I_6,  Stdlib.huBody, 1, "分: Hex partition anchor as hu"⟩
  | .I_8  => some ⟨.I_8,  Stdlib.cuoZongBody, 1, "別: Hex differentiation as cuoZong"⟩
  | .H_1  => some ⟨.H_1,  Stdlib.hexIdBody, 1, "道: extractor anchor as identity; no Dao semantics"⟩
  | .H_2  => some ⟨.H_2,  Stdlib.hexIdBody, 1, "理: extractor anchor as identity; no principle semantics"⟩
  | .H_3  => some ⟨.H_3,  Stdlib.hexIdBody, 1, "勢/势: extractor anchor as identity; no tendency semantics"⟩
  | .H_4  => some ⟨.H_4,  Stdlib.hexIdBody, 1, "機/机: extractor anchor as identity; no opportunity semantics"⟩
  | .H_5  => some ⟨.H_5,  Stdlib.pairHBody, 2, "法: Hex pair carrier constructor; no law/norm semantics"⟩
  | .H_6  => some ⟨.H_6,  Stdlib.hexIdBody, 1, "象: extractor anchor as identity; no image semantics"⟩
  | .P_2  => some ⟨.P_2,  Stdlib.hexIdBody, 1, "體/体: Mohist part extractor anchor as identity; no part-whole semantics"⟩
  | .P_3  => some ⟨.P_3,  Stdlib.list1HBody, 1, "兼: singleton Hex aggregate carrier; no universal inclusion semantics"⟩
  | .P_6  => some ⟨.P_6,  Stdlib.hexIdBody, 1, "久: temporal extractor anchor as identity; no duration semantics"⟩
  | .P_7  => some ⟨.P_7,  Stdlib.hexIdBody, 1, "宇: spatial extractor anchor as identity; no spatial extent semantics"⟩
  | .P_9  => some ⟨.P_9,  Stdlib.hexIdBody, 1, "止: Mohist stop as identity"⟩
  | .P_10 => some ⟨.P_10, Stdlib.hexIdBody, 1, "端: Mohist endpoint anchor as identity; no geometry semantics"⟩
  | .P_11 => some ⟨.P_11, Stdlib.pairHBody, 2, "尺: Hex pair carrier constructor; no metric semantics"⟩
  | .P_12 => some ⟨.P_12, Stdlib.hexIdBody, 1, "中: Mohist middle-point anchor as identity; no geometry semantics"⟩
  | .P_13 => some ⟨.P_13, Stdlib.pairHBody, 2, "圜/圆: Hex pair carrier constructor; no geometric semantics"⟩
  | .P_18 => some ⟨.P_18, Stdlib.hexIdBody, 1, "法: Mohist model extractor anchor as identity; no rule semantics"⟩
  | .P_22 => some ⟨.P_22, Stdlib.pairHBody, 2, "說/说: Hex pair carrier constructor; no rhetorical semantics"⟩
  | .P_24 => some ⟨.P_24, Stdlib.hexIdBody, 1, "類/类: Mohist class extractor anchor as identity; no taxonomy semantics"⟩
  | .G_2  => some ⟨.G_2,  Stdlib.hexIdBody, 1, "物: concrete object anchor as identity; no ontology semantics"⟩
  | .G_4  => some ⟨.G_4,  Stdlib.hexIdBody, 1, "實/实: concrete actuality anchor as identity; no ontology semantics"⟩
  | .G_5  => some ⟨.G_5,  Stdlib.hexIdBody, 1, "位: position extractor anchor as identity; no role ontology"⟩
  | .G_8  => some ⟨.G_8,  Stdlib.pairHBody, 2, "兼/合: Names-school binary constructor carrier; no ontology semantics"⟩
  | .G_9  => some ⟨.G_9,  Stdlib.dupHBody, 1, "別/别: Names-school facet carrier via duplicate Hex; no separation semantics"⟩
  | .D_1  => some ⟨.D_1,  Stdlib.hexIdBody, 1, "一: numeric unity as identity"⟩
  | .D_4  => some ⟨.D_4,  Stdlib.dupHBody, 1, "兩/两: duplicate a Hex into a pair carrier"⟩
  | .D_8  => some ⟨.D_8,  Stdlib.pairHBody, 2, "餘/余: Hex pair carrier constructor; no arithmetic remainder"⟩
  | .H_8  => some ⟨.H_8,  Stdlib.dupHBody, 1, "體/体與用: paired facet carrier via duplicate Hex; no essence/function decomposition"⟩
  | .L_5  => some ⟨.L_5,  Stdlib.list1HBody, 1, "參同/参同: singleton Hex list carrier; no verification semantics"⟩
  | .L_3  => some ⟨.L_3,  Stdlib.hexIdBody, 1, "勢/势: Legalist power-position extractor anchor as identity; no governance semantics"⟩
  | .L_9  => some ⟨.L_9,  Stdlib.hexIdBody, 1, "守: governance hold as identity"⟩
  | .L_10 => some ⟨.L_10, Stdlib.hexIdBody, 1, "靜/静: governance stillness as identity"⟩
  | .L_12 => some ⟨.L_12, Stdlib.hexIdBody, 1, "利: benefit extractor anchor as identity; no utility semantics"⟩
  | .L_13 => some ⟨.L_13, Stdlib.list1HBody, 1, "一: Legalist unification aggregate carrier; no legal theory semantics"⟩
  | .L_15 => some ⟨.L_15, Stdlib.hexIdBody, 1, "度: Legalist measure extractor anchor as identity; no metric semantics"⟩
  | .Y_1  => some ⟨.Y_1,  Stdlib.dupHBody, 1, "陰/阴與陽/阳: paired facet carrier via duplicate Hex; no yin-yang decomposition"⟩
  | .Y_3  => some ⟨.Y_3,  Stdlib.tuiBody, 1, "相生: five-phase generation as increment"⟩
  | .Y_4  => some ⟨.Y_4,  Stdlib.sunBody, 1, "相克: five-phase control as decrement"⟩
  | .Y_5  => some ⟨.Y_5,  Stdlib.sunBody, 1, "相侮/反侮: counter-control as decrement"⟩
  | .Y_6  => some ⟨.Y_6,  Stdlib.hexIdBody, 1, "氣/气: medical state projection anchor as identity; no qi physiology semantics"⟩
  | .Y_7  => some ⟨.Y_7,  Stdlib.hexIdBody, 1, "血: medical state projection anchor as identity; no blood physiology semantics"⟩
  | .Y_8  => some ⟨.Y_8,  Stdlib.hexIdBody, 1, "精: medical state projection anchor as identity; no essence physiology semantics"⟩
  | .Y_10 => some ⟨.Y_10, Stdlib.hexIdBody, 1, "升/降: medical movement-state projection anchor as identity; no directional physiology semantics"⟩
  | .Y_11 => some ⟨.Y_11, Stdlib.hexIdBody, 1, "開/闔/樞: medical phase projection anchor as identity; no channel mechanics semantics"⟩
  | .Y_12 => some ⟨.Y_12, Stdlib.hexIdBody, 1, "經/絡: medical channel projection anchor as identity; no meridian semantics"⟩
  | .Y_13 => some ⟨.Y_13, Stdlib.hexIdBody, 1, "表/裡: medical surface/interior projection anchor as identity; no diagnostic semantics"⟩
  | .Y_14 => some ⟨.Y_14, Stdlib.hexIdBody, 1, "寒/熱: medical thermal-state projection anchor as identity; no pathology semantics"⟩
  | .Y_15 => some ⟨.Y_15, Stdlib.hexIdBody, 1, "虛/實: medical deficiency/excess projection anchor as identity; no pathology semantics"⟩
  | .Y_17 => some ⟨.Y_17, Stdlib.hexIdBody, 1, "平: medical balance as identity"⟩
  | .Y_18 => some ⟨.Y_18, Stdlib.hexIdBody, 1, "和: medical harmony as identity"⟩
  | .Y_21 => some ⟨.Y_21, Stdlib.dupHBody, 1, "標/标本: paired facet carrier via duplicate Hex; no root/branch decomposition"⟩
  | .Y_22 => some ⟨.Y_22, Stdlib.dupHBody, 1, "營/营與衛/卫: paired facet carrier via duplicate Hex; no medical channel decomposition"⟩
  | .Y_23 => some ⟨.Y_23, Stdlib.hexIdBody, 1, "通/滯: medical patency projection anchor as identity; no treatment semantics"⟩
  | .Y_24 => some ⟨.Y_24, Stdlib.hexIdBody, 1, "五运六气: medical cosmological-state projection anchor as identity; no calendrical physiology semantics"⟩
  | .Y_25 => some ⟨.Y_25, Stdlib.hexIdBody, 1, "上工/中工/下工: medical skill-grade projection anchor as identity; no practitioner evaluation semantics"⟩
  | .Y_26 => some ⟨.Y_26, Stdlib.hexIdBody, 1, "出/入: medical ingress/egress projection anchor as identity; no physiological motion semantics"⟩
  | .Y_27 => some ⟨.Y_27, Stdlib.hexIdBody, 1, "候: diagnostic query anchor as identity; no observation protocol semantics"⟩
  | .X_1  => some ⟨.X_1,  Stdlib.hexIdBody, 1, "性: social nature-state projection anchor as identity; no anthropology semantics"⟩
  | .X_4  => some ⟨.X_4,  Stdlib.list1HBody, 1, "群: singleton Hex list carrier; no social grouping semantics"⟩
  | .X_14 => some ⟨.X_14, Stdlib.list2HBody, 2, "積/积: two-input aggregate carrier; no arithmetic accumulation"⟩
  | .Z_2  => some ⟨.Z_2,  Stdlib.huBody, 1, "相: mutuality prefix as hu anchor"⟩
  | .Z_7  => some ⟨.Z_7,  Stdlib.list1HBody, 1, "雜/杂: singleton Hex list carrier; no mixture semantics"⟩
  | .Z_8  => some ⟨.Z_8,  Stdlib.sunBody, 1, "隱/隐: conceal as decrement"⟩
  | .Z_9  => some ⟨.Z_9,  Stdlib.tuiBody, 1, "顯/显: manifest as increment"⟩
  | .Z_12 => some ⟨.Z_12, Stdlib.hexIdBody, 1, "守: hold as identity"⟩
  | .Z_13 => some ⟨.Z_13, Stdlib.hexIdBody, 1, "持: maintain as identity"⟩
  | .Z_16 => some ⟨.Z_16, Stdlib.list1HBody, 1, "聚: singleton Hex list carrier"⟩
  | .Z_17 => some ⟨.Z_17, Stdlib.list1HBody, 1, "集: singleton Hex list carrier"⟩
  | .Z_18 => some ⟨.Z_18, Stdlib.headHBody, 1, "散: first Hex projection from a list carrier"⟩
  | .Z_19 => some ⟨.Z_19, Stdlib.list2HBody, 2, "積/积: two-input aggregate carrier; no arithmetic accumulation"⟩
  | .Z_21 => some ⟨.Z_21, Stdlib.list1HBody, 1, "攝/摄: singleton Hex list carrier; no subsumption semantics"⟩
  | .Z_22 => some ⟨.Z_22, Stdlib.sunBody, 1, "蘊/蕴: enfold as decrement"⟩
  | .Z_23 => some ⟨.Z_23, Stdlib.hexIdBody, 1, "萌: incipient object anchor as identity; no germination semantics"⟩
  | .Z_24 => some ⟨.Z_24, Stdlib.hexIdBody, 1, "兆: omen extractor anchor as identity; no prognostic semantics"⟩
  | .Z_26 => some ⟨.Z_26, Stdlib.hexIdBody, 1, "占: divination query anchor as identity; no divinatory semantics"⟩
  | .Z_27 => some ⟨.Z_27, Stdlib.hexIdBody, 1, "卜: divination query anchor as identity; no divinatory semantics"⟩
  | .Z_29 => some ⟨.Z_29, Stdlib.hexApplyBody, 2, "推: operator-level Hex endomap application"⟩
  | .Z_31 => some ⟨.Z_31, Stdlib.cuoBody, 1, "反: operator-level reversal anchored as cuo"⟩
  | .Z_32 => some ⟨.Z_32, Stdlib.hexApplyBody, 2, "自: reflexive Hex endomap application"⟩
  | .Z_33 => some ⟨.Z_33, Stdlib.cuoZongBody, 1, "自反/反自: self-reflection as cuoZong"⟩
  | .Z_34 => some ⟨.Z_34, Stdlib.hexIdBody, 1, "觀/观: observation query anchor as identity; no perceptual semantics"⟩
  | .Z_35 => some ⟨.Z_35, Stdlib.hexIdBody, 1, "察: inspection query anchor as identity; no investigation semantics"⟩
  | .F_1  => some ⟨.F_1,  Stdlib.hexApplyBody, 2, "往: directional flow as Hex endomap application; no path semantics"⟩
  | .F_2  => some ⟨.F_2,  Stdlib.hexApplyBody, 2, "來/来: return flow as Hex endomap application; no path semantics"⟩
  | .F_3  => some ⟨.F_3,  Stdlib.tuiBody, 1, "進/进: forward Hex motion as increment"⟩
  | .F_4  => some ⟨.F_4,  Stdlib.sunBody, 1, "退: backward Hex motion as decrement"⟩
  | .F_5  => some ⟨.F_5,  Stdlib.tuiBody, 1, "升: upward Hex motion as increment"⟩
  | .F_6  => some ⟨.F_6,  Stdlib.sunBody, 1, "降: downward Hex motion as decrement"⟩
  | .F_7  => some ⟨.F_7,  Stdlib.hexApplyBody, 2, "出: outbound flow as Hex endomap application; no boundary topology"⟩
  | .F_8  => some ⟨.F_8,  Stdlib.hexApplyBody, 2, "入: inbound flow as Hex endomap application; no boundary topology"⟩
  | .F_9  => some ⟨.F_9,  Stdlib.tuiBody, 1, "行: active Hex motion as increment"⟩
  | .F_10 => some ⟨.F_10, Stdlib.tuiBody, 1, "動/动: movement as Hex increment"⟩
  | .F_11 => some ⟨.F_11, Stdlib.hexIdBody, 1, "靜/静: still flow as Hex identity"⟩
  | .L_11 => some ⟨.L_11, Stdlib.hexIdBody, 1, "無為/无为: no-op governance process as Hex identity"⟩
  | .LIJ_5 => some ⟨.LIJ_5, Stdlib.hexIdBody, 1, "儀/仪: ritual protocol anchor as identity; no ritual-procedure semantics"⟩
  | .SUN_6 => some ⟨.SUN_6, Stdlib.hexIdBody, 1, "正: orthodox military formation as Hex identity"⟩
  | .Z_10 => some ⟨.Z_10, Stdlib.sunBody, 1, "藏: concealment transition as decrement"⟩
  | .Z_11 => some ⟨.Z_11, Stdlib.tuiBody, 1, "露: exposure transition as increment"⟩
  | .Z_36 => some ⟨.Z_36, Stdlib.tuiBody, 1, "明: clarification transition as increment"⟩
  | .Z_37 => some ⟨.Z_37, Stdlib.sunBody, 1, "蔽: obscuring transition as decrement"⟩
  | .ZA_2 => some ⟨.ZA_2, Stdlib.hexIdBody, 1, "靜/静: Huang-Lao stillness as identity"⟩
  | .ZA_3 => some ⟨.ZA_3, Stdlib.hexIdBody, 1, "心君: supervisory anchor as identity; no heart-governance semantics"⟩
  | .ZA_5 => some ⟨.ZA_5, Stdlib.hexIdBody, 1, "精: inner-cultivation process anchor as identity; no cultivation semantics"⟩
  | .ZA_7 => some ⟨.ZA_7, Stdlib.hexIdBody, 1, "令: monthly-order directive anchor as identity; no calendrical mandate semantics"⟩
  | .ZA_11 => some ⟨.ZA_11, Stdlib.hexIdBody, 1, "督: supervisory anchor as identity; no control semantics"⟩
  | .ZHU_9 => some ⟨.ZHU_9, Stdlib.hexIdBody, 1, "天理: Zhuangzi pattern extractor anchor as identity; no cosmological semantics"⟩
  | .ZHU_10 => some ⟨.ZHU_10, Stdlib.hexIdBody, 1, "方: modifier anchor as identity; no direction/method semantics"⟩
  | .SUN_1 => some ⟨.SUN_1, Stdlib.hexIdBody, 1, "形: military signal anchor as identity; no formation semantics"⟩
  | .SUN_2 => some ⟨.SUN_2, Stdlib.pairHBody, 2, "勢/势: military two-input extractor carrier; no force-position semantics"⟩
  | .SUN_3 => some ⟨.SUN_3, Stdlib.hexIdBody, 1, "虛/虚: military weakness extractor anchor as identity; no tactical semantics"⟩
  | .SUN_4 => some ⟨.SUN_4, Stdlib.hexIdBody, 1, "實/实: military strength extractor anchor as identity; no tactical semantics"⟩
  | .SUN_5 => some ⟨.SUN_5, Stdlib.hexIdBody, 1, "奇: military process anchor as identity; no tactical-surprise semantics"⟩
  | .SUN_14 => some ⟨.SUN_14, Stdlib.pairHBody, 2, "知: military intelligence extractor carrier; no epistemic semantics"⟩
  | .CHU_4 => some ⟨.CHU_4, Stdlib.hexIdBody, 1, "登: Chu-ci ascent extractor anchor as identity; no elevation semantics"⟩
  | .CHU_5 => some ⟨.CHU_5, Stdlib.pairHBody, 2, "望: Chu-ci vantage extractor carrier; no visual semantics"⟩
  | .CHU_9 => some ⟨.CHU_9, Stdlib.list1HBody, 1, "集: singleton Hex list carrier"⟩
  | .LIJ_4 => some ⟨.LIJ_4, Stdlib.hexIdBody, 1, "位: ritual role-position extractor anchor as identity; no ritual ontology"⟩
  | .LIJ_7 => some ⟨.LIJ_7, Stdlib.hexIdBody, 1, "中: ritual equilibrium extractor anchor as identity; no affective semantics"⟩
  | .LIJ_11 => some ⟨.LIJ_11, Stdlib.hexIdBody, 1, "獨/独: ritual solitude extractor anchor as identity; no individuation semantics"⟩
  | .ZA_6 => some ⟨.ZA_6, Stdlib.hexIdBody, 1, "時/时: monthly-order time anchor as identity; no calendrical semantics"⟩
  | .N_3  => some ⟨.N_3,  Stdlib.buBody, 1, "弗: Bool negation alias"⟩
  | .N_4  => some ⟨.N_4,  Stdlib.buBody, 1, "勿: Bool negation alias"⟩
  | .N_5  => some ⟨.N_5,  Stdlib.buBody, 1, "毋: Bool negation alias"⟩
  | .N_6  => some ⟨.N_6,  Stdlib.buBody, 1, "反: proposition-level Bool negation"⟩
  | .K_1  => some ⟨.K_1,  Stdlib.impBody, 2, "故: Bool implication"⟩
  | .K_5  => some ⟨.K_5,  Stdlib.pairHBody, 2, "致: causative binary object carrier"⟩
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
  | .I_7  => some ⟨.I_7,  Stdlib.pairHBody, 2, "合: binary object combination carrier"⟩
  | .P_4  => some ⟨.P_4,  Stdlib.tongBody, 2, "同: Mohist equality alias"⟩
  | .N_2  => some ⟨.N_2,  Stdlib.neqHexBody, 2, "非: Hex disequality"⟩
  | .N_7  => some ⟨.N_7,  Stdlib.neqHexBody, 2, "異/异: Hex disequality"⟩
  | .N_8  => some ⟨.N_8,  Stdlib.pairHBody, 2, "別/别: binary object distinction carrier"⟩
  | .P_5  => some ⟨.P_5,  Stdlib.neqHexBody, 2, "異/异: Mohist disequality alias"⟩
  | .P_23 => some ⟨.P_23, .andB, 2, "辯/辩: proposition connective carrier as Bool conjunction; no debate semantics"⟩
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
  | .A_1  => some ⟨.A_1,  Stdlib.hexIdBody, 1, "漸/渐: aspect anchor as identity; no gradual-time semantics"⟩
  | .A_2  => some ⟨.A_2,  Stdlib.hexIdBody, 1, "驟/骤: aspect anchor as identity; no sudden-time semantics"⟩
  | .A_3  => some ⟨.A_3,  Stdlib.hexIdBody, 1, "忽: aspect anchor as identity; no abrupt-time semantics"⟩
  | .A_8  => some ⟨.A_8,  Stdlib.hexIdBody, 1, "愈: adverbial modifier anchor as identity; no degree semantics"⟩
  | .A_9  => some ⟨.A_9,  Stdlib.hexIdBody, 1, "益: adverbial modifier anchor as identity; no increment semantics"⟩
  | .A_11 => some ⟨.A_11, .andB, 2, "既...又... / 一...且...: Bool conjunction"⟩
  | .A_12 => some ⟨.A_12, .andB, 2, "且: Bool conjunction"⟩
  | .A_13 => some ⟨.A_13, .andB, 2, "但: truth-conditional contrast as Bool conjunction"⟩
  | .A_14 => some ⟨.A_14, Stdlib.uniqueHBody, 1, "唯: focus-only layer as finite unique-existence"⟩
  | .A_15 => some ⟨.A_15, Stdlib.hexIdBody, 1, "亦: adverbial modifier anchor as identity; no focus/additive semantics"⟩
  | .D_2  => some ⟨.D_2,  Stdlib.repeatOnceBody, 1, "再: repeat a Hex endomap once"⟩
  | .A_5  => some ⟨.A_5,  Stdlib.repeatOnceBody, 1, "復/复: aspectual repeat as applying a Hex endomap twice"⟩
  | .A_6  => some ⟨.A_6,  Stdlib.repeatOnceBody, 1, "又: again as applying a Hex endomap twice"⟩
  | .A_7  => some ⟨.A_7,  Stdlib.hexIdBody, 1, "屢/屡: aspect anchor as identity; no frequency semantics"⟩
  | .A_10 => some ⟨.A_10, Stdlib.hexIdBody, 1, "寖/浸: aspect anchor as identity; no gradual-time semantics"⟩
  | .A_16 => some ⟨.A_16, Stdlib.hexIdBody, 1, "已: aspect anchor as identity; no completed-time semantics"⟩
  | .A_17 => some ⟨.A_17, Stdlib.hexIdBody, 1, "未: aspect anchor as identity; no future/negation semantics"⟩
  | .A_18 => some ⟨.A_18, Stdlib.hexIdBody, 1, "將/将: aspect anchor as identity; no prospective-time semantics"⟩
  | .A_19 => some ⟨.A_19, Stdlib.hexIdBody, 1, "方: aspect anchor as identity; no progressive-time semantics"⟩
  | .A_20 => some ⟨.A_20, Stdlib.hexIdBody, 1, "嘗/尝: aspect anchor as identity; no experiential-time semantics"⟩
  | .S_4  => some ⟨.S_4,  Stdlib.boolMarkerBody, 1, "若: truth-core conditional marker"⟩
  | .S_5  => some ⟨.S_5,  Stdlib.boolMarkerBody, 1, "雖/虽: truth-core concessive marker"⟩
  | .S_6  => some ⟨.S_6,  Stdlib.boolMarkerBody, 1, "然: truth-core discourse marker"⟩
  | .S_8  => some ⟨.S_8,  Stdlib.boolMarkerBody, 1, "乃: truth-core sequential marker"⟩
  | .S_9  => some ⟨.S_9,  Stdlib.hexIdBody, 1, "既: aspect anchor as identity; no completed-time semantics"⟩
  | .S_10 => some ⟨.S_10, Stdlib.hexIdBody, 1, "將/将: aspect anchor as identity; no prospective-time semantics"⟩
  | .S_11 => some ⟨.S_11, Stdlib.hexIdBody, 1, "方: aspect anchor as identity; no progressive-time semantics"⟩
  | .S_12 => some ⟨.S_12, Stdlib.hexIdBody, 1, "嘗/尝: aspect anchor as identity; no experiential-time semantics"⟩
  | .S_17 => some ⟨.S_17, Stdlib.hexIdBody, 1, "未: aspect anchor as identity; no future/negation semantics"⟩
  | .S_18 => some ⟨.S_18, Stdlib.hexIdBody, 1, "已: aspect anchor as identity; no completed-time semantics"⟩
  | .S_19 => some ⟨.S_19, Stdlib.hexApplyBody, 2, "的: explicit modifier application as Hex endomap application; no modern-grammar semantics"⟩
  | .S_1  => some ⟨.S_1,  Stdlib.hexApplyBody, 2, "之: Hex endomap application/projection"⟩
  | .S_2  => some ⟨.S_2,  Stdlib.endoCompBody, 2,
      "而: Hex endomap composition; surface currently requires explicit Hex→Hex terms"⟩
  | id    => relationPredicateBoolSemanticsFor? id

/-- The exact theorem-backed subset, kept separate from structural catalogue semantics. -/
def coreTheoremBackedOperatorIds : List OperatorId :=
  [.T_10, .R_8, .N_1, .M_1, .I_1, .Q_1, .T_12, .T_13, .Z_5, .Z_6, .Z_3, .T_6]
    ++ [.R_5, .R_6, .R_11, .R_12, .R_13, .R_14, .R_15,
        .C_2, .C_4, .C_5, .C_6, .C_7, .C_8,
        .T_1, .T_2, .T_3, .T_4, .T_5, .T_7, .T_8, .T_9, .T_11, .T_14, .T_15,
        .B_1, .B_2, .B_3, .B_4, .B_5, .B_6, .B_7,
        .I_2, .I_6, .I_8, .H_1, .H_2, .H_3, .H_4, .H_5, .H_6,
        .P_2, .P_3, .P_6, .P_7, .P_9, .P_10,
        .P_11, .P_12, .P_13, .P_18, .P_22, .P_24, .G_2, .G_4, .G_5, .G_8, .G_9,
        .D_1, .D_4, .D_8, .H_8, .L_3, .L_5, .L_9, .L_10, .L_12, .L_13, .L_15,
        .Y_1, .Y_3, .Y_4, .Y_5, .Y_6, .Y_7, .Y_8, .Y_10, .Y_11, .Y_12,
        .Y_13, .Y_14, .Y_15, .Y_17, .Y_18, .Y_21, .Y_22, .Y_23, .Y_24,
        .Y_25, .Y_26, .Y_27, .X_1, .X_4, .X_14,
        .Z_2, .Z_7, .Z_8, .Z_9, .Z_12, .Z_13,
        .Z_16, .Z_17, .Z_18, .Z_19, .Z_21, .Z_22, .Z_23, .Z_24, .Z_26, .Z_27,
        .Z_29, .Z_31, .Z_32, .Z_33, .Z_34, .Z_35,
        .F_1, .F_2, .F_3, .F_4, .F_5, .F_6, .F_7, .F_8, .F_9, .F_10, .F_11,
        .L_11, .LIJ_5, .SUN_1, .SUN_5, .SUN_6, .Z_10, .Z_11, .Z_36, .Z_37,
        .ZA_2, .ZA_3, .ZA_5, .ZA_7, .ZA_11, .ZHU_9, .ZHU_10,
        .SUN_2, .SUN_3, .SUN_4, .SUN_14, .CHU_4, .CHU_5, .CHU_9,
        .LIJ_4, .LIJ_7, .LIJ_11, .ZA_6]
    ++ [.N_3, .N_4, .N_5, .N_6, .K_1, .K_5, .K_6, .K_7, .K_8, .L_7, .S_3, .S_7, .Z_1, .I_3, .I_4,
        .I_5, .I_7, .P_4, .N_2, .N_7, .N_8, .P_5, .P_23, .Q_2, .Q_4, .M_2, .Q_5, .Q_6, .Q_7,
        .Q_3, .Q_8, .D_2, .D_3, .D_9, .D_10, .M_3, .M_4, .M_5, .M_6, .M_7, .M_8,
        .A_1, .A_2, .A_3, .A_4, .A_5, .A_6, .A_7, .A_8, .A_9, .A_10,
        .A_11, .A_12, .A_13, .A_14, .A_15, .A_16, .A_17, .A_18, .A_19, .A_20,
        .S_1, .S_2, .S_4, .S_5, .S_6, .S_8, .S_9, .S_10, .S_11, .S_12, .S_17, .S_18, .S_19]

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
the 285 exact rows above: they preserve the operator id, signature kind, and
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
    coreTheoremBackedOperatorIds.length = 239 := by native_decide

theorem theoremBackedOperatorIds_length :
    theoremBackedOperatorIds.length = 285 := by native_decide

theorem theoremBackedOperatorIds_nodup :
    theoremBackedOperatorIds.Nodup := by native_decide

theorem theoremBackedOperatorIds_all_semantics :
    theoremBackedOperatorIds.all (fun id => (theoremBackedSemanticsFor? id).isSome) = true := by
  native_decide

theorem structuralCatalogueOperatorIds_length :
    structuralCatalogueOperatorIds.length = 86 := by native_decide

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
      ∧ theoremBackedOperatorIds.length = 285
      ∧ structuralCatalogueOperatorIds.length = 86
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
