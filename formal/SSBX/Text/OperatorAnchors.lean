import SSBX.Text.WenyanOperators
import SSBX.Foundation.Bagua.BaguaWenSpec

/-!
# OperatorAnchors — 文言算子到八卦系统的锚点

This file is the bridge between the text-level `OperatorId` catalogue and the
formal Bagua/Yi layer.  It is intentionally conservative:

* `catalogueIds` records existing `OperatorId` entries.
* `semanticIds` records nearby formal anchors when the hexagram table names a
  variant or derived meaning.
* `missingForms` records words present in the 64-hexagram operator table that
  are still not admitted as Lean `OperatorId`s.
* `hexagramGapPromotions` records the 25 former gap words now admitted as
  general catalogue entries.
-/

namespace SSBX.Text.OperatorAnchors

open SSBX.Text.WenyanOperators
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.BaguaWenSpec

/-! ## § 1 Anchor kinds -/

/-- Coarse classification of an anchor into the Bagua/Yi system. -/
inductive AnchorKind where
  | yiInstr
  | shi
  | yaoPosition
  | targetMarker
  | positionRelation
  | trigramOperator
  | hexagramOperator
  | cellPosition
  deriving Repr, DecidableEq, BEq

/-! ## § 2 BaguaWen L0 instruction anchors -/

/-- Parameter-erased shape of the 12 `YiInstr` constructors. -/
inductive YiInstrKind where
  | nop
  | setShi
  | flipYao
  | hu
  | cuo
  | zong
  | branchYaoEq
  | branchShiEq
  | jump
  | push
  | pop
  | halt
  deriving Repr, DecidableEq, BEq

namespace YiInstrKind

/-- Canonical BaguaWen token for each parameter-erased instruction shape. -/
def token : YiInstrKind → String
  | .nop => "不动"
  | .setShi => "设时"
  | .flipYao => "翻爻"
  | .hu => "互"
  | .cuo => "错"
  | .zong => "综"
  | .branchYaoEq => "比爻"
  | .branchShiEq => "比时"
  | .jump => "跳"
  | .push => "推"
  | .pop => "取"
  | .halt => "终"

/-- A representative concrete instruction for checking against `primaryToken`. -/
def sample : YiInstrKind → YiInstr
  | .nop => .nop
  | .setShi => .setShi Shi.jin
  | .flipYao => .flipYao ⟨0, by decide⟩
  | .hu => .hu
  | .cuo => .cuo
  | .zong => .zong
  | .branchYaoEq => .branchYaoEq ⟨0, by decide⟩ ⟨1, by decide⟩ 0
  | .branchShiEq => .branchShiEq Shi.jin 0
  | .jump => .jump 0
  | .push => .push
  | .pop => .pop
  | .halt => .halt

theorem primaryToken_sample (k : YiInstrKind) :
    primaryToken k.sample = k.token := by
  cases k <;> rfl

end YiInstrKind

def yiInstrKinds : List YiInstrKind :=
  [.nop, .setShi, .flipYao, .hu, .cuo, .zong,
   .branchYaoEq, .branchShiEq, .jump, .push, .pop, .halt]

theorem yiInstrKinds_length : yiInstrKinds.length = 12 := by native_decide

theorem yiInstrKinds_tokens_eq_primaryTokens :
    yiInstrKinds.map YiInstrKind.token = primaryTokens := by
  native_decide

/-- L0 token to catalogue bridge. Empty `catalogueIds` means primitive-only. -/
structure L0OperatorAnchor where
  kind : YiInstrKind
  catalogueIds : List OperatorId
  missingForms : List String
  deriving Repr

namespace L0OperatorAnchor

def token (a : L0OperatorAnchor) : String := a.kind.token

end L0OperatorAnchor

/-- All 12 BaguaWen primary instruction tokens, with text-catalogue status. -/
def l0OperatorAnchors : List L0OperatorAnchor :=
  [ { kind := .nop,          catalogueIds := [],              missingForms := ["不动"] }
  , { kind := .setShi,       catalogueIds := [],              missingForms := ["设时"] }
  , { kind := .flipYao,      catalogueIds := [],              missingForms := ["翻爻"] }
  , { kind := .hu,           catalogueIds := [.Z_3],          missingForms := [] }
  , { kind := .cuo,          catalogueIds := [.Z_5],          missingForms := [] }
  , { kind := .zong,         catalogueIds := [.Z_6],          missingForms := [] }
  , { kind := .branchYaoEq,  catalogueIds := [.R_8],          missingForms := [] }
  , { kind := .branchShiEq,  catalogueIds := [.R_8],          missingForms := [] }
  , { kind := .jump,         catalogueIds := [],              missingForms := ["跳"] }
  , { kind := .push,         catalogueIds := [.T_10, .Z_29],  missingForms := [] }
  , { kind := .pop,          catalogueIds := [],              missingForms := ["取"] }
  , { kind := .halt,         catalogueIds := [.B_2, .D_9],    missingForms := [] }
  ]

theorem l0OperatorAnchors_length : l0OperatorAnchors.length = 12 := by
  native_decide

theorem l0OperatorAnchor_tokens_eq_primaryTokens :
    l0OperatorAnchors.map L0OperatorAnchor.token = primaryTokens := by
  native_decide

theorem primaryToken_has_l0_anchor (s : String) :
    s ∈ primaryTokens → s ∈ l0OperatorAnchors.map L0OperatorAnchor.token := by
  intro h
  simpa [l0OperatorAnchor_tokens_eq_primaryTokens] using h

/-! ## § 3 Shi and yao-position anchors -/

structure ShiAnchor where
  shi : Shi
  token : String
  deriving Repr

def shiAnchors : List ShiAnchor :=
  [ { shi := .ji,  token := "已" }
  , { shi := .jin, token := "今" }
  , { shi := .wei, token := "未" }
  ]

theorem shiAnchors_length : shiAnchors.length = 3 := by native_decide

theorem shiAnchors_cover_all : shiAnchors.map (·.shi) = Shi.all := by
  native_decide

theorem shiAnchor_tokens_eq_shiTokens : shiAnchors.map (·.token) = shiTokens := by
  native_decide

structure YaoPositionAnchor where
  position : Fin 6
  token : String
  deriving Repr

def yaoPositionAnchors : List YaoPositionAnchor :=
  [ { position := ⟨0, by decide⟩, token := "初爻" }
  , { position := ⟨1, by decide⟩, token := "二爻" }
  , { position := ⟨2, by decide⟩, token := "三爻" }
  , { position := ⟨3, by decide⟩, token := "四爻" }
  , { position := ⟨4, by decide⟩, token := "五爻" }
  , { position := ⟨5, by decide⟩, token := "上爻" }
  ]

theorem yaoPositionAnchors_length : yaoPositionAnchors.length = 6 := by
  native_decide

theorem yaoPositionAnchor_values :
    yaoPositionAnchors.map (fun a => a.position.val) = List.range 6 := by
  native_decide

theorem yaoPositionAnchor_tokens_eq_yaoTokens :
    yaoPositionAnchors.map (·.token) = yaoTokens := by
  native_decide

/-! ## § 3b Full reserved-token anchors -/

structure ReservedTokenAnchor where
  token : String
  kind : AnchorKind
  deriving Repr

def reservedTokenAnchors : List ReservedTokenAnchor :=
  (l0OperatorAnchors.map fun a =>
    { token := a.token, kind := AnchorKind.yiInstr }) ++
  (shiAnchors.map fun a =>
    { token := a.token, kind := AnchorKind.shi }) ++
  (yaoPositionAnchors.map fun a =>
    { token := a.token, kind := AnchorKind.yaoPosition }) ++
  [{ token := atKeyword, kind := AnchorKind.targetMarker }]

theorem reservedTokenAnchors_length :
    reservedTokenAnchors.length = 22 := by
  native_decide

theorem reservedTokenAnchor_tokens_eq_reservedTokens :
    reservedTokenAnchors.map (·.token) = reservedTokens := by
  native_decide

theorem reservedToken_has_anchor (s : String) :
    s ∈ reservedTokens → s ∈ reservedTokenAnchors.map (·.token) := by
  intro h
  simpa [reservedTokenAnchor_tokens_eq_reservedTokens] using h

/-! ## § 4 Position-relation anchors -/

/-- Named position relations used by the Yi layer. -/
inductive PositionRelationKind where
  | zhong
  | zheng
  | ying
  | bi
  | chengBelow
  | riding
  deriving Repr, DecidableEq, BEq

namespace PositionRelationKind

def token : PositionRelationKind → String
  | .zhong => "中"
  | .zheng => "正"
  | .ying => "应"
  | .bi => "比"
  | .chengBelow => "承"
  | .riding => "乘"

end PositionRelationKind

structure PositionRelationAnchor where
  relation : PositionRelationKind
  catalogueId : OperatorId
  deriving Repr

def positionRelationAnchors : List PositionRelationAnchor :=
  [ { relation := .zhong,      catalogueId := .R_5 }
  , { relation := .zheng,      catalogueId := .R_6 }
  , { relation := .ying,       catalogueId := .R_7 }
  , { relation := .bi,         catalogueId := .R_8 }
  , { relation := .chengBelow, catalogueId := .R_9 }
  , { relation := .riding,     catalogueId := .R_10 }
  ]

theorem positionRelationAnchors_length : positionRelationAnchors.length = 6 := by
  native_decide

def positionWordAnchor : OperatorId := .G_5

/-! ## § 5 Eight trigram operator anchors -/

structure TrigramOperatorAnchor where
  trigram : Trigram
  name : String
  mode : JianMode
  catalogueIds : List OperatorId
  semanticIds : List OperatorId
  missingForms : List String
  deriving Repr

def trigramOperatorAnchors : List TrigramOperatorAnchor :=
  [ { trigram := Trigram.qian, name := "乾", mode := .sheng,
      catalogueIds := [.F_10],       semanticIds := [],      missingForms := [] }
  , { trigram := Trigram.dui,  name := "兑", mode := .kai,
      catalogueIds := [.T_26],       semanticIds := [],      missingForms := [] }
  , { trigram := Trigram.li,   name := "离", mode := .xian,
      catalogueIds := [.R_18],       semanticIds := [],      missingForms := ["丽"] }
  , { trigram := Trigram.zhen, name := "震", mode := .yuan,
      catalogueIds := [.F_10],       semanticIds := [],      missingForms := ["震"] }
  , { trigram := Trigram.xun,  name := "巽", mode := .shen,
      catalogueIds := [.F_8, .Y_20], semanticIds := [],      missingForms := [] }
  , { trigram := Trigram.kan,  name := "坎", mode := .sai,
      catalogueIds := [.M_9],        semanticIds := [],      missingForms := [] }
  , { trigram := Trigram.gen,  name := "艮", mode := .ju,
      catalogueIds := [.B_4],        semanticIds := [],      missingForms := [] }
  , { trigram := Trigram.kun,  name := "坤", mode := .shou,
      catalogueIds := [.C_3],        semanticIds := [],      missingForms := [] }
  ]

theorem trigramOperatorAnchors_length :
    trigramOperatorAnchors.length = 8 := by
  native_decide

theorem trigramOperatorAnchors_cover_all :
    trigramOperatorAnchors.map (·.trigram) = Trigram.all := by
  native_decide

theorem trigramOperatorAnchors_modes :
    trigramOperatorAnchors.map (·.mode) =
      trigramOperatorAnchors.map (fun a => a.trigram.jianMode) := by
  native_decide

/-! ## § 6 64 hexagram operator anchors -/

/--
One row of the `64 卦 ↔ 算子` bridge.

`ordinal` is zero-based and points into `xuGua`; `number = ordinal + 1` recovers
the traditional Zhouyi order number.
-/
structure HexagramOperatorAnchor where
  ordinal : Fin 64
  name : String
  catalogueIds : List OperatorId
  semanticIds : List OperatorId
  missingForms : List String
  deriving Repr

namespace HexagramOperatorAnchor

def number (a : HexagramOperatorAnchor) : Nat := a.ordinal.val + 1

def hexagram (a : HexagramOperatorAnchor) : Hexagram :=
  xuGua.get ⟨a.ordinal.val, by
    rw [xuGua_length]
    exact a.ordinal.isLt⟩

def hasCatalogueId (a : HexagramOperatorAnchor) : Bool :=
  !a.catalogueIds.isEmpty

def hasGap (a : HexagramOperatorAnchor) : Bool :=
  !a.missingForms.isEmpty

end HexagramOperatorAnchor

def hexAnchor (n : Nat) (h : n < 64) (name : String)
    (catalogueIds semanticIds : List OperatorId) (missingForms : List String) :
    HexagramOperatorAnchor :=
  { ordinal := ⟨n, h⟩
  , name := name
  , catalogueIds := catalogueIds
  , semanticIds := semanticIds
  , missingForms := missingForms
  }

/--
The full 64-row bridge from `xuGua` positions to text-catalogue operator ids.
Rows keep only still-unadmitted documentary words in `missingForms`.
-/
def hexagramOperatorAnchors : List HexagramOperatorAnchor :=
  [ hexAnchor 0  (by decide) "乾"   [.F_10]              []        []
  , hexAnchor 1  (by decide) "坤"   [.C_3]               []        []
  , hexAnchor 2  (by decide) "屯"   [.B_1, .F_17]        []        []
  , hexAnchor 3  (by decide) "蒙"   [.Z_37]              []        []
  , hexAnchor 4  (by decide) "需"   [.F_13]              [.B_4]    []
  , hexAnchor 5  (by decide) "讼"   [.R_16]              []        []
  , hexAnchor 6  (by decide) "师"   [.Z_16, .F_10]       []        []
  , hexAnchor 7  (by decide) "比"   [.R_8]               []        []
  , hexAnchor 8  (by decide) "小畜" [.T_16]              [.Z_19]   ["小"]
  , hexAnchor 9  (by decide) "履"   [.F_9, .X_6]         []        []
  , hexAnchor 10 (by decide) "泰"   [.F_12]              []        []
  , hexAnchor 11 (by decide) "否"   [.F_14]              [.F_12]   []
  , hexAnchor 12 (by decide) "同人" [.I_1]               []        []
  , hexAnchor 13 (by decide) "大有" [.Q_6]               []        ["大"]
  , hexAnchor 14 (by decide) "谦"   [.T_12]              []        []
  , hexAnchor 15 (by decide) "豫"   [.T_17]              []        []
  , hexAnchor 16 (by decide) "随"   [.F_15]              []        []
  , hexAnchor 17 (by decide) "蛊"   [.Y_28]              []        []
  , hexAnchor 18 (by decide) "临"   [.R_17]              []        []
  , hexAnchor 19 (by decide) "观"   [.Z_34]              []        []
  , hexAnchor 20 (by decide) "噬嗑" [.T_18, .T_19]       []        []
  , hexAnchor 21 (by decide) "贲"   [.T_20]              []        []
  , hexAnchor 22 (by decide) "剥"   [.T_12]              []        []
  , hexAnchor 23 (by decide) "复"   [.T_7]               []        []
  , hexAnchor 24 (by decide) "无妄" [.L_8]               []        []
  , hexAnchor 25 (by decide) "大畜" [.T_16]              [.Z_19]   ["大"]
  , hexAnchor 26 (by decide) "颐"   [.T_21]              []        []
  , hexAnchor 27 (by decide) "大过" [.T_22]              []        ["大"]
  , hexAnchor 28 (by decide) "坎"   [.M_9]               []        []
  , hexAnchor 29 (by decide) "离"   [.R_18]              []        ["丽"]
  , hexAnchor 30 (by decide) "咸"   [.R_19]              [.R_7]    []
  , hexAnchor 31 (by decide) "恒"   [.P_6]               []        []
  , hexAnchor 32 (by decide) "遁"   [.F_4, .Z_8]         []        []
  , hexAnchor 33 (by decide) "大壮" [.T_23]              []        ["大"]
  , hexAnchor 34 (by decide) "晋"   [.F_3, .Z_36]        []        []
  , hexAnchor 35 (by decide) "明夷" [.Z_37]              []        []
  , hexAnchor 36 (by decide) "家人" [.C_6]               []        []
  , hexAnchor 37 (by decide) "睽"   [.N_7]               []        []
  , hexAnchor 38 (by decide) "蹇"   [.M_10]              [.B_4]    []
  , hexAnchor 39 (by decide) "解"   [.X_13]              []        []
  , hexAnchor 40 (by decide) "损"   [.T_12]              []        []
  , hexAnchor 41 (by decide) "益"   [.T_13]              []        []
  , hexAnchor 42 (by decide) "夬"   [.T_18]              []        []
  , hexAnchor 43 (by decide) "姤"   [.R_20]              []        []
  , hexAnchor 44 (by decide) "萃"   [.Z_16]              []        []
  , hexAnchor 45 (by decide) "升"   [.F_5]               []        []
  , hexAnchor 46 (by decide) "困"   [.M_11]              []        []
  , hexAnchor 47 (by decide) "井"   []                   []        ["井"]
  , hexAnchor 48 (by decide) "革"   [.T_4]               []        []
  , hexAnchor 49 (by decide) "鼎"   []                   [.B_5]    ["鼎"]
  , hexAnchor 50 (by decide) "震"   [.F_10]              []        ["震"]
  , hexAnchor 51 (by decide) "艮"   [.B_4]               []        []
  , hexAnchor 52 (by decide) "渐"   [.A_1]               []        []
  , hexAnchor 53 (by decide) "归妹" [.T_24]              [.T_7]    []
  , hexAnchor 54 (by decide) "丰"   [.T_25]              []        []
  , hexAnchor 55 (by decide) "旅"   [.F_9, .F_16]        []        []
  , hexAnchor 56 (by decide) "巽"   [.F_8, .Y_20]        []        []
  , hexAnchor 57 (by decide) "兑"   [.T_26]              []        []
  , hexAnchor 58 (by decide) "涣"   [.Z_18]              []        []
  , hexAnchor 59 (by decide) "节"   [.B_8]               []        []
  , hexAnchor 60 (by decide) "中孚" [.M_12]              []        []
  , hexAnchor 61 (by decide) "小过" [.T_22]              []        ["小"]
  , hexAnchor 62 (by decide) "既济" [.S_9, .B_6]         []        []
  , hexAnchor 63 (by decide) "未济" [.S_17, .B_6]        []        []
  ]

theorem hexagramOperatorAnchors_length :
    hexagramOperatorAnchors.length = 64 := by
  native_decide

theorem hexagramOperatorAnchor_ordinals :
    hexagramOperatorAnchors.map (fun a => a.ordinal.val) = List.range 64 := by
  native_decide

def anchoredHexagrams : List Hexagram :=
  hexagramOperatorAnchors.map HexagramOperatorAnchor.hexagram

theorem anchoredHexagrams_eq_xuGua : anchoredHexagrams = xuGua := by
  native_decide

def hexagramAnchorsWithCatalogue : List HexagramOperatorAnchor :=
  hexagramOperatorAnchors.filter HexagramOperatorAnchor.hasCatalogueId

def hexagramAnchorsWithGaps : List HexagramOperatorAnchor :=
  hexagramOperatorAnchors.filter HexagramOperatorAnchor.hasGap

theorem hexagramAnchorsWithCatalogue_length :
    hexagramAnchorsWithCatalogue.length = 62 := by
  native_decide

theorem hexagramAnchorsWithGaps_length :
    hexagramAnchorsWithGaps.length = 10 := by
  native_decide

theorem hexagramAnchor_numbers_range :
    hexagramOperatorAnchors.all
      (fun a => decide (1 <= a.number ∧ a.number <= 64)) = true := by
  native_decide

theorem hexagramAnchorsWithCatalogue_all_have_catalogueId :
    hexagramAnchorsWithCatalogue.all HexagramOperatorAnchor.hasCatalogueId = true := by
  native_decide

theorem hexagramAnchorsWithGaps_all_have_gap :
    hexagramAnchorsWithGaps.all HexagramOperatorAnchor.hasGap = true := by
  native_decide

/-- All documentary words from the 64-hexagram table that still lack exact `OperatorId`s. -/
def hexagramMissingForms : List String :=
  hexagramOperatorAnchors.flatMap (·.missingForms)

/-- Deduplicated vocabulary of still-missing 64-hexagram operator words. -/
def hexagramMissingVocabulary : List String :=
  ["丽", "井", "鼎", "震", "大", "小"]

theorem hexagramMissingForms_length :
    hexagramMissingForms.length = 10 := by
  native_decide

theorem hexagramMissingVocabulary_length :
    hexagramMissingVocabulary.length = 6 := by
  native_decide

theorem hexagramMissingVocabulary_nodup :
    hexagramMissingVocabulary.Nodup := by
  native_decide

/-- Every current gap word is accounted for by the deduplicated vocabulary. -/
theorem hexagramMissingForms_in_vocabulary :
    hexagramMissingForms.all (fun s => hexagramMissingVocabulary.contains s) = true := by
  native_decide

/-!
The remaining missing vocabulary is not all the same kind of gap.  Some words
are parameters, and some are hexagram/trigram-specific image words.  The former
general-operator gap words are listed separately in `hexagramGapPromotions`.
-/
inductive MissingFormDisposition where
  | generalOperator
  | parameter
  | hexagramSpecific
  deriving Repr, DecidableEq, BEq

structure MissingFormPolicy where
  form : String
  disposition : MissingFormDisposition
  suggestedGroup : Option OperatorGroup
  semanticIds : List OperatorId
  deriving Repr

/-- Conservative policy for the 6 still-missing 64-hexagram gap words. -/
def hexagramMissingPolicies : List MissingFormPolicy :=
  [ { form := "丽", disposition := .hexagramSpecific, suggestedGroup := none, semanticIds := [] }
  , { form := "井", disposition := .hexagramSpecific, suggestedGroup := none, semanticIds := [] }
  , { form := "鼎", disposition := .hexagramSpecific, suggestedGroup := none, semanticIds := [.B_5] }
  , { form := "震", disposition := .hexagramSpecific, suggestedGroup := none, semanticIds := [.F_10] }
  , { form := "大", disposition := .parameter, suggestedGroup := none, semanticIds := [] }
  , { form := "小", disposition := .parameter, suggestedGroup := none, semanticIds := [] }
  ]

def hexagramMissingGeneralForms : List String :=
  (hexagramMissingPolicies.filter
    (fun p => p.disposition == MissingFormDisposition.generalOperator)).map (·.form)

def hexagramMissingParameterForms : List String :=
  (hexagramMissingPolicies.filter
    (fun p => p.disposition == MissingFormDisposition.parameter)).map (·.form)

def hexagramMissingSpecificForms : List String :=
  (hexagramMissingPolicies.filter
    (fun p => p.disposition == MissingFormDisposition.hexagramSpecific)).map (·.form)

theorem hexagramMissingPolicies_length :
    hexagramMissingPolicies.length = 6 := by
  native_decide

theorem hexagramMissingPolicies_cover_vocabulary :
    hexagramMissingPolicies.map (·.form) = hexagramMissingVocabulary := by
  native_decide

theorem hexagramMissingGeneralForms_length :
    hexagramMissingGeneralForms.length = 0 := by
  native_decide

theorem hexagramMissingParameterForms_eq :
    hexagramMissingParameterForms = ["大", "小"] := by
  native_decide

theorem hexagramMissingSpecificForms_eq :
    hexagramMissingSpecificForms = ["丽", "井", "鼎", "震"] := by
  native_decide

/-!
The policy split above is reflected in a small promotion layer.  These rows are
the 25 former gap words that now have exact catalogue entries, with the target
catalogue group and id audited.
-/
structure HexagramGapPromotion where
  form : String
  targetGroup : OperatorGroup
  targetId : OperatorId
  deriving Repr

/-- Conservative catalogue-admission subset of the original 31 hexagram gap words. -/
def hexagramGapPromotions : List HexagramGapPromotion :=
  [ { form := "待", targetGroup := .F, targetId := .F_13 }
  , { form := "争", targetGroup := .R, targetId := .R_16 }
  , { form := "蓄", targetGroup := .T, targetId := .T_16 }
  , { form := "塞", targetGroup := .F, targetId := .F_14 }
  , { form := "备", targetGroup := .T, targetId := .T_17 }
  , { form := "从", targetGroup := .F, targetId := .F_15 }
  , { form := "临", targetGroup := .R, targetId := .R_17 }
  , { form := "决", targetGroup := .T, targetId := .T_18 }
  , { form := "断", targetGroup := .T, targetId := .T_19 }
  , { form := "饰", targetGroup := .T, targetId := .T_20 }
  , { form := "养", targetGroup := .T, targetId := .T_21 }
  , { form := "过", targetGroup := .T, targetId := .T_22 }
  , { form := "险", targetGroup := .M, targetId := .M_9 }
  , { form := "附", targetGroup := .R, targetId := .R_18 }
  , { form := "感", targetGroup := .R, targetId := .R_19 }
  , { form := "壮", targetGroup := .T, targetId := .T_23 }
  , { form := "难", targetGroup := .M, targetId := .M_10 }
  , { form := "遇", targetGroup := .R, targetId := .R_20 }
  , { form := "困", targetGroup := .M, targetId := .M_11 }
  , { form := "归", targetGroup := .T, targetId := .T_24 }
  , { form := "丰", targetGroup := .T, targetId := .T_25 }
  , { form := "远", targetGroup := .F, targetId := .F_16 }
  , { form := "悦", targetGroup := .T, targetId := .T_26 }
  , { form := "信", targetGroup := .M, targetId := .M_12 }
  , { form := "阻", targetGroup := .F, targetId := .F_17 }
  ]

def hexagramPromotedGapForms : List String :=
  hexagramGapPromotions.map (·.form)

def hexagramUnpromotedGapForms : List String :=
  hexagramMissingSpecificForms ++ hexagramMissingParameterForms

theorem hexagramGapPromotions_length :
    hexagramGapPromotions.length = 25 := by
  native_decide

theorem hexagramPromotedGapForms_eq :
    hexagramPromotedGapForms =
      ["待", "争", "蓄", "塞", "备", "从", "临", "决", "断", "饰",
       "养", "过", "险", "附", "感", "壮", "难", "遇", "困", "归",
       "丰", "远", "悦", "信", "阻"] := by
  native_decide

theorem hexagramGapPromotions_match_targets :
    hexagramGapPromotions.map (fun p => (p.form, p.targetGroup, p.targetId)) =
      [ ("待", .F, .F_13), ("争", .R, .R_16), ("蓄", .T, .T_16),
        ("塞", .F, .F_14), ("备", .T, .T_17), ("从", .F, .F_15),
        ("临", .R, .R_17), ("决", .T, .T_18), ("断", .T, .T_19),
        ("饰", .T, .T_20), ("养", .T, .T_21), ("过", .T, .T_22),
        ("险", .M, .M_9), ("附", .R, .R_18), ("感", .R, .R_19),
        ("壮", .T, .T_23), ("难", .M, .M_10), ("遇", .R, .R_20),
        ("困", .M, .M_11), ("归", .T, .T_24), ("丰", .T, .T_25),
        ("远", .F, .F_16), ("悦", .T, .T_26), ("信", .M, .M_12),
        ("阻", .F, .F_17) ] := by
  native_decide

theorem hexagramGapPromotions_target_ids_catalogue :
    hexagramGapPromotions.all (fun p => decide (p.targetId ∈ allOperatorIds)) = true := by
  native_decide

theorem hexagramGapPromotions_target_groups_match :
    hexagramGapPromotions.all (fun p => decide (p.targetId.group = p.targetGroup)) = true := by
  native_decide

theorem hexagramPromotedGapForms_not_missing :
    hexagramPromotedGapForms.all
      (fun s => !hexagramMissingVocabulary.contains s) = true := by
  native_decide

theorem hexagramUnpromotedGapForms_eq :
    hexagramUnpromotedGapForms = ["丽", "井", "鼎", "震", "大", "小"] := by
  native_decide

theorem hexagramUnpromotedGapForms_are_missing :
    hexagramUnpromotedGapForms.all
      (fun s => hexagramMissingVocabulary.contains s) = true := by
  native_decide

theorem hexagramPromotedGapForms_exclude_unpromoted :
    hexagramPromotedGapForms.all
      (fun s => !hexagramUnpromotedGapForms.contains s) = true := by
  native_decide

theorem hexagramPromotionPartition_count :
    hexagramPromotedGapForms.length + hexagramUnpromotedGapForms.length =
      31 := by
  native_decide

/-!
Some original gap forms have nearby semantic anchors that are not exact
catalogue ids.  Keeping this list separate prevents accidental promotion of a
synonym, compound, or image word into `catalogueIds`.
-/
structure NearMissAnchor where
  missingForm : String
  semanticIds : List OperatorId
  reason : String
  deriving Repr

/-- Auditable near-miss cases among the original 31 64-hexagram gap words. -/
def hexagramNearMissAnchors : List NearMissAnchor :=
  [ { missingForm := "蓄", semanticIds := [.Z_19], reason := "near 积/accumulation, not exact 蓄" }
  , { missingForm := "塞", semanticIds := [.F_12], reason := "opposite/obstruction near 通, not exact 塞" }
  , { missingForm := "感", semanticIds := [.R_7], reason := "near 应/correspondence, not exact 感" }
  , { missingForm := "难", semanticIds := [.B_4], reason := "near 止/block, not exact 难" }
  , { missingForm := "鼎", semanticIds := [.B_5], reason := "near 立/standing vessel image, not exact 鼎" }
  , { missingForm := "震", semanticIds := [.F_10], reason := "near 动/initiation, not exact 震" }
  , { missingForm := "归", semanticIds := [.T_7], reason := "near 复/return, not exact 归" }
  ]

def hexagramNearMissForms : List String :=
  hexagramNearMissAnchors.map (·.missingForm)

theorem hexagramNearMissAnchors_length :
    hexagramNearMissAnchors.length = 7 := by
  native_decide

theorem hexagramNearMissForms_eq :
    hexagramNearMissForms = ["蓄", "塞", "感", "难", "鼎", "震", "归"] := by
  native_decide

theorem hexagramNearMissForms_accounted :
    hexagramNearMissForms.all
      (fun s => (hexagramPromotedGapForms ++ hexagramUnpromotedGapForms).contains s) = true := by
  native_decide

theorem hexagramNearMissSemanticIds_nonempty :
    hexagramNearMissAnchors.all (fun a => !a.semanticIds.isEmpty) = true := by
  native_decide

/-! ## § 7 192 Cell anchors -/

structure CellOperatorAnchor where
  hexagramAnchor : HexagramOperatorAnchor
  shi : Shi
  deriving Repr

namespace CellOperatorAnchor

def cell (a : CellOperatorAnchor) : Cell192 :=
  (a.hexagramAnchor.hexagram, a.shi)

def hexagramNumber (a : CellOperatorAnchor) : Nat :=
  a.hexagramAnchor.number

end CellOperatorAnchor

/-- The 64 hexagram anchors lifted across the three `Shi` states. -/
def cellOperatorAnchors : List CellOperatorAnchor :=
  hexagramOperatorAnchors.flatMap fun h =>
    shiAnchors.map fun s => { hexagramAnchor := h, shi := s.shi }

def anchoredCells : List Cell192 :=
  cellOperatorAnchors.map CellOperatorAnchor.cell

def cellCovered (c : Cell192) : Bool :=
  anchoredCells.any fun d => d == c

theorem cellOperatorAnchors_length :
    cellOperatorAnchors.length = 192 := by
  native_decide

theorem cellOperatorAnchors_length_eq_cell192 :
    cellOperatorAnchors.length = Cell192.all.length := by
  rw [cellOperatorAnchors_length, Cell192.all_length]

theorem anchoredCells_nodup :
    anchoredCells.Nodup := by
  native_decide

theorem cellOperatorAnchor_hexagram_numbers_range :
    cellOperatorAnchors.all
      (fun a => decide (1 <= a.hexagramNumber ∧ a.hexagramNumber <= 64)) = true := by
  native_decide

theorem cellOperatorAnchors_cover_all (c : Cell192) :
    cellCovered c = true := by
  rcases c with ⟨⟨y1, y2, y3, y4, y5, y6⟩, s⟩
  cases y1 <;> cases y2 <;> cases y3 <;>
    cases y4 <;> cases y5 <;> cases y6 <;> cases s <;>
    native_decide

/--
Machine-checkable summary: reserved tokens, L0 instructions, Shi, yao
positions, position relations, all 64 `xuGua` positions, and all 192
hexagram-time cells now have explicit anchor rows.
-/
theorem bagua_operator_anchor_summary :
    reservedTokenAnchors.length = reservedTokens.length
    ∧ reservedTokenAnchors.map (·.token) = reservedTokens
    ∧ l0OperatorAnchors.length = primaryTokens.length
    ∧ shiAnchors.length = Shi.all.length
    ∧ yaoPositionAnchors.length = 6
    ∧ positionRelationAnchors.length = 6
    ∧ trigramOperatorAnchors.length = Trigram.all.length
    ∧ trigramOperatorAnchors.map (·.trigram) = Trigram.all
    ∧ hexagramOperatorAnchors.length = xuGua.length
    ∧ anchoredHexagrams = xuGua
    ∧ hexagramOperatorAnchors.all
        (fun a => decide (1 <= a.number ∧ a.number <= 64)) = true
    ∧ hexagramMissingVocabulary.length = 6
    ∧ hexagramMissingForms.all (fun s => hexagramMissingVocabulary.contains s) = true
    ∧ hexagramMissingPolicies.map (·.form) = hexagramMissingVocabulary
    ∧ hexagramMissingGeneralForms.length = 0
    ∧ hexagramGapPromotions.length = 25
    ∧ hexagramGapPromotions.all (fun p => decide (p.targetId ∈ allOperatorIds)) = true
    ∧ hexagramGapPromotions.all (fun p => decide (p.targetId.group = p.targetGroup)) = true
    ∧ hexagramPromotedGapForms.all
        (fun s => !hexagramMissingVocabulary.contains s) = true
    ∧ hexagramUnpromotedGapForms = ["丽", "井", "鼎", "震", "大", "小"]
    ∧ hexagramPromotedGapForms.all
        (fun s => !hexagramUnpromotedGapForms.contains s) = true
    ∧ hexagramNearMissAnchors.length = 7
    ∧ hexagramNearMissForms.all
        (fun s => (hexagramPromotedGapForms ++ hexagramUnpromotedGapForms).contains s) = true
    ∧ cellOperatorAnchors.length = Cell192.all.length
    ∧ anchoredCells.Nodup
    ∧ cellOperatorAnchors.all
        (fun a => decide (1 <= a.hexagramNumber ∧ a.hexagramNumber <= 64)) = true
    ∧ (∀ c : Cell192, cellCovered c = true) := by
  exact
    ⟨ by rw [reservedTokenAnchors_length, reservedTokens_length]
    , reservedTokenAnchor_tokens_eq_reservedTokens
    , by rw [l0OperatorAnchors_length, primaryTokens_length]
    , by rw [shiAnchors_length, Shi.all_length]
    , yaoPositionAnchors_length
    , positionRelationAnchors_length
    , by rw [trigramOperatorAnchors_length, Trigram.all_length]
    , trigramOperatorAnchors_cover_all
    , by rw [hexagramOperatorAnchors_length, xuGua_length]
    , anchoredHexagrams_eq_xuGua
    , hexagramAnchor_numbers_range
    , hexagramMissingVocabulary_length
    , hexagramMissingForms_in_vocabulary
    , hexagramMissingPolicies_cover_vocabulary
    , hexagramMissingGeneralForms_length
    , hexagramGapPromotions_length
    , hexagramGapPromotions_target_ids_catalogue
    , hexagramGapPromotions_target_groups_match
    , hexagramPromotedGapForms_not_missing
    , hexagramUnpromotedGapForms_eq
    , hexagramPromotedGapForms_exclude_unpromoted
    , hexagramNearMissAnchors_length
    , hexagramNearMissForms_accounted
    , cellOperatorAnchors_length_eq_cell192
    , anchoredCells_nodup
    , cellOperatorAnchor_hexagram_numbers_range
    , cellOperatorAnchors_cover_all
    ⟩

end SSBX.Text.OperatorAnchors
