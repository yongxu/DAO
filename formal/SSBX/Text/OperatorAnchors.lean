import SSBX.Text.WenyanOperators
import SSBX.Foundation.Bagua.BaguaWenSpec

/-!
# OperatorAnchors — 文言算子到八卦系统的锚点

This file is the bridge between the text-level `OperatorId` catalogue and the
formal Bagua/Yi layer.  It is intentionally conservative:

* `catalogueIds` records existing `OperatorId` entries.
* `semanticIds` records nearby formal anchors when the hexagram table names a
  variant or derived meaning.
* `missingForms` records words present in the 64-hexagram operator table but not
  yet admitted as Lean `OperatorId`s.
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
      catalogueIds := [],            semanticIds := [],      missingForms := ["悦"] }
  , { trigram := Trigram.li,   name := "离", mode := .xian,
      catalogueIds := [],            semanticIds := [],      missingForms := ["丽", "附"] }
  , { trigram := Trigram.zhen, name := "震", mode := .yuan,
      catalogueIds := [.F_10],       semanticIds := [],      missingForms := ["震"] }
  , { trigram := Trigram.xun,  name := "巽", mode := .shen,
      catalogueIds := [.F_8, .Y_20], semanticIds := [],      missingForms := [] }
  , { trigram := Trigram.kan,  name := "坎", mode := .sai,
      catalogueIds := [],            semanticIds := [],      missingForms := ["险"] }
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
Rows with no exact catalogue id keep the documentary word in `missingForms`.
-/
def hexagramOperatorAnchors : List HexagramOperatorAnchor :=
  [ hexAnchor 0  (by decide) "乾"   [.F_10]              []        []
  , hexAnchor 1  (by decide) "坤"   [.C_3]               []        []
  , hexAnchor 2  (by decide) "屯"   [.B_1]               []        ["阻"]
  , hexAnchor 3  (by decide) "蒙"   [.Z_37]              []        []
  , hexAnchor 4  (by decide) "需"   []                   [.B_4]    ["待"]
  , hexAnchor 5  (by decide) "讼"   []                   []        ["争"]
  , hexAnchor 6  (by decide) "师"   [.Z_16, .F_10]       []        []
  , hexAnchor 7  (by decide) "比"   [.R_8]               []        []
  , hexAnchor 8  (by decide) "小畜" []                   [.Z_19]   ["蓄", "小"]
  , hexAnchor 9  (by decide) "履"   [.F_9, .X_6]         []        []
  , hexAnchor 10 (by decide) "泰"   [.F_12]              []        []
  , hexAnchor 11 (by decide) "否"   []                   [.F_12]   ["塞"]
  , hexAnchor 12 (by decide) "同人" [.I_1]               []        []
  , hexAnchor 13 (by decide) "大有" [.Q_6]               []        ["大"]
  , hexAnchor 14 (by decide) "谦"   [.T_12]              []        []
  , hexAnchor 15 (by decide) "豫"   []                   []        ["备"]
  , hexAnchor 16 (by decide) "随"   []                   []        ["从"]
  , hexAnchor 17 (by decide) "蛊"   [.Y_28]              []        []
  , hexAnchor 18 (by decide) "临"   []                   []        ["临"]
  , hexAnchor 19 (by decide) "观"   [.Z_34]              []        []
  , hexAnchor 20 (by decide) "噬嗑" []                   []        ["决", "断"]
  , hexAnchor 21 (by decide) "贲"   []                   []        ["饰"]
  , hexAnchor 22 (by decide) "剥"   [.T_12]              []        []
  , hexAnchor 23 (by decide) "复"   [.T_7]               []        []
  , hexAnchor 24 (by decide) "无妄" [.L_8]               []        []
  , hexAnchor 25 (by decide) "大畜" []                   [.Z_19]   ["蓄", "大"]
  , hexAnchor 26 (by decide) "颐"   []                   []        ["养"]
  , hexAnchor 27 (by decide) "大过" []                   []        ["过", "大"]
  , hexAnchor 28 (by decide) "坎"   []                   []        ["险"]
  , hexAnchor 29 (by decide) "离"   []                   []        ["丽", "附"]
  , hexAnchor 30 (by decide) "咸"   []                   [.R_7]    ["感"]
  , hexAnchor 31 (by decide) "恒"   [.P_6]               []        []
  , hexAnchor 32 (by decide) "遁"   [.F_4, .Z_8]         []        []
  , hexAnchor 33 (by decide) "大壮" []                   []        ["壮", "大"]
  , hexAnchor 34 (by decide) "晋"   [.F_3, .Z_36]        []        []
  , hexAnchor 35 (by decide) "明夷" [.Z_37]              []        []
  , hexAnchor 36 (by decide) "家人" [.C_6]               []        []
  , hexAnchor 37 (by decide) "睽"   [.N_7]               []        []
  , hexAnchor 38 (by decide) "蹇"   []                   [.B_4]    ["难"]
  , hexAnchor 39 (by decide) "解"   [.X_13]              []        []
  , hexAnchor 40 (by decide) "损"   [.T_12]              []        []
  , hexAnchor 41 (by decide) "益"   [.T_13]              []        []
  , hexAnchor 42 (by decide) "夬"   []                   []        ["决"]
  , hexAnchor 43 (by decide) "姤"   []                   []        ["遇"]
  , hexAnchor 44 (by decide) "萃"   [.Z_16]              []        []
  , hexAnchor 45 (by decide) "升"   [.F_5]               []        []
  , hexAnchor 46 (by decide) "困"   []                   []        ["困"]
  , hexAnchor 47 (by decide) "井"   []                   []        ["井"]
  , hexAnchor 48 (by decide) "革"   [.T_4]               []        []
  , hexAnchor 49 (by decide) "鼎"   []                   [.B_5]    ["鼎"]
  , hexAnchor 50 (by decide) "震"   [.F_10]              []        ["震"]
  , hexAnchor 51 (by decide) "艮"   [.B_4]               []        []
  , hexAnchor 52 (by decide) "渐"   [.A_1]               []        []
  , hexAnchor 53 (by decide) "归妹" []                   [.T_7]    ["归"]
  , hexAnchor 54 (by decide) "丰"   []                   []        ["丰"]
  , hexAnchor 55 (by decide) "旅"   [.F_9]               []        ["远"]
  , hexAnchor 56 (by decide) "巽"   [.F_8, .Y_20]        []        []
  , hexAnchor 57 (by decide) "兑"   []                   []        ["悦"]
  , hexAnchor 58 (by decide) "涣"   [.Z_18]              []        []
  , hexAnchor 59 (by decide) "节"   [.B_8]               []        []
  , hexAnchor 60 (by decide) "中孚" []                   []        ["信"]
  , hexAnchor 61 (by decide) "小过" []                   []        ["过", "小"]
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
    hexagramAnchorsWithCatalogue.length = 37 := by
  native_decide

theorem hexagramAnchorsWithGaps_length :
    hexagramAnchorsWithGaps.length = 31 := by
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

/-- All documentary words from the 64-hexagram table that lack exact `OperatorId`s. -/
def hexagramMissingForms : List String :=
  hexagramOperatorAnchors.flatMap (·.missingForms)

/-- Deduplicated vocabulary of currently missing 64-hexagram operator words. -/
def hexagramMissingVocabulary : List String :=
  ["待", "争", "蓄", "塞", "备", "从", "临", "决", "断", "饰",
   "养", "过", "险", "丽", "附", "感", "壮", "难", "遇", "困",
   "井", "鼎", "震", "归", "丰", "远", "悦", "信", "大", "小", "阻"]

theorem hexagramMissingForms_length :
    hexagramMissingForms.length = 38 := by
  native_decide

theorem hexagramMissingVocabulary_length :
    hexagramMissingVocabulary.length = 31 := by
  native_decide

theorem hexagramMissingVocabulary_nodup :
    hexagramMissingVocabulary.Nodup := by
  native_decide

/-- Every current gap word is accounted for by the deduplicated vocabulary. -/
theorem hexagramMissingForms_in_vocabulary :
    hexagramMissingForms.all (fun s => hexagramMissingVocabulary.contains s) = true := by
  native_decide

/-!
The missing vocabulary is not all the same kind of gap.  Some words are good
candidates for general `OperatorId`s, some are parameters, and some are
hexagram/trigram-specific image words.
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

/-- Conservative policy for the 31 deduplicated 64-hexagram gap words. -/
def hexagramMissingPolicies : List MissingFormPolicy :=
  [ { form := "待", disposition := .generalOperator, suggestedGroup := some .F, semanticIds := [] }
  , { form := "争", disposition := .generalOperator, suggestedGroup := some .R, semanticIds := [] }
  , { form := "蓄", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [.Z_19] }
  , { form := "塞", disposition := .generalOperator, suggestedGroup := some .F, semanticIds := [.F_12] }
  , { form := "备", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "从", disposition := .generalOperator, suggestedGroup := some .F, semanticIds := [] }
  , { form := "临", disposition := .generalOperator, suggestedGroup := some .R, semanticIds := [] }
  , { form := "决", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "断", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "饰", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "养", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "过", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "险", disposition := .generalOperator, suggestedGroup := some .M, semanticIds := [] }
  , { form := "丽", disposition := .hexagramSpecific, suggestedGroup := none, semanticIds := [] }
  , { form := "附", disposition := .generalOperator, suggestedGroup := some .R, semanticIds := [] }
  , { form := "感", disposition := .generalOperator, suggestedGroup := some .R, semanticIds := [.R_7] }
  , { form := "壮", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "难", disposition := .generalOperator, suggestedGroup := some .M, semanticIds := [.B_4] }
  , { form := "遇", disposition := .generalOperator, suggestedGroup := some .R, semanticIds := [] }
  , { form := "困", disposition := .generalOperator, suggestedGroup := some .M, semanticIds := [] }
  , { form := "井", disposition := .hexagramSpecific, suggestedGroup := none, semanticIds := [] }
  , { form := "鼎", disposition := .hexagramSpecific, suggestedGroup := none, semanticIds := [.B_5] }
  , { form := "震", disposition := .hexagramSpecific, suggestedGroup := none, semanticIds := [.F_10] }
  , { form := "归", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [.T_7] }
  , { form := "丰", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "远", disposition := .generalOperator, suggestedGroup := some .F, semanticIds := [] }
  , { form := "悦", disposition := .generalOperator, suggestedGroup := some .T, semanticIds := [] }
  , { form := "信", disposition := .generalOperator, suggestedGroup := some .M, semanticIds := [] }
  , { form := "大", disposition := .parameter, suggestedGroup := none, semanticIds := [] }
  , { form := "小", disposition := .parameter, suggestedGroup := none, semanticIds := [] }
  , { form := "阻", disposition := .generalOperator, suggestedGroup := some .F, semanticIds := [] }
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
    hexagramMissingPolicies.length = 31 := by
  native_decide

theorem hexagramMissingPolicies_cover_vocabulary :
    hexagramMissingPolicies.map (·.form) = hexagramMissingVocabulary := by
  native_decide

theorem hexagramMissingGeneralForms_length :
    hexagramMissingGeneralForms.length = 25 := by
  native_decide

theorem hexagramMissingParameterForms_eq :
    hexagramMissingParameterForms = ["大", "小"] := by
  native_decide

theorem hexagramMissingSpecificForms_eq :
    hexagramMissingSpecificForms = ["丽", "井", "鼎", "震"] := by
  native_decide

/-!
Some missing forms have nearby semantic anchors, but they are not exact
catalogue ids.  Keeping this list separate prevents accidental promotion of a
synonym, compound, or image word into `catalogueIds`.
-/
structure NearMissAnchor where
  missingForm : String
  semanticIds : List OperatorId
  reason : String
  deriving Repr

/-- Auditable near-miss cases among the 31 64-hexagram gap words. -/
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

theorem hexagramNearMissForms_are_missing :
    hexagramNearMissForms.all (fun s => hexagramMissingVocabulary.contains s) = true := by
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
    ∧ hexagramMissingVocabulary.length = 31
    ∧ hexagramMissingForms.all (fun s => hexagramMissingVocabulary.contains s) = true
    ∧ hexagramMissingPolicies.map (·.form) = hexagramMissingVocabulary
    ∧ hexagramMissingGeneralForms.length = 25
    ∧ hexagramNearMissAnchors.length = 7
    ∧ hexagramNearMissForms.all (fun s => hexagramMissingVocabulary.contains s) = true
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
    , hexagramNearMissAnchors_length
    , hexagramNearMissForms_are_missing
    , cellOperatorAnchors_length_eq_cell192
    , anchoredCells_nodup
    , cellOperatorAnchor_hexagram_numbers_range
    , cellOperatorAnchors_cover_all
    ⟩

end SSBX.Text.OperatorAnchors
