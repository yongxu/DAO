/-
# WenSurface.Reading — 单读 resolver (v1)

把 GlyphTok 流映到 ResolvedTok 流。每个 ResolvedTok 携带：
  · 原 GlyphTok（位置 / surface）
  · ResolvedAtom：要么是 hex 常值，要么是 catalogue 算子读法

## 当前范围

解析层默认走 cue-aware resolver：先识别语法 marker / binder / 字面值，
再走 registry-backed executable surface map，最后落到 `OperatorReadings` catalogue。
non-exact catalogue operator 可以进入 symbolic evaluator，但不会被伪装成
Hex/Bool denotation。

## 状态

0 sorry / 0 axiom / 总函数. 关键例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Lex
import SSBX.Foundation.Wen.WenSurface.Semantics
import SSBX.Foundation.Bagua.Cell192
import SSBX.Text.OperatorAnchors
import SSBX.Text.OperatorReadings
import SSBX.Foundation.Yi.YiCore

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.Cell192
open SSBX.Text.OperatorAnchors

/-! ## § 1  Resolved 类型 -/

/-- Surface-level syntax markers that are not value operators by themselves. -/
inductive SyntaxMarker where
  | zhe
  | ling
deriving DecidableEq, Repr

/-- 已消歧的原子：卦字面值 / Bool 字面值 / catalogue 算子读法 /
    应用标记 / 迭代构式. -/
inductive ResolvedAtom where
  | hexConst    (h : Hexagram)
  | boolConst   (b : Bool)
  | varName     (name : String)
  | catalogueOp (reading : OperatorReading)
  | hexOrOp     (h : Hexagram) (reading : OperatorReading)
  | syntax      (marker : SyntaxMarker)
  | appMarker             -- 「之」 等不发射 Tm 的 surface marker
  | iterate               -- 「之又」 迭代构式 marker：F X ↦ F (F X)
  | openBracket
  | closeBracket
deriving DecidableEq, Repr

/-- 已消歧的 token：保留 GlyphTok 与解析结果. -/
structure ResolvedTok where
  tok  : GlyphTok
  atom : ResolvedAtom
deriving DecidableEq, Repr

/-- Resolver 错误。 -/
inductive ResolveErr where
  | noReading (surface : String) (col : Nat) : ResolveErr
  | ambiguous (surface : String) (col : Nat) (candidates : List OperatorReading) : ResolveErr
  | knownButUnsupported (surface : String) (col : Nat) (readings : List OperatorReading) : ResolveErr
  | unpromotedHexagramGap (surface : String) (col : Nat) : ResolveErr
deriving DecidableEq, Repr

/-! ## § 2  Surface maps -/

/-- Surface variables accepted by the prefix-only binder forms. -/
def surfaceVarNames : List String :=
  ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"]

def resolveVarName : Glyph → Option String
  | g => if surfaceVarNames.contains g then some g else none

/-- Canonical King Wen hexagram names, aligned with `Cell192.xuGua`. -/
def canonicalHexNames : List String :=
  [ "乾", "坤", "屯", "蒙", "需", "讼", "师", "比"
  , "小畜", "履", "泰", "否", "同人", "大有", "谦", "豫"
  , "随", "蛊", "临", "观", "噬嗑", "贲", "剥", "复"
  , "无妄", "大畜", "颐", "大过", "坎", "离", "咸", "恒"
  , "遁", "大壮", "晋", "明夷", "家人", "睽", "蹇", "解"
  , "损", "益", "夬", "姤", "萃", "升", "困", "井"
  , "革", "鼎", "震", "艮", "渐", "归妹", "丰", "旅"
  , "巽", "兑", "涣", "节", "中孚", "小过", "既济", "未济" ]

/-- Conservative traditional aliases for full hexagram names. -/
def hexNameAliases : List (String × String) :=
  [ ("訟", "讼"), ("師", "师"), ("謙", "谦"), ("隨", "随")
  , ("蠱", "蛊"), ("臨", "临"), ("觀", "观"), ("賁", "贲")
  , ("剝", "剥"), ("復", "复"), ("無妄", "无妄"), ("頤", "颐")
  , ("過", "过"), ("大過", "大过"), ("小過", "小过")
  , ("離", "离"), ("恆", "恒"), ("晉", "晋"), ("大壯", "大壮")
  , ("損", "损"), ("漸", "渐"), ("歸妹", "归妹"), ("豐", "丰")
  , ("兌", "兑"), ("渙", "涣"), ("節", "节"), ("濟", "济")
  , ("既濟", "既济"), ("未濟", "未济") ]

def lookupStringAssoc? (key : String) : List (String × α) → Option α
  | [] => none
  | (k, v) :: rest => if k = key then some v else lookupStringAssoc? key rest

def canonicalHexNameRows : List (String × Hexagram) :=
  canonicalHexNames.zip xuGua

def canonicalHexForName? (name : String) : Option Hexagram :=
  lookupStringAssoc? name canonicalHexNameRows

def normalizeHexName (name : String) : String :=
  match lookupStringAssoc? name hexNameAliases with
  | some canonical => canonical
  | none => name

def resolveNamedHexConst (g : Glyph) : Option Hexagram :=
  canonicalHexForName? (normalizeHexName g)

def isUnpromotedHexagramGap (g : Glyph) : Bool :=
  hexagramUnpromotedGapForms.contains g

/-- Legacy executable stdlib surface → catalogue reading witness.

Runtime resolution is table/registry-driven through
`uniqueExecutableReadingForGlyph`; this definition is retained as a compact
compatibility check for the original v1 surfaces. -/
def resolveStdlibOp : Glyph → Option OperatorReading
  | "推" => some (catalogueReading "推" "T-10" "对象推进 / 生" (some .T_10)
                    .prefix [.expectedObject])
  | "比" => some (catalogueReading "比" "R-8"  "邻接对应"     (some .R_8)
                    .prefix [.expectedObject])
  | "不" => some (catalogueReading "不" "N-1"  "命题否定"     (some .N_1)
                    .prefix [.expectedProp])
  | "必" => some (catalogueReading "必" "M-1"  "必然 / □"     (some .M_1)
                    .prefix [.modalFrame])
  | "同" => some (catalogueReading "同" "I-1"  "恒等谓词"     (some .I_1)
                    .prefix [.expectedObject])
  | "凡" => some (catalogueReading "凡" "Q-1"  "凡量"         (some .Q_1)
                    .prefix [.quantifierDomain])
  | "損" | "损" =>
      some (catalogueReading "損" "T-12" "减一"         (some .T_12)
                    .prefix [.expectedObject])
  | "益" =>
      some (catalogueReading "益" "T-13" "加一"         (some .T_13)
                    .prefix [.expectedObject])
  | "错" | "錯" =>
      some (catalogueReading "错" "Z-5" "错卦 / 爻位取反" (some .Z_5)
                    .prefix [.expectedObject])
  | "综" | "綜" =>
      some (catalogueReading "综" "Z-6" "综卦 / 爻序反转" (some .Z_6)
                    .prefix [.expectedObject])
  | "互" =>
      some (catalogueReading "互" "Z-3" "互卦 / 中四爻抽取" (some .Z_3)
                    .prefix [.expectedObject])
  | "反" =>
      some (catalogueReading "反" "T-6" "对象层反转" (some .T_6)
                    .prefix [.expectedObject])
  | _   => none

/-- v1+ hex 常值 surface → Hexagram。包含「一」与完整 64 卦名. -/
def resolveHexConst : Glyph → Option Hexagram
  | "一" => some «一»
  | g    => resolveNamedHexConst g

/-- v1 Bool 字面值 surface → Bool。古汉语之「真」/「假」. -/
def resolveBoolConst : Glyph → Option Bool
  | "真" => some true
  | "假" => some false
  | _    => none

/-- 「之」/「以」 等 application marker —— 不发射 Tm，elab 阶段跳过. -/
def isApplicationMarker : Glyph → Bool
  | "之" => true   -- S_1 属格 / function application
  | _    => false

/-- 「之又」迭代构式：surface 之又 双字独立辨认，
    与单字「之」(appMarker) 互不冲突（不同 surface）. -/
def isIterateConstruction : Glyph → Bool
  | "之又" => true
  | _      => false

def resolveSyntaxMarker : Glyph → Option SyntaxMarker
  | "者" => some .zhe
  | "令" => some .ling
  | _    => none

def matchingCloseBracket? : Glyph → Option Glyph
  | "（" => some "）"
  | "("  => some ")"
  | _    => none

def isOpenBracketSurface (g : Glyph) : Bool :=
  (matchingCloseBracket? g).isSome

def isCloseBracketSurface : Glyph → Bool
  | "）" | ")" => true
  | _ => false

def catalogueReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  (readingsForGlyph glyph).filter (fun r => r.status = .catalogue ∧ r.operator?.isSome)

def operatorFormIdsForGlyph (glyph : Glyph) : List OperatorId :=
  allOperatorIds.filter (fun id =>
    (operatorForms id).any (fun sense => sense.glyph = glyph))

def operatorFormReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  (operatorFormIdsForGlyph glyph).map (fun id =>
    catalogueReading glyph id.code id.title (some id) .prefix [.expectedObject])

def operatorCompoundReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  (operatorCompoundSurfaceIds.filter (fun row => row.fst = glyph)).map (fun row =>
    let id := row.snd
    catalogueReading glyph id.code id.title (some id) .prefix [.expectedObject])

def catalogueOrOperatorFormReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  let tableReadings := catalogueReadingsForGlyph glyph
  if tableReadings.isEmpty && !isUnpromotedHexagramGap glyph then
    let compoundReadings := operatorCompoundReadingsForGlyph glyph
    if compoundReadings.isEmpty then operatorFormReadingsForGlyph glyph else compoundReadings
  else
    tableReadings

def executableCatalogueReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  (catalogueReadingsForGlyph glyph).filter (fun r =>
    match r.operator? with
    | some id => (executableSemanticsFor? id).isSome
    | none => false)

def theoremBackedCatalogueReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  (catalogueReadingsForGlyph glyph).filter (fun r =>
    match r.operator? with
    | some id => isTheoremBackedOperator id
    | none => false)

def executableOperatorFormReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  (operatorFormIdsForGlyph glyph).filterMap (fun id =>
    if (executableSemanticsFor? id).isSome then
      some (catalogueReading glyph id.code id.title (some id) .prefix [.expectedObject])
    else
      none)

def theoremBackedOperatorFormReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  (operatorFormIdsForGlyph glyph).filterMap (fun id =>
    if isTheoremBackedOperator id then
      some (catalogueReading glyph id.code id.title (some id) .prefix [.expectedObject])
    else
      none)

def executableSemanticsForReading? (r : OperatorReading) : Option ExecutableSemantics :=
  r.operator?.bind executableSemanticsFor?

def sameExecutableSemantics (sem : ExecutableSemantics) (r : OperatorReading) : Bool :=
  match executableSemanticsForReading? r with
  | some sem' => sem'.arity == sem.arity && decide (sem'.body = sem.body)
  | none => false

/--
Choose a surface reading when all executable candidates collapse to the same
typed body.  This keeps true homographic aliases such as `故` (K-1/S-7) usable
without pretending that different bodies, such as object-level and proposition-
level `反`, have been disambiguated.
-/
def uniqueExecutableReadingBySemantics : List OperatorReading → Option OperatorReading
  | [] => none
  | r :: rest =>
      match executableSemanticsForReading? r with
      | none => none
      | some sem =>
          if rest.all (sameExecutableSemantics sem) then some r else none

def uniqueExecutableCatalogueReading (glyph : Glyph) : Option OperatorReading :=
  let exact := theoremBackedCatalogueReadingsForGlyph glyph
  match uniqueExecutableReadingBySemantics exact with
  | some r => some r
  | none =>
      if exact.isEmpty then
        uniqueExecutableReadingBySemantics (executableCatalogueReadingsForGlyph glyph)
      else
        none

def uniqueExecutableReadingForGlyph (glyph : Glyph) : Option OperatorReading :=
  let exactCatalogue := theoremBackedCatalogueReadingsForGlyph glyph
  match uniqueExecutableReadingBySemantics exactCatalogue with
  | some r => some r
  | none =>
      if exactCatalogue.isEmpty then
        let exactForms := theoremBackedOperatorFormReadingsForGlyph glyph
        match uniqueExecutableReadingBySemantics exactForms with
        | some r => some r
        | none =>
            if exactForms.isEmpty then
              match resolveHexConst glyph with
              | some _ => none
              | none =>
                  let catalogue := executableCatalogueReadingsForGlyph glyph
                  match uniqueExecutableReadingBySemantics catalogue with
                  | some r => some r
                  | none =>
                      if catalogue.isEmpty then
                        uniqueExecutableReadingBySemantics (executableOperatorFormReadingsForGlyph glyph)
                      else
                        none
            else
              none
      else
        none

def resolveCatalogueByTable (t : GlyphTok) : Except ResolveErr ResolvedTok :=
  if isUnpromotedHexagramGap t.surface then
    .error (.unpromotedHexagramGap t.surface t.startCol)
  else
    let readings := catalogueOrOperatorFormReadingsForGlyph t.surface
    match readings with
    | [] =>
        let knownReadings := readingsForGlyph t.surface
        if knownReadings.isEmpty then
          .error (.noReading t.surface t.startCol)
        else
          .error (.knownButUnsupported t.surface t.startCol knownReadings)
    | [r] => .ok ⟨t, .catalogueOp r⟩
    | rs  => .error (.ambiguous t.surface t.startCol rs)

/-! ## § 3  Resolver -/

/-- 单 token resolver。优先级：iterate (「之又」) → appMarker (「之」) → bool 常值 →
    hex 常值 → stdlib 算子；全失败则 `.noReading`.

    注：「之又」与「之」是不同 GlyphTok surface（多字 vs 单字 lex 输出），
    优先序无歧义；此处先判 iterate 仅为可读性. -/
def resolveOne (t : GlyphTok) : Except ResolveErr ResolvedTok :=
  if isOpenBracketSurface t.surface then
    .ok ⟨t, .openBracket⟩
  else if isCloseBracketSurface t.surface then
    .ok ⟨t, .closeBracket⟩
  else if isIterateConstruction t.surface then
    .ok ⟨t, .iterate⟩
  else if isApplicationMarker t.surface then
    .ok ⟨t, .appMarker⟩
  else match resolveSyntaxMarker t.surface with
  | some marker => .ok ⟨t, .syntax marker⟩
  | none =>
  match resolveVarName t.surface with
  | some name => .ok ⟨t, .varName name⟩
  | none =>
  match resolveBoolConst t.surface with
  | some b => .ok ⟨t, .boolConst b⟩
  | none =>
    match uniqueExecutableReadingForGlyph t.surface with
    | some r =>
        match resolveHexConst t.surface with
        | some h => .ok ⟨t, .hexOrOp h r⟩
        | none   => .ok ⟨t, .catalogueOp r⟩
    | none =>
      match resolveHexConst t.surface with
      | some h => .ok ⟨t, .hexConst h⟩
      | none   => resolveCatalogueByTable t

/-- 全 token 列表 resolver。结构递归，总函数. -/
def resolveSimple : List GlyphTok → Except ResolveErr (List ResolvedTok)
  | []       => .ok []
  | t :: ts  =>
    match resolveOne t with
    | .error e => .error e
    | .ok r =>
      match resolveSimple ts with
      | .error e  => .error e
      | .ok rs    => .ok (r :: rs)

/-- 顶层 entry：String → ResolvedTok 流，串接 lex 与 resolve. -/
def lexAndResolve (s : String)
    : Except (LexErr ⊕ ResolveErr) (List ResolvedTok) :=
  match lexWen s with
  | .error e => .error (.inl e)
  | .ok toks =>
    match resolveSimple toks with
    | .error e => .error (.inr e)
    | .ok rs   => .ok rs

/-! ## § 4  Helper：从 ResolvedTok 抽 atom 列表 -/

/-- 从 resolve 结果抽 atom 序列（丢弃位置信息）. -/
def atomsOf : List ResolvedTok → List ResolvedAtom :=
  List.map (·.atom)

/-- 从 ResolvedAtom 抽 OperatorId（仅对 catalogueOp 有效）. -/
def ResolvedAtom.opId? : ResolvedAtom → Option OperatorId
  | .hexConst _    => none
  | .boolConst _   => none
  | .varName _     => none
  | .catalogueOp r => r.operator?
  | .hexOrOp _ r   => r.operator?
  | .syntax _      => none
  | .appMarker     => none
  | .iterate       => none
  | .openBracket   => none
  | .closeBracket  => none

/-- 判别 atom 是否为 appMarker（elab 阶段用）. -/
def ResolvedAtom.isAppMarker : ResolvedAtom → Bool
  | .appMarker => true
  | _          => false

/-! ## § 5  Sanity 例子 (native_decide) -/

/-- Helper: 提取 atom 的 OperatorId（hexConst → none）. -/
private def opIdsOf (s : String) : Option (List (Option OperatorId)) :=
  (lexAndResolve s).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?))

/-- 「推」单独 → catalogueOp T_10. -/
example : opIdsOf "推" = some [some OperatorId.T_10] := by native_decide

/-- 「一」单独 → hexConst «一». -/
example : opIdsOf "一" = some [none] := by native_decide

/-- 基础 stdlib 算子 + 「一」全打通. -/
example :
    opIdsOf "推 比 不 必 同 凡 一"
      = some [some OperatorId.T_10, some OperatorId.R_8, some OperatorId.N_1,
              some OperatorId.M_1,  some OperatorId.I_1, some OperatorId.Q_1,
              none] :=
  by native_decide

/-- 「推 一」流：T_10 + hex const «一». -/
example :
    opIdsOf "推 一" = some [some OperatorId.T_10, none] :=
  by native_decide

/-- 「乾」 → hexConst Hexagram.qian. -/
example : opIdsOf "乾" = some [none] := by native_decide

/-- 「坤」 → hexConst Hexagram.kun. -/
example : opIdsOf "坤" = some [none] := by native_decide

/-- 「推 乾」 → T_10 + qian. -/
example : opIdsOf "推 乾" = some [some OperatorId.T_10, none] := by native_decide

/-- 「推 之 一」 → T_10 + appMarker + 一. -/
example : opIdsOf "推 之 一" = some [some OperatorId.T_10, none, none] := by native_decide

/-- 「之」 单独识别为 appMarker. -/
example :
    ((lexAndResolve "之").toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.isAppMarker)))
      = some [true] :=
  by native_decide

/-- 「之又」识别为 iterate atom（与单字「之」不同 surface, 不冲突）. -/
example :
    ((lexAndResolve "之又").toOption.map (fun rs => rs.map (·.atom)))
      = some [.iterate] :=
  by native_decide

/-- 未知 surface → ResolveErr. -/
example : opIdsOf "瓜" = none := by native_decide

/-- 空串 → 空 list. -/
example : opIdsOf "" = some [] := by native_decide

/-! ## § 6  结构性断言 -/

/-- Legacy stdlib witness still covers the first six v1 surfaces. -/
example : (["推", "比", "不", "必", "同", "凡"].all
            (resolveStdlibOp · |>.isSome)) = true := by native_decide

/-- Hex 常值 map. -/
theorem canonicalHexNames_length :
    canonicalHexNames.length = 64 := by native_decide

theorem canonicalHexNameRows_length :
    canonicalHexNameRows.length = 64 := by native_decide

theorem canonicalHexNameRows_hexagrams_eq_xuGua :
    canonicalHexNameRows.map Prod.snd = xuGua := by native_decide

def lexesAsSingleSurface (s : String) : Bool :=
  match lexWen s with
  | .ok [tok] =>
      (tok.surface == s)
        && (tok.startCol == 0)
        && (tok.width == s.toList.length)
        && (tok.isMulti == decide (s.toList.length > 1))
  | _ => false

theorem canonicalMultiHexNames_lex_as_single :
    (canonicalHexNames.filter (fun s => decide (s.toList.length > 1))).all
        lexesAsSingleSurface = true := by
  native_decide

theorem hexNameAliasSurfaces_lex_as_single :
    ((hexNameAliases.map Prod.fst).filter (fun s => decide (s.toList.length > 1))).all
        lexesAsSingleSurface = true := by
  native_decide

example : resolveHexConst "一" = some «一»          := by native_decide
example : resolveHexConst "乾" = some Hexagram.qian := by native_decide
example : resolveHexConst "坤" = some Hexagram.kun  := by native_decide
example : resolveHexConst "大壯" = resolveHexConst "大壮" := by native_decide
example : resolveHexConst "推" = none               := by native_decide
example : isUnpromotedHexagramGap "鼎" = true := by native_decide
example : isUnpromotedHexagramGap "丽" = true := by native_decide
example : isUnpromotedHexagramGap "益" = false := by native_decide
example :
    (uniqueExecutableCatalogueReading "推").bind (·.operator?) = some OperatorId.T_10 :=
  by native_decide
example :
    (uniqueExecutableCatalogueReading "同").bind (·.operator?) = some OperatorId.I_1 :=
  by native_decide
example :
    (uniqueExecutableCatalogueReading "益").bind (·.operator?) = some OperatorId.T_13 :=
  by native_decide
example :
    (uniqueExecutableReadingForGlyph "错").bind (·.operator?) = some OperatorId.Z_5 :=
  by native_decide
example :
    (uniqueExecutableReadingForGlyph "反").bind (·.operator?) = some OperatorId.T_6 :=
  by native_decide
theorem executableSurfaceReadings_use_registry_path :
    (["推", "比", "不", "必", "同", "凡", "損", "损", "益",
      "错", "錯", "综", "綜", "互", "反"].all
        (fun s => (uniqueExecutableReadingForGlyph s).isSome)) = true := by
  native_decide

theorem executableSurfaceReadings_table_driven_ids :
    (["推", "比", "不", "必", "同", "凡", "損", "损", "益",
      "错", "錯", "综", "綜", "互", "反"].filterMap
        (fun s => (uniqueExecutableReadingForGlyph s).bind (·.operator?)))
      = [ OperatorId.T_10, OperatorId.R_8, OperatorId.N_1,
          OperatorId.M_1, OperatorId.I_1, OperatorId.Q_1,
          OperatorId.T_12, OperatorId.T_12, OperatorId.T_13,
          OperatorId.Z_5, OperatorId.Z_5, OperatorId.Z_6,
          OperatorId.Z_6, OperatorId.Z_3, OperatorId.T_6 ] := by
  native_decide
example :
    (operatorFormReadingsForGlyph "在").map (fun r => r.operator?) = [some OperatorId.R_1] :=
  by native_decide
example : opIdsOf "在" = some [some OperatorId.R_1] := by native_decide
example :
    (operatorCompoundReadingsForGlyph "五行").map (fun r => r.operator?) =
      [some OperatorId.Y_2] :=
  by native_decide
example : opIdsOf "五行" = some [some OperatorId.Y_2] := by native_decide
example : opIdsOf "形名" = some [some OperatorId.L_4] := by native_decide
example : opIdsOf "大一" = some [some OperatorId.ZA_13] := by native_decide
example : opIdsOf "陰与陽" = some [some OperatorId.Y_1] := by native_decide
example : opIdsOf "上工" = some [some OperatorId.Y_25] := by native_decide

/-- 基础 stdlib 算子的 OperatorId 互不相同（按定义顺序展开）. -/
example :
    (["推", "比", "不", "必", "同", "凡"].filterMap
       (fun s => (resolveStdlibOp s).bind (·.operator?)))
      = [OperatorId.T_10, OperatorId.R_8, OperatorId.N_1,
         OperatorId.M_1,  OperatorId.I_1, OperatorId.Q_1] :=
  by native_decide

/-! ### § 6.5  損/益 surface map (T-12 / T-13) -/

/-- 損/损/益 之 OperatorId — 繁简同读 T_12，益读 T_13. -/
example :
    (["損", "损", "益"].filterMap
       (fun s => (resolveStdlibOp s).bind (·.operator?)))
      = [OperatorId.T_12, OperatorId.T_12, OperatorId.T_13] :=
  by native_decide

/-- 「損」 → catalogueOp T_12. -/
example : opIdsOf "損" = some [some OperatorId.T_12] := by native_decide

/-- 「损」（简体）也读 T_12. -/
example : opIdsOf "损" = some [some OperatorId.T_12] := by native_decide

/-- 「益」 → catalogueOp T_13. -/
example : opIdsOf "益" = some [some OperatorId.T_13] := by native_decide

/-! ## § 7  Cue-based resolution (Phase C)

  simple resolver 对「之」一律视为透明 appMarker；cue-aware 路径可在
  betweenNominals 上下文把它消歧为 S_1 catalogue reading。

  本节增加 cue-aware 通路：从邻居 GlyphTok 之 `canonicalKind` 推 ContextCue，
  再用 `OperatorReadings.contextualReadings` 过滤，若唯一则采用之。
  与 simple 通路并行 —— `resolveSimple` / `resolveOne` 保留作对照。

  cue 重点：当左右皆为 `.glyph` (普通名物) 时发射 `.betweenNominals`，
  「之」据此唯一对应 `«之属格读法»` (operator? = some .S_1)。这与 stdlib
  基础算子相容（其 surface 单字 canonicalKind = .glyph），故 cue 路径与
  surface 路径在 stdlib 范围内殊途同归。

  其他 cue（如 .afterVerb / .beforeMotionVerb）需引入 verb / motion
  分类表，留作后续扩充；现版先覆盖 betweenNominals 启动样.
-/

/-- 取 `i` 处 token 之 surface 之 canonicalKind；越界返 none. -/
def kindAt? (toks : List GlyphTok) (i : Nat) : Option LexKind :=
  (toks[i]?).map (fun t => canonicalKind t.surface)

/-- 从相邻 GlyphTok 推 ContextCue。窗口 ±1 token.

    启动样：左右皆为 `.glyph` 时发射 `.betweenNominals` —— 此时「之」唯一
    对应 `«之属格读法»` (status = .catalogue, operator? = some .S_1).

    扩充时可加：
    - 左为 `.operator` (motion-like) 时 `.afterVerb`
    - 右为特定 motion verb 时 `.beforeMotionVerb`
    现版只覆盖 `.betweenNominals` 一例，避免引入尚未建模的语义判定.

    位置 0 由于无左邻居，返空 cues. -/
def computeCues (toks : List GlyphTok) (i : Nat) : List ContextCue :=
  match i with
  | 0     => []
  | j + 1 =>
    let leftKind  := kindAt? toks j
    let rightKind := kindAt? toks (j + 2)
    match leftKind, rightKind with
    | some .glyph, some .glyph => [.betweenNominals]
    | _,           _           => []

/-- 从给定 cue 上下文中查找 glyph 的唯一 catalogue reading
    （status = .catalogue ∧ operator?.isSome）.

    关键：当 cues 为空时直接返 none —— 不依赖 `contextualReadings` 的
    fallback（后者在空 cue 时会返所有 readings，让 cue 路径退化）.
    cue 路径 *只* 在显式 cue 下生效；其余情形退到 registry-backed surface map. -/
def uniqueCatalogueReading (glyph : Glyph) (cues : List ContextCue)
    : Option OperatorReading :=
  if cues.isEmpty then none
  else
    let rs := contextualReadings glyph cues
    let cats := rs.filter (fun r => r.status = .catalogue ∧ r.operator?.isSome)
    match cats with
    | [r] => some r
    | _   => none

/-- Cue-aware 单 token resolver。优先级:
    appMarker 关闭后改走 cue 路径 → bool 常值 → hex 常值 → cue-唯一 catalogue
    → executable registry surface map → 错误.

    与 `resolveOne` 并存：appMarker 路径仍保留作 fallback，但若 cue 路径
    给出唯一 catalogue reading（如「之」在 betweenNominals 下→ S_1），
    则采用之；其余情形回到 registry-backed surface map. -/
def resolveOneWithCues (toks : List GlyphTok) (i : Nat) (t : GlyphTok)
    : Except ResolveErr ResolvedTok :=
  if isOpenBracketSurface t.surface then
    .ok ⟨t, .openBracket⟩
  else if isCloseBracketSurface t.surface then
    .ok ⟨t, .closeBracket⟩
  else if isIterateConstruction t.surface then
    .ok ⟨t, .iterate⟩
  else
  match resolveBoolConst t.surface with
  | some b => .ok ⟨t, .boolConst b⟩
  | none =>
    match resolveSyntaxMarker t.surface with
    | some marker => .ok ⟨t, .syntax marker⟩
    | none =>
    match resolveVarName t.surface with
    | some name => .ok ⟨t, .varName name⟩
    | none =>
      let cues := computeCues toks i
      match uniqueCatalogueReading t.surface cues with
      | some r =>
          match resolveHexConst t.surface with
          | some h => .ok ⟨t, .hexOrOp h r⟩
          | none   => .ok ⟨t, .catalogueOp r⟩
      | none =>
        -- cue 路径无唯一答；回 registry-backed surface map / appMarker
        if isApplicationMarker t.surface then
          .ok ⟨t, .appMarker⟩
        else
          match uniqueExecutableReadingForGlyph t.surface with
          | some r =>
              match resolveHexConst t.surface with
              | some h => .ok ⟨t, .hexOrOp h r⟩
              | none   => .ok ⟨t, .catalogueOp r⟩
          | none =>
            match resolveHexConst t.surface with
            | some h => .ok ⟨t, .hexConst h⟩
            | none   => resolveCatalogueByTable t

/-- 全 token 列表 cue-aware resolver。结构递归 on index. -/
def resolveWithCuesAux (toks : List GlyphTok)
    : Nat → List GlyphTok → Except ResolveErr (List ResolvedTok)
  | _, []       => .ok []
  | i, t :: ts  =>
    match resolveOneWithCues toks i t with
    | .error e => .error e
    | .ok r =>
      match resolveWithCuesAux toks (i + 1) ts with
      | .error e  => .error e
      | .ok rs    => .ok (r :: rs)

/-- 顶层 cue-aware resolver：对 GlyphTok 流做 cue 计算 + 消歧.
    与 `resolveSimple` 同 type，可作 drop-in 替换. -/
def resolveWithCues (toks : List GlyphTok)
    : Except ResolveErr (List ResolvedTok) :=
  resolveWithCuesAux toks 0 toks

/-! ### § 7.1  Cue 计算 sanity 例子 -/

/-- 「推 之 一」之 i=1 (「之」位置) 之 cues = [.betweenNominals]。
    「推」「一」皆 canonicalKind = .glyph (非 .operator/.particle/.modal). -/
example :
    computeCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩] 1
      = [ContextCue.betweenNominals] :=
  by native_decide

/-- i=0 (无左邻居) → 空 cues. -/
example :
    computeCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩] 0
      = ([] : List ContextCue) :=
  by native_decide

/-- 末位 (无右邻居) → 空 cues. -/
example :
    computeCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩] 2
      = ([] : List ContextCue) :=
  by native_decide

/-! ### § 7.2  uniqueCatalogueReading sanity -/

/-- 「之」在 betweenNominals 上下文 → 唯一 catalogue (S_1 属格). -/
example :
    (uniqueCatalogueReading "之" [.betweenNominals]).map (·.operator?)
      = some (some OperatorId.S_1) :=
  by native_decide

/-- 「之」无 cue → 多 reading，非唯一 catalogue（4 readings, 仅 1 catalogue
    但 isApplicationMarker 路径会 fallback；这里测的是 cue 路径本身）. -/
example : uniqueCatalogueReading "之" [] = none := by native_decide

/-- 「推」在任意 cue 下不在 cue 表（无对应 readings）→ none. -/
example : uniqueCatalogueReading "推" [.betweenNominals] = none := by native_decide

/-! ### § 7.3  resolveWithCues 端到端 -/

/-- Helper：从 cue-aware resolve 抽 OperatorId 序列. -/
private def opIdsOfCues (toks : List GlyphTok) : Option (List (Option OperatorId)) :=
  (resolveWithCues toks).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?))

/-- 「推 之 一」走 cue 路径 → [T_10, S_1, none]。注意此处「之」拿到 S_1
    catalogue reading（与 simple 透明 appMarker 不同；parser/elab 将其作为
    explicit marker 透明处理）. -/
example :
    opIdsOfCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩]
      = some [some OperatorId.T_10, some OperatorId.S_1, none] :=
  by native_decide

/-- resolveWithCues 在「推 之 一」上 success（.toOption.isSome = true）. -/
example :
    (resolveWithCues
        [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩]).toOption.isSome
      = true :=
  by native_decide

/-- 「之」单独（无邻居）走 fallback → appMarker，与 resolveSimple 一致. -/
example :
    ((resolveWithCues [⟨"之", 0, 1, false⟩]).toOption.map
       (fun rs => rs.map (·.atom |> ResolvedAtom.isAppMarker)))
      = some [true] :=
  by native_decide

/-- 「推 一」无「之」，与 resolveSimple 完全等价（atom 序列）. -/
example :
    opIdsOfCues [⟨"推", 0, 1, false⟩, ⟨"一", 2, 1, false⟩]
      = some [some OperatorId.T_10, none] :=
  by native_decide

/-! ### § 7.4  Cue → unique catalogue 桥定理

  和 OperatorReadings.zhi_between_nominals_unique（line 749-751）对齐:
  在 betweenNominals 上下文中，「之」唯一对应 S_1 catalogue reading. -/

/-- 在 betweenNominals 上下文，uniqueCatalogueReading 之 operator? 唯一为 S_1. -/
theorem zhi_between_nominals_unique_catalogue :
    (uniqueCatalogueReading "之" [.betweenNominals]).bind (·.operator?)
      = some OperatorId.S_1 :=
  by native_decide

/-- 在 afterVerb 上下文，「之」之 contextualReadings 唯一（zhi_after_verb_unique
    桥），但该读法 status = .contextual ∧ operator? = none —— 故
    uniqueCatalogueReading 返 none（catalogue gate 不通）. -/
theorem zhi_after_verb_no_catalogue :
    uniqueCatalogueReading "之" [.afterVerb] = none :=
  by native_decide

/-- 在 cue-空 上下文，「之」非 cue-唯一. -/
theorem zhi_no_cue_no_unique_catalogue :
    uniqueCatalogueReading "之" [] = none :=
  by native_decide

/-! ### § 7.5  resolveWithCues 不破坏现有路径

  对不包含「之」的 stdlib token 流，cue 路径与 surface 路径一致 —— 这
  通过 atom 序列对比见证. -/

/-- 基础 stdlib 算子 + 「一」的 atom 序列同 resolveSimple. -/
example :
    ((resolveWithCues
        [⟨"推", 0, 1, false⟩, ⟨"比", 2, 1, false⟩, ⟨"不", 4, 1, false⟩,
         ⟨"必", 6, 1, false⟩, ⟨"同", 8, 1, false⟩, ⟨"凡", 10, 1, false⟩,
         ⟨"一", 12, 1, false⟩]).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?)))
      = some [some OperatorId.T_10, some OperatorId.R_8, some OperatorId.N_1,
              some OperatorId.M_1,  some OperatorId.I_1, some OperatorId.Q_1,
              none] :=
  by native_decide

end SSBX.Foundation.Wen.WenSurface
