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
import SSBX.Foundation.Wen.WenDef
import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8
import SSBX.Text.OperatorAnchors
import SSBX.Text.OperatorReadings
import SSBX.Foundation.Atlas.Yi.Classical.Core.YiCore

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.R8
open SSBX.Text.OperatorAnchors
open SSBX.Foundation.Wen.WenDef

/-! ## § 1  Resolved 类型 -/

/-- Surface-level syntax markers that are not value operators by themselves. -/
inductive SyntaxMarker where
  | zhe
  | ling
  /-- wen-2.0 ⑪ `执 「X」`: quote-eval prefix marker.  Consumes the next
      SurfaceExpr (expected to elaborate to a `.quoted`) and wraps it in a
      `Tm.unquote` so the evaluator re-runs the quoted body under the
      current env.  Not a value operator; not registered as an OperatorId
      to keep the catalogue audit/coverage tables stable. -/
  | zhi
  /-- wen-2.0 ⑦ `X 属 S`: set-membership infix marker.  Parsed in
      postfix-application dispatch (similar to relation infix `同`/`比`):
      consumes one trailing expression as the Set argument and emits
      `Tm.memberOf x s`.  Not registered as an OperatorId. -/
  | shu
  /-- wen-2.0 ⑧ `所 PRED 者`: object relativization.  The leading `所`
      marker triggers the parser to consume one sub-expression `PRED`
      followed by a required `者`, then desugar to `λ甲. PRED 甲` (i.e.,
      nominalize the predicate over an implicit object via the existing
      `Tm.abs` lambda-binder).  Note: this **overrides** the legacy
      catalogue reading `S_16` (nominalization particle as Hex→Hex
      identity), which had no surface-grammar uses prior to ⑧. -/
  | suo
  /-- wen-2.0 ⑧ `Y 之所以 X`: reason-extraction marker.  When the
      preceding `acc` is a complete expression, `之所以` consumes the
      next sub-expression `X` and reshapes `acc` into `X acc`
      (reason-as-application — the rhetorical "what causes Y to X"
      collapses to ordinary application in the kernel; surface form
      preserved for pretty-print). -/
  | zhiSuoYi
deriving DecidableEq, Repr

/-- 已消歧的原子：卦字面值 / Bool 字面值 / catalogue 算子读法 /
    应用标记 / 迭代构式 / builtin Tm primitive. -/
inductive ResolvedAtom where
  | hexConst    (h : Hexagram)
  | boolConst   (b : Bool)
  | varName     (name : String)
  | catalogueOp (reading : OperatorReading)
  | ambiguousOp (candidates : List OperatorReading)
  | hexOrOp     (h : Hexagram) (reading : OperatorReading)
  | syntax      (marker : SyntaxMarker)
  | appMarker             -- 「之」 等不发射 Tm 的 surface marker
  | iterate               -- 「之又」 迭代构式 marker：F X ↦ F (F X)
  | openBracket
  | closeBracket
  /-- B-2 / B-3 / B-6: builtin `WenDef.Tm` primitive that has no
      OperatorId in the catalogue.  `body` is a closed Tm whose
      `typeCheck` is `arr a₁ (... arr aₙ b)` for some `n = arity`;
      parser/elaborator treat this like a `.catalogueOp` of the
      corresponding arity but bypass the OperatorId / executable-registry
      dispatch entirely. -/
  | builtinTm   (body : Tm) (arity : Nat)
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
  /-- B-10: surface glyph is a first-character of one or more multi-glyph
      hexagram names (e.g. 大 → 大有/大壮/大畜/大过; 中 → 中孚; 明 → 明夷).
      The glyph is intentionally unreachable as a bare expression — write the
      full hex name instead.  `examples` carries up to a few canonical full
      names that begin with `surface`. -/
  | hexCompoundStarter (surface : String) (col : Nat) (examples : List String) : ResolveErr
  /-- B-11: surface is a registered 学派 namespace name (e.g. 墨经, 名家,
      庄子, 中庸).  These are labels for `OperatorGroup`s used in
      `用 NS_NAME` declarations and are not parseable expressions. -/
  | schoolNamespaceName (surface : String) (col : Nat) : ResolveErr
deriving DecidableEq, Repr

/-! ## § 2  Surface maps -/

/-- Surface variables accepted by the prefix-only binder forms. -/
def surfaceVarNames : List String :=
  ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"]

def resolveVarName : Glyph → Option String
  | g => if surfaceVarNames.contains g then some g else none

/-- Canonical surface hexagram names, aligned with `R8.xuGua`.
    The traditional `鼎` is retained as an alias; the default single-glyph
    surface for hexagram 50 is `器` to avoid the unpromoted gap-form conflict. -/
def canonicalHexNames : List String :=
  [ "乾", "坤", "屯", "蒙", "需", "讼", "师", "比"
  , "小畜", "履", "泰", "否", "同人", "大有", "谦", "豫"
  , "随", "蛊", "临", "观", "噬嗑", "贲", "剥", "复"
  , "无妄", "大畜", "颐", "大过", "坎", "离", "咸", "恒"
  , "遁", "大壮", "晋", "明夷", "家人", "睽", "蹇", "解"
  , "损", "益", "夬", "姤", "萃", "升", "困", "井"
  , "革", "器", "震", "艮", "渐", "归妹", "丰", "旅"
  , "巽", "兑", "涣", "节", "中孚", "小过", "既济", "未济" ]

/-- Conservative traditional aliases for full hexagram names. -/
def hexNameAliases : List (String × String) :=
  [ ("訟", "讼"), ("師", "师"), ("謙", "谦"), ("隨", "随")
  , ("蠱", "蛊"), ("臨", "临"), ("觀", "观"), ("賁", "贲")
  , ("剝", "剥"), ("復", "复"), ("無妄", "无妄"), ("頤", "颐")
  , ("過", "过"), ("大過", "大过"), ("小過", "小过")
  , ("離", "离"), ("恆", "恒"), ("晉", "晋"), ("大壯", "大壮")
  , ("損", "损"), ("鼎", "器"), ("漸", "渐"), ("歸妹", "归妹"), ("豐", "丰")
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
  | "兩" | "两" =>
      some (catalogueReading "兩" "D-4" "兩 / duplicate" (some .D_4)
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
  | "执" => some .zhi    -- wen-2.0 ⑪ quote-eval prefix
  | "執" => some .zhi    -- traditional variant
  | "属" => some .shu    -- wen-2.0 ⑦ set-membership infix
  | "屬" => some .shu    -- traditional variant
  | "所" => some .suo    -- wen-2.0 ⑧ object relativization head
  | "之所以" => some .zhiSuoYi  -- wen-2.0 ⑧ reason-extraction infix
  | _    => none

/-! ### Builtin Tm surface map (B-2 / B-3 / B-6)

Surfaces that map directly to a closed `WenDef.Tm` body and a parser arity,
without going through the catalogue / OperatorId path.  These are kept here
(rather than added as new OperatorIds) so the 375-row catalogue audit stays
stable; the catalogue is about classical text glosses, while these surfaces
are mechanical Tm primitives.

* **B-2** yao flips (`Hex → Hex`): 初/二/三/四/五/上 爻 → `flip{1..6}H`.
* **B-3** Hex addition `加` (`Hex → Hex → Hex`): the `Tm.jia` primitive.
* **B-6** Hex list ops: 列一/二/三 → `list{1..3}H`; 首 → `headH`. -/
def resolveBuiltinSurface : Glyph → Option (Tm × Nat)
  -- B-2: yao flips (per `WenDef.lean` Tm constructors)
  | "初爻" => some (.flip1H, 1)
  | "二爻" => some (.flip2H, 1)
  | "三爻" => some (.flip3H, 1)
  | "四爻" => some (.flip4H, 1)
  | "五爻" => some (.flip5H, 1)
  | "上爻" => some (.flip6H, 1)
  -- B-3: Hex addition `加 : Hex → Hex → Hex`
  | "加" => some (.jia, 2)
  -- B-4: Bool conjunction `並/并 : Bool → Bool → Bool`
  | "並" => some (.andB, 2)
  | "并" => some (.andB, 2)
  -- B-5: Bool disjunction `或 : Bool → Bool → Bool`
  | "或" => some (.orB, 2)
  -- B-6: list ops
  | "列一" => some (.list1H, 1)
  | "列二" => some (.list2H, 2)
  | "列三" => some (.list3H, 3)
  | "首"   => some (.headH, 1)
  | _      => none

def matchingCloseBracket? : Glyph → Option Glyph
  | "（" => some "）"
  | "("  => some ")"
  | "「" => some "」"   -- wen-2.0 ⑩ quote bracket (primary)
  | "『" => some "』"   -- wen-2.0 ⑩ quote bracket (nested)
  | _    => none

def isOpenBracketSurface (g : Glyph) : Bool :=
  (matchingCloseBracket? g).isSome

def isCloseBracketSurface : Glyph → Bool
  | "）" | ")" | "」" | "』" => true
  | _ => false

/-- wen-2.0 ⑩: an open-bracket surface is a *quote* bracket (vs value
    grouping) when it is one of `「` / `『`. -/
def isQuoteOpenBracketSurface (g : Glyph) : Bool :=
  g == "「" || g == "『"

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

def sameExecutableReadingShape (base r : OperatorReading) : Bool :=
  decide (r.fixity = base.fixity) && decide (r.construction = base.construction)

def sameExecutableSemanticsAndShape (base : OperatorReading) (sem : ExecutableSemantics)
    (r : OperatorReading) : Bool :=
  sameExecutableSemantics sem r && sameExecutableReadingShape base r

def firstTheoremBackedReading? : List OperatorReading → Option OperatorReading
  | [] => none
  | r :: rest =>
      match r.operator? with
      | some id => if isTheoremBackedOperator id then some r else firstTheoremBackedReading? rest
      | none => firstTheoremBackedReading? rest

/--
Choose a surface reading when all executable candidates collapse to the same
typed body and the same syntactic reading shape.  This keeps true aliases such
as `同` (I-1/P-4) usable without pretending that different constructions, such
as quantifier/modal `或`, have been disambiguated just because the current
finite model shares a body for them.
-/
def uniqueExecutableReadingBySemantics : List OperatorReading → Option OperatorReading
  | [] => none
  | r :: rest =>
      match executableSemanticsForReading? r with
      | none => none
      | some sem =>
          if rest.all (sameExecutableSemanticsAndShape r sem) then
            match firstTheoremBackedReading? (r :: rest) with
            | some exact => some exact
            | none => some r
          else
            none

def uniqueExecutableCatalogueReading (glyph : Glyph) : Option OperatorReading :=
  uniqueExecutableReadingBySemantics (catalogueReadingsForGlyph glyph)

structure SurfaceExecutableAlias where
  surface : Glyph
  id : OperatorId
  gloss : String
  cues : List ContextCue
deriving Repr

/-- Conservative executable aliases added by the Bagua naming pass.

The table only points at already theorem-backed/operator-registry semantics.
Names whose intended value would need a new codomain or primitive stay in the
candidate Markdown table until they receive real semantics.
-/
def surfaceExecutableAliasRows : List SurfaceExecutableAlias :=
  [ ⟨"恒", .L_10, "恒: identity / no-op alias", [.identityContext, .expectedObject]⟩
  , ⟨"静", .L_10, "静: identity / no-op alias", [.identityContext, .expectedObject]⟩
  , ⟨"靜", .L_10, "靜: identity / no-op alias", [.identityContext, .expectedObject]⟩
  , ⟨"定", .L_10, "定: identity / no-op alias", [.identityContext, .expectedObject]⟩
  , ⟨"常", .L_10, "常: identity / no-op alias", [.identityContext, .expectedObject]⟩
  , ⟨"安", .L_10, "安: identity / no-op alias", [.identityContext, .expectedObject]⟩
  , ⟨"寂", .L_10, "寂: identity / no-op alias", [.identityContext, .expectedObject]⟩
  , ⟨"息", .L_10, "息: identity / no-op alias", [.identityContext, .expectedObject]⟩
  , ⟨"復", .T_7, "復: return-to-root identity alias", [.expectedObject]⟩
  , ⟨"复", .T_7, "复: return-to-root identity alias", [.expectedObject]⟩
  , ⟨"展", .T_15, "展: extension / unfold alias", [.expectedObject]⟩
  , ⟨"顯", .Z_9, "顯: reveal/advance alias", [.expectedObject]⟩
  , ⟨"显", .Z_9, "显: reveal/advance alias", [.expectedObject]⟩
  , ⟨"藏", .Z_10, "藏: conceal/archive alias", [.expectedObject]⟩ ]

def surfaceExecutableAliasReadingsForGlyph (glyph : Glyph) : List OperatorReading :=
  surfaceExecutableAliasRows.filterMap (fun row =>
    if decide (row.surface = glyph) && isTheoremBackedOperator row.id then
      some (catalogueReading row.surface row.id.code row.gloss (some row.id)
        .prefix row.cues)
    else
      none)

def uniqueSurfaceExecutableAliasReading (glyph : Glyph) : Option OperatorReading :=
  uniqueExecutableReadingBySemantics (surfaceExecutableAliasReadingsForGlyph glyph)

/--
Reserved v1 surfaces remain stable even when the full catalogue records later
homographs for the same glyph.  Outside this small compatibility surface, a
glyph only auto-resolves when every relevant catalogue candidate has the same
executable semantics.
-/
def reservedV1ExecutableReadingForGlyph (glyph : Glyph) : Option OperatorReading :=
  match resolveStdlibOp glyph with
  | some r =>
      match r.operator? with
      | some id => if isTheoremBackedOperator id then some r else none
      | none => none
  | none => uniqueSurfaceExecutableAliasReading glyph

def uniqueExecutableReadingForGlyph (glyph : Glyph) : Option OperatorReading :=
  match reservedV1ExecutableReadingForGlyph glyph with
  | some r => some r
  | none =>
      match resolveHexConst glyph with
      | some _ => none
      | none =>
          let catalogue := catalogueReadingsForGlyph glyph
          if catalogue.isEmpty then
            let compounds := operatorCompoundReadingsForGlyph glyph
            if compounds.isEmpty then
              uniqueExecutableReadingBySemantics (operatorFormReadingsForGlyph glyph)
            else
              uniqueExecutableReadingBySemantics compounds
          else
            uniqueExecutableReadingBySemantics catalogue

/-! ### B-10 / B-11  Helpful error classification for unreachable surfaces

For glyphs that have no catalogue reading, we classify them into one of:

* **hex-compound starter** — first glyph of a multi-glyph canonical hex name
  (e.g. `大` → 大有 / 大壮 / 大畜 / 大过).  These are intentionally
  unreachable as bare expressions to avoid prefix ambiguity with the lexer's
  longest-prefix match; the lexer would consume `大壮` as one token, so a
  bare `大` cannot mean either a single-glyph hex or a partial compound.
* **学派 namespace name** — surfaces registered in `Namespace.entries`
  (e.g. 墨经, 名家, 庄子, 中庸).  These are labels for `OperatorGroup`s
  used in `用 NS_NAME` declarations; they have no expression-level Tm
  constructor.

Both classifications take priority over the generic `noReading` error.  See
`renderResolveErr` in `WenSurface.ErrorRender` for the user-facing
messages. -/

/-- A glyph 是 hex-compound starter ⇔ 它是某条多字 `canonicalHexNames` 或
    `hexNameAliases` 的首字符（按 codepoint 计），且本身不是该名（即不是
    完整的单字 hex 名）。 -/
def firstCharOf? (s : String) : Option String :=
  match s.toList with
  | []      => none
  | c :: _  => some c.toString

/-- 多字 canonical hex names + multi-char aliases，作为 starter 的来源集合. -/
def multiCharHexNames : List String :=
  canonicalHexNames.filter (fun s => decide (s.toList.length > 1))
    ++ (hexNameAliases.map Prod.fst).filter (fun s => decide (s.toList.length > 1))

/-- Full hex names whose first glyph equals `g`. Used for `hexCompoundStarter`
    error examples. -/
def hexCompoundsStartingWith (g : Glyph) : List String :=
  multiCharHexNames.filter (fun s =>
    match firstCharOf? s with
    | some c => c = g
    | none   => false)

/-- `g` 是某多字 hex name 的首字符（且 `g` 本身不是单字 canonical hex；如
    `小畜` 起字 `小` 也是 unpromoted-gap 单字 hex，仍归此类以给出更具体的
    指引）。 -/
def isHexCompoundStarter (g : Glyph) : Bool :=
  !(hexCompoundsStartingWith g).isEmpty

/-- Surfaces registered as 学派 namespace names.  This list mirrors the keys
    of `Namespace.entries` but is duplicated here (rather than imported) to
    avoid a circular dependency: `Namespace` already imports `EndToEnd`,
    which transitively depends on `Reading`. -/
def schoolNamespaceSurfaces : List String :=
  [ "墨经", "墨經", "墨家", "墨"
  , "名家", "名学", "名學"
  , "法家", "法學", "法学"
  , "医家", "醫家", "中医", "中醫", "黄帝内经", "黃帝內經"
  , "庄子", "莊子", "齐物", "齊物"
  , "孙子", "孫子", "兵家", "兵法"
  , "楚辞", "楚辭"
  , "礼记", "禮記", "中庸"
  , "杂家", "雜家", "黄老", "黃老", "淮南", "淮南子"
  , "史官", "春秋"
  , "社会", "社會", "荀子"
  , "补遗", "補遺" ]

def isSchoolNamespaceSurface (g : Glyph) : Bool :=
  schoolNamespaceSurfaces.contains g

/-- Promote a `noReading` to a more informative classification when possible. -/
def classifyNoReading (surface : String) (col : Nat) : ResolveErr :=
  if isSchoolNamespaceSurface surface then
    .schoolNamespaceName surface col
  else if isHexCompoundStarter surface then
    .hexCompoundStarter surface col (hexCompoundsStartingWith surface)
  else
    .noReading surface col

def resolveCatalogueByTable (t : GlyphTok) : Except ResolveErr ResolvedTok :=
  if isUnpromotedHexagramGap t.surface then
    -- B-10: 大/小 are both unpromoted-gap AND hex-compound starters; the
    -- compound-starter classification is strictly more actionable for the
    -- user (it lists concrete examples).
    if isHexCompoundStarter t.surface then
      .error (.hexCompoundStarter t.surface t.startCol
                (hexCompoundsStartingWith t.surface))
    else
      .error (.unpromotedHexagramGap t.surface t.startCol)
  else
    let readings := catalogueOrOperatorFormReadingsForGlyph t.surface
    match readings with
    | [] =>
        let knownReadings := readingsForGlyph t.surface
        if knownReadings.isEmpty then
          .error (classifyNoReading t.surface t.startCol)
        else
          .error (.knownButUnsupported t.surface t.startCol knownReadings)
    | [r] => .ok ⟨t, .catalogueOp r⟩
    | rs  => .error (.ambiguous t.surface t.startCol rs)

def resolveCatalogueByTableAllowAmbiguous (t : GlyphTok)
    : Except ResolveErr ResolvedTok :=
  if isUnpromotedHexagramGap t.surface then
    if isHexCompoundStarter t.surface then
      .error (.hexCompoundStarter t.surface t.startCol
                (hexCompoundsStartingWith t.surface))
    else
      .error (.unpromotedHexagramGap t.surface t.startCol)
  else
    let readings := catalogueOrOperatorFormReadingsForGlyph t.surface
    match readings with
    | [] =>
        let knownReadings := readingsForGlyph t.surface
        if knownReadings.isEmpty then
          .error (classifyNoReading t.surface t.startCol)
        else
          .error (.knownButUnsupported t.surface t.startCol knownReadings)
    | [r] => .ok ⟨t, .catalogueOp r⟩
    | rs  => .ok ⟨t, .ambiguousOp rs⟩

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
  -- B-2 / B-3 / B-6: builtin Tm surfaces (no OperatorId, no catalogue row).
  -- These take priority over any catalogue reading so the surface table stays
  -- the canonical source for builtin primitives.
  match resolveBuiltinSurface t.surface with
  | some (body, arity) => .ok ⟨t, .builtinTm body arity⟩
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
  | .ambiguousOp _ => none
  | .hexOrOp _ r   => r.operator?
  | .syntax _      => none
  | .appMarker     => none
  | .iterate       => none
  | .openBracket   => none
  | .closeBracket  => none
  | .builtinTm _ _ => none

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

/-- 「乾」 → hexConst Hexagram.heaven. -/
example : opIdsOf "乾" = some [none] := by native_decide

/-- 「坤」 → hexConst Hexagram.earth. -/
example : opIdsOf "坤" = some [none] := by native_decide

/-- 「推 乾」 → T_10 + heaven. -/
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
example : resolveHexConst "乾" = some Hexagram.heaven := by native_decide
example : resolveHexConst "坤" = some Hexagram.earth  := by native_decide
example : resolveHexConst "大壯" = resolveHexConst "大壮" := by native_decide
example : resolveHexConst "器" = resolveHexConst "鼎" := by native_decide
example : resolveHexConst "推" = none               := by native_decide
example : isUnpromotedHexagramGap "鼎" = true := by native_decide
example : isUnpromotedHexagramGap "器" = false := by native_decide
example : isUnpromotedHexagramGap "丽" = true := by native_decide
example : isUnpromotedHexagramGap "益" = false := by native_decide
example : uniqueExecutableCatalogueReading "推" = none := by native_decide
example :
    (uniqueExecutableReadingForGlyph "推").bind (·.operator?) = some OperatorId.T_10 :=
  by native_decide
example :
    (uniqueExecutableCatalogueReading "同").bind (·.operator?) = some OperatorId.I_1 :=
  by native_decide
example : uniqueExecutableCatalogueReading "益" = none := by native_decide
example :
    (uniqueExecutableReadingForGlyph "益").bind (·.operator?) = some OperatorId.T_13 :=
  by native_decide
example : uniqueExecutableReadingForGlyph "或" = none := by native_decide
example : uniqueExecutableReadingForGlyph "反" = none := by native_decide
example : uniqueExecutableReadingForGlyph "名分" = none := by native_decide
example :
    (uniqueExecutableReadingForGlyph "错").bind (·.operator?) = some OperatorId.Z_5 :=
  by native_decide
example :
    (uniqueExecutableReadingForGlyph "恒").bind (·.operator?) = some OperatorId.L_10 :=
  by native_decide
example :
    (uniqueExecutableReadingForGlyph "静").bind (·.operator?) = some OperatorId.L_10 :=
  by native_decide
example :
    (["复", "復", "展"].filterMap
        (fun s => (uniqueExecutableReadingForGlyph s).bind (·.operator?)))
      = [OperatorId.T_7, OperatorId.T_7, OperatorId.T_15] :=
  by native_decide
theorem executableSurfaceReadings_use_registry_path :
    (["推", "比", "不", "必", "同", "凡", "損", "损", "益",
      "错", "錯", "综", "綜", "互"].all
        (fun s => (uniqueExecutableReadingForGlyph s).isSome)) = true := by
  native_decide

theorem executableSurfaceReadings_table_driven_ids :
    (["推", "比", "不", "必", "同", "凡", "損", "损", "益",
      "错", "錯", "综", "綜", "互"].filterMap
        (fun s => (uniqueExecutableReadingForGlyph s).bind (·.operator?)))
      = [ OperatorId.T_10, OperatorId.R_8, OperatorId.N_1,
          OperatorId.M_1, OperatorId.I_1, OperatorId.Q_1,
          OperatorId.T_12, OperatorId.T_12, OperatorId.T_13,
          OperatorId.Z_5, OperatorId.Z_5, OperatorId.Z_6,
          OperatorId.Z_6, OperatorId.Z_3 ] := by
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
example : opIdsOf "不动" = some [some OperatorId.L_10] := by native_decide
example : opIdsOf "錯綜" = some [some OperatorId.I_8] := by native_decide
example : opIdsOf "交错" = some [some OperatorId.Z_33] := by native_decide
example : opIdsOf "归一" = some [some OperatorId.T_7] := by native_decide
example : opIdsOf "展开" = some [some OperatorId.T_15] := by native_decide
example : opIdsOf "动初" = some [some OperatorId.T_5] := by native_decide
example : opIdsOf "初动" = some [some OperatorId.T_5] := by native_decide
example : opIdsOf "動中" = some [some OperatorId.T_1] := by native_decide
example : opIdsOf "承变" = some [some OperatorId.T_1] := by native_decide
example : opIdsOf "上变" = some [some OperatorId.T_2] := by native_decide
example : opIdsOf "际变" = some [some OperatorId.T_2] := by native_decide
example : opIdsOf "恒 乾" = some [some OperatorId.L_10, none] := by native_decide

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

/-! ### § 6.6  Builtin Tm surface map (B-2 / B-3 / B-4 / B-5 / B-6)

`resolveBuiltinSurface` maps surface glyphs directly to `WenDef.Tm` primitive
bodies, bypassing the OperatorId catalogue.  These surfaces have no
`operator?` entry (they are not catalogue rows) so `opIdsOf` returns `[none]`
for them — the test below witnesses that they resolve to a `.builtinTm`
atom rather than to `.noReading` / `.catalogueOp`. -/

/-- B-2: yao flips all resolve to `.builtinTm`. -/
example :
    (["初爻", "二爻", "三爻", "四爻", "五爻", "上爻"].all
      (fun s => match resolveBuiltinSurface s with | some _ => true | none => false)) = true := by
  native_decide

/-- B-3: 加 resolves to `.builtinTm` with arity 2. -/
example : (resolveBuiltinSurface "加").map Prod.snd = some 2 := by native_decide

/-- B-4: 並/并 resolve to `Tm.andB` with arity 2. -/
example :
    (resolveBuiltinSurface "並") = some (Tm.andB, 2) := by native_decide
example :
    (resolveBuiltinSurface "并") = some (Tm.andB, 2) := by native_decide

/-- B-5: 或 resolves to `Tm.orB` with arity 2. -/
example :
    (resolveBuiltinSurface "或") = some (Tm.orB, 2) := by native_decide

/-- B-6: list ops resolve to `.builtinTm` with their declared arities. -/
example : (resolveBuiltinSurface "列一").map Prod.snd = some 1 := by native_decide
example : (resolveBuiltinSurface "列二").map Prod.snd = some 2 := by native_decide
example : (resolveBuiltinSurface "列三").map Prod.snd = some 3 := by native_decide
example : (resolveBuiltinSurface "首").map Prod.snd = some 1 := by native_decide

/-- 加 (single glyph) lexes and resolves via `lexAndResolve`. -/
example :
    ((lexAndResolve "加").toOption.map (fun rs => rs.map (·.atom)))
      = some [.builtinTm Tm.jia 2] := by native_decide

/-- B-4: 並/并 lex+resolve to `Tm.andB` (builtin priority overrides
    the legacy catalogue routing to `R_13` pairH carrier). -/
example :
    ((lexAndResolve "並").toOption.map (fun rs => rs.map (·.atom)))
      = some [.builtinTm Tm.andB 2] := by native_decide
example :
    ((lexAndResolve "并").toOption.map (fun rs => rs.map (·.atom)))
      = some [.builtinTm Tm.andB 2] := by native_decide

/-- B-5: 或 lex+resolves to `Tm.orB` (builtin priority overrides the
    legacy catalogue routing to `Q_5` / `M_2` quantifier/modal). -/
example :
    ((lexAndResolve "或").toOption.map (fun rs => rs.map (·.atom)))
      = some [.builtinTm Tm.orB 2] := by native_decide

/-- 初爻 (multi-glyph) is lexed as a single 2-char surface and resolves to flip1H. -/
example :
    ((lexAndResolve "初爻").toOption.map (fun rs => rs.map (·.atom)))
      = some [.builtinTm Tm.flip1H 1] := by native_decide

/-- 列一 / 首 likewise resolve to their builtin Tms. -/
example :
    ((lexAndResolve "列一").toOption.map (fun rs => rs.map (·.atom)))
      = some [.builtinTm Tm.list1H 1] := by native_decide

example :
    ((lexAndResolve "首").toOption.map (fun rs => rs.map (·.atom)))
      = some [.builtinTm Tm.headH 1] := by native_decide

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

  对普通 prefix operator，则从右邻 token 的明显起点补一个轻量 expected-type
  cue：Hex/变量起点 → `.expectedObject`，Bool 起点 → `.expectedProp`，
  `者` 起点 → `.quantifierDomain`。这能消解「反 乾」「化 乾」
  以及「或 者 ...」这样的局部上下文，同时不把泛语义 cue 强塞给「之」。
-/

/-- 取 `i` 处 token 之 surface 之 canonicalKind；越界返 none. -/
def kindAt? (toks : List GlyphTok) (i : Nat) : Option LexKind :=
  (toks[i]?).map (fun t => canonicalKind t.surface)

/-- 从一个显然的右邻表达式起点推 operator argument cue。

    这不是完整 parser；只处理无需解析即可确定的起点：
    - Hex 常值 / binder 变量名：对象参数
    - Bool 常值：命题参数
    - `者` lambda 起点：Hex 谓词，服务存在量化等 operator
-/
def argumentStartCue? (t : GlyphTok) : Option ContextCue :=
  match resolveHexConst t.surface, resolveVarName t.surface, resolveBoolConst t.surface,
      resolveSyntaxMarker t.surface with
  | some _, _, _, _ => some .expectedObject
  | _, some _, _, _ => some .expectedObject
  | _, _, some _, _ => some .expectedProp
  | _, _, _, some .zhe => some .quantifierDomain
  | _, _, _, _ => none

/-- 从相邻 GlyphTok 推 ContextCue。窗口 ±1 token.

    启动样：左右皆为 `.glyph` 时发射 `.betweenNominals` —— 此时「之」唯一
    对应 `«之属格读法»` (status = .catalogue, operator? = some .S_1).

    若不是 between-nominals，则用右邻起点给 prefix 多义 operator 一个
    conservative expected-type cue。between-nominals 优先，避免「乾 之 坤」
    被额外 `.expectedObject` 过度约束。

    位置 0 没有 left-neighbor cue，但仍可从右邻起点取得 expected-type cue. -/
def computeCues (toks : List GlyphTok) (i : Nat) : List ContextCue :=
  let rightTok := toks[i + 1]?
  let rightStartCue :=
    match rightTok with
    | some t => (argumentStartCue? t).toList
    | none => []
  match i with
  | 0     => rightStartCue
  | j + 1 =>
    let leftKind  := kindAt? toks j
    let rightKind := kindAt? toks (j + 2)
    match leftKind, rightKind with
    | some .glyph, some .glyph => [.betweenNominals]
    | _,           _           => rightStartCue

/-- A reading satisfies a cue either by carrying that exact cue or by exposing
    the expected type denoted by that cue.  This lets strong type cues refine
    ambiguous surfaces without changing parser/elaborator syntax. -/
def readingSatisfiesCue (r : OperatorReading) (cue : ContextCue) : Bool :=
  r.cues.contains cue ||
    match expectedTypeOfCue cue with
    | some ty => r.expectedTypes.contains ty
    | none => false

/-- Cue-selected catalogue readings: every cue must be satisfied by the reading.
    Non-type contextual cues such as `.mohistContext` still require an exact cue
    match; expected-type cues may match `expectedTypes` metadata. -/
def cueSelectedCatalogueReadings (glyph : Glyph) (cues : List ContextCue)
    : List OperatorReading :=
  (readingsForGlyph glyph).filter (fun r =>
    r.status = .catalogue ∧ r.operator?.isSome ∧
      cues.all (readingSatisfiesCue r))

/-- 从给定 cue 上下文中查找 glyph 的唯一 catalogue reading
    （status = .catalogue ∧ operator?.isSome）.

    关键：当 cues 为空时直接返 none —— 不依赖 `contextualReadings` 的
    fallback（后者在空 cue 时会返所有 readings，让 cue 路径退化）.
    cue 路径 *只* 在显式 cue 下生效；其余情形退到 registry-backed surface map. -/
def uniqueCatalogueReading (glyph : Glyph) (cues : List ContextCue)
    : Option OperatorReading :=
  if cues.isEmpty then none
  else
    match cueSelectedCatalogueReadings glyph cues with
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
    -- B-2 / B-3 / B-6: builtin Tm surfaces take priority over both cue and
    -- registry paths.
    match resolveBuiltinSurface t.surface with
    | some (body, arity) => .ok ⟨t, .builtinTm body arity⟩
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

def resolveOneWithCuesAllowAmbiguous (toks : List GlyphTok) (i : Nat) (t : GlyphTok)
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
    match resolveBuiltinSurface t.surface with
    | some (body, arity) => .ok ⟨t, .builtinTm body arity⟩
    | none =>
      let cues := computeCues toks i
      match uniqueCatalogueReading t.surface cues with
      | some r =>
          match resolveHexConst t.surface with
          | some h => .ok ⟨t, .hexOrOp h r⟩
          | none   => .ok ⟨t, .catalogueOp r⟩
      | none =>
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
            | none   => resolveCatalogueByTableAllowAmbiguous t

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

def resolveWithCuesAllowAmbiguousAux (toks : List GlyphTok)
    : Nat → List GlyphTok → Except ResolveErr (List ResolvedTok)
  | _, []       => .ok []
  | i, t :: ts  =>
    match resolveOneWithCuesAllowAmbiguous toks i t with
    | .error e => .error e
    | .ok r =>
      match resolveWithCuesAllowAmbiguousAux toks (i + 1) ts with
      | .error e  => .error e
      | .ok rs    => .ok (r :: rs)

/-- Resolver variant used by the parser: unselected catalogue ambiguity is
    carried as an atom so expected-type parsing can refine it later.  The
    public resolve path remains strict via `resolveWithCues`. -/
def resolveWithCuesAllowAmbiguous (toks : List GlyphTok)
    : Except ResolveErr (List ResolvedTok) :=
  resolveWithCuesAllowAmbiguousAux toks 0 toks

/-! ### § 7.1  Cue 计算 sanity 例子 -/

/-- 「推 之 一」之 i=1 (「之」位置) 之 cues = [.betweenNominals]。
    「推」「一」皆 canonicalKind = .glyph (非 .operator/.particle/.modal). -/
example :
    computeCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩] 1
      = [ContextCue.betweenNominals] :=
  by native_decide

/-- i=0 且右邻不是明显参数起点 → 空 cues. -/
example :
    computeCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩] 0
      = ([] : List ContextCue) :=
  by native_decide

example :
    computeCues [⟨"反", 0, 1, false⟩, ⟨"乾", 2, 1, false⟩] 0
      = [ContextCue.expectedObject] :=
  by native_decide

example :
    computeCues [⟨"故", 0, 1, false⟩, ⟨"真", 2, 1, false⟩] 0
      = [ContextCue.expectedProp] :=
  by native_decide

example :
    computeCues [⟨"或", 0, 1, false⟩, ⟨"者", 2, 1, false⟩] 0
      = [ContextCue.quantifierDomain] :=
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

/-! ### § 7.2.1  Cue selection for ambiguous catalogue surfaces -/

example :
    (uniqueCatalogueReading "或" [.quantifierDomain]).bind (·.operator?)
      = some OperatorId.Q_5 :=
  by native_decide

example :
    (uniqueCatalogueReading "或" [.expectedProp, .quantifierDomain]).bind (·.operator?)
      = some OperatorId.Q_5 :=
  by native_decide

example :
    uniqueCatalogueReading "或" [.expectedProp] = none :=
  by native_decide

example :
    (uniqueCatalogueReading "反" [.expectedObject]).bind (·.operator?)
      = some OperatorId.T_6 :=
  by native_decide

example :
    (uniqueCatalogueReading "反" [.expectedProp]).bind (·.operator?)
      = some OperatorId.N_6 :=
  by native_decide

example :
    (uniqueCatalogueReading "反" [.expectedOperator]).bind (·.operator?)
      = some OperatorId.Z_31 :=
  by native_decide

example :
    (uniqueCatalogueReading "故" [.mohistContext]).bind (·.operator?)
      = some OperatorId.P_1 :=
  by native_decide

example :
    uniqueCatalogueReading "故" [.expectedProp] = none :=
  by native_decide

example : uniqueCatalogueReading "或" [] = none := by native_decide
example : uniqueCatalogueReading "反" [] = none := by native_decide
example : uniqueCatalogueReading "故" [] = none := by native_decide
example : uniqueCatalogueReading "名分" [] = none := by native_decide

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

example :
    opIdsOfCues [⟨"反", 0, 1, false⟩, ⟨"乾", 2, 1, false⟩]
      = some [some OperatorId.T_6, none] :=
  by native_decide

example :
    (match resolveWithCuesAllowAmbiguous [⟨"反", 0, 1, false⟩] with
     | .ok [⟨_, .ambiguousOp candidates⟩] => candidates.length == 3
     | _ => false) = true :=
  by native_decide

example :
    (resolveWithCues [⟨"反", 0, 1, false⟩]).toOption.isNone = true :=
  by native_decide

example :
    opIdsOfCues [⟨"化", 0, 1, false⟩, ⟨"乾", 2, 1, false⟩]
      = some [some OperatorId.T_1, none] :=
  by native_decide

/-- B-5: 或 now resolves to `Tm.orB` builtin (priority above catalogue),
    so the cue path no longer routes to `Q_5`. The first atom is a
    `.builtinTm` whose `opId?` is `none`. -/
example :
    opIdsOfCues [⟨"或", 0, 1, false⟩, ⟨"者", 2, 1, false⟩, ⟨"甲", 4, 1, false⟩]
      = some [none, none, none] :=
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

/-! ## § 8  B-10 / B-11  Helpful classifications for unreachable surfaces -/

/-- B-10: 大 是 4 个多字卦名 (大有 / 大壮 / 大畜 / 大过) 的起字。 -/
example :
    hexCompoundsStartingWith "大"
      = ["大有", "大畜", "大过", "大壮", "大過", "大壯"] :=
  by native_decide

/-- B-10: 中 是 1 个多字卦名 (中孚) 的起字. -/
example : hexCompoundsStartingWith "中" = ["中孚"] := by native_decide

/-- B-10: 明 是 1 个多字卦名 (明夷) 的起字. -/
example : hexCompoundsStartingWith "明" = ["明夷"] := by native_decide

/-- B-10: 既 / 未 / 同 / 小 / 噬 / 家 / 归 / 歸 / 既濟 起字之全集. -/
example : isHexCompoundStarter "既" = true := by native_decide
example : isHexCompoundStarter "未" = true := by native_decide
example : isHexCompoundStarter "同" = true := by native_decide
example : isHexCompoundStarter "小" = true := by native_decide
example : isHexCompoundStarter "噬" = true := by native_decide
example : isHexCompoundStarter "家" = true := by native_decide
example : isHexCompoundStarter "归" = true := by native_decide
example : isHexCompoundStarter "歸" = true := by native_decide

/-- 单字 hex 名（如 乾 / 坤 / 离）不视作 compound starter（即便其名长度 = 1）. -/
example : isHexCompoundStarter "乾" = false := by native_decide
example : isHexCompoundStarter "坤" = false := by native_decide
example : isHexCompoundStarter "离" = false := by native_decide

/-- 普通算子 surface 不视作 compound starter. -/
example : isHexCompoundStarter "推" = false := by native_decide
example : isHexCompoundStarter "及" = false := by native_decide  -- 不是任何多字 hex 起字
example : isHexCompoundStarter "夷" = false := by native_decide  -- 是 *第二* 字 (明夷)

/-- B-11: 学派 surface 全集都识别. -/
example : isSchoolNamespaceSurface "墨经" = true := by native_decide
example : isSchoolNamespaceSurface "墨" = true := by native_decide
example : isSchoolNamespaceSurface "名家" = true := by native_decide
example : isSchoolNamespaceSurface "庄子" = true := by native_decide
example : isSchoolNamespaceSurface "中庸" = true := by native_decide
example : isSchoolNamespaceSurface "兵家" = true := by native_decide
example : isSchoolNamespaceSurface "孙子" = true := by native_decide

/-- 非学派 surface 不被误识. -/
example : isSchoolNamespaceSurface "推" = false := by native_decide
example : isSchoolNamespaceSurface "乾" = false := by native_decide
example : isSchoolNamespaceSurface "兼愛" = false := by native_decide  -- 在 spec 但未入表
example : isSchoolNamespaceSurface "仁" = false := by native_decide      -- 同上

/-- classifyNoReading 之分类逻辑：学派优先 > hex-compound starter > noReading. -/
example :
    classifyNoReading "墨经" 0
      = ResolveErr.schoolNamespaceName "墨经" 0 :=
  by native_decide

example :
    classifyNoReading "中" 5
      = ResolveErr.hexCompoundStarter "中" 5 ["中孚"] :=
  by native_decide

example :
    classifyNoReading "及" 0
      = ResolveErr.noReading "及" 0 :=
  by native_decide

/-- 「大」走 resolveCatalogueByTable：unpromoted-gap **AND** hex-compound starter
    → 取 hex-compound starter 分类（更具体）. -/
example :
    (match resolveCatalogueByTable ⟨"大", 0, 1, false⟩ with
     | .error (.hexCompoundStarter s _ _) => s == "大"
     | _ => false) = true :=
  by native_decide

/-- 「鼎」是 unpromoted-gap 但不是 compound starter → 保留旧错误. -/
example :
    (match resolveCatalogueByTable ⟨"鼎", 0, 1, false⟩ with
     | .error (.unpromotedHexagramGap s _) => s == "鼎"
     | _ => false) = true :=
  by native_decide

end SSBX.Foundation.Wen.WenSurface
