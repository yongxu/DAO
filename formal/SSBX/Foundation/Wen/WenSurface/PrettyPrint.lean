/-
# WenSurface.PrettyPrint — Tm → 文言 prose

把 typed-λ `Tm` 渲染成可读 wenyan 文言：

  prettyPrintTm .yi                                    -- → "一"
  prettyPrintTm Stdlib.cuoBody                         -- → "错"
  prettyPrintTm (.app .tuiBody .yi)                    -- → "推 一"
  prettyPrintTm Stdlib.hexIdBody                       -- → "者 x x"

## 设计

1. **47 个 Tm constructor** 全部覆盖：
   - 字面值 (`hexLit` / `boolLit` / `cellLit`)
   - 22 个 core builtin → 表驱动 `builtinGlyph`
   - 12 个 cell-endo builtin → 表驱动
   - `catalogue1/2/3 id args` → 取 `OperatorId.title` 之首字
   - `abs` / `app` / `var` → 「者 n body」 / 「f x」 / 「n」
2. **Hex 字面值** 用 `Hexagram.toIdx` + 在 `xuGua` 列表中线性查找其 King-Wen 序号，
   然后取 `canonicalHexNames` 对应名（如 「乾」/「坤」/「同人」）。
3. **Bool 字面值** 用 "真" / "假"。
4. **Cell 字面值** 用 R8 之 `(hex, shi)` 配对，分别 render hex name 与 shi 标签。
5. **Round-trip safety** 不强求 — 仅给可读 output；parser 之 cue resolve
   可能选 alternate glyph，round-trip 留待 follow-up.

   wen-2.0 ⑧ 备注：`所 PRED 者` desugars at parse time to `λ甲. PRED 甲`
   (a `Tm.abs`)，pretty-prints back as `者 甲 (PRED 甲)`；`Y 之所以 X`
   desugars to `.app X Y`，pretty-prints back as `X Y`。两种 surface
   relativization 形式 round-trip 都 lossy，但语义保持（v1 acceptable）。

## 状态

0 sorry / 0 axiom / 总函数. 关键例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Reading

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Wen.WenDef
open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators

/-! ## § 1  Builtin glyph table -/

/-- 22 个 Hex/Bool core builtin 之首选 wenyan glyph.
    其余（如 `var`/`app`/`abs`/literals）由顶层 `prettyPrintTm` 单独处理. -/
def builtinGlyph : Tm → Option String
  | .jia       => some "加"
  | .yi        => some "一"
  | .notB      => some "不"
  | .andB      => some "並"
  | .orB       => some "或"
  | .eqHex     => some "同"
  | .forallH   => some "凡"
  | .uniqueH   => some "唯"
  | .exactly3H => some "三"
  | .majorityH => some "過半"
  | .cuoH      => some "错"
  | .zongH     => some "综"
  | .huH       => some "互"
  | .cuoZongH  => some "错综"
  | .flip1H    => some "初爻"
  | .flip2H    => some "二爻"
  | .flip3H    => some "三爻"
  | .flip4H    => some "四爻"
  | .flip5H    => some "五爻"
  | .flip6H    => some "上爻"
  | .pairH     => some "對"
  | .dupH      => some "倍"
  | .list1H    => some "列一"
  | .list2H    => some "列二"
  | .list3H    => some "列三"
  | .headH     => some "首"
  | .eqCell    => some "同位"
  | .cuoC      => some "错位"
  | .zongC     => some "综位"
  | .huC       => some "互位"
  | .shiNextC  => some "进时"
  | .shiPrevC  => some "退时"
  | .flip1C    => some "位初爻"
  | .flip2C    => some "位二爻"
  | .flip3C    => some "位三爻"
  | .flip4C    => some "位四爻"
  | .flip5C    => some "位五爻"
  | .flip6C    => some "位上爻"
  | _          => none

/-! ## § 2  Hex / Bool / Cell literal rendering -/

/-- 在 (canonicalHexNames × xuGua) 配对中查 `h` 之名.
    若未匹配（理论上不可达 — xuGua 覆盖全 64 卦），回落到 「卦#idx」. -/
def hexagramSurfaceName (h : Hexagram) : String :=
  let rec aux : List (String × Hexagram) → Option String
    | [] => none
    | (n, x) :: rest => if x = h then some n else aux rest
  match aux canonicalHexNameRows with
  | some s => s
  | none   => "卦#" ++ toString (Hexagram.toIdx h).val

/-- Bool 字面值之文言：true → "真", false → "假". -/
def boolSurfaceName : Bool → String
  | true  => "真"
  | false => "假"

/-- R8 cell 字面值之渲染：「(hex,shi)」 — 给可读的复合形. -/
def cellSurfaceName (c : R8) : String :=
  let hexName := hexagramSurfaceName c.1
  let shiName : String :=
    match c.2 with
    | (false, false) => "道"
    | (false, true)  => "已"
    | (true, false)  => "今"
    | (true, true)   => "未"
  hexName ++ "·" ++ shiName

/-! ## § 3  Catalogue rendering helper -/

/-- 取 `OperatorId.title` 的首个汉字，去掉「/ 异体」与括注（"屬 / 属" → "屬"）.
    fallback 到完整 title 若分割失败. -/
def operatorPrimaryGlyph (id : OperatorId) : String :=
  let raw := OperatorId.title id
  -- 切掉空格、「/」与「(」之后的部分
  let trimmed :=
    (raw.splitOn " ").headD raw
  let trimmedNoSlash := (trimmed.splitOn "/").headD trimmed
  let trimmedNoParen := (trimmedNoSlash.splitOn "(").headD trimmedNoSlash
  if trimmedNoParen.isEmpty then raw else trimmedNoParen

/-! ## § 4  Top-level pretty printer -/

/-- Render a single `MatchPat` to its surface glyph. -/
def renderMatchPat : MatchPat → String
  | .lit h           => hexagramSurfaceName h
  | .boolP b         => boolSurfaceName b
  | .userP _ cn      => cn
  | .wildcard        => "_"
  | .varP n          => n

mutual
  /-- 把 `Tm` 渲染为可读的文言串.
      总函数（mutual with `prettyPrintArms`，结构递归 on Tm + MatchArms). -/
  def prettyPrintTm : Tm → String
    | .var n        => n
    | .abs n _ body => "者 " ++ n ++ " " ++ prettyPrintTm body
    | .app f x      => prettyPrintTm f ++ " " ++ prettyPrintTm x
    | .hexLit h     => hexagramSurfaceName h
    | .boolLit b    => boolSurfaceName b
    | .cellLit c    => cellSurfaceName c
    | .catalogue1 id a =>
        operatorPrimaryGlyph id ++ " " ++ prettyPrintTm a
    | .catalogue2 id a b =>
        operatorPrimaryGlyph id ++ " " ++ prettyPrintTm a ++ " " ++ prettyPrintTm b
    | .catalogue3 id a b c =>
        operatorPrimaryGlyph id ++ " " ++ prettyPrintTm a ++ " " ++
          prettyPrintTm b ++ " " ++ prettyPrintTm c
    -- wen-2.0 ⑥/⑩: 引语 wrap 用 「」（primary quote bracket）.
    | .quote body => "「" ++ prettyPrintTm body ++ "」"
    -- wen-2.0 ⑪: `执 「X」` quote-eval.  Show as `执 ` + body's pretty form.
    | .unquote q => "执 " ++ prettyPrintTm q
    -- wen-2.0 ④: user-ctor renders to its bare ctor name.
    | .userCtor _ cn => cn
    -- wen-2.0 ⑤: pattern match.  Pretty-prints as
    -- `析 <scrut> 为 <pat> → <body> | <pat> → <body> | …`
    | .«match» scrut arms =>
        "析 " ++ prettyPrintTm scrut ++ " 为 " ++ prettyPrintArms arms
    -- wen-2.0 ⑦: setOf / memberOf — nominalize predicate / set-membership.
    -- `setOf pred` renders as `pred 者`; `memberOf x s` as `x 属 s`.
    | .setOf pred => prettyPrintTm pred ++ " 者"
    | .memberOf x s => prettyPrintTm x ++ " 属 " ++ prettyPrintTm s
    | t =>
        match builtinGlyph t with
        | some s => s
        | none   => "?"  -- defensive

  /-- Pretty-print a chain of match arms, separated by `|`. -/
  def prettyPrintArms : MatchArms → String
    | .nil => ""
    | .cons p body .nil => renderMatchPat p ++ " → " ++ prettyPrintTm body
    | .cons p body rest =>
        renderMatchPat p ++ " → " ++ prettyPrintTm body ++ " | " ++ prettyPrintArms rest
end

/-! ## § 5  Sanity examples (≥ 5 by spec) -/

example : prettyPrintTm .yi = "一" := by native_decide

example : prettyPrintTm Stdlib.cuoBody = "错" := by native_decide

example : prettyPrintTm Stdlib.zongBody = "综" := by native_decide

example : prettyPrintTm Stdlib.huBody = "互" := by native_decide

example : prettyPrintTm Stdlib.cuoZongBody = "错综" := by native_decide

example : prettyPrintTm Stdlib.fanBody = "凡" := by native_decide

example : prettyPrintTm Stdlib.buBody = "不" := by native_decide

example : prettyPrintTm Stdlib.tongBody = "同" := by native_decide

example : prettyPrintTm Stdlib.hexIdBody = "者 x x" := by native_decide

example : prettyPrintTm (.app .cuoH .yi) = "错 一" := by native_decide

example : prettyPrintTm (.app Stdlib.tuiBody .yi) = "者 x 加 一 x 一" := by native_decide

example : prettyPrintTm Stdlib.endoCompBody
    = "者 f 者 g 者 x f g x" := by native_decide

example : prettyPrintTm (.boolLit true) = "真" := by native_decide

example : prettyPrintTm (.boolLit false) = "假" := by native_decide

example : prettyPrintTm (.hexLit Hexagram.heaven) = "乾" := by native_decide

example : prettyPrintTm (.hexLit Hexagram.earth) = "坤" := by native_decide

example : prettyPrintTm (.catalogue2 .E_2 (.hexLit Hexagram.heaven) (.hexLit Hexagram.earth))
    = "曰 乾 坤" := by native_decide

example : prettyPrintTm (.catalogue1 .T_10 (.hexLit Hexagram.heaven))
    = "推 乾" := by native_decide

/-! ### wen-2.0 ⑥/⑩ 之 prettyPrint -/

/-- Quoted hex literal: `.quote (.hexLit 乾)` → `「乾」`. -/
example : prettyPrintTm (.quote (.hexLit Hexagram.heaven)) = "「乾」" := by native_decide

/-- 曰 + quote: `子曰：「学」` shape — speaker = 甲 (heavenly stem).  -/
example :
    prettyPrintTm (.catalogue2 .E_2 (.var "甲") (.quote .yi))
      = "曰 甲 「一」" := by native_decide

/-- Quote-of-non-trivial expression: `「推 乾」`. -/
example :
    prettyPrintTm (.quote (.app .cuoH (.hexLit Hexagram.heaven)))
      = "「错 乾」" := by native_decide

end SSBX.Foundation.Wen.WenSurface
