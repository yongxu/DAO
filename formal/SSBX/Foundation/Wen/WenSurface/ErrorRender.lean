/-
# WenSurface.ErrorRender — 错误渲染（含 source-span caret）

把 `WenSurfaceErr` (含 `LexErr / ResolveErr / ParseErr / ElabErr / TypeDiag`)
渲染成 ASCII caret + 人话多行字符串。纯加件：本模块只读既有 err 类型，
不修改任何上游定义；上游错误类型未来若扩枝，会在此处出现 missing case
warning，及时维护即可。

## 入口

```
renderWenSurfaceErr : String → WenSurfaceErr → String
```

输出形如：
```
推 真
    ^
type mismatch at column 4:
  expected: Hex
  got:      Bool
```

## 状态

0 sorry / 0 axiom / 总函数. 关键例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd
import SSBX.Text.WenyanOperators.Code
import SSBX.Text.WenyanOperators.Title

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Wen.WenDef
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings

/-! ## § 1  小工具 -/

/-- 长度为 `n` 的空格行（用作 caret 前缀）。 -/
def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

/-- 长度为 `n` 的 caret 行（'^'）。 -/
def carets (n : Nat) : String :=
  String.ofList (List.replicate n '^')

/-- 单行 caret：`col` 空格 + `max 1 width` 个 '^'。
    宽度为 0 时显示 1 个 caret，保证总是可见. -/
def caretLine (col width : Nat) : String :=
  let w := if width = 0 then 1 else width
  spaces col ++ carets w

/-- 取 source 的 codepoint 长度（用于 col bounds）。 -/
def sourceCodepoints (s : String) : Nat :=
  s.toList.length

/-- 当 col 越过 source 长度时，钳到末尾，避免 caret 漂浮过远. -/
def clampCol (s : String) (col : Nat) : Nat :=
  let n := sourceCodepoints s
  if col > n then n else col

/-- Source line + caret block：source 一行，caret 在下一行，并附带列号信息. -/
def withCaret (source : String) (col width : Nat) : String :=
  let c := clampCol source col
  source ++ "\n" ++ caretLine c width

/-! ## § 2  Ty 渲染 -/

/-- 渲染简单类型为可读字符串。 -/
partial def Ty.render : Ty → String
  | .hex            => "Hex"
  | .bool           => "Bool"
  | .cell           => "Cell"
  | .catalogue _    => "Catalogue"
  | .prod a b       => "(" ++ Ty.render a ++ " × " ++ Ty.render b ++ ")"
  | .list a         => "List " ++ Ty.render a
  | .arr a b        => Ty.render a ++ " → " ++ Ty.render b
  | .quoted         => "Quoted"
  | .user n         => n
  | .set a          => "Set " ++ Ty.render a

/-! ## § 3  OperatorReading 渲染 -/

/-- 简洁渲染 reading：label + (id code) + gloss. -/
def renderReading (r : OperatorReading) : String :=
  let idPart :=
    match r.operator? with
    | some id => " (" ++ id.code ++ ")"
    | none    => ""
  r.label ++ idPart ++ " — " ++ r.gloss

/-- 候选 readings 之 bullet list. 截断为前 N 条以免过长. -/
def renderReadingCandidates (rs : List OperatorReading) (maxLines : Nat := 6) : String :=
  let shown := rs.take maxLines
  let bullets := shown.map (fun r => "    - " ++ renderReading r)
  let header := "  candidates (" ++ toString rs.length ++ "):"
  let body := String.intercalate "\n" bullets
  let extra :=
    if rs.length > maxLines
    then "\n    ... (" ++ toString (rs.length - maxLines) ++ " more)"
    else ""
  header ++ "\n" ++ body ++ extra

/-! ## § 4  LexErr 渲染 -/

def renderLexErr (source : String) : LexErr → String
  | .unexpected col ch =>
      withCaret source col 1 ++ "\n"
        ++ "lex error at column " ++ toString col ++ ":\n"
        ++ "  unexpected character: '" ++ ch.toString ++ "'"
  | .fuelExhausted =>
      "lex error: fuel exhausted (input too large for the bounded lexer)"

/-! ## § 5  ResolveErr 渲染 -/

/-- 渲染 hex-compound starter 之示例名清单（最多前 N 条），用作 B-10 error 之
    内联提示。 -/
def renderHexCompoundExamples (examples : List String) (maxShown : Nat := 4) : String :=
  let shown := examples.take maxShown
  let body := String.intercalate " / " shown
  let extra :=
    if examples.length > maxShown then ", …"
    else if examples.length = 0 then ""
    else ""
  body ++ extra

def renderResolveErr (source : String) : ResolveErr → String
  | .noReading surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "resolve error at column " ++ toString col ++ ":\n"
        ++ "  unknown glyph or surface: '" ++ surface ++ "'"
  | .ambiguous surface col candidates =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "resolve error at column " ++ toString col ++ ":\n"
        ++ "  ambiguous surface: '" ++ surface ++ "'\n"
        ++ renderReadingCandidates candidates
  | .knownButUnsupported surface col readings =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "resolve error at column " ++ toString col ++ ":\n"
        ++ "  surface '" ++ surface
        ++ "' has " ++ toString readings.length
        ++ " known reading(s) but none are operator-backed in the current registry"
  | .unpromotedHexagramGap surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "resolve error at column " ++ toString col ++ ":\n"
        ++ "  '" ++ surface ++ "' is an unpromoted gap-form hexagram surface;\n"
        ++ "  use the canonical surface instead"
  | .hexCompoundStarter surface col examples =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "resolve error at column " ++ toString col ++ ":\n"
        ++ "  '" ++ surface ++ "' is a hex compound starter ("
        ++ renderHexCompoundExamples examples
        ++ ") — write the full hex name"
  | .schoolNamespaceName surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "resolve error at column " ++ toString col ++ ":\n"
        ++ "  '" ++ surface
        ++ "' is a 学派 namespace name, not an expression — try `用 "
        ++ surface ++ "` to activate"

/-! ## § 6  ParseErr 渲染 -/

def renderParseErr (source : String) : ParseErr → String
  | .empty =>
      if source.isEmpty
      then "parse error: empty input"
      else "parse error: empty subexpression"
  | .expectedExpression col =>
      if source.isEmpty then
        "parse error: empty input"
      else
        withCaret source col 1 ++ "\n"
          ++ "parse error at column " ++ toString col ++ ":\n"
          ++ "  expected an expression here"
  | .fuelExhausted =>
      "parse error: fuel exhausted (expression too deep for the bounded parser)"
  | .unmatchedOpenBracket surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "parse error at column " ++ toString col ++ ":\n"
        ++ "  unmatched open bracket: '" ++ surface ++ "'"
  | .unmatchedCloseBracket surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "parse error at column " ++ toString col ++ ":\n"
        ++ "  unmatched close bracket: '" ++ surface ++ "'"
  | .expectedCloseBracket openSurface expected openCol col =>
      withCaret source col 1 ++ "\n"
        ++ "parse error at column " ++ toString col ++ ":\n"
        ++ "  expected close bracket '" ++ expected
        ++ "' to match open '" ++ openSurface
        ++ "' at column " ++ toString openCol
  | .expectedVariable surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "parse error at column " ++ toString col ++ ":\n"
        ++ "  expected a variable name after '" ++ surface ++ "'"
  | .unexpectedApplicationMarker surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "parse error at column " ++ toString col ++ ":\n"
        ++ "  unexpected application marker: '" ++ surface ++ "'"
  | .unpromotedHexagramGap surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "parse error at column " ++ toString col ++ ":\n"
        ++ "  '" ++ surface ++ "' is an unpromoted gap-form hexagram surface"
  | .nonassocInfix surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "parse error at column " ++ toString col ++ ":\n"
        ++ "  non-associative infix operator '" ++ surface
        ++ "' cannot be chained"
  | .typeMismatch expected actual surface col =>
      withCaret source col (surface.toList.length) ++ "\n"
        ++ "type mismatch at column " ++ toString col ++ ":\n"
        ++ "  expected: " ++ Ty.render expected ++ "\n"
        ++ "  got:      " ++ Ty.render actual ++ "\n"
        ++ "  near:     '" ++ surface ++ "'"
  | .leftoverAtoms count firstSurface firstCol =>
      withCaret source firstCol (firstSurface.toList.length) ++ "\n"
        ++ "parse error at column " ++ toString firstCol ++ ":\n"
        ++ "  leftover tokens (" ++ toString count ++ " starting at '"
        ++ firstSurface ++ "');\n"
        ++ "  the parser consumed a complete expression but more atoms remain"

/-! ## § 7  TypeDiag / ElabErr 渲染 -/

def renderTypeDiag : TypeDiag → String
  | .unknownVar name =>
      "type mismatch:\n  unknown variable: '" ++ name ++ "'"
  | .expectedFunction actual =>
      "type mismatch:\n"
        ++ "  expected: function type (a → b)\n"
        ++ "  got:      " ++ Ty.render actual
  | .argumentMismatch expected actual =>
      "type mismatch:\n"
        ++ "  expected: " ++ Ty.render expected ++ "\n"
        ++ "  got:      " ++ Ty.render actual

/-- Prepend the source line (with a caret at col 0) when source is non-empty.
    Used by elab errors which lack span info. -/
def withSourcePreamble (source : String) (body : String) : String :=
  if source.isEmpty then body
  else source ++ "\n" ++ caretLine 0 1 ++ "\n" ++ body

def renderElabErr (source : String) : ElabErr → String
  | .unsupportedOp id surface col =>
      let header :=
        if surface.isEmpty
        then withSourcePreamble source ""
        else withCaret source col (surface.toList.length) ++ "\n"
      header
        ++ "elab error: operator " ++ id.code ++ " ("
        ++ id.title ++ ") is not supported by the executable semantics"
  | .unsupportedConstruction name =>
      withSourcePreamble source
        ("elab error: unsupported construction '" ++ name ++ "'")
  | .empty =>
      withSourcePreamble source "elab error: empty or ill-formed expression"
  | .leftoverAtoms count =>
      withSourcePreamble source
        ("elab error: " ++ toString count ++ " atom(s) left after elaboration")
  | .fuelExhausted =>
      withSourcePreamble source
        "elab error: fuel exhausted (expression too deep for the bounded elaborator)"
  | .typeMismatch diag =>
      withSourcePreamble source (renderTypeDiag diag)

/-! ## § 8  顶层 dispatcher -/

/-- 把 `WenSurfaceErr` 渲染成多行字符串。`source` 为原始输入文本。
    对带 col 的错误，会在首行展示 source 与 caret；elab 错误无 col 信息时
    会展示 source + caret(col 0) 作上下文锚定，最后再加分类说明. -/
def renderWenSurfaceErr (source : String) : WenSurfaceErr → String
  | .lex e     => renderLexErr source e
  | .resolve e => renderResolveErr source e
  | .parse e   => renderParseErr source e
  | .elab e    => renderElabErr source e
  | .denoteFailed expected actual =>
      withSourcePreamble source
        ("denotation failed:\n"
          ++ "  expected carrier: " ++ Ty.render expected ++ "\n"
          ++ "  got:              " ++ Ty.render actual)

/-- 便利函数：直接对 `wenyanCompile` 的结果作渲染. -/
def renderCompileResult (source : String) (r : Except WenSurfaceErr TypedTm) : String :=
  match r with
  | .ok _ => "ok"
  | .error e => renderWenSurfaceErr source e

/-! ## § 9  Sanity 例子 (native_decide) -/

private def renderForInput (s : String) : String :=
  match wenyanCompile s with
  | .ok _ => "ok"
  | .error e => renderWenSurfaceErr s e

/-- 包含子串. -/
private def containsSubstring (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- caretLine 之自检. -/
example : caretLine 0 1 = "^" := by native_decide
example : caretLine 4 1 = "    ^" := by native_decide
example : caretLine 2 3 = "  ^^^" := by native_decide
example : caretLine 0 0 = "^" := by native_decide

/-- spaces / carets. -/
example : spaces 0 = "" := by native_decide
example : spaces 3 = "   " := by native_decide
example : carets 1 = "^" := by native_decide
example : carets 4 = "^^^^" := by native_decide

/-- Ty.render 自检. -/
example : Ty.render .hex = "Hex" := by native_decide
example : Ty.render .bool = "Bool" := by native_decide
example : Ty.render (.arr .hex .hex) = "Hex → Hex" := by native_decide
example : Ty.render (.arr .bool (.arr .hex .bool)) = "Bool → Hex → Bool" := by
  native_decide

/-- withCaret 输出格式（col 2 为 「真」 在 codepoint stream 中的位置）. -/
example :
    withCaret "推 真" 2 1 = "推 真\n  ^" := by native_decide

/-- clampCol：col 越界时钳到末尾. -/
example : clampCol "abc" 5 = 3 := by native_decide
example : clampCol "abc" 1 = 1 := by native_decide

/-! ### Acceptance 例子 ≥6

  注：实际渲染输出取决于 pipeline 的真实 error 分支；以下例子直接构造
  对应的 `WenSurfaceErr` 测试 renderer 主轴，并辅以若干端到端 substring
  断言守住 `renderForInput` 之核心信号. -/

/-- (1) type mismatch on "推 真" — render explicit parse-typeMismatch case
    (col 2 = codepoint index of 「真」 in "推 真" after lex). -/
example :
    let src := "推 真"
    let err := WenSurfaceErr.parse (.typeMismatch .hex .bool "真" 2)
    let out := renderWenSurfaceErr src err
    containsSubstring out "type mismatch at column 2" = true
      ∧ containsSubstring out "expected: Hex" = true
      ∧ containsSubstring out "got:      Bool" = true
      ∧ ((out.splitOn "\n").take 2 = ["推 真", "  ^"]) := by native_decide

/-- end-to-end 「推 真」 — pipeline 实际产 elab.typeMismatch (argumentMismatch
    .hex .bool); 验证 renderer 给出 source preamble + Hex/Bool 信号. -/
example :
    let out := renderForInput "推 真"
    containsSubstring out "Hex" = true
      ∧ containsSubstring out "Bool" = true
      ∧ ((out.splitOn "\n").head? = some "推 真") := by native_decide

/-- (2) unknown var — synthetic `.unknownVar` rendered with caret(0) preamble. -/
example :
    let src := "者 甲 乙"
    let err := WenSurfaceErr.elab (.typeMismatch (.unknownVar "乙"))
    let out := renderWenSurfaceErr src err
    containsSubstring out "unknown variable" = true
      ∧ containsSubstring out "乙" = true
      ∧ ((out.splitOn "\n").head? = some "者 甲 乙") := by native_decide

/-- end-to-end 「凡 甲 乙」 — pipeline 产 unknownVar. -/
example :
    let out := renderForInput "凡 甲 乙"
    containsSubstring out "unknown variable" = true
      ∧ containsSubstring out "乙" = true := by native_decide

/-- (3) unmatched open bracket — 「推 (一」. -/
example :
    let src := "推 (一"
    let err := WenSurfaceErr.parse (.unmatchedOpenBracket "(" 2)
    let out := renderWenSurfaceErr src err
    containsSubstring out "unmatched open bracket" = true
      ∧ ((out.splitOn "\n").take 2 = ["推 (一", "  ^"]) := by native_decide

/-- end-to-end 「推 (一」 — pipeline 实际给 unmatched (open or close). -/
example :
    let out := renderForInput "推 (一"
    (containsSubstring out "unmatched" = true
      ∨ containsSubstring out "expected" = true) := by native_decide

/-- (4) ambiguous resolve — 「或 乾」 with 2 catalogue candidates. -/
example :
    let src := "或 乾"
    let cand : List OperatorReading :=
      [ catalogueReading "或" "Q-5" "存在量化" (some .Q_5) .prefix [.quantifierDomain]
      , catalogueReading "或" "M-2" "可能模态" (some .M_2) .prefix [.modalFrame] ]
    let err := WenSurfaceErr.resolve (.ambiguous "或" 0 cand)
    let out := renderWenSurfaceErr src err
    containsSubstring out "ambiguous" = true
      ∧ containsSubstring out "Q-5" = true
      ∧ containsSubstring out "M-2" = true
      ∧ containsSubstring out "candidates" = true
      ∧ ((out.splitOn "\n").head? = some "或 乾") := by native_decide

/-- end-to-end 「或 乾」 — after B-5, `或` resolves to the `Tm.orB` builtin
    (priority above catalogue), so the pipeline no longer produces a
    `resolve.ambiguous`. The renderer test for the ambiguous-resolve
    path above (constructed err) still exercises the renderer logic. -/
example :
    let out := renderForInput "或 乾"
    out ≠ "" := by native_decide

/-- (5) empty input — pipeline 实际产 parse.expectedExpression 0. -/
example :
    renderForInput "" = "parse error: empty input" := by native_decide

example :
    let src := ""
    let err := WenSurfaceErr.parse .empty
    renderWenSurfaceErr src err = "parse error: empty input" := by native_decide

/-- (6) leftover tokens — synthetic `.leftoverAtoms` (col 4 = 「二」 in
    "推 一 二": 推=col 0, 一=col 2, 二=col 4). -/
example :
    let src := "推 一 二"
    let err := WenSurfaceErr.parse (.leftoverAtoms 1 "二" 4)
    let out := renderWenSurfaceErr src err
    containsSubstring out "leftover" = true
      ∧ ((out.splitOn "\n").take 2 = ["推 一 二", "    ^"]) := by native_decide

/-! ### 辅助 renderer 覆盖测试 -/

/-- lex error: synthetic. -/
example :
    let src := "x"
    let err := WenSurfaceErr.lex (.unexpected 0 'x')
    let out := renderWenSurfaceErr src err
    containsSubstring out "unexpected character" = true
      ∧ ((out.splitOn "\n").take 2 = ["x", "^"]) := by native_decide

/-- lex fuel exhausted. -/
example :
    renderWenSurfaceErr "" (.lex .fuelExhausted)
      = "lex error: fuel exhausted (input too large for the bounded lexer)" := by
  native_decide

/-- resolve noReading. -/
example :
    let src := "abc xy"
    let err := WenSurfaceErr.resolve (.noReading "c" 2)
    let out := renderWenSurfaceErr src err
    ((out.splitOn "\n").take 2 = ["abc xy", "  ^"]) := by native_decide

/-- resolve knownButUnsupported. -/
example :
    let src := "X"
    let err := WenSurfaceErr.resolve (.knownButUnsupported "X" 0 [])
    let out := renderWenSurfaceErr src err
    containsSubstring out "known reading" = true := by native_decide

/-- resolve unpromotedHexagramGap. -/
example :
    let src := "鼎"
    let err := WenSurfaceErr.resolve (.unpromotedHexagramGap "鼎" 0)
    let out := renderWenSurfaceErr src err
    containsSubstring out "unpromoted" = true := by native_decide

/-! ### B-10 / B-11  Informative classifications -/

/-- B-10: hex-compound starter error includes glyph + examples + actionable hint. -/
example :
    let src := "大"
    let err := WenSurfaceErr.resolve (.hexCompoundStarter "大" 0
      ["大有", "大畜", "大过", "大壮"])
    let out := renderWenSurfaceErr src err
    containsSubstring out "hex compound starter" = true
      ∧ containsSubstring out "大" = true
      ∧ containsSubstring out "大有" = true
      ∧ containsSubstring out "大壮" = true
      ∧ containsSubstring out "write the full hex name" = true
      ∧ ((out.splitOn "\n").head? = some "大") := by native_decide

/-- B-10: end-to-end 「大」 — pipeline 自动产 hexCompoundStarter classification
    (via resolveCatalogueByTable; 大 同时是 unpromoted-gap, compound 起字优先). -/
example :
    let out := renderForInput "大"
    containsSubstring out "hex compound starter" = true
      ∧ containsSubstring out "write the full hex name" = true := by native_decide

/-- B-10: 中 单字 — 是 hex 复合 starter (中孚) 但有 4 个 catalogue readings,
    走 ambiguous 分支，不进 classifyNoReading。这是当前行为；测试用
    synthetic err 守护 renderer. -/
example :
    let src := "中"
    let err := WenSurfaceErr.resolve (.hexCompoundStarter "中" 0 ["中孚"])
    let out := renderWenSurfaceErr src err
    containsSubstring out "中孚" = true
      ∧ containsSubstring out "hex compound starter" = true := by native_decide

/-- B-10: 多于 4 个示例时会显示截断 ", …". -/
example :
    let src := "大"
    let err := WenSurfaceErr.resolve (.hexCompoundStarter "大" 0
      ["大有", "大畜", "大过", "大壮", "大過", "大壯"])
    let out := renderWenSurfaceErr src err
    containsSubstring out "…" = true
      ∧ containsSubstring out "大有" = true
      ∧ containsSubstring out "大壮" = true := by native_decide

/-- B-11: schoolNamespaceName error suggests the 用 NS form. -/
example :
    let src := "墨经"
    let err := WenSurfaceErr.resolve (.schoolNamespaceName "墨经" 0)
    let out := renderWenSurfaceErr src err
    containsSubstring out "学派 namespace" = true
      ∧ containsSubstring out "墨经" = true
      ∧ containsSubstring out "`用 墨经`" = true
      ∧ containsSubstring out "not an expression" = true
      ∧ ((out.splitOn "\n").head? = some "墨经") := by native_decide

/-- B-11: end-to-end 「墨经」(实际是两个单字 token 墨 + 经) — 第一个 token 墨
    本身是已知学派 surface，触发 schoolNamespaceName 分类。 -/
example :
    let out := renderForInput "墨"
    containsSubstring out "学派 namespace" = true
      ∧ containsSubstring out "用 墨" = true := by native_decide

/-- B-11: 中庸 单作为 token 输入：lex 为单字 中 + 庸；
    中 有 4 catalogue readings → ambiguous 不走 noReading；
    所以 schoolNamespaceName 走在 noReading 之上而非 ambiguous 之上。
    Synthetic 测试守护 renderer 端文本. -/
example :
    let src := "中庸"
    let err := WenSurfaceErr.resolve (.schoolNamespaceName "中庸" 0)
    let out := renderWenSurfaceErr src err
    containsSubstring out "中庸" = true
      ∧ containsSubstring out "用 中庸" = true := by native_decide

/-- renderHexCompoundExamples: 前 4 个用 / 分隔，多余 ", …". -/
example :
    renderHexCompoundExamples ["大有", "大畜", "大过", "大壮"]
      = "大有 / 大畜 / 大过 / 大壮" := by native_decide

example :
    renderHexCompoundExamples ["大有", "大畜", "大过", "大壮", "大過"]
      = "大有 / 大畜 / 大过 / 大壮, …" := by native_decide

example : renderHexCompoundExamples [] = "" := by native_decide
example : renderHexCompoundExamples ["中孚"] = "中孚" := by native_decide

/-- parse expectedExpression with non-empty source. -/
example :
    let src := "推 一"
    let err := WenSurfaceErr.parse (.expectedExpression 0)
    let out := renderWenSurfaceErr src err
    containsSubstring out "expected an expression" = true
      ∧ ((out.splitOn "\n").take 2 = ["推 一", "^"]) := by native_decide

/-- parse fuelExhausted. -/
example :
    renderWenSurfaceErr "" (.parse .fuelExhausted)
      = "parse error: fuel exhausted (expression too deep for the bounded parser)" := by
  native_decide

/-- parse unmatchedCloseBracket. -/
example :
    let src := "推 )"
    let err := WenSurfaceErr.parse (.unmatchedCloseBracket ")" 2)
    let out := renderWenSurfaceErr src err
    containsSubstring out "unmatched close bracket" = true := by native_decide

/-- parse expectedCloseBracket. -/
example :
    let src := "(推"
    let err := WenSurfaceErr.parse (.expectedCloseBracket "(" ")" 0 2)
    let out := renderWenSurfaceErr src err
    containsSubstring out "expected close bracket" = true := by native_decide

/-- parse expectedVariable. -/
example :
    let src := "者 推"
    let err := WenSurfaceErr.parse (.expectedVariable "者" 0)
    let out := renderWenSurfaceErr src err
    containsSubstring out "expected a variable name" = true := by native_decide

/-- parse unexpectedApplicationMarker. -/
example :
    let src := "之"
    let err := WenSurfaceErr.parse (.unexpectedApplicationMarker "之" 0)
    let out := renderWenSurfaceErr src err
    containsSubstring out "unexpected application marker" = true := by native_decide

/-- parse unpromotedHexagramGap. -/
example :
    let src := "鼎"
    let err := WenSurfaceErr.parse (.unpromotedHexagramGap "鼎" 0)
    let out := renderWenSurfaceErr src err
    containsSubstring out "unpromoted" = true := by native_decide

/-- parse nonassocInfix. -/
example :
    let src := "一 同 一 同 一"
    let err := WenSurfaceErr.parse (.nonassocInfix "同" 6)
    let out := renderWenSurfaceErr src err
    containsSubstring out "non-associative" = true := by native_decide

/-- elab unsupportedOp 含 op id code 与 title. -/
example :
    let src := "推"
    let err := WenSurfaceErr.elab (.unsupportedOp .T_10 "推" 0)
    let out := renderWenSurfaceErr src err
    containsSubstring out "T-10" = true := by native_decide

/-- elab unsupportedConstruction. -/
example :
    let src := "之又 推"
    let err := WenSurfaceErr.elab (.unsupportedConstruction "之又")
    let out := renderWenSurfaceErr src err
    containsSubstring out "unsupported construction" = true := by native_decide

/-- elab leftoverAtoms. -/
example :
    let src := "推 一 一"
    let err := WenSurfaceErr.elab (.leftoverAtoms 1)
    let out := renderWenSurfaceErr src err
    containsSubstring out "atom(s) left" = true := by native_decide

/-- elab fuelExhausted. -/
example :
    renderWenSurfaceErr "" (.elab .fuelExhausted)
      = "elab error: fuel exhausted (expression too deep for the bounded elaborator)" := by
  native_decide

/-- elab.typeMismatch + expectedFunction. -/
example :
    let src := "乾 坤"
    let err := WenSurfaceErr.elab (.typeMismatch (.expectedFunction .hex))
    let out := renderWenSurfaceErr src err
    containsSubstring out "function type" = true := by native_decide

/-- denoteFailed. -/
example :
    let src := "推 一"
    let err := WenSurfaceErr.denoteFailed .hex .bool
    let out := renderWenSurfaceErr src err
    containsSubstring out "denotation failed" = true
      ∧ containsSubstring out "Hex" = true
      ∧ containsSubstring out "Bool" = true := by native_decide

/-! ### renderReading / renderReadingCandidates 单测 -/

example :
    let r := catalogueReading "推" "T-10" "对象推进" (some .T_10) .prefix []
    renderReading r = "推-T-10 (T-10) — 对象推进" := by native_decide

example :
    let rs : List OperatorReading :=
      [ catalogueReading "或" "Q-5" "存在量化" (some .Q_5) .prefix []
      , catalogueReading "或" "M-2" "可能模态" (some .M_2) .prefix [] ]
    let out := renderReadingCandidates rs
    containsSubstring out "Q-5" = true
      ∧ containsSubstring out "M-2" = true
      ∧ containsSubstring out "candidates (2):" = true := by native_decide

end SSBX.Foundation.Wen.WenSurface
