/-
# Foundation.Wen.REPL — 文交互解释器 (read-eval-print loop)

`wen` CLI exe 之实现：包装现有的
[wenyanCompile](./WenSurface/EndToEnd.lean) /
[wenyanInterp](./WenSurface/EndToEnd.lean) /
[wenyanInterpBool](./WenSurface/EndToEnd.lean)
管线，给一个交互式 REPL。

## 行为

每行输入为「一次提交」(submission)，可含多个由 「；」 / 「。」 / 「;」
分隔的 statement。REPL 会:
- 调 `wenyanCompileProgramWithDefs` 把整次提交编译成 `List Stmt`
  (支持 wen-2.0 ② 定/定递、④ 类、⑤ 析、⑫ rewrite-rule 各种 decl)
- 逐 Stmt 渲染:
  - `defStmt`     → `定: NAME`
  - `classStmt`   → `类: TYPENAME`
  - `rewriteStmt` → `定 (rewrite rule)`
  - `exprStmt`    → 按 type dispatch:
    - `Hex`  → `denoteHex`，按 King-Wen 64 卦名 + 6-bit pattern 渲染
    - `Bool` → `denoteBool`
    - 其他 (函数、pair、list、cell、catalogue) → 显示 typed.ty
- 错误 → 友好打印 `ProgramErrWithDefs` / `WenSurfaceErr`
  (full rich rendering 留给 sub-plan 04)

**注**: 此 REPL 没有 cross-submission 持久 def env (Option A v1)；每次
提交独立编译。要复用 def 需把整段一起提交 (如脚本 / heredoc 输入)。

## REPL 命令

| 命令 | 行为 |
|------|------|
| `:help` | 列命令 |
| `:quit` | 退出 (`Ctrl-D` / EOF 同效) |
| `:type <expr>` | 编译表达式并显示其类型 |
| (空) | 跳过 |
| 其他 | 默认 eval |

## 实现注

- Lean 4 `IO` monad — 用 `(← (← IO.getStdin).getLine)` 一行行读
- `IO.FS.Stdin.getLine` 返 `""` 表示 EOF (干净退出)
- 用 `Hexagram.kingWenIdx` + `hexagramOperatorAnchors` 查 CJK 名
- 状态: 0 sorry / 0 axiom / 总函数 (`partial def` 仅 loop 体)
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd
import SSBX.Foundation.Atlas.Yi.Classical.Core.Yi
import SSBX.Text.OperatorAnchors

namespace SSBX.Foundation.Wen.REPL

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Foundation.Wen.WenSurface
open SSBX.Text.OperatorAnchors

/-! ## § 1  Pretty printers -/

/-- `Ty` → human-readable string with arrows. -/
partial def tyStr : Ty → String
  | .hex            => "Hex"
  | .bool           => "Bool"
  | .cell           => "Cell"
  | .catalogue k    => s!"Catalogue({(repr k).pretty})"
  | .prod a b       => s!"({tyStr a} × {tyStr b})"
  | .list a         => s!"List {tyStr a}"
  | .quoted         => "Quoted"   -- wen-2.0 ⑥/⑩ 引语括号 payload
  | .user n         => n          -- wen-2.0 ④ user inductive type
  | .set a          => s!"Set {tyStr a}"  -- wen-2.0 ⑦ predicate extension
  | .arr a b        =>
    -- right-associate: `a → b → c` rather than `a → (b → c)`
    match a with
    | .arr _ _ => s!"({tyStr a}) → {tyStr b}"
    | _        => s!"{tyStr a} → {tyStr b}"

/-- 6-bit pattern of a hexagram, low → high (i.e. y1 first, y6 last).
    `1` = 阳 (yang), `0` = 阴 (yin), matching `Wenyan.lean`'s
    `parseHexLit` / `hexToBits` convention. Since `yang = false`
    internally, we invert the underlying Bool. -/
def hexBits (h : Hexagram) : String :=
  -- yang (false) → '1';  yin (true) → '0'
  let bit (b : Bool) : Char := if b then '0' else '1'
  String.ofList
    [ bit h.y1, bit h.y2, bit h.y3, bit h.y4, bit h.y5, bit h.y6 ]

/-- Look up the CJK name of a hexagram via the 64-row anchor table.
    Returns the documentary form (e.g. "乾", "坤", "既济"). Falls back
    to "?" if the hexagram is not found (impossible, since the table is
    complete — `xuGua.length = 64`). -/
def hexCJKName (h : Hexagram) : String :=
  match hexagramOperatorAnchors.find? (fun a => a.hexagram = h) with
  | some anchor => anchor.name
  | none        => "?"

/-- Render a hexagram for REPL output: `«乾» (111111)` style. -/
def hexShow (h : Hexagram) : String :=
  s!"«{hexCJKName h}» ({hexBits h})"

/-! ## § 2  Error printer -/

/-- Single-line friendly summary of a `WenSurfaceErr`. Full rich rendering
    (column anchors, suggestions, etc.) lives in sub-plan 04. -/
def errShow : WenSurfaceErr → String
  | .lex e          => s!"lex error: {(repr e).pretty}"
  | .resolve e      => s!"resolve error: {(repr e).pretty}"
  | .parse e        => s!"parse error: {(repr e).pretty}"
  | .elab e         => s!"elab error: {(repr e).pretty}"
  | .denoteFailed expected actual =>
      s!"denote failed: expected {tyStr expected}, got {tyStr actual}"

/-- Single-line friendly summary of a `DefErr`. -/
def defErrShow : DefErr → String
  | .redefinition name           => s!"redefinition: {name}"
  | .conflictWithCatalogue name  => s!"name conflicts with catalogue: {name}"
  | .emptyName                   => "empty def name"
  | .missingFor                  => "missing 为 separator in def"
  | .emptyBody                   => "empty def body"
  | .recBodyNotLambda name       => s!"recursive def body not a lambda: {name}"
  | .recMultiTokenName name      => s!"recursive def name must be a single token: {name}"
  | .recNameNotStem name         => s!"recursive def name must be a Heavenly Stem (甲..癸): {name}"
  | .rewriteAmbiguous            => "ambiguous: chunk contains both 等 and 为"
  | .rewriteEmptyLhs             => "empty LHS in rewrite rule"
  | .rewriteEmptyRhs             => "empty RHS in rewrite rule"
  | .rewriteLhsCompileFailed     => "rewrite LHS compile failed"
  | .rewriteRhsCompileFailed     => "rewrite RHS compile failed"
  | .rewriteRuleRejected reason  => s!"rewrite rule rejected: {(repr reason).pretty}"
  | .classMalformed raw          => s!"malformed 类 decl: {raw}"
  | .classRedefinition tn        => s!"class redefinition: {tn}"
  | .classNameConflict tn        => s!"class name conflict: {tn}"
  | .classNoConstructors tn      => s!"class has no constructors: {tn}"
  | .classCtorConflict tn cn     => s!"class ctor conflict in {tn}: {cn}"
  | .matchMalformed raw          => s!"malformed 析 chunk: {raw}"
  | .matchNoArms raw             => s!"析 has no arms: {raw}"
  | .matchBadPattern raw         => s!"bad match pattern: {raw}"
  | .matchArmBodyFailed raw      => s!"match arm body compile failed: {raw}"
  | .matchScrutFailed            => "match scrutinee compile failed"
  | .matchTypeError              => "match type error (mismatched arm types?)"

/-- Single-line friendly summary of a multi-statement `ProgramErrWithDefs`. -/
def progErrShow : ProgramErrWithDefs → String
  | .base i e     => s!"stmt {i}: {errShow e}"
  | .defError i e => s!"stmt {i}: {defErrShow e}"

/-! ## § 3  Eval dispatch -/

/-- Render the result of evaluating a single typed expression `TypedTm`.
    Mirrors the original single-statement REPL dispatch: Hex via
    `denoteHex`, Bool via `denoteBool`, otherwise show the type. -/
def renderExpr (typed : TypedTm) : String :=
  match typed.ty with
  | .hex =>
    match denoteHex typed.tm with
    | some h => s!"{hexShow h} : Hex"
    | none   => s!"<unreduced> : Hex"
  | .bool =>
    match denoteBool typed.tm with
    | some b => s!"{toString b} : Bool"
    | none   => s!"<unreduced> : Bool"
  | t => s!"<elaborated> : {tyStr t}"

/-- Render one compiled `Stmt`: a short confirmation for decl-type statements,
    or the evaluated body for `exprStmt`. -/
def renderStmt : Stmt → String
  | .defStmt name _      => s!"定: {name}"
  | .rewriteStmt _       => "定 (rewrite rule)"
  | .classStmt tn _      => s!"类: {tn}"
  | .exprStmt typed      => renderExpr typed

/-- Evaluate one source submission and produce the REPL output.
    Multiple statements (separated by `；` / `。` / `;`) are each compiled
    and rendered in order; declarations print a short confirmation, and
    expressions display the evaluated result. Falls back to single-stmt
    compile only if the program-level pipeline errors out at parse stage
    (preserves legacy behavior + error messages for plain expressions). -/
def evalLine (src : String) : String :=
  match wenyanCompileProgramWithDefs src with
  | .ok stmts =>
    -- Render each statement on its own line; drop empty lines.
    let lines := (stmts.map renderStmt).filter (fun s => !s.isEmpty)
    String.intercalate "\n" lines
  | .error progErr =>
    -- For a single-statement submission, prefer the legacy single-stmt
    -- diagnostic (more focused than `stmt 0: ...`).  We detect this by
    -- checking the chunk count.
    let chunks := splitOnStatementSep src
    match chunks with
    | [_] =>
      match wenyanCompile src with
      | .error e => errShow e
      | .ok typed => renderExpr typed
    | _ => progErrShow progErr

/-- Type query: compile and show `ty` without evaluating.  For multi-stmt
    submissions we show the type of the last `exprStmt` (or the last stmt
    body); for non-decl single-stmt this reduces to the legacy behaviour. -/
def typeLine (src : String) : String :=
  match wenyanCompileProgramWithDefs src with
  | .ok stmts =>
    match stmts.reverse.head? with
    | some s =>
      match s.body? with
      | some typed => tyStr typed.ty
      | none =>
        match s with
        | .classStmt tn _  => s!"类 {tn}"
        | .rewriteStmt _   => "rewrite rule"
        | _                => "<no expression>"
    | none => "<empty program>"
  | .error _ =>
    -- Fall back to single-stmt path for clearer diagnostics.
    match wenyanCompile src with
    | .error e => errShow e
    | .ok typed => tyStr typed.ty

/-! ## § 4  Help text -/

def banner : String :=
  "wen — 文言 interactive read-eval-print loop\n\
   Multi-statement input supported via 「；」 / 「。」 / 「;」.\n\
   Type :help for commands.  Ctrl-D or :quit to exit."

def helpText : String :=
  ":help            -- show this message\n\
   :quit            -- exit the REPL\n\
   :type <expr>     -- show the elaborated type of <expr>\n\
   <stmts>          -- compile + evaluate; multi-stmt via 「；」/「。」/「;」\n\n\
   Examples:\n\
     ≫ 一\n\
     ≫ 推 一\n\
     ≫ 凡 甲 同 甲 甲\n\
     ≫ 定 甲 为 错 之 一；甲\n\
     ≫ :type 推"

/-! ## § 5  Main loop -/

/-- Strip leading/trailing whitespace (including '\r' / '\n') from a line.
    Uses `String.trimAscii` (post-2026 deprecation of `String.trim`). -/
def trimLine (s : String) : String :=
  (s.trimAscii).toString

/-- Strip a known prefix `p` from `s` (if `s` starts with `p`),
    then trim the remainder. -/
def stripPrefix (p s : String) : Option String :=
  if s.startsWith p then some (trimLine (s.drop p.length).toString) else none

partial def loop : IO Unit := do
  let stdin ← IO.getStdin
  let prompt := "≫ "
  let rec go : IO Unit := do
    IO.print prompt
    (← IO.getStdout).flush
    let raw ← stdin.getLine
    if raw.isEmpty then
      -- EOF
      IO.println ""
      pure ()
    else
      let line := trimLine raw
      if line.isEmpty then
        go
      else if line == ":quit" || line == ":q" then
        pure ()
      else if line == ":help" || line == ":h" || line == ":?" then
        IO.println helpText
        go
      else
        match stripPrefix ":type " line, stripPrefix ":t " line with
        | some rest, _ =>
          IO.println (typeLine rest)
          go
        | _, some rest =>
          IO.println (typeLine rest)
          go
        | none, none =>
          IO.println (evalLine line)
          go
  go

/-- Entry point: print banner then loop. -/
def main : IO Unit := do
  IO.println banner
  loop

end SSBX.Foundation.Wen.REPL
