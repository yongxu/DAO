/-
# Foundation.Wen.REPL — 文交互解释器 (read-eval-print loop)

`wen` CLI exe 之实现：包装
[wenyanCompileProgramWithDefs](./WenSurface/EndToEnd.lean) /
[wenyanCompile](./WenSurface/EndToEnd.lean) 等管线，给一个交互式 REPL。

## 行为

**每行输入为一“提交”（submission），可含多个 `；`/`。`/`;` 分隔的语句**
（B-1 修复，2026-05-18）。提交走 `wenyanCompileProgramWithDefs`：

- `定 NAME 为 BODY` / `定递 …` / `定 LHS 等 RHS` / `类 …` / `析 …` /
  `用 …` — 静默处理（声明类语句不打印输出）。
- 表达式 `exprStmt` — 按 type dispatch 打印：
  - `Hex` → King-Wen 64 卦名 + 6-bit pattern
  - `Bool` → `true` / `false`
  - `user T` (wen-2.0 ④ user inductive) → 提取 ctor name
  - 其他 → 显示 `<elaborated> : ty`

错误统一打印为 `programErrShow`（v1：薄包装，富格式留给 sub-plan 04）。
提交内多语句以**换行**呈现：每个 `exprStmt` 独立一行。

注：**当前提交无跨提交持久化**（Option A）— 每个 submission 是独立
program；def 仅在自身 submission 内可见。`定 X 为 Y；X 之 一` 之类
教学场景已可用。跨提交持久化（Option B）留给后续 sub-plan。

## REPL 命令

| 命令 | 行为 |
|------|------|
| `:help` | 列命令 |
| `:quit` | 退出 (`Ctrl-D` / EOF 同效) |
| `:type <expr>` | 编译单表达式并显示其类型 |
| (空) | 跳过 |
| 其他 | 默认 eval (多语句 OK) |

## 实现注

- Lean 4 `IO` monad — 用 `(← (← IO.getStdin).getLine)` 一行行读
- `IO.FS.Stdin.getLine` 返 `""` 表示 EOF (干净退出)
- 用 `Hexagram.kingWenIdx` + `hexagramOperatorAnchors` 查 CJK 名
- 状态: 0 sorry / 0 axiom / 总函数 (`partial def` 仅 loop 体)
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd
import SSBX.Foundation.Wen.WenSurface.ErrorRender
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

/-- Friendly multi-line rendering of a `WenSurfaceErr`, anchored to the
    original `src` line. Delegates to `renderWenSurfaceErr` from
    `WenSurface.ErrorRender` so that `typeMismatch` (and friends) show
    expected vs actual `Ty` plus a caret indicating the offending span.

    Previously this just printed `(repr e).pretty`, which for
    `ElabErr.typeMismatch` collapsed to the bare constructor name
    `SSBX.Foundation.Wen.WenSurface.ElabErr.typeMismatch` with no info
    (bug B-9). -/
def errShow (src : String) (e : WenSurfaceErr) : String :=
  renderWenSurfaceErr src e

/-- Single-line friendly summary of a `DefErr` (declaration-level
    failure). v1: thin `repr` wrapper; richer messages can come later. -/
def defErrShow : DefErr → String
  | .redefinition n          => s!"def redefinition: {n}"
  | .conflictWithCatalogue n => s!"def conflicts with catalogue name: {n}"
  | .emptyName               => "def: empty NAME"
  | .missingFor              => "def: missing `为`"
  | .emptyBody               => "def: empty BODY"
  | .recBodyNotLambda n      => s!"定递 body must be lambda (者 …): {n}"
  | .recMultiTokenName n     => s!"定递 name must be single token: {n}"
  | .recNameNotStem n        => s!"定递 name must be a Heavenly Stem: {n}"
  | .rewriteAmbiguous        => "定 ... 等 ... 为 ... ambiguous"
  | .rewriteEmptyLhs         => "rewrite rule: empty LHS"
  | .rewriteEmptyRhs         => "rewrite rule: empty RHS"
  | .rewriteLhsCompileFailed => "rewrite rule: LHS compile failed"
  | .rewriteRhsCompileFailed => "rewrite rule: RHS compile failed"
  | .rewriteRuleRejected r   => s!"rewrite rule rejected: {(repr r).pretty}"
  | .classMalformed raw      => s!"类 malformed: {raw}"
  | .classRedefinition n     => s!"类 redefinition: {n}"
  | .classNameConflict n     => s!"类 name conflict: {n}"
  | .classNoConstructors n   => s!"类 has no constructors: {n}"
  | .classCtorConflict tn cn => s!"类 {tn} ctor conflict: {cn}"
  | .matchMalformed raw      => s!"析 malformed: {raw}"
  | .matchNoArms raw         => s!"析 has no arms: {raw}"
  | .matchBadPattern raw     => s!"析 bad pattern: {raw}"
  | .matchArmBodyFailed raw  => s!"析 arm body failed: {raw}"
  | .matchScrutFailed        => "析 scrutinee compile failed"
  | .matchTypeError          => "析 type error"

/-- Render a `ProgramErrWithDefs` with a 1-indexed statement number for
    user friendliness. Passes `src` through to `errShow` so caret +
    expected/actual rendering survives (B-9). -/
def programErrShow (src : String) : ProgramErrWithDefs → String
  | .base i e     => s!"[stmt {i+1}] {errShow src e}"
  | .defError i e => s!"[stmt {i+1}] {defErrShow e}"

/-! ## § 3  Stmt-level eval dispatch -/

/-- Render the value of a single `exprStmt`'s `TypedTm`. -/
def showTypedTm (typed : TypedTm) : String :=
  match typed.ty with
  | .hex =>
    match denoteHex typed.tm with
    | some h => s!"{hexShow h} : Hex"
    | none   => s!"<elaborated> : Hex"
  | .bool =>
    match denoteBool typed.tm with
    | some b => s!"{toString b} : Bool"
    | none   => s!"<elaborated> : Bool"
  | .user tn =>
    -- wen-2.0 ④: a closed user-inductive value is a `.userCtor`.
    match typed.tm with
    | .userCtor _ cn => s!"{cn} : {tn}"
    | _              => s!"<elaborated> : {tn}"
  | t => s!"<elaborated> : {tyStr t}"

/-- Render one compiled `Stmt`. Declaration-class statements
    (`defStmt`, `rewriteStmt`, `classStmt`) are silent and return
    `none`; only `exprStmt` produces a visible output line. -/
def showStmt? : Stmt → Option String
  | .exprStmt typed => some (showTypedTm typed)
  | .defStmt _ _    => none
  | .rewriteStmt _  => none
  | .classStmt _ _  => none

/-! ## § 4  Submission-level eval dispatch -/

/-- Evaluate one submission (possibly multi-statement, separated by
    `；`/`。`/`;`) and produce the REPL output lines.

    On compile success: returns one line per `exprStmt` in source order
    (declaration statements are silent). Empty submissions / all-decl
    submissions yield `[]` (no output).
    On compile error: returns a single line with the error. -/
def evalSubmission (src : String) : List String :=
  match wenyanCompileProgramWithDefs src with
  | .error e   => [programErrShow src e]
  | .ok stmts  => stmts.filterMap showStmt?

/-- Backward-compatible single-line evaluator. Returns ONE string by
    joining all output lines with newlines (or an empty string if the
    submission produced no visible output). Kept for callers that
    still expect a `String` instead of `List String`. -/
def evalLine (src : String) : String :=
  String.intercalate "\n" (evalSubmission src)

/-- Type query: compile single expression and show `ty` without evaluating.
    `:type` does NOT support multi-statement submissions (the type of a
    program is not well-defined); falls back to single-stmt `wenyanCompile`. -/
def typeLine (src : String) : String :=
  match wenyanCompile src with
  | .error e => errShow src e
  | .ok typed => tyStr typed.ty

/-! ## § 5  Help text -/

def banner : String :=
  "wen 1.5 — 文言 interactive read-eval-print loop\n\
   Type :help for commands.  Ctrl-D or :quit to exit.\n\
   Multi-statement submissions: separate with ；/。/; (B-1)."

def helpText : String :=
  ":help            -- show this message\n\
   :quit            -- exit the REPL\n\
   :type <expr>     -- show the elaborated type of <expr>\n\
   <expr>           -- compile + evaluate + show result\n\
   <stmt₁>；<stmt₂> -- multi-statement submission (；/。/; separated)\n\n\
   Examples:\n\
     ≫ 一\n\
     ≫ 推 一\n\
     ≫ 凡 甲 同 甲 甲\n\
     ≫ 定 甲 为 错 之 一；甲\n\
     ≫ 类 五行 = 木 用 火 用 土 用 金 用 水；木\n\
     ≫ :type 推"

/-! ## § 6  Main loop -/

/-- Strip leading/trailing whitespace (including '\r' / '\n') from a line.
    Uses `String.trimAscii` (post-2026 deprecation of `String.trim`). -/
def trimLine (s : String) : String :=
  (s.trimAscii).toString

/-- Strip a known prefix `p` from `s` (if `s` starts with `p`),
    then trim the remainder. -/
def stripPrefix (p s : String) : Option String :=
  if s.startsWith p then some (trimLine (s.drop p.length).toString) else none

/-- Print all output lines from an `evalSubmission` result. Skips
    silent (no-output) submissions; one `IO.println` per visible line. -/
def emitSubmission (src : String) : IO Unit := do
  for line in evalSubmission src do
    IO.println line

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
          emitSubmission line
          go
  go

/-- Entry point: print banner then loop. -/
def main : IO Unit := do
  IO.println banner
  loop

end SSBX.Foundation.Wen.REPL
