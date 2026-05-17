/-
# Foundation.Wen.REPL — 文交互解释器 (read-eval-print loop)

`wen` CLI exe 之实现：包装现有的
[wenyanCompile](./WenSurface/EndToEnd.lean) /
[wenyanInterp](./WenSurface/EndToEnd.lean) /
[wenyanInterpBool](./WenSurface/EndToEnd.lean)
管线，给一个交互式 REPL。

## 行为

每行输入为一表达式，REPL 会:
- 编译 (lex + resolve + parse + elab + typecheck)
- 按 type dispatch:
  - `Hex` → `wenyanInterp` 取 `Hexagram`，按 King-Wen 64 卦名 + 6-bit pattern 渲染
  - `Bool` → `wenyanInterpBool` 取 `Bool`
  - 其他 (函数、pair、list、cell、catalogue) → 显示 typed.ty
- 错误 → 友好打印 `WenSurfaceErr` (full rich rendering 留给 sub-plan 04)

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
  | .quoted         => "Quoted"
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

/-! ## § 3  Eval dispatch -/

/-- Evaluate one source string and produce the REPL output line. -/
def evalLine (src : String) : String :=
  match wenyanCompile src with
  | .error e => errShow e
  | .ok typed =>
    match typed.ty with
    | .hex =>
      match wenyanInterp src with
      | .ok h    => s!"{hexShow h} : Hex"
      | .error e => errShow e
    | .bool =>
      match wenyanInterpBool src with
      | .ok b    => s!"{toString b} : Bool"
      | .error e => errShow e
    | t => s!"<elaborated> : {tyStr t}"

/-- Type query: compile and show `ty` without evaluating. -/
def typeLine (src : String) : String :=
  match wenyanCompile src with
  | .error e => errShow e
  | .ok typed => tyStr typed.ty

/-! ## § 4  Help text -/

def banner : String :=
  "wen 1.5 — 文言 interactive read-eval-print loop\n\
   Type :help for commands.  Ctrl-D or :quit to exit."

def helpText : String :=
  ":help            -- show this message\n\
   :quit            -- exit the REPL\n\
   :type <expr>     -- show the elaborated type of <expr>\n\
   <expr>           -- compile + evaluate + show result\n\n\
   Examples:\n\
     ≫ 一\n\
     ≫ 推 一\n\
     ≫ 凡 甲 同 甲 甲\n\
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
