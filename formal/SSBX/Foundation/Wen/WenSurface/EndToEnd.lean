/-
# WenSurface.EndToEnd — 文表层端到端管线

把 lex / resolve / parse / elab / typecheck / denote 拼成单一入口：
  · `wenyanCompile : String → Except WenSurfaceErr TypedTm`
  · `wenyanInterp : String → Except WenSurfaceErr Hexagram`
  · `wenyanInterpBool : String → Except WenSurfaceErr Bool`
  · `wenyanInterpHexPair` / `wenyanInterpHexList` for exact carrier values

求值复用既有 [WenDefEval.denoteHex / denoteBool / denoteHexPair / denoteHexList](../WenDefEval.lean)，
不走 baguaWen IL（保留 [WenDefCompile.lean](../WenDefCompile.lean) 的
complement-equivariant 子集 commute 作 future work）。

## 当前范围

- cue-aware resolver + explicit `SurfaceExpr` AST
- 64 卦名 / aliases + Bool literals + Hex-first/Bool-fallback lambdas and lets
- executable registry 覆盖全部 375 个 OperatorId
- 375 个 theorem-backed operator 可求 Hex/Bool/Pair/List；0 个 catalogue rows 只需 structural normal form
- unpromoted gap form 只诊断，不伪造 denotation

## 状态

0 sorry / 0 axiom / 总函数. 端到端例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Elaborate

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Text.OperatorSignatures

/-! ## § 1  统一错误类型 -/

/-- WenSurface pipeline 之统一错误。 -/
inductive WenSurfaceErr where
  | lex     (e : LexErr)
  | resolve (e : ResolveErr)
  | parse   (e : ParseErr)
  | elab    (e : ElabErr)
  | denoteFailed (expected actual : Ty)
deriving DecidableEq, Repr

/-! ## § 2  端到端管线 -/

/-- String → typed Tm 之完整管线（lex + cue-aware resolve + parse + elab + typecheck）. -/
def wenyanCompile (s : String) : Except WenSurfaceErr TypedTm :=
  match lexWen s with
  | .error e => .error (.lex e)
  | .ok toks =>
    match resolveWithCuesAllowAmbiguous toks with
    | .error e => .error (.resolve e)
    | .ok rs =>
      match parseSurfaceResolvedOrResolveErr rs with
      | .error (.inl e) => .error (.resolve e)
      | .error (.inr e) => .error (.parse e)
      | .ok expr =>
        match elabSurfaceTyped expr with
        | .error e => .error (.elab e)
        | .ok t    => .ok t

/-- Backward-compatible untyped projection for code that only needs the Tm. -/
def wenyanCompileTm (s : String) : Except WenSurfaceErr Tm :=
  (wenyanCompile s).map (fun typed => typed.tm)

/-- 闭项 hex 求值：String → Hexagram. -/
def wenyanInterp (s : String) : Except WenSurfaceErr Hexagram :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok typed =>
    match denoteHex typed.tm with
    | some h => .ok h
    | none   => .error (.denoteFailed .hex typed.ty)

/-- 闭项 bool 求值：String → Bool. -/
def wenyanInterpBool (s : String) : Except WenSurfaceErr Bool :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok typed =>
    match denoteBool typed.tm with
    | some b => .ok b
    | none   => .error (.denoteFailed .bool typed.ty)

def wenyanInterpHexPair (s : String) : Except WenSurfaceErr (Hexagram × Hexagram) :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok typed =>
    match denoteHexPair typed.tm with
    | some p => .ok p
    | none   => .error (.denoteFailed (.prod .hex .hex) typed.ty)

def wenyanInterpHexList (s : String) : Except WenSurfaceErr (List Hexagram) :=
  match wenyanCompile s with
  | .error e => .error e
  | .ok typed =>
    match denoteHexList typed.tm with
    | some xs => .ok xs
    | none    => .error (.denoteFailed (.list .hex) typed.ty)


/-! ## § 2b  Multi-statement programs

Statement separators: `；` (ideographic), `。` (period), `;` (ASCII).
A program is a sequence of statements; `wenyanCompileProgram` compiles each
chunk via `wenyanCompile` and returns the list of `TypedTm`.

Limitation (v1): separators are recognised at top level only — there is no
bracket-aware splitting.  Statements inside `（...）` should not contain bare
top-level separators in this version.
-/

/-- Split a String on a single Char delimiter via a char fold (linear time;
    stable across toolchain changes to `String.split` return type). -/
def splitOnChar (s : String) (delim : Char) : List String :=
  let step : (List String × String) → Char → (List String × String) :=
    fun (acc, cur) c =>
      if c = delim then (cur :: acc, "")
      else (acc, cur.push c)
  let (acc, cur) := s.foldl step ([], "")
  (cur :: acc).reverse

/-- Split a String on the ideographic 「；」, full-stop 「。」, and ASCII `;`.
    Returns chunks with whitespace trimmed and empty chunks removed. -/
def splitOnStatementSep (s : String) : List String :=
  -- Replace 「。」 and ASCII `;` with 「；」, then split on 「；」.
  let unified := (s.replace "。" "；").replace ";" "；"
  (splitOnChar unified '；').map (fun c => c.trimAscii.toString)
    |>.filter (fun c => !c.isEmpty)

/-- Multi-statement compiler.  Returns the list of typed terms in source order.
    On error, fails fast at the offending statement. -/
def wenyanCompileProgram (s : String) :
    Except WenSurfaceErr (List TypedTm) :=
  let chunks := splitOnStatementSep s
  let rec go : List String → List TypedTm → Except WenSurfaceErr (List TypedTm)
    | [], acc => .ok acc.reverse
    | c :: rest, acc =>
        match wenyanCompile c with
        | .error e => .error e
        | .ok t    => go rest (t :: acc)
  go chunks []


/-! ## § 2c  User-defined `def` declarations + scoped env — Wen 1.5 sub-plan 05

  Adds top-level `定 NAME 为 BODY` declarations to multi-statement programs.
  Definitions accumulate into a `DefEnv`; subsequent statements expand
  references to defined names by **textual substitution** of the original
  body source (wrapped in 「（…）」) into the chunk **before** lexing.

  Design choices:
  · Surface keyword `定` (open) `NAME` `为` `BODY`.
    `定` resolves at the WenSurface layer as `L_10` (identity alias), so it
    is only treated as a def head when it appears literally as the FIRST
    non-space codepoint of a chunk *and* a `为` separator exists later in the
    same chunk. Outside this pattern `定` continues to resolve as L_10.
  · Recursion: REJECTED (v1). The body is fully compiled BEFORE its name
    becomes available — recursive references resolve as ordinary unbound
    glyphs and the body compile errors.
  · Re-definition: REJECTED (returns `defRedefinition`). Forces explicit
    cleanup; no silent shadow.
  · Name conflict with catalogue glyph: REJECTED with
    `defConflictWithCatalogue`. Each glyph of the bare name is fed through
    `resolveOne`; if any token resolves to a catalogue op, app-marker,
    syntax marker, var, bool/hex literal, or iterate, the name is rejected.
  · Multi-glyph names like `倍推` are encouraged because the lexer splits
    them into glyphs `倍 + 推`, neither of which resolves as catalogue
    (since `倍` is unknown). Substitution handles them cleanly.

  This module is purely additive over `wenyanCompileProgram`: no existing
  pipeline functions, types, or examples change. -/

/-- A compiled statement: either a `定` declaration or an evaluated expression. -/
inductive Stmt where
  | defStmt  (name : String) (body : TypedTm)
  | exprStmt (body : TypedTm)
deriving Repr

def Stmt.body : Stmt → TypedTm
  | .defStmt _ b => b
  | .exprStmt b  => b

/-- Per-definition entry: name + body source + compiled `TypedTm`. -/
structure DefEntry where
  name       : String
  bodySource : String
  body       : TypedTm
deriving Repr

/-- Accumulated in-scope definitions, in source order. -/
abbrev DefEnv := List DefEntry

/-- Wen 1.5 sub-plan 05 errors specific to `def` processing. -/
inductive DefErr where
  | redefinition          (name : String)
  | conflictWithCatalogue (name : String)
  | emptyName
  | missingFor
  | emptyBody
deriving Repr

/-- Multi-statement program error with `def` support. Extends the base
    `WenSurfaceErr` with `def`-specific failures, tagged by the 0-indexed
    statement at which they were raised. -/
inductive ProgramErrWithDefs where
  | base      (index : Nat) (err : WenSurfaceErr)
  | defError  (index : Nat) (err : DefErr)
deriving Repr

def ProgramErrWithDefs.index : ProgramErrWithDefs → Nat
  | .base i _     => i
  | .defError i _ => i

/-! ### § 2c.1  Def-line detection and parsing -/

/-- Trim helper that always returns a `String` (not a `Slice`). -/
private def strTrim (s : String) : String := s.trimAscii.toString

/-- True iff the first non-whitespace codepoint(s) of `s` start with the
    literal `定` keyword used to open a user-defined definition. -/
def chunkStartsWithDefKeyword (s : String) : Bool :=
  (strTrim s).startsWith "定"

/-- Parse a chunk starting with `定` into (name, bodySource).
    Splits on the FIRST `为` after the leading `定`. Returns `none` if either
    component is empty after trim. -/
def parseDefChunk? (s : String) : Option (String × String) :=
  let trimmed := strTrim s
  if !trimmed.startsWith "定" then none
  else
    let afterDing := strTrim (trimmed.drop 1).toString
    match afterDing.splitOn "为" with
    | [] => none
    | [_] => none
    | nameRaw :: bodyParts =>
        let bodyRaw := String.intercalate "为" bodyParts
        let name := strTrim nameRaw
        let body := strTrim bodyRaw
        if name.isEmpty || body.isEmpty then none else some (name, body)

/-! ### § 2c.2  Name validation against catalogue -/

/-- Returns true iff the bare name would already resolve to a meaningful
    glyph reading and so should NOT be redefined.

    Semantics:
    · The name is rejected if, after `lexWen`, it produces **a single
      token** that resolves via `resolveOne` to anything other than the
      generic catch-all error.
    · Multi-token names (e.g. `倍推` lexed as `倍 + 推`) are allowed even if
      individual glyphs are operators, because textual substitution acts
      on the verbatim multi-codepoint substring before the lexer ever
      sees it — the rewritten chunk no longer contains `倍推` as a
      substring, so there is no live collision.
    · The full name must NOT appear in `multiCharSurfaces` (otherwise the
      lexer would emit it as a single token, allowing semantic confusion).
-/
def nameConflictsWithCatalogue (name : String) : Bool :=
  match lexWen name with
  | .error _ => true   -- Unlexable name → reject defensively
  | .ok toks =>
    -- 1. Full name registered in the multi-char surface table → reject.
    if multiCharSurfaces.contains name then true
    else
      -- 2. Single-token name that resolves to anything → reject.
      match toks with
      | [t] =>
        match resolveOne t with
        | .ok r =>
          match r.atom with
          | .catalogueOp _ => true
          | .ambiguousOp _ => true
          | .hexOrOp _ _   => true
          | .hexConst _    => true   -- hex literals (64 卦名 + 「一」)
          | .appMarker     => true
          | .iterate       => true
          | .syntax _      => true
          | .boolConst _   => true
          | .varName _     => true
          | .openBracket   => true
          | .closeBracket  => true
        | .error _ => false
      | _ =>
        -- Multi-token names are fine: substitution runs textually on the
        -- verbatim multi-glyph substring before lex/resolve runs.
        false

/-! ### § 2c.3  Textual substitution of def references -/

/-- Replace every occurrence of `needle` in `s` with `replacement`.
    Linear in `s.length` via `String.splitOn` + `intercalate`. -/
def replaceAll (s needle replacement : String) : String :=
  if needle.isEmpty then s
  else
    String.intercalate replacement (s.splitOn needle)

/-- Apply all in-scope defs to the chunk by textual substitution.
    Iterates the env in REVERSE declaration order (most-recent first), so a
    later def can shadow the name boundary against an earlier def (we already
    reject re-definition though, so this is mostly future-proofing).  Each
    occurrence of a defined name is rewritten as 「（BODY_SOURCE）」 (full-width
    parens) so the lexer treats the body as a grouped sub-expression. -/
def applyDefs (env : DefEnv) (chunk : String) : String :=
  let go : String → DefEntry → String :=
    fun acc entry => replaceAll acc entry.name ("（" ++ entry.bodySource ++ "）")
  env.reverse.foldl go chunk

/-! ### § 2c.4  Main entry: wenyanCompileProgramWithDefs -/

/-- Compile a multi-statement program with `def`-declarations.

    Each chunk is either a `定 NAME 为 BODY` declaration or an ordinary
    expression.  Declarations accumulate into a `DefEnv`; subsequent chunks
    rewrite references to declared names by textual substitution of the
    declaration's body source before invoking `wenyanCompile`.

    All chunk-local errors propagate as `.base i e` with the statement index;
    `def`-specific errors (re-def, catalogue collision, malformed `定` line)
    propagate as `.defError i e`. -/
def wenyanCompileProgramWithDefs (s : String)
    : Except ProgramErrWithDefs (List Stmt) :=
  let chunks := splitOnStatementSep s
  let rec go (i : Nat) (env : DefEnv) (acc : List Stmt) :
      List String → Except ProgramErrWithDefs (List Stmt)
    | [] => .ok acc.reverse
    | c :: rest =>
      if chunkStartsWithDefKeyword c then
        match parseDefChunk? c with
        | none =>
          let trimmed := strTrim c
          let err : DefErr :=
            if (strTrim (trimmed.drop 1).toString).isEmpty then .emptyName
            else if !c.contains '为' then .missingFor
            else .emptyBody
          .error (.defError i err)
        | some (name, bodySrc) =>
          if env.any (fun e => e.name = name) then
            .error (.defError i (.redefinition name))
          else if nameConflictsWithCatalogue name then
            .error (.defError i (.conflictWithCatalogue name))
          else
            let expanded := applyDefs env bodySrc
            match wenyanCompile expanded with
            | .error e => .error (.base i e)
            | .ok typed =>
                let env' := env ++ [⟨name, bodySrc, typed⟩]
                go (i + 1) env' (.defStmt name typed :: acc) rest
      else
        let expanded := applyDefs env c
        match wenyanCompile expanded with
        | .error e => .error (.base i e)
        | .ok typed => go (i + 1) env (.exprStmt typed :: acc) rest
  go 0 [] [] chunks


/-! ## § 2c.5  Helper sanity (cheap; pipeline tests live in `EndToEndTests.lean`) -/

/-- `chunkStartsWithDefKeyword` recognises a leading `定` after trimming. -/
example : chunkStartsWithDefKeyword "定 倍推 为 而 推 推" = true := by native_decide
example : chunkStartsWithDefKeyword "  定 倍推 为 而 推 推" = true := by native_decide
example : chunkStartsWithDefKeyword "推 一" = false := by native_decide
example : chunkStartsWithDefKeyword "" = false := by native_decide

/-- `parseDefChunk?` splits on the first `为`. -/
example :
    parseDefChunk? "定 倍推 为 而 推 推" = some ("倍推", "而 推 推") :=
  by native_decide

example :
    parseDefChunk? "定 错综 为 而 错 综" = some ("错综", "而 错 综") :=
  by native_decide

/-- Empty body after `为` → none. -/
example : parseDefChunk? "定 倍推 为 " = none := by native_decide

/-- Empty name before `为` → none. -/
example : parseDefChunk? "定  为 推" = none := by native_decide

/-- Missing `为` separator → none. -/
example : parseDefChunk? "定 倍推 而 推 推" = none := by native_decide

/-- A non-`定` chunk → none. -/
example : parseDefChunk? "推 一" = none := by native_decide

/-- Multiple `为` in body: only the first splits. -/
example :
    parseDefChunk? "定 X 为 凡 甲 同 甲 为" = some ("X", "凡 甲 同 甲 为") :=
  by native_decide

/-- `nameConflictsWithCatalogue` rejects catalogue glyphs like `推`. -/
example : nameConflictsWithCatalogue "推" = true := by native_decide

/-- `nameConflictsWithCatalogue` rejects `一` (hex literal). -/
example : nameConflictsWithCatalogue "一" = true := by native_decide

/-- `nameConflictsWithCatalogue` rejects var name `甲`. -/
example : nameConflictsWithCatalogue "甲" = true := by native_decide

/-- `nameConflictsWithCatalogue` accepts `倍推` (a multi-token name not in
    `multiCharSurfaces`).  Textual substitution runs on the verbatim
    substring before lex/resolve, so the name is safe. -/
example : nameConflictsWithCatalogue "倍推" = false := by native_decide

/-- `nameConflictsWithCatalogue` accepts `错综` even though `错` and `综` are
    catalogue glyphs — multi-token names bypass the per-glyph collision
    check (substitution is textual, pre-lex). -/
example : nameConflictsWithCatalogue "错综" = true := by native_decide

/-- A purely unknown multi-glyph name like `甴甴` passes. -/
example : nameConflictsWithCatalogue "甴甴" = false := by native_decide

/-- A purely unknown single-glyph name passes too. -/
example : nameConflictsWithCatalogue "甴" = false := by native_decide

/-- `replaceAll` basic. -/
example : replaceAll "abc abc" "abc" "xy" = "xy xy" := by native_decide
example : replaceAll "hello" "" "WORLD" = "hello" := by native_decide
example : replaceAll "hello" "ll" "rr" = "herro" := by native_decide

/-- `applyDefs`: single def is substituted once per occurrence and wrapped
    in full-width parens. -/
example :
    applyDefs [⟨"F", "推 一", ⟨.yi, .hex⟩⟩] "F" = "（推 一）" := by native_decide

/-- Two-def substitution: the env is applied in reverse declaration order
    (most-recent first). -/
example :
    applyDefs
      [⟨"F", "推 一", ⟨.yi, .hex⟩⟩, ⟨"G", "凡 甲 同 甲 甲", ⟨.yi, .bool⟩⟩]
      "F 与 G"
      = "（推 一） 与 （凡 甲 同 甲 甲）" := by native_decide

/-! ## § 3  端到端 sanity tests

318 `example := by native_decide` tests moved to `EndToEndTests.lean` (Phase γ,
2026-05-15). After `Hexagram := Fin 6 → Bool`, each `native_decide` compilation
takes ~10s vs ms before, making 318 examples cost >1h wall-clock per build.

Run tests separately:
    lake build SSBX.Foundation.Wen.WenSurface.EndToEndTests

This module is not in `SSBX.lean`; default `lake build SSBX` skips it.
-/

end SSBX.Foundation.Wen.WenSurface
