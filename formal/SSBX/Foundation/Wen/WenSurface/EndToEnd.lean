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
import SSBX.Foundation.Wen.WenSurface.RewriteRules

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

/-- Variant of `wenyanCompile` that elaborates and typechecks in a non-empty
    context — used by wen-2.0 ② `定递` so chunks that reference recursive
    defs can name them as bound vars during compile, with AST-level
    substitution applied afterward.  Threads `ctx` through BOTH the parser
    (`parseSurfaceResolvedInCtx`) and the elaborator
    (`elabSurfaceTypedWithCtx`) so application-arity inference for var
    names works against the pre-bound recursive-def types. -/
def wenyanCompileInCtx (ctx : Ctx) (s : String) : Except WenSurfaceErr TypedTm :=
  match lexWen s with
  | .error e => .error (.lex e)
  | .ok toks =>
    match resolveWithCuesAllowAmbiguous toks with
    | .error e => .error (.resolve e)
    | .ok rs =>
      match parseSurfaceResolvedOrResolveErrInCtx ctx rs with
      | .error (.inl e) => .error (.resolve e)
      | .error (.inr e) => .error (.parse e)
      | .ok expr =>
        match elabSurfaceTypedWithCtx ctx expr with
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
    `defConflictWithCatalogue`.  Rules:
      ‣ Single-token names that `resolveOne` resolves to anything (catalogue
        op, app-marker, syntax marker, var, bool/hex literal, iterate) are
        rejected.
      ‣ Names appearing literally in `multiCharSurfaces` (e.g. `错综`) are
        rejected — those names would be lexed as a single multi-char token.
      ‣ All other multi-token names (e.g. `倍推`) are accepted because the
        lexer splits them into separate glyphs; textual substitution acts
        on the verbatim multi-codepoint substring before lex/resolve sees
        it, so there is no runtime collision.

  This module is purely additive over `wenyanCompileProgram`: no existing
  pipeline functions, types, or examples change. -/

/-- A compiled statement: a `定`/`定递` def, a `定 LHS 等 RHS` rewrite-rule
    decl, a `类 TYPENAME = …` user-inductive decl, or an evaluated
    expression. -/
inductive Stmt where
  | defStmt     (name : String) (body : TypedTm)
  | rewriteStmt (rule : RewriteRule)
  | exprStmt    (body : TypedTm)
  /-- wen-2.0 ④ `类 TYPENAME = CTOR₁ | … | CTORₙ` decl.  The `ctors`
      list preserves source order; each entry's `typeName` field equals
      `typeName`. -/
  | classStmt   (typeName : String) (ctors : List UserCtor)
deriving Repr

/-- For the convenience of consumers that only want the typed body of an
    expression / def statement.  `rewriteStmt`/`classStmt` have no runtime
    body, so we return `none`. -/
def Stmt.body? : Stmt → Option TypedTm
  | .defStmt _ b   => some b
  | .exprStmt b    => some b
  | .rewriteStmt _ => none
  | .classStmt _ _ => none

/-- Legacy `Stmt.body` accessor — defaults `rewriteStmt`/`classStmt` to a
    sentinel `TypedTm` so existing callers (`EndToEndTests.lean`) don't
    break.  New callers should use `Stmt.body?` or pattern-match.

    Rationale: every existing user of `Stmt.body` expects a `TypedTm`.
    Semantics-sensitive callers (REPL display, denote loop) have always
    done their own pattern match. -/
def Stmt.body : Stmt → TypedTm
  | .defStmt _ b   => b
  | .exprStmt b    => b
  | .classStmt _ _ => ⟨.yi, .hex⟩
  | .rewriteStmt r =>
    -- The LHS has whatever type `typeCheck [] r.lhs` says.  This may be
    -- `none` if LHS contains free pattern vars, but we still need to
    -- return *some* TypedTm; pick `.bool` as a defensive placeholder.
    match typeCheck [] r.lhs with
    | some ty => ⟨r.lhs, ty⟩
    | none    => ⟨r.lhs, .bool⟩

/-- Per-definition entry: name + body source + compiled `TypedTm`.
    `isRec` distinguishes Wen 1.5 textual `定` defs from Wen 2.0 ② `定递`
    recursive defs.  For recursive entries the `body` carries the already
    self-referential `.fix NAME ty body'` Tm; references in subsequent
    chunks are substituted at the AST level (not textually) to avoid
    infinite expansion. -/
structure DefEntry where
  name       : String
  bodySource : String
  body       : TypedTm
  isRec      : Bool := false
deriving Repr

/-- Accumulated in-scope definitions, in source order. -/
abbrev DefEnv := List DefEntry

/-- Wen 1.5 sub-plan 05 errors specific to `def` processing.
    wen-2.0 ② extends with:
      · `recBodyNotLambda` — `定递 NAME 为 BODY` requires BODY to elaborate
        to a `Tm.abs` (so we can extract the self-reference type).
      · `recMultiTokenName` — the recursive-def name must be a single
        resolver token (the `者` binder accepts only single-token vars).
      · `recNameNotStem` — for v1, `定递` NAMEs are restricted to the 10
        Heavenly Stems (甲乙丙丁戊己庚辛壬癸) — these are the only glyphs
        the resolver accepts as bare var names.  Other glyphs would fail
        to resolve at the call sites of the recursive def. -/
inductive DefErr where
  | redefinition          (name : String)
  | conflictWithCatalogue (name : String)
  | emptyName
  | missingFor
  | emptyBody
  | recBodyNotLambda      (name : String)
  | recMultiTokenName     (name : String)
  | recNameNotStem        (name : String)
  -- wen-2.0 ⑫: 定 LHS 等 RHS rewrite-rule decls.
  /-- The chunk contains BOTH `等` and `为` after the leading `定` —
      ambiguous between `定 NAME 为 BODY` (user-def) and
      `定 LHS 等 RHS` (rewrite rule).  User must restructure. -/
  | rewriteAmbiguous
  /-- Missing LHS or RHS of a `定 ... 等 ...` rewrite rule. -/
  | rewriteEmptyLhs
  | rewriteEmptyRhs
  /-- The LHS source failed to compile. -/
  | rewriteLhsCompileFailed
  /-- The RHS source failed to compile. -/
  | rewriteRhsCompileFailed
  /-- Rule rejected by `RewriteRules.addRule` (bare-var LHS, non-linear
      pattern, RHS extra vars, or head-tag collision with an existing
      rule). -/
  | rewriteRuleRejected   (reason : RewriteErr)
  -- wen-2.0 ④ `类 NAME = CTOR₁ | … | CTORₙ` errors
  /-- The decl `类 NAME = …` had an empty TYPENAME or no `=`. -/
  | classMalformed        (raw : String)
  /-- TYPENAME redeclared / clashes with another `类`. -/
  | classRedefinition     (typeName : String)
  /-- TYPENAME clashes with catalogue / existing 定 decl. -/
  | classNameConflict     (typeName : String)
  /-- An empty constructor list after `=`. -/
  | classNoConstructors   (typeName : String)
  /-- A ctor name clashes with another in-scope `类`/`定`/catalogue. -/
  | classCtorConflict     (typeName ctorName : String)
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
    literal `定递` keyword used to open a recursive user-def (wen-2.0 ②).
    Checked BEFORE `chunkStartsWithDefKeyword` so a `定递 …` line is not
    confused for a plain `定 递 …` (which would mis-parse name as `递`). -/
def chunkStartsWithRecDefKeyword (s : String) : Bool :=
  (strTrim s).startsWith "定递"

/-- True iff the first non-whitespace codepoint(s) of `s` start with the
    literal `定` keyword used to open a user-defined definition.  Returns
    `false` for `定递 …` chunks (those are handled by the recursive-def
    pipeline). -/
def chunkStartsWithDefKeyword (s : String) : Bool :=
  let t := strTrim s
  t.startsWith "定" && !t.startsWith "定递"

/-- Parse a chunk starting with `定` into (name, bodySource).
    Splits on the FIRST `为` after the leading `定`. Returns `none` if either
    component is empty after trim. -/
def parseDefChunk? (s : String) : Option (String × String) :=
  let trimmed := strTrim s
  if !trimmed.startsWith "定" || trimmed.startsWith "定递" then none
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

/-- True iff `s` (already trimmed) starts with `定` and contains `等` —
    a rewrite-rule chunk (wen-2.0 ⑫: `定 LHS 等 RHS`).

    The check is structural: we look for `等` anywhere AFTER the leading
    `定` codepoint.  The actual ambiguity guard (the body must NOT also
    contain `为`) is enforced separately by `chunkStartsWithRewriteKeyword`
    so that ambiguous chunks become a distinct diagnostic. -/
def chunkContainsDeng (s : String) : Bool :=
  s.contains '等'

/-- True iff the chunk should be parsed as a rewrite-rule decl.

    Rules:
    · must start with `定` (after trim)
    · must NOT start with `定递`
    · must contain `等`
    · must NOT contain `为` (to disambiguate from `定 NAME 为 BODY`).  A
      chunk containing both is rejected as `rewriteAmbiguous` upstream.

    Returning `false` here means the chunk is either a non-`定` chunk or
    a `定 NAME 为 BODY` user-def. -/
def chunkStartsWithRewriteKeyword (s : String) : Bool :=
  let t := strTrim s
  t.startsWith "定" && !t.startsWith "定递"
    && chunkContainsDeng t && !t.contains '为'

/-- Detect a chunk that is `定`-led and contains BOTH `等` and `为`.  This
    is ambiguous between a rewrite rule and a user-def; we raise
    `rewriteAmbiguous` rather than guessing. -/
def chunkIsAmbiguousDefRewrite (s : String) : Bool :=
  let t := strTrim s
  t.startsWith "定" && !t.startsWith "定递"
    && chunkContainsDeng t && t.contains '为'

/-- Parse a `定 LHS 等 RHS` chunk into (lhsSource, rhsSource).  Splits on
    the FIRST `等` after the leading `定`.  Both sides trimmed; returns
    `none` if either is empty. -/
def parseRewriteChunk? (s : String) : Option (String × String) :=
  let trimmed := strTrim s
  if !trimmed.startsWith "定" || trimmed.startsWith "定递" then none
  else if !chunkContainsDeng trimmed then none
  else
    let afterDing := strTrim (trimmed.drop 1).toString
    match afterDing.splitOn "等" with
    | [] => none
    | [_] => none
    | lhsRaw :: rhsParts =>
        let rhsRaw := String.intercalate "等" rhsParts
        let lhs := strTrim lhsRaw
        let rhs := strTrim rhsRaw
        if lhs.isEmpty || rhs.isEmpty then none else some (lhs, rhs)

/-- Parse a chunk starting with `定递` into (name, bodySource).
    Splits on the FIRST `为` after the leading `定递`.  Same shape as
    `parseDefChunk?` but consumes 2 codepoints of the prefix. -/
def parseRecDefChunk? (s : String) : Option (String × String) :=
  let trimmed := strTrim s
  if !trimmed.startsWith "定递" then none
  else
    -- drop the 2-codepoint prefix 「定递」
    let afterDingDi := strTrim (trimmed.drop 2).toString
    match afterDingDi.splitOn "为" with
    | [] => none
    | [_] => none
    | nameRaw :: bodyParts =>
        let bodyRaw := String.intercalate "为" bodyParts
        let name := strTrim nameRaw
        let body := strTrim bodyRaw
        if name.isEmpty || body.isEmpty then none else some (name, body)

/-! ### § 2c.1b  wen-2.0 ④ `类` decl detection + parsing

  Syntax: `类 TYPENAME = CTOR₁ | CTOR₂ | … | CTORₙ`

  - Statement separator (`；`/`。`/`;`) ends the decl.
  - Trimmed ctors are non-empty bare glyphs (one resolver token each).
  - Examples:  `类 五行 = 木 | 火 | 土 | 金 | 水`
              `类 真假 = 真 | 假`
-/

/-- True iff the first non-whitespace codepoint of `s` starts with `类`. -/
def chunkStartsWithClassKeyword (s : String) : Bool :=
  (strTrim s).startsWith "类"

/-- Parse `类 TYPENAME = CTOR₁ | CTOR₂ | … | CTORₙ` into
    `(typeName, [ctor₁, …, ctorₙ])`.

    Returns `none` if:
      · the chunk does not start with `类`, OR
      · there is no `=` separator, OR
      · TYPENAME is empty after trim, OR
      · the constructor list is empty.

    Each ctor is the trimmed substring between `|` separators (or the
    final tail).  Empty ctor names cause `none`. -/
def parseClassChunk? (s : String) : Option (String × List String) :=
  let trimmed := strTrim s
  if !trimmed.startsWith "类" then none
  else
    let afterLei := strTrim (trimmed.drop 1).toString
    match afterLei.splitOn "=" with
    | [] => none
    | [_] => none
    | nameRaw :: bodyParts =>
        let bodyRaw := String.intercalate "=" bodyParts
        let typeName := strTrim nameRaw
        if typeName.isEmpty then none
        else
          let ctors := (bodyRaw.splitOn "|").map strTrim
          if ctors.any String.isEmpty then none
          else if ctors.isEmpty then none
          else some (typeName, ctors)

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

/-- Apply all in-scope **non-recursive** defs to the chunk by textual
    substitution.  Iterates the env in REVERSE declaration order
    (most-recent first), so a later def can shadow the name boundary
    against an earlier def (we already reject re-definition though, so
    this is mostly future-proofing).  Each occurrence of a defined name
    is rewritten as 「（BODY_SOURCE）」 (full-width parens) so the lexer
    treats the body as a grouped sub-expression.

    Recursive (`定递`) entries are **skipped** here — their names are
    substituted at the AST level by `applyRecDefs` after compilation,
    avoiding the infinite-loop hazard of textually expanding a body that
    references itself. -/
def applyDefs (env : DefEnv) (chunk : String) : String :=
  let go : String → DefEntry → String :=
    fun acc entry =>
      if entry.isRec then acc
      else replaceAll acc entry.name ("（" ++ entry.bodySource ++ "）")
  env.reverse.foldl go chunk

/-- After the existing textual pipeline produces a `Tm`, apply AST-level
    substitution of recursive-def names with their compiled `.fix` Tm.
    Iterates the env in declaration order (oldest first) so a later rec-def
    that references an earlier rec-def works.  Uses
    `WenDef.substTmFree` (capture-avoiding on binders, safe because the
    replacement is a closed `.fix` term). -/
def applyRecDefs (env : DefEnv) (t : Tm) : Tm :=
  env.foldl (fun acc e =>
    if e.isRec then substTmFree e.name e.body.tm acc else acc) t

/-! ### § 2c.3c  wen-2.0 ④ user-ctor AST resolution

  When a chunk is elaborated by `elabSurfaceTypedWithCtx`, bare ctor
  glyphs (e.g. `木`) resolve as ordinary tokens — typically through
  `Reading.surfaceVarNames` as `.varName "木"` if they're heavenly stems,
  otherwise as catalogue ops if they collide.  After elaboration, we
  walk the Tm and rewrite each unbound `.var n` (or any leaf whose source
  surface was the ctor glyph) into `.userCtor typeName n` provided
  `n` appears in the user-ctor table and is NOT shadowed by a binder
  along the walk.

  This pass is a closure-respecting substitution: when we enter a
  binder `.abs name _ body` (or `.fix name _ body`) we DROP `name`
  from the table before recursing, restoring it afterwards is not
  needed because we descend into independent subtrees.
-/

/-- Rewrite the Tm's free `.var n` leaves into `.userCtor typeName n`
    when `n` appears in `ctors`.  `bound` accumulates currently-bound
    var names from enclosing `.abs` / `.fix` binders. -/
def resolveUserCtors (ctors : List UserCtor) : Tm → List String → Tm
  | .var n, bound =>
      if bound.contains n then .var n
      else
        match UserCtor.lookupType ctors n with
        | some tn => .userCtor tn n
        | none    => .var n
  | .abs n t body, bound =>
      .abs n t (resolveUserCtors ctors body (n :: bound))
  | .app f x, bound =>
      .app (resolveUserCtors ctors f bound) (resolveUserCtors ctors x bound)
  | .catalogue1 id a, bound =>
      .catalogue1 id (resolveUserCtors ctors a bound)
  | .catalogue2 id a b, bound =>
      .catalogue2 id (resolveUserCtors ctors a bound) (resolveUserCtors ctors b bound)
  | .catalogue3 id a b c, bound =>
      .catalogue3 id
        (resolveUserCtors ctors a bound)
        (resolveUserCtors ctors b bound)
        (resolveUserCtors ctors c bound)
  | .quote body, _ => .quote body  -- quote bodies are data; do not rewrite
  | .fix n t body, bound =>
      .fix n t (resolveUserCtors ctors body (n :: bound))
  | t, _ => t  -- literals + primitives + .userCtor leaves are stable

/-- Compile-time context that binds each in-scope recursive def's name to
    its inferred fixpoint type.  Used by `wenyanCompileInCtx` so chunks
    that reference rec-defs by name don't trigger unbound-var diagnostics
    during the elaborate / typecheck pass.  Order: most-recent first, so
    later defs shadow earlier defs of the same name (which we currently
    reject anyway). -/
def recDefCtx (env : DefEnv) : Ctx :=
  env.foldr (fun e acc => if e.isRec then (e.name, e.body.ty) :: acc else acc) []

/-- Compile-time context augmenting `recDefCtx` with each in-scope
    user-ctor name bound to its nominal `.user typeName` type.  Used so
    chunks that reference bare ctor glyphs don't trip
    `unknownVar`/`unsupported` diagnostics during elaborate/typecheck —
    they elaborate as `.var name : .user typeName`, then the post-pass
    `resolveUserCtors` rewrites them to `.userCtor typeName name`. -/
def recDefAndCtorCtx (env : DefEnv) (ctors : List UserCtor) : Ctx :=
  let baseCtx := recDefCtx env
  ctors.foldr (fun c acc => (c.name, .user c.typeName) :: acc) baseCtx

/-! ### § 2c.3b  Recursive-def name validation + type inference

  The recursive-def name must lex to **exactly one** token (the `者 NAME …`
  binder only accepts a single var token).  Multi-token names work for
  textual `定` defs but are rejected by `定递`.

  For a recursive `定递 F 为 BODY`, the desired fixpoint type T must satisfy
  `body' : T`  in ctx `[(F, T)]`  — i.e. the body's type *with F bound* equals
  T.  We discover T by trying a small list of candidates; if none fit, the
  def is rejected. -/

/-- True iff `name` lexes to a single token (acceptable as a `者` binder). -/
def isSingleTokenName (name : String) : Bool :=
  match lexWen name with
  | .error _ => false
  | .ok toks => toks.length = 1

/-- True iff `name` is one of the 10 Heavenly Stems (甲乙丙丁戊己庚辛壬癸).
    Only these are accepted as `定递` NAMEs in v1, since the WenSurface
    resolver (`Reading.surfaceVarNames`) accepts only these glyphs as bare
    var names — any other glyph would fail to resolve at the call sites of
    the recursive def. -/
def isHeavenlyStem (name : String) : Bool :=
  ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"].contains name

/-- Candidate types for inferring a recursive-def's fixpoint type.
    Ordered from most-common to least-common; the first that yields a
    typecheck wins.  Mirrors the candidate list in `Elaborate.lean`'s
    `者` binder elaborator. -/
def recFixTyCandidates : List Ty :=
  [ .arr .hex .hex
  , .arr .hex (.arr .hex .hex)
  , .arr .hex .bool
  , .arr .hex (.arr .hex .bool)
  , .arr .bool .bool
  , .arr .bool .hex
  , .hex
  , .bool ]

/-- Try each candidate fixpoint type for a recursive def's body.
    Returns the first `T` such that `typeCheck [(name, T)] body' = some T`. -/
def findRecFixTy? (name : String) (body : Tm) : Option Ty :=
  recFixTyCandidates.findSome? fun T =>
    match typeCheck [(name, T)] body with
    | some T' => if T = T' then some T else none
    | none    => none

/-! ### § 2c.4  Main entry: wenyanCompileProgramWithDefs -/

/-- Re-typecheck a `Tm` after AST-level substitution of recursive-def names.
    Returns `none` if the substituted term no longer typechecks (should not
    happen given that each replacement is a closed `.fix` of the bound type;
    safety net only). -/
private def retypeAfterRecSubst? (t : Tm) : Option TypedTm :=
  match typeCheck [] t with
  | some ty => some ⟨t, ty⟩
  | none    => none

/-! ### § 2c.3c  Rewrite-rule chunk compilation (wen-2.0 ⑫)

  Compiling a `定 LHS 等 RHS` chunk:

  1. Both sides are compiled via `wenyanCompileInCtx` against a context
     that pre-binds every Heavenly Stem as `.hex`.  This lets pattern
     variables (`甲`, `乙`, …) resolve as `Tm.var` without
     unknown-variable diagnostics.  The pattern's actual *type* is
     determined post-hoc by `typeCheck`; we use `.hex` here only as a
     plausible default that matches the dominant Hex-endomap use case
     (錯, 综, 互, etc.).
  2. The resulting LHS / RHS `Tm` pair is fed to `RewriteRules.addRule`.
     If accepted, the new rule is appended to the rewrite env and a
     `Stmt.rewriteStmt` is emitted.

  v1 limitation: only the 10 Heavenly Stems can appear as pattern vars
  (mirroring the `定递` NAME restriction — these are the only single-
  codepoint glyphs the WenSurface resolver treats as bare var names).
-/

/-- Ctx that pre-binds all 10 Heavenly Stems as `.hex`.  Used by the
    rewrite-rule compiler so pattern vars resolve cleanly. -/
def heavenlyStemHexCtx : Ctx :=
  [ ("甲", .hex), ("乙", .hex), ("丙", .hex), ("丁", .hex), ("戊", .hex)
  , ("己", .hex), ("庚", .hex), ("辛", .hex), ("壬", .hex), ("癸", .hex) ]

/-- Compile (in an environment-aware way) one side of a rewrite-rule
    declaration.  Returns just the `Tm` (drops type) since rewrite rules
    operate at the Tm level. -/
def compileRewriteSide (env : DefEnv) (src : String) : Except WenSurfaceErr Tm :=
  -- Apply existing non-rec defs textually (so user-named macros work in
  -- rule patterns) but DO NOT recursively expand `.fix` bodies.
  let expanded := applyDefs env src
  let ctx := heavenlyStemHexCtx ++ recDefCtx env
  match wenyanCompileInCtx ctx expanded with
  | .error e => .error e
  | .ok typed =>
    -- AST-substitute rec-def names (preserves closed `.fix` body).
    let substituted := applyRecDefs env typed.tm
    .ok substituted

/-- Compile a multi-statement program with `def` / `定递` / rewrite-rule /
    `类` declarations.

    Each chunk is one of:
      · `定递 NAME 为 BODY`  — wen-2.0 ② μ-fixpoint recursive def.  Compiles
        `者 NAME （BODY）` to obtain `.abs NAME T body'`, then wraps as
        `.fix NAME T body'`.  Subsequent references to NAME are
        AST-substituted (not textual) so the recursive body's self-reference
        is preserved without infinite textual expansion.
      · `定 LHS 等 RHS`     — wen-2.0 ⑫ rewrite rule.  Adds a structural
        equational rewrite that normalises subsequent terms.
      · `定 NAME 为 BODY`   — Wen 1.5 non-recursive textual def.
      · `类 TYPENAME = CTOR₁ | … | CTORₙ` — wen-2.0 ④ user inductive type.
        Registers `typeName` + each `CTORᵢ` in the in-scope user-ctor
        table; subsequent expressions resolve bare `CTORᵢ` glyphs to
        `Tm.userCtor typeName ctorᵢ` after elaboration.
      · ordinary expression.

    Chunks that match both `等` and `为` after a leading `定` are rejected
    as `rewriteAmbiguous` to avoid silently picking one parse.

    Declarations accumulate into a `DefEnv` (defs / rec defs), a
    `RewriteEnv` (rules), and a `List UserCtor` table (类 ctors).  Each
    subsequent expression chunk is normalised by `RewriteRules.normalize`
    AFTER AST-subst and re-typechecked.  User-ctor resolution runs on
    `定`/expression bodies after rec-subst.

    All chunk-local errors propagate as `.base i e`; declaration-specific
    failures (re-def, catalogue collision, malformed `定`/`定递`/`类`
    line, class-ctor clash, malformed/rejected rewrite rule, ambiguous
    `定 ... 等 ... 为 ...`) propagate as `.defError i e`. -/
def wenyanCompileProgramWithDefs (s : String)
    : Except ProgramErrWithDefs (List Stmt) :=
  let chunks := splitOnStatementSep s
  let rec go (i : Nat) (env : DefEnv) (rwEnv : RewriteEnv)
      (ctors : List UserCtor) (acc : List Stmt) :
      List String → Except ProgramErrWithDefs (List Stmt)
    | [] => .ok acc.reverse
    | c :: rest =>
      if chunkStartsWithClassKeyword c then
        match parseClassChunk? c with
        | none =>
            .error (.defError i (.classMalformed (strTrim c)))
        | some (typeName, ctorNames) =>
            -- 1. Reject TYPENAME clashes: existing 类 decl, def, or
            --    catalogue (we reuse `nameConflictsWithCatalogue` —
            --    even multi-token typenames are conservative here).
            if ctors.any (fun uc => uc.typeName = typeName) then
              .error (.defError i (.classRedefinition typeName))
            else if env.any (fun e => e.name = typeName) then
              .error (.defError i (.classNameConflict typeName))
            else if nameConflictsWithCatalogue typeName then
              .error (.defError i (.classNameConflict typeName))
            else if ctorNames.isEmpty then
              .error (.defError i (.classNoConstructors typeName))
            else
              -- 2. Reject CTOR clashes against in-scope ctors / defs.
              --    A ctor name resolving to a catalogue op / hex literal /
              --    syntax marker is rejected (it would never reach the
              --    `.var` leaf where `resolveUserCtors` rewrites it).
              --    Heavenly stems (which `nameConflictsWithCatalogue`
              --    flags as `.varName`) are *allowed* because they
              --    resolve to `.var` leaves we can rewrite.
              let bareVarName (cn : String) : Bool :=
                match lexWen cn with
                | .error _ => false
                | .ok toks =>
                  match toks with
                  | [t] =>
                    match resolveOne t with
                    | .ok r =>
                      match r.atom with
                      | .varName _ => true
                      | _ => false
                    | .error _ => false  -- unknown glyph won't reach `.var` leaf
                  | _ => false           -- multi-token names not supported
              let conflict := ctorNames.find? (fun cn =>
                ctors.any (fun uc => uc.name = cn)
                  || env.any (fun e => e.name = cn)
                  || !bareVarName cn)
              match conflict with
              | some cn =>
                  .error (.defError i (.classCtorConflict typeName cn))
              | none =>
                  let newCtors := ctorNames.map (fun cn =>
                    ({ name := cn, typeName := typeName } : UserCtor))
                  let ctors' := ctors ++ newCtors
                  go (i + 1) env rwEnv ctors' (.classStmt typeName newCtors :: acc) rest
      else if chunkStartsWithRecDefKeyword c then
        match parseRecDefChunk? c with
        | none =>
          let trimmed := strTrim c
          let err : DefErr :=
            if (strTrim (trimmed.drop 2).toString).isEmpty then .emptyName
            else if !c.contains '为' then .missingFor
            else .emptyBody
          .error (.defError i err)
        | some (name, bodySrc) =>
          if env.any (fun e => e.name = name) then
            .error (.defError i (.redefinition name))
          else if !isSingleTokenName name then
            .error (.defError i (.recMultiTokenName name))
          else if !isHeavenlyStem name then
            -- v1 restriction: 定递 NAME must be a Heavenly Stem so it
            -- resolves as a bare var at the call sites of the recursive
            -- def.  Other glyphs would fail to resolve.  (Note: stems
            -- *do* trip `nameConflictsWithCatalogue` since they resolve
            -- as varName — that check is intentionally bypassed for
            -- 定递, which deliberately rebinds a stem to a closed `.fix`.)
            .error (.defError i (.recNameNotStem name))
          else
            -- Compile 者 NAME （expanded BODY）.  Existing non-rec defs are
            -- textually expanded in BODY first.  The wrapper makes NAME a
            -- bound var inside BODY so self-references resolve cleanly.
            -- The outer abs's domain type (`T_outer`) is whatever the
            -- elaborator picks — we re-infer the *fixpoint* type T
            -- independently via `findRecFixTy?` because T_outer may differ
            -- from T when NAME is unused in the body.
            let expandedBody := applyDefs env bodySrc
            let wrappedSrc := "者 " ++ name ++ " （" ++ expandedBody ++ "）"
            match wenyanCompileInCtx (recDefAndCtorCtx env ctors) wrappedSrc with
            | .error e => .error (.base i e)
            | .ok typed =>
                -- AST-substitute any earlier in-scope rec defs that this
                -- body uses.  Capture-avoiding subst (`substTmFree`) skips
                -- the outer 者 NAME binder cleanly.
                let substituted := applyRecDefs env typed.tm
                match substituted with
                | .abs n _ body' =>
                    match findRecFixTy? n body' with
                    | none =>
                        .error (.defError i (.recBodyNotLambda name))
                    | some fixTy =>
                        let fixTm : Tm := .fix n fixTy body'
                        match retypeAfterRecSubst? fixTm with
                        | none =>
                            .error (.defError i (.recBodyNotLambda name))
                        | some recTyped =>
                            let entry : DefEntry :=
                              { name := name, bodySource := bodySrc
                              , body := recTyped, isRec := true }
                            let env' := env ++ [entry]
                            go (i + 1) env' rwEnv ctors (.defStmt name recTyped :: acc) rest
                | _ =>
                    .error (.defError i (.recBodyNotLambda name))
      else if chunkIsAmbiguousDefRewrite c then
        -- 定 ... 等 ... 为 ...：cannot disambiguate.  Force user to rephrase.
        .error (.defError i .rewriteAmbiguous)
      else if chunkStartsWithRewriteKeyword c then
        match parseRewriteChunk? c with
        | none =>
          let trimmed := strTrim c
          let err : DefErr :=
            if (strTrim (trimmed.drop 1).toString).isEmpty then .rewriteEmptyLhs
            else .rewriteEmptyRhs
          .error (.defError i err)
        | some (lhsSrc, rhsSrc) =>
          match compileRewriteSide env lhsSrc with
          | .error _ => .error (.defError i .rewriteLhsCompileFailed)
          | .ok lhsTm =>
            match compileRewriteSide env rhsSrc with
            | .error _ => .error (.defError i .rewriteRhsCompileFailed)
            | .ok rhsTm =>
              match addRule rwEnv lhsTm rhsTm with
              | .error reason =>
                .error (.defError i (.rewriteRuleRejected reason))
              | .ok rwEnv' =>
                let rule : RewriteRule :=
                  { lhs := lhsTm, rhs := rhsTm, vars := freeVars lhsTm }
                go (i + 1) env rwEnv' ctors (.rewriteStmt rule :: acc) rest
      else if chunkStartsWithDefKeyword c then
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
          else if ctors.any (fun uc => uc.name = name) then
            -- wen-2.0 ④: 定 NAME 不可与 类 之 ctor 同名 (clash detection).
            .error (.defError i (.conflictWithCatalogue name))
          else if nameConflictsWithCatalogue name then
            .error (.defError i (.conflictWithCatalogue name))
          else
            let expanded := applyDefs env bodySrc
            match wenyanCompileInCtx (recDefAndCtorCtx env ctors) expanded with
            | .error e => .error (.base i e)
            | .ok typed =>
                -- Apply rec-def AST subst then user-ctor resolution.
                let substituted := applyRecDefs env typed.tm
                let resolved := resolveUserCtors ctors substituted []
                match retypeAfterRecSubst? resolved with
                | none => .error (.base i (.denoteFailed typed.ty typed.ty))
                | some typed' =>
                    let env' := env ++ [⟨name, bodySrc, typed', false⟩]
                    go (i + 1) env' rwEnv ctors (.defStmt name typed' :: acc) rest
      else
        let expanded := applyDefs env c
        match wenyanCompileInCtx (recDefAndCtorCtx env ctors) expanded with
        | .error e => .error (.base i e)
        | .ok typed =>
            let substituted := applyRecDefs env typed.tm
            -- wen-2.0 ④: resolve bare ctor glyphs into `.userCtor` leaves.
            let resolved := resolveUserCtors ctors substituted []
            -- wen-2.0 ⑫: apply accumulated rewrite rules to normalise.
            let normalized := normalize rwEnv resolved
            match retypeAfterRecSubst? normalized with
            | none => .error (.base i (.denoteFailed typed.ty typed.ty))
            | some typed' =>
                go (i + 1) env rwEnv ctors (.exprStmt typed' :: acc) rest
  go 0 [] [] [] [] chunks


/-! ## § 2d  Subject ellipsis (wen-2.0 ⑨) — PendingBinder state

  Classical Chinese commonly omits the subject across statements once it is
  bound by an earlier clause.  Example:

      凡 仁 者；其 心 為 善

  Meaning: `∀x. virtuous(x) → (x.mind = good)`, where `其` ("his") refers
  back to the bound `x` in the second clause.

  **v1 design** — pragmatic, narrow scope:

  · A statement is **open** (has a dangling binder) iff its elaborated `Tm`
    is `Tm.abs n t (.var n)` — i.e. a pure identity lambda waiting for an
    argument.  This is the simplest, structurally-recognisable "dangling
    subject" form.
  · After an open statement under a `；` separator, `PendingBinder` records
    `(n, t)`.  Subsequent statements compile with `(n, t)` pre-bound in the
    Ctx so references to `n` (and the new pronoun `其`, resolved to `n` —
    Step 2) typecheck.
  · After a `。` separator, the pending binder is cleared.
  · A non-open statement clears the pending binder.

  This is intentionally a minimal-viable design.  Broader patterns (e.g.
  `凡 X 仁 者；其 X` where the binder body is non-trivial) are out of v1
  scope — they require deciding whether to discard the body or build a
  conjunction, both of which have semantic pitfalls.
-/

/-- Detect the pending binder of an open statement.
    Returns `some (n, t)` iff the term is `Tm.abs n t (.var n)`, i.e. a pure
    identity lambda.  All other shapes are treated as closed. -/
def openBinderOf? : Tm → Option (String × Ty)
  | .abs n t (.var m) => if n = m then some (n, t) else none
  | _ => none

/-- Cross-statement pending binder state.  `none` = no open binder in scope. -/
abbrev PendingBinder := Option (String × Ty)

/-- Promote a `PendingBinder` to a typing Ctx extension (empty if none). -/
def pendingCtx (pb : PendingBinder) : Ctx :=
  match pb with
  | some (n, t) => [(n, t)]
  | none        => []

/-- Sanity: identity lambda `Tm.abs "甲" .hex (.var "甲")` is open. -/
example : openBinderOf? (.abs "甲" .hex (.var "甲")) = some ("甲", .hex) := by
  native_decide

/-- Sanity: a non-identity binder (body ≠ var n) is NOT open. -/
example : openBinderOf? (.abs "甲" .hex (.hexLit «一»)) = none := by
  native_decide

/-- Sanity: a binder whose body is a *different* var is not open. -/
example : openBinderOf? (.abs "甲" .hex (.var "乙")) = none := by
  native_decide

/-- Sanity: a non-binder term is not open. -/
example : openBinderOf? (.hexLit «一») = none := by
  native_decide

/-- Sanity: pendingCtx empty / singleton. -/
example : pendingCtx none = [] := by native_decide
example : pendingCtx (some ("甲", .hex)) = [("甲", .hex)] := by native_decide

/-! ### § 2d.1  `其` pronoun resolution

  Surface form: `其` ("his/its") inside a statement that follows an open
  binder is rewritten to the binder's variable name BEFORE lex/resolve.

  Design choice: textual substitution rather than resolver-level integration.
  Reasons:
  · Consistency with the Wen 1.5 `定 NAME 为 BODY` pipeline (which also
    uses textual substitution to expand user-defs).
  · The resolver is context-free; threading a runtime pending-binder state
    through it would be a much larger change.
  · `其` does NOT currently resolve to anything (no `OperatorReading`, no
    surface marker), so substituting it pre-lex has no collision risk.

  Note: we deliberately do NOT substitute `之` as a pronoun.  `之` is the
  application-marker (S_1) and re-purposing it would silently break
  thousands of catalogue invocations.

  Edge cases handled by `replaceAll` semantics:
  · Multiple `其` in one chunk all rewrite to the same name (correct: the
    pronoun refers to the SAME bound subject).
  · `其` appearing without a pending binder is left untouched — it will
    then fail to resolve as an unknown glyph and surface a clean
    parser-level error, which is the desired Wen 1.5 behaviour for unknown
    glyphs. -/

/-- Rewrite all literal occurrences of `其` in `chunk` to the pending
    binder's variable name (wrapped in spaces so it tokenises as a separate
    glyph). When `pb = none`, `chunk` is returned unchanged. -/
def applyPendingBinder (pb : PendingBinder) (chunk : String) : String :=
  match pb with
  | none        => chunk
  | some (n, _) => replaceAll chunk "其" (" " ++ n ++ " ")

/-- Sanity: no pending binder → no-op. -/
example : applyPendingBinder none "其 一" = "其 一" := by native_decide

/-- Sanity: pending binder `甲` rewrites `其` to `甲`. -/
example : applyPendingBinder (some ("甲", .hex)) "其" = " 甲 " := by native_decide

/-- Sanity: multiple occurrences. -/
example :
    applyPendingBinder (some ("甲", .hex)) "其 与 其" = " 甲  与  甲 " :=
  by native_decide

/-- Sanity: non-`其` chunk unchanged. -/
example : applyPendingBinder (some ("甲", .hex)) "推 一" = "推 一" := by native_decide

/-! ### § 2d.2  Separator-tagged statement split

  For subject ellipsis the SOFT vs HARD distinction between statement
  separators is load-bearing:

      `；` / `;` : SOFT — pending binder propagates to the next statement.
      `。`      : HARD — pending binder cleared at this boundary.

  `splitOnStatementSep` (used by the legacy pipeline) normalises all three
  separators to one, so we need a sibling that retains the kind.  Returned
  list is `(chunk, isSoft)` pairs in source order; the boolean indicates
  whether THIS chunk was followed by a soft separator (`true`) or a hard
  one / EOF (`false`). -/

inductive StmtSepKind where
  | soft   -- 「；」 or ASCII `;`
  | hard   -- 「。」 (also used at EOF)
deriving DecidableEq, Repr

/-- Result of separator-tagged split: each chunk + the separator that
    terminates it (hard at EOF). -/
abbrev TaggedChunk := String × StmtSepKind

/-- Walk the string char-by-char accumulating chunks, tagging each by the
    separator that closed it.  EOF emits a final chunk tagged `.hard`. -/
def splitOnStatementSepTagged (s : String) : List TaggedChunk :=
  let step : (List TaggedChunk × String) → Char → (List TaggedChunk × String) :=
    fun (acc, cur) c =>
      if c = '；' || c = ';' then
        ((cur, StmtSepKind.soft) :: acc, "")
      else if c = '。' then
        ((cur, StmtSepKind.hard) :: acc, "")
      else
        (acc, cur.push c)
  let (acc, cur) := s.foldl step ([], "")
  let withTail :=
    if cur.trimAscii.toString.isEmpty then acc
    else (cur, StmtSepKind.hard) :: acc
  withTail.reverse.map (fun (c, k) => (c.trimAscii.toString, k))
    |>.filter (fun (c, _) => !c.isEmpty)

/-- Sanity: soft separator. -/
example :
    splitOnStatementSepTagged "推 一；推 二" =
      [("推 一", .soft), ("推 二", .hard)] := by native_decide

/-- Sanity: hard separator. -/
example :
    splitOnStatementSepTagged "推 一。推 二" =
      [("推 一", .hard), ("推 二", .hard)] := by native_decide

/-- Sanity: mixed. -/
example :
    splitOnStatementSepTagged "推 一；推 二。推 三" =
      [("推 一", .soft), ("推 二", .hard), ("推 三", .hard)] := by native_decide

/-- Sanity: ASCII `;` is soft. -/
example :
    splitOnStatementSepTagged "推 一;推 二" =
      [("推 一", .soft), ("推 二", .hard)] := by native_decide

/-! ### § 2d.3  Ellipsis-aware multi-statement compiler

  Extends the no-defs pipeline with PendingBinder threading.  After each
  statement compiles, we inspect the resulting `Tm` via `openBinderOf?`:
  · If open AND the terminating separator is `.soft`, set PendingBinder
    to that `(name, ty)` for the next statement.
  · If closed OR the separator is `.hard`, clear PendingBinder.

  The next statement's source has `其` substituted (`applyPendingBinder`)
  and compiles in a Ctx that pre-binds the pending name.  This lets the
  body typecheck even though the binder is "outside" the statement.

  v1 limitation: the compiled `TypedTm` of an ellipsis-following statement
  is its raw `Tm` (with `Tm.var n` references to the pending binder).  We
  do NOT re-bind it as `Tm.abs n t body` — callers that want the
  λ-equivalent should compose with the prior statement's identity binder
  externally.  This keeps the per-statement output shape stable so
  existing `List TypedTm` consumers don't break. -/

/-- Multi-statement compiler with subject-ellipsis support.

    Returns one `TypedTm` per chunk in source order.  PendingBinder is
    threaded across `；` separators and cleared at `。` separators.  On the
    first compile error, fails fast at the offending statement. -/
def wenyanCompileProgramWithEllipsis (s : String) :
    Except WenSurfaceErr (List TypedTm) :=
  let tagged := splitOnStatementSepTagged s
  let rec go : PendingBinder → List TaggedChunk → List TypedTm →
      Except WenSurfaceErr (List TypedTm)
    | _,  [],            acc => .ok acc.reverse
    | pb, (c, sep) :: rest, acc =>
        let chunk := applyPendingBinder pb c
        match wenyanCompileInCtx (pendingCtx pb) chunk with
        | .error e => .error e
        | .ok typed =>
            let pb' :=
              match sep with
              | .hard => none
              | .soft =>
                  match openBinderOf? typed.tm with
                  | some nt => some nt
                  | none    => none
            go pb' rest (typed :: acc)
  go none tagged []

/-! ### § 2d.4  Helper sanity (more end-to-end tests live in EllipsisTests.lean) -/

/-- An empty program yields the empty list. -/
example : wenyanCompileProgramWithEllipsis "" = .ok [] := by native_decide

/-- A single non-binder statement compiles cleanly and produces one TypedTm
    of the right type. -/
example :
    (wenyanCompileProgramWithEllipsis "推 一").toOption.map (·.map (·.ty))
      = some [.hex] := by native_decide

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
    applyDefs [⟨"F", "推 一", ⟨.yi, .hex⟩, false⟩] "F" = "（推 一）" := by native_decide

/-- Two-def substitution: the env is applied in reverse declaration order
    (most-recent first). -/
example :
    applyDefs
      [⟨"F", "推 一", ⟨.yi, .hex⟩, false⟩, ⟨"G", "凡 甲 同 甲 甲", ⟨.yi, .bool⟩, false⟩]
      "F 与 G"
      = "（推 一） 与 （凡 甲 同 甲 甲）" := by native_decide

/-- Recursive entries are SKIPPED by `applyDefs` (textual substitution would
    risk infinite expansion; AST-level `applyRecDefs` handles them instead). -/
example :
    applyDefs [⟨"F", "推 一", ⟨.yi, .hex⟩, true⟩] "F" = "F" := by native_decide

/-! ## § 2c.6  wen-2.0 ④ `类` decl sanity (cheap; pipeline tests in `UserInductiveTests.lean`) -/

example : chunkStartsWithClassKeyword "类 五行 = 木 | 火" = true := by native_decide
example : chunkStartsWithClassKeyword "  类 真假 = 真 | 假" = true := by native_decide
example : chunkStartsWithClassKeyword "推 一" = false := by native_decide
example : chunkStartsWithClassKeyword "" = false := by native_decide

/-- Parse a 5-ctor 类 decl. -/
example :
    parseClassChunk? "类 五行 = 木 | 火 | 土 | 金 | 水"
      = some ("五行", ["木", "火", "土", "金", "水"]) := by native_decide

/-- 2-ctor decl. -/
example :
    parseClassChunk? "类 真假 = 真 | 假" = some ("真假", ["真", "假"]) :=
  by native_decide

/-- 1-ctor decl is fine. -/
example : parseClassChunk? "类 X = 甲" = some ("X", ["甲"]) := by native_decide

/-- Missing `=` → none. -/
example : parseClassChunk? "类 五行 木 火" = none := by native_decide

/-- Empty TYPENAME → none. -/
example : parseClassChunk? "类  = 木 | 火" = none := by native_decide

/-- Empty ctor → none. -/
example : parseClassChunk? "类 X = 甲 | " = none := by native_decide

/-- `resolveUserCtors` rewrites a free `.var` to `.userCtor`. -/
example :
    resolveUserCtors [⟨"木", "五行"⟩] (.var "木") [] = .userCtor "五行" "木" := by
  native_decide

/-- Bound `.var` (under `.abs`) is NOT rewritten. -/
example :
    resolveUserCtors [⟨"木", "五行"⟩]
        (.abs "木" .hex (.var "木")) []
      = .abs "木" .hex (.var "木") := by native_decide

/-- A non-ctor `.var` is preserved. -/
example :
    resolveUserCtors [⟨"木", "五行"⟩] (.var "甲") []
      = .var "甲" := by native_decide

/-! ## § 3  端到端 sanity tests

318 `example := by native_decide` tests moved to `EndToEndTests.lean` (Phase γ,
2026-05-15). After `Hexagram := Fin 6 → Bool`, each `native_decide` compilation
takes ~10s vs ms before, making 318 examples cost >1h wall-clock per build.

Run tests separately:
    lake build SSBX.Foundation.Wen.WenSurface.EndToEndTests

This module is not in `SSBX.lean`; default `lake build SSBX` skips it.
-/

end SSBX.Foundation.Wen.WenSurface
