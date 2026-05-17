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

/-- Split a String on a single Char delimiter. -/
def splitOnChar (s : String) (delim : Char) : List String :=
  s.split (· = delim)

/-- Split a String on the ideographic 「；」, full-stop 「。」, and ASCII `;`.
    Returns chunks with whitespace trimmed and empty chunks removed. -/
def splitOnStatementSep (s : String) : List String :=
  -- Replace 「。」 and ASCII `;` with 「；」, then split on 「；」.
  let unified := (s.replace "。" "；").replace ";" "；"
  (splitOnChar unified '；').map String.trim
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


/-! ## § 3  端到端 sanity tests

318 `example := by native_decide` tests moved to `EndToEndTests.lean` (Phase γ,
2026-05-15). After `Hexagram := Fin 6 → Bool`, each `native_decide` compilation
takes ~10s vs ms before, making 318 examples cost >1h wall-clock per build.

Run tests separately:
    lake build SSBX.Foundation.Wen.WenSurface.EndToEndTests

This module is not in `SSBX.lean`; default `lake build SSBX` skips it.
-/

end SSBX.Foundation.Wen.WenSurface
