/-
# WenSurface.UserDefsTests — focused tests for sub-plan 05 (user-defined `def`)

Split from `EndToEndTests.lean` so the 12 user-def acceptance tests can be
built / iterated in seconds rather than waiting for the full 339-example
EndToEndTests dependency chain.  Same `set_option maxHeartbeats 8000000`;
same `import EndToEnd`; same `native_decide` style.

This module is **not** in `SSBX.lean`'s import chain — it builds on demand
via `lake build SSBX.Foundation.Wen.WenSurface.UserDefsTests`.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## User-defined `def` declarations (wen-1.5 sub-plan 05)

Surface form: `定 NAME 为 BODY`.  Sequential definitions accumulate into
a `DefEnv`; subsequent statements rewrite references to declared names
by textual substitution of the body source (wrapped in 「（…）」) BEFORE
lexing.  v1: no recursion; re-definition rejected; catalogue glyphs
rejected as names. -/

/-- (1) Single def + single use: `定 倍推 为 而 推 推；倍推 一`.
    The defStmt body has type `Hex → Hex` (S_2 = endoCompBody composes
    the two T_10 endomaps); the exprStmt applies it to `一` and has
    type `Hex`. -/
example :
    (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；倍推 一").toOption.map
        (·.map (·.body.ty))
      = some [.arr .hex .hex, .hex] := by
  native_decide

/-- (2) `倍推 一` after `定 倍推 为 而 推 推` has the SAME denotation as
    `推 推 一` (S_2 ≡ composition; substitution preserves semantics). -/
example :
    let lhs := (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；倍推 一").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    let rhs := (wenyanCompile "推 推 一").toOption
    (lhs.bind (denoteHex ·.tm)) = (rhs.bind (denoteHex ·.tm)) := by
  native_decide

/-- (3) Chained defs: `定 甴 为 推 一；定 乸 为 甴；乸` ≡ `推 一`. -/
example :
    let chained := (wenyanCompileProgramWithDefs "定 甴 为 推 一；定 乸 为 甴；乸").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    let direct := (wenyanCompile "推 一").toOption
    (chained.bind (denoteHex ·.tm)) = (direct.bind (denoteHex ·.tm)) := by
  native_decide

/-- (4) Redefinition rejected: `定 甴 为 推 一；定 甴 为 推 推 一` errors. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴 为 推 一；定 甴 为 推 推 一" with
     | .error (.defError 1 (.redefinition "甴")) => true
     | _ => false) = true := by native_decide

/-- (5) Catalogue collision rejected: `定 推 为 推 一` cannot shadow the
    catalogue glyph `推`. -/
example :
    (match wenyanCompileProgramWithDefs "定 推 为 推 一" with
     | .error (.defError 0 (.conflictWithCatalogue "推")) => true
     | _ => false) = true := by native_decide

/-- (6) Missing `为` separator → defError. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴" with
     | .error (.defError 0 _) => true
     | _ => false) = true := by native_decide

/-- (7) Empty body after `为` → defError. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴 为 " with
     | .error (.defError 0 _) => true
     | _ => false) = true := by native_decide

/-- (8) Def-body compile failure surfaces as a `.base` (not `.defError`).
    The body `推 真` is a type error: `推` expects `Hex` but `真` is `Bool`. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴 为 推 真" with
     | .error (.base 0 _) => true
     | _ => false) = true := by native_decide

/-- (9) Multi-token name «倍推» is accepted (not in `multiCharSurfaces`).
    Body `推 一` has type `Hex`; `倍推` resolves to it. -/
example :
    (wenyanCompileProgramWithDefs "定 倍推 为 推 一；倍推").toOption.map List.length
      = some 2 := by
  native_decide

/-- (10) Recursion rejected (body compile errors): `定 甴 为 甴`.
    Inner `甴` is an unbound glyph in the body's own compile context. -/
example :
    (match wenyanCompileProgramWithDefs "定 甴 为 甴" with
     | .error (.base 0 _) => true
     | _ => false) = true := by native_decide

/-- (11) Plain expression chunks unaffected by an empty env. -/
example :
    (wenyanCompileProgramWithDefs "推 一").toOption.map List.length = some 1 := by
  native_decide

/-- (12) End-to-end value check: `定 倍推 为 而 推 推；倍推 一` denotes
    «生生» 2 «一» (compose-then-apply ≡ apply-twice). -/
example :
    let lastExpr := (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；倍推 一").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    lastExpr.bind (denoteHex ·.tm) = some («生生» 2 «一») := by
  native_decide

/-- (13) Nested def references: `三推 = 而 倍推 推 ≡ apply-推-thrice`. -/
example :
    let lastExpr :=
      (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；定 三推 为 而 倍推 推；三推 一").toOption
        |>.bind (·.getLast?) |>.map Stmt.body
    lastExpr.bind (denoteHex ·.tm) = some («生生» 3 «一») := by
  native_decide

/-! ## wen-2.0 ② Recursive user-defs (`定递`) — μ-fixpoint with fuel

Surface form: `定递 NAME 为 BODY`.  BODY may reference NAME freely.  At
compile time we wrap as `者 NAME （BODY）`, extract the resulting abs body,
re-infer the fixpoint type T, and emit `.fix NAME T body'`.  Recursion is
evaluated by `WenDefEval.applyFuel`'s `.fixV` case: each unfolding consumes
one fuel tick, so divergent recursion exhausts cleanly (returns `none`)
instead of crashing.

**v1 restriction**: NAME must be one of the 10 Heavenly Stems
(甲乙丙丁戊己庚辛壬癸) — the only glyphs the resolver accepts as bare var
names.  This is documented; lifting the restriction is left for future work. -/

/-- (R-1) Recursive def that doesn't actually recurse — identity λ wrapped
    in a `.fix`.  `定递 甲 为 者 乙 乙` defines 甲 as `μ f. λ x. x`;
    `甲 一` evaluates to 一. -/
example :
    let lastExpr := (wenyanCompileProgramWithDefs "定递 甲 为 者 乙 乙；甲 一").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    lastExpr.bind (denoteHex ·.tm) = some «一» := by
  native_decide

/-- (R-2) Recursive def returning a constant Hex (no self-reference used).
    `定递 甲 为 者 乙 推 乙；甲 一` ≡ `推 一` ≡ «生» «一». -/
example :
    let lastExpr := (wenyanCompileProgramWithDefs "定递 甲 为 者 乙 推 乙；甲 一").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    lastExpr.bind (denoteHex ·.tm) = some («生» «一») := by
  native_decide

/-- (R-3) Divergent recursion exhausts fuel cleanly.
    `定递 甲 为 者 乙 甲 乙；甲 一` is `μ f. λ x. f x` — every unfolding
    just re-applies, never producing a Hex.  `denoteHex` returns `none`. -/
example :
    let lastExpr := (wenyanCompileProgramWithDefs "定递 甲 为 者 乙 甲 乙；甲 一").toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    lastExpr.bind (denoteHex ·.tm) = none := by
  native_decide

/-- (R-4) Self-reference (no λ body) compiles to a typed `.fix` at type
    `.hex` — operationally diverges if forced, but the def statement itself
    succeeds (no longer rejected as in Wen 1.5).  `定递 甲 为 甲`. -/
example :
    (wenyanCompileProgramWithDefs "定递 甲 为 甲").toOption.map List.length
      = some 1 := by
  native_decide

/-- (R-5) `定递` priority over `定`: `定递 …` is recognised before `定 递 …`. -/
example : chunkStartsWithRecDefKeyword "定递 甲 为 者 乙 乙" = true := by native_decide
example : chunkStartsWithDefKeyword    "定递 甲 为 者 乙 乙" = false := by native_decide
example : chunkStartsWithRecDefKeyword "定 倍推 为 而 推 推"  = false := by native_decide
example : chunkStartsWithDefKeyword    "定 倍推 为 而 推 推"  = true := by native_decide

/-- (R-6) `parseRecDefChunk?` splits on the first `为` after the `定递`
    2-codepoint prefix. -/
example :
    parseRecDefChunk? "定递 甲 为 者 乙 甲 乙" = some ("甲", "者 乙 甲 乙") := by
  native_decide

/-- (R-7) Empty body after `为` → none. -/
example : parseRecDefChunk? "定递 甲 为 " = none := by native_decide

/-- (R-8) Empty name → none. -/
example : parseRecDefChunk? "定递  为 推" = none := by native_decide

/-- (R-9) Missing `为` → none. -/
example : parseRecDefChunk? "定递 甲 者 乙 乙" = none := by native_decide

/-- (R-10) A non-`定递` chunk → none. -/
example : parseRecDefChunk? "定 倍推 为 推" = none := by native_decide

/-- (R-11) Non-stem name rejected for `定递` (v1 restriction).
    `甴` is a single-token CJK char but not in {甲乙丙丁戊己庚辛壬癸}. -/
example :
    (match wenyanCompileProgramWithDefs "定递 甴 为 者 乙 乙" with
     | .error (.defError 0 (.recNameNotStem "甴")) => true
     | _ => false) = true := by native_decide

/-- (R-12) Redefinition rejected across `定递` + `定递`. -/
example :
    (match wenyanCompileProgramWithDefs "定递 甲 为 者 乙 乙；定递 甲 为 者 乙 推 乙" with
     | .error (.defError 1 (.redefinition "甲")) => true
     | _ => false) = true := by native_decide

/-- (R-13) Mixed `定` + `定递` work together.  Define a non-rec `多 = 推 推 一`
    (a constant Hex; non-conflicting with any catalogue glyph), then a rec
    `甲` (returning 多 unchanged).  Result is `推 推 一` ≡ «生生» 2 «一». -/
example :
    let lastExpr :=
      (wenyanCompileProgramWithDefs "定 多 为 推 推 一；定递 甲 为 者 乙 多；甲 一").toOption
        |>.bind (·.getLast?) |>.map Stmt.body
    lastExpr.bind (denoteHex ·.tm) = some («生生» 2 «一») := by
  native_decide

/-- (R-14) Multi-token name rejected for `定递`. -/
example :
    (match wenyanCompileProgramWithDefs "定递 倍推 为 者 乙 乙" with
     | .error (.defError 0 (.recMultiTokenName "倍推")) => true
     | _ => false) = true := by native_decide

/-- (R-15) `isHeavenlyStem` recogniser. -/
example : isHeavenlyStem "甲" = true  := by native_decide
example : isHeavenlyStem "癸" = true  := by native_decide
example : isHeavenlyStem "甴" = false := by native_decide
example : isHeavenlyStem ""   = false := by native_decide

end SSBX.Foundation.Wen.WenSurface
