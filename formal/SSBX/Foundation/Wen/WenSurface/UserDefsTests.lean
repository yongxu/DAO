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

end SSBX.Foundation.Wen.WenSurface
