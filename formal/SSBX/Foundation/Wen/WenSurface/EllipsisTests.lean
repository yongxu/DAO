/-
# WenSurface.EllipsisTests — wen-2.0 ⑨ subject-ellipsis acceptance tests

Focused tests for `wenyanCompileProgramWithEllipsis` — the cross-statement
PendingBinder pipeline introduced for subject ellipsis 主语省略.

Split from `EndToEndTests.lean` so the small acceptance set can be iterated
quickly without rebuilding the 339-example end-to-end suite.

Design recap (`§ 2d` of EndToEnd.lean):

- An "open" statement is one whose elaborated `Tm` is `Tm.abs n t (.var n)`
  — a pure identity λ in v1.
- Following a SOFT separator (`；` / `;`), the binder `(n, t)` propagates:
  the next chunk has `其` rewritten to `n` pre-lex, and compiles in Ctx
  `[(n, t)]`.
- A HARD separator (`。`) clears the pending binder.
- The per-statement output shape is unchanged: each chunk produces one
  `TypedTm`.  Ellipsis-following statements compile to their body Tm with
  `Tm.var n` references; the λ-rebind is left to downstream consumers.

This module is **not** in `SSBX.lean`'s import chain — it builds on demand
via `lake build SSBX.Foundation.Wen.WenSurface.EllipsisTests`.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## (1) Baseline: an empty program returns the empty list. -/

example : wenyanCompileProgramWithEllipsis "" = .ok [] := by native_decide

/-! ## (2) Single non-binder statement: PendingBinder stays clear. -/

/-- `推 一` is one statement; the result list has length 1 and type `Hex`. -/
example :
    (wenyanCompileProgramWithEllipsis "推 一").toOption.map (·.map (·.ty))
      = some [.hex] := by native_decide

/-! ## (3) Open binder + soft separator → `其` substitution + Ctx binding. -/

/-- `者 甲 甲；推 其` — first statement is `λ甲. 甲` (identity), an open
    binder; the soft `；` propagates the binder; second statement `推 其`
    rewrites to `推 甲` and compiles in Ctx `[(甲, .hex)]`.

    Result list: two TypedTms.  First has type `Hex → Hex` (the identity
    abs); second has type `Hex` (the body `推 甲` with `甲` bound). -/
example :
    (wenyanCompileProgramWithEllipsis "者 甲 甲；推 其").toOption.map (·.map (·.ty))
      = some [.arr .hex .hex, .hex] := by native_decide

/-! ## (4) Hard separator clears the pending binder. -/

/-- `者 甲 甲。推 其` — same first statement, but the HARD `。` clears
    PendingBinder.  Second statement compiles WITHOUT `其` substitution; it
    surfaces as an unresolved glyph and the pipeline fails.  We just assert
    that the compile fails (the precise error code is implementation-
    detail; `.resolve` is the expected category). -/
example :
    (match wenyanCompileProgramWithEllipsis "者 甲 甲。推 其" with
     | .error _ => true
     | _        => false) = true := by native_decide

/-! ## (5) Non-open first statement leaves PendingBinder unchanged. -/

/-- `推 一；推 其` — first statement is `推 一 : Hex` (NOT an open binder),
    so PendingBinder remains `none` after it; second statement's `其` is
    NOT substituted and the program fails to compile. -/
example :
    (match wenyanCompileProgramWithEllipsis "推 一；推 其" with
     | .error _ => true
     | _        => false) = true := by native_decide

/-! ## (6) Multiple `其` in one chunk share the same binder. -/

/-- `者 甲 甲；同 其 其` — second statement has two `其`, both substituted
    to `甲`.  `同 甲 甲` (I_1) is `Hex → Hex → Bool`, fully applied → Bool. -/
example :
    (wenyanCompileProgramWithEllipsis "者 甲 甲；同 其 其").toOption.map
        (·.map (·.ty))
      = some [.arr .hex .hex, .bool] := by native_decide

/-! ## (7) Standalone `其` (no pending binder) fails. -/

example :
    (match wenyanCompileProgramWithEllipsis "其" with
     | .error _ => true
     | _        => false) = true := by native_decide

/-! ## (8) Continued ellipsis: after a non-open intermediate, the binder
       clears, so the THIRD chunk's `其` is unsubstituted and errors.

    `者 甲 甲；推 其；推 其` — first chunk is open `λ甲. 甲`; second compiles
    as `推 甲` (not an open binder, so PendingBinder clears); third chunk's
    `其` is then unresolved → error. -/
example :
    (match wenyanCompileProgramWithEllipsis "者 甲 甲；推 其；推 其" with
     | .error _ => true
     | _        => false) = true := by native_decide

/-! ## (9) Pending binder of type Bool: `者 甲 不 甲`.

    `者 甲 不 甲` parses as `λ甲. ¬甲` (BOOL identity-style).  v1 sees this
    as NOT an open binder (body is `not 甲`, not `.var 甲`), so the next
    `其` is rejected.  Demonstrates the v1 "pure identity only" boundary. -/
example :
    (match wenyanCompileProgramWithEllipsis "者 甲 不 甲；推 其" with
     | .error _ => true
     | _        => false) = true := by native_decide

end SSBX.Foundation.Wen.WenSurface
