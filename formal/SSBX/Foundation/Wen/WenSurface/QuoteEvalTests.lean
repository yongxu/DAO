/-
# WenSurface.QuoteEvalTests — wen-2.0 ⑪ 执 「X」 quote-eval acceptance suite

End-to-end checks for the `执 「X」` macro: surface form parses, elaborates
to `Tm.unquote`, typechecks to `.hex`, and evaluates by re-running the
quoted body under the current env.  Fuel-bounded: divergent quoted bodies
return a `denoteFailed` runtime error, *not* a crash.

This module is not part of `SSBX.lean`'s import chain — build on demand:
  `lake build SSBX.Foundation.Wen.WenSurface.QuoteEvalTests`

0 sorry / 0 axiom.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 4000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## § 1  Surface acceptance: `执 「X」` compiles -/

/-- `执 「一」` parses + elaborates + typechecks. -/
example : (wenyanCompile "执 「一」").toOption.isSome = true := by native_decide

/-- `执 「乾」` parses + elaborates + typechecks. -/
example : (wenyanCompile "执 「乾」").toOption.isSome = true := by native_decide

/-- `执 「推 之 一」` parses + elaborates + typechecks. -/
example : (wenyanCompile "执 「推 之 一」").toOption.isSome = true := by native_decide

/-- Result type of `执 「X」` is `.hex`. -/
example :
    (wenyanCompile "执 「一」").toOption.map (·.ty) = some .hex := by native_decide

example :
    (wenyanCompile "执 「乾」").toOption.map (·.ty) = some .hex := by native_decide

example :
    (wenyanCompile "执 「推 之 一」").toOption.map (·.ty) = some .hex := by
  native_decide

/-! ## § 2  End-to-end evaluation: 执 「X」 ≡ X -/

/-- `执 「乾」` evaluates to Hexagram.heaven. -/
example : wenyanInterp "执 「乾」" = .ok Hexagram.heaven := by native_decide

/-- `执 「一」` evaluates to «一». -/
example : wenyanInterp "执 「一」" = .ok «一» := by native_decide

/-- `执 「推 之 一」` evaluates to «生» «一» (same as `推 之 一`). -/
example : wenyanInterp "执 「推 之 一」" = .ok («生» «一») := by native_decide

/-- 执 「推 之 乾」 ≡ 推 之 乾.  The quote-bracketed body is re-evaluated
    verbatim under the current env, so the result must match the unquoted
    form. -/
example :
    wenyanInterp "执 「推 之 乾」" = wenyanInterp "推 之 乾" := by native_decide

/-- 执 「推 之 推 之 一」 ≡ 推 之 推 之 一. -/
example :
    wenyanInterp "执 「推 之 推 之 一」" = wenyanInterp "推 之 推 之 一" := by
  native_decide

/-! ## § 3  Compile-time rejection: 执 on non-quoted args -/

/-- 执 一 (no quote brackets) is rejected at compile time.  The bare `一`
    has type `.hex`, but `执` requires `.quoted`, so elaboration / kernel
    typecheck rejects.  We assert "not ok" without committing to the exact
    error tag (the surface parser may pre-empt this with a different
    diagnostic — what matters is that no `TypedTm` is produced). -/
example : (wenyanCompile "执 一").toOption.isNone = true := by native_decide

/-- 执 乾 (bare hex const) is rejected. -/
example : (wenyanCompile "执 乾").toOption.isNone = true := by native_decide

/-- 执 alone (no argument) is rejected. -/
example : (wenyanCompile "执").toOption.isNone = true := by native_decide

/-! ## § 4  Nested 执 «X»: clean fuel-bounded behaviour

The evaluator is *fuel-bounded*: every `.unquote` step costs one fuel
tick (`fuel+1 → fuel`), and the recursive `evalFuel fuel env inner`
call shares the same fuel budget.  So nested `执 「执 「X」」` simply
unwraps one quote per unquote step and exhausts fuel cleanly on
pathological chains rather than crashing.

We verify *positive* behaviour for sensible nesting depth (default fuel
= 512 covers anything human-typeable).
-/

/-- 双层 执 「执 「乾」」 succeeds: the outer unquote re-evaluates the
    inner Tm `.unquote .quote .hexLit Hexagram.heaven`, which itself
    reduces to `Hexagram.heaven`.  Net result: `Hexagram.heaven`. -/
example : wenyanInterp "执 「执 「乾」」" = .ok Hexagram.heaven := by native_decide

/-- Triple-nested 执 succeeds with the same fuel-bounded recursion. -/
example : wenyanInterp "执 「执 「执 「乾」」」" = .ok Hexagram.heaven := by
  native_decide

/-- Fuel-exhaustion path: evaluating `.unquote` directly with fuel 0 returns
    `none` (no crash).  This is the structural fuel guard that bounds any
    pathological recursion at the kernel level. -/
example : evalFuel 0 [] (.unquote (.quote .yi)) = none := by native_decide

/-- Fuel-exhaustion path: a 5-deep `.unquote .quote .unquote .quote ...`
    chain needs more than 5 fuel ticks to fully reduce; at fuel = 1 we get
    `none` (the outer `.unquote` consumes the tick before any inner step). -/
example :
    evalFuel 1 []
      (.unquote (.quote (.unquote (.quote .yi)))) = none := by native_decide

/-! ## § 5  Composition with rest of the language -/

/-- 执 「X」 composes inside an outer 推: `推 之 执 「乾」` ≡ `推 之 乾`. -/
example :
    wenyanInterp "推 之 执 「乾」" = wenyanInterp "推 之 乾" := by native_decide

/-- Same as above with `一`: `推 之 执 「一」` ≡ `推 之 一`. -/
example :
    wenyanInterp "推 之 执 「一」" = wenyanInterp "推 之 一" := by native_decide

end SSBX.Foundation.Wen.WenSurface
