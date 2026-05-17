/-
# WenSurface.NominalizerTests — wen-2.0 ⑦ 真名词化器 acceptance suite

End-to-end checks for context-sensitive `者`:
  · Head position `者 NAME body` — λ-binder (back-compat with Wen 1.5)
  · After predicate `PRED 者` — nominalize predicate to `Set elem`

And for the companion `属` (set-membership) operator:
  · `X 属 S` returns `.bool`; runtime tests the predicate at `X`.

This module is not part of `SSBX.lean`'s import chain — build on demand:
  `lake build SSBX.Foundation.Wen.WenSurface.NominalizerTests`

0 sorry / 0 axiom.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 4000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## § 1  Back-compat: 者 as λ-binder (head position) -/

/-- Classic `者 甲 甲` — λx:Hex. x. -/
example : (wenyanCompile "者 甲 甲").toOption.isSome = true := by native_decide

/-- `者 甲 甲` has type `Hex → Hex`. -/
example :
    (wenyanCompile "者 甲 甲").toOption.map (·.ty) = some (.arr .hex .hex) := by
  native_decide

/-- `者 甲 同 甲 一` is a predicate `Hex → Bool`. -/
example :
    (wenyanCompile "者 甲 同 甲 一").toOption.map (·.ty) = some (.arr .hex .bool) := by
  native_decide

/-! ## § 2  Nominalizer: predicate 者 → Set elem -/

/-- A parenthesised predicate `(者 甲 同 甲 一)` followed by `者` nominalizes:
    result is `Set Hex`. -/
example :
    (wenyanCompile "（者 甲 同 甲 一） 者").toOption.map (·.ty) = some (.set .hex) := by
  native_decide

/-- ASCII-paren variant works too. -/
example :
    (wenyanCompile "(者 甲 同 甲 一) 者").toOption.map (·.ty) = some (.set .hex) := by
  native_decide

/-! ## § 3  属 set-membership: X 属 S → Bool -/

/-- `一 属 (predicate 者)` returns Bool. -/
example :
    (wenyanCompile "一 属 （者 甲 同 甲 一） 者").toOption.map (·.ty) = some .bool := by
  native_decide

/-- `一 属 (λx. x = 一) 者` evaluates to `true` (一 is the only member). -/
example :
    wenyanInterpBool "一 属 （者 甲 同 甲 一） 者" = .ok true := by native_decide

/-- `乾 属 (λx. x = 一) 者` evaluates to `false` (乾 ≠ 一). -/
example :
    wenyanInterpBool "乾 属 （者 甲 同 甲 一） 者" = .ok false := by native_decide

/-! ## § 4  Universal / empty sets -/

/-- The universal predicate `λx. 真` nominalized — every Hex is a member. -/
example :
    wenyanInterpBool "一 属 （者 甲 真） 者" = .ok true := by native_decide

/-- The empty predicate `λx. 假` nominalized — nothing is a member. -/
example :
    wenyanInterpBool "一 属 （者 甲 假） 者" = .ok false := by native_decide

/-- 乾 against `λx. 真` is still `true`. -/
example :
    wenyanInterpBool "乾 属 （者 甲 真） 者" = .ok true := by native_decide

/-! ## § 5  Direct kernel-Tm sanity (independent of surface parser) -/

/-- Direct `Tm.setOf` of `λx:Hex. x = 一` typechecks to `Set Hex`. -/
example :
    typeCheck [] (.setOf (.abs "x" .hex (.app (.app .eqHex (.var "x")) .yi)))
      = some (.set .hex) := by native_decide

/-- Direct membership evaluates correctly: `一 ∈ {x | x = 一}` is `true`. -/
example :
    denoteBool
        (.memberOf .yi
          (.setOf (.abs "x" .hex (.app (.app .eqHex (.var "x")) .yi))))
      = some true := by native_decide

/-- Direct membership: `乾 ∉ {x | x = 一}` is `false`. -/
example :
    denoteBool
        (.memberOf (.hexLit Hexagram.heaven)
          (.setOf (.abs "x" .hex (.app (.app .eqHex (.var "x")) .yi))))
      = some false := by native_decide

end SSBX.Foundation.Wen.WenSurface
