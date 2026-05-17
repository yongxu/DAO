/-
# WenSurface.TypeInferTests — acceptance tests for Wen 2.0 ①

Tests for Hindley-Milner type inference of `者 NAME body` (lambda
binders) without explicit type annotations.  Built on demand:

    lake build SSBX.Foundation.Wen.WenSurface.TypeInferTests

Not in `SSBX.lean`'s import chain to keep cold-build wall time down.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## § 1  Unit tests on the HM primitives (TypeInfer.lean) -/

/-- Identity unification on a base type. -/
example : (unifyTop [] .hex .hex).toOption.isSome := by native_decide

/-- Mvar resolves to a concrete type. -/
example : (unifyTop [] (.mvar 0) .bool).toOption = some [(0, .bool)] := by
  native_decide

/-- Arr-structural unification. -/
example :
    (unifyTop [] (.arr (.mvar 0) (.mvar 1)) (.arr .hex .bool)).toOption.isSome :=
  by native_decide

/-- Mismatch fires for incompatible carriers. -/
example :
    (match unifyTop [] .hex .bool with
     | .error (.mismatch _ _) => true
     | _ => false) = true :=
  by native_decide

/-- Occurs check on `α ~ α → β`. -/
example :
    (match unifyTop [] (.mvar 0) (.arr (.mvar 0) (.mvar 1)) with
     | .error (.occursCheck 0 _) => true
     | _ => false) = true :=
  by native_decide

/-! ## § 2  HM end-to-end on `者 NAME body` from surface syntax -/

/-- `者 甲 甲` — identity at Hex (default mvar resolution). -/
example :
    (wenyanCompile "者 甲 甲").toOption.map (·.ty)
      = some (.arr .hex .hex) := by
  native_decide

/-- `者 甲 不 甲` — body uses `不 : Bool → Bool`, so 甲 must be Bool. -/
example :
    (wenyanCompile "者 甲 不 甲").toOption.map (·.ty)
      = some (.arr .bool .bool) := by
  native_decide

/-- `者 甲 推 甲` — 推 : Hex → Hex constrains 甲 to Hex. -/
example :
    (wenyanCompile "者 甲 推 甲").toOption.map (·.ty)
      = some (.arr .hex .hex) := by
  native_decide

/-- `者 甲 同 甲 甲` — eqHex : Hex → Hex → Bool; result type Hex → Bool. -/
example :
    (wenyanCompile "者 甲 同 甲 甲").toOption.map (·.ty)
      = some (.arr .hex .bool) := by
  native_decide

/-! ## § 3  HM picks the right domain when body operator is Bool-typed
        (legacy 6-candidate trial used .hex first).  We use the `不`
        glyph which the catalogue resolves to `.notB : Bool → Bool`. -/

/-- Pure boolean lambda body — domain inferred as Bool. -/
example :
    (wenyanCompile "者 甲 不 甲").toOption.map (·.ty)
      = some (.arr .bool .bool) := by
  native_decide

/-! ## § 4  Higher-order: f : Hex → Hex inferred from `f 一` usage. -/

/-- `者 甲 甲 之 乾`: 甲 used as a function applied to 乾 (Hex), and the
    result feeds nothing further, so 甲 : Hex → α; α defaults to Hex. -/
example :
    (wenyanCompile "者 甲 甲 之 乾").toOption.map (·.ty)
      = some (.arr (.arr .hex .hex) .hex) := by
  native_decide

/-- `者 甲 甲 之 真`: f applied to Bool, defaulting result to Hex
    (legacy: `(Bool → Bool) → Bool`).  HM picks `(Bool → Hex) → Hex`
    because there is no constraint pinning the codomain.
    Either is a valid principal-type instance; pin it down here. -/
example :
    (wenyanCompile "者 甲 甲 之 真").toOption.bind (fun t =>
      match t.ty with
      | .arr (.arr .bool _) _ => some true
      | _ => none) = some true := by
  native_decide

/-! ## § 5  Eval still works through the inferred lambda. -/

/-- `者 甲 甲 真` reduces to `true`. -/
example :
    (wenyanInterpBool "者 甲 甲 真").toOption = some true :=
  by native_decide

/-- `者 甲 不 甲 真` reduces to `false`. -/
example :
    (wenyanInterpBool "者 甲 不 甲 真").toOption = some false :=
  by native_decide

/-- `者 甲 推 甲 乾` reduces to «一» (推 乾 ≡ 加 一 乾). -/
example :
    (wenyanInterp "者 甲 推 甲 乾").toOption = some «一» :=
  by native_decide

/-! ## § 6  Nested binders: two lambdas, two distinct domain inferences. -/

/-- `而 者 甲 甲 者 甲 推 甲` ≡ compose (id : Hex → Hex) (推 : Hex → Hex).
    Both inner lambdas should be inferred as Hex → Hex. -/
example :
    (wenyanCompile "而 者 甲 甲 者 甲 推 甲").toOption.map (·.ty)
      = some (.arr .hex .hex) := by
  native_decide

end SSBX.Foundation.Wen.WenSurface
