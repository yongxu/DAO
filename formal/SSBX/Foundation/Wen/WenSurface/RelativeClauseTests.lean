/-
# WenSurface.RelativeClauseTests — wen-2.0 ⑧ acceptance suite

Tested surface forms:

    所 PRED 者         -- object relativization → λ甲. PRED 甲
    Y 之所以 X         -- reason-extraction   → .app X Y

Coverage matrix:
  · `所 不 者` typechecks to `.arr .bool .bool` (Bool→Bool predicate
    nominalization; HM picks `甲 : .bool` since `不` is Bool→Bool).
  · `所 推 者` typechecks to `.arr .hex .hex` (Hex→Hex predicate
    nominalization; HM picks `甲 : .hex`).
  · `所 不 者` parses and produces the same `Tm` as `者 甲 (不 甲)`
    (the spec's stated reduction `≈ 者 z (X z)`).
  · `乾 之所以 推` typechecks to `.hex` (推 乾 : Hex).
  · `乾 之所以 推` parses and produces the same `Tm` as `推 乾`
    (reason-as-application).
  · `所 不 者` and `者 甲 (不 甲)` produce identical compiled `Tm`s.

This module is **not** in `SSBX.lean`'s import chain — it builds on
demand via `lake build SSBX.Foundation.Wen.WenSurface.RelativeClauseTests`.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef

/-! ## § 1  Lex + Reading sanity -/

/-- `之所以` lexes as a single 3-codepoint surface. -/
example :
    (lexWen "之所以").toOption = some [⟨"之所以", 0, 3, true⟩] := by
  native_decide

/-- `之所以` resolves to the `.zhiSuoYi` syntax marker. -/
example :
    ((lexAndResolve "之所以").toOption.map (fun rs => rs.map (·.atom)))
      = some [.syntax .zhiSuoYi] := by
  native_decide

/-- `所` resolves to the `.suo` syntax marker (shadowing the legacy
    `S_16` catalogue reading). -/
example :
    ((lexAndResolve "所").toOption.map (fun rs => rs.map (·.atom)))
      = some [.syntax .suo] := by
  native_decide

/-- `所 不 者` lexes as three tokens. -/
example :
    ((lexWen "所 不 者").toOption.map List.length) = some 3 := by
  native_decide

/-! ## § 2  `所 PRED 者` parsing -/

/-- `所 不 者` parses successfully. -/
example : (parseSurface "所 不 者").toOption.isSome = true := by native_decide

/-- `所 推 者` parses successfully. -/
example : (parseSurface "所 推 者").toOption.isSome = true := by native_decide

/-! ## § 3  `所 PRED 者` typechecking -/

/-- `所 不 者` typechecks to `.arr .bool .bool` — HM picks the implicit
    binder domain as `.bool` because `不 : Bool→Bool`. -/
example :
    (wenyanCompile "所 不 者").toOption.map (·.ty) = some (.arr .bool .bool) := by
  native_decide

/-- `所 推 者` typechecks to `.arr .hex .hex` — HM picks `甲 : .hex`
    because `推 : Hex→Hex`. -/
example :
    (wenyanCompile "所 推 者").toOption.map (·.ty) = some (.arr .hex .hex) := by
  native_decide

/-! ## § 4  `所 PRED 者` desugaring equivalence

Per spec: `所 X 者` ≈ `者 甲 (X 甲)`.  Both surfaces should compile to
identical `Tm`s (modulo binder name).
-/

/-- `所 不 者` compiles to the same `Tm` as `者 甲 (不 甲)`. -/
example :
    (wenyanCompileTm "所 不 者") = (wenyanCompileTm "者 甲 不 甲") := by
  native_decide

/-- `所 推 者` compiles to the same `Tm` as `者 甲 推 甲`. -/
example :
    (wenyanCompileTm "所 推 者") = (wenyanCompileTm "者 甲 推 甲") := by
  native_decide

/-! ## § 5  `Y 之所以 X` parsing + typechecking -/

/-- `乾 之所以 推` parses successfully. -/
example : (parseSurface "乾 之所以 推").toOption.isSome = true := by native_decide

/-- `乾 之所以 推` typechecks to `.hex` — kernel collapses to `推 乾 : Hex`. -/
example :
    (wenyanCompile "乾 之所以 推").toOption.map (·.ty) = some .hex := by
  native_decide

/-! ## § 6  `Y 之所以 X` desugaring equivalence

Per spec/design: `Y 之所以 X` desugars to `.app X Y` (reason-as-application).
-/

/-- `乾 之所以 推` compiles to the same `Tm` as `推 乾`. -/
example :
    (wenyanCompileTm "乾 之所以 推") = (wenyanCompileTm "推 乾") := by
  native_decide

/-- `坤 之所以 推` compiles to the same `Tm` as `推 坤`. -/
example :
    (wenyanCompileTm "坤 之所以 推") = (wenyanCompileTm "推 坤") := by
  native_decide

/-! ## § 7  Error cases -/

/-- `所 不` (missing `者`) is a parse error. -/
example : (parseSurface "所 不").toOption.isNone = true := by native_decide

/-- `之所以` alone (no subject, no rhs) errors at expression start
    because it's grammatically a postfix-infix marker. -/
example : (parseSurface "之所以").toOption.isNone = true := by native_decide

end SSBX.Foundation.Wen.WenSurface
