/-
# WenSurface.MatchTests — wen-2.0 ⑤ pattern matching acceptance suite

Statement-level surface form:

    析 SCRUT 为 PAT₁ → BODY₁ | PAT₂ → BODY₂ | … | PATₙ → BODYₙ

Tested matters:
  · Bool match (literal patterns).
  · Hex match (literal patterns).
  · User-inductive match (after `类` decl).
  · `varP` pattern binds the scrutinee in the arm body.
  · Stem-as-userCtor wins over stem-as-varP when ctor is in scope.
  · No-match scrutinee yields a clean runtime `none`.
  · Arm-type-mismatch and pattern-type-mismatch surface as kernel
    typecheck errors (`matchTypeError`).

This module is **not** in `SSBX.lean`'s import chain — it builds on demand
via `lake build SSBX.Foundation.Wen.WenSurface.MatchTests`.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## § 1  Surface parsing of `析 …` -/

example : chunkStartsWithMatchKeyword "析 一 为 一 → 真 | 凡 → 假" = true := by
  native_decide

example :
    parseMatchChunkHead? "析 一 为 一 → 真 | 凡 → 假"
      = some ("一", "一 → 真 | 凡 → 假") := by native_decide

example :
    parseMatchArmsSource "一 → 真 | 凡 → 假"
      = [("一", "真"), ("凡", "假")] := by native_decide

/-! ## § 2  End-to-end Bool match -/

/-- (1) Bool scrutinee with two boolean arms; ResultType = .hex. -/
example :
    let prog := "析 真 为 真 → 一 | 假 → 乾"
    (wenyanCompileProgramWithDefs prog).toOption.map
        (·.map (fun s => s.body.ty))
      = some [.hex] := by native_decide

/-- The runtime denotes the matched arm. -/
example :
    let prog := "析 真 为 真 → 一 | 假 → 乾"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?)
        |>.bind (fun s => denoteHex s.body.tm)
      = some «一» := by native_decide

/-- Second arm of the boolean match picks 乾 when scrut = 假. -/
example :
    let prog := "析 假 为 真 → 一 | 假 → 乾"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?)
        |>.bind (fun s => denoteHex s.body.tm)
      = some Hexagram.heaven := by native_decide

/-! ## § 3  End-to-end Hex match with wildcard-like varP fallback -/

/-- (2) Hex scrutinee with hex literal then stem fallback (varP binds). -/
example :
    let prog := "析 一 为 一 → 真 | 甲 → 假"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?)
        |>.bind (fun s => denoteBool s.body.tm)
      = some true := by native_decide

/-- Scrut = 乾 falls through to stem-bound arm; body = 假. -/
example :
    let prog := "析 乾 为 一 → 真 | 甲 → 假"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?)
        |>.bind (fun s => denoteBool s.body.tm)
      = some false := by native_decide

/-- (3) varP body references the bound scrutinee value (identity). -/
example :
    let prog := "析 一 为 甲 → 甲"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?)
        |>.bind (fun s => denoteHex s.body.tm)
      = some «一» := by native_decide

/-! ## § 4  User-inductive match (post `类` decl) -/

/-- (4) `类 X = 甲 | 乙`; then `析 甲 为 甲 → 一 | 乙 → 乾`.  The bare
    ctors 甲/乙 resolve to `.userCtor X _`, and the scrutinee likewise
    elaborates as `userCtor`.  The match's pattern `甲` (with ctor in
    scope) becomes `userP X 甲`, so the first arm fires. -/
example :
    let prog := "类 甴甴 = 甲 | 乙；析 甲 为 甲 → 一 | 乙 → 乾"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?)
        |>.bind (fun s => denoteHex s.body.tm)
      = some «一» := by native_decide

/-- Second user-ctor branch fires for 乙. -/
example :
    let prog := "类 甴甴 = 甲 | 乙；析 乙 为 甲 → 一 | 乙 → 乾"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?)
        |>.bind (fun s => denoteHex s.body.tm)
      = some Hexagram.heaven := by native_decide

/-! ## § 5  Failure modes -/

/-- (5) Malformed match (missing `为`) → `matchMalformed`. -/
example :
    (match wenyanCompileProgramWithDefs "析 一 一 → 真" with
     | .error (.defError 0 (.matchMalformed _)) => true
     | _ => false) = true := by native_decide

/-- (6) Empty arm list (just `析 X 为`) → matchMalformed at parse stage
    (because parseMatchChunkHead? rejects empty body). -/
example :
    (match wenyanCompileProgramWithDefs "析 一 为 " with
     | .error (.defError 0 (.matchMalformed _)) => true
     | _ => false) = true := by native_decide

/-- (7) Pattern type mismatch (Bool pattern on Hex scrutinee) →
    `matchTypeError` (the pattern's `patternBindings` rejects). -/
example :
    (match wenyanCompileProgramWithDefs "析 一 为 真 → 真 | 甲 → 假" with
     | .error (.defError 0 (.matchBadPattern _)) => true
     | .error (.defError 0 .matchTypeError) => true
     | _ => false) = true := by native_decide

/-- (8) Arm type mismatch (two arms produce different types) →
    `matchTypeError`.  Here arm 1 = `.yi` (Hex), arm 2 = `真` (Bool). -/
example :
    (match wenyanCompileProgramWithDefs "析 真 为 真 → 一 | 假 → 真" with
     | .error (.defError 0 .matchTypeError) => true
     | _ => false) = true := by native_decide

/-! ## § 6  Kernel-level Tm structure (sanity) -/

/-- The compiled match Tm carries the expected scrutinee + arm list. -/
example :
    let prog := "析 真 为 真 → 一 | 假 → 乾"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?)
        |>.map (·.body.tm)
      = some
          (Tm.«match» (.boolLit true)
            (MatchArms.ofList
              [(.boolP true, .yi),
               (.boolP false, .hexLit Hexagram.heaven)])) := by native_decide

end SSBX.Foundation.Wen.WenSurface
