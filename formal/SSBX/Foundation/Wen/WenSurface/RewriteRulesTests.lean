/-
# WenSurface.RewriteRulesTests — focused tests for wen-2.0 ⑫

Split from `EndToEndTests.lean` for the same reason as `UserDefsTests.lean`:
keep the dozen acceptance tests for the new feature buildable in seconds
without dragging the full 339-example chain.

This module is **not** in `SSBX.lean`'s import chain — it builds on demand
via `lake build SSBX.Foundation.Wen.WenSurface.RewriteRulesTests`.

## Coverage

1. Single rule: `定 错 错 甲 等 甲；错 错 乾` ≡ `乾`
2. Multi-step / cascade rewriting via `normalize` fixpoint
3. Ambiguity rejection: `定 ... 等 ... 为 ...` → `rewriteAmbiguous`
4. Confluence: same head constructor (cat1 vs cat1) → rule rejected
5. Coexistence with `定 NAME 为 BODY` (Wen 1.5)
6. Coexistence with `定递 NAME 为 BODY` (Wen 2.0 ②)
7. Non-linear LHS rejected
8. Bare-var LHS rejected
9. Rule that doesn't fire leaves the term alone (semantic equivalence)
10. Chunk parsing helpers
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## § 1  Chunk-detection sanity -/

example : chunkContainsDeng "定 错 错 甲 等 甲" = true := by native_decide
example : chunkContainsDeng "推 一" = false := by native_decide

example : chunkStartsWithRewriteKeyword "定 错 错 甲 等 甲" = true := by native_decide
example : chunkStartsWithRewriteKeyword "定 倍推 为 而 推 推" = false := by native_decide
example : chunkStartsWithRewriteKeyword "定递 甲 为 推 甲" = false := by native_decide
/-- Chunks that contain both `等` and `为` are NOT classified as rewrite —
    they go to the ambiguity branch. -/
example : chunkStartsWithRewriteKeyword "定 X 等 Y 为 Z" = false := by native_decide
example : chunkIsAmbiguousDefRewrite "定 X 等 Y 为 Z" = true := by native_decide

example :
    parseRewriteChunk? "定 错 错 甲 等 甲" = some ("错 错 甲", "甲") := by
  native_decide

example :
    parseRewriteChunk? "定  等 甲" = none := by native_decide

example :
    parseRewriteChunk? "定 错 错 甲 等 " = none := by native_decide

/-- A `定递`-led chunk is not a rewrite. -/
example : parseRewriteChunk? "定递 甲 为 推 甲" = none := by native_decide

/-! ## § 2  Rule data + addRule sanity (Tm-level) -/

/-- Single rule: `错 错 甲 → 甲` reduces `错 错 乾` → `乾`. -/
example :
    let rule : RewriteRule :=
      { lhs := .app .cuoH (.app .cuoH (.var "甲"))
      , rhs := .var "甲"
      , vars := ["甲"] }
    normalize [rule] (.app .cuoH (.app .cuoH (.hexLit Hexagram.heaven)))
      = .hexLit Hexagram.heaven := by
  native_decide

/-- Cascade: 4 `错`s collapse to 0 via repeated application. -/
example :
    let rule : RewriteRule :=
      { lhs := .app .cuoH (.app .cuoH (.var "甲"))
      , rhs := .var "甲"
      , vars := ["甲"] }
    normalize [rule]
        (.app .cuoH (.app .cuoH
          (.app .cuoH (.app .cuoH (.hexLit Hexagram.heaven)))))
      = .hexLit Hexagram.heaven := by
  native_decide

/-- Odd number of `错`s: cascade leaves one outer 错 (3 → 1). -/
example :
    let rule : RewriteRule :=
      { lhs := .app .cuoH (.app .cuoH (.var "甲"))
      , rhs := .var "甲"
      , vars := ["甲"] }
    normalize [rule]
        (.app .cuoH
          (.app .cuoH (.app .cuoH (.hexLit Hexagram.heaven))))
      = .app .cuoH (.hexLit Hexagram.heaven) := by
  native_decide

/-- A non-matching Tm is left untouched. -/
example :
    let rule : RewriteRule :=
      { lhs := .app .cuoH (.app .cuoH (.var "甲"))
      , rhs := .var "甲"
      , vars := ["甲"] }
    normalize [rule] (.app .notB (.boolLit true))
      = .app .notB (.boolLit true) := by
  native_decide

/-! ## § 3  End-to-end via `wenyanCompileProgramWithDefs` -/

/-- (1) The canonical spec ⑫ example.

    After `定 错 错 甲 等 甲`, the program-level normaliser reduces
    `错 错 乾` to `乾`.  We check semantic equivalence: the rewritten
    chunk's `denoteHex` must equal `denoteHex` of the bare `乾`. -/
example :
    let prog := "定 错 错 甲 等 甲；错 错 乾"
    let lhs := (wenyanCompileProgramWithDefs prog).toOption
      |>.bind (·.getLast?) |>.map Stmt.body
    let rhs := (wenyanCompile "乾").toOption
    (lhs.bind (denoteHex ·.tm)) = (rhs.bind (denoteHex ·.tm)) := by
  native_decide

/-- (2) Direct AST equality: the exprStmt body's Tm is literally `.hexLit 乾`
    (the rule normalized it; no residual `.app .cuoH` remains). -/
example :
    let prog := "定 错 错 甲 等 甲；错 错 乾"
    (wenyanCompileProgramWithDefs prog).toOption
      |>.bind (·.getLast?) |>.map (·.body.tm)
      = some (.hexLit Hexagram.heaven) := by
  native_decide

/-- (3) Cascade through the surface pipeline: 4 错s → 0. -/
example :
    let prog := "定 错 错 甲 等 甲；错 错 错 错 乾"
    (wenyanCompileProgramWithDefs prog).toOption
      |>.bind (·.getLast?) |>.map (·.body.tm)
      = some (.hexLit Hexagram.heaven) := by
  native_decide

/-! ## § 4  Confluence + ambiguity -/

/-- (4) Two rules with the same head primitive are rejected.

    Two `错 错 ?` rules collide on head `.primH 10` (the index for `.cuoH`
    in the spine-walking discriminator).  The second add fails with
    `overlapWithExisting`. -/
example :
    let prog := "定 错 错 甲 等 甲；定 错 错 乙 等 乙"
    (match wenyanCompileProgramWithDefs prog with
     | .error (.defError 1 (.rewriteRuleRejected
         (.overlapWithExisting _ _))) => true
     | _ => false) = true := by native_decide

/-- (4b) Two rules with DIFFERENT primitive heads (`错 错 ?` vs `综 综 ?`)
    coexist because the spine-walking discriminator distinguishes them. -/
example :
    let prog := "定 错 错 甲 等 甲；定 综 综 乙 等 乙"
    (match wenyanCompileProgramWithDefs prog with
     | .ok _ => true
     | _ => false) = true := by native_decide

/-- (5) Ambiguous chunk: contains both 等 and 为 → `rewriteAmbiguous`.

    `定 X 为 Y 等 Z` — body contains 等 but starts with `定 ... 为`,
    we choose the safer path and reject. -/
example :
    let prog := "定 X 为 推 一 等 Z"
    (match wenyanCompileProgramWithDefs prog with
     | .error (.defError 0 .rewriteAmbiguous) => true
     | _ => false) = true := by native_decide

/-! ## § 5  Coexistence with Wen 1.5 / 2.0 ② -/

/-- (6) `定 NAME 为 BODY` still works after adding rewrite support. -/
example :
    (wenyanCompileProgramWithDefs "定 倍推 为 而 推 推；倍推 一").toOption.map
        (·.map (·.body.ty))
      = some [.arr .hex .hex, .hex] := by
  native_decide

/-- (7) Rewrite rule + user-def coexist in same program.

    The rule fires inside the body of a user-def chunk's expansion: the
    program parses successfully (3 statements: rewriteStmt, defStmt,
    exprStmt) and the trailing exprStmt has Hex type.  We don't pin
    down the exact Tm or the intermediate defStmt's body type since
    textual user-def expansion affects the post-rewrite structure;
    cohabitation is what matters here. -/
example :
    let prog := "定 错 错 甲 等 甲；定 倍推 为 而 推 推；倍推 乾"
    (wenyanCompileProgramWithDefs prog).toOption.map List.length
      = some 3 := by
  native_decide

/-- (7b) Final exprStmt of the same program has Hex type. -/
example :
    let prog := "定 错 错 甲 等 甲；定 倍推 为 而 推 推；倍推 乾"
    (wenyanCompileProgramWithDefs prog).toOption
      |>.bind (·.getLast?) |>.map (·.body.ty)
      = some .hex := by
  native_decide

/-- (8) `定递 NAME 为 BODY` still parses (rewrite detection didn't break it). -/
example :
    let prog := "定递 甲 为 者 乙 推 乙"
    (match wenyanCompileProgramWithDefs prog with
     | .ok _ => true
     | .error _ => false) = true := by native_decide

/-! ## § 6  Rule-validation rejections -/

/-- (9) Bare-var LHS is rejected.

    The source `定 甲 等 乾` would have LHS = `.var "甲"`, which would
    rewrite every term — rejected with `lhsIsBareVar`. -/
example :
    let prog := "定 甲 等 乾"
    (match wenyanCompileProgramWithDefs prog with
     | .error (.defError 0 (.rewriteRuleRejected .lhsIsBareVar)) => true
     | _ => false) = true := by native_decide

/-- (10) Non-linear LHS is rejected.

    `定 同 甲 甲 等 真`: the variable `甲` appears twice on the LHS, so
    the rule is non-linear and rejected. -/
example :
    let prog := "定 同 甲 甲 等 真"
    (match wenyanCompileProgramWithDefs prog with
     | .error (.defError 0 (.rewriteRuleRejected (.nonLinearLhs _))) => true
     | _ => false) = true := by native_decide

/-! ## § 7  Negative — rule that doesn't apply is a no-op -/

/-- (11) `错 错 甲 → 甲` declared, but the next chunk is `综 乾` — the rule
    doesn't fire, so `综 乾 ≡ Hexagram.heaven.reverse`. -/
example :
    let prog := "定 错 错 甲 等 甲；综 乾"
    (wenyanCompileProgramWithDefs prog).toOption
      |>.bind (·.getLast?) |>.bind (fun s => denoteHex s.body.tm)
      = some Hexagram.heaven.reverse := by
  native_decide

end SSBX.Foundation.Wen.WenSurface
