/-
# WenSurface.UserInductiveTests — focused tests for wen-2.0 ④ (user inductive types)

Surface form: `类 TYPENAME = CTOR₁ | CTOR₂ | … | CTORₙ`.  Subsequent
statements resolve bare `CTORᵢ` glyphs (currently restricted to
heavenly stems — `Reading.surfaceVarNames`) to `Tm.userCtor TYPENAME
CTORᵢ`; the term typechecks at `Ty.user TYPENAME`.

Note: typenames must NOT collide with the catalogue (see
`nameConflictsWithCatalogue`).  In particular CJK words registered in
`multiCharSurfaces` (e.g. `五行`, `太极`) are reserved.  Tests use
unregistered glyph combinations like `甴甴` (which lexes as two
unknown tokens — not in `multiCharSurfaces`) or the 2-glyph `真假`
(which is also not registered as a catalogue compound).

This module is **not** in `SSBX.lean`'s import chain — it builds on demand
via `lake build SSBX.Foundation.Wen.WenSurface.UserInductiveTests`.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Wen.WenDef

/-! ## § 1  Surface decl parsing -/

/-- A 5-ctor decl on heavenly stems parses cleanly. -/
example :
    parseClassChunk? "类 甴甴 = 甲 | 乙 | 丙 | 丁 | 戊"
      = some ("甴甴", ["甲", "乙", "丙", "丁", "戊"]) :=
  by native_decide

/-- A 2-ctor decl on heavenly stems. -/
example :
    parseClassChunk? "类 真假 = 甲 | 乙" = some ("真假", ["甲", "乙"]) :=
  by native_decide

/-! ## § 2  End-to-end class compile -/

/-- (1) A valid `类` decl emits a `classStmt`; a subsequent reference to a
    ctor name elaborates to `.userCtor TYPENAME CTORNAME` with type
    `.user TYPENAME`. -/
example :
    let prog := "类 甴甴 = 甲 | 乙 | 丙 | 丁 | 戊；甲"
    (wenyanCompileProgramWithDefs prog).toOption.map
        (·.map (fun s => s.body.ty))
      = some [.hex, .user "甴甴"] :=
  by native_decide

/-- The exprStmt body Tm is exactly `Tm.userCtor "甴甴" "甲"`. -/
example :
    let prog := "类 甴甴 = 甲 | 乙 | 丙 | 丁 | 戊；甲"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?) |>.map Stmt.body
      = some ⟨.userCtor "甴甴" "甲", .user "甴甴"⟩ :=
  by native_decide

/-- (2) Class with 2 ctors; bare ctor use after decl elaborates. -/
example :
    let prog := "类 真假 = 甲 | 乙；甲"
    (wenyanCompileProgramWithDefs prog).toOption
        |>.bind (·.getLast?) |>.map (·.body.ty)
      = some (.user "真假") :=
  by native_decide

/-- A bare ctor followed by another ctor (sequential use, distinct
    statements) — both elaborate to `.userCtor` with the same `.user`
    type. -/
example :
    let prog := "类 甴甴 = 甲 | 乙 | 丙；甲；乙"
    (wenyanCompileProgramWithDefs prog).toOption.map
        (·.map (·.body.ty))
      = some [.hex, .user "甴甴", .user "甴甴"] :=
  by native_decide

/-! ## § 3  Rejection / hygiene -/

/-- (3) Ctor name clashing with a prior `定 NAME 为 BODY` decl: the
    `类` decl is rejected with `classCtorConflict`. -/
example :
    (match wenyanCompileProgramWithDefs "定 倍推 为 推 一；类 甴甴 = 倍推 | 甲" with
     | .error (.defError 1 (.classCtorConflict "甴甴" "倍推")) => true
     | _ => false) = true :=
  by native_decide

/-- (3b) The reverse direction — `定 NAME 为 BODY` where NAME clashes
    with an in-scope ctor: the `定` decl is rejected. -/
example :
    (match wenyanCompileProgramWithDefs "类 真假 = 甲 | 乙；定 甲 为 推 一" with
     | .error (.defError 1 (.conflictWithCatalogue "甲")) => true
     | _ => false) = true :=
  by native_decide

/-- (4) Reading a `甲` without any prior `类` decl: `甲` is a heavenly stem
    and resolves to `.var "甲"`, but with no binder it's unbound — clean
    error (no crash, no silent `.user`). -/
example :
    (wenyanCompileProgramWithDefs "甲").toOption.isNone :=
  by native_decide

/-- (5) Class redefinition rejected. -/
example :
    (match wenyanCompileProgramWithDefs "类 甴甴 = 甲 | 乙；类 甴甴 = 丙 | 丁" with
     | .error (.defError 1 (.classRedefinition "甴甴")) => true
     | _ => false) = true :=
  by native_decide

/-- (6) TYPENAME clashing with catalogue glyph rejected. -/
example :
    (match wenyanCompileProgramWithDefs "类 推 = 甲 | 乙" with
     | .error (.defError 0 (.classNameConflict "推")) => true
     | _ => false) = true :=
  by native_decide

/-- (7) Ctor that is a catalogue op (not a `.varName`) is rejected at
    decl time. -/
example :
    (match wenyanCompileProgramWithDefs "类 甴甴 = 甲 | 推" with
     | .error (.defError 0 (.classCtorConflict "甴甴" "推")) => true
     | _ => false) = true :=
  by native_decide

/-- (8) Empty constructor list (no `|`-separated names after `=`) is
    rejected.  Note: parseClassChunk? rejects empty ctors too; here we
    test it via the program pipeline. -/
example :
    (match wenyanCompileProgramWithDefs "类 X = " with
     | .error (.defError 0 _) => true
     | _ => false) = true :=
  by native_decide

/-! ## § 4  Kernel typecheck of `.userCtor` -/

/-- `Tm.userCtor "X" "甲"` typechecks to `.user "X"` in the empty ctx. -/
example :
    WenDef.typeCheck [] (.userCtor "甴甴" "甲") = some (.user "甴甴") :=
  by native_decide

/-- Two `.user` types with different names are distinct. -/
example : Ty.user "甴甴" ≠ Ty.user "真假" := by native_decide

end SSBX.Foundation.Wen.WenSurface
