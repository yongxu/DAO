/-
# WenSurface.NamespaceTests — `用 NS_NAME` end-to-end examples

Tests for Wen 2.0 item ③ (namespace / 用-stmt). Split from
`EndToEndTests.lean` to keep that file under the existing pipeline
focus. native_decide tests for `wenyanCompileProgramWithNamespaces`.

This module is NOT in `SSBX.lean`'s import chain — it builds on demand via
    lake build SSBX.Foundation.Wen.WenSurface.NamespaceTests
mirroring the EndToEndTests pattern.
-/
import SSBX.Foundation.Wen.WenSurface.Namespace

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Text.WenyanOperators

/-! ## 端到端 `用 NS_NAME` 示例 -/

/-- 用 墨经；推 一 — NS 声明 + code chunk，两者都在 stmts 中. -/
example :
    (wenyanCompileProgramWithNamespaces "用 墨经；推 一").toOption.map
        (fun r => (r.activeNamespaces, r.stmts.length, r.typedTms.length))
      = some ([.P], 2, 1) :=
  by native_decide

/-- 用 法家；用 墨经；不动 — 两 NS active，code 编译成功. -/
example :
    (wenyanCompileProgramWithNamespaces "用 法家；用 墨经；不动").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length))
      = some ([.L, .P], 1) :=
  by native_decide

/-- 用 名家；同 — 名家 active，同 解为 I_1 (catalogue). -/
example :
    (wenyanCompileProgramWithNamespaces "用 名家；同 一 一").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length))
      = some ([.G], 1) :=
  by native_decide

/-- 默认（无 `用` 声明）—— 行为同 1.5 wenyanCompileProgram. -/
example :
    (wenyanCompileProgramWithNamespaces "推 一；推 推 一；推 推 推 一").toOption.map
        (·.typedTms.length)
      = some 3 :=
  by native_decide

/-- 用 NONEXISTENT_NS 拒绝 (unknownNamespace error). -/
example :
    (match wenyanCompileProgramWithNamespaces "用 妖怪派" with
     | .error (.unknownNamespace _ name) => name = "妖怪派"
     | _ => False) :=
  by native_decide

/-! ## 别名 / 兼收繁简的 NS_NAME -/

example :
    (wenyanCompileProgramWithNamespaces "用 墨經；推 一").toOption.map (·.activeNamespaces)
      = some [.P] :=
  by native_decide

example :
    (wenyanCompileProgramWithNamespaces "用 莊子；推 一").toOption.map (·.activeNamespaces)
      = some [.ZHU] :=
  by native_decide

example :
    (wenyanCompileProgramWithNamespaces "用 兵法；推 一").toOption.map (·.activeNamespaces)
      = some [.SUN] :=
  by native_decide

/-! ## `用` 与 H_8 (体用) 不冲突：孤立「用」仍走 normal compile -/

/-- 「用」单独成句 → 视作 H_8 (L_10 alias) 编译；非 NS 声明. -/
example :
    (wenyanCompileProgramWithNamespaces "用 乾").toOption.map (·.typedTms.length)
      -- 「用 乾」 中「用」 不是已知 NS_NAME，且「乾」 也不是 → unknownNamespace
      = none :=
  by native_decide

/-- 但「用 乾」 应触发 unknownNamespace 错误，因为我们以「用 X」开头检测. -/
example :
    (match wenyanCompileProgramWithNamespaces "用 乾" with
     | .error (.unknownNamespace _ name) => name = "乾"
     | _ => False) :=
  by native_decide

/-! ## 多句程序：NS 状态贯穿 -/

/-- 6 句程序：用 X；code；code；用 Y；code；code  — active 集 = [X, Y]. -/
example :
    (wenyanCompileProgramWithNamespaces
        "用 墨经；推 一；推 推 一；用 名家；同 一 一；推 一").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length, r.stmts.length))
      = some ([.P, .G], 4, 6) :=
  by native_decide

/-- 仅 NS 声明，无 code — typedTms 为空但 stmts 有声明. -/
example :
    (wenyanCompileProgramWithNamespaces "用 墨经；用 名家；用 法家").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length, r.stmts.length))
      = some ([.P, .G, .L], 0, 3) :=
  by native_decide

/-! ## 错误 index 正确 -/

example :
    (match wenyanCompileProgramWithNamespaces "推 一；用 妖怪派；推 二" with
     | .error (.unknownNamespace i name) => i = 1 ∧ name = "妖怪派"
     | _ => False) :=
  by native_decide

example :
    (match wenyanCompileProgramWithNamespaces "用 墨经；XYZ不存在；推 一" with
     | .error (.compile i _) => i = 1
     | _ => False) :=
  by native_decide

/-! ## 12 学派覆盖 sanity (one per group) -/

example : (wenyanCompileProgramWithNamespaces "用 墨经").toOption.map (·.activeNamespaces) = some [.P] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 名家").toOption.map (·.activeNamespaces) = some [.G] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 法家").toOption.map (·.activeNamespaces) = some [.L] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 医家").toOption.map (·.activeNamespaces) = some [.Y] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 庄子").toOption.map (·.activeNamespaces) = some [.ZHU] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 孙子").toOption.map (·.activeNamespaces) = some [.SUN] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 楚辞").toOption.map (·.activeNamespaces) = some [.CHU] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 礼记").toOption.map (·.activeNamespaces) = some [.LIJ] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 杂家").toOption.map (·.activeNamespaces) = some [.ZA] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 史官").toOption.map (·.activeNamespaces) = some [.E] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 荀子").toOption.map (·.activeNamespaces) = some [.X] := by native_decide
example : (wenyanCompileProgramWithNamespaces "用 补遗").toOption.map (·.activeNamespaces) = some [.Z] := by native_decide

end SSBX.Foundation.Wen.WenSurface
