/-
# WenSurface.ISABridge — 文言 → Bagua-ISA 端到端桥

## 缘起

`samples/wenSurfaceProse.wen` 跑在 `wenyanInterp` (Lean 直执 WenDef.Tm
denotation); `samples/{hello,microKernel,daoJudge}.wen` 跑在 `wenyan` CLI
之 Bagua-ISA virtual machine. 二者过去看似两条平行表面.

本模块把它们桥接为单一管线:

  String --wenyanCompile--> Tm --compileHexFunCertified?--> List YiInstr

并证: 该 ISA 程序在 64 Hex 上之输出 == wenyanInterp 之 denotation.
故 Bagua-ISA 实际是 WenDef.Tm 之**后端目标**, 不是另一个表面.

## v2 — universal Hex → Hex 桥 (post-doctrine break, 2026-05-17)

v1 doctrine 之「错等变 ceiling」在 v2 中**已破**: `BaguaTuring.lean`
加 `branchYaoYang` 后, ISA 升为 universal Hex → Hex 后端。

v1 之「★ 等式」`(prog h).complement = prog h.complement`：
- 在 v2 中仅对 `complementEquivariantProg` 子集成立
- `branchYaoYang` 含 program 不在此约束内, 可表 `Stdlib.tuiBody` (+1 mod 64) /
  `Stdlib.sunBody` (-1 mod 64) 等 non-equivariant Hex → Hex 函数

故 `推` / `損` 在 v2 中可桥 (v1 中返 `none`)。下方 §3 之示例更新。

可桥子集 (v2):
  · 所有 Hex → Hex Tm (universal, 含 v1 之 equivariant 子集与新加 non-equivariant)
  · identity (`者 甲 甲`)
  · `.cuoH` / `.zongH` / `.huH` / `.cuoZongH` / `.flip1H`..`.flip6H`
  · 经 `Stdlib.endoCompBody` 之 straight-line composition (`而 反 综` 等)
  · `Stdlib.repeatOnceBody` (`再 反` 等)
  · `Stdlib.hexApplyBody` 之透明应用
  · **v2 新**: `Stdlib.tuiBody` (推, +1 mod 64) / `Stdlib.sunBody` (損, -1 mod 64)

仍不可桥 (类型不匹配, 与 equivariance 无关):
  · `同` (`.eqHex : Hex → Hex → Bool`) — 非 `Hex → Hex` 型

## 状态

0 sorry / 0 axiom / 总函数. 全 8+ 例由 `native_decide` 见证, 含 64-Hex
finite agreement (`compiledHexFunAgrees`).

## 不在 SSBX.lean

per-example native_decide 在 `Hexagram := Fin 6 → Bool` 之后 ~10s, 故
不进默认 build chain. 按需:

    lake build SSBX.Foundation.Wen.WenSurface.ISABridge
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd
import SSBX.Foundation.Wen.WenDefCompile
-- WenyanParser provides `DecidableEq YiInstr` (needed for native_decide on
-- nested `Option (List YiInstr)` equalities — see line ~95).  Without this
-- import, typeclass synthesis silently fails on the deeper test cases.
import SSBX.Foundation.Wen.WenyanParser

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval
open SSBX.Foundation.Wen.WenDefCompile

/-! ## § 1  String → YiInstr 之端到端桥 -/

/--
文言 prose → Bagua-ISA 程序. v2: 对 type `Hex → Hex` 且经 64-Hex 验证之
universal Tm 子集 (含 v1 equivariant 与 v2 新加之 non-equivariant tui/sun)
返成功; 非 `Hex → Hex` 型 (如 `同 : Hex → Hex → Bool`) 返 `none`. -/
def wenyanCompileToYiInstr? (s : String) : Option (List YiInstr) :=
  match wenyanCompile s with
  | .ok typed => compileHexFunCertified? typed.tm
  | .error _ => none

/-! ## § 2  可桥子集 (equivariant) -/

/-- 「者 甲 甲」 (λx. x) → `[halt]`. -/
example : wenyanCompileToYiInstr? "者 甲 甲" = some [.halt] := by native_decide

/-- 「错」 → `[complement, halt]`. -/
example : wenyanCompileToYiInstr? "错" = some [.complement, .halt] := by native_decide

/-- 「综」 → `[reverse, halt]`. -/
example : wenyanCompileToYiInstr? "综" = some [.reverse, .halt] := by native_decide

/-- 「互」 → `[interlace, halt]`. -/
example : wenyanCompileToYiInstr? "互" = some [.interlace, .halt] := by native_decide

/-- 「而 反 综」 → `[reverse, complement, halt]`. 反 = `.cuoH`, 综 = `.zongH`,
    复合顺序: g 先 (反 后处理), f 后 (复合定义: f∘g, 先跑 g). -/
example :
    wenyanCompileToYiInstr? "而 反 综" = some [.reverse, .complement, .halt] :=
  by native_decide

/-- 「再 反」 (反 ∘ 反 = id 之复合形) → `[complement, complement, halt]`. -/
example :
    wenyanCompileToYiInstr? "再 反" = some [.complement, .complement, .halt] :=
  by native_decide

/-! ## § 3  v2 新可桥子集 (non-equivariant Hex → Hex, was rejected in v1)

  v2 doctrine break 把 `Stdlib.tuiBody` (mod-64 +1) 与 `Stdlib.sunBody` (mod-64 -1)
  从 v1 之 "结构性不可 compile" 移入 "可 compile" 子集, via `branchYaoYang`
  之 propagate-carry/borrow adder (见 `WenDefCompile.lean § 3b`).

  Prose-level 之 wenyanCompile "推" 单独 (无 arg) 仍因 parser arity 检查 error;
  v2 之 universality 在 ISA 层 (Tm → YiInstr 之 compile) 直接见证, 不依 prose
  parser 之 arity 配合.
-/

/-- 直接 ISA 层测试 (绕过 prose parser): `compileHexFunCertified? Stdlib.tuiBody`
    现 v2 中返 `some (tuiSteps ++ [.halt])` (含 5 个 `branchYaoYang`). -/
example : compileHexFunCertified? Stdlib.tuiBody = some (tuiSteps ++ [.halt]) := by
  native_decide

/-- 直接 ISA 层测试: `compileHexFunCertified? Stdlib.sunBody`
    现 v2 中返 `some (sunSteps ++ [.halt])`. -/
example : compileHexFunCertified? Stdlib.sunBody = some (sunSteps ++ [.halt]) := by
  native_decide

/-! ## § 3b  仍不可桥子集 (类型不匹配, 与 equivariance 无关) -/

/-- 「同」 (`.eqHex : Hex → Hex → Bool`, 非 `Hex → Hex` 型) → 仍 `none`. -/
example : wenyanCompileToYiInstr? "同" = none := by native_decide

/-! ## § 4  跨层 commute (64-Hex finite agreement)

`compiledHexFunCertified?` 已要求 `compiledHexFunAgrees` (64 Hex 全验证).
本节把"成功 compile"显式 pin 到 cross-layer 跨层一致:

    ∀ h ∈ 64 Hex, runHexProg prog h == denoteHexFun typed.tm h

亦即 Bagua-ISA 执行 = wenyanInterp 计值. -/

/-- 把 "wenyanCompile 成功 + ISA 桥成功 + 64 Hex agreement" 三件事并合
    成一个 native_decide 判定: 给出 prose, 若可桥, 桥与解释必跨层一致. -/
def proseBridgeAgrees (s : String) : Bool :=
  match wenyanCompile s with
  | .ok typed =>
      match compileHexFunCertified? typed.tm with
      | some prog => compiledHexFunAgrees typed.tm prog
      | none => false
  | .error _ => false

/-- 「错」 cross-layer 一致. -/
example : proseBridgeAgrees "错" = true := by native_decide

/-- 「综」 cross-layer 一致. -/
example : proseBridgeAgrees "综" = true := by native_decide

/-- 「互」 cross-layer 一致. -/
example : proseBridgeAgrees "互" = true := by native_decide

/-- 「而 反 综」 cross-layer 一致 — 复合算子端到端见证. -/
example : proseBridgeAgrees "而 反 综" = true := by native_decide

/-- 「再 反」 cross-layer 一致. -/
example : proseBridgeAgrees "再 反" = true := by native_decide

/-- v2: ISA-level cross-layer agreement for `Stdlib.tuiBody` (mod-64 +1).
    Bypasses prose parser (推 alone is arity-error at parser level). -/
example : compiledHexFunAgrees Stdlib.tuiBody (tuiSteps ++ [.halt]) = true := by
  native_decide

/-- v2: ISA-level cross-layer agreement for `Stdlib.sunBody` (mod-64 -1). -/
example : compiledHexFunAgrees Stdlib.sunBody (sunSteps ++ [.halt]) = true := by
  native_decide

/-! ## § 5  汇总定理 (v2 — universal coverage of `Hex → Hex` 子集) -/

/-- 文言→Bagua-ISA 桥之 v2 核心见证:

    (i) 5 v1 equivariant prose 例皆 (a) 成功 compile, (b) 与 wenyanInterp 在
        64 Hex 上跨层一致
    (ii) v2 新加 2 个 non-equivariant Tm (Stdlib.tuiBody / Stdlib.sunBody)
         直接 ISA 层 universal compile + 64-Hex agreement (prose parser 之
         arity 检查 故 推/損 单独无 arg 仍 parser-error; ISA-level test 直接
         测 Tm)
    (iii) 1 个非 `Hex → Hex` 型 (同 : Hex → Hex → Bool) 仍正确返 `none`
          (类型不匹配, 与 equivariance 无关)

  Bagua-ISA 不是 WenSurface 之"另一个表面", 是其后端目标. v2 中 ISA 升为
  universal Hex → Hex 后端 (含 cuo-equivariant 与 non-equivariant 子集). -/
theorem isaBridge_endToEnd :
    -- (i) v1 equivariant 子集: cross-layer 一致
    proseBridgeAgrees "错" = true
  ∧ proseBridgeAgrees "综" = true
  ∧ proseBridgeAgrees "互" = true
  ∧ proseBridgeAgrees "而 反 综" = true
  ∧ proseBridgeAgrees "再 反" = true
    -- (ii) v2 ISA-level: tui / sun universal compile + 64-Hex agreement
  ∧ compileHexFunCertified? Stdlib.tuiBody = some (tuiSteps ++ [.halt])
  ∧ compileHexFunCertified? Stdlib.sunBody = some (sunSteps ++ [.halt])
    -- (iii) 类型不匹配: 正确拒绝
  ∧ wenyanCompileToYiInstr? "同" = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end SSBX.Foundation.Wen.WenSurface
