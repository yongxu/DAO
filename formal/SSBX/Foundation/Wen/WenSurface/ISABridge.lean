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

## 「错等变」约束 (complement-equivariance ceiling)

由 `WenDefCompile.lean` 之 doctrine: YiInstr 之 12 原语皆与 Hex.complement
通约. 故任 YiInstr 可表达之 f : Hex → Hex 须满足

    f(h.complement) = (f h).complement    ... (★)

非 equivariant 项 (如 «生» / `.jia` / Stdlib.tuiBody / Stdlib.sunBody / .yi)
**结构性不可桥**. 此非工程缺陷, 是 YiInstr 之代数刚性. 故下方 `推`/`损`
返 `none`, 符预期.

可桥子集:
  · identity (`者 甲 甲`)
  · `.cuoH` / `.zongH` / `.huH` / `.cuoZongH` / `.flip1H`..`.flip6H`
  · 经 `Stdlib.endoCompBody` 之 straight-line composition (`而 反 综` 等)
  · `Stdlib.repeatOnceBody` (`再 反` 等)
  · `Stdlib.hexApplyBody` 之透明应用

## 状态

0 sorry / 0 axiom / 总函数. 全 6 例由 `native_decide` 见证, 含 64-Hex
finite agreement (`compiledHexFunAgrees`).

## 不在 SSBX.lean

per-example native_decide 在 `Hexagram := Fin 6 → Bool` 之后 ~10s, 故
不进默认 build chain. 按需:

    lake build SSBX.Foundation.Wen.WenSurface.ISABridge
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd
import SSBX.Foundation.Wen.WenDefCompile

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
文言 prose → Bagua-ISA 程序. 仅对 type `Hex → Hex` 且经 64-Hex 验证之
complement-equivariant 子集返成功; 其他 (含 non-equivariant 与非 Hex→Hex 型)
皆返 `none`. -/
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

/-! ## § 3  不可桥子集 (non-equivariant) -/

/-- 「推」 (= `Stdlib.tuiBody` 用 `.jia` + `.yi`, 非 equivariant) → `none`. -/
example : wenyanCompileToYiInstr? "推" = none := by native_decide

/-- 「損」 (= `Stdlib.sunBody`, mod-64 减, 非 equivariant) → `none`. -/
example : wenyanCompileToYiInstr? "損" = none := by native_decide

/-- 「同」 (Hex × Hex → Bool, 非 Hex → Hex 型) → `none`. -/
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

/-! ## § 5  汇总定理 -/

/-- 文言→Bagua-ISA 桥之核心见证:

    五个 equivariant prose 例皆 (i) 成功 compile, (ii) 与 wenyanInterp 在
    64 Hex 上跨层一致; 二个 non-equivariant 例正确返 `none` (反映 YiInstr
    之代数刚性).

  Bagua-ISA 不是 WenSurface 之"另一个表面", 是其后端目标. 此定理为 PR #26
  之"vertical slice"补一段水平桥: 两条表面在 WenDef.Tm 处汇合. -/
theorem isaBridge_endToEnd :
    -- (i) 可桥子集: cross-layer 一致
    proseBridgeAgrees "错" = true
  ∧ proseBridgeAgrees "综" = true
  ∧ proseBridgeAgrees "互" = true
  ∧ proseBridgeAgrees "而 反 综" = true
  ∧ proseBridgeAgrees "再 反" = true
    -- (ii) 不可桥子集: 正确拒绝
  ∧ wenyanCompileToYiInstr? "推" = none
  ∧ wenyanCompileToYiInstr? "損" = none
  ∧ wenyanCompileToYiInstr? "同" = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end SSBX.Foundation.Wen.WenSurface
