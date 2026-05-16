/-
# WenSurface.ProseSample — 文言级 prose 样本之 end-to-end round-trip

镜像 `formal/SSBX/Foundation/Wen/samples/wenSurfaceProse.wen` 之 7 行,
每行通过 `wenyanCompile / wenyanInterp / wenyanInterpBool` 跑完整管线
(lex → resolveWithCues → parseSurface → elabSurface → desugar via
 `theoremBackedSemanticsFor?` → WenDef.Tm → R₈ denotation), 并将
结果 pin 死.

## 与 EndToEndTests.lean 之别

EndToEndTests 是 318 例零散 sanity. 本模块把 7 个 S-组虚词 (一/推/之/
而/凡/令/者) 拼成一段连续 prose, 演示 WenSurface 这一层 *作为整体*
可用; 等同于把 `samples/wenSurfaceProse.wen` 之注释外内容搬入 Lean.

## 与 baguaWen ISA 之别

`samples/{hello,microKernel,daoJudge}.wen` 是 «»-quoted 22-token 汇编,
走 Bagua-ISA 内核; 本样本走 WenSurface 之 desugar 层, 落到同一组
WenDef.Tm builtin (推=`Stdlib.tuiBody` / 同=`Stdlib.tongBody` 等),
故"两条平行表面"在 R₈ 上汇合.

## 状态

0 sorry / 0 axiom. 每行一个 `native_decide`, 总和经 `theorem
proseSurface_endToEnd` 汇总.

## 不在 SSBX.lean 之中

与 EndToEndTests 同理 — `native_decide` 在 `Hexagram := Fin 6 → Bool`
之后 per-example ~10s, 故不进默认 build chain; 按需:

    lake build SSBX.Foundation.Wen.WenSurface.ProseSample
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## § 1  Prose 样本行 (镜像 samples/wenSurfaceProse.wen)

每个常量对应 `.wen` 文件中之一非注释行. 单引号 String, 不含末尾换行. -/

def proseLine_yi          : String := "一"
def proseLine_tuiYi       : String := "推 一"
def proseLine_tuiZhiYi    : String := "推 之 一"
def proseLine_erTuiSunYi  : String := "而 推 損 一"
def proseLine_fanForall   : String := "凡 甲 同 甲 甲"
def proseLine_lingBind    : String := "令 甲 乾 推 甲"
def proseLine_zheLambda   : String := "（者 甲 甲 之 乾） 之 推"

/-! ## § 2  逐行 round-trip 例 -/

/-- 一 → «一». -/
example : (wenyanInterp proseLine_yi).toOption = some «一» := by native_decide

/-- 推 一 → «生» «一». -/
example : (wenyanInterp proseLine_tuiYi).toOption = some («生» «一») := by native_decide

/-- 推 之 一 ≡ 推 一 (「之」 application marker 透明). -/
example :
    (wenyanInterp proseLine_tuiZhiYi).toOption
      = (wenyanInterp proseLine_tuiYi).toOption :=
  by native_decide

/-- 而 推 損 一 → «一» (推 ∘ 損 = id mod 64). -/
example : (wenyanInterp proseLine_erTuiSunYi).toOption = some «一» := by native_decide

/-- 凡 甲 同 甲 甲 → true (∀ Hex 甲, 甲 = 甲). -/
example : (wenyanInterpBool proseLine_fanForall).toOption = some true := by native_decide

/-- 令 甲 乾 推 甲 → «一» (let 甲 := 乾 in 推 甲 = «生» 乾 = «一»). -/
example : (wenyanInterp proseLine_lingBind).toOption = some «一» := by native_decide

/-- （者 甲 甲 之 乾） 之 推 → «一» ((λx.x) 乾 = 乾, then 推 乾 = «一»). -/
example : (wenyanInterp proseLine_zheLambda).toOption = some «一» := by native_decide

/-! ## § 3  汇总定理

七行 prose 同时成立, 见证 WenSurface 这一层 *作为整体* 端到端可用. -/

theorem proseSurface_endToEnd :
    (wenyanInterp     proseLine_yi          ).toOption = some «一»
  ∧ (wenyanInterp     proseLine_tuiYi       ).toOption = some («生» «一»)
  ∧ (wenyanInterp     proseLine_tuiZhiYi    ).toOption
      = (wenyanInterp proseLine_tuiYi       ).toOption
  ∧ (wenyanInterp     proseLine_erTuiSunYi  ).toOption = some «一»
  ∧ (wenyanInterpBool proseLine_fanForall   ).toOption = some true
  ∧ (wenyanInterp     proseLine_lingBind    ).toOption = some «一»
  ∧ (wenyanInterp     proseLine_zheLambda   ).toOption = some «一» := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end SSBX.Foundation.Wen.WenSurface
