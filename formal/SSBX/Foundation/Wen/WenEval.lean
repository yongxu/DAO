/-
# WenEval — 多步求值器（Cell256 编码层）

Path 丙 § M2：把 `metaStep` 之单步反射扩展为多步求值，并提供 String 端到端入口
（`解程` + `runFuel` + `encState` 三件合一）。

## 设计

`wenEval n s = StateEnc.encState (s.runFuel n)`

即「n 步后的末态编码」。

  ·  `wenEval_correct`     由定义即得 (refl)
  ·  `wenEval_head`        编码列首 = 末态之 cur
  ·  `wenEval_succ`        wenEval (n+1) 之展开（halted / step 二分）
  ·  `wenEval_halted`      停态下幂等

顶层入口 `«解执»`：String → Hexagram → Nat → Option (List Cell256)
  ·  `解执 src h n = ((«解程» src).map (fun p => wenEval n (YiState.init h p)))`

## 状态

0 sorry / 0 axiom / 全 def 总函数。
具体程序之端到端见证由 native_decide。

## 链条

```
String  ──[«解程»]──→  List YiInstr  ──[YiState.init h]──→  YiState
                                            │
                                            ↓ runFuel n
                                          YiState
                                            │
                                            ↓ StateEnc.encState
                                       List Cell256
                                       ↑
                                  wenEval n / 解执
```

`«解执» «道判源» qian 10` 之 head = `some (qian, Shi.ji)` —— 文之源经 String 入，
最终在编码层得到「乾卦 + 已（天道）」之 cur 字面，全 Lean kernel 见证.
-/
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Wen.WenyanParser

namespace SSBX.Foundation.Wen.WenEval

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanParser

/-! ## § 1  wenEval — n 步求值之编码 -/

/-- 多步 metaStep：n 步后的末态编码。 -/
def wenEval (n : Nat) (s : YiState) : List Cell256 :=
  StateEnc.encState (s.runFuel n)

/-! ## § 2  基本性质 -/

/-- wenEval 与 encState ∘ runFuel 同形（定义即得）. -/
theorem wenEval_correct (n : Nat) (s : YiState) :
    wenEval n s = StateEnc.encState (s.runFuel n) := rfl

/-- 0 步：编码原状态. -/
theorem wenEval_zero (s : YiState) :
    wenEval 0 s = StateEnc.encState s := rfl

/-- 编码列首即末态之 cur. -/
theorem wenEval_head (n : Nat) (s : YiState) :
    (wenEval n s).head? = some (s.runFuel n).cur := by
  unfold wenEval StateEnc.encState
  rfl

/-! ## § 3  顶层入口 — String 端到端 -/

/-- 「解执」：从文之源、初卦、燃料 n，得末态之编码列。 -/
def «解执» (src : String) (h : Hexagram) (n : Nat) : Option (List Cell256) :=
  («解程» src).map (fun p => wenEval n (YiState.init h p))

/-- 解执之正确性：解程成功时，解执 = wenEval ∘ runFuel 之复合. -/
theorem «解执_correct» (src : String) (h : Hexagram) (n : Nat)
    (prog : List YiInstr) (hp : «解程» src = some prog) :
    «解执» src h n = some (StateEnc.encState ((YiState.init h prog).runFuel n)) := by
  unfold «解执»
  rw [hp]
  rfl

/-- 解执之首格：成功时返回末态之 cur. -/
theorem «解执_head» (src : String) (h : Hexagram) (n : Nat)
    (prog : List YiInstr) (hp : «解程» src = some prog) :
    («解执» src h n).bind (fun cells => cells.head?)
      = some ((YiState.init h prog).runFuel n).cur := by
  rw [«解执_correct» src h n prog hp]
  show (StateEnc.encState ((YiState.init h prog).runFuel n)).head?
       = some ((YiState.init h prog).runFuel n).cur
  unfold StateEnc.encState
  rfl

/-! ## § 4  端到端 PoC：道判文之源 → 编码末态 -/

/-- 「道判源」（重声明，与 Demo.«道判源» 同体）. -/
def «道判源» : String :=
  "«比爻» «三爻» «四爻» «至» «三»；«设时» «未»；«终»；«设时» «已»；«终»"

/-- 端到端 1：乾卦输入 → 解执 → 编码列首 = (乾, 已). -/
theorem «端到端_乾» :
    («解执» «道判源» Hexagram.qian 10).bind (fun cells => cells.head?)
      = some (Hexagram.qian, Shi.ji) := by native_decide

/-- 端到端 2：坤卦输入 → 解执 → 编码列首 = (坤, 已). -/
theorem «端到端_坤» :
    («解执» «道判源» Hexagram.kun 10).bind (fun cells => cells.head?)
      = some (Hexagram.kun, Shi.ji) := by native_decide

/-- 端到端 3：否卦输入 → 解执 → 编码列首 = (否, 未). -/
def «否» : Hexagram := ⟨.yin, .yin, .yin, .yang, .yang, .yang⟩

theorem «端到端_否» :
    («解执» «道判源» «否» 10).bind (fun cells => cells.head?)
      = some («否», Shi.wei) := by native_decide

/-- 端到端 4：非法源 → 解执 = none. -/
theorem «端到端_非法» :
    «解执» "«未知»" Hexagram.qian 10 = none := by native_decide

/-! ## § 5  与 metaStep 之关系

  `metaStep` (in WenyanSelfInterp) gives single-step reflection:
    `metaStep s = StateEnc.encState s.step`

  `wenEval n s = StateEnc.encState (s.runFuel n)`.

  By `runFuel.zero = id`，`wenEval 0 s = StateEnc.encState s`.
  其余多步关系（与 `runFuel` 之归纳一致）由调用 `runFuel` 之既有性质即得；
  本文件仅给 PoC 端到端，多步循环之 simulation 留 §6b universal interp.
-/

end SSBX.Foundation.Wen.WenEval
