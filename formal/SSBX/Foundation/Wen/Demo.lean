/-
# Demo · DaoJudgeWenyan — first-light PoC

路径丙 § M1 / M2 之 first light：

  1. **自编译**：`«解程» «道判源» = some daoJudgeProg`
  2. **印解之逆**：`«印程» daoJudgeProg = «道判源»`
  3. **自释（接 BaguaTuring）**：解析后由 `runFuel` 执行得末态
     - 乾卦 → 已（天道）
     - 否卦 → 未（心道，y3≠y4）

全数 `native_decide` 见证。

## 链条

```
String "«比爻» «三爻» «四爻» «至» «三»；…"
  ↓  «解程»  (M1)
List YiInstr [.branchYaoEq ⟨2,_⟩ ⟨3,_⟩ 3, .setShi .wei, .halt, …]
  ↓  YiState.init + runFuel  (BaguaTuring 已证)
末态 (Hexagram, Shi)
  ↓  .cur.2
Shi (天道 / 心道 / 今)
```

文之源 = 文之直写 = 文之执行 = Lean 之执行 — 一行 `native_decide` 见证。
-/
import SSBX.Foundation.Bagua.BaguaTuring
import SSBX.Foundation.Wen.WenyanParser

namespace SSBX.Foundation.Wen.Demo

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanParser

/-! ## § 1  道判源 -/

/-- 道判机之文言源（5 命，22-token 范围内）. -/
def «道判源» : String :=
  "«比爻» «三爻» «四爻» «至» «三»；«设时» «未»；«终»；«设时» «已»；«终»"

/-! ## § 2  自编译：文 → 形式项 -/

/-- 文之源经 «解程» 得到的程序与 daoJudgeProg 字面同体。 -/
theorem daojudge_parse :
    «解程» «道判源» = some daoJudgeProg := by native_decide

/-! ## § 3  印解之逆：形式项 → 文之源 -/

theorem daojudge_print :
    «印程» daoJudgeProg = «道判源» := by native_decide

/-! ## § 4  自释：解析后由 runFuel 执行 -/

/-- 乾卦 (all yang)：y3=y4=yang, branch 取，末态 Shi.ji（天道）. -/
theorem daojudge_qian :
    let prog := («解程» «道判源»).getD []
    ((YiState.init Hexagram.qian prog).runFuel 10).cur.2 = Shi.ji := by
  native_decide

/-- 坤卦 (all yin)：y3=y4=yin, branch 取，末态 Shi.ji（天道）. -/
theorem daojudge_kun :
    let prog := («解程» «道判源»).getD []
    ((YiState.init Hexagram.kun prog).runFuel 10).cur.2 = Shi.ji := by
  native_decide

/-- 否卦 (天地否, y1..y3=yin / y4..y6=yang)：y3=yin ≠ yang=y4, branch 不取，
    fall-through 至 setShi Shi.wei → 末态 Shi.wei (心道). -/
def «否» : Hexagram := ⟨.yin, .yin, .yin, .yang, .yang, .yang⟩

theorem daojudge_pi :
    let prog := («解程» «道判源»).getD []
    ((YiState.init «否» prog).runFuel 10).cur.2 = Shi.wei := by
  native_decide

/-! ## § 5  反例：非合度文言之拒接 -/

/-- 未注册之 token 拒接。 -/
example : «解程» "«未知字»；«终»" = none := by native_decide

/-- «设时» 之参数若非 三时态 之一，拒接。 -/
example : «解程» "«设时» «未知态»；«终»" = none := by native_decide

/-- 未闭之 «»，拒接。 -/
example : «解程» "«终" = none := by native_decide

/-! ## § 6  组合：解 + 印 之 fixpoint  -/

/-- daojudge 文之源经 «解程» → daoJudgeProg → «印程» = 自身. -/
theorem daojudge_compile_print_id :
    («解程» «道判源»).map «印程» = some «道判源» := by native_decide

end SSBX.Foundation.Wen.Demo
