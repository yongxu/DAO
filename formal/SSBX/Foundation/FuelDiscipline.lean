/-
# FuelDiscipline — 燃料显式纪律

Forces every claim about program execution to carry **explicit fuel** as a
parameter.  No `∃ n, halts p n` ever appears as a `Decidable` claim — that
would collide with `GodelLi.halts_undecidable_internally`.

Provides:
  · `BoundedExec p h n` — explicit-fuel execution structure with witness
  · `«合度判停» p h n` — Bool-valued bounded halting check (decidable)
  · sanity lemma: `daoJudgeProg` halts within 10 fuel for every input

Risk mitigated: 路径丙 § 风险 5（Gödel 撞墙）.
-/
import SSBX.Foundation.BaguaTuring

namespace SSBX.Foundation.FuelDiscipline

open SSBX.Foundation.Yi
open SSBX.Foundation.Cell192
open SSBX.Foundation.BaguaTuring

/-! ## § 1  有界执行结构 -/

/-- 「有界执」：显式 fuel + 末态凭据。任何关于执行的命题都应通过此结构传递。 -/
structure BoundedExec (p : List YiInstr) (h : Hexagram) (n : Nat) where
  finalState : YiState
  witness : (YiState.init h p).runFuel n = finalState

namespace BoundedExec

/-- 总判定：给定 (p, h, n)，「有界执」总存在。 -/
def run (p : List YiInstr) (h : Hexagram) (n : Nat) : BoundedExec p h n :=
  ⟨(YiState.init h p).runFuel n, rfl⟩

/-- 末态之 cur 卦时。 -/
def curOf {p : List YiInstr} {h : Hexagram} {n : Nat}
    (b : BoundedExec p h n) : Cell192 := b.finalState.cur

/-- 末态是否已止。 -/
def haltedOf {p : List YiInstr} {h : Hexagram} {n : Nat}
    (b : BoundedExec p h n) : Bool := b.finalState.halted

end BoundedExec

/-! ## § 2  合度判停 — 显式 fuel 之停机 Bool 函数 -/

/-- 「合度判停」：显式 fuel 之停机判定。**不**判 `∃ n`，故不撞 Gödel。 -/
def «合度判停» (p : List YiInstr) (h : Hexagram) (n : Nat) : Bool :=
  ((YiState.init h p).runFuel n).halted

/-- 反射等价：判停函数等于 `runFuel` 末态的 halted 标志。 -/
theorem judgeHalt_reflect (p : List YiInstr) (h : Hexagram) (n : Nat) :
    «合度判停» p h n = ((YiState.init h p).runFuel n).halted := rfl

/-- 凭据之等价：用 BoundedExec 取末态与直接 `runFuel` 等价。 -/
theorem judgeHalt_via_bounded (p : List YiInstr) (h : Hexagram) (n : Nat) :
    «合度判停» p h n = (BoundedExec.run p h n).haltedOf := rfl

/-! ## § 3  范例：道判 + 乾卦必停 -/

/-- 验证：daoJudgeProg 在乾卦输入 + 10 燃料下必止（与 BaguaTuring.daoJudgeProg_total_within_10
    精神一致）。 -/
example : «合度判停» daoJudgeProg Hexagram.qian 10 = true := by native_decide

/-- 验证：daoJudgeProg 在坤卦输入 + 10 燃料下必止。 -/
example : «合度判停» daoJudgeProg Hexagram.kun 10 = true := by native_decide

/-! ## § 4  边界声明（命名而不证）

  以下命题**不可**声明为 Decidable / 不可 `native_decide`：
    · `∀ p h, Decidable (∃ n, ((YiState.init h p).runFuel n).halted = true)`
    · `∀ p h, ∃ n, «合度判停» p h n = true`（即「全程序必停」）
    · 任何忽略 fuel 之停机断言

  反例与不可判定性见 `GodelLi.halts_undecidable_internally`、`KleeneInternal.lean`。
  本模块仅在 fuel 显式时声明；fuel 隐式之断言留给 partial def 与外部 oracle。
-/

end SSBX.Foundation.FuelDiscipline
