/-
# ChunkedDecide — 长 List 之分段反射判定

When `«微核源»` (M4-甲) reaches ~500 instructions, a single `native_decide` call
on a 500-element `List YiInstr` may exceed Lean kernel reduction limits.  This
module provides the chunking framework: split-and-conquer for `Bool`-valued
predicates over lists.

Key technique:
  ((xs ++ ys).all p = true) ↔ (xs.all p = true) ∧ (ys.all p = true)

So we can `native_decide` each half independently and combine.

Risk mitigated: 路径丙 § 风险 1（native_decide 对长 List 卡顿）.
-/
import SSBX.Foundation.BaguaTuring

namespace SSBX.Foundation.ChunkedDecide

open SSBX.Foundation.Yi
open SSBX.Foundation.Cell192
open SSBX.Foundation.BaguaTuring

/-! ## § 1  「all」 之分合 -/

/-- 分合律：`xs ++ ys` 上 `all p` 等于二者各自 `all p` 之合取。 -/
theorem all_append {α : Type} (xs ys : List α) (p : α → Bool) :
    (xs ++ ys).all p = (xs.all p && ys.all p) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.all_cons, ih, Bool.and_assoc]

/-- 三段分合（用于将 ~500 行字面拆为三段后分别 native_decide）。 -/
theorem all_append3 {α : Type} (xs ys zs : List α) (p : α → Bool) :
    (xs ++ ys ++ zs).all p = (xs.all p && ys.all p && zs.all p) := by
  rw [all_append, all_append]

/-! ## § 2  范例：将 daoJudgeProg 分两半 -/

/-- daoJudgeProg 的前半（3 条）。 -/
def daoJudgeFront : List YiInstr := daoJudgeProg.take 3

/-- daoJudgeProg 的后半（剩余）。 -/
def daoJudgeBack : List YiInstr := daoJudgeProg.drop 3

theorem daoJudge_split : daoJudgeFront ++ daoJudgeBack = daoJudgeProg := by
  unfold daoJudgeFront daoJudgeBack
  exact List.take_append_drop 3 daoJudgeProg

theorem daoJudgeFront_length : daoJudgeFront.length = 3 := by native_decide
theorem daoJudgeBack_length : daoJudgeBack.length = 2 := by native_decide

/-! ## § 3  分段反射模式

  以下展示「分段 native_decide → 合取」之三步法。当 `«微核源»` 长 500 时，
  可分 10 段每段 50 条，分别证明，再以 `all_append` 拼。
-/

/-- 全是 nop 的占位谓词（用于演示模式）。 -/
def isNop : YiInstr → Bool
  | .nop => true
  | _    => false

/-- 范例：daoJudgeFront 上 `isNop` 之判定（其实 false，仅展示分段模式）。 -/
example : daoJudgeFront.all isNop = false := by native_decide

/-- 范例：分段判定后合取（同义重写演示）。 -/
example :
    daoJudgeProg.all (fun _ => true) = true := by native_decide

/-- 范例：用 `all_append` 把 daoJudgeProg 上的全 true 判定拆为两段证。 -/
example : daoJudgeProg.all (fun _ => true) = true := by
  rw [← daoJudge_split, all_append]
  -- 现在目标变成: daoJudgeFront.all _ && daoJudgeBack.all _ = true
  native_decide

/-! ## § 4  长度上界提示

  Lean kernel 之 `native_decide` 在 List 长度 ≤ 200 时通常 < 5s。
  超过 200 时建议拆段。`«微核源»` (~500) 推荐拆 10 段。
-/

/-- 推荐分段大小（行数）。 -/
def recommendedChunkSize : Nat := 50

theorem recommendedChunkSize_eq : recommendedChunkSize = 50 := rfl

end SSBX.Foundation.ChunkedDecide
