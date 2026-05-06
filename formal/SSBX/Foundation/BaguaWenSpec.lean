/-
# BaguaWenSpec — 受控文 baguaWen 之冻结词表

Frozen at HEAD `1cd30f8`, corresponding to `docs/baguaWen-spec.md`.

This module is the **machine-checkable** companion to the human-readable spec.
It defines:

  · `primaryToken` — canonical wenyan string for each YiInstr constructor
  · `primaryTokens` — the 12 verb tokens (de-duplicated, ordered)
  · `shiTokens` — 3 time-mode tokens
  · `yaoTokens` — 6 line-position tokens
  · `reservedTokens` — full reserved set (22 tokens, excluding numerals)

Lemmas verified by `native_decide`:
  · `primaryTokens` length = 12, no duplicates
  · `reservedTokens` length = 22
  · `primaryToken` covers every `YiInstr` constructor

Risk mitigated: 路径丙 § 风险 3.
-/
import SSBX.Foundation.BaguaTuring

namespace SSBX.Foundation.BaguaWenSpec

open SSBX.Foundation.Yi
open SSBX.Foundation.Cell192
open SSBX.Foundation.BaguaTuring

/-! ## § 1  12 主字 -/

/-- baguaWen 主字之规范化字符串。每个 `YiInstr` 构造子对应唯一一个 token。 -/
def primaryToken : YiInstr → String
  | .nop                => "不动"
  | .setShi _           => "设时"
  | .flipYao _          => "翻爻"
  | .hu                 => "互"
  | .cuo                => "错"
  | .zong               => "综"
  | .branchYaoEq _ _ _  => "比爻"
  | .branchShiEq _ _    => "比时"
  | .jump _             => "跳"
  | .push               => "推"
  | .pop                => "取"
  | .halt               => "终"

/-- 12 主字之表（去重，序与 YiInstr tag 对齐）。 -/
def primaryTokens : List String :=
  ["不动", "设时", "翻爻", "互", "错", "综",
   "比爻", "比时", "跳", "推", "取", "终"]

theorem primaryTokens_length : primaryTokens.length = 12 := by native_decide

theorem primaryTokens_nodup : primaryTokens.Nodup := by native_decide

/-! ## § 2  3 时态 -/

/-- 时态三字。 -/
def shiToken : Shi → String
  | .ji  => "已"
  | .jin => "今"
  | .wei => "未"

def shiTokens : List String := ["已", "今", "未"]

theorem shiTokens_length : shiTokens.length = 3 := by native_decide

/-! ## § 3  6 爻位 -/

/-- 爻位六字。 -/
def yaoTokens : List String :=
  ["初爻", "二爻", "三爻", "四爻", "五爻", "上爻"]

theorem yaoTokens_length : yaoTokens.length = 6 := by native_decide

theorem yaoTokens_nodup : yaoTokens.Nodup := by native_decide

/-! ## § 4  关键字与全保留集 -/

/-- 跳转目标关键字。 -/
def atKeyword : String := "至"

/-- 全部保留 token（不含数词）。M1 parser 遇任何不在此表的 CJK token 即拒。 -/
def reservedTokens : List String :=
  primaryTokens ++ shiTokens ++ yaoTokens ++ [atKeyword]

theorem reservedTokens_length : reservedTokens.length = 22 := by native_decide

theorem reservedTokens_nodup : reservedTokens.Nodup := by native_decide

/-! ## § 5  覆盖性公示 -/

/-- 公示：`primaryToken` 之返回总在 `primaryTokens` 表内（覆盖完整）。 -/
theorem primaryToken_in_primaryTokens (i : YiInstr) :
    primaryToken i ∈ primaryTokens := by
  cases i <;> simp [primaryToken, primaryTokens]

/-- 公示：`shiToken` 之返回总在 `shiTokens` 表内。 -/
theorem shiToken_in_shiTokens (s : Shi) : shiToken s ∈ shiTokens := by
  cases s <;> simp [shiToken, shiTokens]

/-! ## § 6  数词范围

  数词范围为 1..64（与 Hexagram 索引共域）。M1 parser 须验证数词在此范围内。
-/

/-- 数词上界。 -/
def maxNumeral : Nat := 64

theorem maxNumeral_eq : maxNumeral = 64 := rfl

end SSBX.Foundation.BaguaWenSpec
