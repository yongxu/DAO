/-
# XingWei — 几何位 · 形式 / 度量 / 易经四位

Companion document: `义理/几何位 · 从元到形.md`

This file formalizes the **几何位** 衍 file's metric / topology / 易经四位 results
on top of `BaguaAlgebra`'s `hammingDist`.

  § 1   项目几何字 (dian/wei/ju/lin/zhong/ying/bi/dang) as Lean defs
  § 2   汉明度量公理：对称、自距零、三角不等式（NEW results）
  § 3   反爻之等距性：motion/middleFlip/topFlip 保汉明距离
  § 4   立方体 Euler 特征：3-cube χ = 1，6-cube χ = 1（concrete computation）
  § 5   易经四位 之 Lean wrap（refer Yi.lean）

## 道理二分立场
本文件给出 **理层** 之具体度量与位结构。所证之三角不等式、对称性、等距性
皆是关于具体类型 `Trigram`/`Hexagram` 之 finitary 命题，0 sorry / 0 公理。
-/
import SSBX.Foundation.Atlas.YiLegacy.Bagua.BaguaAlgebra
import SSBX.Foundation.Atlas.YiLegacy.Yi

namespace SSBX.Foundation.Eight.XingWei

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.Yi.Hexagram
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 项目几何字 -/

/-- **点 (dian)**：几何之元 = `Unit`，cardinality 1。 -/
abbrev Dian : Type := Unit

/-- **位 (wei)**：八卦层之具体顶点。 -/
abbrev Wei : Type := Trigram

/-- **距 (ju)**：度量函数 = 汉明距离。 -/
def ju (a b : Trigram) : Nat := hammingDist a b

/-- **邻 (lin)**：距 1 之配对（一爻之差）。 -/
def lin (a b : Trigram) : Bool := decide (ju a b = 1)

/-! ## § 2 度量公理之 Lean 形式

数与算术 + 几何位之"度量公理"（symm, refl-zero, triangle）皆形式化。 -/

/-- **自距零**（refl-zero）：`ju a a = 0`. -/
theorem ju_self (a : Trigram) : ju a a = 0 := by
  unfold ju; exact hammingDist_self a

/-- **同一**：`ju a b = 0 ⟺ a = b`. -/
theorem ju_eq_zero_iff (a b : Trigram) : ju a b = 0 ↔ a = b := by
  unfold ju; exact hammingDist_eq_zero_iff a b

/-- **对称**：`ju a b = ju b a`. -/
theorem ju_comm (a b : Trigram) : ju a b = ju b a := by
  unfold ju hammingDist
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-- **三角不等式**：`ju a c ≤ ju a b + ju b c`（NEW result, 单值 cardinality 论证）。 -/
theorem ju_triangle (a b c : Trigram) : ju a c ≤ ju a b + ju b c := by
  unfold ju hammingDist
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  rcases c with ⟨c₁, c₂, c₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;>
      cases c₁ <;> cases c₂ <;> cases c₃ <;> decide

/-- **直径上界**：`ju a b ≤ 3`（继承 BaguaAlgebra）。 -/
theorem ju_le_three (a b : Trigram) : ju a b ≤ 3 := by
  unfold ju; exact hammingDist_le_3 a b

/-! ## § 3 反爻之等距性 (isometry)

(Z/2)³ 群作用是 (Trigram, ju) 上之等距群——
即"几何对称群 = 算子群"。 -/

/-- **动 (motion) 等距**：`ju (motion a) (motion b) = ju a b`. -/
theorem motion_iso (a b : Trigram) : ju (motion a) (motion b) = ju a b := by
  unfold ju hammingDist motion
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-- **化 (middleFlip) 等距**：`ju (middleFlip a) (middleFlip b) = ju a b`. -/
theorem middleFlip_iso (a b : Trigram) : ju (middleFlip a) (middleFlip b) = ju a b := by
  unfold ju hammingDist middleFlip
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-- **变 (topFlip) 等距**：`ju (topFlip a) (topFlip b) = ju a b`. -/
theorem topFlip_iso (a b : Trigram) : ju (topFlip a) (topFlip b) = ju a b := by
  unfold ju hammingDist topFlip
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-- **错 (complement) 等距**：错卦保距离（错 = 三反复合，由各反等距递进可得）。 -/
theorem complement_iso (a b : Trigram) : ju (Trigram.complement a) (Trigram.complement b) = ju a b := by
  unfold ju hammingDist Trigram.complement
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-! ## § 4 立方体 Euler 特征

3-cube 之 (V, E, F, C) = (8, 12, 6, 1)，Euler 特征 χ = 1（contractible）。 -/

/-- 3-cube 顶点数：8（八卦）。 -/
def cube3_V : Nat := 8

/-- 3-cube 边数：12（每轴 4 边 × 3 轴）。 -/
def cube3_E : Nat := 12

/-- 3-cube 面数：6（每轴对 face × 3 轴对）。 -/
def cube3_F : Nat := 6

/-- 3-cube 体数：1（整体一个 3-cube）。 -/
def cube3_C : Nat := 1

/-- **3-cube Euler 特征 = 1**：contractible。 -/
theorem cube3_euler : cube3_V + cube3_F = cube3_E + cube3_C + 1 := by
  unfold cube3_V cube3_E cube3_F cube3_C
  decide

/-- 显式形式：χ = V - E + F - C = 1（用 Int 表达）。 -/
theorem cube3_euler_int :
    (cube3_V : Int) - cube3_E + cube3_F - cube3_C = 1 := by
  unfold cube3_V cube3_E cube3_F cube3_C
  decide

/-- 顶点数验证：`Trigram.all.length = cube3_V`. -/
theorem trigram_card_cube3 : Trigram.all.length = cube3_V := by decide

/-! ## § 5 6-cube Euler 特征

6-cube 之 face counts：每 k-cell 数 = C(6,k) · 2^(6-k)。
χ = (2-1)^6 = 1. -/

/-- 6-cube 各维 cell 数。 -/
def cube6_V : Nat := 64    -- C(6,0) × 2^6 = 1 × 64
def cube6_E : Nat := 192   -- C(6,1) × 2^5 = 6 × 32
def cube6_2 : Nat := 240   -- C(6,2) × 2^4 = 15 × 16
def cube6_3 : Nat := 160   -- C(6,3) × 2^3 = 20 × 8
def cube6_4 : Nat := 60    -- C(6,4) × 2^2 = 15 × 4
def cube6_5 : Nat := 12    -- C(6,5) × 2^1 = 6 × 2
def cube6_6 : Nat := 1     -- C(6,6) × 2^0 = 1 × 1

/-- **6-cube Euler 特征 = 1**：64 卦立方体 contractible。
    χ = V - E + F2 - F3 + F4 - F5 + F6
      = 64 - 192 + 240 - 160 + 60 - 12 + 1 = 1 -/
theorem cube6_euler_int :
    (cube6_V : Int) - cube6_E + cube6_2 - cube6_3 + cube6_4 - cube6_5 + cube6_6 = 1 := by
  unfold cube6_V cube6_E cube6_2 cube6_3 cube6_4 cube6_5 cube6_6
  decide

/-- 顶点数验证：`Hexagram.allHex.length = cube6_V`. -/
theorem hexagram_card_cube6 : Hexagram.allHex.length = cube6_V := by decide

/-! ## § 6 易经四位 之 Lean wrap

Yi.lean 已实现 `wellPos / isZhongPos / yingResponds / biAdj`。
本节给出项目字面 wrap 与一些具体结果。 -/

/-- **当 (dang)**：当位之 wrap。 -/
abbrev dang : Hexagram → Fin 6 → Bool := wellPos

/-- **中 (zhong)**：中位之 wrap。 -/
abbrev zhong : Fin 6 → Bool := isZhongPos

/-- **应 (ying)**：应位之 wrap。 -/
abbrev ying : Hexagram → Fin 3 → Bool := yingResponds

/-- **比 (bi)**：比位之 wrap。 -/
abbrev bi : Hexagram → Fin 5 → Yao × Yao := biAdj

/-- **乾五位**当位（具体见证）。 -/
theorem dang_qian_5 : dang Hexagram.heaven ⟨4, by omega⟩ = true := heaven_5th_wellPos

/-- **坤五位**不当位（阴爻在阳位）。 -/
theorem dang_kun_5_not : dang Hexagram.earth ⟨4, by omega⟩ = false := earth_5th_not_wellPos

/-- **既济**全当位：六爻皆当其位。 -/
theorem dang_jiji_all (i : Fin 6) : dang Hexagram.complete i = true := complete_wellPos_all i

/-- **未济**全不当位：六爻皆不当其位。 -/
theorem dang_weiji_none (i : Fin 6) : dang Hexagram.incomplete i = false := incomplete_wellPos_none i

/-! ## § 7 公开摘要 -/

/-- **几何位总摘要**：度量公理 + 反爻等距 + Euler χ = 1 + 易经四位。 -/
theorem xingwei_summary :
    -- (1) 度量公理
    (∀ a : Trigram, ju a a = 0)
    ∧ (∀ a b : Trigram, ju a b = 0 ↔ a = b)
    ∧ (∀ a b : Trigram, ju a b = ju b a)
    ∧ (∀ a b c : Trigram, ju a c ≤ ju a b + ju b c)
    -- (2) 三反爻等距
    ∧ (∀ a b : Trigram, ju (motion a) (motion b) = ju a b)
    ∧ (∀ a b : Trigram, ju (middleFlip a) (middleFlip b) = ju a b)
    ∧ (∀ a b : Trigram, ju (topFlip a) (topFlip b) = ju a b)
    -- (3) 立方体 Euler
    ∧ ((cube3_V : Int) - cube3_E + cube3_F - cube3_C = 1)
    ∧ ((cube6_V : Int) - cube6_E + cube6_2 - cube6_3 + cube6_4 - cube6_5 + cube6_6 = 1)
    -- (4) 卡数验证
    ∧ (Trigram.all.length = cube3_V)
    ∧ (Hexagram.allHex.length = cube6_V) :=
  ⟨ju_self, ju_eq_zero_iff, ju_comm, ju_triangle,
   motion_iso, middleFlip_iso, topFlip_iso,
   cube3_euler_int, cube6_euler_int,
   trigram_card_cube3, hexagram_card_cube6⟩

end SSBX.Foundation.Eight.XingWei
