/-
# DongLi — 动力 · 离散动力系统之最薄骨架

Companion document: `四级生成_太极两翼四象八卦/动力 · 从元到行.md`

This file gives the **finite, no-Mathlib** core of the **动力** 衍 file:
  § 1   动力系统 DynSys（相空间 + 一步映射）
  § 2   迭代 iter / 轨道 orbit
  § 3   不动点 FixedPoint / 周期点 Periodic
  § 4   八卦反爻动力（无不动点 / 周期 = 2）
  § 5   Markov 链 之 Nat 计数版
  § 6   公开摘要

## 道理二分立场
本文件仅依 Lean stdlib + Yi.lean + BaguaAlgebra，不引入 Mathlib。
连续动力（ODE/PDE）/ Lyapunov / chaos / KAM 皆 Phase 4 future work（需 Mathlib + 实数）。
-/
import SSBX.Foundation.Yi
import SSBX.Foundation.BaguaAlgebra
import SSBX.Foundation.TongJi

namespace SSBX.Foundation.DongLi

open SSBX.Foundation.Yi
open SSBX.Foundation.BaguaAlgebra

/-! ## § 1 离散动力系统 -/

/-- **离散动力系统**：相空间 X + 一步映射 T : X → X。 -/
structure DynSys (X : Type) where
  step : X → X

/-- **n 步迭代** Tⁿ。 -/
def iter {X : Type} (S : DynSys X) : Nat → X → X
  | 0,     x => x
  | n + 1, x => S.step (iter S n x)

/-- **轨道**之前 n 步：[x, T(x), T²(x), ..., Tⁿ⁻¹(x)]。 -/
def orbit {X : Type} (S : DynSys X) (n : Nat) (x : X) : List X :=
  (List.range n).map (fun k => iter S k x)

/-- **轨道长度** = n。 -/
theorem orbit_length {X : Type} (S : DynSys X) (n : Nat) (x : X) :
    (orbit S n x).length = n := by
  unfold orbit
  rw [List.length_map, List.length_range]

/-! ## § 2 不动点 / 周期点 -/

/-- **不动点**：T(x) = x。 -/
def IsFixed {X : Type} (S : DynSys X) (x : X) : Prop :=
  S.step x = x

/-- **周期点 of period k**：Tᵏ(x) = x。 -/
def IsPeriodic {X : Type} (S : DynSys X) (k : Nat) (x : X) : Prop :=
  iter S k x = x

/-- 不动点是周期 1 之周期点。 -/
theorem fixed_is_periodic_one {X : Type} (S : DynSys X) (x : X)
    (h : IsFixed S x) : IsPeriodic S 1 x := by
  unfold IsPeriodic iter
  exact h

/-! ## § 3 八卦反爻动力 · 无不动点 -/

/-- **dong 动力系统**：相空间 = Trigram，一步 = dong。 -/
def dongDyn : DynSys Trigram where step := dong

/-- **hua 动力系统**。 -/
def huaDyn : DynSys Trigram where step := hua

/-- **bian 动力系统**。 -/
def bianDyn : DynSys Trigram where step := bian

/-- **cuo 动力系统**（错卦：阴阳全反）。 -/
def cuoDyn : DynSys Trigram where step := Trigram.cuo

/-- **dong 在 乾 上之 2-周期性**：iter 2 = id at 乾。 -/
theorem dong_qian_period :
    iter dongDyn 2 qian = qian := dong_dong qian

/-- **dong 在 Trigram 上无不动点**：不存在 t 使 dong t = t。 -/
theorem dong_no_fixed : ¬ ∃ t : Trigram, IsFixed dongDyn t := by
  rintro ⟨⟨y1, y2, y3⟩, h⟩
  cases y1 <;> simp [IsFixed, dongDyn, dong, Yao.neg] at h

/-- **hua 在 Trigram 上无不动点**。 -/
theorem hua_no_fixed : ¬ ∃ t : Trigram, IsFixed huaDyn t := by
  rintro ⟨⟨y1, y2, y3⟩, h⟩
  cases y2 <;> simp [IsFixed, huaDyn, hua, Yao.neg] at h

/-- **bian 在 Trigram 上无不动点**。 -/
theorem bian_no_fixed : ¬ ∃ t : Trigram, IsFixed bianDyn t := by
  rintro ⟨⟨y1, y2, y3⟩, h⟩
  cases y3 <;> simp [IsFixed, bianDyn, bian, Yao.neg] at h

/-! ## § 4 周期 = 2 -/

/-- **dong 周期 = 2**：dong² = id 即任意 t 是 dong 之 2-周期点。 -/
theorem dong_period_2 (t : Trigram) : IsPeriodic dongDyn 2 t := by
  unfold IsPeriodic iter
  exact dong_dong t

/-- **hua 周期 = 2**。 -/
theorem hua_period_2 (t : Trigram) : IsPeriodic huaDyn 2 t :=
  hua_hua t

/-- **bian 周期 = 2**。 -/
theorem bian_period_2 (t : Trigram) : IsPeriodic bianDyn 2 t :=
  bian_bian t

/-- **cuo 周期 = 2**：错² = id。 -/
theorem cuo_period_2 (t : Trigram) : IsPeriodic cuoDyn 2 t := by
  unfold IsPeriodic iter cuoDyn
  exact Trigram.cuo_cuo t

/-! ## § 5 Markov 链 之 Nat 计数版（接 TongJi 之大衍）-/

/-- **大衍单步转移**：以 DaYan 之 4 状态投影到 Yao 之 2 状态。
    laoYin → yang（必变）；shaoYang → yang；shaoYin → yin；laoYang → yin（必变）。 -/
def daYanProject : SSBX.Foundation.TongJi.DaYan → Yao
  | .laoYin   => .yang  -- 老阴 → 之卦阳
  | .shaoYang => .yang  -- 少阳 → 阳
  | .shaoYin  => .yin   -- 少阴 → 阴
  | .laoYang  => .yin   -- 老阳 → 之卦阴

/-- **大衍投影确定**：每个 DaYan 唯一对应一 Yao（即 Markov 矩阵每行单点）。 -/
theorem daYanProject_laoYin_yang : daYanProject .laoYin = .yang := rfl
theorem daYanProject_shaoYang_yang : daYanProject .shaoYang = .yang := rfl
theorem daYanProject_shaoYin_yin : daYanProject .shaoYin = .yin := rfl
theorem daYanProject_laoYang_yin : daYanProject .laoYang = .yin := rfl

/-! ## § 6 之卦动力（多老爻同变）-/

/-- **本卦 → 之卦**：取 Trigram 之每爻，依"老必变 / 少不变"得之卦。
    简化：仅作 Trigram 反爻（即每爻 toggle if isLao）。
    本文件取**全反**作 demo（实际之卦由具体老爻位置决定，不全反）。 -/
def zhiTrigram (t : Trigram) : Trigram := Trigram.cuo t

/-- **之卦动力周期 = 2**：本卦 → 之卦 → 本卦（cuo² = id）。 -/
theorem zhi_period_2 (t : Trigram) : zhiTrigram (zhiTrigram t) = t := by
  unfold zhiTrigram
  exact Trigram.cuo_cuo t

/-! ## § 7 公开摘要 -/

/-- **动力总摘要**：
    (1) dong 在 Trigram 上无不动点
    (2) hua 在 Trigram 上无不动点
    (3) bian 在 Trigram 上无不动点
    (4) dong 周期 = 2（任意起点）
    (5) hua 周期 = 2
    (6) bian 周期 = 2
    (7) cuo 周期 = 2
    (8) 之卦周期 = 2
    (9) orbit 长度公式
    (10) 大衍 4 状态 → Yao 投影确定 -/
theorem dongli_summary :
    (¬ ∃ t : Trigram, IsFixed dongDyn t)
    ∧ (¬ ∃ t : Trigram, IsFixed huaDyn t)
    ∧ (¬ ∃ t : Trigram, IsFixed bianDyn t)
    ∧ (∀ t : Trigram, IsPeriodic dongDyn 2 t)
    ∧ (∀ t : Trigram, IsPeriodic huaDyn 2 t)
    ∧ (∀ t : Trigram, IsPeriodic bianDyn 2 t)
    ∧ (∀ t : Trigram, IsPeriodic cuoDyn 2 t)
    ∧ (∀ t : Trigram, zhiTrigram (zhiTrigram t) = t)
    ∧ (∀ (S : DynSys Trigram) (n : Nat) (x : Trigram), (orbit S n x).length = n)
    ∧ (daYanProject .laoYin = .yang) :=
  ⟨dong_no_fixed, hua_no_fixed, bian_no_fixed,
   dong_period_2, hua_period_2, bian_period_2, cuo_period_2, zhi_period_2,
   orbit_length, daYanProject_laoYin_yang⟩

end SSBX.Foundation.DongLi
