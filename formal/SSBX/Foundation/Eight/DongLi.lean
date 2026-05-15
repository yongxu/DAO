/-
# DongLi — 动力 · 离散动力系统之最薄骨架

Companion document: `义理/动力 · 从元到行.md`

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
import SSBX.Foundation.Atlas.Yi.Classical.Core.Yi
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.BaguaAlgebra
import SSBX.Foundation.Eight.TongJi

namespace SSBX.Foundation.Eight.DongLi

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra

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

/-- **motion 动力系统**：相空间 = Trigram，一步 = motion。 -/
def dongDyn : DynSys Trigram where step := motion

/-- **middleFlip 动力系统**。 -/
def middleFlipDyn : DynSys Trigram where step := middleFlip

/-- **topFlip 动力系统**。 -/
def topFlipDyn : DynSys Trigram where step := topFlip

/-- **complement 动力系统**（错卦：阴阳全反）。 -/
def complementDyn : DynSys Trigram where step := Trigram.complement

/-- **motion 在 乾 上之 2-周期性**：iter 2 = id at 乾。 -/
theorem motion_heaven_period :
    iter dongDyn 2 heaven = heaven := motion_motion heaven

/-- **motion 在 Trigram 上无不动点**：不存在 t 使 motion t = t。 -/
theorem motion_no_fixed : ¬ ∃ t : Trigram, IsFixed dongDyn t := by
  rintro ⟨⟨y1, y2, y3⟩, h⟩
  cases y1 <;> simp [IsFixed, dongDyn, motion, Yao.neg] at h <;> revert h <;> decide

/-- **middleFlip 在 Trigram 上无不动点**。 -/
theorem middleFlip_no_fixed : ¬ ∃ t : Trigram, IsFixed middleFlipDyn t := by
  rintro ⟨⟨y1, y2, y3⟩, h⟩
  cases y2 <;> simp [IsFixed, middleFlipDyn, middleFlip, Yao.neg] at h <;> revert h <;> decide

/-- **topFlip 在 Trigram 上无不动点**。 -/
theorem topFlip_no_fixed : ¬ ∃ t : Trigram, IsFixed topFlipDyn t := by
  rintro ⟨⟨y1, y2, y3⟩, h⟩
  cases y3 <;> simp [IsFixed, topFlipDyn, topFlip, Yao.neg] at h <;> revert h <;> decide

/-! ## § 4 周期 = 2 -/

/-- **motion 周期 = 2**：motion² = id 即任意 t 是 motion 之 2-周期点。 -/
theorem motion_period_2 (t : Trigram) : IsPeriodic dongDyn 2 t := by
  unfold IsPeriodic iter
  exact motion_motion t

/-- **middleFlip 周期 = 2**。 -/
theorem middleFlip_period_2 (t : Trigram) : IsPeriodic middleFlipDyn 2 t :=
  middleFlip_middleFlip t

/-- **topFlip 周期 = 2**。 -/
theorem topFlip_period_2 (t : Trigram) : IsPeriodic topFlipDyn 2 t :=
  topFlip_topFlip t

/-- **complement 周期 = 2**：错² = id。 -/
theorem complement_period_2 (t : Trigram) : IsPeriodic complementDyn 2 t := by
  unfold IsPeriodic iter complementDyn
  exact Trigram.complement_involutive t

/-! ## § 5 Markov 链 之 Nat 计数版（接 TongJi 之大衍）-/

/-- **大衍单步转移**：以 DaYan 之 4 状态投影到 Yao 之 2 状态。
    laoYin → yang（必变）；lesserYang → yang；lesserYin → yin；laoYang → yin（必变）。 -/
def daYanProject : SSBX.Foundation.Eight.TongJi.DaYan → Yao
  | .laoYin   => .yang  -- 老阴 → 之卦阳
  | .lesserYang => .yang  -- 少阳 → 阳
  | .lesserYin  => .yin   -- 少阴 → 阴
  | .laoYang  => .yin   -- 老阳 → 之卦阴

/-- **大衍投影确定**：每个 DaYan 唯一对应一 Yao（即 Markov 矩阵每行单点）。 -/
theorem daYanProject_laoYin_yang : daYanProject .laoYin = .yang := rfl
theorem daYanProject_shaoYang_yang : daYanProject .lesserYang = .yang := rfl
theorem daYanProject_shaoYin_yin : daYanProject .lesserYin = .yin := rfl
theorem daYanProject_laoYang_yin : daYanProject .laoYang = .yin := rfl

/-! ## § 6 之卦动力（多老爻同变）-/

/-- **本卦 → 之卦**：取 Trigram 之每爻，依"老必变 / 少不变"得之卦。
    简化：仅作 Trigram 反爻（即每爻 toggle if isLao）。
    本文件取**全反**作 demo（实际之卦由具体老爻位置决定，不全反）。 -/
def zhiTrigram (t : Trigram) : Trigram := Trigram.complement t

/-- **之卦动力周期 = 2**：本卦 → 之卦 → 本卦（complement² = id）。 -/
theorem zhi_period_2 (t : Trigram) : zhiTrigram (zhiTrigram t) = t := by
  unfold zhiTrigram
  exact Trigram.complement_involutive t

/-! ## § 7 连续 ODE 之 finite approximation (Phase 4 先行)

ODE: dx/dt = f(x)，连续。
Euler 离散化：x_{n+1} = x_n + h · f(x_n)。
Trigram-空间之 finite 版：相空间 = Trigram，"速度场" f : Trigram → 候选 transform，
"一步" = 应用 transform 至 current state。

无 Mathlib 之核心可建：
- targetEulerStep：每步靠近 target 一爻（Hamming 距 ≤ 1 步）
- Lyapunov 函数：hammingDist(x, target)，在 targetEulerStep 下严格下降
- 收敛：在 ≤ 3 步内必到 target（Trigram 之 hammingDist ≤ 3）

连续 ODE 之 smoothness / Lipschitz / Cauchy 等需 Mathlib，属 Phase 4 之 Mathlib 工作。 -/

/-- **target-driven Euler step**：从 current 一步靠 target（直接应用 transform）。 -/
def targetEulerStep (target current : Trigram) : Trigram :=
  transform current target current

/-- **target-Euler 之 transform_correct**：一步即达 target。 -/
theorem targetEuler_one_step (target current : Trigram) :
    targetEulerStep target current = target :=
  transform_correct current target

/-- **Lyapunov 函数**：到 target 之 Hamming 距离。 -/
def lyapunov (target current : Trigram) : Nat :=
  hammingDist target current

/-- **Lyapunov 上界**：≤ 3。 -/
theorem lyapunov_bound (target current : Trigram) :
    lyapunov target current ≤ 3 :=
  hammingDist_le_3 target current

/-- **Lyapunov 之严格下降**：一步后 Lyapunov = 0（直达）。 -/
theorem lyapunov_descent_one_step (target current : Trigram) :
    lyapunov target (targetEulerStep target current) = 0 := by
  unfold lyapunov targetEulerStep
  rw [transform_correct]
  exact hammingDist_self target

/-- **lyapunov 之自反性**：lyapunov target target = 0。 -/
theorem lyapunov_zero_at_target (target : Trigram) :
    lyapunov target target = 0 :=
  hammingDist_self target

/-- **finite reach**：从任意 current 到 target 一步即达。 -/
theorem finite_reach_one_step (target current : Trigram) :
    iter ⟨targetEulerStep target⟩ 1 current = target := by
  unfold iter
  exact targetEuler_one_step target current

/-! ## § 8 不动点之 finite 收敛（Banach 之 finite 类比）

在 finite simply-transitive 群作用下，**任意 target 是 target-Euler 之不动点**。
此即 Banach 不动点定理之 finite 类比：collapse 在一步内完成。 -/

/-- **target-Euler 在 target 上不动**。 -/
theorem targetEuler_fixed_at_target (target : Trigram) :
    targetEulerStep target target = target :=
  transform_correct target target

/-- **target-Euler 之 fixed point structure**：每个 target 在自身之 Euler step 下静止。 -/
theorem targetEuler_idempotent (target current : Trigram) :
    targetEulerStep target (targetEulerStep target current) = target := by
  rw [targetEuler_one_step]

/-! ## § 9 公开摘要 -/

/-- **动力总摘要**（含 Phase 4 先行：连续 ODE 之 finite approximation）：
    (1) motion 在 Trigram 上无不动点
    (2) middleFlip 在 Trigram 上无不动点
    (3) topFlip 在 Trigram 上无不动点
    (4) motion 周期 = 2（任意起点）
    (5) middleFlip 周期 = 2
    (6) topFlip 周期 = 2
    (7) complement 周期 = 2
    (8) 之卦周期 = 2
    (9) orbit 长度公式
    (10) 大衍 4 状态 → Yao 投影确定
    (11) target-Euler 一步达 target
    (12) Lyapunov 一步降至 0
    (13) target-Euler idempotent at target
    (14) Lyapunov 上界 ≤ 3 -/
theorem dongli_summary :
    (¬ ∃ t : Trigram, IsFixed dongDyn t)
    ∧ (¬ ∃ t : Trigram, IsFixed middleFlipDyn t)
    ∧ (¬ ∃ t : Trigram, IsFixed topFlipDyn t)
    ∧ (∀ t : Trigram, IsPeriodic dongDyn 2 t)
    ∧ (∀ t : Trigram, IsPeriodic middleFlipDyn 2 t)
    ∧ (∀ t : Trigram, IsPeriodic topFlipDyn 2 t)
    ∧ (∀ t : Trigram, IsPeriodic complementDyn 2 t)
    ∧ (∀ t : Trigram, zhiTrigram (zhiTrigram t) = t)
    ∧ (∀ (S : DynSys Trigram) (n : Nat) (x : Trigram), (orbit S n x).length = n)
    ∧ (daYanProject .laoYin = .yang)
    ∧ (∀ target current : Trigram, targetEulerStep target current = target)
    ∧ (∀ target current : Trigram, lyapunov target (targetEulerStep target current) = 0)
    ∧ (∀ target current : Trigram, targetEulerStep target (targetEulerStep target current) = target)
    ∧ (∀ target current : Trigram, lyapunov target current ≤ 3) :=
  ⟨motion_no_fixed, middleFlip_no_fixed, topFlip_no_fixed,
   motion_period_2, middleFlip_period_2, topFlip_period_2, complement_period_2, zhi_period_2,
   orbit_length, daYanProject_laoYin_yang,
   targetEuler_one_step, lyapunov_descent_one_step,
   targetEuler_idempotent, lyapunov_bound⟩

end SSBX.Foundation.Eight.DongLi
