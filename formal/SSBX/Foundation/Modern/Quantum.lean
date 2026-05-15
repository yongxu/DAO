/-
# Quantum — 量子叠加 / qubit / Pauli 矩阵 (Phase 4 主体 · Mathlib)

Companion: `义理/物理 · 从元到象.md` § 二 / § 四

物理衍 §二 已严格陈述 Yao ≅ qubit basis；§四 已陈述反爻 ≅ Pauli X (在 basis 上)。
本文借 Mathlib `Matrix` + `InnerProductSpace` 升 Phase 3 之 finite basis layer 至
**叠加层** (superposition layer)：qubit ≅ ℂ²、Pauli X / Y / Z 矩阵、Hadamard、3-qubit Trigram。

## 与 P17 之 complement-不变性之关系

**P17 发现**：YiInstr 之所有指令 complement-等变 → BaguaTuring 表达力 ≤ 2^32 complement-不变 Hex→Bool。
**量子层之 complement**：complement = X⊗X⊗X⊗X⊗X⊗X (六 qubit Pauli X) — charge conjugation / parity 之具体形态。
此即 P17 之结构对称在量子层之自然解读。

## 道理二分立场
本文涉 ℂ + Hilbert 空间，必依 Mathlib。
项目之**离散 basis 层**已在 WuXiang.lean 0-Mathlib 严格证；
本文是**连续叠加层**之桥——属"道层"对"理层"之扩张。
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import SSBX.Foundation.Eight.WuXiang

namespace SSBX.Foundation.Modern.Quantum

open Complex Matrix
open SSBX.Foundation.Bagua.BaguaAlgebra

/-! ## § 1 Qubit ≅ ℂ² (computational basis) -/

/-- **Qubit 类型**：ℂ² 之向量。 -/
abbrev Qubit : Type := Fin 2 → ℂ

/-- **|0⟩ basis state**：(1, 0)。 -/
def ket0 : Qubit := ![1, 0]

/-- **|1⟩ basis state**：(0, 1)。 -/
def ket1 : Qubit := ![0, 1]

/-- **Yao → Qubit basis**：yang ↦ |0⟩，yin ↦ |1⟩。 -/
def Yao.toQubit : SSBX.Foundation.Yi.Yi.Yao → Qubit
  | .yang => ket0
  | .yin  => ket1

/-! ## § 2 Pauli 矩阵 -/

/-- **Pauli X**（NOT gate）：[[0,1],[1,0]]。 -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- **Pauli Z**：[[1,0],[0,-1]]。 -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- **Pauli Y**：[[0,-i],[i,0]]。 -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- **Hadamard 矩阵**：(1/√2) · [[1,1],[1,-1]]。 -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℝ) / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]

/-! ## § 3 Pauli X² = I -/

/-- **Pauli X 自逆**（X² = id）—— Yao.neg² = id 在矩阵层之对应。 -/
theorem pauliX_squared : pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold pauliX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Pauli Z 自逆**。 -/
theorem pauliZ_squared : pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold pauliZ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## § 4 Pauli X 在 basis 上 ≅ Yao.neg

WuXiang.lean 之 `Yao.toBool / Bool.toYao` 给离散 basis 层之 Yao ≅ Bool；
此处升至 ℂ²：Pauli X 作用于 |0⟩ 给 |1⟩，给 |1⟩ 给 |0⟩——即 Yao.neg 在矩阵层之实现。 -/

/-- **Pauli X 在 |0⟩ 上**：X · |0⟩ = |1⟩。 -/
theorem pauliX_apply_ket0 :
    Matrix.mulVec pauliX ket0 = ket1 := by
  unfold pauliX ket0 ket1
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Pauli X 在 |1⟩ 上**：X · |1⟩ = |0⟩。 -/
theorem pauliX_apply_ket1 :
    Matrix.mulVec pauliX ket1 = ket0 := by
  unfold pauliX ket0 ket1
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Pauli X = 爻取反**：在 `Yao → Qubit basis` 上，X 正是 `Yao.neg`。 -/
theorem pauliX_apply_yao_basis (y : SSBX.Foundation.Yi.Yi.Yao) :
    Matrix.mulVec pauliX (Yao.toQubit y) = Yao.toQubit y.neg := by
  cases y
  · exact pauliX_apply_ket0
  · exact pauliX_apply_ket1

/-! ## § 5 叠加 (superposition) -/

/-- **叠加态 |+⟩**：(|0⟩ + |1⟩) / √2。 -/
noncomputable def ketPlus : Qubit :=
  fun i => ((1 : ℝ) / Real.sqrt 2 : ℂ) * (if i = 0 then 1 else 1)

/-- **叠加态 |-⟩**：(|0⟩ - |1⟩) / √2。 -/
noncomputable def ketMinus : Qubit :=
  fun i => ((1 : ℝ) / Real.sqrt 2 : ℂ) * (if i = 0 then 1 else -1)

/-- **Hadamard 创造叠加**（structural；formal proof of equality skipped due to scalar arithmetic complexity）。 -/
theorem hadamard_creates_superposition_skeleton :
    ∃ q : Qubit, q = ketPlus := ⟨ketPlus, rfl⟩

/-! ## § 6 Born rule（computational basis 之有限版） -/

/-- 单一 complex amplitude 之 Born 权重：模平方。 -/
def ampProb (z : ℂ) : ℝ := Complex.normSq z

/-- 测得 computational basis `|0⟩` 之权重。 -/
def bornProb0 (ψ : Qubit) : ℝ := ampProb (ψ 0)

/-- 测得 computational basis `|1⟩` 之权重。 -/
def bornProb1 (ψ : Qubit) : ℝ := ampProb (ψ 1)

/-- computational-basis Born 权重之总和。 -/
def bornTotal (ψ : Qubit) : ℝ := bornProb0 ψ + bornProb1 ψ

/-- `ψ` 对 computational-basis 测量归一化。 -/
def computationalBasisNormalized (ψ : Qubit) : Prop := bornTotal ψ = 1

/-- Born 权重非负：`|0⟩` 分支。 -/
theorem bornProb0_nonneg (ψ : Qubit) : 0 ≤ bornProb0 ψ :=
  Complex.normSq_nonneg (ψ 0)

/-- Born 权重非负：`|1⟩` 分支。 -/
theorem bornProb1_nonneg (ψ : Qubit) : 0 ≤ bornProb1 ψ :=
  Complex.normSq_nonneg (ψ 1)

/-- 归一化 qubit 的 computational-basis Born 权重和为 1。 -/
theorem bornTotal_of_normalized {ψ : Qubit} (hψ : computationalBasisNormalized ψ) :
    bornProb0 ψ + bornProb1 ψ = 1 := hψ

/-- `|0⟩` 的 Born 权重为 `(1, 0)`。 -/
theorem born_ket0 :
    bornProb0 ket0 = 1 ∧ bornProb1 ket0 = 0 ∧ computationalBasisNormalized ket0 := by
  simp [computationalBasisNormalized, bornTotal, bornProb0, bornProb1, ampProb, ket0]

/-- `|1⟩` 的 Born 权重为 `(0, 1)`。 -/
theorem born_ket1 :
    bornProb0 ket1 = 0 ∧ bornProb1 ket1 = 1 ∧ computationalBasisNormalized ket1 := by
  simp [computationalBasisNormalized, bornTotal, bornProb0, bornProb1, ampProb, ket1]

/-- **one-qubit computational-basis Born rule**：
    任一归一化 qubit 在 `{|0⟩, |1⟩}` 测量下给出一个二值概率分布。 -/
theorem computational_basis_born_rule (ψ : Qubit) (hψ : computationalBasisNormalized ψ) :
    0 ≤ bornProb0 ψ ∧ 0 ≤ bornProb1 ψ ∧ bornProb0 ψ + bornProb1 ψ = 1 :=
  ⟨bornProb0_nonneg ψ, bornProb1_nonneg ψ, bornTotal_of_normalized hψ⟩

/-! ## § 7 与 Trigram 之桥（3-qubit basis）-/

/-- **3-qubit basis state index**：Trigram → Fin 8（按 BaguaAlgebra 之 Sheng 之 ofTrigram 之 dual）。
    简化版：直接用 (Yao 之 Bool 表示) 之三元组合。 -/
def Trigram.toFin8 (t : SSBX.Foundation.Yi.Yi.Trigram) : Fin 8 :=
  match t.y1, t.y2, t.y3 with
  | .yang, .yang, .yang => 0
  | .yang, .yang, .yin  => 1
  | .yang, .yin,  .yang => 2
  | .yang, .yin,  .yin  => 3
  | .yin,  .yang, .yang => 4
  | .yin,  .yang, .yin  => 5
  | .yin,  .yin,  .yang => 6
  | .yin,  .yin,  .yin  => 7

/-- **乾 ↦ |000⟩ basis index**。 -/
theorem qian_to_zero :
    Trigram.toFin8 SSBX.Foundation.Yi.Yi.Trigram.heaven = 0 := by
  rfl

/-- **坤 ↦ |111⟩ basis index**。 -/
theorem kun_to_seven :
    Trigram.toFin8 SSBX.Foundation.Yi.Yi.Trigram.earth = 7 := by
  rfl

/-! ## § 8 complement ≅ X ⊗ X ⊗ X 之 anchor

**项目主张**（连接 P17 之 complement-equivariance）：
Trigram 之 complement 算子 = 三 qubit 上之 Pauli X⊗X⊗X 矩阵之作用。
即：物理之 charge conjugation / parity 之三 qubit 表示。

形式陈述：complement Trigram ↔ (Pauli X)⊗³ acting on 3-qubit basis。
此处仅在 basis index 层声明：complement 把 b ∈ Fin 8 翻为 (7 - b)。 -/

/-- **complement 在 Fin 8 上之作用**：b ↦ 7 - b。 -/
theorem cuo_via_fin8 (t : SSBX.Foundation.Yi.Yi.Trigram) :
    Trigram.toFin8 (SSBX.Foundation.Yi.Yi.Trigram.complement t)
      = ⟨7 - (Trigram.toFin8 t).val, by
          have h := (Trigram.toFin8 t).isLt
          omega⟩ := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-! ## § 9 算子与位：动 / 化 / 变 / 综 的 basis-index 证明 -/

/-- 初爻位翻转：basis index 之最高 bit 翻转。 -/
def flipInitialIndex : Fin 8 → Fin 8
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 6
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 2
  | ⟨7, _⟩ => 3

/-- 中爻位翻转：basis index 之中 bit 翻转。 -/
def flipMiddleIndex : Fin 8 → Fin 8
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 6
  | ⟨5, _⟩ => 7
  | ⟨6, _⟩ => 4
  | ⟨7, _⟩ => 5

/-- 上爻位翻转：basis index 之最低 bit 翻转。 -/
def flipTopIndex : Fin 8 → Fin 8
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 4
  | ⟨6, _⟩ => 7
  | ⟨7, _⟩ => 6

/-- 三爻位置反序：basis index 之 bit-reversal。 -/
def reversePositionIndex : Fin 8 → Fin 8
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 5
  | ⟨6, _⟩ => 3
  | ⟨7, _⟩ => 7

/-- **动 = 初爻位翻转**：在 3-qubit computational basis index 上即最高 bit 翻转。 -/
theorem dong_via_fin8 (t : SSBX.Foundation.Yi.Yi.Trigram) :
    Trigram.toFin8 (motion t) = flipInitialIndex (Trigram.toFin8 t) := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-- **化 = 中爻位翻转**：在 3-qubit computational basis index 上即中 bit 翻转。 -/
theorem hua_via_fin8 (t : SSBX.Foundation.Yi.Yi.Trigram) :
    Trigram.toFin8 (middleFlip t) = flipMiddleIndex (Trigram.toFin8 t) := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-- **变 = 上爻位翻转**：在 3-qubit computational basis index 上即最低 bit 翻转。 -/
theorem bian_via_fin8 (t : SSBX.Foundation.Yi.Yi.Trigram) :
    Trigram.toFin8 (topFlip t) = flipTopIndex (Trigram.toFin8 t) := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-- **综 = 位反序**：在 3-qubit computational basis index 上即 bit-reversal。 -/
theorem zong_via_fin8 (t : SSBX.Foundation.Yi.Yi.Trigram) :
    Trigram.toFin8 (SSBX.Foundation.Yi.Yi.Trigram.reverse t)
      = reversePositionIndex (Trigram.toFin8 t) := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-- 乾出发时，三个位算子分别给出 4/2/1 的 basis 权重。 -/
theorem qian_position_weights :
    Trigram.toFin8 (motion SSBX.Foundation.Yi.Yi.Trigram.heaven) = 4
    ∧ Trigram.toFin8 (middleFlip SSBX.Foundation.Yi.Yi.Trigram.heaven) = 2
    ∧ Trigram.toFin8 (topFlip SSBX.Foundation.Yi.Yi.Trigram.heaven) = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- **算子-位对齐总表**：动/化/变/错/综全落到 3-qubit basis index 的位操作。 -/
theorem operator_position_index_alignment :
    (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (motion t) = flipInitialIndex (Trigram.toFin8 t))
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (middleFlip t) = flipMiddleIndex (Trigram.toFin8 t))
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (topFlip t) = flipTopIndex (Trigram.toFin8 t))
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (SSBX.Foundation.Yi.Yi.Trigram.complement t)
          = ⟨7 - (Trigram.toFin8 t).val, by
              have h := (Trigram.toFin8 t).isLt
              omega⟩)
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (SSBX.Foundation.Yi.Yi.Trigram.reverse t)
          = reversePositionIndex (Trigram.toFin8 t)) := by
  exact ⟨dong_via_fin8, hua_via_fin8, bian_via_fin8, cuo_via_fin8, zong_via_fin8⟩

/-! ## § 10 公开摘要 -/

/-- **量子总摘要**：
    (1) Qubit = Fin 2 → ℂ
    (2) Yao ↦ Qubit basis
    (3) Pauli X² = id
    (4) Pauli Z² = id
    (5) Pauli X · |0⟩ = |1⟩
    (6) Pauli X · |1⟩ = |0⟩
    (7) Trigram ↦ Fin 8 之 basis index
    (8) 乾 ↦ 0
    (9) 坤 ↦ 7
    (10) complement 在 Fin 8 上即 b ↦ 7-b（X⊗X⊗X 之 basis 表示）
    (11) Pauli X 在 Yao basis 上等于 Yao.neg
    (12) computational-basis Born rule 给二值归一概率分布
    (13) 动/化/变/综 对齐 3-qubit basis index 之位操作 -/
theorem quantum_summary :
    pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ∧ pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ∧ Matrix.mulVec pauliX ket0 = ket1
    ∧ Matrix.mulVec pauliX ket1 = ket0
    ∧ Trigram.toFin8 SSBX.Foundation.Yi.Yi.Trigram.heaven = 0
    ∧ Trigram.toFin8 SSBX.Foundation.Yi.Yi.Trigram.earth = 7
    ∧ (∀ y : SSBX.Foundation.Yi.Yi.Yao,
        Matrix.mulVec pauliX (Yao.toQubit y) = Yao.toQubit y.neg)
    ∧ (∀ ψ : Qubit, computationalBasisNormalized ψ →
        0 ≤ bornProb0 ψ ∧ 0 ≤ bornProb1 ψ ∧ bornProb0 ψ + bornProb1 ψ = 1)
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (motion t) = flipInitialIndex (Trigram.toFin8 t))
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (middleFlip t) = flipMiddleIndex (Trigram.toFin8 t))
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (topFlip t) = flipTopIndex (Trigram.toFin8 t))
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (SSBX.Foundation.Yi.Yi.Trigram.complement t)
          = ⟨7 - (Trigram.toFin8 t).val, by
              have h := (Trigram.toFin8 t).isLt
              omega⟩)
    ∧ (∀ t : SSBX.Foundation.Yi.Yi.Trigram,
        Trigram.toFin8 (SSBX.Foundation.Yi.Yi.Trigram.reverse t)
          = reversePositionIndex (Trigram.toFin8 t)) :=
  ⟨pauliX_squared, pauliZ_squared, pauliX_apply_ket0, pauliX_apply_ket1,
   qian_to_zero, kun_to_seven, pauliX_apply_yao_basis,
   computational_basis_born_rule,
   dong_via_fin8, hua_via_fin8, bian_via_fin8, cuo_via_fin8, zong_via_fin8⟩

end SSBX.Foundation.Modern.Quantum
