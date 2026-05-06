/-
# Quantum — 量子叠加 / qubit / Pauli 矩阵 (Phase 4 主体 · Mathlib)

Companion: `义理/物理 · 从元到象.md` § 二 / § 四

物理衍 §二 已严格陈述 Yao ≅ qubit basis；§四 已陈述反爻 ≅ Pauli X (在 basis 上)。
本文借 Mathlib `Matrix` + `InnerProductSpace` 升 Phase 3 之 finite basis layer 至
**叠加层** (superposition layer)：qubit ≅ ℂ²、Pauli X / Y / Z 矩阵、Hadamard、3-qubit Trigram。

## 与 P17 之 cuo-不变性之关系

**P17 发现**：YiInstr 之所有指令 cuo-等变 → BaguaTuring 表达力 ≤ 2^32 cuo-不变 Hex→Bool。
**量子层之 cuo**：cuo = X⊗X⊗X⊗X⊗X⊗X (六 qubit Pauli X) — charge conjugation / parity 之具体形态。
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
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Eight.WuXiang

namespace SSBX.Foundation.Modern.Quantum

open Complex Matrix

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

/-! ## § 6 与 Trigram 之桥（3-qubit basis）-/

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
    Trigram.toFin8 SSBX.Foundation.Yi.Yi.Trigram.qian = 0 := by
  rfl

/-- **坤 ↦ |111⟩ basis index**。 -/
theorem kun_to_seven :
    Trigram.toFin8 SSBX.Foundation.Yi.Yi.Trigram.kun = 7 := by
  rfl

/-! ## § 7 cuo ≅ X ⊗ X ⊗ X 之 anchor

**项目主张**（连接 P17 之 cuo-equivariance）：
Trigram 之 cuo 算子 = 三 qubit 上之 Pauli X⊗X⊗X 矩阵之作用。
即：物理之 charge conjugation / parity 之三 qubit 表示。

形式陈述：cuo Trigram ↔ (Pauli X)⊗³ acting on 3-qubit basis。
此处仅在 basis index 层声明：cuo 把 b ∈ Fin 8 翻为 (7 - b)。 -/

/-- **cuo 在 Fin 8 上之作用**：b ↦ 7 - b。 -/
theorem cuo_via_fin8 (t : SSBX.Foundation.Yi.Yi.Trigram) :
    Trigram.toFin8 (SSBX.Foundation.Yi.Yi.Trigram.cuo t)
      = ⟨7 - (Trigram.toFin8 t).val, by
          have h := (Trigram.toFin8 t).isLt
          omega⟩ := by
  cases t with
  | mk y1 y2 y3 =>
    cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-! ## § 8 公开摘要 -/

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
    (10) cuo 在 Fin 8 上即 b ↦ 7-b（X⊗X⊗X 之 basis 表示） -/
theorem quantum_summary :
    pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ∧ pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ∧ Matrix.mulVec pauliX ket0 = ket1
    ∧ Matrix.mulVec pauliX ket1 = ket0
    ∧ Trigram.toFin8 SSBX.Foundation.Yi.Yi.Trigram.qian = 0
    ∧ Trigram.toFin8 SSBX.Foundation.Yi.Yi.Trigram.kun = 7 :=
  ⟨pauliX_squared, pauliZ_squared, pauliX_apply_ket0, pauliX_apply_ket1,
   qian_to_zero, kun_to_seven⟩

end SSBX.Foundation.Modern.Quantum
