/-
# SoundnessProbe — 探针：原 `KleeneInverter`（cuo-限定）能否在 Lean 内导出 False？

诊断文件，不进 SSBX.lean 主导入树。

## 问题

原 `kleene_recursion_axiom : KleeneInverter` 之 cuo-限定形：

```
KleeneInverter := ∀ decide, CuoInvariantDecide decide →
                   ∃ D, ∀ h, Halts D h ↔ decide D h = false
```

设以 Classical 之 propDecidable 取
`decide := fun P h => Decidable.decide (Halts P h)`：

1. 此 decide 之类型为 `List YiInstr → Hexagram → Bool` ✓
2. 由 `halts_cuo_invariant`，`Halts P h ↔ Halts P h.cuo`，故
   `decide P h = decide P h.cuo`，即 cuo-不变 ✓
3. KleeneInverter 应给 `D` 与 `Halts D h ↔ decide D h = false`
4. 但 `decide D h = false ↔ ¬ Halts D h`（propDecidable 之定义）
5. 故 `Halts D h ↔ ¬ Halts D h` ——逻辑矛盾

**结论**：cuo-限定不足以拯救 `KleeneInverter`——只要 Lean 之 Classical
可造 cuo-不变之 Bool 判定器（如 `decide (Halts P h)`），axiom 就不一致。
-/
import SSBX.Foundation.Bagua.KleeneCarrier

namespace SSBX.Foundation.Bagua.SoundnessProbe

open Classical
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.GodelLi
open SSBX.Foundation.Bagua.KleeneCarrier

/-- Classical 构造之 Halts 判定器（noncomputable，但是合法 Lean term）. -/
noncomputable def classical_halts_decide : List YiInstr → Hexagram → Bool :=
  fun P h => Decidable.decide (Halts P h)

/-- 此判定器满足规格：true ↔ Halts. -/
theorem classical_halts_decide_spec (P : List YiInstr) (h : Hexagram) :
    classical_halts_decide P h = true ↔ Halts P h := by
  unfold classical_halts_decide
  exact decide_eq_true_iff

/-- 此判定器是 cuo-不变的（继承自 Halts 之 cuo-不变性）. -/
theorem classical_halts_decide_cuoInvariant :
    CuoInvariantDecide classical_halts_decide := by
  intro P h
  unfold classical_halts_decide
  have h_iff : Halts P h ↔ Halts P h.cuo := halts_cuo_invariant P h
  by_cases h_halts : Halts P h
  · have h_cuo_halts : Halts P h.cuo := h_iff.mp h_halts
    rw [decide_eq_true h_halts, decide_eq_true h_cuo_halts]
  · have h_cuo_no_halts : ¬ Halts P h.cuo := fun hh => h_halts (h_iff.mpr hh)
    rw [decide_eq_false h_halts, decide_eq_false h_cuo_no_halts]

/-- **致命探针**：从 `kleene_recursion`（即原 `kleene_recursion_axiom`）+ Classical
    导出 `False`. -/
theorem kleene_recursion_inconsistent : False := by
  obtain ⟨D, hD⟩ := kleene_recursion classical_halts_decide
    classical_halts_decide_cuoInvariant
  -- hD : ∀ h, Halts D h ↔ classical_halts_decide D h = false
  have h_iff : Halts D Hexagram.qian ↔
                classical_halts_decide D Hexagram.qian = false :=
    hD Hexagram.qian
  -- decide_eq_false 与 Halts 之关系
  by_cases h_halts : Halts D Hexagram.qian
  · -- Halts → decide = false → ¬Halts，矛盾
    have h_dec_false : classical_halts_decide D Hexagram.qian = false :=
      h_iff.mp h_halts
    have h_dec_true : classical_halts_decide D Hexagram.qian = true :=
      (classical_halts_decide_spec D Hexagram.qian).mpr h_halts
    rw [h_dec_true] at h_dec_false
    exact Bool.noConfusion h_dec_false
  · -- ¬Halts → decide = false → Halts，矛盾
    have h_dec_false : classical_halts_decide D Hexagram.qian = false := by
      unfold classical_halts_decide
      exact decide_eq_false h_halts
    have h_should_halt : Halts D Hexagram.qian := h_iff.mpr h_dec_false
    exact h_halts h_should_halt

end SSBX.Foundation.Bagua.SoundnessProbe
