/-
# KleeneCarrier — 显式分解 Kleene 递归公理

本文件取代原 `GodelLi.lean` 中 monolithic `axiom kleene_recursion_axiom :
KleeneInverter` 之公理化捕获.  按 `KleeneInternal.path_to_zero_axiom` 之
精确分解，列出四件原本被打包进单一公理之独立工程目标，每件作为一条具名
原子公理；然后用 `path_to_zero_axiom` 将 `KleeneInverter` 派生为
**定理**（不再是公理）。

## 公理分解（与 `KleeneInternal.path_to_zero_axiom` 一一对应）

| 公理                          | 性质         | 去除路径                            |
|-------------------------------|--------------|-------------------------------------|
| `universalInterpExists`       | 工程         | ~ 700 行 YiInstr U（§6b 已 ≈ 15%） |
| `smnExists`                   | 工程         | ~ 50 行 cell-pushing 子程序         |
| `kleeneFromPrimitives`        | 工程         | ~ 100 行对角构造                    |
| `allDecidersAreYiComputable`  | **元公理**   | Church-Turing 论题 (cuo-限定)       |

前三件皆为 YiInstr 内可显式实现之工程目标（参见 `KleeneInternal.lean`
之 spec），第四件为 Church-Turing 论题之 Lean 形式：每个 cuo-不变 Lean
Bool 判定器皆为 YiComputable.  此最后一件**不可在 Lean 内消除**（Lean
之 Classical 可造非可计算 Bool 函数），是 道-理二分 之精确公理化捕获。

## 与原 `kleene_recursion_axiom` 之关系

派生定理 `kleene_recursion : KleeneInverter` 与原公理在使用上完全等价：
所有依赖 `KleeneInverter` 之下游不可判定结果（Halts 不可判 / Rice 四象 /
Rice uniform / 道判机不可通用化）皆从此派生。

净效果：1 个 monolithic 公理 → 4 个原子公理（其中 3 个是工程债，1 个
为 Church-Turing 元公理）。axiom count 上升，但 axiom **scope** 大幅
收窄、各债项**独立可削减**。
-/
import SSBX.Foundation.Bagua.KleeneInternal

namespace SSBX.Foundation.Bagua.KleeneCarrier

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.GodelLi
open SSBX.Foundation.Bagua.KleeneInternal

/-! ## § 1 四件原子公理 -/

/-- **公理 1/4 — 通用解释器存在性**.

    `∃ U : List YiInstr, ∀ P h, Halts P h ↔ HaltsWith U h (encProg P)`.

    `WenyanSelfInterp § 6b` 之 metaInterpProg 当前覆盖 nop + halt（≈ 15%）；
    余 12 路 dispatch + 11 个 execute blocks + fetch + writeback 之机械
    工程，约 700 行 Lean.  无需新 Mathlib，无需 axiom；纯 YiInstr 内的
    可执行构造 + 模拟引理。 -/
axiom universalInterpExists : UniversalInterpExists

/-- **公理 2/4 — s-m-n 特化编译器存在性**.

    `∃ subst : List YiInstr → List Cell192 → List YiInstr,
       ∀ P input h, HaltsWith P h input ↔ Halts (subst P input) h`.

    朴素实现 `subst P input := pushList input ++ P` 不可直接表达，因
    YiInstr 之 push 推 `cur` 而非任意 cell（无 `pushLiteral`）。需
    或引入 ISA 扩展指令、或用一段长度 ≈ 50 之"运行时 cur 构造"前缀
    （6 yao 翻 + setShi + push）。 -/
axiom smnExists : SmnExists

/-- **公理 3/4 — Kleene 对角构造**.

    `KleeneFromPrimitives := KleeneFixedPointFromPrimitives ∧
                              BoolInverterCompilerFromUniversal`.

    标准递归定理之 BaguaTuring 形：从通用解释器 + s-m-n 派生
    `KleeneFixedPointExists` 与 `BoolInverterCompilerExists`（Bool 输出
    反转编译器）。约 100 行 Lean，依赖 #1 + #2 之具体见证。 -/
axiom kleeneFromPrimitives : KleeneFromPrimitives

/-- **公理 4/4 — Cuo-限定 Church-Turing 论题**.

    `∀ decide : List YiInstr → Hexagram → Bool, CuoInvariantDecide decide →
       YiComputable decide`.

    每个 cuo-不变 Lean Bool 判定器皆可由某 YiInstr 程序实现.  此件
    **不可在 Lean 内消除**：Lean 之 Classical.choice 可造非可计算
    Bool 函数，故"所有 Lean Bool 函数皆 YiComputable"在 Lean 内非定理。
    此即 Church-Turing 论题之精确 Lean 形式，也是道-理二分中"道认可
    理之 CT 论题"之公理化落位。 -/
axiom allDecidersAreYiComputable : AllDecidersAreYiComputable

/-! ## § 2 派生：`kleene_recursion : KleeneInverter` 不再是公理

由 `KleeneInternal.path_to_zero_axiom` 直接拼装四件原子公理。 -/

/-- **`KleeneInverter` 之派生定理**.  原 `GodelLi.kleene_recursion_axiom`
    之等价物，现以四原子公理之合集替代单一公理. -/
theorem kleene_recursion : KleeneInverter :=
  path_to_zero_axiom universalInterpExists smnExists
                     kleeneFromPrimitives allDecidersAreYiComputable

/-! ## § 3 下游不可判定结果之无条件版本

每个定理皆从 `_under_kleene` 之条件版定理（位于 `GodelLi.lean`，0 axiom）
+ `kleene_recursion` 派生.  与原 `GodelLi` 中之同名定理在断言上完全一致。 -/

/-! ### § 3.1 Halts 主不可判 -/

/-- **理之不完备主定理**（无条件版）：Halts 不可由任何 Lean Bool 函数判定. -/
theorem halts_undecidable_internally :
    ¬ ∃ decide : List YiInstr → Hexagram → Bool,
        ∀ P h, decide P h = true ↔ Halts P h :=
  halts_undecidable_under_kleene kleene_recursion

/-- **¬Halts 亦不可判**（无条件版）. -/
theorem not_halts_undecidable :
    ¬ ∃ decide : List YiInstr → Hexagram → Bool,
        ∀ P h, decide P h = true ↔ ¬ Halts P h :=
  not_halts_undecidable_under_kleene kleene_recursion

/-- **任意固定 h 之 Halts 不可判**（无条件版）. -/
theorem halts_at_fixed_undecidable (h₀ : Hexagram) :
    ¬ ∃ decide : List YiInstr → Bool,
        ∀ P, decide P = true ↔ Halts P h₀ :=
  halts_at_fixed_undecidable_under_kleene kleene_recursion h₀

/-! ### § 3.2 Rice 四象（无条件版） -/

/-- **Π_some 不可判**（无条件版）. -/
theorem halts_on_some_undecidable :
    ¬ ∃ decide_some : List YiInstr → Bool,
        ∀ P, decide_some P = true ↔ ∃ h, Halts P h :=
  halts_on_some_undecidable_under_kleene kleene_recursion

/-- **Π_none 不可判**（无条件版）. -/
theorem halts_on_none_undecidable :
    ¬ ∃ decide_none : List YiInstr → Bool,
        ∀ P, decide_none P = true ↔ ∀ h, ¬ Halts P h :=
  halts_on_none_undecidable_under_kleene kleene_recursion

/-- **Π_all 不可判**（无条件版）. -/
theorem halts_on_all_undecidable :
    ¬ ∃ decide_all : List YiInstr → Bool,
        ∀ P, decide_all P = true ↔ ∀ h, Halts P h :=
  halts_on_all_undecidable_under_kleene kleene_recursion

/-- **Π_some_no 不可判**（无条件版）. -/
theorem halts_on_some_no_undecidable :
    ¬ ∃ decide_some_no : List YiInstr → Bool,
        ∀ P, decide_some_no P = true ↔ ∃ h, ¬ Halts P h :=
  halts_on_some_no_undecidable_under_kleene kleene_recursion

/-- **Rice 四象总定理**（无条件版）. -/
theorem rice_four_images :
    (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∀ h, Halts P h)
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∃ h, Halts P h)
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∃ h, ¬ Halts P h)
    ∧ (¬ ∃ d : List YiInstr → Bool, ∀ P, d P = true ↔ ∀ h, ¬ Halts P h) :=
  rice_four_images_under_kleene kleene_recursion

/-! ### § 3.3 Rice uniform + 道判机不可通用化 -/

/-- **Rice uniform**（无条件版）：任何区分 ∅/univ profile 之外延性质皆不可判. -/
theorem rice_uniform
    (Phi : (Hexagram → Prop) → Bool)
    (h_dist : Phi (fun _ => True) ≠ Phi (fun _ => False)) :
    ¬ ∃ decide_Phi : List YiInstr → Bool,
        ∀ P, decide_Phi P = true ↔ Phi (Halts P) = true :=
  rice_uniform_under_kleene kleene_recursion Phi h_dist

/-- **道判机不可通用化**（无条件版，Shi.ji 版）. -/
theorem daoJudge_not_universal :
    ¬ ∃ enc : List YiInstr → Hexagram → Hexagram,
        ∀ P h, daoJudge (enc P h) = Shi.ji ↔ Halts P h :=
  daoJudge_not_universal_under_kleene kleene_recursion

/-- **道判机不可通用化**（无条件版，Shi.wei 对偶版）. -/
theorem daoJudge_wei_not_universal :
    ¬ ∃ enc : List YiInstr → Hexagram → Hexagram,
        ∀ P h, daoJudge (enc P h) = Shi.wei ↔ Halts P h :=
  daoJudge_wei_not_universal_under_kleene kleene_recursion

/-! ## § 4 兼容别名

为保持向后兼容性：原 `GodelLi.kleene_recursion_axiom` 之名以 deprecated
alias 暴露于此. -/

/-- 兼容别名：原 `GodelLi.kleene_recursion_axiom` 之等价物。新代码请用
    `kleene_recursion`（已派生为定理，不再是公理）。 -/
@[deprecated kleene_recursion (since := "2026-05-08")]
theorem kleene_recursion_axiom : KleeneInverter := kleene_recursion

end SSBX.Foundation.Bagua.KleeneCarrier
