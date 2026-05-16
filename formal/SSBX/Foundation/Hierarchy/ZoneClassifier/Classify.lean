/-
# Foundation.Hierarchy.ZoneClassifier.Classify — 主分类函数

## 收紧 (第二轮)

- 删除 `encodesSheng` stub —— 墙是 op 之结构事实，非 cell 性质
- `detectWalls` 签名改为 `(op : OperatorTag) → (n : Nat) → List WallWitness`
  (cell-independent)；每个 op→walls 之映射有 docstring 之 structural 理由
- 阈值 `n < 8` 替换为 `op.applicable n`：不适用档 → ke_li（升档可决）；
  适用档但其余路径未命中 → li_conditional（需前提）

## 优先级阶梯之派生说明

  classify 之 if-else 阶梯输出**所有可激活 zone 中 level 最小者**
  （level 见 Operators.lean § 4 之 `Zone.level`）。这对应"最强证据胜出"原则：

  - dao_axiom (level 0) 优先 dao_dynamic (level 1)：静态不动点是更强结构事实
  - dao_dynamic 优先 wall (level 4)：「生生不息」之轨道见证比墙更具体
  - wall 优先 li/ke_li (level 2/3)：有具体墙引用即不需 fallback

## detectWalls 之 op→walls 映射 (structural rationale)

  | op                    | walls                  | 结构理由 |
  |-----------------------|------------------------|----------|
  | cuo_complement (任意 n) | [cuoFail]              | `cuo_not_truth_preserving` 之 universal claim |
  | zong_reverse  (任意 n) | [zongFail]             | `zong_not_truth_preserving` 之 universal claim |
  | hu_interlace  (任意 n) | [huFixed]              | `hu_fixed_point` 之 "仅 2 个不动点" structural cap |
  | isa_12 @ n=8          | [sheng]                | `sheng_not_cuo_equivariant` 之 12-ISA ceiling |
  | isa_12 @ n≠8          | []                     | 该 op 在该档不适用 |
  | 其他                   | []                     | 当前无 structural wall 引用 |
-/

import SSBX.Foundation.Hierarchy.ZoneClassifier.Types
import SSBX.Foundation.Hierarchy.ZoneClassifier.Operators
import SSBX.Foundation.Hierarchy.ZoneClassifier.Axes
import SSBX.Foundation.Hierarchy.ZoneClassifier.WallCitations

namespace SSBX.Foundation.Hierarchy.ZoneClassifier

open SSBX.Foundation.Wen.Layered

/-! ## § 1  detectWalls — cell-independent op→walls 映射 -/

/-- 由 (op, n) 推墙列表；与 cell 无关。每条映射对应 docstring 表里的
    结构理由，引用 WallCitations 中的 cited_* 定理。 -/
def detectWalls (op : OperatorTag) (n : Nat) : List WallWitness :=
  match op, n with
  | .cuo_complement, _ => [WallWitness.cuoFail]
  | .zong_reverse,   _ => [WallWitness.zongFail]
  | .hu_interlace,   _ => [WallWitness.huFixed]
  | .isa_12,         8 => [WallWitness.sheng]
  | _,               _ => []

/-! ## § 2  classify — 主分类函数 -/

/-- 主分类函数。5 步优先级阶梯，每步派生说明见文件 docstring。 -/
def classify {n : Nat} (c : BitSpace n) (op : OperatorTag) : Classification n :=
  -- Step 1: 静态不动点 (R_n 内禀有限计算)
  let isFixed : Bool := decide (op.applyUnary n c = c)
  -- Step 2: yiCore_step + n = 6 → 由 «生生不息» 派生 (见 Subsets.dao_via_shengshengbuxi)
  let isShengsheng : Bool :=
    match op with
    | .yiCore_step => decide (n = 6)
    | _            => false
  -- Step 3: 墙检测（与 cell 无关）
  let walls := detectWalls op n
  -- 阈值由 op.applicable n 派生（非全局 n<8 硬编码）
  let zone : Zone :=
    if isFixed then .dao_axiom
    else if isShengsheng then .dao_dynamic
    else if !walls.isEmpty then .wall
    else if !op.applicable n then .ke_li
    else .li_conditional
  { cell := c
  , opTag := op
  , zone := zone
  , shi := extractShi n c
  , walls := walls }

/-! ## § 3  classify 之关键不变量 -/

/-- 静态不动点 → dao_axiom。 -/
theorem classify_zone_fixed {n : Nat} (c : BitSpace n) (op : OperatorTag)
    (h : op.applyUnary n c = c) :
    (classify c op).zone = .dao_axiom := by
  simp [classify, h]

/-- yiCore_step at n = 6 + 非不动点 → dao_dynamic。
    真之来源为 `«生生不息»`（见 Subsets.dao_via_shengshengbuxi 中之引用）。 -/
theorem classify_zone_yiCore_dao_dynamic (c : BitSpace 6)
    (h_not_fixed : OperatorTag.yiCore_step.applyUnary 6 c ≠ c) :
    (classify c .yiCore_step).zone = .dao_dynamic := by
  simp [classify, h_not_fixed]

end SSBX.Foundation.Hierarchy.ZoneClassifier
