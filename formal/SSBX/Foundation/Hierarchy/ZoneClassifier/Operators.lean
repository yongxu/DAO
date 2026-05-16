/-
# Foundation.Hierarchy.ZoneClassifier.Operators — 算子目录与应用

每个 `OperatorTag` 提供 `apply` (binary) 与 `applyUnary` (unary) 的 total
实现；超出适用 n 的回退到 identity。`composeZone` 是 5×5 表的 decidable
function (墙吸收原则)。

## 证据流

本文件 只提供**有限计算**层的算子实现：所有 `apply` 都是 `BitSpace n` 上的
有限位运算 (XOR / 否定 / 恒等)，是 R_n 内禀的可计算性，不引入新的真值断言。
对超档算子的 fallback 一律走 identity，不冒充其实意义。
-/

import SSBX.Foundation.Hierarchy.ZoneClassifier.Types
import SSBX.Foundation.Atlas.Yi.YiCore
import SSBX.Foundation.Atlas.Yi.Operators

namespace SSBX.Foundation.Hierarchy.ZoneClassifier

open SSBX.Foundation.Wen.Layered

/-! ## § 0  类型等同：Hexagram = BitSpace 6

  `Hexagram = R 6 = Fin 6 → Bool = Slot 6 → Bool = BitSpace 6`
  —— 经 `abbrev` 链定义性相等。故 `yiCore_step` 的 `applyUnary` 在 n=6 时
  可直接调用 `«生» : Hexagram → Hexagram`，无须显式 bridge。这是证据流
  在类型层的体现：道运动直接落在 R₆ 载体上。 -/

/-! ## § 1  applicable — 算子在哪些 n 上"有意义" -/

/-- 算子是否在 `BitSpace n` 上有结构意义。超出此域的回退到 identity。 -/
def OperatorTag.applicable : OperatorTag → Nat → Bool
  | .yiCore_step,    n => decide (n = 6)
  | .v4_compose,     n => decide (n % 2 = 0)
  | .cayley_mul,     n => decide (n = 8)
  | .yin_mask,       n => decide (n = 8)
  | .tou_mask,       n => decide (n = 8)
  | .isa_12,         n => decide (n = 8)
  | .hu_interlace,   n => decide (n = 6)
  | .zong_reverse,   n => decide (n = 6)
  | .cuo_complement, _ => true
  | .identity_op,    _ => true

/-! ## § 2  applyUnary — 一元应用 -/

/-- 比特取反 (`错`)：将所有比特按位取反。 -/
def bitNot {n : Nat} (c : BitSpace n) : BitSpace n :=
  fun i => !(c i)

/-! ### 一元行动 — 消灭"空洞 dao_axiom"原则

  每个 OperatorTag 在 `applyUnary` 下都对应一个**结构性非平凡的**一元映射；
  fallback `identity` 已被消灭。这样 `dao_axiom(op) = {c | op.applyUnary n c = c}`
  始终是真实子集（非平凡完整），与算子的结构语义直接对应。

  | op                | applyUnary               | dao_axiom                          | 派生 |
  |-------------------|--------------------------|------------------------------------|------|
  | identity_op       | c                        | univ                               | 平凡 |
  | cuo_complement    | bitNot c                 | ∅                                  | 错无不动点 |
  | v4_compose        | c ⊕ c = 0                | {0}                                | V₄ identity |
  | cayley_mul        | c ⊕ c = 0                | {0}                                | Cayley identity |
  | yin_mask          | c ⊕ c = 0                | {0}                                | 印 之原点 |
  | tou_mask          | c ⊕ c = 0                | {0}                                | 投 之原点 |
  | isa_12            | bitNot c (cuo)           | ∅                                  | 12-ISA 之代表非平凡动作 |
  | yiCore_step @ 6   | «生» c                   | ∅                                  | sheng_no_fixed_point |
  | yiCore_step @ ≠6  | bitNot c                 | ∅                                  | 不适用档之 sentinel |
  | hu_interlace @ 6  | hu c                     | {qianqian, kunkun}                 | hu_fixed_point |
  | hu_interlace @ ≠6 | bitNot c                 | ∅                                  | sentinel |
  | zong_reverse @ 6  | zong c                   | zong-对称卦集                       | zong-fixed |
  | zong_reverse @ ≠6 | bitNot c                 | ∅                                  | sentinel |

  原则：能算子自身结构给出的不动点用之；否则用 `bitNot`（无不动点）作 sentinel，
  让超档调用得到空 dao_axiom，而非虚假全集。 -/
def OperatorTag.applyUnary : (op : OperatorTag) → (n : Nat) → BitSpace n → BitSpace n
  | .identity_op,    _, c => c
  | .cuo_complement, _, c => bitNot c
  | .v4_compose,     _, c => BitSpace.xor c c
  | .cayley_mul,     _, c => BitSpace.xor c c
  | .yin_mask,       _, c => BitSpace.xor c c
  | .tou_mask,       _, c => BitSpace.xor c c
  | .isa_12,         _, c => bitNot c
  | .yiCore_step,    6, c => SSBX.Foundation.Atlas.Yi.YiCore.«生» c
  | .yiCore_step,    _, c => bitNot c
  | .hu_interlace,   6, c => SSBX.Foundation.Atlas.Yi.Hexagram.hu c
  | .hu_interlace,   _, c => bitNot c
  | .zong_reverse,   6, c => SSBX.Foundation.Atlas.Yi.Hexagram.zong c
  | .zong_reverse,   _, c => bitNot c

/-! ## § 3  apply — 二元应用（Option 签名，无任意 fallback）

  仅有自然二元行动的 op 返回 `some`；其他返回 `none`（诚实的"无二元意义"）。 -/

/-- 二元算子的应用。XOR-类返回 `some`；无自然二元行动者返回 `none`。 -/
def OperatorTag.apply : (op : OperatorTag) → (n : Nat) → BitSpace n → BitSpace n → Option (BitSpace n)
  | .v4_compose,     _, a, b => some (BitSpace.xor a b)
  | .cayley_mul,     _, a, b => some (BitSpace.xor a b)
  | .yin_mask,       _, a, b => some (BitSpace.xor a b)
  | .tou_mask,       _, a, b => some (BitSpace.xor a b)
  | .identity_op,    _, a, _ => some a
  | _,               _, _, _ => none

/-! ## § 4  composeZone — Zone 全序 + max（结构派生，非 5×5 硬编码）

  Zone 排序之直觉："证据等级"——dao_axiom 是最强结构性见证（最低 level），
  wall 是最终结论（最高 level）。两个 zone 之复合 = level 较高者，对应
  "证据被弱化"之单调性。

  ```
  level 0: dao_axiom       (静态不动点)
  level 1: dao_dynamic     (轨道道，如生生不息)
  level 2: li_conditional  (理：需前提)
  level 3: ke_li           (可理：升档可决)
  level 4: wall            (墙：结构性不可达)
  ```

  原 5×5 表之每条等式均是 max 之实例。无新断言。 -/

/-- Zone 之"证据弱化等级"。 -/
def Zone.level : Zone → Nat
  | .dao_axiom      => 0
  | .dao_dynamic    => 1
  | .li_conditional => 2
  | .ke_li          => 3
  | .wall           => 4

/-- 由 level 反查 Zone。`Nat.min` 保证 fromLevel 之 totality。 -/
def Zone.fromLevel : Nat → Zone
  | 0 => .dao_axiom
  | 1 => .dao_dynamic
  | 2 => .li_conditional
  | 3 => .ke_li
  | _ => .wall

@[simp] theorem Zone.fromLevel_level (z : Zone) : Zone.fromLevel z.level = z := by
  cases z <;> rfl

/-- Zone 复合 = 两边 level 之 max 反查回 Zone。墙吸收、dao 闭合等性质
    皆由 max 之单调性派生，不再硬编码。 -/
def composeZone (a b : Zone) : Zone :=
  Zone.fromLevel (max a.level b.level)

@[simp] theorem composeZone_wall_left (z : Zone) :
    composeZone .wall z = .wall := by
  unfold composeZone Zone.level
  cases z <;> rfl

@[simp] theorem composeZone_wall_right (z : Zone) :
    composeZone z .wall = .wall := by
  unfold composeZone Zone.level
  cases z <;> rfl

@[simp] theorem composeZone_dao_axiom_left (z : Zone) :
    composeZone .dao_axiom z = z := by
  unfold composeZone Zone.level
  cases z <;> rfl

@[simp] theorem composeZone_dao_axiom_right (z : Zone) :
    composeZone z .dao_axiom = z := by
  unfold composeZone Zone.level
  cases z <;> rfl

/-! ## § 5  «生» 之结构性事实：在 Hexagram 上无不动点

  此引理用于 Classify/Subsets：表明 `yiCore_step` 在 R₆ 上的应用从不退化为
  identity，从而 classify 的 Step 1 (静态不动点) 永不命中，Step 2 (生生不息
  分支) 才是 R₆ + yiCore_step 的实际入口。

  派生于 YiCore：«生» = «加» «一»，而 «一» 之 toIdx = 1，故 (n+1) mod 64 ≠ n。 -/

theorem sheng_no_fixed_point (c : SSBX.Foundation.Atlas.Yi.Hexagram) :
    SSBX.Foundation.Atlas.Yi.YiCore.«生» c ≠ c := by
  intro hfix
  -- «生» c = «生生» 1 c（由 «生生» 的递归定义直接得到）
  have h1 : SSBX.Foundation.Atlas.Yi.YiCore.«生生» 1 c = SSBX.Foundation.Atlas.Yi.YiCore.«生» c := rfl
  -- 通过 toIdx 变换：toIdx («生生» 1 c) = (toIdx c + 1) % 64
  -- 用全限定 YiCore.toIdx，避免 dot-notation 在 R 6 上无法投影
  have hidx : (SSBX.Foundation.Atlas.Yi.YiCore.toIdx
                (SSBX.Foundation.Atlas.Yi.YiCore.«生生» 1 c)).val
             = (SSBX.Foundation.Atlas.Yi.YiCore.toIdx c).val := by
    rw [h1, hfix]
  rw [SSBX.Foundation.Atlas.Yi.YiCore.«生生_toIdx»] at hidx
  have hlt : (SSBX.Foundation.Atlas.Yi.YiCore.toIdx c).val < 64 :=
    (SSBX.Foundation.Atlas.Yi.YiCore.toIdx c).isLt
  omega

end SSBX.Foundation.Hierarchy.ZoneClassifier
