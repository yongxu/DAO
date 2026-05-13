# R₅ 五爻 (provisional) — strict-uniform R-hierarchy 之中介层

> 状态：v3 定本 (2026-05-11)
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ strict-uniform doctrine, § 3.5)
> 配套：[r4-r8-character-ladder.md](r4-r8-character-ladder.md) · [ox-notation.md](ox-notation.md) · [shi-v4.md](shi-v4.md) · [lift-project.md](lift-project.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md)
> 形式锚：[`Foundation/Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean)

> 2026-05-13 注：本文保留 R₅ 现有 Lean carrier (`Wuyao = Mian × Bool`) 与旧「五爻 provisional」讨论。公开字 / reader grammar 的新一版决策见 [r4-r8-character-ladder.md](r4-r8-character-ladder.md)：R₅ surface 推荐为「內」，位值为「內本 / 內征」，算子为「易內」。这尚未等于 Lean declaration rename。

---

## 第一部分：位置与必要性 (Position & Necessity)

### 1.1 R₅ 在 R-hierarchy 中之位置

R₅ 介于 R₄ Mian 与 R₆ Hexagram 之间：

```
R₀ → R₁ → R₂ → R₃ → R₄ → R₅ → R₆ → R₇ → R₈
 1    2    4    8   16   32   64  128  256
                    ↑    ↑    ↑
                    Mian  Wuyao Hex
```

**Size**: |R₅| = 32 = (Z/2)⁵ = 2 × |R₄| = |R₆| / 2。

R₅ 是 strict-uniform (Z/2)ⁿ 律下**唯一无传统 Yi anchor**之层 — 它 mathematical 存在但 philosophical 上未独立刻画 (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.5)。

### 1.2 为何 R₅ 必须存在

**strict-uniform (Z/2)ⁿ 闭合**要求每个 R 层之 size 为 2ⁿ，每升 1 层加恰 1 binary axis。R₃ → R₆ 跨越 +3 bits — 不是单 lift。要保持 strict-uniform：

```
R₃ (8) → R₄ (16) → R₅ (32) → R₆ (64)
        +1 bit    +1 bit    +1 bit
```

R₄ Mian 与 R₆ Hexagram **都有传统 Yi anchor**（Mian = Ben × Zheng 之 16 命载体；Hexagram 即六十四卦）。但 (Z/2)⁵ = 32 这层在传统 Yi 中**没有独立 ontology 单位** — 既不是「面」也不是「卦」。

旧 v1 R-hierarchy 把 R₃ → R₆ 看作单 +3 bit 之「chong 跳跃」（重卦 = trigram × trigram），跳过 R₄ 与 R₅。v2.1 strict-uniform 显式纳入 R₄ + R₅，让 R-hierarchy 真正逐 bit 进展，无跳跃 ([yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.9)。

### 1.3 R₅ 之 ontological status

**最弱 ontological 层**：

> R₅ 是 (Z/2)ⁿ 机械补全之产物 — 不是 Yi 传统直接刻画之单位 ([yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.5)。

这与 R₄ 不同。R₄ 之 16-命 Mian = Ben × Zheng 通过 BenZheng doctrine 有完整 ontology (4 本 × 4 征)。R₅ 之 32 cells 仅是 R₄ × Bool 之纯机械 product — 第 5 位 Bool 没有独立 anchor。

---

## 第二部分：Lean 实现 (Lean Realization)

### 2.1 R₅ Carrier — Wuyao = Mian × Bool

[`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) § 1：

```lean
namespace SSBX.Foundation.Hierarchy.R5_Wuyao

open SSBX.Foundation.Bagua.BenZheng

/-- R₅ (32-cell Wuyao) = Mian × Bool. -/
abbrev Wuyao : Type := Mian × Bool
```

**结构**：`Wuyao` 是 `Mian` (16) 与 `Bool` (2) 之 product —— 32 个有序对 `(m, b)`。

设计选择 (来自 [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) 文件 docstring)：

```
R₅ = R₄ × Bool = Mian × Bool. The added Bool is the "5th yao" extension
bit — Mian carries 4 bits (2 for Ben + 2 for Zheng = 4); a single Bool
makes it (Z/2)⁵ = 32.

|Wuyao| = 16 × 2 = 32 = (Z/2)⁵.

Atomic operator: **flip5** = toggle the 5th-yao Bool bit (Z/2 involution).
```

### 2.2 全枚举 (`Wuyao.all`)

[`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) § 1：

```lean
namespace Wuyao

/-- All 32 wuyao: 16 mian × 2 bit-state. -/
def all : List Wuyao :=
  Mian.all.flatMap fun m => [(m, false), (m, true)]

theorem all_length : all.length = 32 := by native_decide

theorem all_nodup : all.Nodup := by native_decide

theorem mem_all (w : Wuyao) : w ∈ all := by
  rcases w with ⟨m, b⟩
  unfold all
  refine List.mem_flatMap.mpr ⟨m, ?_, ?_⟩
  · -- m ∈ Mian.all
    rcases m with ⟨bn, zh⟩
    show (bn, zh) ∈ Mian.all
    unfold Mian.all
    refine List.mem_flatMap.mpr ⟨bn, ?_, ?_⟩
    · cases bn <;> simp [Ben.all]
    · refine List.mem_map.mpr ⟨zh, ?_, rfl⟩
      cases zh <;> simp [Zheng.all]
  · cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

end Wuyao
```

### 2.3 R₅ Atomic 算子 — flip5

[`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) § 2：

```lean
/-- flip5: toggle the Bool component (the "5th yao"). Z/2 involution. -/
def flip5 (w : Wuyao) : Wuyao := (w.1, !w.2)

/-- flip5 is involutive: flip5² = id. -/
theorem flip5_flip5 (w : Wuyao) : flip5 (flip5 w) = w := by
  rcases w with ⟨m, b⟩
  cases b <;> rfl

/-- flip5 preserves the Mian component. -/
theorem flip5_preserves_mian (w : Wuyao) : (flip5 w).1 = w.1 := by
  rcases w with ⟨m, b⟩; rfl
```

**flip5** 是 R₅ 之**唯一 atomic 算子** — toggle 第 5 位 Bool。它与 R₆ Hexagram 之 6 个单爻 flip (flip1..flip6) 无关，是 R₅ 独立层之 own atom。

注意：在 Cell128 / Cell256 中亦有 `flip5` 函数（toggle 第 5 yao 即 huaOuter），但语义不同：

| flip5 location | 作用 | bit 位置 |
|---|---|---|
| `R5_Wuyao.flip5` | toggle Wuyao 之 Bool | R₅ 之第 5 bit (Bool) |
| `Cell128.flip5` | toggle hexagram 之 5th yao (huaOuter) | Hexagram 之 y5 |
| `Cell256.flip5` | toggle hexagram 之 5th yao (huaOuter) | Hexagram 之 y5 |

它们**不**等价 — `R5_Wuyao.flip5` 是 R₅ 层之 own atom；其它二者是 hexagram-side 算子 lift 到 R₇/R₈。

### 2.4 R₄ ↔ R₅ Lift / Project

[`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) § 3：

```lean
/-- Lift R₄ Mian into R₅ Wuyao by attaching a 5th-yao bit. -/
def liftR4toR5 (m : Mian) (b : Bool) : Wuyao := (m, b)

/-- Project R₅ Wuyao back to R₄ Mian (forget the 5th-yao bit). -/
def projR5toR4 (w : Wuyao) : Mian := w.1

/-- proj ∘ lift = id on R₄: faithful R₄ ↪ R₅. -/
theorem proj_lift_id_R4 (m : Mian) (b : Bool) :
    projR5toR4 (liftR4toR5 m b) = m := rfl
```

最简：lift 加 Bool，project 取 .1。`rfl` 闭合。

详见 [lift-project.md](lift-project.md) § 3.5 R₄ ↔ R₅ 之全 context。

### 2.5 Public summary

[`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) § 4：

```lean
/-- R₅ Wuyao 收口摘要: 基数 32 + 全覆盖 + flip5 involution. -/
theorem wuyao_summary :
    Wuyao.all.length = 32
    ∧ (∀ w : Wuyao, w ∈ Wuyao.all)
    ∧ (∀ w : Wuyao, flip5 (flip5 w) = w) :=
  ⟨Wuyao.all_length, Wuyao.mem_all, flip5_flip5⟩

end SSBX.Foundation.Hierarchy.R5_Wuyao
```

---

## 第三部分：命名候选 (Naming Candidates) — Provisional

### 3.1 当前命名: 五爻 (Wuyao)

**「五爻」为 descriptive baseline** — 字面意指「5 个 yao」之 binary structure；不是 Yi 传统 ontology。

来源：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.5 之 caveat（**provisional naming**）：

> R₅ — 五爻 (5-yao) ⭐ 新显式纳入 (provisional)
>
> 元 (`ooooo`..`xxxxx`): 32 cells = (Z/2)⁵
> 新 atom: 第 5 个 binary axis（无传统 Yi anchor; 可看作「Mian + 一个额外 yao」或「半个 hexagram」）
> Lift₅: R₅ × R₁ → R₆ (chong 之最后一步)

### 3.2 候选命名表

来自 [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.5 与 [yi-calculus-theorem.md](yi-calculus-theorem.md) §16：

| 候选 | 含义 / 来源 | 优点 | 缺点 |
|---|---|---|---|
| **五爻** (current, descriptive) | 字面: 5 yaos | 安全, 无 ontological 承诺 | 仅描述 size; 无 ontology 内容 |
| **接** (jie) | 「连接 R₄ Mian 与 R₆ Hexagram 之过渡」| 揭示中介性 (transition) | 字义模糊；与「接续」「接口」相涉 |
| **临** (lin) | "approaching" — 古汉语接近义 | 古文丰富 | **与卦名 #19 临 相重** — 命名冲突 |
| **渐** (jian) | "gradual" — 渐进 | 古文丰富 | **与卦名 #53 渐 相重** — 命名冲突 |
| **进** (jin) | "advance" — 进展 | 古文丰富 | 与 晋 (#35) 字音近；进/晋区分难 |

### 3.3 评估 axes

(per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 10.4 开放问题)

四轴评估：

| 候选 | 哲学 anchor | 形式科学 anchor | 古文 anchor | 项目耦合 |
|---|---|---|---|---|
| 五爻 (descriptive) | × | × (descriptive) | △ | △ |
| 接 (jie) | △ | △ (transition) | △ | × |
| 临 (lin) | △ (临卦) | × | ✓ | × (与 hex 名冲突) |
| 渐 (jian) | △ (渐卦) | × | ✓ | × (与 hex 名冲突) |
| 进 (jin) | △ | × | △ | △ (听觉撞 jin) |

### 3.4 当前实践

项目当前**保持 descriptive 「五爻」**：
- Lean type 名 `Wuyao` (拼音)
- 算子名 `flip5` (descriptive, 与 Cell128/256 之 flip5 在 R₆ 层 yao#5 之命名同形但语义不同)
- 文档以 「R₅ 五爻 (provisional)」标注

回看时机：在更多下游 doctrine 把 R₅ 当作独立 ontological 单位使用（即真有「R₅ 之内容线」）后，再决定是否换为 anchored 名（接 / 临 / 渐 / 进 之一）。

### 3.5 为何不强行命名

强行用 anchored 名 (临 / 渐 / 进) 之风险：

1. **语义错配**：传统 Yi 中临 / 渐 / 进 都是**重卦** (R₆) 之名，不是「介于 Mian 与 Hexagram 之间的某层」。把 R₆ 卦名挪到 R₅ 会引发概念混乱。
2. **过早承诺**：R₅ 在项目当前 Lean 落地中**仅作为 lift/project 之中介**出现，没有独立 ontological 内容。强加 ontology 名意味着承诺了它将有独立 doctrine — 这违反「形式跟随实质」之原则。
3. **冲突可能**：若 future 引入了真正的「R₅-命」（即一种确实存在于 32-cell 上之 Yi 结构），strong-named 命可能与之冲突。

descriptive 「五爻」是 *safe placeholder* — 准确反映「这是 R-hierarchy 之第 5 层，无独立 Yi anchor」之事实。

---

## 第四部分：chong 之 3-步分解 (chong as 3-step composite)

### 4.1 旧 chong jump

旧 v1 R-hierarchy 把 chong : Trigram × Trigram → Hexagram 看作 R₃ → R₆ 之单一 +3 bit 跳跃。这隐藏了 R₄ 与 R₅。

### 4.2 strict-uniform 视角

v2.1 strict-uniform 把 chong 显式分解为 **3 步 +1 bit lift** (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 4.4 模式 C)：

$$\text{chong}: R_3 \times R_3 \to R_6 \quad \cong \quad R_3 \xrightarrow{\text{liftR3toR4}} R_4 \xrightarrow{\text{liftR4toR5}} R_5 \xrightarrow{\text{liftR5toR6}} R_6$$

R₅ 成为 chong 之第 2 步中介 — 在 strict-uniform 视角下，hexagram 不是「2 个 trigram 之 product」，而是「6 个 yao 之 sequence」之 6-step lift 中之第 5 步。

### 4.3 3-step composite 之具体 input

由 [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 4–6：

| Step | input | output | extra param |
|---|---|---|---|
| `liftR3toR4` | R₃ Trigram | R₄ Mian | 1 Yao (`y4`) |
| `liftR4toR5` | R₄ Mian | R₅ Wuyao | 1 Bool (`b`) |
| `liftR5toR6` | R₅ Wuyao | R₆ Hexagram | 1 Yao (`y6`) |

合计：1 Trigram + 1 Yao + 1 Bool + 1 Yao = 8 → 1 → 16 → 32 → 64。
即 R₃ (8 cells) × Yao (2) × Bool (2) × Yao (2) = 64 = R₆ 之 cardinality。

### 4.4 R₅ 之中介性

R₅ 是 chong 中**唯一无 traditional Yi 对应**之中介。R₃ 是 trigram，R₄ 是 Mian (Ben × Zheng)，R₆ 是 hexagram — 每个都有独立 doctrine。R₅ 仅作为 chong 之第 2 步 stepping stone 存在。

这是 R₅ 「最弱 ontological 层」之具体表达：

- **R₃ 提问**: 「这个 trigram 是什么 phase？」
- **R₄ 提问**: 「这是 Ben × Zheng 之哪个组合？」
- **R₅ 提问**: ??? (没有独立问题)
- **R₆ 提问**: 「这是 64 卦之哪一卦？」
- **R₇ 提问**: 「这卦携带 past trace 否？」
- **R₈ 提问**: 「这卦之 (因, 果) 时态是什么？」

R₅ 之 32 cells 仅是 **Mian × Bool 之纯机械积** — Bool 没有独立 ontological 内容。

---

## 第五部分：边界 (Boundaries)

### 5.1 R₅ **不**做的事

| 不做 | 原因 |
|---|---|
| 不刻画独立 Yi-style 32-命 doctrine | R₅ 无传统 Yi anchor |
| 不刻画 V₄ outer 算子 (zong / hu) | V₄ outer 主要在 R₃ / R₆ / R₈; R₅ 无独立 V₄ structure |
| 不刻画 BenZheng quadrant 之 R₅ analog | quadrant 在 R₃ / R₆ 层定义 |
| 不接 retention/protention 现象学 | 那是 R₇ / R₈ (因 / 果) 之内容 |

### 5.2 与 R₅ 相邻 (但不在 R₅ 内)

- **R₄ Mian** ([`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean))：R₄ 之 16-命 doctrine
- **R₆ Hexagram** ([`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean))：64 卦 doctrine + V₄ outer algebra
- **chong (R₃ → R₆)** ([`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean))：3-step composite 之 explicit form
- **R₇ Cell128 + 因** ([`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean))：下一层 atom (因/YinBit) 之 ontology
- **R₈ Cell256 + 果 + Shi V₄** ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean))：top layer

R₅ 之**唯一职责**是「让 R-hierarchy 在 R₃ → R₆ 之间不跳过 (Z/2)⁵」。

---

## 第六部分：未来方向 (Future Directions)

### 6.1 是否需要 R₅ Lean 主类型？

R₅ 当前以 `Wuyao = Mian × Bool` 之 abbrev 存在 ([`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) § 1)，**不是** independent inductive。

候选：

- **当前 (abbrev)**: `abbrev Wuyao : Type := Mian × Bool`
  - 优点：minimal LOC; auto-decidable
  - 缺点：无独立 namespace；跟 R₄ 强耦合

- **future option (independent inductive)**: `inductive Wuyao : Type where ...` (32 ctors 或 enum-style)
  - 优点：独立 namespace; 可加 own structure
  - 缺点：32 ctors 重复 Mian × Bool 信息；增加证明 cost

当前选择 abbrev — 与 R₅ 「无独立 ontology」之 status 一致。

### 6.2 如果 future 引入 R₅ ontology

若发现 32-cell 上确实存在某种 Yi-style 结构（例如「8-trigram × 4-quadrant」或「2-mian × 16-state」），则：

1. 命名从 descriptive 「五爻」换为 anchored 名
2. type 从 `abbrev` 升级为 `inductive` 或 `structure`
3. 加 own atomic 算子 (除 `flip5` 外的 R₅ 独有变换)
4. 加 own doctrine 文件 (类似 [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean))

但这些都是 *future-conditional* — 只有在实际发现 ontological 内容后再做。

### 6.3 V₄ outer 算子之可能 R₅ lift

V₄ outer (zong / hu / cuoZong) 在 R₃ 与 R₆ / R₈ 上有定义。R₅ 上尚无 V₄ outer — 因为 R₅ 之 5-yao 结构没有自然的「reverse」或「inner-extract」对称。

候选：
- `zong5` : Wuyao → Wuyao 反 5-yao 序? 但 Wuyao 不是直接 5-yao tuple — 需先 lift 到 R₆ 再做 zong 再 project 回。
- 这等价于 R₆ 之 zong 加 R₅↔R₆ 之 lift/project sandwich — **不是新算子**。

结论：R₅ **没有**独立 V₄ outer 算子；任何 R₅-level zong/hu 都通过 R₆ 之 zong/hu sandwich 得到。

---

## 附录 A：R₅ Wuyao 完整 Lean 签名摘要

来自 [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean)：

```lean
namespace SSBX.Foundation.Hierarchy.R5_Wuyao

open SSBX.Foundation.Bagua.BenZheng

-- § 1 R₅ carrier
abbrev Wuyao : Type := Mian × Bool

namespace Wuyao
def all : List Wuyao
theorem all_length : all.length = 32
theorem all_nodup : all.Nodup
theorem mem_all (w : Wuyao) : w ∈ all
end Wuyao

-- § 2 atomic operator
def flip5 (w : Wuyao) : Wuyao
theorem flip5_flip5 (w : Wuyao) : flip5 (flip5 w) = w
theorem flip5_preserves_mian (w : Wuyao) : (flip5 w).1 = w.1

-- § 3 Lift / Project (R₄ ↔ R₅)
def liftR4toR5 (m : Mian) (b : Bool) : Wuyao
def projR5toR4 (w : Wuyao) : Mian
theorem proj_lift_id_R4 : ∀ m b, projR5toR4 (liftR4toR5 m b) = m

-- § 4 summary
theorem wuyao_summary : ...

end SSBX.Foundation.Hierarchy.R5_Wuyao
```

## 附录 B：R₅ 命名讨论摘要

```
来源 | 名 | status
─────────────────────────────────────────────────
当前 (project)   | 五爻 / Wuyao   | provisional baseline (descriptive)
yi-RO-hierarchy.md § 3.5 | 五爻 (or 接/临/渐/进) | "(provisional, 无传统 Yi anchor)"
yi-calculus-theorem.md §16 | (no R₅-specific entry; §16 focuses on 因/果) | (R₅ 命名问题 unaddressed)
```

R₅ 命名属于「形式 R-hierarchy 完备性 vs 传统 Yi ontology 直接对应」之 tension 之具体表现。当前 default = 形式优先（descriptive 「五爻」），保留 future flexibility。

## 附录 C：与其它文档之关系

| 文档 | 与本文关系 |
|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | parent doctrine — § 3.5 R₅ 显式纳入 + § 3.9 chong 3-step |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorem K (R₀..R₈ 全 closure) 中 R₅ 之 32-cell 基数 |
| [ox-notation.md](ox-notation.md) | OX 字面量是 R₈; R₅ 之 5-char OX 未实现 (boundaries 5.1) |
| [shi-v4.md](shi-v4.md) | Shi V₄ 在 R₈ — R₅ 之 Bool 与之无直接关系 |
| [lift-project.md](lift-project.md) | § 3.5 R₄ ↔ R₅ + § 3.6 R₅ ↔ R₆ + § 5 chong 3-step |
| [r7-yin-r8-guo.md](r7-yin-r8-guo.md) | R₇ / R₈ 之因/果 axes 与 R₅ 之 Bool axis 在 ontology 上无关 (因/果 有 anchor; R₅ 无) |
| [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | **本文档之 ground truth source** |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | R₄ Mian 之 source — R₅ 之直接 base |
| [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | R₄ ↔ R₅ + R₅ ↔ R₆ 之 lift/project 函数 |
