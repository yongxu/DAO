# D · 算子代数体系（计算/范畴对应）

由 `wenyan-operators.md` 第 19.7 节启始，将四级生成翻译至**类型论 / 范畴论**。
此为本目录最薄、最严之 base case——其他体系皆可视为此结构之具体填充。

## 主表

| 级 | 类型 | 基数 | 同构 |
|----|-----|-----|------|
| 太极 | `Unit` (`()`, `1`) | 1 | terminal object |
| 两翼 | `Bool` = {⊤, ⊥} | 2 | 2 = 1 + 1 |
| 四象 | `Bool × Bool` | 4 | 2 × 2 |
| 八卦 | `Bool × Bool × Bool` | 8 | 2³ |
| 六十四卦 | `Bool⁶` | 64 | 2⁶ |

## 类型构造

```
太极  ≜ Unit
两翼  ≜ Unit + Unit         -- 即 Bool
四象  ≜ Bool × Bool
八卦  ≜ Bool × Bool × Bool
卦  ≜ Vec Bool 6
```

## 算子（按级递增）

### 太极级
| 算子 | 类型 | 释 |
|------|-----|---|
| `id` | A → A | 恒等 |
| `Y` | (a → a) → a | 自指（生生 ≅ Y combinator） |
| 生生 | inductive `Sheng : Nat → Type` | `wenyan-operators.md` §19.6；亦见 `BaguaAlgebra.lean` |

### 两翼级
| 算子 | 类型 | 公理 |
|------|-----|------|
| `反` (¬) | Bool → Bool | ¬² = id（involution） |
| `分` (生) | A → Bool → A × Bool | 附加新爻：太极加一爻成两仪 |
| `合` (省) | A × Bool → A | 第一投影 π₁；丢一爻 |
| `!` | A → Unit | 唯一映射（终对象） |

注：`Unit → Bool` 不可有函数（cardinality 失配）。「太极生两仪」之形式实现是
`分 : Unit → Bool → Unit × Bool ≅ Bool`——即"取一爻"等于"做选择"。

### 四象级
| 算子 | 类型 | 释 |
|------|-----|---|
| `⟨·, ·⟩` (pairing) | (C → A) × (C → B) → (C → A × B) | 普范性：积之 universal property |
| `易` (swap) | A × B → B × A | swap² = id |
| `π₁, π₂` | A × B → A / B | 投影 |
| `分` (生) | Bool → Bool → Bool × Bool | 两仪附一爻成四象 |
| `合` (省) | Bool × Bool → Bool | π₁ 或 π₂（任选） |

注：`配` 之严格类型是 `(C→A) × (C→B) → (C→A×B)`，即从两个映射得一个到积之映射；
原文写"A × B → B × A 之伴随"不准确，已改。

### 八卦级
| 算子 | 类型 | 释 |
|------|-----|---|
| `分` (生) | Bool² → Bool → Bool³ | 四象附一爻成八卦 |
| `合_i` (省) | Bool³ → Bool² | 投影删第 i 爻（i ∈ {上, 中, 下}） |
| `重` (chong / oplus) | Bool³ × Bool³ → Bool⁶ | 内卦 ⊕ 外卦 = 六爻卦 |
| `内 / 外` | Bool⁶ → Bool³ | 取下三爻 / 取上三爻 |
| `归一` | Bool³ → Unit | 合 之三阶迭代（= !） |

## 生成方程（递归）

```
级₀ = Unit
级_{n+1} = 级_n × Bool
```

或等价地用 `分` 作为 **type-level functor**（升维构造器，非 set-level 函数）：

$$\boxed{F : A \mapsto A \times \mathrm{Bool}}, \qquad \text{级}_n = F^n(\text{Unit}), \qquad |\text{级}_n| = 2^n$$

term-level 之 `分` 算子需取一新爻为参（"附爻"）：

$$\text{分} : A \to \mathrm{Bool} \to A \times \mathrm{Bool}, \quad \text{分}(a, b) = (a, b)$$

term 层非函数 $A \to A \times \mathrm{Bool}$（cardinality 失配 $|A| < 2|A|$，缺一位信息）。
"太极生两仪"之严格语义是 type-level **嵌入**：$\mathrm{Unit} \hookrightarrow \mathrm{Bool}$
（两种嵌入对应两仪之两支），亦即 $\mathrm{Bool} \cong \mathrm{Unit} + \mathrm{Unit}$ 之 coproduct 注入。

## Y combinator 与生生

由 `wenyan-operators.md` §19.6：

```
生生 ≅ Y(生)
損之又損 ≅ iter(損, x)
```

文言文之 **反復 / 之又** 模式即 fixed-point combinator 之自然语形式。
太极一级承担**自指算子**之位——是整个生成树之 root，也是不动点之 host。

## 与 A、B、C 之同构关系

| 体系 | 同构方向 | 说明 |
|------|---------|------|
| A 易传 | 一一同构 | A 之四象/八卦即 D 之 Bool²/Bool³，符号映射 |
| B 六征 | 注入同构 | B 三征对 → D 之三个 Bool 分量 |
| C 实虚史真 | 注入同构 | C 三轴 → D 之三个 Bool 分量 |

A、B、C 三体系**底层皆同构于 D**，差别在**填充语义**：
- A：阴阳之精粗
- B：六征之三对
- C：modal × 史 × 真假

## 范畴论刻画

四级生成 = 笛卡尔闭范畴 (CCC) 中的 `2ⁿ` 序列：
- `Unit` = terminal object `1`
- `Bool` = `1 + 1`
- 四象 = `2 × 2`
- 八卦 = `2 × 2 × 2 = 2³`

`分` 算子 = 与 `Bool` 之笛卡尔积函子：
$$- \times \text{Bool} : \mathcal{C} \to \mathcal{C}$$

迭代 6 次得 64 卦：
$$(- \times \text{Bool})^6(1) = \text{Bool}^6$$

## 不交换性（参 §20）

虽然各级**结构层**严格 2ⁿ，但**算子施加之顺序**未必交换：

| 算子对 | 是否交换 |
|--------|---------|
| 分 × 分 | 交换（笛卡尔积满足结合/对称） |
| 分 × 易 | 交换 |
| 反 × 反 | 显然 |
| 损 × 益 | **不交换**（参 §20.2） |
| 化 × 反 | **不交换** |

形式上四级生成是 commutative 的，但**应用层**算子（如损益、化反）非 commutative。
故四级生成树是结构骨架，算子代数才是动态。

## 形式实现指引

项目实际 Lean 实现（`formal/SSBX/Foundation/BaguaAlgebra.lean`）：

```lean
-- Yao 来自 Yi.lean：inductive Yao | yang | yin
inductive Sheng : Nat → Type
  | tai  : Sheng 0
  | step : ∀ {n}, Sheng n → Yao → Sheng (n + 1)

theorem Sheng.toTrigram_ofTrigram : ... -- Sheng 3 ≃ Trigram
theorem Sheng.toHexagram_ofHexagram : ... -- Sheng 6 ≃ Hexagram
```

或者作为 `Trigram` 之 structure（`Yi.lean`）：

```lean
structure Trigram where
  y1 : Yao  -- 初爻 (下)
  y2 : Yao  -- 中爻
  y3 : Yao  -- 上爻

structure Hexagram where  -- ⟨y1..y6⟩，y1..y3 = 内卦，y4..y6 = 外卦
  y1 y2 y3 y4 y5 y6 : Yao
```

详见 [`H_证明报告.md`](H_证明报告.md) 之 75 定理 / 0 sorry 验证。

## 与项目 MonadDAG 之接口

由 `formal/SSBX/MonadDAG.md` 之单字 333 + 生成 134 = 467 体系：
- 四级之 1+2+4+8 = 15 个结点皆有单字承担
- 64 卦皆有传统单字（49 单字 + 15 双字）
- 但 64 之 3 时态投影（192 格）不再造新字（参表六）

D 体系是**形式骨架**，落字交给 A／B／E 体系。
