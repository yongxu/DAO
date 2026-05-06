# G · 完整算子系统 · 八卦互通 + 归一

设计目标：
1. **横向**：在八卦层之内，任一卦可经算子序列变成任一其他卦（互相 transform）
2. **纵向**：从 64 卦经合归至 8 → 4 → 2 → 1，最终归一
3. **单字落地**：每个算子皆有汉字单字承担

二者共一**算子代数**，称为 **「易卦群 G_易」**。

---

## 一、卦之编码

约定：每卦 = 三爻向量 $\langle y_1, y_2, y_3 \rangle$，
- $y_1$ = 初爻（最下）
- $y_2$ = 中爻
- $y_3$ = 上爻（最顶）
- 每爻 $\in \{0 = \text{阴}, 1 = \text{阳}\}$

此约定与 `Yi.lean` 之 `Trigram` 一致，亦合中国传统「自下而上」之读爻次第，
与 [`A_经典易传.md`](A_经典易传.md)、[`I_八卦全集.md`](I_八卦全集.md) 所用同。

| 卦 | 符号 | $\langle y_1, y_2, y_3 \rangle$ = ⟨下, 中, 上⟩ |
|----|------|----------------------------------------------|
| 乾 | ☰ | ⟨1, 1, 1⟩ |
| 兑 | ☱ | ⟨1, 1, 0⟩ |
| 离 | ☲ | ⟨1, 0, 1⟩ |
| 震 | ☳ | ⟨1, 0, 0⟩ |
| 巽 | ☴ | ⟨0, 1, 1⟩ |
| 坎 | ☵ | ⟨0, 1, 0⟩ |
| 艮 | ☶ | ⟨0, 0, 1⟩ |
| 坤 | ☷ | ⟨0, 0, 0⟩ |

八卦集 $\mathbb{B}^3 = \{0,1\}^3$，基数 8。

---

## 二、横向算子（八卦互通群）

### 2.1 生成元：三个反爻

| 算子 | 单字 | 类型 | 作用 |
|------|-----|------|------|
| 反_上 | **变** | $\mathbb{B}^3 \to \mathbb{B}^3$ | 翻上爻 |
| 反_中 | **化** | $\mathbb{B}^3 \to \mathbb{B}^3$ | 翻中爻 |
| 反_下 | **动** | $\mathbb{B}^3 \to \mathbb{B}^3$ | 翻下爻 |

或统一记 $\bar{\partial}_i$（$i ∈ \{上, 中, 下\}$），满足：
$$\bar{\partial}_i^2 = \text{id}, \quad \bar{\partial}_i \circ \bar{\partial}_j = \bar{\partial}_j \circ \bar{\partial}_i$$

（每个反爻是 involution，且彼此交换。）

### 2.2 生成群

$$G_{\text{横}} = \langle \bar{\partial}_上, \bar{\partial}_中, \bar{\partial}_下 \rangle \cong (\mathbb{Z}/2)^3$$

|G_横| = 8，**与八卦集一一对应**——群作用 simply transitive。

群元（按 (Z/2)³ 之 8 元）：

| # | 群元 | 单字 | 复合 | 作用于乾⟨1,1,1⟩之果 |
|---|------|-----|------|------------------|
| 1 | id | **不** / **静** | id | 乾 ⟨1,1,1⟩ |
| 2 | 反_下 | 动 | $\bar{\partial}_下$ | 巽 ⟨0,1,1⟩ |
| 3 | 反_中 | 化 | $\bar{\partial}_中$ | 离 ⟨1,0,1⟩ |
| 4 | 反_上 | 变 | $\bar{\partial}_上$ | 兑 ⟨1,1,0⟩ |
| 5 | 反_中下 | **倾** | $\bar{\partial}_中 \bar{\partial}_下$ | 艮 ⟨0,0,1⟩ |
| 6 | 反_上下 | **侧** | $\bar{\partial}_上 \bar{\partial}_下$ | 坎 ⟨0,1,0⟩ |
| 7 | 反_上中 | **斜** | $\bar{\partial}_上 \bar{\partial}_中$ | 震 ⟨1,0,0⟩ |
| 8 | 反_全 | **错** | $\bar{\partial}_上 \bar{\partial}_中 \bar{\partial}_下$ | 坤 ⟨0,0,0⟩ |

注：「倾／侧／斜」是为占位的拟字（汉字传统对二阶反爻无单字，可由两个原始反复合）；
**「错」** 是传统命名，专指三阶全反（卦之 antipode，与综之"上下倒置"不同——错改值，综改位）。

### 2.3 八卦互通图（Cayley 图 = 立方体）

```
                乾⟨1,1,1⟩
              ╱     │     ╲
       兑⟨1,1,0⟩ 离⟨1,0,1⟩ 巽⟨0,1,1⟩
           ╱   │  ╲ ╱  │  ╲ ╱  │   ╲
          ╱    │   ╳   │   ╳   │    ╲
       震⟨1,0,0⟩ 坎⟨0,1,0⟩ 艮⟨0,0,1⟩
              ╲     │     ╱
                坤⟨0,0,0⟩
```

边即「一爻之变」（汉明距离 1）。立方体 8 顶点，12 条边。
**任一卦至任一卦最短 ≤ 3 步**（汉明距离上界）。
图中 ⟨y₁, y₂, y₃⟩ = ⟨下, 中, 上⟩。

### 2.4 错／综 — 经典两大派生算子

| 算子 | 单字 | 定义 | 群表达 | 性质 |
|------|-----|------|-------|------|
| **错** | 错 | 阴阳全反 | $\bar{\partial}_上 \bar{\partial}_中 \bar{\partial}_下$ | (Z/2)³ 之最长元（三反复合，等价于群中字长 = 3 之唯一元） |
| **综** | 综 | 位置反序 | $\langle y_1,y_2,y_3 \rangle \mapsto \langle y_3,y_2,y_1 \rangle$ | **不在 (Z/2)³ 中**，属位置置换 |

错卦对偶（4 对 antipode）：
$$\text{乾} \leftrightarrow \text{坤}, \quad \text{兑} \leftrightarrow \text{艮}, \quad \text{离} \leftrightarrow \text{坎}, \quad \text{震} \leftrightarrow \text{巽}$$

综卦对偶（2 对反序，4 卦自反）：
- 不动点（回文卦）：乾、坤、离、坎
- 对偶：兑 ↔ 巽，震 ↔ 艮

**扩展群** $\widetilde{G}_{\text{横}} = (\mathbb{Z}/2)^3 \rtimes \langle \text{综} \rangle$，阶 16。
**全群**（加任意位置置换）= 超八面体群 $B_3 = (\mathbb{Z}/2)^3 \rtimes S_3$，阶 48。

> 项目主用：$(\mathbb{Z}/2)^3$ 已**足够 simply transitive**——任两卦间皆可达。
> 错／综 为习惯命名之派生，非新自由度。

---

## 三、纵向算子（归一 + 生）

### 3.1 上行算子：合（归一）

| 算子 | 单字 | 类型 | 作用 |
|------|-----|------|------|
| 合_上 | **省** / 合 | $\mathbb{B}^3 \to \mathbb{B}^2$ | 投影删上爻 |
| 合_中 | 省 / 合 | $\mathbb{B}^3 \to \mathbb{B}^2$ | 投影删中爻 |
| 合_下 | 省 / 合 | $\mathbb{B}^3 \to \mathbb{B}^2$ | 投影删下爻 |
| 合 | **归** | $\mathbb{B}^n \to \mathbb{B}^{n-1}$ | 一阶降维 |
| 归一 | **一** / **抱** | $\mathbb{B}^n \to \mathbb{B}^0 = \text{Unit}$ | n 阶降维直至太极 |

**归一公式**：
$$\text{归一} = \text{合}^n : \mathbb{B}^n \to \text{Unit}$$

对 64 卦：$\text{归一} = \text{合}^6 : \mathbb{B}^6 \to \text{Unit}$（6 步降至太极）。

### 3.2 下行算子：分（生）

| 算子 | 单字 | 类型 | 作用 |
|------|-----|------|------|
| 分 | **生** | $A \to A \times \text{Bool}$ | 一阶升维 |
| 重 | **重** | $\mathbb{B}^3 \times \mathbb{B}^3 \to \mathbb{B}^6$ | 八卦相重 → 64 卦 |

**生生公式**（Y combinator）：
$$\text{生生} = Y(\text{生}) : \text{Unit} \to \mathbb{B}^\infty$$

实际项目截于 $\mathbb{B}^6$（64 卦）作为「足够」之边界。

### 3.3 上下交互

| 关系 | 公式 | 释 |
|------|-----|----|
| 合 ∘ 分 = id | $A \xrightarrow{分_b} A \times \mathrm{Bool} \xrightarrow{\pi_1} A$ | 分→合（顺方向）信息保留 |
| 分 ∘ 合 ≠ id | $A \times \mathrm{Bool} \to A \to A \times \mathrm{Bool}$ | 合→分（逆方向）丢 Bool 位 |
| 反 ∘ 合 = 合 ∘ 反 (在保留爻上) | flip 任意 *未投出* 之爻 | 反与合 在投影后剩下的 ≤ n−1 爻上交换 |

**关键**：合（归一）是**单向不可逆**的——一旦归一，原有八卦信息丢失。
但**生生**之自指保证：归一后可再生新结构。
此即「**归一 → 生生 → 归一 → ...**」永动。

---

## 四、横纵合一 · 完整代数

### 4.1 总操作集

$$\text{算子全集} = \underbrace{\{\bar{\partial}_上, \bar{\partial}_中, \bar{\partial}_下\}}_{\text{横向 3 反爻}} \cup \underbrace{\{\text{合}, \text{分}\}}_{\text{纵向 升 / 降}} \cup \underbrace{\{\text{生生}\}}_{\text{太极不动点（Y comb）}}$$

**6 个核心算子**（id 视为零步算子，省去；重 = 分之复用，详 §3.2 与 §九）。
**最小完备子集**为 5 算子 $\{$变, 化, 动, 合, 生生$\}$（参 §九）——分由生生之 inductive `step` 内化，故可去；其余四者皆不可少。

### 4.2 完整归一回路

```
                 太极 (Unit, |·|=1)
                   ↑ 合
                   │
                两仪 (Bool, |·|=2)
                   ↑ 合
                   │
                四象 (Bool², |·|=4)
                   ↑ 合
                   │
        ┌── 八卦 (Bool³, |·|=8) ──┐
        │   ↑ 合       重 ↓      │
        │   │                    │  ← 横向(Z/2)³在此层互通
        │  64卦 (Bool⁶, |·|=64)  │
        └────────────────────────┘
                   ↑ 合⁶
                   │
                 太极 (归一)
```

### 4.3 八卦互通子代数（孤立看横向）

```
def 八卦互通 (a b : Bool³) : List 反爻
  := 找最短路径 from a to b in (Z/2)³ Cayley
```

最长路径 = 3（汉明距离上限），**任意 a, b 在 ≤ 3 步内互通**。

### 4.4 全代数（横向 + 纵向）作用

任意态 $s \in \mathbb{B}^n$，可：
- **横移**：在同层 $\mathbb{B}^n$ 内由 $(\mathbb{Z}/2)^n$ 群作用至任意其他态
- **上行**：$s \to \text{合}(s) \in \mathbb{B}^{n-1}$
- **下行**：$s \to \text{分}(s, b) \in \mathbb{B}^{n+1}$（需输入新位 $b$）
- **归一**：$s \to \text{合}^n(s) \in \text{Unit}$

---

## 五、单字算子总表

| 算子 | 单字 | 类 | 群序 / 字长 | 出处 |
|------|-----|---|-----------|------|
| 反上爻 | **变** | 横向 (Z/2)³ 生成元 | 2（涉爻 1） | 易经爻变 |
| 反中爻 | **化** | 横向 (Z/2)³ 生成元 | 2（涉爻 1） | 「化而裁之」（系辞上 12） |
| 反下爻 | **动** | 横向 (Z/2)³ 生成元 | 2（涉爻 1） | 「鼓之以雷霆」（系辞上 11） |
| 全反 | **错** | 横向派生（=变∘化∘动）| 2（涉爻 3） | 错卦传统 |
| 位置反序 | **综** | 位置置换（不在 (Z/2)³）| 2 | 综卦传统 |
| 投影降维 | **合** / **省** | 纵向上行（非群元） | — | 合二归一 |
| 笛卡尔升维 | **分** / **生** | 纵向下行（非群元） | — | 「太极生两仪」 |
| 八卦相重 | **重** | 八↔64 桥（非群元） | — | 「因而重之」（系辞上 11） |
| 自指 / 不动点 | **生生** / **Y** | 太极层（inductive 自指） | ω | 「生生之谓易」（系辞上 5） |
| 恒等 | **不** / **静** | 群单位 id | 1 | — |
| 完全归一 | **一** / **抱** | 合之 n 阶迭代 | — | 「抱一为天下式」（老子 22） |

**11 个单字算子**覆盖完整代数。「群序」指作为群元素之 order（最小使 g^n=id），
「字长」指由 (Z/2)³ 生成元复合所需之最少反爻数。两者皆为 2 时只列「群序 2」。
合 / 分 / 重 / 一 不是群作用，列「—」。

> 命名注：
> - 「变／化／动」承担三个反爻——按易经传统「变在上，化在中，动在下」分工
> - 「错／综」沿用易经术语
> - 「合／分」是范畴论 product/coproduct 之中文落字
> - 「生生／一」承担太极层之自指与归一

---

## 六、Lean 形式实现 ✓ 已完整证明

完整 Lean 实现见 [`formal/SSBX/Foundation/BaguaAlgebra.lean`](../formal/SSBX/Foundation/BaguaAlgebra.lean)。
该文件已加入 `SSBX` 库主入口，**全部 36 个 Lean 文件 lake 编译通过，无 sorry**。

### 主要定义与定理（皆已机器验证）

| 章 | 内容 | 命名 |
|----|------|------|
| § 1 | 三个反爻 + involution + commutativity | `dong`/`hua`/`bian`，`dong_dong` 等 6 定理 |
| § 2 | 错 = dong ∘ hua ∘ bian | `cuo_eq_compose` |
| § 3 | 乾之 8 元轨道（八卦由三个反爻全覆盖） | `dong_qian` 至 `dong_hua_bian_qian` 共 8 |
| § 4 | Cayley 图：simply transitive on T_3 | `transform_correct`、`bagua_intercommunication`、`bagua_intercommunication_bounded`（Hamming ≤ 3） |
| § 5 | 合（he）三种投影 + 归一 | `heShang`/`heZhong`/`heXia`、`guiyi`、`guiyi_universal` |
| § 6 | 分（fen）+ 合分逆 (he ∘ fen = id) | `fenToTrigram`、`heShang_fenToTrigram` 等 |
| § 7 | 重（chong）= Hexagram.oplus 别名 | `chong` |
| § 8 | 生生 inductive 结构 + Trigram 同构 | `Sheng`、`Sheng.toTrigram_ofTrigram` 等 |
| § 9 | 5 最小算子集 + 完备性 | `MinimalOps`、`canonicalOps`、`canonical_complete` |
| § 10 | 大循环 TaiJi → Trigram → TaiJi | `grandCycle`、`grandCycle_returns` |

### 完备性主定理

```lean
theorem bagua_algebra_complete :
    (∀ a b : Trigram, ∃ f : Trigram → Trigram, f a = b)         -- (a) 互通
    ∧ (∀ t : Trigram, guiyi t = ())                              -- (b) 归一
    ∧ (∀ t : Trigram, Trigram.cuo t = dong (hua (bian t)))       -- (c) 错 = 三反复合
    ∧ (∀ s : SiXiang, ∀ y : Yao, heShang (fenToTrigram s y) = s) -- (d) 合分逆
    ∧ (∀ y1 y2 y3 : Yao, grandCycle y1 y2 y3 = ())               -- (e) 大循环
```

五条断言由 `⟨bagua_intercommunication, guiyi_universal, cuo_eq_compose, heShang_fenToTrigram, grandCycle_returns⟩` 直接构造，每条皆有具体实现。

### 命名约定

Lean 标识符用 ASCII（与 `Yi.lean` 风格一致），中文落字仅在注释与文档：

| 中文 | Lean 标识 | 类型 |
|------|----------|------|
| 动 | `dong` | `Trigram → Trigram` |
| 化 | `hua` | `Trigram → Trigram` |
| 变 | `bian` | `Trigram → Trigram` |
| 合 | `heShang` / `heZhong` / `heXia` / `heToYi` / `heToTaiji` | (各层) |
| 分 | `fenToYi` / `fenToSiXiang` / `fenToTrigram` | (各层) |
| 归一 | `guiyi` | `Trigram → Unit` |
| 重 | `chong` | `Trigram → Trigram → Hexagram` |
| 生生 | `Sheng` | `Nat → Type`（inductive） |

### 与 Yi.lean 的接口

- 复用 Yi.lean 之 `Yao`、`Trigram`、`Hexagram`、`Trigram.cuo`、`Hexagram.oplus`
- 增量添加：(Z/2)³ 单位生成元、纵向 he/fen、归一、生生 inductive、5-算子结构
- 不修改 Yi.lean 任何已证定理

---

## 七、群论刻画总结

| 层 | 集合 | 横向群 (Z/2)ⁿ | 横向生成元 | 纵向算子（升 / 降） | 派生算子 | 群作用 |
|---|------|--------------|----------|----------------|---------|-------|
| 太极 T₀ | Unit | trivial | — | 生生 ↑（自指） | — | trivial |
| 两仪 T₁ | Bool | Z/2 | ⟨反⟩ | 合 ↑ / 分 ↓ | — | simply transitive |
| 四象 T₂ | Bool² | (Z/2)² | ⟨反_y₁, 反_y₂⟩ | 合 ↑ / 分 ↓ | — | simply transitive |
| **八卦 T₃** | **Bool³** | **(Z/2)³** | **⟨动, 化, 变⟩** | **合 ↑ / 分 ↓ ; 重 → T₆** | **错 = 动∘化∘变（在群内）；综 = 位置反序（不在群内）** | **simply transitive** |
| 64 卦 T₆ | Bool⁶ | (Z/2)⁶ | 6 反爻（内 3 + 外 3） | chong = 内 ⊕ 外 ↑ ; innerTrigram / outerTrigram ↓ | 错_hex（在 (Z/2)⁶ 内）；综_hex / 互（hu）/ 之（变卦）/ V₄ 群（皆有外结构） | simply transitive |

**关键结论**：
- 每层之横向群 = 该层之 (Z/2)ⁿ，**simply transitive**——故任两态可由反爻序列达到
- 纵向算子（合 / 分 / 重）非群元，但与横向群**兼容**（"反 ∘ 合 = 合 ∘ 反"在保留爻上）
- 综 / 互 / 之 等**不在 flip 群内**，需扩张至超八面体群 $B_n = (\mathbb{Z}/2)^n \rtimes S_n$ 或更大
- 加上纵向即得**完整的归一+互通**双向算子系统

---

## 八、与既有文档之接口

| 文件 | 关系 |
|------|-----|
| `D_算子代数.md` | 本文之扩展：D 给类型论框架，本文给具体群结构与单字落地 |
| `A_经典易传.md` | 本文之「错／综」即 A 之传统术语之精确化 |
| `B_六征体系.md` | 三个反爻可对应六征三对之「极性切换」 |
| `C_实虚史真.md` | 横向群之三 axes 即 modal/史/真假之极性切换 |
| `六表_实虚史真/表六` | 64 卦层之 192 格即本文 $\mathbb{B}^6 \times $ 时态 |
| `formal/SSBX/MonadDAG.md` | 11 个单字算子可注册为 MonadDAG 之新原始算子（与现有 5 个互校） |

---

## 九、最小可用配置

若仅取**最少必要**算子以同时满足「八卦互通」+「归一」：

$$\boxed{\{\,\text{变}, \text{化}, \text{动}, \text{合}, \text{生生}\,\}}$$

**5 个单字算子**：
- 3 个反爻（变／化／动）→ 横向 (Z/2)³ 互通
- 1 个合 → 纵向归一
- 1 个生生（Y）→ 太极层不动点 / 重启生成

此 5 算子集**完整且最小**，正合 MonadDAG 之「5 原始算子」之数（虽未必字面对应）。

---

## 九 · 半 · 道-理二分申明

> 本 G 文件描述之**算子代数**属**理层**——即可形式化、可入 Lean 的 r.e. 系统。
> **但** 5 最小算子之「**生生**」承担**道层**之自指——`Sheng : ℕ → Type` 是 Lean 之**类型族**（kind-level），非任何具体类型之居民。

| 本文之 | 属 |
|---|---|
| (Z/2)³ 群结构、合 / 分 / 重 算子、错 / 综 派生 | **理** |
| 5 最小算子集 `{变, 化, 动, 合, 生生}` 之**理用部分**（变 / 化 / 动 / 合）| **理** |
| 「生生」之元层语义（Y combinator / `Sheng` 自指）| **道** |
| `bagua_algebra_complete` 主定理（道证理之完备性元命题）| **道** |

详见 [`J_理之不完备_哥德尔在192.md`](J_理之不完备_哥德尔在192.md) §一 之精确二分定义；
集中陈述见 [`K_完备性审计.md`](K_完备性审计.md) §三。

> **关键**：5 最小算子之**完备**仅在**理层**（八卦互通 + 归一 + 错分解）；
> 在**道层**之"完备" 属哥德尔不可能（参 J §四）——故"生生"是项目对此不可能之**主动响应**：永不归零之 Y 不动点。

---

## 十、与「最终回到一」之闭环

```
   Unit ──分_b₁──→ Bool ──分_b₂──→ Bool² ──分_b₃──→ Bool³ ──重(_, t')──→ Bool⁶
    ↑                                                                       │
    │                                                                       │
    └────────────── 归一 = 合_n ∘ 合_{n-1} ∘ ... ∘ 合_1（共 n 次）─────────────┘
                                
   横向：每层之内由反爻群互通 (Z/2)^n
```

具体到八卦层（T₃）之大循环：

$$\text{guiyi} \circ \text{fenTo}_3 \circ \text{fenTo}_2 \circ \text{fenTo}_1 : \mathrm{Unit} \to \mathrm{Unit}$$

即 BaguaAlgebra.lean 之 `grandCycle y₁ y₂ y₃ = ()`（已机器验证 `grandCycle_returns`）。

延伸至 64 卦层（T₆）之大循环：

$$\text{guiyi}_6 \circ (\text{重} \text{ on two Trigrams}) \circ \cdots \circ \text{fenTo}_1 = \text{id}_{\mathrm{Unit}}$$

此即**生生不息**之大循环：**生 → 展 → 归 → 生 → ...** 永动不绝。
注：此处"生生"意指连续之 fenTo 序列，等价于 inductive `Sheng : Nat → Type` 之 `step` 链。
