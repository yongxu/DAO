# v4-foundation — The $R_0$–$R_8$ Root Tower

> **文 形式语言** · Foundation Note
> $R_0$ through $R_8$ as the root layers; each $R_N$ has its own structure and meaning
> Companion to: `r4.md` (R_4 专题), `r8.md` (R_8 专题), `wen-algebra.md` (v0.6 tower algebra)
> **Single formal language**: Lean 4 + Mathlib
> v0.5

**Changelog**

- v0.5 — 自我 review 修订: §13.3 加 R_2 特例注 (Sp(2,2) = GL(2,2) 巧合相等); §14.1 修正错误的 "in tensor view" 标注 (squaring tower 通过 direct sum); §14.2 性质继承说明澄清 (direct sum 自然 lift, tensor 产生大得多的层). 标注 Lean 唯一形式语言 (Clojure 已弃用).
- v0.4 — **重大视角矫正**：弃用「𝕏 中心」与「𝕐 中心」的单层中心化论述。$R_0$–$R_8$ 作为根集合，每层各有独特结构。**$R_4$ 与 $R_8$ 是双中心**（$R_4$ 为数学最小完整单元；$R_8 = R_4^2$ 为含下层的 ceiling）。Squaring 子塔 $R_1 \to R_2 \to R_4 \to R_8$ 显式建立。$\mathbb{X}, \mathbb{Y}$ 符号弃用
- v0.3 — 二进制占位符规范；{oo, xx} 三合一刻画；象单层 11 节
- v0.2 — 四套并行命名落地
- v0.1 — 初稿

---

## 0. 范围与约定 · Scope and Conventions

### 0.1 文档范围

本文档是 文 形式语言的**根层规范**。它确立：

1. **$R_0$ 到 $R_8$ 是文 algebra 的根层集合**（9 层）
2. **每个 $R_N$ 都有其独特结构、形式与哲学意义**——不存在单一「中心层」
3. **$R_4$ 与 $R_8$ 是双重点**：$R_4$ 是数学最小完整单元（rank 分层 + endomorphism 自封闭首现）；$R_8 = R_4^2$ 是 ceiling（含 $R_0$–$R_7$ 所有作为 $\mathbb{F}_2$-子空间；多种常用概念定居于此）
4. **Squaring 子塔 $R_1 \to R_2 \to R_4 \to R_8$**：每层 = 上层²。这是 R-族内的自相似自然倍增
5. **$N > 8$ 由 $R_0$–$R_8$ 构造**：高层 R_N 经直和、张量、Hom 由根层组合得到
6. **三层 bilinear 精细度**（Layer 0/1/2: dot, σ, q + Arf）在所有偶 $N$ 上一致定义

### 0.2 命名约定

**Notation**: $R_N$ 表示第 $N$ 层；$R$ 可视为 layer-root 的通用记号。

$$R_N := \mathbb{F}_2^N, \qquad |R_N| = 2^N$$

**Element representation**: $R_N$ 的元素表示为长度 $N$ 的 **o/x 字符串**。约定 $\mathrm{o} = 0$, $\mathrm{x} = 1$。

| $N$ | $|R_N|$ | 元素示例 |
|-----|---------|----------|
| 0 | 1 | $\varepsilon$ 或 $\cdot$ |
| 1 | 2 | $\mathrm{o}, \mathrm{x}$ |
| 2 | 4 | $\mathrm{oo}, \mathrm{ox}, \mathrm{xo}, \mathrm{xx}$ |
| 3 | 8 | $\mathrm{ooo}, \mathrm{oox}, \ldots, \mathrm{xxx}$ |
| 4 | 16 | $\mathrm{oooo}, \mathrm{ooox}, \ldots, \mathrm{xxxx}$ |
| 8 | 256 | $\mathrm{oooooooo}, \ldots, \mathrm{xxxxxxxx}$ |

**字符约定弃用**：本版**不**为元素或层赋予具体汉字或英文实指 (Image / Frame / Hexagram 等都退场)。所有命名以纯结构记号表达。

### 0.3 视角原则

为避免重复历史错位（v0.1–v0.3 经历过 𝕏 中心化、𝕐 中心化的偏移），本版采纳以下原则：

1. **无单层中心**：每个 $R_N$ 都是独立的代数对象，有其特有结构
2. **双焦点 $R_4$ + $R_8$**：但具体论述深度上，$R_4$ 与 $R_8$ 获得最大篇幅
3. **根集合 $R_0$–$R_8$ 作为论证范围**：可在此范围内证明所需性质；高层从此构造
4. **外部传统对应** (Pauli, Yi, Galois 等) 严格作为 application-layer，详见 §10

### 0.4 与 wen-algebra 的边界

| `wen-algebra.md` (待 v0.6 更新) | `v4-foundation.md` (本文档) |
|---|---|
| $\mathbb{X}^n$-塔 (旧名) 的代数完备性 | $R_0$–$R_8$ 根层规范 |
| Tower-level dot product 与 LIC | 单层 bilinear 形式定义 |
| Hom = Mat 表示 | $R_4$ = End($R_2$) 单层等同 |
| 接口层与 surface 暴露规则 | 每 $R_N$ 的内部结构 |

两文档**配套使用**：foundation 给根层的结构事实，algebra 用这些根层构建上层 tower。

### 0.5 形式语言

**Lean 4 + Mathlib 是唯一形式语言**（v0.5 update：Clojure 已弃用）：

- **证明轨** (Lean 4 + Mathlib)：每 $R_N$ 的结构性断言可机器验证
- **解释/编译轨** (Lean 4 computable defs)：$R_N$ 作为 IR primitive，按 N 参数化，运行通过 `decide` / `native_decide`

详见 §16.

---

## 1. $R_N$-族的整体视图 · Overview of the R-Family

### 1.1 9 层 $R_0$–$R_8$ 总览

| 层 | 大小 | $\mathbb{F}_2$-维 | 是否偶 | Bilinear layers | $|{\mathrm{Aut}}|$ | 关键特征 |
|---|------|-------------------|--------|----------------|---------------------|---------|
| $R_0$ | 1 | 0 | — | trivial | 1 | 平凡 |
| $R_1$ | 2 | 1 | odd | Layer 0 only | 1 | 原始 bit |
| $R_2$ | 4 | 2 | **even** | Layer 0/1/2 | 6 | Klein-4，双轴，三合一 |
| $R_3$ | 8 | 3 | odd | Layer 0 only | 168 | Fano 平面 PG(2, 2) |
| **$R_4$** ★ | 16 | 4 | **even** | Layer 0/1/2 | 20160 | 数学最小完整单元、End($R_2$) |
| $R_5$ | 32 | 5 | odd | Layer 0 only | 9,999,360 | 31 (Mersenne) |
| $R_6$ | 64 | 6 | **even** | Layer 0/1/2 | 20,158,709,760 | $R_2 \otimes R_3$ 等多重分解 |
| $R_7$ | 128 | 7 | odd | Layer 0 only | $1.64 \times 10^{14}$ | Hamming(7,4) 完美码 |
| **$R_8$** ★ | 256 | 8 | **even** | Layer 0/1/2 | $5.35 \times 10^{18}$ | byte / ceiling / $R_4^2$ |

★ = 重点延伸层。

### 1.2 三个观察 · Three Observations

**Observation 1 (Bilinear layers 与奇偶)**：

- **奇 $N$** ($R_1, R_3, R_5, R_7$): 只支持 Layer 0 (Boolean dot)
- **偶 $N$** ($R_2, R_4, R_6, R_8$): 全部 Layer 0/1/2 (含 σ 与 q + Arf)
- 这是 char 2 下 symplectic form 要求偶维的几何事实

**Observation 2 (Mersenne 与 Hamming)**：

- $|R_5| - 1 = 31$，$|R_7| - 1 = 127$，都是 Mersenne 素数
- $R_7$ 是 Hamming(7,4) 完美码的自然居所
- 这些数论事实使 $R_5, R_7$ 在编码理论中独特

**Observation 3 (Aut 阶增长)**：

$|\mathrm{Aut}(R_N)| = |\mathrm{GL}(N, \mathbb{F}_2)| = \prod_{k=0}^{N-1} (2^N - 2^k)$

阶按 $N$ 接近 $2^{N^2}$ / (some polynomial) 速率超指数增长——根层之间复杂度跨越极大。

### 1.3 Squaring 子塔 · The Squaring Sub-Tower

$R_N$-族内有一个特别自然的子塔：

$$R_1 \xrightarrow{\;(\cdot)^2\;} R_2 \xrightarrow{\;(\cdot)^2\;} R_4 \xrightarrow{\;(\cdot)^2\;} R_8 \xrightarrow{\;(\cdot)^2\;} (R_{16}, \ldots)$$

每层 = 上层²（cardinality 平方，$\mathbb{F}_2$-维倍增）：

$$|R_1| = 2, \quad |R_2| = 4 = 2^2, \quad |R_4| = 16 = 4^2, \quad |R_8| = 256 = 16^2$$

**这是 $R_0$–$R_8$ 内部的「自相似倍增」结构**。

为什么 squaring：

- $R_{2N} = R_N \otimes_{\mathbb{F}_2} R_N$（张量积）
- $R_{2N} \cong \mathrm{End}_{\mathbb{F}_2}(R_N)$ 当且仅当某些 dimension 条件成立——具体地，$R_4 = \mathrm{End}(R_2)$，$R_{16} = \mathrm{End}(R_4)$（但 $R_8 \neq \mathrm{End}(R_4)$，因 End($R_4$) over $\mathbb{F}_2$ 是 $4 \times 4$ matrix space = $R_{16}$）
- $R_8 = R_4 \otimes R_4 = R_4^2$ 在张量意义上

Squaring 子塔的层数从 $R_1$ 起每翻一倍记号下标：1, 2, 4, 8, (16, 32, ...). $R_0$–$R_8$ 包含此塔的前 4 层加 $R_0$。

### 1.4 直和分解 · Direct-Sum Decomposition

任何 $R_N$ for $N \in \{3, 5, 6, 7\}$（squaring tower 外的根层）可由 squaring tower 直和：

- $R_3 = R_1 \oplus R_2$（二进制 3 = 1 + 2）
- $R_5 = R_1 \oplus R_4$（5 = 1 + 4）
- $R_6 = R_2 \oplus R_4$（6 = 2 + 4）
- $R_7 = R_1 \oplus R_2 \oplus R_4$（7 = 1 + 2 + 4）

由二进制展开 $N = \sum_i 2^{e_i}$（不同 $e_i$）：

$$R_N \cong \bigoplus_i R_{2^{e_i}}$$

——squaring tower **$R_1, R_2, R_4$ 是 $R_0$–$R_7$ 的「生成基」**（在直和意义下）。$R_8 = R_8$ 自身是 squaring tower 的下一层，不可由更小的 squaring tower 元素直和得到。

### 1.5 $R_8$ 作为根层 ceiling

$R_8$ 在 $R_0$–$R_8$ 中享有 ceiling 地位：

1. **$R_0$–$R_7$ 全部嵌入 $R_8$**：$R_N \hookrightarrow R_8$ for $N \leq 7$（取前 $N$ 坐标的子空间）
2. **任何 $R_N$ for $N \in \{0, \ldots, 7\}$ 是 $R_8$ 的子结构**（由 §1.4 直和分解 + 嵌入）
3. **常用编码尺度集中于 $R_8$**：byte (256 元), UTF-8 single byte, $\mathrm{GF}(256)$ (用于 AES 等), DNA/RNA 多重编码尺度
4. **从 $R_0$–$R_8$ 可构造任意 $R_N$ for $N > 8$**：$R_N = R_8 \oplus R_{N-8}$，递归直到 $N-k \leq 8$

由此**根层范围 $R_0$–$R_8$ 是充分的**：所有需要的代数事实可在此范围内陈述与证明，更大层由直和/张量构造，性质继承。

---

## 2. $R_0$ — The Trivial Layer

### 2.1 定义

$R_0 = \{\varepsilon\}$（长度 0 字符串集合，亦记 $\{\cdot\}$）。 $|R_0| = 1 = 2^0$.

### 2.2 结构

- **群结构**：平凡群 $\{e\}$
- **$\mathbb{F}_2$-vector space**：0 维
- **$\mathrm{Aut}(R_0)$**：平凡，单元
- **Bilinear forms**：无（dimension 0 的退化情形）
- **子群**：仅自身

### 2.3 角色

$R_0$ 作为 R-族的「底」(bottom)：

- 它是任何 $R_N$ 的子结构（trivial subspace）
- 它是任何 $R_N$ 直和分解的「单位」($R_0 \oplus R_N = R_N$)
- 它是 $R_N \otimes R_0 = R_0$ 的「零」(在张量意义)

哲学：$R_0$ 标记「无结构」的起点。所有上层结构由此向上构造。

---

## 3. $R_1$ — The Bit

### 3.1 定义

$R_1 = \{\mathrm{o}, \mathrm{x}\}$. $|R_1| = 2$.

### 3.2 群结构

$R_1 = \mathbb{Z}/2 = \mathbb{F}_2$ 作为 abelian 群。加法表：

| $+$ | o | x |
|-----|----|----|
| o | o | x |
| x | x | o |

唯一非恒等元 $\mathrm{x}$ 是 self-inverse: $\mathrm{x} + \mathrm{x} = \mathrm{o}$.

### 3.3 $\mathbb{F}_2$-vector space

$R_1$ 是 1-维 $\mathbb{F}_2$-向量空间。典则基：$\{\mathrm{x}\}$. 每元素唯一表示为 $c \cdot \mathrm{x}$ for $c \in \{\mathrm{o}, \mathrm{x}\}$.

### 3.4 $\mathrm{Aut}(R_1)$

$\mathrm{Aut}_{\mathbb{F}_2}(R_1) = \mathrm{GL}(1, \mathbb{F}_2)$. 

$1 \times 1$ 可逆 $\mathbb{F}_2$ 矩阵只有 $[1]$. 所以 $|\mathrm{Aut}(R_1)| = 1$.

注：作为**集合**的双射 $R_1 \to R_1$ 有 2 个 ($\mathrm{id}$ 与 swap)。但 swap 把 $\mathrm{o}$ 映到 $\mathrm{x}$——不保单位元 $\mathrm{o}$——故不是群同态。**$R_1$ 没有非平凡 group automorphism**。

### 3.5 Bilinear form

唯一可能的 bilinear form：$\langle u, v \rangle = u \cdot v$（$\mathbb{F}_2$ 乘法 = AND）。

| $\langle \cdot, \cdot \rangle$ | o | x |
|-----|----|----|
| o | 0 | 0 |
| x | 0 | 1 |

对称、非退化。**self-pairing 零集** = $\{\mathrm{o}\}$.

$R_1$ 是奇维，**无 Layer 1 (σ)**。Char 2 下 symplectic 要求偶维。

### 3.6 子群

仅两个：$\{\mathrm{o}\}$ 与 $R_1$ 自身。无非平凡真子群。

### 3.7 哲学/结构意义

$R_1$ = **最基本的二元区分**：

- 存在 / 不存在
- 真 / 假
- 0 / 1
- 是 / 非

它是任何分类、判断、命题的最简单代数体现。也是 Shannon 信息论的最小信息单元 (1 bit)。

在 v0.1–v0.3 框架中 $R_1$ 曾被作为「half-image」边缘化，**v0.4 矫正：$R_1$ 是有自身独立地位的根层**。

### 3.8 与其他层的关系

- $R_1 \oplus R_1 = R_2$（两个 bit 拼成 image）
- $R_1 \oplus R_4 = R_5$
- $R_1 \oplus R_2 \oplus R_4 = R_7$
- $R_1 \hookrightarrow R_8$（subspace embedding）
- $R_1 \otimes R_N = R_N$（张量单位）

---

## 4. $R_2$ — The Klein-Four / Pair Layer

### 4.1 定义

$R_2 = \{\mathrm{oo}, \mathrm{ox}, \mathrm{xo}, \mathrm{xx}\}$. $|R_2| = 4$.

每元素是长度 2 字符串 $u = u_1 u_2$ where $u_i \in \{\mathrm{o}, \mathrm{x}\}$. 

约定坐标：$u_\alpha := u_1$, $u_\beta := u_2$. 即第一字符 = α，第二字符 = β。

### 4.2 群结构

$R_2 = \mathbb{F}_2 \times \mathbb{F}_2 = \mathbb{Z}/2 \times \mathbb{Z}/2$ = **Klein 四元群** $V_4$. 

群乘法（= component-wise XOR）：

| $+$ | oo | xo | ox | xx |
|----|----|----|----|----|
| oo | oo | xo | ox | xx |
| xo | xo | oo | xx | ox |
| ox | ox | xx | oo | xo |
| xx | xx | ox | xo | oo |

性质：

- 阶 4
- 阿贝尔
- Exponent 2（所有元素 self-inverse）
- 单位元 $\mathrm{oo}$
- 3 个非平凡 $\mathbb{Z}/2$ 子群（§4.5）

### 4.3 $\mathbb{F}_2$-vector space

$R_2 = \mathbb{F}_2^2$. 典则基：

- $e_\alpha = \mathrm{xo} = (1, 0)$
- $e_\beta = \mathrm{ox} = (0, 1)$

每 $v \in R_2$ 唯一分解 $v = v_\alpha e_\alpha + v_\beta e_\beta$.

### 4.4 线性形式与对角线性形式

$R_2$ 上 $\mathbb{F}_2$-线性形式 ($R_2 \to \mathbb{F}_2$) 共 4 个：

1. 零形式 $0(v) = 0$
2. α-投影 $\pi_\alpha(v) = v_\alpha$
3. β-投影 $\pi_\beta(v) = v_\beta$
4. **对角形式** $L(v) := v_\alpha + v_\beta$ ★

$L$ 在 §4.7 三合一刻画中起关键作用。$\ker L = \{\mathrm{oo}, \mathrm{xx}\}$.

### 4.5 子群结构

$R_2$ 的所有子群：

| 子群 | 阶 | 元素 |
|------|----|----|
| $\{\mathrm{oo}\}$ | 1 | 平凡 |
| $\{\mathrm{oo}, \mathrm{xo}\}$ | 2 | α-axis |
| $\{\mathrm{oo}, \mathrm{ox}\}$ | 2 | β-axis |
| $\{\mathrm{oo}, \mathrm{xx}\}$ | 2 | **diagonal** ★ |
| $R_2$ | 4 | 全 |

5 个子群。三个非平凡 $\mathbb{Z}/2$ 子群中，$\{\mathrm{oo}, \mathrm{xx}\}$ 享三合一特权（§4.7）。

**辨析**：$\{\mathrm{xo}, \mathrm{ox}\}$ **不是**子群（不含单位元 $\mathrm{oo}$）。它是 $\{\mathrm{oo}, \mathrm{xx}\}$ 的非平凡 coset，是商群 $R_2 / \{\mathrm{oo}, \mathrm{xx}\}$ 的另一等价类。

### 4.6 三层 Bilinear 形式

#### Layer 0 — Boolean dot product

$$\langle u, v \rangle := u_\alpha v_\alpha + u_\beta v_\beta \in \mathbb{F}_2$$

性质：对称、$\mathbb{F}_2$-双线性、非退化、**非 alternating**。

| $\langle \cdot, \cdot \rangle$ | oo | xo | ox | xx |
|---|----|----|----|----|
| oo | 0 | 0 | 0 | 0 |
| xo | 0 | 1 | 0 | 1 |
| ox | 0 | 0 | 1 | 1 |
| xx | 0 | 1 | 1 | 0 |

Self-pairing 零集 = $\{\mathrm{oo}, \mathrm{xx}\}$ — 即 diagonal subgroup.

#### Layer 1 — Symplectic form σ

$$\sigma(u, v) := u_\alpha v_\beta + u_\beta v_\alpha \in \mathbb{F}_2$$

性质：对称、双线性、**alternating** ($\sigma(v, v) = 0$ ∀ $v$)、非退化。

| $\sigma$ | oo | xo | ox | xx |
|---|----|----|----|----|
| oo | 0 | 0 | 0 | 0 |
| xo | 0 | 0 | 1 | 1 |
| ox | 0 | 1 | 0 | 1 |
| xx | 0 | 1 | 1 | 0 |

#### 分解定理

$$\boxed{\;\langle u, v \rangle = \sigma(u, v) + L(u) \cdot L(v)\;}$$

证：直接展开 (§v0.3 §4.3 已给详证). ∎

**结构含义**：$\langle\cdot,\cdot\rangle$, $\sigma$, $L$, $\{\mathrm{oo}, \mathrm{xx}\}$-subgroup **是同一结构事实的四个侧面**。

#### Layer 2 — Quadratic refinements

$$q_0(v) := v_\alpha \cdot v_\beta, \qquad q_1(v) := L(v) + q_0(v) = v_\alpha + v_\beta + v_\alpha v_\beta$$

值表：

| $v$ | $q_0(v)$ | $q_1(v)$ |
|---|---|---|
| oo | 0 | 0 |
| xo | 0 | 1 |
| ox | 0 | 1 |
| xx | **1** | 1 |

性质：$q_0, q_1$ 都是 σ 的 quadratic refinement。

#### Arf 不变量

$$\mathrm{Arf}(q) := q(e_\alpha) \cdot q(e_\beta) = q(\mathrm{xo}) \cdot q(\mathrm{ox})$$

- $\mathrm{Arf}(q_0) = 0 \cdot 0 = \mathbf{0}$
- $\mathrm{Arf}(q_1) = 1 \cdot 1 = \mathbf{1}$

两类 quadratic refinements 完备分类（在 Arf 意义下）。

### 4.7 $\{\mathrm{oo}, \mathrm{xx}\}$ 三合一刻画

> **定理 4.7**：在 $R_2$ 中，$\{\mathrm{oo}, \mathrm{xx}\}$ 是唯一同时具备以下三性质的非平凡子群：
> 
> 1. **同态保护**：保 contrapositive 同态
> 2. **几何 isotropy**：$\langle\cdot,\cdot\rangle$ self-pairing 零集
> 3. **线性 kernel**：$\ker L$

三者同集合，三种刻画互为代数等价。

证明梗概：

- (2) ⟺ (3): self-pairing $\langle v, v \rangle = v_\alpha + v_\beta = L(v)$. 所以 $\{v: \langle v, v \rangle = 0\} = \ker L$.
- (1) ⟺ (3): contrapositive 是命题 $p \Rightarrow q$ ↦ $\neg q \Rightarrow \neg p$ 的同态。在 $R_2$ 中作为「双对偶」: 同时 flip α 与 β。这个映射 $v \mapsto v + \mathrm{xx}$ 保 $\{\mathrm{oo}, \mathrm{xx}\}$（作为 coset）且仅此非平凡 $\mathbb{Z}/2$ 子群被保。

详细推导见 v0.3 §5。

### 4.8 $\mathrm{Aut}(R_2)$

$\mathrm{Aut}(R_2) = \mathrm{GL}(2, \mathbb{F}_2) \cong S_3$, 阶 6.

每个 $\xi \in \mathrm{Aut}(R_2)$ 必固定 $\mathrm{oo}$，在 $\{\mathrm{xo}, \mathrm{ox}, \mathrm{xx}\}$ 上作置换。6 个 Aut 元素 = $\{xo, ox, xx\}$ 的 6 个置换。

| Aut 元素 | 矩阵 | 在 $\{xo, ox, xx\}$ 的作用 | 阶 |
|---|---|---|---|
| $\mathrm{id}$ | $\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ | (固定) | 1 |
| swap | $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ | (xo ↔ ox), fix xx ★ | 2 |
| fix-xo | $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ | (ox ↔ xx), fix xo | 2 |
| fix-ox | $\begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$ | (xo ↔ xx), fix ox | 2 |
| rot$_+$ | $\begin{pmatrix} 0 & 1 \\ 1 & 1 \end{pmatrix}$ | (xo → ox → xx → xo) | 3 |
| rot$_-$ | $\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$ | (xo → xx → ox → xo) | 3 |

**Stab$(\mathrm{xx}) = \{\mathrm{id}, \mathrm{swap}\}$** = stabilizer of $\{\mathrm{oo}, \mathrm{xx}\}$ subgroup = 保 $\langle\cdot,\cdot\rangle$ 的 Aut-子群（详 §4.9）。

### 4.9 Preservation Hierarchy

| 结构 | 保它的 Aut 子群 | 阶 |
|---|---|---|
| 群结构、σ、$q_1$ | 全 $S_3$ | 6 |
| $\{\mathrm{oo}, \mathrm{xx}\}$、$\langle\cdot,\cdot\rangle$、$q_0$ | Stab(xx) | 2 |
| 个别坐标 ($\alpha$ vs $\beta$) | $\{\mathrm{id}\}$ | 1 |

三层 filtration $S_3 \supseteq \mathbb{Z}/2 \supseteq \{1\}$。

### 4.10 $R_2$ 的角色

$R_2$ 是**首层非平凡复合层**：

- 含双轴 (α, β) 的最简结构
- Aut 首次出现非平凡 ($S_3$，6 元)
- Bilinear 三层 (Layer 0/1/2) 首次完整定义
- 三合一刻画为 $\{\mathrm{oo}, \mathrm{xx}\}$ 提供深层结构地位

但 $R_2$ 仍**缺少 rank stratification** — 所有 3 个非恒等元在 $S_3$ 下共轭。这一点要到 $R_4$ 才出现。

---

## 5. $R_3$ — Fano Plane Layer

### 5.1 定义

$R_3 = \mathbb{F}_2^3$. $|R_3| = 8$.

元素：长度 3 字符串 $u = u_1 u_2 u_3$ ∈ $\{\mathrm{o}, \mathrm{x}\}^3$.

8 元：ooo, oox, oxo, oxx, xoo, xox, xxo, xxx.

### 5.2 群与 vector space 结构

$R_3 = (\mathbb{Z}/2)^3$, abelian, exponent 2, 阶 8.

3-维 $\mathbb{F}_2$-vector space. 典则基：$\{e_1, e_2, e_3\}$ where $e_i$ has 1 in position $i$, 0 elsewhere.

7 个非零元，每个 self-inverse.

### 5.3 子群

$R_3$ 的 $\mathbb{F}_2$-subspaces：

- dim 0: 1 (trivial)
- dim 1: $\binom{3}{1}_2 = 7$（每个 $\mathbb{Z}/2$ 子群对应一个非零向量）
- dim 2: $\binom{3}{2}_2 = 7$ (hyperplanes; 每个是 kernel of 一个非零线性形式)
- dim 3: 1 (whole)

共 16 个子群。

### 5.4 $\mathrm{Aut}(R_3)$

$$|\mathrm{Aut}(R_3)| = |\mathrm{GL}(3, \mathbb{F}_2)| = (8-1)(8-2)(8-4) = 7 \cdot 6 \cdot 4 = 168$$

$\mathrm{GL}(3, \mathbb{F}_2) \cong \mathrm{PSL}(2, 7)$ — 一个著名的 simple group of order 168。

它作用 transitively 在 7 个非零元上、也 transitively 在 7 个 hyperplanes 上。

### 5.5 Fano 平面 PG(2, 2)

$R_3$ 的**射影空间** $\mathrm{PG}(2, 2)$ 是 **Fano 平面**——一个 finite projective plane with 7 points and 7 lines, each line containing 3 points, each point on 3 lines.

构造：把 7 个非零元作为 points；每对非零元 $u, v$ 决定一条 line $\{u, v, u + v\}$（3-element subset of 非零元，对应 2-dim subspace minus 0）。

性质（标准 incidence axioms）：

- 任两 points 决定唯一 line
- 任两 lines 在唯一 point 相交
- 存在 4 points 中无 3 共线

Fano 平面是最小的 non-trivial projective plane，与 $R_3$ 的群结构紧密绑定。

### 5.6 Bilinear form

dot product on $R_3$:

$$\langle u, v \rangle := u_1 v_1 + u_2 v_2 + u_3 v_3 \in \mathbb{F}_2$$

对称、非退化。但奇维 ⇒ **无 Layer 1 (σ)**、**无 Layer 2 (q + Arf)** 在自然意义下。

注：$R_3$ 上可定义有「准 alternating」二次形式，但需 break symmetry，不是自然的。

### 5.7 与其他根层的关系

- $R_3 \cong R_1 \oplus R_2$（任一非平凡 dim-1/dim-2 直和分解）
- $R_3 \hookrightarrow R_4, R_5, \ldots, R_8$
- $R_3$ 不是 squaring tower 成员（3 不是 2 的幂）

### 5.8 哲学/结构意义

$R_3$ 是**最小有趣的射影几何**——Fano 平面。它出现在：

- finite geometry 的开端
- error-correcting codes（Steiner systems 等）
- 量子信息中的 mutually unbiased bases
- representation theory of small groups

$R_3$ 不在 squaring tower，但作为根层有独立结构地位。

---

## 6. $R_4$ — The Minimum Complete Unit ★

> **重点层 1**：$R_4$ 是数学意义上的**最小完整单元** (minimum complete unit)。从 $R_4$ 开始，代数结构具备 rank 分层、群作用嵌入、endomorphism 自封闭三大特征。

### 6.1 定义

$R_4 = \mathbb{F}_2^4$. $|R_4| = 16$. 

元素：长度 4 字符串。例：$\mathrm{ooxx}, \mathrm{xxoo}, \mathrm{xoxo}, \ldots$

### 6.2 三种结构身份 · Three Structural Identities

$R_4$ 在三种意义上同构于同一 16-元对象：

1. **$\mathbb{F}_2^4$**：4-维 $\mathbb{F}_2$-vector space (flat view)
2. **$R_2 \otimes_{\mathbb{F}_2} R_2 = R_2^2$**：双 $R_2$ 张量（pair-of-images）
3. **$\mathrm{End}_{\mathbb{F}_2}(R_2) = \mathrm{Mat}_{2 \times 2}(\mathbb{F}_2)$**：$R_2$ 的全体线性自同态

这三种 view 是 $R_4$ 的不同**呈现**而非不同对象。它们共生：每个 $R_4$ 元素 $w \in R_4$ 既是 (1) 一个 4-bit 向量，又是 (2) 一对 $R_2$ 元素，又是 (3) 一个 $R_2 \to R_2$ 的线性映射。

### 6.3 群结构

$R_4 = (\mathbb{Z}/2)^4$，abelian、exponent 2、阶 16. 

群运算 = component-wise XOR（4 个坐标各独立）。

### 6.4 Vector space 与典则基

$R_4 = \mathbb{F}_2^4$. 典则基 $\{e_1, e_2, e_3, e_4\}$，对应坐标 $(w_1, w_2, w_3, w_4)$.

#### 双坐标读法

$R_4 = R_2 \otimes R_2$ 给出二级坐标：

| flat | pair-of-images $(u, v) \in R_2 \times R_2$ |
|------|-------------------------------------------|
| $w_1 w_2 w_3 w_4$ | $(w_1 w_2, w_3 w_4)$ |
| oooo | (oo, oo) |
| ooxx | (oo, xx) |
| xxoo | (xx, oo) |
| xxxx | (xx, xx) |
| oxxo | (ox, xo) |

#### Matrix 读法

$R_4 = \mathrm{Mat}_{2 \times 2}(\mathbb{F}_2)$. 每元素 $w$ 视为：

$$M_w = \begin{pmatrix} w_1 & w_2 \\ w_3 & w_4 \end{pmatrix}$$

这给出**线性映射** $R_2 \to R_2$ via $u \mapsto M_w u$.

### 6.5 Rank Stratification ★

$R_4$ 是**首层带 rank 分层**的根层。按矩阵秩分类 16 个元素：

| Rank | 数 | 描述 | 例子 |
|------|----|----|----|
| 0 | 1 | 零矩阵 | oooo |
| 1 | 9 | 退化映射（image 1-dim 或 kernel 1-dim） | oxoo, ooox, xxoo, ... |
| 2 | 6 | invertible = $\mathrm{GL}(2, \mathbb{F}_2)$ | xoox, oxxo, xoxx, oxxx, xxox, xxxo |

**注**：rank-2 6 个 = $\mathrm{GL}(2, \mathbb{F}_2) \cong S_3$. 这是 §4.8 的 $\mathrm{Aut}(R_2)$ 重现于 $R_4$ 内部！

矩阵阶分布的 rank stratification 是**$R_2$ 完全缺失**的：在 $R_2$ 中所有非恒等元都是 "rank 2" involutions, flat。$R_4$ 在结构上首次出现「分层」。

### 6.6 子群

$R_4$ 的 $\mathbb{F}_2$-subspaces 数：

$$\sum_{k=0}^{4} \binom{4}{k}_2 = 1 + 15 + 35 + 15 + 1 = 67$$

详细：

- dim 0: 1
- dim 1: 15
- dim 2: 35
- dim 3: 15
- dim 4: 1

**重要嵌入**：$R_4$ 内含 $R_2$ subspaces. dim-2 共 35 个，分两类（按 quadratic form 限制）：

- 各种「轴对齐」 $R_2$（前两坐标、后两坐标、对角等）
- 一般 $R_2$-style subspaces

值得特别注意的子群（来自 §1.4 直和 $R_4 = R_2 \oplus R_2$）：

- **左半 $R_2^{(L)}$** = $\{w : w_3 = w_4 = 0\}$ = $\{\mathrm{oooo}, \mathrm{xooo}, \mathrm{oxoo}, \mathrm{xxoo}\}$
- **右半 $R_2^{(R)}$** = $\{w : w_1 = w_2 = 0\}$ = $\{\mathrm{oooo}, \mathrm{ooxo}, \mathrm{ooox}, \mathrm{ooxx}\}$

这两个 $R_2$ 直和恢复 $R_4$.

### 6.7 $\mathrm{Aut}(R_4)$

$$|\mathrm{Aut}(R_4)| = |\mathrm{GL}(4, \mathbb{F}_2)| = (16-1)(16-2)(16-4)(16-8) = 15 \cdot 14 \cdot 12 \cdot 8 = \mathbf{20160}$$

20160 是 $A_8$ (阶 20160) 的阶。事实上 $\mathrm{GL}(4, \mathbb{F}_2) \cong A_8$ — 著名的群同构。

$A_8$ 是 alternating group on 8 letters。这给 $R_4$ 一个跨学科桥接 (combinatorics、Galois theory、Lie theory)。

### 6.8 三层 Bilinear 形式 on $R_4$

$R_4$ 是偶维，三层全部存在。

#### Layer 0 — Standard dot

$$\langle w, w' \rangle_{R_4} := \sum_{i=1}^{4} w_i w'_i \in \mathbb{F}_2$$

非退化、对称、非 alternating.

或在 $R_2 \otimes R_2$ view 下：

$$\langle (u_1, u_2), (u'_1, u'_2) \rangle = \langle u_1, u'_1 \rangle_{R_2} + \langle u_2, u'_2 \rangle_{R_2}$$

这是 $R_2$-component-wise 直和。

#### Layer 1 — Symplectic σ on $R_4$

$$\sigma_{R_4}(w, w') := w_1 w'_2 + w_2 w'_1 + w_3 w'_4 + w_4 w'_3$$

或 $R_2 \otimes R_2$ view：

$$\sigma_{R_4}((u_1, u_2), (u'_1, u'_2)) = \sigma_{R_2}(u_1, u'_1) + \sigma_{R_2}(u_2, u'_2)$$

Alternating, 非退化。

#### Layer 2 — Quadratic refinements & Arf

$$q_0^{R_4}(w) := w_1 w_2 + w_3 w_4$$

$$q_1^{R_4}(w) := L_{R_4}(w) + q_0^{R_4}(w)$$

其中 $L_{R_4}(w) = w_1 + w_2 + w_3 + w_4$.

Arf 不变量：

- $\mathrm{Arf}(q_0^{R_4}) = q_0(e_1) \cdot q_0(e_2) \cdot q_0(e_3) \cdot q_0(e_4)$ ... wait, Arf 在 $R_{2k}$ 上定义为 $\sum$ 类型，详细：

$$\mathrm{Arf}(q^{R_4}) = q^{R_4}(e_1) q^{R_4}(e_2) + q^{R_4}(e_3) q^{R_4}(e_4) \pmod 2$$

具体 $\mathrm{Arf}(q_0^{R_4}) = 0$, $\mathrm{Arf}(q_1^{R_4}) = 0$（前者显然，后者由 $L \cdot$ self contributing）.

如要 Arf-1 类的 quadratic form on $R_4$，可逐 $R_2$-block 选 $q_1$，例如 $q_{1,0}^{R_4}(w) = q_1(w_1 w_2) + q_0(w_3 w_4)$.

### 6.9 $R_4 = \mathrm{End}(R_2)$ 自封闭

> **核心事实**：$R_4$ 的 16 元 = $R_2 \to R_2$ 的全部线性映射。

把 $w \in R_4$ 视为矩阵 $M_w$（§6.4），它作用 $R_2$ 上 via $u \mapsto M_w u$。 

**16 个线性映射的分类**（§6.5 rank stratification）：

- 1 zero map (rank 0)
- 9 退化 maps (rank 1) — 包括各种 projections, shears
- 6 invertible maps (rank 2) = $\mathrm{GL}(2, \mathbb{F}_2) = \mathrm{Aut}(R_2) = S_3$

最后一点是 $R_4$ 作为「**$R_2$ 的自我描述**」的精确表达：

$$\mathrm{Aut}(R_2) \hookrightarrow R_4 \;\text{(rank-2 invertibles)}$$

$R_2$ 的所有 6 个 group automorphisms **整体内嵌**到 $R_4$ 中作为 invertible 矩阵。

### 6.10 $R_4$ 的角色 · The Significance of $R_4$

$R_4$ 是数学最小完整单元的几条具体表述：

1. **首层 rank 分层** (§6.5) — 「flat」一阶 $R_2$ 没有 rank，$R_4$ 是首层结构丰富
2. **首层 endomorphism 自封闭** — $\mathrm{End}(R_2) = R_4$ 自身在 $R$-族内
3. **首层内嵌前一层 Aut** (§6.9) — $\mathrm{Aut}(R_2)$ 作为 invertible 子集出现于 $R_4$
4. **首层有 quadratic forms 的 Arf 分类** ($R_2$ 上 Arf 0/1 是定义，但 $R_4$ 上 Arf 才有多类 contribution)
5. **首层属 squaring tower 非基** — $R_1 \to R_2 \to R_4 \to \ldots$，$R_4 = R_2^2$ 表达「自相似首层 doubling」

哲学/工程意义：

> $R_4$ 是**算法的最小完整体**。任何「需要 transformations 上 transformations」的代数结构都从 $R_4$ 开始变得 well-defined。$R_4$ 出现在范畴论的 endomorphism algebra、$2 \times 2$ matrix algebra、量子 single-qubit Clifford group、有限几何 $\mathrm{PG}(3, 2)$ 等多个场景，作为「最小可表达完整结构」。

### 6.11 与其他根层的关系

- $R_4 = R_2 \otimes R_2 = R_2^2$（张量积、squaring）
- $R_4 = R_2 \oplus R_2$（直和、splitting view）
- $R_4 = \mathrm{End}(R_2)$ (endomorphism view)
- $R_4 \hookrightarrow R_8$ (subspace)
- $R_4 \otimes R_4 = R_8$（squaring 下一步）
- $R_4 \oplus R_4 = R_8$（直和 view of $R_8$）

---

## 7. $R_5$ — The 32-Element Layer

### 7.1 定义

$R_5 = \mathbb{F}_2^5$. $|R_5| = 32$. 

元素：长度 5 字符串。

### 7.2 群与 vector space

$R_5 = (\mathbb{Z}/2)^5$. 5-维。Abelian exponent-2.

### 7.3 数论特征

$|R_5| - 1 = 31$ 是 **Mersenne 素数** ($2^5 - 1$). 这意味着 $R_5$ 的 31 个非零元在 $\mathrm{Aut}$ 下形成 transitive orbit，并且 31 是素数让 $\mathrm{Aut}$ 的结构与 Galois 理论有特殊接口。

### 7.4 子群

$\mathbb{F}_2$-subspace 数：$\sum_{k=0}^{5} \binom{5}{k}_2$

- dim 0: 1
- dim 1: 31
- dim 2: 155
- dim 3: 155
- dim 4: 31
- dim 5: 1

共 374 子群。

### 7.5 $\mathrm{Aut}(R_5)$

$$|\mathrm{GL}(5, \mathbb{F}_2)| = 31 \cdot 30 \cdot 28 \cdot 24 \cdot 16 = \mathbf{9{,}999{,}360}$$

### 7.6 Bilinear form

奇维。仅 Layer 0 (dot product) 存在自然定义。

### 7.7 射影空间 PG(4, 2)

$R_5$ 的射影空间是 $\mathrm{PG}(4, 2)$：

- 31 points (= dim-1 subspaces of $R_5$)
- 155 lines (= dim-2 subspaces)
- 155 planes (= dim-3 subspaces)
- 31 hyperplanes (= dim-4 subspaces)

### 7.8 $R_5 = R_1 \oplus R_4$ 分解

$R_5$ 自然分解 $R_1 \oplus R_4$，把一个 bit 单独抽出。这给出 $R_4$-block + scalar 的 representations.

### 7.9 角色

$R_5$ 作为根层：

- Mersenne 5 是最小 prime Mersenne
- $\mathrm{GL}(5, 2)$ 体积近 $10^7$
- 出现在 Galois group of $x^{31} - 1$ 等代数数论场景

---

## 8. $R_6$ — The 64-Element Layer

### 8.1 定义

$R_6 = \mathbb{F}_2^6$. $|R_6| = 64$. 元素：长度 6 字符串。

### 8.2 多重分解

$R_6$ 有多种自然张量/直和分解：

- $R_6 = R_2 \otimes R_3$（=12 不对，应=4×8=32... wait, $R_N \otimes R_M = R_{NM}$, so $R_2 \otimes R_3 = R_6$，dim 6 yes，$|R_2 \otimes R_3| = 64$ ✓）
- $R_6 = R_3 \otimes R_2$（同上，commutative）
- $R_6 = R_2 \oplus R_4$（直和：dim 2+4=6）
- $R_6 = R_2 \oplus R_2 \oplus R_2 = R_2^3$（in old framework 这是 "Hexagram" 解读 $R_2$ 三 fold）
- $R_6 = \mathrm{Hom}(R_2, R_3)$ 或 $\mathrm{Hom}(R_3, R_2)$

### 8.3 子群

$\mathbb{F}_2$-subspace 数：

- dim 0: 1
- dim 1: 63
- dim 2: 651
- dim 3: 1395
- dim 4: 651
- dim 5: 63
- dim 6: 1

共 2825 子群。

### 8.4 $\mathrm{Aut}(R_6)$

$$|\mathrm{GL}(6, \mathbb{F}_2)| = 63 \cdot 62 \cdot 60 \cdot 56 \cdot 48 \cdot 32 = \mathbf{20{,}158{,}709{,}760}$$

约 $2 \times 10^{10}$.

### 8.5 三层 bilinear

$R_6$ 偶维，Layer 0/1/2 全部支持：

- $\langle u, v \rangle = \sum_i u_i v_i$
- $\sigma(u, v) = $ pair-wise $(u_{2k-1} v_{2k} + u_{2k} v_{2k-1})$, $k = 1, 2, 3$
- $q_0, q_1$ 类似 lift

### 8.6 $R_6$ 中嵌入 $R_4$

$R_4 \hookrightarrow R_6$ 通过取前 4 或后 4 坐标。$R_6 / R_4 \cong R_2$（商）。

### 8.7 $R_2^3$ Tensor 解读

把 $R_6$ 视为 $R_2 \otimes R_2 \otimes R_2$：每元素 $w \in R_6$ 看作 3 个 $R_2$ 的 tensor，等价于：

$$w : R_2 \to R_4, \quad \text{or} \quad w : R_4 \to R_2$$

这给 $R_6$ 一个 「Hom-tensor」 解读。

### 8.8 角色

$R_6$ 是**首个 dim-3 张量层**——$R_2^3$ 给出三方对偶关系。某些古典 6-fold symmetries (例如六爻、六极、六方) 与 $R_6$ 的代数结构对应（详 §10 Atlas）。

---

## 9. $R_7$ — Hamming Layer

### 9.1 定义

$R_7 = \mathbb{F}_2^7$. $|R_7| = 128$. 元素：长度 7 字符串。

### 9.2 群与 vector space

$R_7 = (\mathbb{Z}/2)^7$. 7-维.

### 9.3 数论特征

$2^7 - 1 = 127$ 也是 Mersenne 素数。$R_7$ 是第二个 Mersenne 根层（$R_5$ 是首个）。

### 9.4 Hamming(7,4) 完美码

$R_7$ 是 **Hamming(7, 4) 完美码**的自然居所——一个最小 perfect single-error-correcting binary linear code:

- 4 message bits + 3 parity bits = 7 transmitted bits
- 128 codeword space, 16 valid codewords forming $R_4$-dim subspace
- distance 3, correcting any single bit error
- "perfect" = sphere-packing-bound 满足

Hamming(7, 4) 的代数：

$$\mathrm{Hamming}(7, 4) = \ker H, \quad H \in \mathrm{Mat}_{3 \times 7}(\mathbb{F}_2)$$

$H$ 是 parity-check matrix，列向量是 7 个非零元 $\mathbb{F}_2^3$ vector — 这又把 Fano 平面 (§5) 嵌入到 $R_7$ 的码结构。

### 9.5 $\mathrm{Aut}(R_7)$

$$|\mathrm{GL}(7, \mathbb{F}_2)| = 127 \cdot 126 \cdot 124 \cdot 120 \cdot 112 \cdot 96 \cdot 64 \approx 1.64 \times 10^{14}$$

巨大。

### 9.6 子群

$\mathbb{F}_2$-subspace 共 $\sum_k \binom{7}{k}_2$ 个，几千个。

### 9.7 角色

$R_7$ 的独特地位主要由 Hamming 码定义：

- 最小 perfect single-error-correcting code
- $R_4$-dim Hamming code 嵌入 $R_7$
- 出现在 quantum error correction 中（Steane code = Hamming-based 量子码）

奇维 ⇒ 仅 Layer 0 bilinear。

### 9.8 $R_7 = R_1 \oplus R_2 \oplus R_4$ 分解

$R_7$ 是 $R_0$–$R_7$ 中**唯一**需要 squaring tower 三层全部参与的根层。所以 $R_7$ 在某种意义上是 squaring tower 「最完整」的非平凡直和.

---

## 10. $R_8$ — The Ceiling ★

> **重点层 2**：$R_8 = R_4^2$ 是**根层 ceiling**。它含 $R_0$–$R_7$ 作为 $\mathbb{F}_2$-子空间；许多常用代数概念定居于此尺度。

### 10.1 定义

$R_8 = \mathbb{F}_2^8$. $|R_8| = 256$. 元素：长度 8 字符串。

### 10.2 多种结构身份

$R_8$ 同时是：

1. **$\mathbb{F}_2^8$**：8-维 $\mathbb{F}_2$-vector space
2. **$R_4 \otimes R_4 = R_4^2$**：张量自方
3. **$R_4 \oplus R_4$**：直和
4. **$R_2^4$**：四 fold $R_2$ 张量 (= $\mathrm{Hom}(R_4, R_2) \cdot \mathrm{Hom}(R_2, R_4)$ 等多种解读)
5. **byte**：computer-science 标准 8-bit primitive unit

### 10.3 群与 vector space

$R_8 = (\mathbb{Z}/2)^8$. 阶 256. Abelian exponent-2.

### 10.4 子群

$\mathbb{F}_2$-subspace 总数 $\sum_k \binom{8}{k}_2 \approx 30000$.

dim-by-dim:

- dim 0: 1
- dim 1: 255
- dim 2: 5,355
- dim 3: 11,811
- dim 4: 200,787
- ... 等

### 10.5 $\mathrm{Aut}(R_8)$

$$|\mathrm{GL}(8, \mathbb{F}_2)| = 255 \cdot 254 \cdot 252 \cdot 248 \cdot 240 \cdot 224 \cdot 192 \cdot 128 \approx 5.35 \times 10^{18}$$

约 $5.35 \times 10^{18}$ — 远超经典 cryptography 的「实用」搜索空间起点。

### 10.6 含 $R_0$–$R_7$ 全部为 subspaces

> **关键事实**：$R_N \hookrightarrow R_8$ for all $N \in \{0, 1, \ldots, 7\}$.

证明（embedding）：对 $N \leq 7$，取「前 $N$ 坐标」subspace $\{w \in R_8 : w_{N+1} = \ldots = w_8 = 0\} \cong R_N$.

这个事实让 $R_8$ 成为**根层 universe**——所有更小根层都生活在 $R_8$ 内。

### 10.7 三层 Bilinear

$R_8$ 偶维 8，全部 Layer 支持：

**Layer 0**:
$$\langle w, w' \rangle = \sum_{i=1}^{8} w_i w'_i$$

**Layer 1** (4 对 symplectic blocks):
$$\sigma_{R_8}(w, w') = \sum_{k=1}^{4} (w_{2k-1} w'_{2k} + w_{2k} w'_{2k-1})$$

**Layer 2** (Arf-graded quadratic forms):
$$q_{R_8}^{(c_1, c_2, c_3, c_4)}(w) = \sum_{k=1}^{4} q_{c_k}(w_{2k-1} w_{2k})$$

$c_k \in \{0, 1\}$ 选 $q_0$ 或 $q_1$ for each $R_2$-block. 总 Arf = $\sum_k c_k \pmod 2$.

### 10.8 $R_8 = R_4^2$ — Nested Matrix Structure

把 $R_8$ 视为 **「矩阵的矩阵」**：

$$R_8 = R_4 \otimes R_4 \cong \mathrm{Mat}_{2 \times 2}(\mathrm{Mat}_{2 \times 2}(\mathbb{F}_2))$$

即 $R_8$ 的元素是「$2 \times 2$ 矩阵，每个 entry 又是 $2 \times 2$ $\mathbb{F}_2$-矩阵」。

或等价地，$R_8 = \mathrm{Mat}_{4 \times 4}(\mathbb{F}_2)$ — $4 \times 4$ $\mathbb{F}_2$-矩阵 space.

注意 $\mathrm{Mat}_{4 \times 4}(\mathbb{F}_2)$ over $\mathbb{F}_2$ 的 dimension 是 16 = 与 $R_4$ 同。但 $R_8$ 自己 dim 8. 

更精确地：$R_8 \neq \mathrm{End}(R_4) = R_{16}$. 而 $R_8 = R_4 \otimes R_4$ 是 tensor，不是 endomorphism algebra.

正确说法：**$R_8$ 是 $R_4$ 的 "tensor square"，不是 "endomorphism algebra"**。

### 10.9 常用概念在 $R_8$ 尺度

256 元的代数结构在以下场景出现：

1. **Computer byte**：8-bit 是计算机基础数据单元
2. **Unicode UTF-8 single-byte**：256 code points
3. **GF(256) finite field**：AES, BCH codes, Reed-Solomon codes 用之
4. **DNA codons**：4³ = 64 codons 但 8-bit 编码扩展 (含碱基组合)
5. **8-qubit register**：256 量子态
6. **Pixel intensity 8-bit**：图像 0-255 灰度
7. **Hex byte**：16² = 256 = 两个 hex digits

许多 cryptography、coding theory、data representation 的 algebraic operations 定居于 $R_8$ 尺度。

### 10.10 $R_8$ 作为 ceiling 的代数事实

> **定理 10.10**：$R_0$–$R_8$ 是文 algebra 的充分根集。任何更大 $R_N$ ($N > 8$) 可由 $R_0$–$R_8$ 经直和、张量、Hom 构造。

证（构造性）：

- 若 $N = 8m + r$ ($0 \leq r < 8$)，则 $R_N = R_8^{\oplus m} \oplus R_r = m \cdot R_8 \oplus R_r$
- $R_8^{\oplus m}$ 由 $R_8$ 自身重复直和
- 由是任意 $R_N$ 在 $R_0$–$R_8$ 的代数闭包内

更精细地：

- $R_{16} = R_8 \oplus R_8 = R_8^2$（张量）— 是 squaring tower 下一层
- $R_{32} = R_{16}^2$
- $R_{64} = R_{32}^2$

每次 squaring 可由 ceiling 的 tensor 翻倍。$R_0$–$R_8$ 是根层的有限封闭范围。

### 10.11 角色 · The Significance of $R_8$

$R_8$ 在 R-族中的独特地位：

1. **Squaring tower 第 4 层**：$R_1 \to R_2 \to R_4 \to R_8$ 完成自相似四步
2. **Ceiling**：含所有 $R_0$–$R_7$ 作为 subspace
3. **Byte-scale**：计算的天然基本单位
4. **生成性**：从 $R_0$–$R_8$ 可构造所有更大 $R_N$
5. **Field structure**：$R_8$ 与 $\mathrm{GF}(256)$ 同构 (作为 $\mathbb{F}_2$-向量空间)，提供乘法环结构

### 10.12 与其他根层的关系

- $R_8 = R_4^2$ (tensor) ← squaring tower 关系
- $R_8 = R_4 \oplus R_4$ (direct sum)
- $R_8 = R_2 \oplus R_2 \oplus R_2 \oplus R_2 = R_2^4$ (4-fold direct sum / tensor)
- $R_8 = R_1 \oplus R_7 = R_3 \oplus R_5 = $ 等多种二分
- $R_0, R_1, \ldots, R_7 \hookrightarrow R_8$（嵌入）

---

## 11. 跨层操作 · Inter-Layer Operations

### 11.1 直和

$$R_N \oplus R_M = R_{N+M}$$

按 $\mathbb{F}_2$-向量空间直和，dimension 加。

### 11.2 张量积

$$R_N \otimes_{\mathbb{F}_2} R_M = R_{NM}$$

dimension 乘。$R_2 \otimes R_2 = R_4$, $R_4 \otimes R_4 = R_8$ — squaring tower 在此涌现。

### 11.3 Hom

$$\mathrm{Hom}_{\mathbb{F}_2}(R_N, R_M) \cong R_{NM}$$

线性映射空间 = matrix space of size $M \times N$ over $\mathbb{F}_2$。

特别：$\mathrm{End}(R_N) = \mathrm{Hom}(R_N, R_N) = R_{N^2}$.

- $\mathrm{End}(R_1) = R_1$
- $\mathrm{End}(R_2) = R_4$ ★ (= $R_2$ squaring)
- $\mathrm{End}(R_3) = R_9$ (out of root layers)
- $\mathrm{End}(R_4) = R_{16}$ (out of root layers; constructible via direct sum)

### 11.4 子空间与商

$R_N$ 含 $R_M$ subspace for $M \leq N$. 商 $R_N / R_M = R_{N-M}$.

### 11.5 Dual

Pontryagin 对偶 $\widehat{R_N} \cong R_N$ — 自对偶（因 $\mathbb{F}_2$ self-dual character group）。

---

## 12. Bilinear Pairings — Cross-Layer Summary

### 12.1 一致性表

| 层 | $N$ 奇偶 | Layer 0 ($\langle\cdot,\cdot\rangle$) | Layer 1 (σ) | Layer 2 (q + Arf) |
|----|---------|----|----|----|
| $R_0$ | — | trivial | — | — |
| $R_1$ | odd | ✓ | — | — |
| $R_2$ | even | ✓ | ✓ | ✓ |
| $R_3$ | odd | ✓ | — | — |
| $R_4$ | even | ✓ | ✓ | ✓ |
| $R_5$ | odd | ✓ | — | — |
| $R_6$ | even | ✓ | ✓ | ✓ |
| $R_7$ | odd | ✓ | — | — |
| $R_8$ | even | ✓ | ✓ | ✓ |

**规律**：

- Layer 0 (dot) 在所有 $R_N$ 上都自然定义
- Layer 1 (σ) 与 Layer 2 (q + Arf) 仅在**偶维** $R_N$ 上自然定义——char 2 symplectic 几何要求偶维

### 12.2 跨层 dot 的 $R_N$-block 因式化

对偶维 $R_{2k}$，dot product 可按 $k$ 个 $R_2$-block 直和分解：

$$\langle w, w' \rangle_{R_{2k}} = \sum_{j=1}^{k} \langle w^{(j)}, w'^{(j)} \rangle_{R_2}$$

where $w^{(j)} = (w_{2j-1}, w_{2j}) \in R_2$.

类似地 σ 与 q 都有 component-wise 因式化（详见 §6.8, §10.7）。

---

## 13. $\mathrm{Aut}(R_N)$ — Automorphism Groups

### 13.1 阶公式

$$|\mathrm{Aut}(R_N)| = |\mathrm{GL}(N, \mathbb{F}_2)| = \prod_{k=0}^{N-1} (2^N - 2^k)$$

| $N$ | $|\mathrm{Aut}(R_N)|$ | 特殊同构 |
|-----|----------------------|----------|
| 0 | 1 | trivial |
| 1 | 1 | trivial |
| 2 | 6 | $\cong S_3$ |
| 3 | 168 | $\cong \mathrm{PSL}(2, 7)$ |
| 4 | 20,160 | $\cong A_8$ |
| 5 | 9,999,360 | — |
| 6 | 20,158,709,760 | — |
| 7 | $\sim 1.64 \times 10^{14}$ | — |
| 8 | $\sim 5.35 \times 10^{18}$ | — |

### 13.2 子群嵌入

$\mathrm{Aut}(R_N)$ 包含 $\mathrm{Aut}(R_M)$ for $M \leq N$ via 作用在 $R_M$-subspace 上的扩展。这给出**Aut 嵌套链**：

$$\{1\} = \mathrm{Aut}(R_0) \hookrightarrow \mathrm{Aut}(R_1) \hookrightarrow \mathrm{Aut}(R_2) \hookrightarrow \ldots \hookrightarrow \mathrm{Aut}(R_8)$$

### 13.3 Preservation hierarchy at $R_2$ (复习)

$\mathrm{Aut}(R_2) = S_3$ 在 $R_2$ 上的 3 层 filtration：

| Level | Aut 子群 | 阶 | 保的结构 |
|-------|----------|----|---------|
| L0 | $S_3$ (full) | 6 | 群、σ、$q_1$ |
| L1 | Stab(xx) | 2 | + $\{\mathrm{oo}, \mathrm{xx}\}$、$\langle\cdot,\cdot\rangle$、$q_0$ |
| L2 | $\{\mathrm{id}\}$ | 1 | 所有 |

> **R_2 是特例**：$\mathrm{Sp}(2, 2) = \mathrm{GL}(2, 2) = S_3$（巧合相等 $|S_3| = 6$）。所以 R_2 上全 Aut 自动保 σ. 对 $R_4, R_8, \ldots$ **不**成立——$\mathrm{Sp}(N, 2) \subsetneq \mathrm{GL}(N, 2)$ 严格真子群，仅部分 Aut 保 σ. 详 r8.md §9.4 与 wen-algebra §5.4.

---

## 14. 超越 $R_8$ · Beyond $R_8$ — Construction Calculus

### 14.1 $R_N$ for $N > 8$ 的构造

由 §1.5 与 §10.10：任意 $R_N$ ($N > 8$) 由 $R_0$–$R_8$ 构造：

$$R_N = R_8^{\oplus \lfloor N/8 \rfloor} \oplus R_{N \mod 8}$$

例：

- $R_{10} = R_8 \oplus R_2$
- $R_{16} = R_8 \oplus R_8$（squaring tower 下一层，via direct sum；cardinality $|R_8|^2$）
- $R_{32} = R_{16} \oplus R_{16}$
- $R_{64} = R_{32} \oplus R_{32}$

> **注意 squaring tower 记号**：「$R_{2N} = R_N^2$」在文档中表示 *cardinality squaring via direct sum* ($R_{2N} = R_N \oplus R_N$)，**不是 tensor square**（$R_N \otimes R_N = R_{N^2}$ much larger）。详 r8.md §1.6 tensor vs direct sum 辨析.

### 14.2 性质继承

由 $R_0$–$R_8$ 中验证的代数事实自动 lift 到任意 $R_N$ 经直和分解：

- **群结构 + 阿贝尔性**：直接经直和继承
- **Bilinear forms**：按 $R_2$-block 因式化（§12.2），由直和分解 lift
- **$\mathrm{Aut}$**：$\mathrm{GL}(N, \mathbb{F}_2)$ 有递归子群结构（含 block-diagonal subgroup）
- **Subspaces**：$R_N$ 子空间包含所有 $R_M \hookrightarrow R_N$ for $M \leq N$（前 $M$ 坐标）

张量与 Hom 函子虽闭合（详 wen-algebra §2），但产生 $R_{NM}$ 这种**大得多**的层；高层 $R_N$ 的主要 lift 路径是**直和**.

### 14.3 根层范围充足性

> **充足性陈述**：所有需要在 $R_N$ ($N \in \mathbb{N}$) 上证明的代数性质，都可在 $R_0$–$R_8$ 上证明，再 lift 到 $R_N$。

这给文 algebra 一个**有限根集**：$R_0, R_1, \ldots, R_8$ 是完整的 generating set。

---

## 15. 外部传统对应 · Application Layer Atlas

> **范围**：本节列出 $R_N$ 在外部传统中的若干对应。这些是 **应用层映射** (application-layer correspondences)，**不是 $R_N$ algebra 的来源或定义**。

### 15.1 $R_1$ — 经典二元

- 数字 logic: $\{0, 1\}$ / true/false
- Shannon bit
- Schmitt trigger 输出
- 是/非, 阴/阳 (古典中文宇宙论的最简层)

### 15.2 $R_2$ — Klein-four

- **Pauli 群 mod phase**: $\{I, X, Y, Z\}$ 同构于 $V_4$
- **CPT 在物理**: trivial / C / P / T 对应
- **Galois of $\mathbb{C}/\mathbb{R}$**: 部分嵌入 (复共轭 = 一个 $\mathbb{Z}/2$)
- **Greimas semiotic square**: A / ¬A / B / ¬B
- **古典中文「象」**: 4-fold (旧译 道/错/综/错综)
- **Boolean logic operators**: identity / negation / dual / contrapositive (4-fold)

### 15.3 $R_3$ — Fano 平面

- **Octonions**: $\mathbb{O}$ 的 multiplication table 由 Fano 平面给出
- **Quantum mutually unbiased bases**: $d = 2^{n/2}$ 系
- **Steiner triple systems**: STS(7) = Fano

### 15.4 $R_4$ — Mat($2 \times 2$, $\mathbb{F}_2$) / Frame

- **Single-qubit Pauli group**: 16 元 (含 phase)
- **Single-qubit Clifford group**: 24 元，但 mod phase 含 $R_4$ 子群
- **Endomorphism algebra of $V_4$**: directly $R_4$
- **Boolean logic 16 functions of 2 vars**: $\mathbb{F}_2^4$ = $R_4$
- **古典中文「对象」/ Frame** (旧译，但不为本版使用)
- **$\mathbb{A}_8$ alternating group**: $\mathrm{Aut}(R_4)$ 同构

### 15.5 $R_5$ — Mersenne 5

- **Galois group of $x^{31} - 1$**: 某些子结构对应
- **Quintic equations**: $S_5$ vs $A_5$
- **Edge code in $\mathbb{F}_2^5$**

### 15.6 $R_6$ — 64-元

- **8-cube symmetry partial**
- **古典中文「卦」/ Hexagram** (易学 64 卦，作为 application-layer 映射)
- **$R_2 \otimes R_3$**: 量子 6-state systems

### 15.7 $R_7$ — Hamming

- **Hamming(7, 4) 完美码**
- **Steane code** (量子 Hamming 推广)
- **Octonions 的扩展几何**

### 15.8 $R_8$ — Byte / GF(256)

- **Byte / 8-bit**: 计算基础单元
- **AES (Rijndael)**: 使用 $\mathrm{GF}(256)$ field structure on $R_8$
- **Reed-Solomon codes**: 多基于 $\mathrm{GF}(256)$
- **Unicode UTF-8 single byte**: 256 code points
- **Pixel intensity 8-bit**: 0-255 灰度
- **古典中文「时卦」** (256 元，作为 application-layer)

### 15.9 跨层共性观察

> 多个外部传统在多个根层上有自然对应，但这些对应是**$R_N$ algebra 在不同领域中的显现**，不是 $R_N$ 的源。$R_0$–$R_8$ 由 §1–§14 的代数事实独立定义。

---

## 16. 形式骨架 · Formal Skeleton

### 16.1 Lean 4

```lean
import Mathlib.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.Data.Fin.Basic

namespace 文.R

/-- R_N = F_2^N — the N-th layer root.
    Element representation: Fin N → Bool (o = false, x = true). -/
def R (N : ℕ) : Type := Fin N → Bool

namespace R

variable {N : ℕ}

/-- Component-wise XOR — abelian group structure -/
def xor (u v : R N) : R N := fun i => Bool.xor (u i) (v i)

instance : Add (R N) := ⟨xor⟩
instance : Zero (R N) := ⟨fun _ => false⟩

instance : AddCommGroup (R N) where
  add_assoc := by intros; funext i; cases (a i) <;> cases (b i) <;> cases (c i) <;> rfl
  zero_add  := by intros; funext i; rfl
  add_zero  := by intros; funext i; cases (a i) <;> rfl
  add_left_neg := by sorry  -- char 2: v + v = 0
  add_comm  := by intros; funext i; exact Bool.xor_comm _ _

/-- Layer 0: Boolean dot product. Defined for all N. -/
def dot (u v : R N) : Bool :=
  (Finset.univ : Finset (Fin N)).foldr (fun i acc => Bool.xor (u i && v i) acc) false

theorem dot_symm (u v : R N) : dot u v = dot v u := by
  unfold dot; congr 1; funext i; exact Bool.and_comm _ _

/-- Layer 1: Symplectic form sigma. Only for even N. -/
def sigma {N : ℕ} (h : Even N) (u v : R N) : Bool := sorry
  -- σ(u, v) = sum_{k=1..N/2} (u_{2k-1} v_{2k} + u_{2k} v_{2k-1})

/-- Linear form L: diagonal projection -/
def L (v : R N) : Bool :=
  (Finset.univ : Finset (Fin N)).foldr (fun i acc => Bool.xor (v i) acc) false

end R

/-- R_2 — the Klein-four pair layer -/
namespace R2

/-- Named convenience constructors -/
def oo : R 2 := fun _ => false
def xo : R 2 := fun i => i = 0
def ox : R 2 := fun i => i = 1
def xx : R 2 := fun _ => true

/-- {oo, xx} subgroup -/
def subgroup_oo_xx : Set (R 2) := {oo, xx}

/-- Three-in-one characterization @ R_2 -/
theorem three_in_one_diagonal :
    ∀ v : R 2, v ∈ subgroup_oo_xx ↔ R.L v = false := by sorry

theorem three_in_one_isotropy :
    ∀ v : R 2, v ∈ subgroup_oo_xx ↔ R.dot v v = false := by sorry

end R2

/-- R_4 — the minimum complete unit ★ -/
namespace R4

/-- R_4 as End(R_2): each element is a 2×2 F_2 matrix -/
def asMatrix (w : R 4) : R 2 → R 2 := fun u i =>
  Bool.xor ((w (2*i)) && (u 0)) ((w (2*i + 1)) && (u 1))

/-- Rank classification -/
inductive Rank | zero | one | two

def rankOf (w : R 4) : Rank := sorry

/-- Number of rank-2 (invertible) elements = 6 = |GL(2, F_2)| -/
theorem rank_two_count : 
    Fintype.card { w : R 4 // rankOf w = Rank.two } = 6 := by sorry

end R4

/-- R_8 — the ceiling ★ -/
namespace R8

/-- R_8 contains R_N as subspace for all N ≤ 7 -/
def embed_from {N : ℕ} (h : N ≤ 7) (v : R N) : R 8 :=
  fun i => if h_lt : i.val < N then v ⟨i.val, h_lt⟩ else false

/-- R_8 = R_4 ⊕ R_4 -/
def split (w : R 8) : R 4 × R 4 :=
  (fun i => w ⟨i.val, by omega⟩, fun i => w ⟨i.val + 4, by omega⟩)

end R8

end 文.R
```

### 16.2 单轨 (Lean only) note

v0.5 update: Clojure 实现已弃用。Lean 4 现为唯一形式语言。所有 verification（rank counts, σ alternating, Aut orders, Arf classification, etc.）在 Lean 内通过 `decide` / `native_decide` 完成，避免双轨 inconsistency.

具体 Lean 模块组织详 `wen-algebra.md` v0.6 §10.9.

---

## 17. Open Questions

1. **Surface 编码状态**：当前所有 $R_N$ 元素用 o/x 字符串作 surface 编码。这是 v0.3 起的设计决定（"字符语义先全部冻结，用 o/x 占位"），**不是占位待命名的过渡态**。汉字命名层只在 mnemonic / human-readable 需求出现时作为可选 application-layer alias 提供（不进 core type system，详 wen-algebra Rule 10）。Q3, Q4 中关于「如果选择用字」的讨论是可选扩展，不阻塞工程.

2. **R-tower 与 squaring tower 双层视角**的工程暴露：surface 类型系统是否需要同时支持两种视角？

3. **$R_4$ 的 mnemonic alias**（可选）：若提供 human-readable alias，rank 分类是自然起点 (rank-2 6 个 = $S_3$ = $\mathrm{GL}(2, \mathbb{F}_2)$ 可命名 id/swap/shear/rotate).

4. **$R_8$ 的 mnemonic alias**（可选）：若需 256 元 human-readable，hex byte (00-FF) 是天然兼容 alias.

5. **奇维 $R_1, R_3, R_5, R_7$ 的 surface 暴露**：奇维仅 Layer 0 bilinear，结构上「不完整」。是否仍允许 surface-level type？

6. **三层 preservation hierarchy** (§4.9) 是否要 surface 暴露？

7. **跨层 dot / σ / q 在 $R_N$ 上的提升机制**：当前 §12.2 给 $R_2$-block 因式化。是否值得给一个 unified Lean tactic?

8. **Atlas (§15) 应用层 binding 的工程组织**：core 文档不含 Atlas，应分到 `wen-correspondences.md`?

9. **$R_8 = \mathrm{GF}(256)$ 的乘法结构**：$R_8$ 作为 $\mathbb{F}_2$-向量空间 (additive only) vs $\mathrm{GF}(256)$ (有乘法环结构)。后者是 application-layer 还是 core?

10. **Beyond $R_8$ 的具体编译实现**：$R_N$ for $N > 8$ 在 IR 中如何表示？硬编码到 $R_8^{\oplus k}$ 还是抽象 $R_N$ type？

---

## 18. 完成度自检 · Completeness Check

| 内容 | 已覆盖 |
|------|------|
| R_N 记号与 o/x 元素表示 | ✓ §0.2 |
| 视角原则（无单层中心） | ✓ §0.3 |
| 与 wen-algebra 的边界 | ✓ §0.4 |
| 9 层 $R_0$–$R_8$ 总览表 | ✓ §1.1 |
| Squaring 子塔 $R_1 \to R_2 \to R_4 \to R_8$ | ✓ §1.3 |
| 直和分解 $R_N$ from squaring tower | ✓ §1.4 |
| $R_8$ 作为 ceiling | ✓ §1.5, §10 |
| $R_0$ 平凡层 | ✓ §2 |
| $R_1$ 完整规范 | ✓ §3 |
| $R_2$ 完整规范（群、空间、子群、三合一、Aut、preservation）| ✓ §4 |
| $R_3$ 完整规范 (Fano 平面) | ✓ §5 |
| **$R_4$ 重点延伸** ★ | ✓ §6 |
| $R_4$ rank 分层 | ✓ §6.5 |
| $R_4 = \mathrm{End}(R_2)$ 自封闭 | ✓ §6.9 |
| $R_5$ 完整规范 (Mersenne) | ✓ §7 |
| $R_6$ 完整规范（多重分解）| ✓ §8 |
| $R_7$ 完整规范 (Hamming) | ✓ §9 |
| **$R_8$ 重点延伸** ★ | ✓ §10 |
| $R_8$ 含 $R_0$–$R_7$ subspaces | ✓ §10.6 |
| $R_8$ 跨域常用概念 | ✓ §10.9 |
| 跨层操作（直和/张量/Hom）| ✓ §11 |
| Bilinear pairings 一致性表 | ✓ §12 |
| Aut($R_N$) 阶 + 嵌入链 | ✓ §13 |
| 超越 $R_8$ 构造 | ✓ §14 |
| Atlas (§15) 应用层 | ✓ §15 |
| Lean 4 骨架 (parametric R N) | ✓ §16.1 |
| Lean-only formalization note | ✓ §16.2 |
| Open Questions（10 项）| ✓ §17 |

---

*End of v0.5 · v4-foundation · The R₀–R₈ Root Tower*
*Each layer has its own structure; $R_4$ and $R_8$ are the dual emphases.*
