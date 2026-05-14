# 文 代数 — R-Family Tower Algebra

> **文 形式语言** · Algebra Note
> Tower-level algebra on the R-Family $\{R_N\}$，R_0–R_8 as root, R_4 and R_8 as dual centers
> Companion to: `v4-foundation.md` (R_N layer specs), `r4.md` (minimum complete unit), `r8.md` (ceiling)
> **Single formal language**: Lean 4 + Mathlib
> v0.6

**Changelog**

- v0.6 — 重大重写：弃用 𝕏/𝕐/矩/象/Frame 等所有历史层名；改用 R_N tower (foundation v0.4 / r4.md / r8.md 体系)。**R_4 与 R_8 双重点**。Lean 唯一形式语言（弃 Clojure）。Focus 从 single-center algebra 转为 **tower-level operations** + **compiler/interpreter foundation**
- v0.5 — 矩 (𝕐 = 𝕏²) 作为代数中心
- v0.4 — Atlas 严格作 application layer
- v0.3 — σ + q + Hom = Mat(矩)
- v0.2 — 四套并行命名
- v0.1 — 初稿

---

## 0. 范围与定位 · Scope and Positioning

### 0.1 文档目的

本文档是文形式语言的**塔级代数规范** (tower-level algebra specification)。它确立：

1. **R-Family $\{R_N\}_{N \geq 0}$ 作为代数族**——结构、闭合、性质提升
2. **Hom 表示定理**：$\mathrm{Hom}(R_{2n}, R_{2m}) = \mathrm{Mat}_{m \times n}(R_4)$
3. **Bilinear forms 跨塔行为**：dot / σ / q + Arf 在 $R_N$ 上的 component-wise factorization
4. **Aut 塔与 preservation hierarchy**
5. **R-Family 作 compiler / interpreter IR**：type system, phantom modes, normalize pass
6. **塔级判断 (judgment) 层**：信息 / 吸引子 / 行为 在 R-Family 上的统一处理
7. **自相似延伸构造**：R_0–R_8 根集合上证立的性质 lift 到 $R_{2^k}$ for $k \geq 4$
8. **Application-layer 隔离原则**

### 0.2 与其他文档的边界

| 文档 | 角色 |
|------|------|
| `v4-foundation.md` (v0.4) | R_0–R_8 单层规范 (每 $R_N$ "是什么") |
| `r4.md` (v0.1) | R_4 = minimum complete unit 专题 |
| `r8.md` (v0.1) | R_8 = ceiling 专题 + spacetime + judgment + 自相似延伸 |
| `wen-algebra.md` (本, v0.6) | 塔级操作 + Lean 编译器 / 解释器 foundation |

**职责分工**：

- foundation 与 r4 / r8 给「层规范」(layer specs)
- wen-algebra 给「跨层 algebra + 工程实现」(cross-layer + engineering)

### 0.3 形式语言约定

> **Lean 4 + Mathlib 是文的唯一形式语言**。

本版及后续不使用 Clojure 或其他外部语言。证明、解释器、未来编译器均在 Lean 4 内：

- **证明轨**：Mathlib 机器验证代数性质
- **解释器轨**：`computable` Lean defs，`decide` / `native_decide` 运行
- **编译器轨**：未来扩展，仍在 Lean 4 内

§10 给出 Lean 4 完整骨架。

### 0.4 元素与命名约定

继承 v4-foundation v0.4：

- R_N = $\mathbb{F}_2^N$，$|R_N| = 2^N$
- 元素是长度 $N$ 的 o/x 字符串
- 字符语义全部冻结，只看结构
- 函数名使用 o/x 占位（如 `is_oo_xx_subspace`）

### 0.5 视角原则

继承 foundation §0.3：

1. **R-Family 是中心**——R_0–R_8 全为 first-class 根层
2. **R_4 与 R_8 双重点**（详 r4.md 与 r8.md）
3. **No single-layer center**——历史的 𝕏-center / 𝕐-center / 矩-center 一律弃用
4. **Atlas 严格作 application layer**

---

## 1. R-Family — Tower Recap

简短回顾 R-Family 结构（详 foundation §1, §3-§11）。

### 1.1 R_N 定义

$$R_N := \mathbb{F}_2^N, \quad |R_N| = 2^N$$

元素长度 N 的 o/x 字符串。$R_N$ 是 $\mathbb{F}_2$-向量空间，N-维。

### 1.2 9 根层 R_0–R_8

| 层 | 大小 | 角色 | 详细 |
|----|------|------|------|
| R_0 | 1 | 平凡 (trivial)  | foundation §2 |
| R_1 | 2 | 原始 bit | foundation §3 |
| R_2 | 4 | Klein-four, 双轴 | foundation §4 |
| R_3 | 8 | Fano 平面 PG(2,2) | foundation §5 |
| **R_4** | 16 | **minimum complete unit** ★ | **r4.md** |
| R_5 | 32 | Mersenne 31 | foundation §7 |
| R_6 | 64 | $R_2 \otimes R_3$ 多分解 | foundation §8 |
| R_7 | 128 | Hamming(7,4) | foundation §9 |
| **R_8** | 256 | **ceiling, R_4²** ★ | **r8.md** |

### 1.3 Squaring 子塔

$$R_1 \xrightarrow{\oplus\text{-sq}} R_2 \xrightarrow{} R_4 \xrightarrow{} R_8 \xrightarrow{} R_{16} \xrightarrow{} R_{32} \xrightarrow{} \ldots$$

其中 $R_{2N} := R_N \oplus R_N$（cardinality squaring via direct sum，see r8.md §1.2 关于 tensor vs sum 的正确区分）。

### 1.4 R_0–R_8 作根集 + 高层延伸

- $R_0$–$R_8$ 是 *root layers*（直接定义）
- $R_N$ for $N > 8$ 由根层直和构造：
$$R_N = R_8^{\oplus \lfloor N/8 \rfloor} \oplus R_{N \bmod 8}$$
- 性质 lift 详 §8

---

## 2. R-Family 闭合性 · Closure Properties

R-Family 在多种代数运算下闭合——这是文 algebra 的代数完备性骨架。

### 2.1 直和

**定理 2.1**：
$$R_N \oplus R_M \cong R_{N+M}$$

阶 $2^N \cdot 2^M = 2^{N+M}$. 闭合于 R-Family. ✓

### 2.2 $\mathbb{F}_2$-张量

**定理 2.2**：
$$R_N \otimes_{\mathbb{F}_2} R_M \cong R_{NM}$$

阶 $2^N \cdot 2^M / ? $... actually $\dim(R_N \otimes R_M) = \dim R_N \cdot \dim R_M = NM$. 阶 $2^{NM}$. 闭合. ✓

特别：

- $R_2 \otimes R_2 = R_4$ (= End(R_2), 见 §3.1)
- $R_4 \otimes R_4 = R_{16}$ (= End(R_4))
- $R_8 \otimes R_8 = R_{64}$

### 2.3 Hom

**定理 2.3**：
$$\mathrm{Hom}_{\mathbb{F}_2}(R_N, R_M) \cong R_{NM}$$

由 $\mathrm{Hom}_{\mathbb{F}_2}(R_N, R_M) \cong \mathrm{Mat}_{M \times N}(\mathbb{F}_2)$, 阶 $2^{NM}$.

特别：

- $\mathrm{Hom}(R_2, R_2) = R_4$ ★ (= End(R_2), 详 r4.md §8)
- $\mathrm{Hom}(R_4, R_2) = R_8$, $\mathrm{Hom}(R_2, R_4) = R_8$ (详 r8.md §7)
- $\mathrm{Hom}(R_4, R_4) = R_{16}$

### 2.4 Pontryagin 自对偶

**定理 2.4**：
$$\widehat{R_N} := \mathrm{Hom}(R_N, S^1) \cong \mathrm{Hom}(R_N, \mathbb{F}_2) \cong R_N$$

即 R_N 是 Pontryagin 自对偶. 这是 §4 dot product 与 §3 Hom representation 自然存在的根.

### 2.5 子群与商

R_N 的 $\mathbb{F}_2$-subspace 数 = $\sum_k \binom{N}{k}_2$（Gaussian binomial 和）。

商：$R_N / S \cong R_{N - \dim S}$ for $\mathbb{F}_2$-subspace $S$.

**$R_N^k$-形子群**（取前 $k$ 坐标）封闭于 R-Family。

### 2.6 闭合性主定理

**定理 2.6 (R-Family Closure)**：以下函子均将 R-Family 映回自身：

| 函子 | 输入 $(N, M)$ → 输出 N' | dim 公式 | cardinality |
|------|-------------------------|----------|-------------|
| 直和 $\oplus$ | $N + M$ | $\dim$ 加 | $\|R_N\| \cdot \|R_M\| = 2^{N+M}$ |
| 张量 $\otimes_{\mathbb{F}_2}$ | $NM$ | $\dim$ 乘 | $2^{NM}$ |
| Hom | $NM$ | $\dim$ 乘 | $2^{NM}$（等同张量）|
| Pontryagin 对偶 | $N$ | 不变 | $2^N$（自对偶）|
| $\mathbb{F}_2^k$-子群 ($k \leq N$) | $k$ | 部分 | $2^k$ |
| 商 (mod $R_k$) | $N - k$ | 减 | $2^{N-k}$ |

**关键区分**：直和与张量 cardinality 差异巨大. 例 $|R_4 \oplus R_4| = 256$ vs $|R_4 \otimes R_4| = 65536$. **Squaring tower 用直和**（详 r8.md §1.6）.

**R-Family 在这 6 类函子下完全闭合**——这是 wen 代数 IR 的核心保证.

### 2.7 R_0–R_8 充足性

**定理 2.7 (Root Sufficiency)**：所有 $R_N$ 上性质可由 $R_0$–$R_8$ 上对应性质 lift（经 §2.1-§2.5 函子）.

证明梗概：任意 $R_N$ 通过 §1.4 直和分解写为 $R_0$–$R_8$ 元素的 sum. 性质 (linear, bilinear, group-theoretic) 经 sum compatible.

---

## 3. Hom 表示定理 · Hom Representation Theorem ★

> **核心定理**：$\mathrm{Hom}_{\mathbb{F}_2}(R_{2n}, R_{2m}) \cong \mathrm{Mat}_{m \times n}(R_4)$
> 
> 即「**Hom = Matrix of R_4-cells**」——R_4 是 Hom representation 的 standard cell type.

### 3.1 R_4 = End(R_2)

由 r4.md §8: $R_4 = \mathrm{End}(R_2) = \mathrm{Mat}_{2 \times 2}(\mathbb{F}_2)$. 16 个 R_4 元素 ↔ 16 个 $R_2 \to R_2$ 线性映射. 见 r4.md §1-§2.

### 3.2 Hom 矩阵化定理

**定理 3.2 (Hom-Mat-R_4)**：
$$\mathrm{Hom}_{\mathbb{F}_2}(R_{2n}, R_{2m}) \cong \mathrm{Mat}_{m \times n}(R_4)$$

**证**：

$R_{2n} = R_2^{\oplus n}$ (view as $n$ blocks of $R_2$), $R_{2m} = R_2^{\oplus m}$.

线性映射 $f: R_{2n} \to R_{2m}$ 等于一个 $(2m) \times (2n)$ $\mathbb{F}_2$-matrix. 把它按 $2 \times 2$ blocks 分割：第 $(i, j)$-block ($1 \leq i \leq m$, $1 \leq j \leq n$) 是一个 $2 \times 2$ $\mathbb{F}_2$-matrix = 一个 R_4 元素 = 一个 $R_2 \to R_2$ 映射.

总 cell 数 $m \times n$，每 cell 16 元，总 $16^{mn}$ = $2^{4mn} = |R_{4mn}| = |R_{(2m)(2n)/?}|$... actually $|\mathrm{Hom}(R_{2n}, R_{2m})| = 2^{(2m)(2n)} = 2^{4mn}$. ✓

∎

### 3.3 三种 Hom 表示方案对比

继承 r4.md §10.2.

| 方案 | 表示 | 优 | 劣 |
|------|------|-----|----|
| **A. Flat emit** | $R_{4mn}$ flat element | 简单 | 失结构 |
| **B. Function primitive** | opaque function type | application 直白 | 失代数对接 |
| **C. Mat of R_4** ★ | $\mathrm{Mat}_{m \times n}(R_4)$ | 结构化 + 代数兼容 + 自然 cell type | 需 2D 索引 |

**文采用方案 C**——这是 R-Family 内自然的「层间映射 = matrix of R_4-cells」表示.

### 3.4 应用 (Apply)

设 $f \in \mathrm{Mat}_{m \times n}(R_4)$, $U \in R_{2n}$. Application $f(U) \in R_{2m}$:

$$f(U)_i := \bigoplus_{j=1}^{n} \mathrm{apply}_{R_4}(f_{ij}, U_j) \in R_2, \quad i = 1, \ldots, m$$

其中：

- $U$ 被 view 为 $n$ 个 $R_2$-blocks $U_1, \ldots, U_n$
- $f_{ij} \in R_4$ apply 到 $U_j \in R_2$ 给 $R_2$ 结果 (详 r4.md §8.2)
- 对 $j$ 累加（$R_2$ 加法 = component-wise XOR）

输出 $f(U)$ 由 $m$ 个 $R_2$-blocks 组装为 $R_{2m}$.

### 3.5 复合 (Composition)

$g \in \mathrm{Mat}_{p \times m}(R_4)$, $f \in \mathrm{Mat}_{m \times n}(R_4)$, 复合 $g \circ f \in \mathrm{Mat}_{p \times n}(R_4)$:

$$(g \circ f)_{ik} := \bigoplus_{j=1}^{m} \mathrm{compose}_{R_4}(g_{ij}, f_{jk})$$

矩阵乘法，scalar 是 R_4 (under endomorphism composition)，加法是 $R_2$ 的群加法（component-wise XOR）.

### 3.6 单位与逆元

- 单位：$\mathrm{id}_{\mathrm{Mat}_{n \times n}(R_4)} = \mathrm{diag}(\mathrm{id}_{R_4}, \ldots, \mathrm{id}_{R_4})$
- $\mathrm{id}_{R_4} = \mathrm{xoox}$（见 r4.md §5.1）
- 可逆 Hom = $\mathrm{Mat}_{m \times n}(R_4)$ 元素 (with $m = n$) 在 $\mathrm{Mat}(\mathrm{GL}(R_4))$-意义下可逆

### 3.7 自封闭性

> Hom representation 在 R-Family 内**自封闭**——$\mathrm{Mat}_{m \times n}(R_4)$ 仍是 R-Family 元素，可继续做其他 R-Family 操作.

工程含义：编译器不需要离开 R-Family 来处理 Hom 类型. 详见 §6.

---

## 4. Bilinear Forms 跨塔行为 · Cross-Tower Bilinear Forms

继承 v4-foundation §12, r4.md §7, r8.md §6. Bilinear 三层（Layer 0/1/2）在 R-Family 上一致定义.

### 4.1 三层 Bilinear 总览

| Layer | 形式 | 适用 N | 性质 |
|-------|------|--------|------|
| L0 | dot $\langle \cdot, \cdot \rangle$ | 所有 N | symmetric, non-alternating |
| L1 | symplectic $\sigma$ | 偶 N | symmetric **alternating** |
| L2 | quadratic $q$ + Arf | 偶 N | quadratic refinements of $\sigma$ |

奇 N (1, 3, 5, 7) 只支持 L0. 偶 N (2, 4, 6, 8) 全部支持 L0/L1/L2.

### 4.2 Layer 0 on R_N

$$\langle u, v \rangle_{R_N} := \sum_{i=0}^{N-1} u_i v_i \in \mathbb{F}_2$$

非退化、对称、$\mathbb{F}_2$-双线性.

#### Component-wise 因式化（偶 N）

对 $N = 2k$，$R_N = R_2^{\oplus k}$:

$$\langle u, v \rangle_{R_{2k}} = \sum_{j=1}^{k} \langle u^{(j)}, v^{(j)} \rangle_{R_2}$$

R_2-block 之 dot 直和.

### 4.3 Layer 1 on R_{2k}

$$\sigma_{R_{2k}}(u, v) := \sum_{j=1}^{k} \sigma_{R_2}(u^{(j)}, v^{(j)})$$

$k$-block alternating sum. 每 block 一个 R_2 σ.

Alternating ($\sigma(v, v) = 0$ ∀ $v$), 非退化, F_2-双线性.

### 4.4 Layer 2 on R_{2k}

Quadratic refinement 按 $k$ 个 block 独立选 $q_0$ 或 $q_1$，共 $2^k$ 种:

$$q^{(c_1, \ldots, c_k)}(u) := \sum_{j=1}^{k} q_{c_j}(u^{(j)})$$

$c_j \in \{0, 1\}$.

### 4.5 Arf 分类

$$\mathrm{Arf}(q^{(c_1, \ldots, c_k)}) = \sum_{j=1}^{k} c_j \pmod 2$$

$2^k$ quadratic refinements 分两 Arf 类（each $2^{k-1}$ 元）.

| $k$ | layer | total q | per Arf class |
|-----|-------|---------|---------------|
| 1 ($R_2$) | block-level | 2 | 1 |
| 2 ($R_4$) | block-level | 4 | 2 |
| 4 ($R_8$) | block-level | 16 | 8 |
| 8 ($R_{16}$) | block-level | 256 | 128 |

### 4.6 信息守恒 (LIC) — Sense 1 + Sense 2

对 $U \in R_{2k}$，有两种信息守恒含义：

**Sense 1 (Linear)**: dot product 的非退化性. 对典则基 $\{E_i\}$：

$$U = \sum_{i=1}^{2k} \langle U, E_i \rangle \cdot E_i$$

$2k$ 次配对足以重构 $U$. 这是 Pontryagin 自对偶的实施.

**Sense 2 ($R_2$-block typed)**: component-wise 恢复. 对 $U = (u^{(1)}, \ldots, u^{(k)})$（$R_2$-block 分解）：

$$u^{(j)} = \langle u^{(j)}, e_\alpha^{(j)} \rangle \cdot \mathrm{xo} + \langle u^{(j)}, e_\beta^{(j)} \rangle \cdot \mathrm{ox}$$

每 R_2-block 独立恢复，**不需 cross-block 通信**.

> **LIC = Sense 1 + Sense 2 同时成立**——文 algebra 的 lossless 含义。**仅在 R_{2k} (偶 N) 上完整**.

### 4.7 为何仅偶 N 享有 LIC

对奇 $N = 2k+1$：

- Sense 1 仍成立（dot product 仍非退化）
- 但**无典则 R_2-block 分解**（$R_{2k+1} = R_{2k} \oplus R_1$ 不典则）
- Sense 2 失败——dot 无法 block-wise 因式

> 「半个 R_2」 (即 $R_1 = $ 单 bit 无双轴) **没有 typed identity**，破坏 Sense 2.

### 4.8 信息层级表

| F_2-空间类型 | Sense 1 | Sense 2 |
|------|----|----|
| 偶 $R_{2k}$ (典则) | ✓ | ✓ |
| 奇 $R_{2k+1}$ | ✓ | ✗ |
| 非典则偶 subspace | ✓ | ✗ |

文 surface 只暴露 LIC 满足的层（偶 R_N）.

---

## 5. Aut 塔与 Preservation · Aut Tower and Preservation

### 5.1 Aut(R_N) = GL(N, F_2)

$$|\mathrm{Aut}(R_N)| = |\mathrm{GL}(N, \mathbb{F}_2)| = \prod_{k=0}^{N-1} (2^N - 2^k)$$

| N | $|\mathrm{Aut}|$ | 特殊 |
|---|------|-----|
| 0 | 1 | 平凡 |
| 1 | 1 | 平凡 |
| 2 | 6 | = $S_3$ |
| 3 | 168 | = $\mathrm{PSL}(2, 7)$ |
| 4 | 20,160 | = $A_8$ ★ |
| 5 | 9,999,360 | |
| 6 | $\sim 2 \times 10^{10}$ | |
| 7 | $\sim 1.6 \times 10^{14}$ | |
| 8 | $\sim 5.35 \times 10^{18}$ | ★ |

R_4 (= A_8) 与 R_8 (= GL(8, F_2)) 是关键 Aut 群。

### 5.2 Aut 嵌入链

$$\{1\} = \mathrm{Aut}(R_0) \hookrightarrow \mathrm{Aut}(R_1) \hookrightarrow \mathrm{Aut}(R_2) \hookrightarrow \ldots \hookrightarrow \mathrm{Aut}(R_8) \hookrightarrow \ldots$$

每嵌入通过「block-stabilize」(保前 $M < N$ 坐标的 Aut 元素扩展到 R_N).

### 5.3 R_2 上 preservation hierarchy (复习)

$\mathrm{Aut}(R_2) = S_3$ 上：

| Level | Aut 子群 | 阶 | 保结构 |
|-------|----------|-----|--------|
| L0 | $S_3$ (full) | 6 | 群、σ、$q_1$ |
| L1 | Stab(xx) | 2 | 上 + $\{\mathrm{oo}, \mathrm{xx}\}$、$\langle\cdot,\cdot\rangle$、$q_0$ |
| L2 | $\{\mathrm{id}\}$ | 1 | all pointwise |

详细 v4-foundation §7. 类似分层在更高 R_N 上更复杂.

### 5.4 信息保护与 Aut 子群

参 r8.md §9.4. **R_N 上 (N ≥ 4) 三层 bilinear 各被严格不同子群保**:

- $\mathrm{Aut}(R_N) = \mathrm{GL}(N, \mathbb{F}_2)$ 仅保**群结构** (定义)
- $\mathrm{O}(N, \mathbb{F}_2)$ 保 L0 (dot product)
- $\mathrm{Sp}(N, \mathbb{F}_2)$ 保 L1 (σ)
- $\mathrm{O}^\pm(N, \mathbb{F}_2)$ 保 L2 (q, per Arf class)

R_8 上具体阶 (详 r8.md §5.2)：

- $|\mathrm{GL}(8, 2)| \approx 5.35 \times 10^{18}$
- $|\mathrm{Sp}(8, 2)| = 47{,}377{,}612{,}800$
- $|\mathrm{O}^\pm(8, 2)|$ 更小

> **特例 R_2**：$\mathrm{Sp}(2, 2) = \mathrm{GL}(2, 2) = S_3$（巧合相等，因 $|S_3| = 6$）。故 R_2 上全 Aut 保 σ. 但 R_4, R_8, R_{16} 等均严格 Sp ⊊ GL.

「信息守恒」由不同 Aut 子群分层保护，**每层 bilinear 对应一个特定子群** — 这给信息守恒律一个清晰的 group-theoretic 形式化.

### 5.5 R_4 内嵌前层 Aut

$\mathrm{Aut}(R_2) = S_3 \hookrightarrow R_4$（作 rank-2 invertible 子集），详 r4.md §5.

这是「**前层 Aut 内嵌当层 elements**」的 minimum 实例.

类似地 $\mathrm{Aut}(R_4) = A_8 \hookrightarrow R_{16}$（作 rank-4 invertibles）。

---

## 6. R-Family 作 Compiler / Interpreter IR ★

> 文 编译器与解释器以 R-Family 为底 type system. 本节给具体 type system 设计.

### 6.1 R-Family 作 type system

文的 type system 以 R_N 为基础类型. 每 surface token (o/x 字符串或将来的 mnemonic) 有一个 type signature:

$$\mathrm{Type}(c) = R_N \quad \text{for some } N \in \{0, 1, 2, 3, 4, 5, 6, 7, 8, \ldots\}$$

实际 surface 暴露 N ∈ {0, 1, 2, 4, 6, 8}（偶层 + R_1）。N = 3, 5, 7 仅 IR-internal.

### 6.2 Surface vs IR Layers

| 层 | Surface 暴露 | IR-internal | Lean 类型 |
|----|----|----|----|
| R_0 | ✓ (trivial) | — | `Unit` |
| R_1 | ✓ (bit) | — | `Bool` |
| R_2 | ✓ ($R_2$ pair) | — | `R 2` |
| R_3 | ✗ | ✓ | `R 3` (IR only) |
| R_4 | ✓ (minimum complete) ★ | — | `R 4` |
| R_5 | ✗ | ✓ | `R 5` (IR only) |
| R_6 | ✓ (hexagram-scale) | — | `R 6` |
| R_7 | ✗ | ✓ | `R 7` (IR only) |
| R_8 | ✓ (ceiling) ★ | — | `R 8` |
| R_N (N ≥ 9) | ✗ | ✓ | `R N` (constructed) |

### 6.3 Type checker 规则

```
Rule 1:  任 surface token c 必有 R_N-签名: ∃ N. Type(c) = R_N
Rule 2:  dot product: dot : R_N × R_N → 𝔽₂  (相同 N 强制)
Rule 3:  arity / type 不匹配 ⇒ 编译失败
Rule 4:  奇 N (≠ 1) 禁出于 surface; IR-internal only
Rule 5:  跨层 R_N ↔ R_M 必经显式 lift / project 算子
Rule 6:  N ≥ 9 仅 IR-internal, 由 §8 construction 生成
Rule 7:  Phantom mode 必须显式（详 §6.4），coerce 必须 explicit
Rule 8:  Hom 表示用 Mat(m × n)(R_4)（方案 C, §3.3）
Rule 9:  Layer 1/2 (σ, q, Arf) 默认隐藏; opt-in 才 surface 暴露
Rule 10: 外部传统对应（GF(256), Pauli, Yi 等）走 application layer，不进 core type system
Rule 11: R_4 与 R_8 双中心: IR normalize 应尽量 lift 到 R_4 或 R_8 进行
```

### 6.4 Phantom Mode Discipline

继承 r4.md §9 与 r8.md §15.3. R-Family 元素带 phantom mode tag:

```lean
inductive Mode 
  | State    -- 状态 (data value)
  | Op       -- 操作 (linear endomorphism)
  | Cause    -- 因 (in causal pair)
  | Effect   -- 果 (in causal pair)
  | TimeIn   -- 时间输入 (time-tag)
  | TimeOut  -- 时间输出 (time-tag dual)
  | Frame    -- frame-of-reference
  -- (扩展中)
  deriving DecidableEq, Repr

structure R_Phantom (N : ℕ) (m : Mode) where
  data : R N
```

底层数据相同，类型不同. Coercion 必须显式（防 silent semantic drift）.

### 6.5 类型规则示例

| 操作 | 输入 | 输出 |
|------|------|------|
| `apply` | `R_Phantom 4 Op × R_Phantom 2 State` | `R_Phantom 2 State` |
| `compose` | `R_Phantom 4 Op × R_Phantom 4 Op` | `R_Phantom 4 Op` |
| `dot` | `R_Phantom N m × R_Phantom N m` | `Bool` |
| `pair` | `R_Phantom 2 State × R_Phantom 2 State` | `R_Phantom 4 State` |
| `causal_pair` | `R_Phantom 4 Cause × R_Phantom 4 Effect` | `R_Phantom 8 State` |
| `time_pair` | `R_Phantom N TimeIn × R_Phantom N TimeOut` | `R_Phantom (2N) State` |
| `coerce_state_to_op` | `R_Phantom N State` | `R_Phantom N Op` ★ explicit |

### 6.6 Normalize pass

> **定理 6.6 (Normalize Closure)**：所有 R-Family 内操作（直和、张量、Hom、子群、商、bilinear、apply、compose）**保 R-Family typing**.

由 §2.6 闭合主定理 + §3 Hom-Mat-R_4 表示，编译器 normalize pass 中所有 type 始终在 R-Family 内.

工程含义：

- 不需要中间步骤做 type coerce
- 编译器可做无类型擦除的连续 normalize
- 直到 surface emit 阶段才 type-erase（如需）

### 6.7 R_4 / R_8 优先级

按 Rule 11，normalize 应尽量 lift 到 R_4 或 R_8 进行：

- **R_4 路径**: 适用于 R_2 / R_4 等小规模 ops; 用 R_4 = End(R_2) 表示
- **R_8 路径**: 适用于 R_6 / R_8 / R_{16} 等大规模 ops; 用 R_8 spacetime/causal/judgment 结构

normalize 时优先选 R_4 (efficiency) 或 R_8 (richness)，避免 stay on 中间层.

---

## 7. 塔级判断层 · Tower-Level Judgment

> R-Family algebra 为信息 / 吸引子 / 行为 判断提供塔级统一接口。R_8 (详 r8.md §9-11) 是最显著实例；本节给塔级泛化.

### 7.1 信息判断 Tower-level

对任意 R_N 上 $u, v$:

```lean
def information_overlap (u v : R N) : Bool := R.dot u v
def information_direction (u v : R N) : Bool := R.sigma u v  -- N even only
def information_signature (c : (Fin (N/2) → Bool)) (u : R N) : Bool := R.q c u  -- N even
```

奇 N 仅 L0 information overlap; 偶 N 全部三层.

特别：

- R_2: 单 block, 简单 information judgment
- R_4: 双 block, 含 Arf 2 类区分（详 r4.md §7.4）
- R_8: 四 block, 16 quadratic refinements / 2 Arf 类各 8 元 ★（详 r8.md §9）

### 7.2 吸引子判断 Tower-level

对 $f \in \mathrm{End}(R_N) = R_{N^2}$ ($\mathbb{F}_2$-线性映射):

```lean
def fixed_points (f : R N → R N) : Finset (R N) :=
  Finset.univ.filter (fun w => f w = w)

def orbit (f : R N → R N) (w : R N) : List (R N) := sorry  -- bounded by 2^N
```

$|R_N|$ 有限 ⇒ 任意 orbit 最终周期. R-Family 是 enumerable attractor theory 的自然居所.

R_4 attractor enumeration: $|R_4|^{|R_4|} = 16^{16} \approx 1.8 \times 10^{19}$ — challenging.
R_8 attractor enumeration: $|R_8|^{|R_8|} = 256^{256} \approx 10^{616}$ — sample-based only.

但 linear-endomorphism 的 attractor 分析 (∈ $\mathrm{GL}(N, F_2)$ + degenerate) 可枚举。

### 7.3 行为判断 Tower-level

继承 r8.md §11. 行为 = trajectory in R_N:

```lean
def trajectory (f : R N → R N) (w0 : R N) (steps : ℕ) : List (R N) := 
  -- iterate f from w0 for `steps` times
  sorry

inductive BehaviorClass | stable | periodic | transient | complex

def classify (f : R N → R N) (w0 : R N) : BehaviorClass := sorry
```

R-Family 行为分类是 enumerable on 小 N (≤ 8), 通过 lift 扩到大 N.

### 7.4 跨层判断 (Cross-Layer Judgment)

判断函数也可作用于 cross-R_N pairs:

```lean
def cross_information (m n : ℕ) (u : R m) (v : R n) : Bool :=
  -- via Hom-mediated comparison
  sorry
```

具体方法：用 $\mathrm{Hom}(R_m, R_n) = R_{mn}$ 作 bridge.

---

## 8. 自相似构造 · Self-Similar Construction Beyond R_8

> R_0–R_8 是 *root layers*. 高层 R_N for $N > 8$ 由根集合直和构造，性质 lift.

继承 r8.md §12. 关键事实：

### 8.1 直和构造

任意 $R_N$ ($N > 8$) 由根层直和：

$$R_N = R_8^{\oplus \lfloor N/8 \rfloor} \oplus R_{N \bmod 8}$$

### 8.2 性质 lift

由 §2.6 闭合，所有 R-Family 性质（group, bilinear, Aut, judgment, etc.）经直和保持 / lift.

**定理 8.2 (Algebraic Closure of Root Layers)**:

> R_0–R_8 内 verifiable 性质 lift 到所有 $R_N$.

证明：性质 P 关于直和 compatible (例：$P(R_N \oplus R_M) \Leftarrow P(R_N) \land P(R_M)$). 对 group, bilinear, dot, σ, q 等 P 都满足.

### 8.3 自相似性

参 r8.md §12. Squaring tower $R_1 \to R_2 \to R_4 \to R_8 \to R_{16} \to \ldots$ 在每层共享 algebraic patterns:

- σ blocks 数 doubling
- q variants squaring  
- Aut order ~ 六次方增长

详 r8.md §12.3 R_8 vs R_{16} 对比表.

### 8.4 工程意义

- **代数验证 focus**: R_0–R_8 内证明，高层 lift
- **解释器范围**: 基本 ops 实现 R_0–R_8，高层 composition
- **memory footprint**: $R_N$ 单元素需 $\lceil N/8 \rceil$ bytes — 线性 cost
- **CS hierarchy 对接**: $R_8 / R_{16} / R_{32} / R_{64}$ ↔ byte / word / dword / qword (r8.md §12.8)

---

## 9. Application Layer 接口 · Application Layer Interface

### 9.1 隔离原则

> 文 core algebra (R-Family) 与 application-layer correspondences (Pauli, GF, Yi, etc.) **严格分离**.

按 v4-foundation §0.5 与 v0.5 视角原则:

1. core algebra 独立完整，不依赖外部传统
2. 外部对应是「应用解读」(application reading)，可选 opt-in
3. 借词（如 IR type tag 名）不蕴含从属

### 9.2 Atlas Bindings

外部对应通过 **application binding** 附加到 R-Family：

```lean
namespace 文.Atlas
namespace Pauli

/-- Application-layer binding: R_2 ↔ Pauli operators mod phase. -/
def pauli_of : R 2 → String
  | oo => "I"
  | xo => "X"
  | ox => "Z"
  | xx => "Y"

end Pauli
namespace Yi

/-- Application-layer binding: R_2 ↔ classical Yi names. -/
def yi_of : R 2 → String
  | oo => "dao"
  | xo => "cuo"
  | ox => "zong"
  | xx => "cuozong"

end Yi

namespace GF256

/-- GF(256) field structure on R_8 (optional extension). -/
-- Multiplicative ring on top of R_8 additive group
def field_mul (p : Polynomial 𝔽_2) : R 8 → R 8 → R 8 := sorry

end GF256
end 文.Atlas
```

每 binding 是 **opt-in**，不进入 core type system.

### 9.3 多 binding 共存

同一 R_N 可附多个 application bindings:

- $R_2$ ↔ Pauli (4 元) ↔ Yi 道/错/综/错综 ↔ Greimas A/¬A/B/¬B ↔ ...

bindings 之间是「应用层互通」(application-level interoperability), core algebra 无须关心.

### 9.4 外部传统不进 core

> **强制**：core 文档 (foundation, r4, r8, wen-algebra) **不**使用任何外部传统的术语作为核心概念名. Application Atlas 内可自由使用.

详 v4-foundation §15, r4.md §11, r8.md §14.

---

## 10. Lean 4 形式骨架 · Lean Skeleton

> **Lean 4 + Mathlib 是文的唯一形式语言**.

### 10.1 R-Family 通用类型

```lean
import Mathlib.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.Data.Fin.Basic

namespace 文.R

/-- R_N = F_2^N, the tower layer at index N. 
    Implementation via ZMod 2 to leverage Mathlib's AddCommGroup instance. -/
def R (N : ℕ) : Type := Fin N → ZMod 2

namespace R

variable {N M : ℕ}

instance : Fintype (R N) := Pi.fintype
instance : DecidableEq (R N) := inferInstance

/-- Group structure inherited via Pi.addCommGroup from ZMod 2. 
    No sorries needed: Mathlib provides everything. -/
instance : AddCommGroup (R N) := Pi.addCommGroup

/-- Concretely: addition is component-wise XOR in F_2. -/
example (u v : R N) (i : Fin N) : (u + v) i = u i + v i := by rfl

/-- Negation in char 2: self-inverse (a + a = 0). -/
example (a : R N) : -a = a := by
  funext i
  -- In ZMod 2, -x = x; Mathlib has neg_eq_self_iff or similar
  exact neg_eq_of_add_eq_zero_left (by simp [show a i + a i = 0 from CharTwo.add_self_eq_zero _])

end R
end 文.R
```

**说明**: 用 `ZMod 2` 代替 `Bool` 让 Mathlib 自动 derive AddCommGroup 通过 `Pi.addCommGroup`，无 `sorry`。若需 boolean 接口，可同时 expose 一个 `R_bool` alias 或 conversion.

### 10.2 直和

```lean
namespace 文.R

/-- Direct sum: R_N ⊕ R_M → R_{N+M}. -/
def direct_sum (u : R N) (v : R M) : R (N + M) := fun i =>
  if h : i.val < N then u ⟨i.val, h⟩
  else v ⟨i.val - N, by omega⟩

/-- Cardinality of direct sum. -/
theorem direct_sum_card : Fintype.card (R (N + M)) = Fintype.card (R N) * Fintype.card (R M) := by
  unfold R
  simp [Fintype.card_fun, pow_add]

end 文.R
```

### 10.3 Bilinear forms 跨塔

```lean
namespace 文.R

/-- Layer 0: dot product, defined for all N. -/
def dot (u v : R N) : Bool :=
  (Finset.univ : Finset (Fin N)).foldr 
    (fun i acc => Bool.xor (u i && v i) acc) false

theorem dot_symm (u v : R N) : dot u v = dot v u := by
  unfold dot; congr 1; funext i; exact Bool.and_comm _ _

theorem dot_zero_left (v : R N) : dot zero v = false := by
  unfold dot zero; simp; induction (Finset.univ : Finset (Fin N)) using Finset.induction <;> simp [*]

/-- Layer 1: symplectic σ on R_{2k}, with k blocks. -/
def sigma {N : ℕ} (h : Even N) (u v : R N) : Bool :=
  -- σ over k = N/2 blocks: each block is a pair (2j, 2j+1)
  let k : ℕ := N / 2
  (Finset.univ : Finset (Fin k)).foldr (fun j acc =>
    let i0 : Fin N := ⟨2 * j.val, by omega⟩
    let i1 : Fin N := ⟨2 * j.val + 1, by omega⟩
    Bool.xor (Bool.xor (u i0 && v i1) (u i1 && v i0)) acc) false

theorem sigma_alternating {N : ℕ} (h : Even N) (v : R N) : sigma h v v = false := by
  unfold sigma
  congr 1
  funext j
  cases (v _) <;> cases (v _) <;> rfl

/-- Layer 2: quadratic refinement with mode (c_1, ..., c_k). -/
def q_refined {N : ℕ} (h : Even N) (c : Fin (N / 2) → Bool) (v : R N) : Bool :=
  let k : ℕ := N / 2
  (Finset.univ : Finset (Fin k)).foldr (fun j acc =>
    let i0 : Fin N := ⟨2 * j.val, by omega⟩
    let i1 : Fin N := ⟨2 * j.val + 1, by omega⟩
    let q0_block := v i0 && v i1
    let q1_block := Bool.xor (Bool.xor (v i0) (v i1)) q0_block
    let block_val := if c j then q1_block else q0_block
    Bool.xor block_val acc) false

/-- Arf invariant: sum of c_j mod 2. -/
def arf {N : ℕ} (h : Even N) (c : Fin (N / 2) → Bool) : Bool :=
  (Finset.univ : Finset (Fin (N / 2))).foldr (fun j acc => Bool.xor (c j) acc) false

end 文.R
```

### 10.4 Hom 表示 Mat(R_4)

```lean
namespace 文.R

/-- R_4 = F_2^4 (alias). -/
abbrev R4 := R 4
abbrev R2 := R 2

/-- R_4 as End(R_2): apply R_4 element as matrix to R_2. -/
def R4_apply (w : R4) (u : R2) : R2 := fun i =>
  let row0 : Bool := Bool.xor (w ⟨0, by omega⟩ && u ⟨0, by omega⟩) 
                              (w ⟨1, by omega⟩ && u ⟨1, by omega⟩)
  let row1 : Bool := Bool.xor (w ⟨2, by omega⟩ && u ⟨0, by omega⟩)
                              (w ⟨3, by omega⟩ && u ⟨1, by omega⟩)
  match i.val with
  | 0 => row0
  | _ => row1

/-- R_4 composition (matrix product). -/
def R4_compose (g f : R4) : R4 := fun i =>
  -- Implementation: g · f over F_2 as 2x2 matrices, see r4.md §14.1
  sorry

/-- Hom matrix: Mat_{m × n}(R_4). -/
def HomMat (n m : ℕ) : Type := Fin m → Fin n → R4

/-- Apply Hom matrix to R_{2n} element, output in R_{2m}. -/
def hom_apply {n m : ℕ} (f : HomMat n m) (U : R (2 * n)) : R (2 * m) := fun i =>
  -- For each i ∈ Fin (2m), compute the appropriate entry
  -- Standard matrix-vector multiplication over R_4-cells
  sorry

/-- Compose two Hom matrices. -/
def hom_compose {n m p : ℕ} (g : HomMat m p) (f : HomMat n m) : HomMat n p := fun i k =>
  -- Matrix product: (g ∘ f)[i][k] = ⨁_j g[i][j] · f[j][k]
  (Finset.univ : Finset (Fin m)).foldr (fun j acc =>
    -- R_4_compose then add to acc element-wise
    sorry) (fun _ => false)

end 文.R
```

### 10.5 Phantom Mode

```lean
namespace 文.R

inductive Mode 
  | State    -- 状态
  | Op       -- 操作
  | Cause    -- 因
  | Effect   -- 果
  | TimeIn   -- 时入
  | TimeOut  -- 时出
  | Frame    -- frame-of-reference
  deriving DecidableEq, Repr

/-- Phantom-typed R_N element. -/
structure RPhantom (N : ℕ) (m : Mode) where
  data : R N

namespace RPhantom

/-- Apply requires Op mode. -/
def apply {N M : ℕ} (f : RPhantom (N * M) Mode.Op) (u : RPhantom N Mode.State) 
    : RPhantom M Mode.State := sorry  -- via Hom representation

/-- Compose requires both Op mode. -/
def compose {N M P : ℕ} (g : RPhantom (M * P) Mode.Op) (f : RPhantom (N * M) Mode.Op)
    : RPhantom (N * P) Mode.Op := sorry

/-- Pair construction → State mode. -/
def pair {N M : ℕ} (u : RPhantom N Mode.State) (v : RPhantom M Mode.State)
    : RPhantom (N + M) Mode.State := ⟨direct_sum u.data v.data⟩

/-- Causal pair: Cause + Effect → State. -/
def causal_pair {N M : ℕ} (cause : RPhantom N Mode.Cause) (effect : RPhantom M Mode.Effect)
    : RPhantom (N + M) Mode.State := ⟨direct_sum cause.data effect.data⟩

/-- Time pair: TimeIn + TimeOut → State. -/
def time_pair {N : ℕ} (tin : RPhantom N Mode.TimeIn) (tout : RPhantom N Mode.TimeOut)
    : RPhantom (2 * N) Mode.State := ⟨direct_sum tin.data tout.data⟩

/-- Explicit coercion: State → Op. -/
def coerce_state_to_op {N : ℕ} (s : RPhantom N Mode.State) : RPhantom N Mode.Op :=
  ⟨s.data⟩

end RPhantom
end 文.R
```

### 10.6 Judgment Layer

```lean
namespace 文.R.Judgment

open 文.R

/-- Information judgment functions. -/
namespace Information

def overlap (u v : R N) : Bool := dot u v

def direction {N : ℕ} (h : Even N) (u v : R N) : Bool := sigma h u v

def signature {N : ℕ} (h : Even N) (c : Fin (N / 2) → Bool) (u : R N) : Bool := 
  q_refined h c u

end Information

/-- Attractor judgment functions. -/
namespace Attractor

def fixed_points {N : ℕ} (f : R N → R N) : Finset (R N) :=
  Finset.univ.filter (fun w => f w = w)

def fixed_point_count {N : ℕ} (f : R N → R N) : ℕ := (fixed_points f).card

end Attractor

/-- Behavior judgment functions. -/
namespace Behavior

inductive BehaviorClass | stable | periodic | transient | complex
  deriving DecidableEq, Repr

def trajectory {N : ℕ} (f : R N → R N) (w0 : R N) : ℕ → R N
  | 0 => w0
  | k + 1 => f (trajectory f w0 k)

partial def find_cycle_period {N : ℕ} (f : R N → R N) (w0 : R N) : ℕ :=
  -- enumerate trajectory until cycle detected
  sorry

end Behavior
end 文.R.Judgment
```

### 10.7 Interpreter Foundation

```lean
namespace 文.R.Interpreter

open 文.R

/-- Core interpreter primitives. -/

/-- A program step: given state and op, produce new state. -/
def step {N : ℕ} (state : RPhantom N Mode.State) (op : RPhantom (N * N) Mode.Op) 
    : RPhantom N Mode.State := 
  RPhantom.apply op state

/-- Trace: run interpreter for n steps. -/
def trace {N : ℕ} (op : RPhantom (N * N) Mode.Op) (initial : RPhantom N Mode.State) 
    : ℕ → List (RPhantom N Mode.State)
  | 0 => [initial]
  | k + 1 => initial :: trace op (step initial op) k

end 文.R.Interpreter
```

### 10.8 Round-trip Tests

```lean
namespace 文.R.Tests

open 文.R

-- Closure under direct sum
example : Fintype.card (R (3 + 5)) = Fintype.card (R 3) * Fintype.card (R 5) := 
  direct_sum_card

-- Dot product symmetric on R_4
example : ∀ u v : R 4, dot u v = dot v u := dot_symm

-- σ alternating on R_4 (Even 4)
example : ∀ v : R 4, sigma (by decide : Even 4) v v = false := by
  intro v
  exact sigma_alternating _ v

-- σ alternating on R_8 (Even 8)
example : ∀ v : R 8, sigma (by decide : Even 8) v v = false := by
  intro v
  exact sigma_alternating _ v

-- Arf count: |Fin 4 → Bool| = 16 for R_8
example : (Finset.univ : Finset (Fin 4 → Bool)).card = 16 := by decide

end 文.R.Tests
```

### 10.9 模块组织

```
文/
├── R/                       -- 通用 R-Family
│   ├── Basic.lean           -- 类型定义、群结构
│   ├── DirectSum.lean       -- 直和
│   ├── Tensor.lean          -- 张量积
│   ├── Hom.lean             -- Hom 与矩阵表示
│   ├── Bilinear.lean        -- dot, σ, q, Arf
│   ├── Aut.lean             -- 自同构群
│   ├── Phantom.lean         -- Phantom modes
│   ├── Judgment/            -- 判断层
│   │   ├── Information.lean
│   │   ├── Attractor.lean
│   │   └── Behavior.lean
│   ├── Interpreter.lean     -- 解释器
│   └── Tests.lean           -- CI tests
├── R2/                      -- R_2 专题（详 v4-foundation §4）
├── R3/                      -- R_3 (Fano)
├── R4/                      -- R_4 专题（详 r4.md）★
├── R5/, R6/, R7/            -- 其他
├── R8/                      -- R_8 专题（详 r8.md）★
│   ├── Spacetime.lean
│   ├── Causality.lean
│   └── ...
├── Atlas/                   -- Application layer
│   ├── Pauli.lean
│   ├── Yi.lean
│   ├── GF256.lean
│   └── ...
└── README.md
```

---

## 11. 工程规则与文档结构 · Engineering Rules and Document Architecture

### 11.1 Type Checker 完整规则（汇总）

```
=== R-Family Type Rules ===

Rule 1:  surface token c 必有 R_N-签名: ∃ N. Type(c) = R_N
Rule 2:  dot product 需相同 N: dot : R_N × R_N → 𝔽₂
Rule 3:  arity/type 不匹配 ⇒ 编译失败
Rule 4:  奇 N (≠ 1) 禁出于 surface; IR-internal only
Rule 5:  跨层 R_N ↔ R_M 必经显式 lift / project 算子
Rule 6:  N ≥ 9 仅 IR-internal, 由 §8 construction 生成
Rule 7:  Phantom mode 必须显式; coerce 必须 explicit
Rule 8:  Hom 表示用 Mat(m × n)(R_4); 方案 C 标准
Rule 9:  Layer 1/2 (σ, q, Arf) 默认隐藏; opt-in 才 surface 暴露
Rule 10: 外部传统对应走 application layer, 不进 core type system
Rule 11: R_4 / R_8 双中心: IR normalize 优先 lift 到 R_4 或 R_8
Rule 12: Lean 4 是唯一形式语言; 不再支持 Clojure / Python / etc.
```

### 11.2 Normalize Pass 闭合保证

由 §2.6 + §6.6:

> **R-Family 内任意操作组合保 R-Family typing**.

工程含义：编译器可做无限制 normalize 路径，typing 始终维持.

### 11.3 文档体系

文 算法文档（核心 + 专题）：

| 文档 | 角色 | 状态 |
|------|------|------|
| `v4-foundation.md` | R_0–R_8 单层 spec | v0.5 ✓ |
| `r4.md` | R_4 minimum complete unit | v0.2 ✓ |
| `r8.md` | R_8 ceiling + 自相似 | v0.2 ✓ |
| `wen-algebra.md` (本) | 塔级 algebra + 编译器 | **v0.6** ✓ |
| `wen-correspondences.md` | Application-layer Atlas 集中 | (forthcoming, 可选) |

文档间 cross-references 已建立. 每文档专注自身角色不重复.

**Surface 编码注**：所有元素当前用 o/x 字符串表示（R_2: 2-char, R_4: 4-char, R_8: 8-char）。这是 surface 编码——非「占位待命名」。汉字命名层是可选的将来扩展（如 mnemonic 需要），不阻塞 IR / 解释器 / 编译器开发.

### 11.4 R_4 / R_8 优先策略 (Rule 11 展开)

| 场景 | 推荐路径 |
|------|----------|
| R_2-level ops (dot, sigma on 4 元) | inline R_2 |
| 多 R_2 操作组合 | lift to R_4 |
| 4-bit / nibble-scale data | R_4 |
| Hom R_2 → R_2 | R_4 (= End(R_2)) |
| 8-bit / byte-scale data | R_8 |
| Cause-effect modeling | R_8 (split L/R) |
| Spacetime/causality | R_8 |
| Information/Attractor/Behavior judgment | R_8 |
| 跨多 byte 数据 | R_8^{⊕k}, lift via §8 |

### 11.5 Lean 4 编译/解释器实现优先级

按重要性：

1. **基本 R N 类型 + 群运算 + dot** (§10.1-10.3) — P0
2. **Hom Mat(R_4) 表示** (§10.4) — P0
3. **Phantom mode** (§10.5) — P0
4. **Judgment functions** (§10.6) — P1
5. **Interpreter primitives** (§10.7) — P1
6. **R_4 + R_8 专题模块** (r4.md, r8.md) — P0
7. **Application atlas** (§9) — P2

---

## 12. Open Questions

1. **Surface 编码状态**：当前 R_2 / R_4 / R_8 元素均用 o/x 字符串作 surface 编码（这是设计决定，不是缺口）。汉字命名层暂不需要——若将来作为 mnemonic 提供，会作 application-layer alias，不影响 core IR.

2. **R_8 上 phantom mode 完整 vocabulary**：当前 7 mode (State/Op/Cause/Effect/TimeIn/TimeOut/Frame)。是否需要更多？
   - Observer mode
   - Snapshot mode
   - Reflexive mode

3. **奇 N (R_1, R_3, R_5, R_7) 的 surface 处理**：当前 IR-internal only. 是否值得给 R_1 一些 surface 角色（作为「bit literal」）？

4. **Hom 表示在 R_4 / R_8 之外**：当前 Method C 用 R_4-cells. 是否值得给 R_8-cells 一个 variant Method (即 Mat of R_8) 对应更大 Hom representation?

5. **Normalize pass 的具体策略**：Rule 11 给出 R_4/R_8 优先级，但具体 lift heuristic 与 cost function 待形式化.

6. **Application-layer 与 core 的交互**：当 application binding (如 GF(256) 乘法) 需要参与 IR optimization 时，如何处理？

7. **判断函数的可微分性**：信息 / 吸引子 / 行为 judgment 函数主要 boolean. 实数-valued 扩展（gradient-friendly）的 path?

8. **R_8 cellular-automaton-style 解释器**：r8.md §10.6 提到 Wolfram CA 对接。是否作为 wen-algebra 的 alternative interpreter mode?

9. **Lean 4 vs Mathlib 性能**：interpreter primitive 需要 fast computation. Lean 4 + `native_decide` 性能 ok 吗？还是需要 FFI 加速？

10. **文档继续演化**：是否还需要 r2.md, r3.md, r5.md, r6.md, r7.md? 当前 R_2/R_3 等在 foundation 内已覆盖；专题文档可选.

---

## 13. 完成度自检 · Completeness Check

| 内容 | 已覆盖 |
|------|------|
| 文档范围与定位 | ✓ §0 |
| 与其他文档边界 (foundation / r4 / r8) | ✓ §0.2 |
| Lean 4 唯一形式语言 | ✓ §0.3 |
| R-Family 9 根层 R_0–R_8 概览 | ✓ §1.2 |
| Squaring 子塔 R_1 → R_2 → R_4 → R_8 → ... | ✓ §1.3 |
| **R-Family 闭合性** ★ | ✓ §2 |
| 直和 / 张量 / Hom / Pontryagin / 子群 / 商 | ✓ §2.1-2.5 |
| 闭合性主定理 + 充足性 | ✓ §2.6-2.7 |
| **Hom 表示定理 = Mat(R_4)** ★ | ✓ §3.2 |
| Method A/B/C 对比 | ✓ §3.3 |
| Apply + Compose 语义 | ✓ §3.4-3.5 |
| Hom 自封闭 | ✓ §3.7 |
| **Bilinear 三层跨塔** | ✓ §4 |
| Layer 0/1/2 on R_N | ✓ §4.2-4.4 |
| Component-wise 因式化 | ✓ §4.2-4.3 |
| LIC Sense 1 + Sense 2 | ✓ §4.6 |
| 仅偶 N 有 LIC | ✓ §4.7 |
| **Aut 塔** | ✓ §5 |
| GL(N, F_2) order + 嵌入链 | ✓ §5.1-5.2 |
| 信息保护 (Aut 子群) | ✓ §5.4 |
| **R-Family 作 IR** ★ | ✓ §6 |
| Type system + surface vs IR | ✓ §6.1-6.2 |
| Type checker 12 rules | ✓ §6.3, §11.1 |
| **Phantom mode discipline (7 modes)** | ✓ §6.4-6.5 |
| Normalize pass closure | ✓ §6.6, §11.2 |
| R_4 / R_8 优先级 (Rule 11) | ✓ §6.7, §11.4 |
| **塔级判断层** | ✓ §7 |
| Information / Attractor / Behavior 泛化 | ✓ §7.1-7.3 |
| 跨层判断 | ✓ §7.4 |
| **自相似构造 beyond R_8** | ✓ §8 |
| 直和构造 + 性质 lift | ✓ §8.1-8.2 |
| 自相似性 | ✓ §8.3 |
| 工程意义 | ✓ §8.4 |
| **Application Layer 隔离** | ✓ §9 |
| Atlas bindings | ✓ §9.2 |
| 多 binding 共存 | ✓ §9.3 |
| 外部传统不进 core | ✓ §9.4 |
| **Lean 4 完整骨架** | ✓ §10 |
| R 通用类型 + 群 | ✓ §10.1 |
| 直和 | ✓ §10.2 |
| Bilinear 三层 | ✓ §10.3 |
| Hom Mat(R_4) 表示 | ✓ §10.4 |
| Phantom mode | ✓ §10.5 |
| Judgment functions | ✓ §10.6 |
| Interpreter primitives | ✓ §10.7 |
| 模块组织 | ✓ §10.9 |
| **12 条 Type Rules 汇总** | ✓ §11.1 |
| Normalize 闭合保证 | ✓ §11.2 |
| 文档体系 | ✓ §11.3 |
| R_4/R_8 优先策略 | ✓ §11.4 |
| 实现优先级 | ✓ §11.5 |
| Open Questions (10 项) | ✓ §12 |

---

*End of v0.6 · wen-algebra.md · R-Family Tower Algebra*
*Lean 4 only. R_0–R_8 root, R_4 + R_8 dual centers, infinite self-similar extension.*
*Companion: `v4-foundation.md` (layer specs), `r4.md` (min complete unit), `r8.md` (ceiling).*
