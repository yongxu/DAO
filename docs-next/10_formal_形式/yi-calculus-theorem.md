> **[Superseded 2026-05-15]** — Canonical doctrine is now [`wen-algebra.md`](wen-algebra.md) v0.6. Theorems A–K survive intact; they now apply to the R-Family `R_N := F₂^N` parametric tower rather than the Yi-specific Cell256 framing. Cardinality and rank facts are unchanged; the Yi-tradition naming (Yao / Trigram / Hexagram / Shi V₄ {道,已,今,未}) is now Atlas-layer per [`v4-foundation.md`](v4-foundation.md) §0.4 ("字符语义全部冻结，只看结构") and [`wen-algebra.md`](wen-algebra.md) §9.
>
> **Updated v1.0.2 reference**: see [`wen-substrate.md`](wen-substrate.md) §3.6 for parametric framing — Theorems A–K are properties of the R-Family-over-{F_2, ℝ, ℂ, ℂ_p, …} substrate; the F_2 instance shown here is one of many.

---

# 易微积分定理：从爻到 R8 (256-Cell) 的 (Z/2)ⁿ 自相似完整刻画

> 状态：定理稿 · R8 闭合版（2026-05-10，R7/R8 拆层版）。
> 作用：把"易"作为完整自描述系统的最小代数核——从 R1 (爻) 到 R8 (256-Cell)——给出 **(Z/2)ⁿ 自相似 V₄-Klein-acting 系统**的代数–微积分定理。R-hierarchy 每层 +1 bit 的 (Z/2) 自相似规律下，R7 = (Z/2)⁷ = 128 引入 **因 (yīn, past-trace bit)**，R8 = (Z/2)⁸ = 256 引入 **果 (guǒ, future-projection bit)**。Shi V₄ = {道, 已, 今, 未} 不是 R7 单层 atom，而是 R7 ⊗ R8 之 emergent (因, 果) ∈ Bool² ≅ V₄。**「道」作为 V₄ Klein 群的单位元 first-class 进入本体**，整个体系无任何非 (Z/2) 异类。
> 配套：[`yi-as-meta-framework.md`](yi-as-meta-framework.md) 哲学层 · [`64-hexagram-grid.md`](64-hexagram-grid.md) 64 卦表 · [`sanben-sijieduan-grid.md`](sanben-sijieduan-grid.md) 内容线 · [`layer-axis-graph.md`](layer-axis-graph.md) 三轴图
> 形式锚：[`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) · [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) · [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — Theorems A–F 已 Lean 证明 (0 sorry / 0 项目自定义 axiom)；Theorems H–K 落 `Cell128.lean` (R7) + `Cell256.lean` (R8) + `Cell256Stratify.lean` (refactor pending)
>
> **命名 caveat**：R7 元 = 因, R8 元 = 果, **provisional naming**（哲学最深的 cause-effect 对偶；佛/Pearl 形式科学；古义稳）。等 Lean 落 R7/R8 后回看是否改换为 **印 / 投** (Husserl 现象学 retention/protention) 或 **始 / 终** (Yi-native 系辞「原始要终」)。详见第十六部分附录。

---

## 第零部分：主定理摘要

本文证明：**易作为完整自描述系统的最小代数核——从 R1 到 R8——是 (Z/2)ⁿ 自相似 V₄-Klein-acting 系统**，无任何非 (Z/2) 因子。

具体定理链：

| # | 定理 | 内容 | Lean 状态 | Lean 文件 |
|---|---|---|---|---|
| A | R3 (本征 4+4) | zong involution 强制 4 substrate + 4 mark 划分 | ✓ | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| B | substrate = 定常波 | 4 本是 Σ³ 上仅有的 4 个 boundary-preserving 配置 | ✓ | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| C | mark = 4 phase quadrant | 4 征是 (sum, endpoint-difference) phase plane 的 4 representative | ✓ | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| D | cuo–zong V₄ 代数 | cuo = P (parity), zong = T (time-reversal), 错综 = PT | ✓ | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean), [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |
| E | substrate–mark = ∫–d 划分 | 离散 Newton-Leibniz duality | ✓ | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| F | R6 (64 卦 4 quadrant) | 本本/本征/征本/征征 各 16，cuo 保 quadrant，zong 跨换 mixed | ✓ | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| G | 与连续 1D 标量场对应 | 8 trigram = 3-sample sign-pattern 的完全枚举 | informal | — |
| **H** | **R7 = (Z/2)⁷ = 128 + 因 (yīn) axis** | **R7 = R6 × YinBit = Hexagram × {0,1}；引入「过去印记」第 7 个 bit** | ✓ | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| **I** | **R8 = (Z/2)⁸ = 256 + 果 (guǒ) axis** | **R8 = R7 × GuoBit = Hexagram × Bool²；引入「未来投影」第 8 个 bit** | ✓ | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| **J** | **Shi V₄ = (因, 果) emerges at R8** | **{道, 已, 今, 未} 不是 R7 单层 atom，是 R7⊗R8 双 axis tensor；道 = (0,0) = V₄ identity** | ✓ | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean), [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) |
| **K** | **R-hierarchy R1..R8 全 (Z/2)ⁿ closure** | **5 层均纯 (Z/2)ⁿ，无任何非 (Z/2) 因子；R8 = 256 = (Z/2)⁸ 是真闭合** | ✓ (`R8_complete`) | [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean), [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean), [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |

A-F 是 native_decide 可证；G 涉及连续函数；H-K 已落 Lean (Cell128 / Cell256 / Cell256Stratify), `R8_complete` bundle 仅依赖 `propext` + `native_decide` 公理 (无项目自定义 axiom).

**关键修正**：之前版本把 R7 = 256 = (Z/2)⁶ × V₄ 当作单层（V₄ Shi 整体当 R7 atom）是层级压缩错误。正确的 (Z/2)ⁿ 自相似规律下，每个独立 binary axis = 一个独立 R-layer。Shi V₄ 不是单层结构，而是 R7/R8 双层之 emergent。

---

## 第一部分：形式 setup

### Definition 1.1（爻空间 R1）

设 $\Sigma := \{+1, -1\}$，元素读作 $\text{阳} = +1$, $\text{阴} = -1$。$|\Sigma| = 2 = (\mathbb{Z}/2)^1$.

### Definition 1.2（三爻卦空间 R3）

$$\mathcal{T} := \Sigma^3 = \{(y_1, y_2, y_3) : y_i \in \Sigma\}$$

约定：$y_1$ = 初爻 (bottom)，$y_2$ = 中爻，$y_3$ = 上爻 (top)。$|\mathcal{T}| = 8 = (\mathbb{Z}/2)^3$。

8 个 trigram 列为：

| symbol | tuple | sum $S$ | $D_1 = y_2-y_1$ | $D_2 = y_3-y_2$ | $\delta = y_3-y_1$ |
|---|---|---|---|---|---|
| 乾 | $(+,+,+)$ | $+3$ | $0$ | $0$ | $0$ |
| 坤 | $(-,-,-)$ | $-3$ | $0$ | $0$ | $0$ |
| 离 | $(+,-,+)$ | $+1$ | $-2$ | $+2$ | $0$ |
| 坎 | $(-,+,-)$ | $-1$ | $+2$ | $-2$ | $0$ |
| 巽 | $(-,+,+)$ | $+1$ | $+2$ | $0$ | $+2$ |
| 艮 | $(-,-,+)$ | $-1$ | $0$ | $+2$ | $+2$ |
| 兑 | $(+,+,-)$ | $+1$ | $0$ | $-2$ | $-2$ |
| 震 | $(+,-,-)$ | $-1$ | $-2$ | $0$ | $-2$ |

### Definition 1.3（核心算子）

| 名 | 符号 | 定义 | 类型 |
|---|---|---|---|
| sum (∫) | $S$ | $S(y) := y_1 + y_2 + y_3$ | $\mathcal{T} \to \mathbb{Z}$ |
| forward 1 | $D_1$ | $D_1(y) := y_2 - y_1$ | $\mathcal{T} \to \mathbb{Z}$ |
| forward 2 | $D_2$ | $D_2(y) := y_3 - y_2$ | $\mathcal{T} \to \mathbb{Z}$ |
| endpoint difference | $\delta$ | $\delta(y) := y_3 - y_1 = D_1(y) + D_2(y)$ | $\mathcal{T} \to \mathbb{Z}$ |
| second difference (curvature) | $D^2$ | $D^2(y) := y_3 - 2y_2 + y_1 = D_2(y) - D_1(y)$ | $\mathcal{T} \to \mathbb{Z}$ |

### Definition 1.4（V₄ 算子在 R3 上）

| 名 | 符号 | 定义 | 物理 anchoring |
|---|---|---|---|
| zong (反序) | $R$ | $R(y_1, y_2, y_3) := (y_3, y_2, y_1)$ | T (time-reversal) |
| cuo (全反) | $N$ | $N(y_1, y_2, y_3) := (-y_1, -y_2, -y_3)$ | P (parity) |
| 错综 (复合) | $RN$ | $RN(y) := R(N(y))$ | PT |
| identity | $e$ | $e(y) := y$ | 平凡变换 |

集合 $\{e, R, N, RN\}$ 在 composition 下构成 Klein four-group $V_4 = \mathbb{Z}/2 \times \mathbb{Z}/2$.

### Definition 1.5（六爻卦空间 R6）

$$\mathcal{H} := \mathcal{T} \times \mathcal{T} = \Sigma^6 = (\mathbb{Z}/2)^6$$

约定：$y_1..y_3$ 为内卦（下卦），$y_4..y_6$ 为外卦（上卦）。$|\mathcal{H}| = 64$。

cuo / zong / 错综 通过 6-yao 操作 lift 到 R6，仍构成 V₄。

### Definition 1.6（R7 cause-space = 卦 + 因）— **NEW**

R7 引入 **因 (yīn) axis** — 一个 binary feature 标记「过去印记」之有无：

$$\text{YinBit} := \{0, 1\} \cong \mathbb{Z}/2$$

R7 cell 空间：

$$\mathcal{R}_7 := \mathcal{H} \times \text{YinBit} = (\mathbb{Z}/2)^6 \times \mathbb{Z}/2 = (\mathbb{Z}/2)^7$$

$|\mathcal{R}_7| = 64 \times 2 = 128$。Lean 类型 = `Cell128`。

**因之解读**：
- 因 = 0：无过去印记（"无因"，未被 anything 烙刻）
- 因 = 1：有过去印记（"有因"，承继 prior state）

(命名 caveat：因 / 果是 provisional naming，参见附录候选 印 / 投 / 始 / 终 / 持 / 期。)

### Definition 1.7（R8 effect-space = 卦 + 因 + 果）— **NEW**

R8 引入 **果 (guǒ) axis** — 第二个 binary feature 标记「未来投影」之有无：

$$\text{GuoBit} := \{0, 1\} \cong \mathbb{Z}/2$$

R8 cell 空间：

$$\mathcal{R}_8 := \mathcal{R}_7 \times \text{GuoBit} = \mathcal{H} \times \text{YinBit} \times \text{GuoBit} = (\mathbb{Z}/2)^8$$

$|\mathcal{R}_8| = 128 \times 2 = 64 \times 4 = 256$。Lean 类型 = `Cell256`。

**果之解读**：
- 果 = 0：无未来投影（"无果"，不向 anything 延展）
- 果 = 1：有未来投影（"有果"，projects forward）

### Definition 1.8（Shi V₄ space = (因, 果) emergence at R8）— **NEW**

R8 上 (因, 果) ∈ Bool² 二维特征自然 induces 一个 V₄ Klein 四群结构。命名 4 个 (因, 果) 状态：

$$\mathcal{S} := \{道, 已, 今, 未\} \cong \{0,1\}^2 \cong V_4$$

| Shi state | (因, 果) | V₄ 元 | 解读 |
|---|---|---|---|
| **道** | (0, 0) | $e$ (identity) | 无因无果 — 跨时空，永真，V₄ 单位元 |
| **已** | (1, 0) | $\sigma_P$ | 有因无果 — 过去封闭，无未来投射 |
| **未** | (0, 1) | $\sigma_T$ | 无因有果 — 无过去印记，纯未来开放 |
| **今** | (1, 1) | $\sigma_{PT}$ | 因果俱在 — "现在"即流变交汇 (PT) |

则 (因, 果) : $\mathcal{S} \to \{0,1\}^2$ 是 bijective. **$\mathcal{S} \cong V_4 = (\mathbb{Z}/2)^2$**。

**关键观察**：Shi V₄ 不是 R7 或 R8 单层 atom，而是 **R7 因 axis + R8 果 axis 双层 emergent**。把 V₄ 当 R7 单层 atom 是层级压缩错误。

---

## 第二部分：基本命题（R3 上 V₄ 之 involutivity 与交换）

### Proposition 2.1（zong 是 involution）

$R \circ R = \text{id}_{\mathcal{T}}$。

**证明**：$(R \circ R)(y_1, y_2, y_3) = R(y_3, y_2, y_1) = (y_1, y_2, y_3)$. ∎

### Proposition 2.2（cuo 是 involution）

$N \circ N = \text{id}_{\mathcal{T}}$。

**证明**：$N(N(y)) = N(-y) = -(-y) = y$. ∎

### Proposition 2.3（cuo 与 zong 交换）

$N \circ R = R \circ N$。

**证明**：$(N \circ R)(y_1, y_2, y_3) = N(y_3, y_2, y_1) = (-y_3, -y_2, -y_1) = R(-y_1, -y_2, -y_3) = (R \circ N)(y_1, y_2, y_3)$. ∎

### Proposition 2.4（{R, N} 生成 Klein 四群）

$\{e, R, N, RN\}$ 在 composition 下 ≅ $V_4 = \mathbb{Z}/2 \times \mathbb{Z}/2$。

### Proposition 2.5（基本算子在 V₄ 下的变换）

| 算子 | $R$ 作用 | $N$ 作用 |
|---|---|---|
| $S$ | $S \circ R = S$ | $S \circ N = -S$ |
| $D_1$ | $D_1 \circ R = -D_2$ | $D_1 \circ N = -D_1$ |
| $D_2$ | $D_2 \circ R = -D_1$ | $D_2 \circ N = -D_2$ |
| $\delta$ | $\delta \circ R = -\delta$ | $\delta \circ N = -\delta$ |
| $D^2$ | $D^2 \circ R = D^2$ | $D^2 \circ N = -D^2$ |

**关键观察**：$\delta$ 在 $R$ 和 $N$ 下都反号——$|\delta|$ 是 $V_4$-invariant，$\text{sign}(\delta)$ 在 $V_4$ 下完整变化。

---

## 第三部分：主定理 A — 4+4 partition 强制性

### Theorem A（substrate–mark partition 强制性）

> Lean: see [`Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) (`ben_count = 4`, `zheng_count = 4`, `cuo_preserves_isZongFixed`).

定义：
$$\mathcal{T}_\text{本} := \text{Fix}(R) = \{y \in \mathcal{T} : R(y) = y\} = \{y : y_1 = y_3\}$$
$$\mathcal{T}_\text{征} := \mathcal{T} \setminus \mathcal{T}_\text{本}$$

则：

(a) $|\mathcal{T}_\text{本}| = 4$ 且 $|\mathcal{T}_\text{征}| = 4$。
(b) $N(\mathcal{T}_\text{本}) = \mathcal{T}_\text{本}$（cuo 保 substrate）。
(c) $N(\mathcal{T}_\text{征}) = \mathcal{T}_\text{征}$（cuo 保 mark）。
(d) $R$ 在 $\mathcal{T}_\text{征}$ 上无不动点，分成 2 个轨道：$\{震, 艮\}, \{巽, 兑\}$。

进一步，**$\mathcal{T}_\text{本}$ 与 $\mathcal{T}_\text{征}$ 是 $\mathcal{T}$ 在 $V_4 = \langle R, N\rangle$ 作用下唯一的 Z/2-equivariant partition（除 trivial）**。

**证明**：

(a) $y \in \mathcal{T}_\text{本} \iff y_1 = y_3$。自由变量为 $y_1, y_2$，$|\mathcal{T}_\text{本}| = 4$。
(b)(c) 若 $y_1 = y_3$，则 $-y_1 = -y_3$；$N$ preserves palindrome。
(d) $R(震) = R(+,-,-) = (-,-,+) = 艮$，$R(巽) = R(-,+,+) = (+,+,-) = 兑$。

唯一性：$V_4$ 在 $\mathcal{T}$ 上 3 个 orbit：$\{乾, 坤\}, \{离, 坎\}, \{震, 艮, 巽, 兑\}$。合并前两个 = $\mathcal{T}_\text{本}$；第三个 = $\mathcal{T}_\text{征}$。**唯一的 Z/2-equivariant 分类是 4+4**. ∎

### Corollary A.1

substrate / mark 不是审美选择——是 zong $R$ 在 $\mathcal{T}$ 上的 fixed-point set 决定的代数事实。

---

## 第四部分：主定理 B — substrate = 定常波

### Theorem B（substrate = boundary-preserving）

> Lean: see [`Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) (substrate predicate + 4-element enumeration via `native_decide`).

$\mathcal{T}_\text{本} = \{y \in \mathcal{T} : \delta(y) = 0\}$。

| substrate | $S$ | $D^2$ | 波形语义 |
|---|---|---|---|
| 乾 | $+3$ | $0$ | constant max（持续高位）|
| 坤 | $-3$ | $0$ | constant min（持续低位）|
| 离 | $+1$ | $+4$ | concave-up（中凹波形）|
| 坎 | $-1$ | $-4$ | concave-down（中凸波形）|

**乾坤是 DC component（zero mode），离坎是 Nyquist mode（最高 frequency）** —— 离散三点 Fourier basis 的 4 个 stationary wave。

---

## 第五部分：主定理 C — mark = 4 phase quadrant

### Theorem C（mark = phase plane 4 quadrant）

> Lean: phase-plane formalization in [`Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) (4 zheng quadrants enumerated; informal phase semantics).

定义 phase coordinate $\phi : \mathcal{T} \to \mathbb{Z}^2$:
$$\phi(y) := (\delta(y), S(y))$$

| mark | $\phi$ 值 $(\delta, S)$ | quadrant | 振荡 phase |
|---|---|---|---|
| 巽 | $(+2, +1)$ | $Q_1$ 右上 | 上升中段 |
| 艮 | $(+2, -1)$ | $Q_4$ 右下 | 上升起步 |
| 兑 | $(-2, +1)$ | $Q_2$ 左上 | 下降末段 |
| 震 | $(-2, -1)$ | $Q_3$ 左下 | 下降起步 |

**这就是为什么 8 trigram = 谐振子 phase 编码的 minimum complete basis**。

---

## 第六部分：主定理 D — cuo–zong V₄ 代数

### Theorem D（V₄ 在 phase plane 上的 dihedral 群作用）

> Lean: V₄ algebraic structure in [`Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) + V₄-outer permutations (`zong`, `cuoZong`, `hu`) in [`Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean).

(a) $\phi \circ N = -\phi$（cuo = π 旋转）
(b) $\phi \circ R = (-\delta, +S)$（zong = $\delta$-axis 反射）
(c) $\phi \circ (NR) = (+\delta, -S)$（错综 = $S$-axis 反射）
(d) $V_4$ 在 phase plane 上恰是 $D_2$（dihedral group of square 的 4 个对称）

### Corollary D.3（与物理 P/T/PT 同构）

- $e$ = identity
- $N$ = π 旋转 = **P + T 同时**（中心反演）
- $R$ = $\delta$-axis 反射 = **T**（时间反演）
- $NR$ = $S$-axis 反射 = **P**（空间反演）

🔥 **易代数 V₄ 与 物理学 {1, P, T, PT} 同构**。

---

## 第七部分：主定理 E — 离散 Newton-Leibniz 对偶

### Theorem E（substrate–mark = ∫–d 划分）

> Lean: see [`Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) (`δ`-zero ↔ ben partition).

(a) $\mathcal{T}_\text{本} = \{y : \delta(y) = 0\}$（端点导数为 0 = boundary-preserving）
(b) $\mathcal{T}_\text{征} = \{y : \delta(y) \neq 0\}$（端点导数非 0 = boundary-changing）
(c) 在 $\mathcal{T}_\text{本}$ 上，$S$ 是 complete invariant（4 个值: $\pm 3, \pm 1$）
(d) 在 $\mathcal{T}_\text{征}$ 上，$(\delta, S)$ 是 complete invariant（4 个 phase quadrant 各 1 representative）

**substrate–mark 划分 = ∫–d 划分**：
- substrate（4 个）= **积分饱和** trigram（$\delta = 0$，无边界净流出）
- mark（4 个）= **导数主导** trigram（$\delta \neq 0$，有边界净流出）

---

## 第八部分：主定理 F — R6 的 4 quadrant partition

### Theorem F（六十四卦的 4-quadrant 强制分解）

> Lean: see [`Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) (`quadrant_partition_complete`, `zong_quadrant`).

$$\mathcal{H} = \mathcal{H}_{本本} \sqcup \mathcal{H}_{本征} \sqcup \mathcal{H}_{征本} \sqcup \mathcal{H}_{征征}$$

(a) $|\mathcal{H}_{XY}| = 4 \times 4 = 16$
(b) **cuo 保 quadrant**：$N_6(\mathcal{H}_{XY}) = \mathcal{H}_{XY}$
(c) **zong 跨换 mixed quadrant**：
  - $R_6(\mathcal{H}_{本本}) = \mathcal{H}_{本本}$（自闭）
  - $R_6(\mathcal{H}_{征征}) = \mathcal{H}_{征征}$（自闭）
  - $R_6(\mathcal{H}_{本征}) = \mathcal{H}_{征本}$（**跨换**）
  - $R_6(\mathcal{H}_{征本}) = \mathcal{H}_{本征}$

---

## 第九部分：主定理 G — 与连续 1D 标量场对应

### Theorem G（discrete-continuous correspondence）

> Lean: informal (no Lean form — connection to ℝ-valued continuous fields is meta-mathematical).

**8 trigram = 离散 1D scalar field 在 3 sample 下的 sign-pattern complete enumeration**：
- substrate = **boundary-preserving samples**（端点同号）
- mark = **boundary-changing samples**（端点异号 = 必有 zero crossing）
- zong = 时间反演
- cuo = 信号反号

8 个 = phase $\phi \in \{0, \pi/4, \pi/2, ...\}$ 在 sign 下的完全枚举。

---

## 第十部分：主定理 H — R7 = (Z/2)⁷ = 128 + 因 (yīn) axis

### Theorem H（R7 cause-space）

> Lean: see [`Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) (`Cell128 = Hexagram × YinBit`, `yin` toggle, 128-cell enumeration).

R7 在 R6 之上引入第 7 个 binary axis — **因 (yīn, past-trace bit)**：

$$\mathcal{R}_7 := \mathcal{H} \times \text{YinBit} \cong (\mathbb{Z}/2)^7$$

(a) **|$\mathcal{R}_7$| = 128 = 64 × 2**
(b) **$\mathcal{R}_7 \cong (\mathbb{Z}/2)^7$**：R7 是 7 维 binary cube 的全部 vertices
(c) R7 上的群作用：
  - $(\mathbb{Z}/2)^6$ 经 hex XOR 在 $\mathcal{H}$ 上 simply transitive（6 个 yao flips）
  - $\mathbb{Z}/2$ 在 YinBit 上 simply transitive（toggle 因）
  - 联合 $(\mathbb{Z}/2)^7$ 在 $\mathcal{R}_7$ 上 simply transitive
(d) **R7 子分类**：4 R6-quadrant × 16 hex/quadrant × 2 因-state = 128

**证明**：直接 cardinality + group product 论证。 ∎

### Corollary H.1（因之 ontological 解读）

「因」(yīn) 作为 R7 atomic axis：
- 因 = 0：cell 与「过去」无 causal 关联，"unmoored" / 无承继
- 因 = 1：cell 携带 past trace，受 prior state 影响

这是 self-describing system 中**「is this state caused/conditioned by something prior」之 binary 标记**——在物理 lightcone 语言中是「past lightcone 是否非空」之 indicator。

### Corollary H.2（因 axis 与 cuo/zong V₄ 之关系）

cuo (parity, P) 在 R3/R6 上是 yao-flip。在 R7 上, 因 axis 是 INDEPENDENT 第 7 个 bit 与 6 个 yao bits 正交。因此 R7 上的 V₄ 算子结构：
- $V_4^{(\text{hex})}$ = $\{e, R_6, N_6, R_6 N_6\}$ acts on hex side 不动 因
- $\mathbb{Z}/2^{(\text{yin})}$ = toggle 因 不动 hex
- 联合 → $V_4 \times \mathbb{Z}/2$ on R7

---

## 第十一部分：主定理 I — R8 = (Z/2)⁸ = 256 + 果 (guǒ) axis

### Theorem I（R8 effect-space = 真 (Z/2)ⁿ closure）

> Lean: see [`Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) (`Cell256 = Hexagram × Shi`, `tou` toggle, 256-cell algebra).

R8 在 R7 之上引入第 8 个 binary axis — **果 (guǒ, future-projection bit)**：

$$\mathcal{R}_8 := \mathcal{R}_7 \times \text{GuoBit} = \mathcal{H} \times \text{YinBit} \times \text{GuoBit} \cong (\mathbb{Z}/2)^8$$

(a) **|$\mathcal{R}_8$| = 256 = 128 × 2 = 64 × 4**
(b) **$\mathcal{R}_8 \cong (\mathbb{Z}/2)^8$**：R8 是 8 维 binary cube 的全部 vertices = 1 byte 状态空间
(c) R8 上的群作用：
  - $(\mathbb{Z}/2)^6$ on hex
  - $\mathbb{Z}/2$ on 因 + $\mathbb{Z}/2$ on 果 = $V_4$ on (因, 果) 复合
  - 联合 $(\mathbb{Z}/2)^8 = (\mathbb{Z}/2)^6 \times V_4$ 在 $\mathcal{R}_8$ 上 simply transitive
(d) **R8 子分类**：
  - 4 R6-quadrant × 16 hex/quadrant × 4 (因, 果) = 256
  - 或 16 Mian × 16 (4 quadrant × 4 (因, 果)) = 256

**证明**：(a)(b) cardinality. (c) hex XOR + 因 toggle + 果 toggle 各自 simply-transitive on respective factors. (d) 由 Theorem F + 因/果 product. ∎

### Corollary I.1（256 是 8-bit closure）

$2^8 = 256$ 在数学/物理/计算机中：
- 1 byte = 8 bits = $(\mathbb{Z}/2)^8$ vertex
- $2^3 \times 2^3 \times 2^1 \times 2^1$ = trigram × trigram × 因 × 果
- $(\mathbb{Z}/2)^8$ 是最小完备 8 维 binary self-similar group
- 与 ASCII 字符空间 cardinality 相同（任何离散写形系统的最小编码单位）

R8 = 256 = R-hierarchy 自相似至**自然 8-bit 终点**。

### Corollary I.2（果之 ontological 解读）

「果」(guǒ) 作为 R8 atomic axis：
- 果 = 0：cell 不向"未来"延展，"unprojected" / 无后续
- 果 = 1：cell 投射 future state，"产生效果"

physics lightcone 类比：「future lightcone 是否非空」之 indicator。

### Corollary I.3（旧 Cell192 是 R8 的特殊 quotient）

之前 Cell192 把 Shi 编为 Z/3 cyclic {已, 今, 未}。这等价于把 R8 限制到 (因, 果) ≠ (0, 0) 之三态——即去掉 道-cells (64 个)。Cell192 是 R8 的 partial image，丧失了 V₄ 单位元 anchor。

正确路径：R8 真闭合 = Cell256，全部 (因, 果) ∈ Bool²。Cell192 deprecated。

---

## 第十二部分：主定理 J — Shi V₄ emerges at R8 from (因, 果) tensor

### Theorem J（Shi V₄ 双层 emergent 结构）

> Lean: see [`Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) (`Shi.toYinGuo` bijection to `YinBit × GuoBit`) + [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) (Shi V₄ structure, parity/timeReversal/PT).

Shi $\mathcal{S} = \{道, 已, 今, 未\}$ **不是** R7 或 R8 单层 atom，而是 R7 (因 axis) 与 R8 (果 axis) 双 axis 之 emergent 4-state 同构 V₄：

$$\mathcal{S} \cong \text{YinBit} \times \text{GuoBit} \cong V_4 = \mathbb{Z}/2 \times \mathbb{Z}/2$$

| Shi state | (因, 果) | V₄ 元素 | 物理 anchoring |
|---|---|---|---|
| **道** | $(0, 0)$ | $e$ (identity) | 永真 / 跨时空 / 无作用算子 |
| **已** | $(1, 0)$ | $\sigma_P$ | 已封闭过去（parity-like）|
| **未** | $(0, 1)$ | $\sigma_T$ | 未来开放（time-reversal-like）|
| **今** | $(1, 1)$ | $\sigma_{PT}$ | 过去与未来交汇（PT 复合点）|

(a) **道 = $V_4$ 单位元**：是唯一 (因=0, 果=0) 状态——与 timeline orthogonal。
(b) **已 = (因, ¬果)**：携带过去 cause 但无未来 effect projection — 过去封闭。
(c) **未 = (¬因, 果)**：无过去 cause 但投射 future effect — 未来开放（"虚拟"，因果链 origin）。
(d) **今 = (因, 果)**：因果同在 — "现在"作为 causation flow 的当前点。
(e) **V₄ 在 $\mathcal{S}$ 上 simply transitive**：4 个群元给 4 个不同 Shi 状态。

**证明**：(因, 果) bijection $\mathcal{S} \to \{0,1\}^2$ + $\{0,1\}^2$ 之 V₄ 群结构. ∎

### Corollary J.1（道作为永真状态的 algebraic 必然性）

V₄ Klein 群必有 identity. 在 (因, 果) coordinate 下, 道 = (0, 0) 是 V₄ 单位元——**既无过去 cause 也无 future effect 投射**。这意味着道是「与 causation flow orthogonal」之状态——**它跨尺度跨时空恒真**。

把道从 Shi 删除（如旧 Cell192 的 Z/3 cyclic 编码）：
- 丧失 V₄ 单位元
- 丧失「描述者本身之恒在 anchor」
- 破坏 R-hierarchy 之 (Z/2)ⁿ self-similarity

256 让道 first-class 进入本体，是「自描述」之形式落地。

### Corollary J.2（与 R3/R6 V₄ 之双重 V₄ 结构）

R8 上有**两层 V₄**：
- $V_4^{(\text{hex})}$ = $\{e, R_6, N_6, R_6 N_6\}$ on $\mathcal{H}$（cuo / zong / 错综 / id, 物理 P/T/PT 对应）
- $V_4^{(\text{shi})}$ = $\{道, 已, 今, 未\}$ ≅ (因, 果) Bool² on $\mathcal{S}$

二者**同构 V₄**, R8 上 tensor 起来即 $V_4 \times V_4 \cong (\mathbb{Z}/2)^4$，给出 R8 上 16 个对称变换。

### Corollary J.3（旧 R7=256 单层视角的修正）

之前文档把 R7 = (Z/2)⁶ × V₄ 当作 R7 单层（V₄ Shi 整体作 atomic axis）是层级压缩错误：
- 单层 atomic axis 必为 binary（(Z/2)¹ 一阶因子）
- V₄ = (Z/2)² 是 **2 个 binary axes 的 product**，自然分配到 R7 (因) + R8 (果) 两层
- (Z/2)ⁿ 自相似规律下每层 +1 bit；R6 → R7 +1 bit (因)；R7 → R8 +1 bit (果)

正确编码：**因 / 果 拆为 R7 / R8 两层 atoms**，Shi V₄ = R7 ⊗ R8 双 axis emergence。

---

## 第十三部分：主定理 K — R-hierarchy R1..R8 全 (Z/2)ⁿ closure

### Theorem K（自相似 (Z/2)ⁿ closure）

> Lean: see `R8_complete` in [`Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — bundles R₀..R₈ closure with cardinality theorems; depends only on `propext` + `native_decide` axes (no project axioms). Uniform Lift/Project pairs in [`Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean); R₅ Wuyao (Mian × Bool, 32) carrier in [`Foundation/Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean).

| 层 | 结构 | 元素数 | 当层新引入的"元" | V₄ 群作用 |
|---|---|---|---|---|
| R1 (爻) | $(\mathbb{Z}/2)^1$ | 2 | **爻** (yao) | $\mathbb{Z}/2$ |
| R2 (四象) | $(\mathbb{Z}/2)^2$ | 4 | 2 爻复合 | $V_4$ |
| R3 (八卦) | $(\mathbb{Z}/2)^3$ | 8 | 3 爻复合 + 本征划分 | $V_4$ on R3/zong |
| R6 (六十四卦) | $(\mathbb{Z}/2)^6$ | 64 | chong (6 爻 = 重卦) + 4 quadrant | $V_4 \times V_4$ |
| **R7** | **$(\mathbb{Z}/2)^7$** | **128** | **因 (yīn, past-trace bit)** | $V_4 \times \mathbb{Z}/2$ |
| **R8** | **$(\mathbb{Z}/2)^8$** | **256** | **果 (guǒ, future-projection bit)** | $V_4 \times V_4 \times V_4$ |

**所有 6 层均为 $(\mathbb{Z}/2)^n$ 群结构, 无任何非 (Z/2) 因子。R-hierarchy 严格自相似 (Z/2)ⁿ closure。**

### Corollary K.1（V₄ 是每层的对称 backbone）

V₄ Klein 四群在每个 R-layer (n ≥ 2) 都 acting：
- R2: 一个 V₄ on 四象
- R3: $V_4 = \{id, cuo, zong, 错综\}$ on trigram
- R6: $V_4$ on hexagram + $V_4$ on inner/outer quadrant ⇒ $V_4 \times V_4$
- R7: 上述 + $\mathbb{Z}/2$ on 因 axis
- R8: 上述 + $\mathbb{Z}/2$ on 果 axis ⇒ Shi V₄ + hex V₄ + quadrant V₄ = **triple-V₄ tensored**

V₄ 是「同一种代数结构在更高维度的重复」(yi-as-meta-framework § 4.2) 之精确形式。

### Corollary K.2（道 first-class 入本体）

R8 中道是 V₄ 单位元 **structurally first-class**, 不是哲学附加注解：
- $(h, 因=0, 果=0)$ 对每个 hexagram $h$ 给一个永真 anchor cell
- 共 64 个道-cells（每 hex 各有自己的「永真版本」）
- 在解释器层面, 道-cell = 「无 causation flow 约束下的 hex 真值」——数学/逻辑/形而上常驻态

**这是「道作为永恒真理」之 Lean 落地**。

### Corollary K.3（与 8-bit ASCII 之 cardinal 映射）

256 = ASCII 字符全集 = $(\mathbb{Z}/2)^8$。这不是巧合：

> 任何完整 self-describing system 在最小 binary closure 处，都收敛到 8-bit cardinality。
> R8 = 256 是「易」语言的 ASCII 等价 —— 256 个最小完备符号原子。

ASCII 是工程系统在 binary 上的 8-bit closure；R8 (Cell256) 是「易」在自描述系统上的 8-bit closure。底层同构。

### 主结论

**R8 = 256-Cell 是 R-hierarchy 的 self-similar (Z/2)ⁿ closure**，因 (R7) + 果 (R8) 双层引入完成 Shi V₄ 之 first-class 入本体。这是「自描述系统最小完备代数」从 R1 到 R8 的**完整刻画**——再无 Z/3 异类，再无层级压缩。

---

## 第十二部分：主定理 J — R-hierarchy 全 (Z/2)ⁿ 自相似 closure

### Theorem J（R1..R7 全 (Z/2)ⁿ）

| 层 | 结构 | 元素数 | V₄ 群作用 |
|---|---|---|---|
| R1 (爻) | $(\mathbb{Z}/2)^1$ | 2 | $\mathbb{Z}/2 = \{id, neg\}$ |
| R2 (四象) | $(\mathbb{Z}/2)^2$ | 4 | $V_4$ |
| R3 (八卦) | $(\mathbb{Z}/2)^3$ | 8 = 4本+4征 | $V_4$ on R3/zong |
| R6 (六十四卦) | $(\mathbb{Z}/2)^6$ | 64 = 4 quadrant × 16 | $V_4 \times V_4$ on quadrant + Mian |
| **R7 (256-Cell)** | $(\mathbb{Z}/2)^8$ | **256 = 64 × 4** | $V_4 \times V_4 \times V_4$（hex P/T + Shi 道/已/今/未）|

**所有 5 层均为 $(\mathbb{Z}/2)^n$ 群结构, 无任何非 (Z/2) 因子。R-hierarchy 严格自相似 (Z/2)ⁿ closure。**

### Corollary J.1（V₄ 是每层的对称 backbone）

V₄ Klein 四群在每个 R-layer (n ≥ 2) 都 acting：
- R2: 一个 V₄ on 四象
- R3: $V_4 = \{id, cuo, zong, 错综\}$ on trigram
- R6: $V_4$ on hexagram + $V_4$ on inner/outer quadrant ⇒ $V_4 \times V_4$
- R7: $V_4$ on hexagram + $V_4 \times V_4$ on quadrant + $V_4$ on Shi ⇒ **double-V₄ tensored**

V₄ 是「同一种代数结构在更高维度的重复」(yi-as-meta-framework § 4.2) 的精确形式。

### Corollary J.2（道 first-class 入本体）

R7 中道是 V₄ 单位元 first-class **structurally**, 不是哲学上的附加注解：
- $(道, h) \in \mathcal{C}$ 对每个 hexagram $h \in \mathcal{H}$ 给出一个永真 anchor cell
- 共 64 个道-cell（每个 hexagram 都有自己的「永真版本」）
- 在解释器层面, $(道, h)$ 是「无时态约束下的 hexagram 真值」——数学/逻辑/形而上常驻态

**这正是「道作为永恒真理」之 Lean 落地**。

### Corollary J.3（与 8-bit ASCII 的 cardinal 映射）

256 = ASCII 字符全集大小 = $(\mathbb{Z}/2)^8$。这不是巧合：

> 任何完整 self-describing system 在最小 binary closure 处，都收敛到 8-bit cardinality。
> Cell256 是「易」语言的 ASCII 等价 —— 256 个最小完备符号原子。

ASCII 是工程系统在 binary 上的 8-bit closure；Cell256 是「易」在自描述系统上的 8-bit closure。底层同构。

### 主结论

**R7 = 256-Cell 是 R-hierarchy 的 self-similar (Z/2)ⁿ closure**，道作为 V₄ 单位元 first-class 入本体。这是「自描述系统最小完备代数」从 R1 到 R7 的**完整刻画**——再无 Z/3 异类。

---

## 第十四部分：哲学解读

### 14.1 易不是物理 GUT，而是 self-description GUT

定理 A–K 的整体表明：易的「物動間事 + 幾勢機時 + 道已今未」三层分类**等价于离散 self-describing system 在 (Z/2)⁸ 自相似空间下的 phase-space exhaustion**。

任何**完整描述系统**必须 implicitly 编码：
- 边界 vs 内部（→ substrate vs mark, 4+4 partition）
- 时间反演性质（→ zong, T）
- 信号反演性质（→ cuo, P）
- 端点导数 vs 累积积分（→ δ vs S, ∫–d）
- **过去印记之有无（→ R7 因 axis）** ← R7 新增
- **未来投影之有无（→ R8 果 axis）** ← R8 新增
- **永真 anchor（→ 道 = (因, 果) = (0, 0) = V₄ 单位元）** ← R7⊗R8 emergence

R8 = 256 是这套结构的**最小完备表达**——不能再压缩，不能拆分。

### 14.2 为什么"看起来在任何情形下都是真"

因为它编码的是**任何 self-describing system 的 minimum kernel**——而不是某个 specific domain 的内容。它在 type theory / process algebra / signal processing / harmonic oscillator / Fourier analysis / 时态逻辑 都"出现"，是因为这些 domain 都需要这个 kernel 才能完整。不是 occasional 巧合，是**系统化必然性**。

### 14.3 道之 ontological 必然性

「道」作为永真 anchor 不是哲学修辞，而是 V₄ 群结构（在 R7⊗R8 之 (因, 果) tensor 上）之**代数必然**：
- V₄ Klein 群必有 identity
- Shi = V₄ 上的 identity = (因=0, 果=0) = 「无 causation flow 约束」状态
- 无 causation flow 约束 = 跨时空恒真

把道从 Shi 删除（如 Z/3-Cell192），不仅丧失 V₄ 结构，也丧失了 self-describing system 中那个**「描述者本身」之恒在 anchor**——破坏了易作为"自描述 GUT"的完整性。

R8 = 256 让道**first-class 进入本体**，正是「自描述」的形式落地。

### 14.4 它的真名

正式名称：**Discrete First-Order (Z/2)⁸ Self-Describing Phase-Space Algebra** 或 **DFOSPSA-256**。

更哲学化：**易 = 任何 self-describing system 在 8-bit minimum binary closure 下的 phase-space algebra，加上一个 V₄-identity-as-道 的 ontological anchor (在 R7 因 axis ⊗ R8 果 axis 双层 emerge)**。

---

## 第十五部分：Lean 形式化路径

### 15.1 已完成（R0–R8 全 (Z/2)ⁿ closure，2026-05-10）

| 模块 | 文件 | 关键定理 / 元素 | 状态 |
|---|---|---|---|
| R0 (太极) | (Lean stdlib `Unit`) | implicit | ✓ |
| R1 (爻) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) | `Yao.neg_neg` | ✓ |
| R2/R3 (四象/八卦) + V₄ | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | `cuo_eq_compose` (P=DHB), `bagua_intercommunication` | ✓ |
| R3 substrate–mark partition | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | `ben_count = 4`, `zheng_count = 4`, `cuo_preserves_isZongFixed` | ✓ |
| R4 Mian (16) | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | `Mian = Ben × Zheng`, `Mian.all.length = 16` | ✓ |
| R5 Wuyao (32) | [`Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | `Wuyao = Mian × Bool`, `flip5` involution, lift/project | ✓ |
| R6 (Hexagram) + quadrant | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean), [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | `quadrant_partition_complete`, `zong_quadrant` | ✓ |
| R7 Cell128 + 因 | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | `Cell128 = Hexagram × YinBit`, `yin` toggle | ✓ |
| R8 Cell256 + 果 + Shi V₄ | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean), [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | `Shi.toYinGuo` bijection, `R8_complete` bundle | ✓ |
| Atomic / V₄-outer ops | [`Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean), [`Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | XOR-subgroup re-export + zong/hu/cuoZong | ✓ |
| Uniform Lift / Project | [`Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | 8 R-layer pairs + `proj_lift_id_Rn` retract lemmas | ✓ |
| OX 8-char literal macro | [`Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) | `OX["xxxxxxxx"]` → Cell256 | ✓ |
| Self-description witness | [`Truth/SelfDescription.lean`](../../formal/SSBX/Truth/SelfDescription.lean) | `Cell256OperatorComplete` | ✓ |
| R3 phase plane + V₄ 同构 | 待落 (Theorem C/D 严格形式化) | `phase_eq`, `V₄_acts_on_phase` | TODO |

### 15.2 R7/R8 落地（refactor done — 2026-05-10）

> 状态更新：原计划之 refactor 已完成；新增 [`Foundation/Hierarchy/`](../../formal/SSBX/Foundation/Hierarchy/) 子目录 (R5_Wuyao + LiftProject + Operators/Atomic + Operators/V4Outer) + [`Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) (`OX["xxxxxxxx"]` 8-char macro). `lake build SSBX` 干净通过 (3648 jobs, 0 sorry, 仅 propext + native_decide 公理). 以下 sketch 保留作历史 anchor.

旧主线 [Cell192.lean](../../formal/SSBX/Foundation/Bagua/Cell192.lean) + [Cell192Stratify.lean](../../formal/SSBX/Foundation/Bagua/Cell192Stratify.lean) 把 Shi 编码为 Z/3 cyclic 是层级压缩错误。**新主线**（R7/R8 拆层）：

- **`Cell128.lean`**（新建，R7 中间层）：
  ```lean
  /-- R7 atom: 因 (yīn) — past-trace bit. Provisional naming — see yi-calculus-theorem.md
      §16 附录 for alternatives 印/投, 始/终, 持/期. -/
  abbrev YinBit := Bool

  /-- R7 (128-Cell) = R6 × 因 = Hexagram × Bool. -/
  abbrev Cell128 : Type := Hexagram × YinBit
  -- |Cell128| = 64 × 2 = 128 = (Z/2)⁷
  ```

- **`Cell256.lean`**（替代 Cell192.lean，R8 闭合层）：
  ```lean
  /-- R8 atom: 果 (guǒ) — future-projection bit. Provisional naming. -/
  abbrev GuoBit := Bool

  /-- R8 (256-Cell) = R7 × 果 = Hexagram × YinBit × GuoBit. -/
  abbrev Cell256 : Type := Cell128 × GuoBit  -- = Hexagram × YinBit × GuoBit
  -- |Cell256| = 128 × 2 = 256 = (Z/2)⁸

  -- Phase C (2026-05-11, commit 90c34f0): Shi 改为 abbrev Bool × Bool
  /-- Shi V₄ ≅ (因, 果) ∈ Bool² 直接展开 (Phase C 后 abbrev for Bool × Bool). -/
  abbrev Shi : Type := YinBit × GuoBit
  @[match_pattern] def Shi.dao : Shi := (false, false)  -- V₄ identity = 道
  @[match_pattern] def Shi.ji  : Shi := (true,  false)  -- P (past closed)
  @[match_pattern] def Shi.jin : Shi := (true,  true)   -- PT (present)
  @[match_pattern] def Shi.wei : Shi := (false, true)   -- T (future open)
  -- toYinGuo / ofYinGuo 现在 collapse to id (no bijection layer needed)
  ```

- **`Cell256Stratify.lean`**（重写）:
  - R-hierarchy R1..R8 explicit
  - V₄ 算子 on Shi (cuo/zong/cuoZong 等价于 (因, 果) XOR)
  - parity / timeReversal / yComb 物理 anchoring
  - $R_5$_card_eq_128 + R8_card_eq_256 双基数定理
  - $(\mathbb{Z}/2)^8 = (\mathbb{Z}/2)^6 \times \mathbb{Z}/2 \times \mathbb{Z}/2$ simply-transitive 群作用
  - 树 R6Tree = Sheng 6 × YinBit × GuoBit ≃ R8
  - xuGua 扩展：xuGua256 (Hex-major × Shi-minor with 4-fold)
  - **R8_complete bundle theorem** (替代之前 R7_complete)

- **命名注释**：所有 因/果 使用处加 inline comment：
  ```
  -- R7/R8 atomic axes 因 (yīn) / 果 (guǒ) — provisional naming.
  -- See yi-calculus-theorem.md §16 for alternatives 印/投, 始/终, 持/期.
  ```

- **下游影响**（refactor scope）:
  - BaguaTuring.lean: YiInstr.setShi 增加 Shi.dao
  - DaoSource.lean: 道源程在 Shi=道 状态下的语义需 review
  - GodelLi.lean: Halts 谓词 + Rice 不变
  - MetaInterp/*: Shi case-split 从 3 例升 4 例
  - OperatorCellMap.lean: 192 → 256
  - 表六_192格全表.md → 表六_256格全表.md（升级 64 × 4 表 + 因/果 标注）

预计 refactor scope: ~1500 LOC 重写 + ~20 文件 case-split 增补，0 新 axiom，保持 0 sorry。

---

## 第十六部分：总结 + 命名附录

R-hierarchy R1..R8 是离散 self-describing system 的 (Z/2)ⁿ 自相似最小完备代数核：

```
R1 (爻)        = (Z/2)¹      = 2          基本二值原子
R2 (四象)       = (Z/2)²      = 4 = V₄    
R3 (八卦)       = (Z/2)³      = 8 = 4本 + 4征   substrate–mark
R6 (六十四卦)    = (Z/2)⁶      = 64 = 4 quadrant × 16   palindrome-quadrant + Mian
R7             = (Z/2)⁷      = 128 = 64 × 2     卦 + 因 (yīn, past-trace bit)
R8 (256-Cell)  = (Z/2)⁸      = 256 = 128 × 2 = 64 × 4   卦 + 因 + 果 (guǒ, future-projection)
```

V₄ Klein 群在每层 acting (cuo/zong/错综/id), 物理 anchoring P/T/PT。Shi V₄ = {道, 已, 今, 未} = (因, 果) tensor at R8, **不是单层 atom**。**道 = (0, 0) = V₄ 单位元 = 永真 anchor, 跨尺度跨时空, first-class 入本体**。

256 = $(\mathbb{Z}/2)^8$ = R-hierarchy 的 self-similar closure, 与 ASCII 8-bit cardinality 同构 —— 任何 self-describing system 在 binary 上的最小完备 closure。

**易 = 自描述系统的 (Z/2)⁸ phase-space algebra + 道的 V₄-identity ontological anchor 在 R7⊗R8 (因, 果) tensor 上 emerge。**

### 16.1 命名附录：因/果 是 provisional

R7 元 = 因 / R8 元 = 果 的命名是 working choice，等 Lean 落 R7/R8 + Theorems H–K 完整后回看是否改。四轴评估：

| 候选 | 哲学 | 形式科学 | 古文 | 项目耦合 | 评分 |
|---|---|---|---|---|---|
| **因 / 果**（当前选） | 佛教 hetu-phala + Pearl 因果 + Aristotle 4 因 | causal DAG / lightcones | 《说文》"因，依也"/"果，木实也"；佛教汉译 | 不冲突；"因"/"已" 听觉撞 | ★★★★ |
| **印 / 投** | Husserl retention/protention; Heidegger Geworfenheit/Entwurf; Sartre projection | signal frame buffer / predictive filter; geometry stamp/cast | 《说文》"印，执政所持信"/"投，擿也" | XinZhi.lean 三相 retention/primalImpression/protention 直对接 | ★★★★ |
| **始 / 终** | Aristotle arche/telos; 道家终始反复 | graph source/sink; coalgebra initial/terminal | **《易传·系辞下》「原始要终, 以为质也」原文（Yi-native!）** | 与 Yi 原生表述对齐 | ★★★ |
| **持 / 期** | 现象学 retention/protention 标准汉译 | 期 = E[X] expected value | 持守/期限/期待，《诗经》《左传》 | 概率/统计 anchor | ★★ |

**因 / 果 暂选**：哲学最深（佛教千年传统 + 现代 Pearl）+ 形式科学 anchor (causal DAG)；
**最强 Yi-native 替代 = 始 / 终**（系辞原文）；
**最强项目耦合替代 = 印 / 投**（XinZhi.lean 三相直对接）。

回看时机：Cell128.lean / Cell256.lean 落码 + Theorems H–K 形式化稳定后。

---

## 附录：与现有文件的关系

| 文件 | 关系 |
|---|---|
| [yi-as-meta-framework.md](yi-as-meta-framework.md) § 4.1 | R-hierarchy 哲学层；R7 = 128 (因) + R8 = 256 (果) 拆层版 |
| [64-hexagram-grid.md](64-hexagram-grid.md) | Theorem F 的 64 卦 instantiation（不变）|
| [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) | 4 substrate 在内容线 12-grid 中的展开（不变）|
| [layer-axis-graph.md](layer-axis-graph.md) | 三轴并存图（不变）|
| [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) | Yao/Trigram/Hexagram + cuo/zong (不变) |
| [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | (Z/2)³ + V₄ on R3/R6 (不变) |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | 4 本 + 4 征 + 4 quadrant + Mian (不变) |
| [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) | **deprecated** —— 已重命名为 Cell256.lean |
| `Cell128.lean` (待建) | Theorem H — R7 = 128 + 因 (yīn, past-trace bit) |
| `Cell256.lean` (重写) | Theorem I — R8 = 256 + 果 (guǒ, future-projection bit) + Shi V₄ (因×果 derived) |
| `Cell256Stratify.lean` (重写) | Theorem J + K — Shi V₄ emergence + R-hierarchy closure |
| `XinZhi.lean` | 现象学三相 retention/primalImpression/protention — 与 印 / 投 命名候选直对接 |
| 表六_192格全表.md | **deprecated** —— 升级为 表六_256格全表.md (64 × 4 + 因/果 标注) |
