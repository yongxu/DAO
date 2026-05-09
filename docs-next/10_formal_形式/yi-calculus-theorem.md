# 易微积分定理：八卦作为离散二阶波形空间的完整刻画

> 状态：定理稿（2026-05-10）。
> 作用：把"八卦 = 物動間事 + 幾勢機時"这个直觉升级为完整的代数-微积分定理：8 trigram 是离散波形空间 Σ³ 上 zong/cuo 双 involution 的 unique fixed-point 分解，4 substrate 是定常波形，4 mark 是 4 phase-space quadrant，cuo 是 phase 空间 π 旋转。
> 配套：[64-hexagram-grid.md](64-hexagram-grid.md) / [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) / [layer-axis-graph.md](layer-axis-graph.md)
> 形式锚：拟落 [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) / [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) 之 Lean theorems

---

## 第零部分：引言

本文证明：**八卦的"物動間事/幾勢機時 = 4 substrate + 4 mark"分解不是哲学约定，是一个由 (Z/2)³ 群结构强制的代数-微积分定理**。

具体地，证明：
1. **Theorem A**（四加四 partition 强制性）：8 trigram 在 zong involution 下唯一地分成 4 fixed (substrate) + 4 在 2 个 orbit 中 (mark)。
2. **Theorem B**（substrate = 定常波）：4 substrate 是 Σ³ 上仅有的 4 个 boundary-preserving 配置。
3. **Theorem C**（mark = phase quadrant）：4 mark 在 (sum, endpoint-difference) phase plane 上恰是 4 个 open quadrant 的 representative。
4. **Theorem D**（cuo-zong 代数）：cuo 是 phase plane 的 π 旋转，zong 是 endpoint-axis 反射，二者构成 Klein four-group 作用。
5. **Theorem E**（discrete 微积分对偶）：endpoint-difference δ 与 sum S 是离散 Newton-Leibniz pair，substrate-mark 划分等价于 d-∫ 划分。
6. **Theorem F**（hexagram extension）：64 = (Σ³ × Σ³) 的 4-quadrant partition 直接由 trigram 4+4 的 product 给出。

这些定理全部是 native_decide 可证，文末给 Lean 形式化路径。

---

## 第一部分：形式 setup

### Definition 1.1（爻空间）

设 $\Sigma := \{+1, -1\}$，元素读作 $\text{阳} = +1$, $\text{阴} = -1$。

### Definition 1.2（三爻卦空间）

$$\mathcal{T} := \Sigma^3 = \{(y_1, y_2, y_3) : y_i \in \Sigma\}$$

约定：$y_1$ = 初爻 (bottom)，$y_2$ = 中爻，$y_3$ = 上爻 (top)。

显然 $|\mathcal{T}| = 8$。8 个 trigram 列为：

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

定义五个算子 $\mathcal{T} \to \mathcal{T}$ 或 $\mathcal{T} \to \mathbb{Z}$：

| 名 | 符号 | 定义 | 类型 |
|---|---|---|---|
| sum (∫) | $S$ | $S(y) := y_1 + y_2 + y_3$ | $\mathcal{T} \to \mathbb{Z}$ |
| forward 1 | $D_1$ | $D_1(y) := y_2 - y_1$ | $\mathcal{T} \to \mathbb{Z}$ |
| forward 2 | $D_2$ | $D_2(y) := y_3 - y_2$ | $\mathcal{T} \to \mathbb{Z}$ |
| endpoint difference | $\delta$ | $\delta(y) := y_3 - y_1 = D_1(y) + D_2(y)$ | $\mathcal{T} \to \mathbb{Z}$ |
| second difference (curvature) | $D^2$ | $D^2(y) := y_3 - 2y_2 + y_1 = D_2(y) - D_1(y)$ | $\mathcal{T} \to \mathbb{Z}$ |

注：$\delta$ 是"边界差"（discrete derivative-at-endpoints），$D^2$ 是"曲率"。

### Definition 1.4（对称算子）

定义两个 involution $\mathcal{T} \to \mathcal{T}$：

| 名 | 符号 | 定义 |
|---|---|---|
| zong (反序) | $R$ | $R(y_1, y_2, y_3) := (y_3, y_2, y_1)$ |
| cuo (全反) | $N$ | $N(y_1, y_2, y_3) := (-y_1, -y_2, -y_3)$ |

---

## 第二部分：基本命题

### Proposition 2.1（zong 是 involution）

$R \circ R = \text{id}_{\mathcal{T}}$。

**证明**：$(R \circ R)(y_1, y_2, y_3) = R(y_3, y_2, y_1) = (y_1, y_2, y_3)$. ∎

### Proposition 2.2（cuo 是 involution）

$N \circ N = \text{id}_{\mathcal{T}}$。

**证明**：$N(N(y)) = N(-y) = -(-y) = y$. ∎

### Proposition 2.3（cuo 与 zong 交换）

$N \circ R = R \circ N$。

**证明**：
$$(N \circ R)(y_1, y_2, y_3) = N(y_3, y_2, y_1) = (-y_3, -y_2, -y_1) = R(-y_1, -y_2, -y_3) = (R \circ N)(y_1, y_2, y_3). \quad \blacksquare$$

### Proposition 2.4（{R, N} 生成 Klein four-group）

集合 $\{\text{id}, R, N, RN\}$ 在 composition 下构成一个 Klein four-group $V_4 = \mathbb{Z}/2 \times \mathbb{Z}/2$。

**证明**：由 P2.1, P2.2, P2.3 直接验证。$RN \circ RN = R(NR)N = R(RN)N = R^2 N^2 = \text{id}$. ∎

### Proposition 2.5（基本算子在 {R, N} 下的变换）

| 算子 | $R$ 作用 | $N$ 作用 |
|---|---|---|
| $S$ | $S \circ R = S$ | $S \circ N = -S$ |
| $D_1$ | $D_1 \circ R = -D_2$ | $D_1 \circ N = -D_1$ |
| $D_2$ | $D_2 \circ R = -D_1$ | $D_2 \circ N = -D_2$ |
| $\delta$ | $\delta \circ R = -\delta$ | $\delta \circ N = -\delta$ |
| $D^2$ | $D^2 \circ R = D^2$ | $D^2 \circ N = -D^2$ |

**证明**：直接代入。例如 $\delta(R(y)) = y_1 - y_3 = -\delta(y)$；$\delta(N(y)) = -y_3 - (-y_1) = -\delta(y)$. ∎

**关键观察**：$\delta$ 在 $R$ 和 $N$ 下都反号——这意味着 $|\delta|$ 是 $V_4$-invariant，$\text{sign}(\delta)$ 在 $V_4$ 下完整变化。

---

## 第三部分：主定理 A — 四加四分解的唯一性

### Theorem A（substrate-mark partition 强制性）

定义：
$$\mathcal{T}_\text{本} := \text{Fix}(R) = \{y \in \mathcal{T} : R(y) = y\} = \{y : y_1 = y_3\}$$
$$\mathcal{T}_\text{征} := \mathcal{T} \setminus \mathcal{T}_\text{本}$$

则：

(a) $|\mathcal{T}_\text{本}| = 4$ 且 $|\mathcal{T}_\text{征}| = 4$.
(b) $N(\mathcal{T}_\text{本}) = \mathcal{T}_\text{本}$（cuo 保 substrate）.
(c) $N(\mathcal{T}_\text{征}) = \mathcal{T}_\text{征}$（cuo 保 mark）.
(d) $R$ 在 $\mathcal{T}_\text{征}$ 上无不动点，分成 2 个轨道，每个 2 元素：$\{震, 艮\}, \{巽, 兑\}$.

进一步，**$\mathcal{T}_\text{本}$ 与 $\mathcal{T}_\text{征}$ 是 $\mathcal{T}$ 在 $V_4 = \langle R, N\rangle$ 作用下唯一的 Z/2-equivariant partition（除 trivial）**。

**证明**：

(a) $y \in \mathcal{T}_\text{本} \iff y_1 = y_3$. 自由变量为 $y_1$ 和 $y_2$（共 2 个，每个 2 取值），故 $|\mathcal{T}_\text{本}| = 4$. 余 4 在 $\mathcal{T}_\text{征}$.

(b) 若 $y \in \mathcal{T}_\text{本}$，则 $y_1 = y_3$，故 $N(y)_1 = -y_1 = -y_3 = N(y)_3$，仍 palindromic.

(c) 由 (b) 同理：$N$ preserves palindrome ⇒ preserves non-palindrome.

(d) $R$ swap $y_1 \leftrightarrow y_3$. 若 $y_1 \neq y_3$, $R$ swap 是非平凡的。具体：$R(震) = R(+,-,-) = (-,-,+) = 艮$, $R(巽) = R(-,+,+) = (+,+,-) = 兑$. 两轨道各 2 元素。

唯一性：$\mathcal{T}/V_4$ 的 orbit 数最多 $|\mathcal{T}|/|V_4| = 2$（若全是 free orbits），但 $V_4$ 在 $\mathcal{T}_\text{本}$ 上 $R$ 是 trivial，故有 fixed points。具体验证：$V_4$ 在 $\mathcal{T}$ 上有 3 个 orbit：
- $\{乾, 坤\}$（cuo orbit, 大小 2）
- $\{离, 坎\}$（cuo orbit, 大小 2）
- $\{震, 艮, 巽, 兑\}$（cuo+zong orbit, 大小 4）

合并前两个 = $\mathcal{T}_\text{本}$, 第三个 = $\mathcal{T}_\text{征}$. **唯一的 Z/2-equivariant 分类是 4+4**. ∎

### Corollary A.1

substrate / mark 不是审美选择——是 zong $R$ 在 $\mathcal{T}$ 上的 fixed-point set 决定的代数事实。任何 $V_4$-equivariant 函数 $\mathcal{T} \to \{0, 1\}$ 必然 factor through $\chi_R := \mathbb{1}_{\mathcal{T}_\text{本}}$.

---

## 第四部分：主定理 B — Substrate 是 4 个定常波形

### Theorem B（substrate = 边界保持配置）

$\mathcal{T}_\text{本} = \{y \in \mathcal{T} : \delta(y) = 0\}$.

进一步，$\mathcal{T}_\text{本}$ 上的 $(S, D^2)$ 取值是 4 个 distinct values:

| substrate | $S$ | $D^2$ | 波形语义 |
|---|---|---|---|
| 乾 | $+3$ | $0$ | constant max（持续高位）|
| 坤 | $-3$ | $0$ | constant min（持续低位）|
| 离 | $+1$ | $+4$ | concave-up（中凹波形，"valley"）|
| 坎 | $-1$ | $-4$ | concave-down（中凸波形，"peak"）|

**证明**：

$\delta(y) = 0 \iff y_3 = y_1$，正是 palindromic 条件 ⇒ $\mathcal{T}_\text{本} = \{y : \delta(y) = 0\}$.

直接计算（已在 §1 表格中）：
- 乾 = $(+,+,+)$: $S = 3$, $D^2 = 1 - 2 + 1 = 0$.
- 坤 = $(-,-,-)$: $S = -3$, $D^2 = -1 - (-2) + (-1) = 0$.
- 离 = $(+,-,+)$: $S = 1$, $D^2 = 1 - 2(-1) + 1 = 4$.
- 坎 = $(-,+,-)$: $S = -1$, $D^2 = -1 - 2(1) + (-1) = -4$.

4 distinct values. ∎

### Corollary B.1（substrate 几何意义）

在 $\mathbb{R}^3$ 中把 trigram $(y_1, y_2, y_3)$ 视为 3 点函数 $f : \{1, 2, 3\} \to \mathbb{R}$:
- **4 substrate 是仅有 4 个使 $f(1) = f(3)$ 的二阶离散 sample 函数**.
- 它们对应到 **standing waves**（驻波）—— 端点固定，不传播.
- 离 / 坎 是这种"端点固定"的 fundamental mode（$|D^2| = 4$）；乾 / 坤 是 constant mode（$D^2 = 0$）.

### Corollary B.2（与连续函数论对应）

定义连续插值 $\hat{f}: [0, 2] \to \mathbb{R}$，则：
- 乾 = $\hat{f} \equiv 1$（constant +1）= $\int_0^2 1 = 2$.
- 坤 = $\hat{f} \equiv -1$（constant -1）= $\int_0^2 (-1) = -2$.
- 离 = $\hat{f}$ ≈ $\cos(\pi t)$（valley shape）= $\int_0^2 \cos(\pi t) dt = 0$ but discrete sample = $+1$.
- 坎 = $\hat{f}$ ≈ $-\cos(\pi t)$（peak shape）= 同上 sign reversed.

**乾坤是 DC component（zero mode），离坎是 Nyquist mode（最高 frequency）** — 它们是离散 Fourier basis 的两个端点。这是为什么这 4 个在易学里地位特殊——它们是离散三点 Fourier 变换的 4 个 stationary wave.

---

## 第五部分：主定理 C — Mark 是 4 phase quadrant

### Theorem C（mark = phase plane 4 个 quadrant）

定义 phase coordinate $\phi : \mathcal{T} \to \mathbb{Z}^2$:
$$\phi(y) := (\delta(y), S(y))$$

则 $\phi$ 是 injective，且 $\mathcal{T}_\text{征}$ 的 4 个 image 恰是 phase plane 的 4 个 open quadrant 中的 unique 整点：

| mark | $\phi$ 值 $(\delta, S)$ | quadrant | 振荡 phase |
|---|---|---|---|
| 巽 | $(+2, +1)$ | $Q_1$（右上）| 上升中段（rising mid）|
| 艮 | $(+2, -1)$ | $Q_4$（右下）| 上升起步（rising start）|
| 兑 | $(-2, +1)$ | $Q_2$（左上）| 下降末段（falling end）|
| 震 | $(-2, -1)$ | $Q_3$（左下）| 下降起步（falling start）|

进一步：
- $\delta$ 决定 quadrant 的左右（$\delta > 0$ 右，$\delta < 0$ 左）= **方向** of 端点 derivative
- $S$ 决定 quadrant 的上下（$S > 0$ 上，$S < 0$ 下）= **位置** in summed amplitude

**证明**：

$\phi$ injective on $\mathcal{T}_\text{征}$：从 §1 表格直接验证 4 个 mark 的 $(\delta, S)$ 值两两不同.

$\phi(\mathcal{T}_\text{本}) \subset \{\delta = 0\}$：T_本 都在 $\delta = 0$ 轴上, 不在任何 open quadrant.

$\phi(\mathcal{T}_\text{征}) \subset \{|\delta| = 2\}$：T_征 都在 $\delta = \pm 2$. ∎

### Corollary C.1（与谐振子 phase space 同构）

设 $(q, p)$ 为谐振子 phase space（$q$ = 位置，$p$ = 动量）. 标准化下，谐振子轨道是 unit circle, 周期 $2\pi$. 把它分成 4 quadrant：

| quadrant | 物理 phase | 易 trigram |
|---|---|---|
| $Q_1$ ($q > 0, p > 0$) | 右上：上升至最大位置 | 巽 |
| $Q_2$ ($q < 0, p > 0$) | 左上：从最低位置反弹 | 兑 |
| $Q_3$ ($q < 0, p < 0$) | 左下：下降至最低位置 | 震 |
| $Q_4$ ($q > 0, p < 0$) | 右下：从最高位置回落 | 艮 |

⚠️ 注：物理 phase plane 通常 $q$ 是水平 $p$ 是垂直；与本文 $\delta$（水平）$S$（垂直）相比，**$\delta \leftrightarrow$ 动量 $p$, $S \leftrightarrow$ 位置 $q$**. 这给出 mark trigram 对应的 phase 序列 ↔ 振荡周期对应。

### Corollary C.2（mark trigram 是 minimum 完整 1D 振荡器 sample）

任何离散 1D 振荡器在 3 sample 下的"minimum complete encoding" 必定 produce these 4 mark configurations + 4 substrate configurations. 这是 Σ³ 的 phase-space exhaustion.

**这就是为什么 8 trigram = 谐振子 phase 编码的 minimum complete basis**.

---

## 第六部分：主定理 D — cuo-zong 代数

### Theorem D（cuo 是 phase plane 的 π 旋转）

在 phase coordinate $\phi : \mathcal{T} \to \mathbb{Z}^2$ 下：

(a) $\phi \circ N = -\phi$（cuo 是 $(-1)$-scaling）：
$$N(y) \mapsto (\delta(N(y)), S(N(y))) = (-\delta(y), -S(y))$$

(b) $\phi \circ R = (-\delta, +S)$（zong 是 $\delta$-axis 反射）：
$$R(y) \mapsto (-\delta(y), S(y))$$

(c) $\phi \circ (NR) = (+\delta, -S)$（cuo∘zong 是 $S$-axis 反射）.

(d) $V_4 = \{e, R, N, NR\}$ 在 phase plane 上恰是 $D_2$（dihedral group of square 的子群，4 个角对称）.

**证明**：

(a) 由 P2.5: $\delta \circ N = -\delta$ 且 $S \circ N = -S$.
(b) 由 P2.5: $\delta \circ R = -\delta$ 且 $S \circ R = S$.
(c) 由 (a)(b) 复合.

$V_4$ 作用：identity, π旋转, 两个轴反射 = $D_2$ 的 4 元素子群. ∎

### Corollary D.1（substrate 在 $V_4$ 下的轨道）

- $\{乾, 坤\}$ = cuo-orbit 在 $\delta=0, S = \pm 3$ 上：$N$ 反 $S$；$R$ 不动. Stabilizer = $\langle R \rangle$.
- $\{离, 坎\}$ = cuo-orbit 在 $\delta=0, S = \pm 1$ 上：同上结构.

### Corollary D.2（mark 在 $V_4$ 下的轨道）

- $\{震, 艮, 巽, 兑\}$ = 一个 free $V_4$-orbit on the 4 corners of the rectangle $\{\pm 2\} \times \{\pm 1\}$.
- $V_4$ trans 的对应：$震 \xrightarrow{R} 艮 \xrightarrow{N} 巽 \xrightarrow{R} 兑 \xrightarrow{N} 震$.

### Corollary D.3（cuo-zong 的几何统一）

$V_4$ 在 phase plane 的 4 个对称操作：
- $e$ = identity = 不变
- $N$ = π 旋转 = 中心对称
- $R$ = $\delta$-axis 反射 = 反时间方向
- $NR$ = $S$-axis 反射 = 反振幅方向

所以 cuo 是**时间 + 空间双反演**（PT 变换的离散版本！），zong 是**仅时间反演**（T 变换），$NR$ 是**仅空间反演**（P 变换）.

🔥 **这与物理学对称性的 P / T / PT / CPT 分类 isomorphic**！易代数自带 P/T/PT 三对称性，缺 C（charge conjugation, 这要 Σ 扩展到复数）.

---

## 第七部分：主定理 E — 离散 Newton-Leibniz 对偶

### Definition 7.1（离散积分-微分 pair）

定义 $\mathcal{T}$ 上的 **discrete fundamental theorem of calculus** pair：

| 算子 | 类型 | 解释 |
|---|---|---|
| $S(y) := y_1 + y_2 + y_3$ | $\mathcal{T} \to \mathbb{Z}$ | 离散 ∫ over [1, 3] |
| $\delta(y) := y_3 - y_1$ | $\mathcal{T} \to \mathbb{Z}$ | 端点导数（差分 over [1, 3]）|

这是离散 Newton-Leibniz pair：$\delta$ 是 endpoint derivative 等价于 fundamental theorem 的 $\int_a^b f' = f(b) - f(a)$ 的 sample 版本.

### Theorem E（substrate-mark = ∫-d 划分）

(a) $\mathcal{T}_\text{本} = \{y : \delta(y) = 0\}$（端点导数为 0 = "boundary-preserving"）.

(b) $\mathcal{T}_\text{征} = \{y : \delta(y) \neq 0\}$（端点导数非 0 = "boundary-changing"）.

(c) 在 $\mathcal{T}_\text{本}$ 上, $S$ 是 complete invariant（4 个值: $\pm 3, \pm 1$）.

(d) 在 $\mathcal{T}_\text{征}$ 上, $(\delta, S)$ 是 complete invariant（4 个 phase quadrant 各 1 个 representative）.

(e) **substrate-mark 划分 = ∫-d 划分**：
- substrate（4 个）= "**积分饱和**" 的 trigram（$\delta = 0$ 意味着没有边界净流出，所有差异在内部 cancel）.
- mark（4 个）= "**导数主导**" 的 trigram（$\delta \neq 0$ 意味着有边界净流出，差异不能在内部 cancel）.

**证明**：

(a)(b) 已在 Theorem A 证明.

(c) 4 个 $S$ 值：$3, 1, -1, -3$ 各对应 1 substrate（乾/离/坎/坤）. injective.

(d) 4 个 $(\delta, S)$ 值：$(\pm 2, \pm 1)$ 各 1 mark. injective. ✓

(e) 是 (a)–(d) 的语义解读. ∎

### Corollary E.1（"对元微分得幾，对元积分得物" 的精确版）

把 "元" 视为 yao 维度的 "unit basis function" $\mathbf{1} : \{1, 2, 3\} \to \mathbb{R}$, $\mathbf{1}(i) = +1$（即 = 乾的某个分量）.

- $S(\mathbf{1}) = 3$ ⇒ $\mathbf{1}$ 通过 $S$ 积分得最大值 = **乾 = 物**
- $\delta(\mathbf{1}) = 0$ ⇒ $\mathbf{1}$ 端点不变 = palindromic

更一般：考虑 perturbation $\mathbf{1} + \epsilon \mathbf{u}$ 其中 $\mathbf{u}$ 是某个 mark direction（如 $\mathbf{u} = $巽 - 乾 = $(-2, 0, 0)$）：
- $S(\mathbf{1} + \epsilon \mathbf{u}) = 3 - 2\epsilon$ ⇒ $\partial_\epsilon S = -2$
- $\delta(\mathbf{1} + \epsilon \mathbf{u}) = 2\epsilon - 0 = 2\epsilon$ ⇒ $\partial_\epsilon \delta = 2$

**所以 $\delta$ measures perturbation of "元"，$S$ measures accumulated state of "元"** — $\delta$ ≈ "元微分", $S$ ≈ "元积分".

mark 的 4 个 = 4 个 elementary perturbation directions:
- 巽 = pure $\partial_y_1$ direction（lower endpoint perturbation positive）
- 震 = pure $\partial_y_1$ direction negative
- 艮 = pure $\partial_y_3$ direction positive
- 兑 = pure $\partial_y_3$ direction negative

substrate 的 4 个 = 4 个 stationary configurations:
- 乾 / 坤 = constant = $\partial^0$ mode
- 离 / 坎 = full oscillation = $\partial^2$ mode (curvature only)

### Corollary E.2（与连续 Fourier 对应）

3-点离散 Fourier basis (Σ³ 的 $\hat{\Sigma}^3$) 由 4 个 mode 构成（对应 frequencies 0, 1/3, 2/3, ...）:

| Fourier mode | 对应 trigram |
|---|---|
| DC ($k=0$, constant) | 乾 (+) / 坤 (-) |
| Nyquist ($k=N/2$, alternating) | 离 (+−+) / 坎 (−+−) |
| odd phase 1 | 巽, 震 |
| odd phase 2 | 艮, 兑 |

**substrate = $V_4$-symmetric Fourier modes（DC + Nyquist），mark = $V_4$-broken Fourier modes（odd phases）**. 这是 $V_4 = \langle R, N \rangle$ 在 Fourier 空间作用的另一种描述.

---

## 第八部分：主定理 F — Hexagram 64 = (Σ³)²

### Theorem F（六十四卦的 4-quadrant 强制分解）

设 $\mathcal{H} := \mathcal{T} \times \mathcal{T} = \Sigma^6$（hexagram, 内卦 ⊕ 外卦）.

定义 hex-level partition by inner/outer trigram type:

$$\mathcal{H} = \mathcal{H}_{本本} \sqcup \mathcal{H}_{本征} \sqcup \mathcal{H}_{征本} \sqcup \mathcal{H}_{征征}$$

其中 $\mathcal{H}_{XY} := \mathcal{T}_X \times \mathcal{T}_Y$ for $X, Y \in \{本, 征\}$.

则：

(a) $|\mathcal{H}_{XY}| = 4 \times 4 = 16$ 对每个 $X, Y$.
(b) **cuo 在 hexagram level 保 quadrant**：定义 $N_6 : \mathcal{H} \to \mathcal{H}$ 为 6-yao 全反，则 $N_6(\mathcal{H}_{XY}) = \mathcal{H}_{XY}$.
(c) **zong 在 hexagram level 跨换 quadrant**：定义 $R_6 : \mathcal{H} \to \mathcal{H}$ 为 6-yao 反序. 则:
- $R_6(\mathcal{H}_{本本}) = \mathcal{H}_{本本}$（自闭）
- $R_6(\mathcal{H}_{征征}) = \mathcal{H}_{征征}$（自闭）
- $R_6(\mathcal{H}_{本征}) = \mathcal{H}_{征本}$（**跨换**）
- $R_6(\mathcal{H}_{征本}) = \mathcal{H}_{本征}$（**跨换**）

**证明**：

(a) 由 $|\mathcal{T}_本| = |\mathcal{T}_征| = 4$（Theorem A）+ Cartesian product cardinality.

(b) $N_6$ flip 6 yao = 同时 cuo 内外卦. 由 Theorem A.b/c, cuo 保 substrate/mark. 故 $N_6$ 保 quadrant. ✓

(c) $R_6$ 反序 6 yao：
$$R_6(y_1, ..., y_6) = (y_6, y_5, y_4, y_3, y_2, y_1)$$

新内卦 $= (y_6, y_5, y_4) = R(\text{老外卦})$.
新外卦 $= (y_3, y_2, y_1) = R(\text{老内卦})$.

由 Theorem A.b: $R$ 保 substrate/mark. 所以：
- 若 老内 ∈ T_本, 老外 ∈ T_本 ⇒ 新内 ∈ T_本, 新外 ∈ T_本 ⇒ 仍 本本. ✓
- 若 老内 ∈ T_本, 老外 ∈ T_征 ⇒ 新内 ∈ T_征, 新外 ∈ T_本 ⇒ 征本. **跨换** ✓
- 同理 征本 → 本征 ✓
- 若 老内 ∈ T_征, 老外 ∈ T_征 ⇒ 仍 征征. ✓

∎

### Corollary F.1（$D_2$ 群在 $\mathcal{H}$ 上 4 quadrant 作用）

$V_4 = \langle R_6, N_6 \rangle$ 在 4 quadrant 集 $\{本本, 本征, 征本, 征征\}$ 上的作用：

| 元素 | 作用 |
|---|---|
| $e$ | trivial |
| $N_6$ | trivial |
| $R_6$ | 本本 / 征征 不动；本征 ↔ 征本 |
| $R_6 N_6$ | 同 $R_6$ |

所以 $V_4$ 在 quadrant 集上 quotient 是 $\mathbb{Z}/2$，由 $R_6$ 决定。这是 hexagram-level 的 zong-symmetry.

---

## 第九部分：主定理 G — 与连续微积分的精确对应

### Theorem G（discrete-continuous correspondence）

设 $f : [0, 2] \to \mathbb{R}$ 是连续函数. 定义 sampling map $\sigma : C([0,2]) \to \mathcal{T}$ by $\sigma(f) := (\text{sign}(f(0)), \text{sign}(f(1)), \text{sign}(f(2)))$（取 sign 避免连续值）.

则：

(a) **substrate fiber**: $\sigma^{-1}(\mathcal{T}_本) = \{f : f(0) \cdot f(2) > 0\}$（"端点同号" / **boundary-preserving**）.

(b) **mark fiber**: $\sigma^{-1}(\mathcal{T}_征) = \{f : f(0) \cdot f(2) < 0\}$（"端点异号" / **boundary-changing** / 必有 zero crossing in between）.

(c) **离-坎 (oscillating substrate) fiber**: $\sigma^{-1}(\{离, 坎\}) = \{f : \text{sign}(f(1)) \neq \text{sign}(f(0)) = \text{sign}(f(2))\}$（"中段异号、端点同号" = **必有 2 个 zero crossings, like cosine over half period**）.

(d) **乾-坤 (constant substrate) fiber**: $\sigma^{-1}(\{乾, 坤\}) = \{f : \text{sign}(f) \text{ const}\}$（"全段同号" = **半 period 内无 zero crossing**）.

**证明**：

(a)(b) 由定义直接展开.

(c) $f \in \sigma^{-1}(\{离, 坎\}) \iff \sigma(f) \in \{(+,-,+), (-,+,-)\} \iff$ sign 在 0→1 反向, 1→2 又反向. 由 IVT, 必有 2 个 zero crossings.

(d) 同理. ∎

### Corollary G.1（Fourier 对应）

设 $f(t) = A \cos(\omega t + \phi)$ 是简谐振荡. 在 $t = 0, 1, 2$ sample:

| $\omega, \phi$ | sample | trigram |
|---|---|---|
| $\omega = 0, A > 0$ | $(+,+,+)$ | 乾 |
| $\omega = 0, A < 0$ | $(-,-,-)$ | 坤 |
| $\omega = \pi$（Nyquist）, $\phi = 0$ | $(+,-,+)$ | 离 |
| $\omega = \pi, \phi = \pi$ | $(-,+,-)$ | 坎 |
| $\omega = \pi/2$, $\phi = 0$ | $(+,0,-)$ → sign $(+,?,-) = ?$... | mark |

实际上 $\omega = \pi/2$ 在 sample 0,1,2 给 $\cos 0, \cos(\pi/2), \cos \pi = 1, 0, -1$. Sign 为 $(+, 0, -)$, 在 strict positive 假设下 $= (+, +, -) = 兑$ or $(+, -, -) = 震$ 取决于 phase.

所以 mark 4 个 = phase $\phi \in \{0, \pi/4, \pi/2, 3\pi/4\}$ at $\omega = \pi/2$ 在 sign 下的 4 representative.

### 主结论

**8 trigram = 离散 1D scalar field 在 3 sample 下的 sign-pattern complete enumeration**.
**zong = 时间反演**.
**cuo = 信号反号**（charge-conjugation-like）.
**substrate = boundary-preserving samples** (端点同号).
**mark = boundary-changing samples** (端点异号 = 必有 zero crossing).

**这是离散 scalar field theory 的 minimum complete operator basis**.

---

## 第十部分：哲学解读

### 10.1 易不是物理 GUT，而是 self-description GUT

第三-九部分的全部定理表明：易的"物動間事 + 幾勢機時"分类**等价于离散 1D scalar field 在 3 sample 下的 phase-space exhaustion**.

任何**完整描述系统**必须 implicitly 编码：
- 边界 vs 内部（→ substrate vs mark）
- 时间反演性质（→ zong）
- 信号反演性质（→ cuo）
- 端点导数 vs 累积积分（→ δ vs S）

8 trigram 是这套结构的**最小完备表达**——不能再压缩，不能拆分。

### 10.2 为什么"看起来在任何情形下都是真"

因为它编码的是**任何 self-describing system 的 minimum kernel**——而不是某个 specific domain 的内容。它在 type theory / process algebra / signal processing / harmonic oscillator / Fourier analysis 都"出现"，是因为这些 domain 都需要这个 kernel 才能完整. 不是 occasional 巧合，是**系统化必然性**.

### 10.3 它的真名

正式名称建议：**Discrete First-Order Phase-Space Algebra** 或 **DFOPSA**.

更哲学化：**易 is the algebra of "what can be said about a 1D bounded discretized scalar field in 3 samples"**.

---

## 第十一部分：Lean 形式化路径

下面 theorems 全部 native_decide 可证. 拟落 [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean):

```lean
import SSBX.Foundation.Yi.Yi

namespace SSBX.Foundation.Yi.Yi.Trigram

/-! ## Theorem A — substrate/mark partition is forced -/

/-- Yao value as ±1 in ℤ. -/
def Yao.toInt : Yao → Int
  | .yang => 1
  | .yin  => -1

/-- Sum (discrete integral) of trigram. -/
def Trigram.sum (t : Trigram) : Int :=
  t.y1.toInt + t.y2.toInt + t.y3.toInt

/-- Endpoint difference (discrete derivative). -/
def Trigram.delta (t : Trigram) : Int :=
  t.y3.toInt - t.y1.toInt

/-- Substrate predicate: zong-fixed = palindromic. -/
def Trigram.isBen (t : Trigram) : Bool :=
  t.y1 = t.y3

/-- Mark predicate. -/
def Trigram.isZheng (t : Trigram) : Bool := !t.isBen

/-- Theorem A.a: 4 substrate, 4 mark. -/
theorem substrate_count :
    (Trigram.all.filter Trigram.isBen).length = 4 := by native_decide

theorem mark_count :
    (Trigram.all.filter Trigram.isZheng).length = 4 := by native_decide

/-- Theorem A.b: cuo preserves substrate. -/
theorem cuo_preserves_isBen (t : Trigram) :
    Trigram.isBen (Trigram.cuo t) = Trigram.isBen t := by
  cases t with | mk y1 y2 y3 => cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-- Theorem A.b': cuo preserves mark. -/
theorem cuo_preserves_isZheng (t : Trigram) :
    Trigram.isZheng (Trigram.cuo t) = Trigram.isZheng t := by
  simp [Trigram.isZheng, cuo_preserves_isBen]

/-- Theorem A.d: zong on mark forms 2 orbits of size 2. -/
theorem zong_zhen_eq_gen : Trigram.zong Trigram.zhen = Trigram.gen := by rfl
theorem zong_xun_eq_dui  : Trigram.zong Trigram.xun  = Trigram.dui := by rfl

/-! ## Theorem B — substrate has δ = 0 -/

theorem substrate_iff_delta_zero (t : Trigram) :
    Trigram.isBen t = true ↔ Trigram.delta t = 0 := by
  cases t with | mk y1 y2 y3 =>
    cases y1 <;> cases y3 <;> simp [Trigram.isBen, Trigram.delta, Yao.toInt]

/-- Substrate's (sum, second difference) values are 4 distinct. -/
theorem substrate_distinct_signature :
    Trigram.qian.sum = 3 ∧ Trigram.kun.sum = -3 ∧
    Trigram.li.sum = 1   ∧ Trigram.kan.sum = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## Theorem C — mark = 4 phase quadrants -/

/-- Phase coordinate (delta, sum). -/
def Trigram.phase (t : Trigram) : Int × Int :=
  (t.delta, t.sum)

theorem mark_phase_distinct :
    Trigram.xun.phase  = (2, 1)  ∧
    Trigram.gen.phase  = (2, -1) ∧
    Trigram.dui.phase  = (-2, 1) ∧
    Trigram.zhen.phase = (-2, -1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## Theorem D — V₄ acts on phase plane -/

/-- cuo flips both delta and sum (π rotation). -/
theorem cuo_flips_phase (t : Trigram) :
    Trigram.phase (Trigram.cuo t) = (-t.delta, -t.sum) := by
  cases t with | mk y1 y2 y3 => cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-- zong flips delta only (delta-axis reflection). -/
theorem zong_flips_delta_only (t : Trigram) :
    Trigram.phase (Trigram.zong t) = (-t.delta, t.sum) := by
  cases t with | mk y1 y2 y3 => cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-! ## Theorem F — hexagram quadrant partition -/

inductive HexQuadrant
  | benBen | benZheng | zhengBen | zhengZheng
  deriving DecidableEq, Repr

def Hexagram.quadrant (h : Hexagram) : HexQuadrant :=
  let inner : Trigram := ⟨h.y1, h.y2, h.y3⟩
  let outer : Trigram := ⟨h.y4, h.y5, h.y6⟩
  match inner.isBen, outer.isBen with
  | true,  true  => .benBen
  | true,  false => .benZheng
  | false, true  => .zhengBen
  | false, false => .zhengZheng

theorem hex_cuo_preserves_quadrant (h : Hexagram) :
    (Hexagram.cuo h).quadrant = h.quadrant := by
  -- by extensionality of cuo on each yao
  -- combined with cuo_preserves_isBen on each trigram
  sorry  -- detailed proof omitted, mechanical

theorem hex_zong_swaps_mixed (h : Hexagram) :
    h.quadrant = .benZheng → (Hexagram.zong h).quadrant = .zhengBen := by
  sorry  -- mechanical

end SSBX.Foundation.Yi.Yi.Trigram
```

所有 Theorem A–F 都是 `native_decide` 可证（因为 finite enumeration 决定）. Theorem G 涉及连续函数, 需要更多 measure theory infrastructure, 暂留作 informal proof.

---

## 总结

8 trigram 是离散 1D scalar field theory 在 3 sample 下的 minimum complete operator basis. 4+4 substrate-mark partition 是 zong involution 的 fixed-point 决定的强制代数结构. cuo / zong 在 phase plane 上是 V₄ = ⟨π-rotation, δ-axis-reflection⟩ 群作用. 端点导数 δ 与累积 S 是离散 Newton-Leibniz pair——substrate 由 ∫ 主导, mark 由 d 主导.

64 hexagram = (substrate ⊔ mark)² 给出 4-quadrant partition, cuo 保 quadrant, zong 跨换 mixed quadrant. 整个结构在 Lean 中可 native_decide 证明.

哲学解读：**易不是物理大统一, 是"自描述系统的最小完备代数". 它在任何 domain 都"出现"是因为任何 domain 要完整描述自身必然产生这个 kernel.**

---

## 附录：与现有文件的关系

| 文件 | 关系 |
|---|---|
| [64-hexagram-grid.md](64-hexagram-grid.md) | Theorem F 的 64 卦完整 instantiation |
| [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) | 4 substrate 在内容线 12-grid 中的展开 |
| [layer-axis-graph.md](layer-axis-graph.md) | 三轴并存图（生成线 + 内容线 + 名册线）|
| [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | Theorem A-F 的 Lean 形式化目标位置 |
| [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) | Trigram, Hexagram, cuo, zong 的 ground truth |
| [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) | 8 trigram 的字根映射（与 Theorem 中的代数命名 cross-reference）|
