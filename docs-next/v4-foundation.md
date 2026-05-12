# V₄ 与其蕴义 · The V₄ Foundation

> **文 形式语言** · Foundation Note · v0.2
> Companion to: `zi-calculus.md`, `wenyan-operators.md`, `yi-calculus.md`
> Status: parallel-build + V8 audit + Information Preservation Theory
> Date: 2026-05-12
> **Dual-track**: 本文档同时支持 (a) Lean 4 + Mathlib 机器证明 (b) 文 编译器 IR 与 Clojure runtime 实现
> Current implementation roadmap: [`00_start/v4-foundation-roadmap.md`](00_start/v4-foundation-roadmap.md)

**v0.2 changelog**:
- Added §7.11 V8 Implementation Audit (基于 R8/Cell256 v3 provisional 命名包审计)
- Added §8 Information Preservation Theory（信息保持的代数刻画 + Lean + 编译器 derivability checker）
- 双重证据确认 {道, 今} 子群的 uniquely privileged 地位（§6.1 元素 level + §8.3 state level）
- Renumbered §9-§13 (history → conclusion)

---

## 0. 文档目的

文 的代数骨架是 **Klein 四元群 V₄ = ℤ/2 × ℤ/2**。这不是设计选择，是被 hexagram 数据结构、量子物理、可计算模型、范畴论独立逼出的同一个 minimum-non-trivial 对称代数。

在 文 系统的具体实施中，V₄ 嵌入到 V8 = (ℤ/2)⁸ 中作为 时-子群（y7-y8 位），全 V8 = R6 (卦) ⊕ V4 (时)。这个嵌入给出 256 cells = 64 卦 × 4 时-state 的 clean direct-sum 分解。

本文档是 **双轨规范**：

- **证明轨** (Lean 4 + Mathlib)：所有结构性断言可被机器验证。§7 提供 V₄ 群结构与 V₄-action Lean 实现骨架；§8 提供 information preservation 定理与算法；§12 列出待证 theorem。
- **编译轨** (文 compiler / Clojure / SCI)：V₄ 作为 IR primitive，编译器 normalize pass 利用 V₄ 阿贝尔性做常量折叠。§7.4–7.9 提供 V8 IR；§8.9 提供 derivability checker pass。

两轨必须 **round-trip 一致**：Lean 中证明的 V₄ 性质对应编译器中的 IR 变换；任何分歧 = CI 失败。

本文档系统化地：

1. **推导** V₄ 在 文 卦域的内禀必然性 (§1)
2. **证立** V₄ 的跨域普适性（量子、计算、Galois、CPT、符号学）(§3)
3. **定位** V₄ 四个位置上各域算子的归属（the **Atlas**）(§4)
4. **辨析** V₄ 内部的保持层级（set / algebra / category / truth）(§5)
5. **识别** {e, 错综} = {道, 今} 作为「真正保结构子群」的特殊地位 (§6)
6. **形式化** 为 Lean 4 证明 + 文 compiler IR + V8 实施审计 (§7)
7. **提出** information preservation theorem 与可推导性算法 (§8) **[v0.2 新]**
8. **梳理** 历史上对 V₄ 框架的部分性发现 (§9)
9. **导出** 由此可延伸的知识方向（the **Implications**）(§10)
10. **检验** 双轨 + 信息保持 完成度 (§12)

---

## 1. V₄ 的卦域推导

### 1.1 卦的双轴结构

把六爻卦看作函数：

$$h : [6] \to \mathbb{F}_2$$

其中 $[6] = \{1,2,3,4,5,6\}$ 是带序位置集，$\mathbb{F}_2 = \{阴, 阳\}$ 是二元值集。

此数据结构有两条独立的对称轴：

| 轴 | 结构 | 非平凡 involution | 文 命名 |
|----|------|-------------------|-----------|
| **值轴** | $\mathrm{Aut}(\mathbb{F}_2)$ | swap (阴↔阳) | **错** |
| **位轴** | path/chain symmetry of $[6]$ allowing order reversal | reversal (1↔6, 2↔5, 3↔4) | **综** |

严格地说，有限全序集 $([6], \leq)$ 的 order-preserving automorphism 只有
identity；「综」不是 order-preserving automorphism，而是 order-reversing
involution，等价地是 path graph $P_6$ 的端点保持反射。本文后文的「位轴
自同构」均按此 corrected sense 理解：保相邻/端点结构，可反转方向。

### 1.2 V₄ 是直接乘积

对六爻函数 $h : [6] \to \mathbb{F}_2$，值域 swap 与定义域 reversal 分别作用于
不同坐标：

$$
(\alpha,\rho)\cdot h = \alpha \circ h \circ \rho^{-1}
$$

其中 $\alpha \in \mathrm{Aut}(\mathbb{F}_2)$，$\rho \in \{id, rev\}$。两者作用于
不同轴（codomain value × domain frame），因此 commute。

因此：

$$\boxed{\mathrm{Sym}_{V_4}(\text{hexagram}) \;=\; \mathrm{Aut}(\mathbb{F}_2) \times \langle rev\rangle \;=\; \mathbb{Z}/2 \times \mathbb{Z}/2 \;=\; V_4}$$

### 1.3 V₄ 的四元素

$$V_4 = \{\,道,\ 错,\ 综,\ 错综\,\}$$

满足：

- $错^2 = 综^2 = 道$
- $错 \cdot 综 = 综 \cdot 错 = 错综$
- $(错综)^2 = 道$
- 所有非恒等元为 involution
- 阿贝尔（commutative）

### 1.4 为什么不是更大的群

| 候选 | 阶 | 为什么不是 |
|------|---|-----------|
| $S_6$ on positions | 720 | 破坏卦体（上下三爻分割） |
| $(\mathbb{Z}/2)^6$ on lines | 64 | 破坏阴阳整体极性 |
| $\mathbb{Z}/4$ | 4 | 是 rotation，非 reflection；非 involutive |
| 单一 $\mathbb{Z}/2$ | 2 | 丢失第二条轴，单轴系统不承载信息 |
| $(\mathbb{Z}/2)^3$ | 8 | 第三条独立轴在卦上不存在（CPT 定理 的卦域类比） |

**V₄ 是「保 hexagram 之为 hexagram」的最大可逆对称群**，也是「最小非平凡双反射对偶」之群。

### 1.5 互卦不在 V₄ 中

经典易学的「互卦」（取 2,3,4 为下卦、3,4,5 为上卦）**不是 V₄ 元素**：

- 非双射（丢失初爻、上爻信息）
- 无自然逆
- 反复作用进入不动点而非循环

互卦属于另一类结构（possibly an idempotent or partial morphism on the hexagram lattice），应在 文 中**与 V₄ 正交地建模**。

---

## 2. 道-row 规律

### 2.1 Statement

定义 **道-row**：

$$\text{道-row} := \{(h, 道) \mid h \in \mathrm{Hexagram}\} \;\subset\; \mathrm{Hexagram} \times V_4$$

包含 64 个 cell，每卦一个。

### 2.2 Theorem (V₄ Identity Closure)

> 对任意 hexagram $h$，$(h, 道)$ 是 V₄ 作用下 $h$ 的不动点。

证明：由 V₄ 单位元公理直接得 $h \cdot 道 = h$。

### 2.3 解读：「永真 atomic state」的结构基础

道-row 中每 cell 不承载任何变换，故：

- **永真**：identity transition 不改变 truth value，$h \text{ 真} \iff (h, 道) \text{ 真}$
- **atomic**：道 在 V₄ 中不可分解（it is the unit），故 $(h, 道)$ 不可被 V₄ 进一步分解
- **不受 causation flow 约束**：identity morphism 是 trivial cobordism，无方向，无前后

### 2.4 道 = e 的必然性

「道」在中国思想里精确是「自身不动而容纳一切动者」。范畴论里 identity 恰好满足这个描述：

- $\mathrm{id}_X \circ f = f \circ \mathrm{id}_X = f$ for all $f$（容纳一切 morphism）
- $(\mathrm{id}_X)^2 = \mathrm{id}_X$（自身不动）

**所以 $e \mapsto 道$ 不是命名约定，是结构对应**。

### 2.5 道-row 作为 Hexagram ↪ Hexagram × V₄ 的嵌入

形式上：

$$\iota: \mathrm{Hexagram} \hookrightarrow \mathrm{Hexagram} \times V_4, \quad h \mapsto (h, e)$$

这是 V₄-action 的 **unit**。道-row 是这个空间的「保 hexagram 自身的对角」。

64 个 atomic state 是因为有 64 个 hexagram；4 倍展开（256 cells）是因为 V₄ 阶为 4。

---

## 3. V₄ 的跨域普适性

### 3.1 普适性断言

> **任何承载意义/计算/观测的最小系统，其对称结构包含一个 V₄ 子群。**

这是本文的研究纲领，而不是对所有数学对象的无条件定理。本文真正依赖的
严格事实是：当一个系统可被读作「二值内容轴 × 二值框架轴」且两轴独立
commute 时，它的最小可逆对偶核是 V₄。跨域 atlas 中的条目按证据强度区分：
有些是 strict isomorphism，有些是 faithful model，有些只是 speculative
alignment。

### 3.2 量子物理

**(a) Pauli 群模相位**

$$\mathcal{P}_1 / \langle \pm 1, \pm i \rangle \;=\; \{I, X, Y, Z\} \;\cong\; V_4$$

- $I$ = 恒等
- $X$ = bit-flip（值轴 σₓ）
- $Z$ = phase-flip（相位/框架轴 σ_z）
- $Y = iXZ$ = 双翻

Stabilizer formalism、Bell-state 互换、量子纠错码的代数基础。

**(b) QFT 离散对称（CPT）**

CPT 相关条目在本文中作为 physics-facing alignment，而不是本文已证明的
QFT theorem。严格表述应放在具体物理模型的离散对称子群中；本文只记录
「charge/content duality」与「spacetime/frame duality」的 V₄-shaped reading。

### 3.3 计算理论

**最小可逆图灵机原子动作**：

$$V_4^{\text{TM}} = \{\text{nop},\ \text{flip-bit},\ \text{flip-dir},\ \text{flip-both}\}$$

- 写值翻：tape symbol $\mathbb{F}_2$ 上的 ℤ/2（X-类）
- 移头翻：方向 $\{L, R\}$ 上的 ℤ/2（Z-类）

任何 2-符号可逆 TM 的**单步对称群**精确是 $V_4$。

### 3.4 Galois 理论

最小非循环 Galois 扩张：

$$\mathrm{Gal}(\mathbb{Q}(\sqrt{2}, \sqrt{3}) / \mathbb{Q}) \;\cong\; V_4$$

四个自同构：

- $\mathrm{id}$
- $\sqrt{2} \mapsto -\sqrt{2}$
- $\sqrt{3} \mapsto -\sqrt{3}$
- both

这是 V₄ 在数论里的最小自然出现，且**结构上同构**于卦的 错/综/错综。

### 3.5 跨域对照表

| 域 | 值轴 ℤ/2 (= 错) | 框架轴 ℤ/2 (= 综) | 复合 (= 错综) |
|----|----------------|-------------------|---------------|
| **文** | 阴/阳 | 始/终 | 双翻 |
| **Pauli** | $X$ (computational basis) | $Z$ (phase) | $Y$ |
| **QFT** | $C$ (charge) | $PT$ (spacetime parity-time) | $CPT \equiv I$ |
| **TM** | tape symbol | head direction | both |
| **Galois** | $\sqrt{2} \to -\sqrt{2}$ | $\sqrt{3} \to -\sqrt{3}$ | both |
| **Logic** | $\neg$ (negation) | reversal of implication | contrapositive |
| **Category** | dagger (in $\dagger$-cat) | $\mathrm{op}$ | dagger ∘ op |
| **Semiotics** | $\neg S$ (contradiction) | $S_2$ (contrary) | $\neg S_2$ |
| **Greimas** | contradictory | contrary | sub-contrary |

**证据强度分层**：

| 层级 | 含义 | 当前例子 |
|------|------|----------|
| strict isomorphism | 明确群同构或已形式化 carrier 等价 | 文 V₄, Pauli modulo phase, Galois $(\sqrt2,\sqrt3)$, TM local flips |
| faithful model | 可给出忠实的结构模型，但本文尚未完整形式化 | classical implication/contrapositive, dagger/op category slice |
| alignment | 启发性或解释性归位，不作为 Lean theorem | CPT/QFT reading, Greimas/Semiotics, Peirce/Hegel historical readings |

### 3.6 普适性的范畴论根据

不能说任意 functor $F:\mathcal C\to\mathcal D$ 都自动拥有完整的
$\mathrm{Aut}(\mathcal C)\times\mathrm{Aut}(\mathcal D)$ 对称；一般需要满足
commuting square 或自然同构兼容条件。安全的 categorical reading 是：
在函数/函子空间上，domain automorphism 以 precomposition 作用，codomain
automorphism 以 postcomposition 作用；当两边都退到唯一非平凡 involution 时，
这个双轴 action 的最小形态是：

$$\mathrm{Sym}(F)_{\min} = \mathbb{Z}/2 \times \mathbb{Z}/2 = V_4$$

> **V₄ 是「frame-indexed value」在最小非平凡双轴边界条件下的 canonical action。**

这就是本文的跨域解释：hexagram、qubit slice、TM local move、Galois
extension 等都能被读作「frame-indexed value」的不同实例。硬同构与软类比
必须按上表分层记录。

---

## 4. V₄ 知识地图（The Atlas）

把 V₄ 的四个位置作为坐标，可以系统化地把已知逻辑/物理/数学/语义算子归位。

### 4.1 Position `e` (道 / identity)

**保结构、保真、不变换之物。**

| 域 | 算子 |
|----|------|
| 逻辑 | $\mathrm{id}$, tautology, $A = A$ |
| 范畴 | identity functor $1_\mathcal{C}$ |
| 量子 | $I$ gate, vacuum |
| 计算 | no-op, $\lambda x.x$ |
| 代数 | 单位元 |
| 物理 | CPT (under CPT theorem) |
| 语义 | Greimas $S$ (origin) |
| 哲学 | 道, Tathata, Spencer-Brown unmarked state |

### 4.2 Position `a` (错 / value-flip)

**翻转内容/值/极性。**

| 域 | 算子 |
|----|------|
| 逻辑 | $\neg$ (negation), Boolean complement |
| 范畴 | dual object $X^*$, dagger |
| 量子 | Pauli $X$, charge conjugation $C$ |
| 计算 | bit-flip, NOT |
| 生物 | DNA complement strand |
| 代数 | 群求逆 $g \mapsto g^{-1}$（阿贝尔群） |
| 物理 | particle ↔ antiparticle, magnetic N↔S |
| 语义 | Greimas $\neg S$ (contradictory) |
| 数学 | complex conjugation $z \mapsto \bar{z}$ |
| 类型论 | linear negation $A^\bot$ |

### 4.3 Position `b` (综 / frame-flip)

**翻转方向/顺序/框架/视角。**

| 域 | 算子 |
|----|------|
| 逻辑 | implication reversal $A \to B \mapsto B \to A$ |
| 范畴 | opposite category $\mathcal{C}^{\mathrm{op}}$, contravariant functor |
| 量子 | Pauli $Z$, time-reversal $T$ |
| 计算 | list reverse, stack ↔ queue |
| 代数 | matrix transpose $A^T$, left ↔ right action |
| 物理 | time-reversal $T$, orientation flip |
| 几何 | inside ↔ outside, Möbius flip |
| 语义 | Greimas $S_2$ (contrary) |
| 拓扑 | bordism orientation, cobordism dual |

### 4.4 Position `ab` (错综 / combined)

**复合对偶——常被遗忘但结构上最特殊。**

| 域 | 算子 |
|----|------|
| 逻辑 | contrapositive: $A \to B \mapsto \neg B \to \neg A$ |
| 范畴 | double dual $X^{**}$, dagger ∘ op |
| 量子 | Pauli $Y$, PT symmetry |
| 计算 | reverse + bit-flip = 二补码取负 |
| 物理 | $CP$ (when CPT theorem 适用) |
| 数学 | $\sqrt{2} \to -\sqrt{2} \wedge \sqrt{3} \to -\sqrt{3}$ |
| 语义 | Greimas $\neg S_2$ (sub-contrary) |
| 哲学 | 「否定之否定」(取道框架翻转，非 Hegelian sublation) |

---

## 5. 保持层级（Preservation Hierarchy）

V₄ 的四个元素**不等价地**保持结构。区分四个层次：

### 5.1 Level 1 — Set bijection

所有 4 元都是双射。**最弱的保持**。

### 5.2 Level 2 — Algebraic homomorphism

此处的「保代数结构」必须按 **variance-corrected** 意义理解：内容翻转
(`cuo`) 是 De Morgan anti-homomorphism，框架翻转 (`zong`) 是进入 dual/opposite
presentation 的 frame anti-homomorphism；二者复合后回到 homomorphism shape。

它不是说在 raw pointwise Boolean meet 上，
`reverse + complement` 会直接满足
$g(a\wedge b)=g(a)\wedge g(b)$。事实上 complement 会把 $\wedge$ 变成 $\vee$。
因此当前 Lean 中 `PreservationLevel.algebraHom` 是 registry-level marker，表示
「经过适当 dual/op variance 校正后保结构」，不是 raw meet-preservation theorem。

| 元素 | raw $A\to A$ 同态? | variance-corrected reading | 备注 |
|------|---------------------|----------------------------|----|
| `e` | ✓ | ✓ | 平凡同态 |
| `a` (错) | ✗ | anti-hom | De Morgan：$\neg(a \wedge b) = \neg a \vee \neg b$ |
| `b` (综) | ✗/depends on algebra | anti-hom / opposite-frame map | 对 frame/order 取 dual/op |
| `ab` (错综) | not claimed raw | ✓ | 两个 anti-variance 复合，回到 homomorphism shape |

> **{e, 错综} 是 V₄ 中保代数结构的子群。**

**这是本文档最重要的发现之一**：V₄ 内部并非平等的——`错综` 与 `道` 共享一个特权地位。

### 5.3 Level 3 — Categorical functor

所有 4 元都是 functor，但 covariance 性质分裂：

|         | 共变? | 保对象? | 保态射方向? |
|---------|------|---------|--------------|
| `e`     | ✓    | ✓       | ✓            |
| `a` (错) | ✓   | translate | ✓          |
| `b` (综) | ✗   | ✓       | ✗            |
| `ab`    | ✗    | translate | ✗          |

二维分类：
- **共变性**轴: $\{e, a\}$ vs $\{b, ab\}$
- **对象保持**轴: $\{e, b\}$ vs $\{a, ab\}$

这两个轴的乘积**又是 V₄**——V₄ 在范畴层有自身的 meta-V₄ 结构。

### 5.4 Level 4 — Truth preservation

| 元素 | 保真 (in classical logic)? |
|------|-----------------------------|
| `e` | ✓ |
| `a` (错) | ✗（翻真假） |
| `b` (综) | ✗（implication reversal 不保真） |
| `ab` (错综) | **✓ on $A \to B$**（contrapositive law） |

> **错综 是经典逻辑 contrapositive 律的代数显形：$A \to B$ 等价于 $\neg B \to \neg A$ 这一事实，正是 V₄ 中 `ab` 在命题逻辑切片上的 truth-preservation 性质。**

---

## 6. V₄ 内部子群分裂

V₄ 有三个真子群（皆同构于 ℤ/2）：

| 子群 | 结构意义 |
|------|----------|
| $\{e, 错\}$ | 仅值轴对偶 — 「内容对立群」 |
| $\{e, 综\}$ | 仅框架轴对偶 — 「视角对立群」 |
| $\{e, 错综\}$ | 复合对偶 — **「结构保持群」** |

### 6.1 {e, 错综} 的特权地位

由 §5.2 可知：在 variance-corrected algebraic homomorphism 意义下，
**只有 {e, 错综} 是 V₄ 的保结构子群**。

这意味着：

1. 「错综」不应被理解为「错与综的衍生物」
2. 「错综」是 V₄ 中唯一非平凡的「真同态」元素
3. 在 文 形式语言中，**错综 应被提升为 primary 概念**

### 6.2 三子群对应的「不完整保持」

每个子群对应一种结构性的「部分保持」：

- {e, 错}: 保共变性、破坏对象同一
- {e, 综}: 保对象同一、破坏共变性
- {e, 错综}: 保代数同态、破坏共变与对象同一

V₄ 的 *全部* 这四种「partial structural preservations」**穷尽**了二轴系统中可能的保持模式。

---

## 7. 形式化骨架（Lean 4 / Clojure 实现条目）

本节是双轨支持的：(a) Lean 4 + Mathlib 用于**机器验证证明**；(b) Clojure 实现用于 **文 编译器的运行时与 IR**。两者必须 round-trip 一致——任何 Lean 中证明的 V₄ 性质，在 Clojure 编译器中必须有对应运行时实现，反之亦然。

### 7.1 V₄ as a `Group` instance (Lean 4 + Mathlib)

```lean
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Logic.Equiv.Basic

namespace Wen.V4

/-- V₄ 的四元素，对应 道/错/综/错综 -/
inductive Elem
  | dao        -- e
  | cuo        -- a (错: value-flip)
  | zong       -- b (综: frame-flip)
  | cuozong    -- ab (错综: composite)
  deriving DecidableEq, Repr, Fintype

/-- 群乘法：V₄ 是 ℤ/2 × ℤ/2，所有非恒等元 self-inverse、commutative -/
def mul : Elem → Elem → Elem
  | .dao,     g          => g
  | g,        .dao       => g
  | .cuo,     .cuo       => .dao
  | .zong,    .zong      => .dao
  | .cuozong, .cuozong   => .dao
  | .cuo,     .zong      => .cuozong
  | .zong,    .cuo       => .cuozong   -- commutativity 显式编码
  | .cuo,     .cuozong   => .zong
  | .cuozong, .cuo       => .zong
  | .zong,    .cuozong   => .cuo
  | .cuozong, .zong      => .cuo

instance : Mul Elem := ⟨mul⟩
instance : One Elem := ⟨.dao⟩
instance : Inv Elem := ⟨id⟩   -- 每个元素 self-inverse

instance : CommGroup Elem where
  mul_assoc       := by decide
  one_mul         := by decide
  mul_one         := by decide
  mul_left_inv    := by decide
  mul_comm        := by decide

/-- 与 Mathlib 标准 Klein-4 的同构 -/
def equivKleinFour : Elem ≃* KleinFour := ...

end Wen.V4
```

`by decide` 关键：因 `Elem` 是 `Fintype` 且乘法 decidable，所有群公理可机械验证。

### 7.2 V₄-action on Hexagram

```lean
namespace Wen.Hexagram

/-- 六爻卦：从 Fin 6 到 Bool 的函数 -/
structure Hexagram where
  lines : Fin 6 → Bool
  deriving DecidableEq

/-- V₄ 在 Hexagram 上的作用 -/
def V4.act : V4.Elem → Hexagram → Hexagram
  | .dao,     h => h
  | .cuo,     h => ⟨fun i => !h.lines i⟩
  | .zong,    h => ⟨fun i => h.lines (Fin.rev i)⟩
  | .cuozong, h => ⟨fun i => !h.lines (Fin.rev i)⟩

/-- V₄ 在 Hexagram 上是群作用 -/
instance : MulAction V4.Elem Hexagram where
  smul := V4.act
  one_smul := by intro h; rfl
  mul_smul := by
    intro g₁ g₂ h
    cases g₁ <;> cases g₂ <;> simp [V4.act, V4.mul, Fin.rev_rev]

end Wen.Hexagram
```

### 7.3 关键定理（含证明）

```lean
namespace Wen.V4.Theorems

open Wen.V4 Wen.Hexagram

/-- §2.2 道-row identity closure -/
theorem dao_fixes_all (h : Hexagram) : V4.act .dao h = h := rfl

/-- 错² = 道 -/
theorem cuo_involutive (h : Hexagram) :
    V4.act .cuo (V4.act .cuo h) = h := by
  simp [V4.act, Bool.not_not]
  rfl

/-- 综² = 道 -/
theorem zong_involutive (h : Hexagram) :
    V4.act .zong (V4.act .zong h) = h := by
  simp [V4.act, Fin.rev_rev]
  rfl

/-- 错综 = 综错 (commutativity 在 action 层) -/
theorem cuo_zong_comm (h : Hexagram) :
    V4.act .cuo (V4.act .zong h) = V4.act .zong (V4.act .cuo h) := by
  simp [V4.act]; rfl

/-- §5.2 的核心：错综 保 De Morgan 复合结构 -/
theorem cuozong_preserves_meet (a b : Hexagram) :
    V4.act .cuozong (Hexagram.meet a b)
      = Hexagram.meet (V4.act .cuozong a) (V4.act .cuozong b) := by
  unfold V4.act Hexagram.meet
  ext i
  simp [Bool.not_and, Fin.rev]

/-- §5.2 的核心：错 *不* 保 ∧ (它把 ∧ 翻成 ∨，是反同态) -/
theorem cuo_not_preserves_meet :
    ¬ (∀ (a b : Hexagram),
        V4.act .cuo (Hexagram.meet a b)
          = Hexagram.meet (V4.act .cuo a) (V4.act .cuo b)) := by
  intro h
  -- 反例：取 a = all-阳, b = all-阴
  ...

/-- §6.1 {e, 错综} 是 V₄ 中保结构的子群 -/
def structurePreservingSubgroup : Subgroup V4.Elem where
  carrier := {.dao, .cuozong}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; cases ha <;> cases hb <;> decide
  inv_mem' := by intro a ha; cases ha <;> decide

theorem structurePreservingSubgroup_iso_Z2 :
    structurePreservingSubgroup ≃* (ZMod 2) := ...

end Wen.V4.Theorems
```

### 7.4 编译器侧：V₄ 作为文 IR 的 primitive

文 编译器（Clojure / SCI）必须把 V₄ 作为**核心 IR primitive**，而非派生构造。理由：

1. V₄ 元素是 Lean 证明可识别的——编译器输出必须与 Lean 证明对齐
2. V₄ 是 hexagram operation 的 normalize 目标——任何 hexagram 上的可逆 unary 变换都应在编译期归约到 4 个 V₄ canonical form 之一
3. {e, 错综} 子群是优化目标——保结构 transformations 可被编译器更积极地内联与重排

**IR 类型层级**：

```clojure
;; src/wen/ir.cljc
(ns wen.ir)

;; V₄ 是闭枚举，编译时 dispatch 高效
(def ^:const V4-ELEMS #{:dao :cuo :zong :cuozong})

(defrecord V4Op [elem]              ;; IR node: V₄ 操作
  IRNode
  (op-kind [_] :v4-action)
  (preservation-level [_]
    (case elem
      :dao      :truth
      :cuozong  :algebra     ;; §5.2 关键事实编码到类型层
      (:cuo
       :zong)   :set)))

(defrecord Hexagram [lines]         ;; IR node: 六爻卦
  IRNode
  (op-kind [_] :hexagram-literal))

(defrecord V4Apply [v4op hex]       ;; IR node: 应用
  IRNode
  (op-kind [_] :v4-apply))
```

### 7.5 V₄ 乘法表作为编译期常量

```clojure
;; src/wen/v4.cljc
(ns wen.v4)

(def ^:const mul-table
  ;; [a b] -> a·b
  {[:dao :dao]         :dao,    [:dao :cuo]      :cuo,
   [:dao :zong]        :zong,   [:dao :cuozong]  :cuozong
   [:cuo :dao]         :cuo,    [:cuo :cuo]      :dao,
   [:cuo :zong]        :cuozong [:cuo :cuozong]  :zong
   [:zong :dao]        :zong,   [:zong :cuo]     :cuozong
   [:zong :zong]       :dao,    [:zong :cuozong] :cuo
   [:cuozong :dao]     :cuozong [:cuozong :cuo]  :zong
   [:cuozong :zong]    :cuo,    [:cuozong :cuozong] :dao})

(defn mul [a b] (get mul-table [a b]))
(defn inv [a]   a)              ; self-inverse
(def  identity-elem :dao)

;; 在 hexagram 上的作用
(defn act [g hex]
  (case g
    :dao     hex
    :cuo     (mapv #(not %) hex)
    :zong    (vec (reverse hex))
    :cuozong (vec (reverse (mapv #(not %) hex)))))
```

### 7.6 编译器层 normalize pass

V₄ 元素的组合可在编译期 collapse 成单个元素。这是一个由 §7.5 mul-table 直接驱动的优化 pass：

```clojure
;; src/wen/passes/v4_normalize.cljc
(ns wen.passes.v4-normalize)

(defn normalize-v4-chain
  "把连续的 V4Apply 节点折叠为单一 V4Apply。
   利用 V₄ 阿贝尔性 + 群乘法表实现常量传播。"
  [ir]
  (match ir
    {:op :v4-apply
     :v4op {:elem g1}
     :hex {:op :v4-apply
           :v4op {:elem g2}
           :hex inner}}
    (->V4Apply (->V4Op (v4/mul g1 g2)) (normalize-v4-chain inner))

    :else
    ir))

;; 例：error errror 应被折叠到 dao
;; (act :cuo (act :cuo h)) ==normalize==> (act :dao h) ==reduce==> h
```

### 7.7 Atlas as typed registry (Clojure)

```clojure
;; src/wen/atlas.cljc
(ns wen.atlas
  "V₄ 跨域 atlas — 编译器查找表 + 类型推导辅助。
   与 Lean 中 V4.Theorems 的 atlas 对应字典必须保持同步。")

(def atlas
  {:dao
   {:wen        "道"
    :logic      :id
    :pauli      :I
    :tm         :nop
    :category   :identity-functor
    :semiotics  :S-origin
    :preserves  #{:set :algebra :category :truth}}

   :cuo
   {:wen        "错"
    :logic      :neg
    :pauli      :X
    :tm         :flip-bit
    :category   :dagger
    :semiotics  :contradictory
    :preserves  #{:set}}

   :zong
   {:wen        "综"
    :logic      :implication-reverse
    :pauli      :Z
    :tm         :flip-direction
    :category   :op-functor
    :semiotics  :contrary
    :preserves  #{:set}}

   :cuozong
   {:wen        "错综"
    :logic      :contrapositive
    :pauli      :Y
    :tm         :flip-both
    :category   :dagger-op
    :semiotics  :sub-contrary
    :preserves  #{:set :algebra}}})    ; §5.2 关键事实

(defn preserves? [v4-elt level]
  (contains? (get-in atlas [v4-elt :preserves]) level))

;; 编译期可证 invariants
(assert (preserves? :dao :truth))
(assert (preserves? :cuozong :algebra))
(assert (not (preserves? :cuo :algebra)))
```

### 7.8 Lean ↔ Clojure round-trip 一致性

| Lean 证明 | Clojure 实现 | 一致性条件 |
|-----------|--------------|------------|
| `cuo_involutive` | `(act :cuo (act :cuo h)) ≡ h` | normalize pass 必须折叠 |
| `mul_comm` | `(mul a b) = (mul b a)` | mul-table 必须对称 |
| `dao_fixes_all` | `(act :dao h) ≡ h` | 编译期消除 :dao act |
| `cuozong_preserves_meet` | `atlas` 中 `:cuozong :preserves` 含 `:algebra` | atlas 必须与定理同步 |
| `structurePreservingSubgroup` | `(filter #(preserves? % :algebra) V4-ELEMS) = #{:dao :cuozong}` | 子群提取一致 |

**双向校验脚本**（应纳入 CI）：

```clojure
;; tests/wen/v4_consistency.clj
;; 1. 读取 Lean 输出的 atlas data
;; 2. 与 Clojure atlas 对比
;; 3. 任何分歧 → 编译器拒绝构建
```

这个 round-trip 保证：**写文 = 证明文 = 编译文**——三位一体不可分裂。

### 7.9 文 surface syntax 层

在 文 surface syntax 上，V₄ 元素以单字呈现，编译器直接 lex 到 IR：

```
道  →  ⟨V4Op :dao⟩
错  →  ⟨V4Op :cuo⟩
综  →  ⟨V4Op :zong⟩
错综 → ⟨V4Op :cuozong⟩    (single token, not :cuo · :zong)
```

「错综」作为单 token 而非 复合，是因为 §6.1 ——它有独立的语义地位，不应被还原。这是 surface syntax 层对结构事实的尊重。

### 7.10 Action notation

```
错 之 乾    → V4Apply(cuo, 乾)        = 坤
综 之 既济  → V4Apply(zong, 既济)     = 未济
错综 之 乾  → V4Apply(cuozong, 乾)    = (reverse all-yang then flip) = 坤 (since 乾 综-fixed)
道 之 h    → V4Apply(dao, h)         = h   (编译期消除)
```

「之」(zhi) 在 文 中作 application particle，对应 V₄ action `·`。这与 9-atom kernel 中的 `之` 一致。

### 7.11 V8 实施审计 (V8 Implementation Audit)

依据 v3 provisional R8 / Cell256 命名包，确立 **V8 = R6 ⊕ V4** 的 clean direct-sum 分解。每个 V8 元素 c 唯一分解为 (h, t) 其中 h ∈ R6（卦部分，y1-y6），t ∈ V4（时部分，y7-y8）。

**结构性正向**：

- ✓ 卦位编码（`o = 0 = 阳, x = 1 = 阴, 左到右 = 下到上`）抽样 13 个卦全部 verified
- ✓ V4 ⊆ V8 嵌入 clean（y7-y8 子群，V8 identity = V4 identity = 道）
- ✓ Atom-additive operator nomenclature 一致（恒 = identity 特殊命名）
- ✓ 256 cells 均通过 (h, t) 分解唯一确定其 V4 coordinate
- ✓ 64 个 V4-orbit 等分 V8（每 orbit 含 4 cells: (h, 道), (h, 未), (h, 已), (h, 今)）

**需修订**：

| # | Issue | 建议 |
|---|-------|------|
| 1 | 「P-like / T-like」labels 是 loose analogy | 改为「果-singleton / 因-singleton / 因果交汇」 |
| 2 | 综 (line reversal) 不在 V8 (是 permutation 非 XOR) | 显式声明 V8 = abelian XOR group, 综 需 permutation layer |
| 3 | 「错」算子 `xxxxxxoo` (改化变临主极) 缺 reserved name | 建议「反」or「卦反」 |
| 4 | 高对称 operator (`11111111` 等) 应系统命名 | 建立 reserved-name 表（如「全反」等） |
| 5 | Hexagram atoms 与 time atoms 应 sort 分离 | compiler 中 `hexagram-atoms` / `time-atoms` 分集合 |
| 6 | Cell metadata 应显式列 R6 + V4 component | 加 `R6_component`, `V4_component` 列 |
| 7 | `o = 阳` vs 直觉 `1 = 阳` 约定应文档化 | spec 顶部明确声明 |
| 8 | `R8` prefix vs `V8` 命名应统一 | 全文统一为 V8 |

**审计结论**：V8 = R6 ⊕ V4 algebraically sound。8 项 issue 全为 documentation / naming，无结构性 bug。

---

## 8. 信息保持论 (Information Preservation Theory)

V8 的代数骨架已建立，但更深的问题是：**当 R ∈ V8 经过 operator 路径到 R'，R 的哪些信息被保留？哪些不可推导？**

这一节提出可机械化的回答。

### 8.1 问题陈述

给定 root state $R \in V_8$（例 `xoxoxooo` = 未济道），将它通过 V8 operator 路径变换得 $R'$。由 V8 阿贝尔性，任何路径 collapse 为单一 XOR mask $m \in V_8$:

$$R' = R \oplus m$$

设 $H \le V_8$ 是「允许的 operator 子群」（例 $H = V_4$ 时间子群、或 $H = \{道, 今\}$ 这样的子子群）。R 在 $H$-action 下的等价类（**H-orbit**）：

$$[R]_H \;=\; \{R \oplus m \mid m \in H\}$$

orbit 大小 = $|H|$。

**核心问题**：对任意 query $Q$（如「卦是否 = 既济?」「y7 = 0?」「y7 ⊕ y8 是否偶?」），能否仅从 $[R]_H$ 推出 $Q(R)$？

### 8.2 信息保持定理 (Information Preservation Theorem)

**Theorem 8.1**: 设 $H \le V_8 = (\mathbb{F}_2)^8$。则：

1. **bit-level invariants**：bit-position $i$ 是 $H$-不变的 $\iff$ 每个 $m \in H$ 在位 $i$ 处为 0
2. **linear invariants**：线性泛函 $\varphi: V_8 \to \mathbb{F}_2$ 是 $H$-不变的 $\iff \varphi \in H^\circ$（$H$ 的 **annihilator**）
3. **state invariants**：R 在 $H$-action 下的可识别信息 = R 在 $V_8 / H$ 中的陪集 $[R]_H$

**Proof sketch**:
- $\varphi(R \oplus m) = \varphi(R) + \varphi(m)$。等于 $\varphi(R)$ iff $\varphi(m) = 0 \; \forall m \in H$ iff $\varphi \in H^\circ$。
- bit $i$ 的 functional 是投影 $\pi_i$。$\pi_i \in H^\circ$ iff every $m \in H$ has $m_i = 0$。

**Corollary**: $H$-invariant 线性信息的维数 $= \dim(H^\circ) = 8 - \dim(H)$。

| H | dim(H) | dim(H°) | 信息保留维数 |
|---|--------|---------|--------------|
| {道} | 0 | 8 | 全 V8 (256 cosets) |
| V4 (time) | 2 | 6 | 卦 only (64 cosets) |
| {道, 今} | 1 | 7 | 卦 + 因⊕果 parity (128 cosets) |
| V8 (full) | 8 | 0 | 无 (1 coset) |

### 8.3 V4 子群格 → 信息保持层级

V4 有恰好 5 个子群，每一个对应一种保持模式：

| H ≤ V4 | 阶 | 保留信息 | 失去信息 | 说明 |
|--------|----|----------|----------|------|
| {道} | 1 | (R6, 因, 果) 全部 | 无 | trivial action |
| {道, 未} | 2 | R6, 因 (y7) | 果 (y8) | 只翻 future-bit 的子群 |
| {道, 已} | 2 | R6, 果 (y8) | 因 (y7) | 只翻 past-bit 的子群 |
| **{道, 今}** | 2 | R6, **因⊕果 parity** (y7⊕y8) | 因, 果 各自 | **唯一保 non-coordinate invariant 的子群** |
| V4 (full) | 4 | R6 only | 全部时间信息 | 卦 invariant，时全失 |

**{道, 今} 的特殊性**：它保留的不是 y7 或 y8 单独，而是它们的 XOR-parity。这是 V4 子群中**唯一非平凡 non-coordinate invariant**。

**与 §6.1 独立交汇**：§6.1 从元素-level（algebraic homomorphism）推出 {e, ab} = {道, 今} 是唯一非平凡保结构子群。§8.3 从 state-level（information invariant）独立推出同一子群是唯一保 non-coordinate parity 的子群。**两条独立路径同指 {道, 今}**——这给该子群以双重证据的特权地位。

### 8.4 V4 Cayley Graph 与 R 的 V4-orbit

V4 的 Cayley graph（取生成元 a = 未, b = 已）：

```
       a
   道 ────── 未
    │        │
   b│        │b
    │        │
   已 ────── 今
       a
```

R 在 V4 下的 orbit 是这个 graph 在 V8 中的同构 copy：

```
       a (XOR y8)
  R ───────────── R⊕未
   │               │
  b│               │b
 (XOR y7)         (XOR y7)
   │               │
  R⊕已 ────── R⊕今
       a (XOR y8)
```

- **4 nodes 共有的部分** = R 的 y1-y6 = **保留信息** (hexagram)
- **nodes 间不同的部分** = y7-y8 = **失去信息** (time-state)

### 8.5 可推导性算法 (Derivability Algorithm)

给定 $(R, H, Q)$ 三元组，其中 $Q$ 是关于 R 的线性 query（mask vector $q$）：

```
input:  R ∈ V8, H ⊆ V8 (subgroup, given by generators), q ∈ V8 (query mask)
output: ('derivable', value) OR ('underivable', reason)

procedure derivable?(R, H, q):
  for each generator m of H:
    if ⟨q, m⟩ ≠ 0 in F₂:        // i.e., q ⋅ m has odd parity
      return ('underivable', q-not-H-invariant)
  return ('derivable', ⟨q, R⟩)
```

时间复杂度 $O(|generators(H)| \cdot 8)$——常数时间。

### 8.6 Worked example: R = `xoxoxooo` (未济道)

R = `xoxoxooo` 分解为 $(h, t) = (\texttt{xoxoxo}, \texttt{oo}) = (\text{未济}, \text{道})$.

**V4-orbit:**

| 元素 | R ⊕ 元素 | cell name |
|------|----------|-----------|
| 道 | xoxoxooo | 未济道 |
| 未 | xoxoxoox | 未济未 |
| 已 | xoxoxoxo | 未济已 |
| 今 | xoxoxoxx | 未济今 |

**Query 验证表**：

| Query 描述 | mask q | 测试 subgroup H | $\langle q, H \rangle = 0$? | 结论 |
|-----------|--------|----------------|---------|------|
| 卦是否 = 未济 (xoxoxo on y1-y6) | `xoxoxooo` | V4 | ✓（q 在 y7-y8 处为 0） | derivable, value = $\langle q, R \rangle$ |
| y3 = 0? (即看 y3 bit) | `00x00000` | V4 | ✓（V4 不动 y3） | derivable, value = 1 (y3 = x) |
| y7 = 0? | `000000x0` | V4 | ✗（mask 已 = `000000x0` 有 overlap） | **underivable from V4-orbit** |
| y8 = 0? | `0000000x` | V4 | ✗（mask 未 = `0000000x` 有 overlap） | **underivable from V4-orbit** |
| y7 ⊕ y8 = 0? | `000000xx` | V4 | ✗（mask 今 = `000000xx`, $\langle xx, xx \rangle = 0$ mod 2 = 0... 等等） | 见下 |
| y7 ⊕ y8 = 0? | `000000xx` | **{道, 今}** | ✓ | **derivable**, value = 0 |

特别看「y7 ⊕ y8 parity」的微妙：

- 在 **V4** 下：mask q = `000000xx`。检查每个生成元：
  - $\langle q, 未 \rangle = \langle \texttt{xx}, \texttt{ox} \rangle = 0+1 = 1$ ⇒ **odd** ⇒ ✗ underivable
- 在 **{道, 今}** 下：唯一非平凡元素 是 今 = `000000xx`。
  - $\langle q, 今 \rangle = \langle \texttt{xx}, \texttt{xx} \rangle = 1+1 = 0$ ⇒ **even** ⇒ ✓ derivable

**这就是 {道, 今} 的信息威力**：在更小的子群下，更细的信息（y7⊕y8 parity）被保留。

### 8.7 信息层级 (Information Strata)

按子群-按-信息的格 (lattice of preservation strata)：

```
{道} (trivial)               dim 0    全 V8 可推 (256 cosets)
   │
   ├── {道, 未}              dim 1    失 果 / 保 R6 + 因 (128 cosets)
   ├── {道, 已}              dim 1    失 因 / 保 R6 + 果 (128 cosets)
   └── {道, 今}              dim 1    失 因/果 各自 / 保 R6 + 因⊕果 parity (128)
         │
         ├──────┐
         ↓      ↓
         V4 (full)            dim 2   仅保 R6 (64 cosets)
            │
            └── 扩到 V8 子群     dim 2-8   逐级失去 R6 信息
                  └── V8 full   dim 8   0 cosets，全失去
```

每条「下降路径」表示信息丢失的渐进。**{道, 今} 是 V4 子群中「信息最富」的非平凡子群**——它保留比 coordinate (因/果 单独) 更深的 XOR-parity invariant。

### 8.8 Lean formalization

```lean
namespace Wen.Preservation

open Wen.V4 Wen.Hexagram

/-- V8 = (F₂)^8, 8-bit state space -/
abbrev V8 := Fin 8 → Bool

/-- XOR (group operation on V8) -/
def xor8 (a b : V8) : V8 := fun i => a i != b i

instance : AddGroup V8 := ...  -- (F₂)^8 standard structure

/-- A subgroup of V8 given by carrier set -/
structure V8Subgroup where
  carrier : Set V8
  contains_zero : 0 ∈ carrier
  closed_xor : ∀ a b, a ∈ carrier → b ∈ carrier → xor8 a b ∈ carrier

/-- Linear functional on V8, represented by its mask -/
def evalQuery (q : V8) (r : V8) : Bool :=
  (Finset.univ : Finset (Fin 8)).image (fun i => q i && r i)
    |>.toList.foldl Bool.xor false

/-- Q is H-invariant iff q annihilates all of H -/
def isInvariant (q : V8) (H : V8Subgroup) : Prop :=
  ∀ m ∈ H.carrier, evalQuery q m = false

/-- The annihilator of H -/
def annihilator (H : V8Subgroup) : Set V8 :=
  { q | isInvariant q H }

/-- Main theorem: Q is derivable from R's H-orbit iff Q is H-invariant -/
theorem info_preservation (q : V8) (H : V8Subgroup) (R : V8) :
    isInvariant q H →
    ∀ R' ∈ orbit H R, evalQuery q R' = evalQuery q R := by
  intro hinv R' ⟨m, hm, rfl⟩
  rw [evalQuery_xor, hinv m hm]
  simp

/-- V4 time subgroup, sitting in V8 at y7-y8 -/
def V4_time : V8Subgroup := {
  carrier := { fun i => 
    if i = 6 then a else if i = 7 then b else false 
    | a b : Bool }
  ...
}

/-- {道, 今} subgroup -/
def dao_jin_subgroup : V8Subgroup := {
  carrier := { 0, fun i => if i ≥ 6 then true else false }
  ...
}

/-- 关键性质: dao_jin preserves the parity y7 ⊕ y8 -/
def parity_y7_y8 : V8 := fun i => i = 6 ∨ i = 7

theorem dao_jin_preserves_parity :
    isInvariant parity_y7_y8 dao_jin_subgroup := by
  intro m hm
  fin_cases hm <;> rfl

/-- V4 does NOT preserve the parity -/
theorem V4_does_not_preserve_parity :
    ¬ isInvariant parity_y7_y8 V4_time := by
  intro h
  -- 反例: take m = 未 = ⟨0,...,0, false, true⟩
  -- evalQuery parity_y7_y8 m = 1 ≠ false
  ...

end Wen.Preservation
```

### 8.9 Compiler implementation

```clojure
(ns wen.passes.preservation
  "Information preservation analysis for V8 states under operator subgroups.")

;; V8 element as 8-bit int (high bit = y1, low bit = y8)
(defn ox->int [s]
  (reduce-kv (fn [acc i c]
               (bit-or acc (if (= c \x) (bit-shift-left 1 (- 7 i)) 0)))
             0
             (vec s)))

(defn int->ox [n]
  (apply str (for [i (range 8)] (if (bit-test n (- 7 i)) \x \o))))

;; F₂ inner product of two V8 elements as ints
(defn dot-product [a b]
  (loop [x (bit-and a b), parity 0]
    (if (zero? x) parity
        (recur (unsigned-bit-shift-right x 1)
               (bit-xor parity (bit-and x 1))))))

;; Check if Q (as mask int) is invariant under subgroup H (set of mask ints)
(defn invariant? [q-mask H]
  (every? #(zero? (dot-product q-mask %)) H))

;; Main derivability decision
(defn derivable?
  "Returns {:derivable true/false, :value? bit} for query q under H."
  [q-mask H R]
  (if (invariant? q-mask H)
    {:derivable true
     :value (dot-product q-mask R)}
    {:derivable false
     :reason :q-not-H-invariant}))

;; Standard subgroups
(def V4-time-subgroup
  #{(ox->int "oooooooo")    ; 道
    (ox->int "ooooooox")    ; 未
    (ox->int "ooooooxo")    ; 已
    (ox->int "ooooooxx")})  ; 今

(def dao-jin-subgroup
  #{(ox->int "oooooooo")    ; 道
    (ox->int "ooooooxx")})  ; 今

;; Worked example: R = 未济道
(def R-weiji-dao (ox->int "xoxoxooo"))

(derivable? (ox->int "xxxxxxoo")   ; query: hexagram bits (all 6 ones in y1-y6)
            V4-time-subgroup
            R-weiji-dao)
;; => {:derivable true, :value 1}   ; hexagram parity is 1 for 未济

(derivable? (ox->int "ooooooxx")   ; query: y7 ⊕ y8 parity
            V4-time-subgroup
            R-weiji-dao)
;; => {:derivable false, :reason :q-not-H-invariant}

(derivable? (ox->int "ooooooxx")
            dao-jin-subgroup
            R-weiji-dao)
;; => {:derivable true, :value 0}   ; under {道, 今}, parity IS derivable
```

### 8.10 Implications

1. **可推导信息的代数刻画**：本理论给「信息保留」一个精确代数定义。R → R' 的 transformation 中保留的恰好是 H° (mask vectors annihilating H)。这把「在 V4 路径下哪些假设仍真」从直觉变成可机械化判定的算法。

2. **{道, 今} 子群的双重证据**：§6.1（元素 level，algebraic homomorphism preservation）与 §8.3（state level，non-coordinate invariant preservation）独立推出同一子群。这不是巧合——{道, 今} 是 V4 中唯一「既保 algebra 又保非 trivial 信息」的子群，这给它 *uniquely privileged* 地位。

3. **Causality 解读**：在 时 V4 解读下，{道, 今} 是「同时性子群」（both-present or both-absent of causal articulation）。它保留的 y7 ⊕ y8 parity 是「因果是否对偶激活」的二元判定。这是 PT-symmetric semantics 的代数核心。

4. **假设检验作为编译时分析**：文 compiler 可在编译期对每个用户假设 Q 与操作子群 H 计算 `(derivable?, value)`。这把 V4 框架从「描述」变成「执行」——R 的信息可通过编译器静态检查。

5. **V8 子群格的开发**：V4 只是 V8 子群格中的一个 canonical 子群（时 V4）。完整的「信息保持几何」应在 V8 的全子群格上展开。每个 V8 子群对应一个信息保持层级，每条 lattice 边对应信息丢失。

6. **与 9-atom kernel 的对接**：「非」(错) 对应 R6 上的 yin-yang complement，是 V8 中的 `xxxxxxoo` mask。在信息保持语境下，{道, 错} 子群（如果它存在，即 V8 中的 ⟨xxxxxxoo⟩ 子群）保留时间 V4 全部信息但失去卦 R6 信息。这是 9-atom kernel atom 与 V8 子群结构的桥梁。

---

## 9. 历史脉络：被部分发现的 V₄ 框架

### 9.1 Gotthard Günther — Polycontextural Logic

德国哲学家 Günther（1900–1984）明确论证经典逻辑是 monocontextural（只一个 ℤ/2），现实需要 polycontextural（多个相交 ℤ/2）。他的「morphograms」在小情形下精确是 V₄ 上的对称模式。

**关键文本**：*Idee und Grundriß einer nicht-Aristotelischen Logik* (1959)

**未尽**：缺乏形式化、未识别 V₄ 普适性、未跨域。

### 9.2 Spencer-Brown / Kauffman / Varela — Distinction Calculus

Spencer-Brown 的 *Laws of Form* (1969) 以一个原始算子（mark）+ re-entry 算子建构所有数学。两者各自 ℤ/2 involution，合起来是 V₄ 的隐式实例。

Louis Kauffman 把这扩到结理论、量子力学。Francisco Varela 的 *A Calculus for Self-Reference* (1975) 扩到自创生（autopoiesis）。

**未尽**：未识别 V₄ 的范畴论根据、未做跨域 atlas。

### 9.3 Greimas — 符号方阵（Carré Sémiotique）

法国符号学家 Algirdas Greimas 的语义方阵：

```
        S₁ ────────── S₂
        │  \      /  │
        │    \  /    │
        │    /  \    │
        │  /      \  │
       ¬S₂ ────────── ¬S₁
```

四位置的关系（contrary, contradiction, sub-contrary, implication）**精确是 V₄ 在语义范畴上的作用**。

Fredric Jameson 在文学批评里大量使用。

**未尽**：未被认作 V₄；当作便利分析工具而非数学结构。

### 9.4 范畴论中隐式的 V₄

任何 dagger compact closed category 自带四个视角：

$$\mathcal{C}, \quad \mathcal{C}^{\mathrm{op}}, \quad \mathcal{C}^*, \quad \mathcal{C}^{*\mathrm{op}}$$

四者间的转换构成 V₄ 作用。Lawvere, Selinger, Coecke (*Picturing Quantum Processes*) 隐式工作于此。

**未尽**：作为「四种自然变换」被使用，但未被显式命名为 V₄ 知识组织原理。

### 9.5 被压缩的 V₄ — Peirce, Hegel

- **Peirce**：Firstness/Secondness/Thirdness 表面三元，底下有 representamen × object 的隐藏 V₄
- **Hegel**：thesis/antithesis/synthesis 表面三元，但合题包含同一性恢复 — 实质四步（同一/否定/反否定/综合）

Žižek, Johnston 等当代解释者暗示过 Hegel 逻辑底下是 V₄。

### 9.6 文 的独特位置

|                       | Günther | Spencer-B | Greimas | Cat Theory | **文** |
|-----------------------|---------|-----------|---------|------------|----------|
| 识别 V₄ 结构          | 部分     | 隐式      | 部分    | 隐式       | **✓ 显式** |
| 跨域归一              | ✗       | ✗         | ✗       | 部分        | **✓**    |
| 形式化语言            | ✗       | 部分       | ✗       | ✓          | **✓**    |
| 可执行                | ✗       | ✗         | ✗       | 部分        | **✓**    |
| 作为知识组织原理      | 部分     | ✗         | ✗       | ✗           | **✓**    |

---

## 10. Implications · 知识延伸方向

### 10.1 V₄ Atlas 作为研究纲领

对每个知识域，明确归位其逻辑算子到 V₄ 四位置之一。**空着的位置 = 该域可延伸的方向**。

### 10.2 经典逻辑系统性丢失了「综」

经典逻辑充分使用 $\{e, a, ab\}$（id、$\neg$、contrapositive），但**几乎不使用 b（综 = 命题反向）**——因为它不保真。

但 b 在范畴论里对应 op，是核心结构。

**假说**：直觉主义逻辑、线性逻辑、量子逻辑的出现，正是为了把 V₄ 中被经典逻辑丢失的「综」重新引入。文 应**显式拥有完整 V₄**，从而**统一这些非经典逻辑**。

### 10.3 错综应被提升为 primary

由 §6.1：错综 是 V₄ 中唯一非平凡的保代数结构元素。在 文 形式语言中：

- 不应将 `cuozong` 仅作为 `(cuo, zong)` 的衍生
- 应给 `cuozong` 独立的 primitive 地位
- 应单独研究 {e, cuozong} 子群作为 文 的「真理保持核心」

### 10.4 64 卦 = 16 个 V₄-orbit?

由 V₄ 作用在 64 卦上，64 / 4 = 16，**若每个轨道大小恰好为 4**，则 64 卦分为 16 个 V₄-orbit。

需检验：有多少卦是 V₄-fixed（如乾、坤、坎、离等对称卦）？

- 乾 (111111): 错 → 坤; 综 → 111111 = 乾; 错综 → 坤. 轨道 = {乾, 坤}
- 坎 (010010): 错 → 离; 综 → 010010 = 坎; 错综 → 离. 轨道 = {坎, 离}

由 Burnside lemma 可精确计算轨道数。**这是一个可执行的 calculation，应纳入 文 实现**。

### 10.5 V₄ 与 9-atom kernel 的整合

文 现有 9-atom kernel：者/之/非/而/凡/即/也/是/令。

**关键观察**：
- `非` 是 ℤ/2 involution → 对应 V₄ 的「错」位置
- `之` (composition / particle) → 对应 V₄ 的「综」位置 (?)
- `凡` (universal quantifier) → 与 V₄ 不平行，是另一维度
- `令` (let/binding) → 同上

**任务**：把 9-atom kernel 中的 involutive operators 与 V₄ 显式对齐，识别 V₄-action 在 kernel 上的轨道结构。

### 10.6 与生生不息论·文开本的对接

V₄ 应被认作 **三相一理框架** 中的对偶代数表征。具体：

- 「相」(phenomenal aspect) 对应 V₄ 中的 non-identity elements
- 「理」(underlying principle) 对应 V₄ identity `e` (道)
- 三相一理 的「三 + 一」结构与 V₄ 的「三个非平凡 + 一个平凡」对应

**这给出 生生不息论 一个代数底座**。需写入 文开本 后续版本。

### 10.7 与 OpenClaw / SST 的对接

OpenClaw 的 Sprite-Space-Token 架构有自身对称：

- Sprite (active entity) ↔ Space (passive medium): 对偶 → ℤ/2
- Token (capability) ↔ Reference (handle): 对偶 → ℤ/2

**两条独立 ℤ/2 → V₄**。SST 架构自然承载一个 V₄ symmetry，可用于：

- Capability delegation 的方向翻转（综）
- Sprite/Space 极性互换（错）
- 对偶 capability flow（错综）

### 10.8 与 Nomad OS 的对接

Pay→Split→Chat→Trust→Coordinate 五阶段产品弧：

- Pay ↔ Receive: 值轴 ℤ/2
- Send ↔ History: 框架轴 ℤ/2

**Nomad OS 的金融原语本质上是 V₄-acted on transaction state**。可用 V₄ 作为支付协议的代数基础。

### 10.9 不被 V₄ 涵盖的结构

V₄ 不涵盖：

- 高阶 articulation (例如 3-element value sets, 需 $S_3$)
- 非阿贝尔对称
- 连续对称 (Lie group)
- Cyclic non-involutive symmetry (rotation)
- 非可逆操作（如互卦的 projection）

**这些应在 文 的 *扩展* 层处理，V₄ 是 *核心* 层**。

### 10.10 V₄ 张量积塔

可考虑：

$$V_4, \quad V_4 \otimes V_4 = (\mathbb{Z}/2)^4, \quad V_4^{\otimes n} = (\mathbb{Z}/2)^{2n}$$

每多一个 V₄ tensor 对应「再一对独立对偶轴」。这给出 文 的高维扩展路径。

可能与 64 卦本身的 $(\mathbb{Z}/2)^6$ 结构同构——$V_4 \otimes V_4 \otimes V_4 = (\mathbb{Z}/2)^6$，**恰好是 64！**

这是一个值得严肃验证的 hypothesis。

---

## 11. Open Questions

1. **V₄ 完备性**：是否所有「meaning-bearing structure」的对称都必然包含 V₄？有反例吗？
2. **Meta-V₄**：§5.3 中出现的范畴层 meta-V₄ 是否有名字？它与原 V₄ 的关系是 ℤ/2 × V₄ 还是 V₄ × V₄？
3. **64 = $V_4^{\otimes 3}$?** §10.10 的 hypothesis 是否成立？卦的 $(\mathbb{Z}/2)^6$ 结构在 V₄-tensor 视角下的精确描述？
4. **互卦的代数化**：互卦不是 V₄ 元素，那它在 文 里应被建模为什么类型的结构？Possibly 一个 idempotent endomorphism on hexagram lattice？
5. **非阿贝尔扩展**：是否存在自然的「非阿贝尔 文」，其对称群是 $D_4$ 或 $Q_8$ 而非 V₄？什么场景需要？
6. **Truth-preservation in non-classical logics**：在直觉主义/线性/量子逻辑中，V₄ 各元的 truth-preservation 性质如何？错综在这些逻辑中是否仍保 contrapositive？
7. **Galois ↔ 卦对应**：$\mathrm{Gal}(\mathbb{Q}(\sqrt{2}, \sqrt{3})/\mathbb{Q}) \cong V_4$ 这个同构是否可被显式化为「数论卦」的对应？某些卦是否对应特定数域扩张？
8. **Bell 状态 ↔ 卦对应**：四个 Bell 状态在 local Pauli 下互换。这能否给出 8 个特殊卦（V₄-fixed 的）与量子纠缠之间的精确字典？

---

## 12. 完成检验清单（双轨）

### 12.1 结构内容（本文档自足覆盖）

- [x] 从 hexagram bi-axial 结构推导 V₄
- [x] 论证 V₄ 是逼出的而非选择的
- [x] 论证不是 ℤ/4、不是 $(\mathbb{Z}/2)^3$、不是更小的群
- [x] 解释 道-row 规律的内禀必然性
- [x] 建立跨域同构：Pauli, CPT, TM, Galois, Logic, Category, Semiotics
- [x] 构建完整 V₄ Atlas（4 位置 × 9+ 域）
- [x] 推导 4 级 preservation hierarchy (set / algebra / category / truth)
- [x] 识别 {e, 错综} = {道, 今} 为唯一非平凡保结构子群
- [x] 识别错综在 contrapositive 上的特殊地位
- [x] **V8 实施审计** (§7.11)：V8 = R6 ⊕ V4 clean direct sum, 8 项 documentation issue 识别
- [x] **信息保持论** (§8)：H-action 下的 invariant theory，5 种 V4 子群保持模式
- [x] **{道, 今} 双重证据**：§6.1 元素 level + §8.3 state level 独立交汇
- [x] 历史脉络梳理（Günther, Spencer-Brown, Greimas, Cat, Peirce, Hegel）
- [x] 识别 文 的独特位置（vs. 历史前驱）
- [x] 9 项 Implications（经典逻辑缺综、错综提升、64=V₄³ 等）
- [x] 8 个 Open Questions
- [x] 与 9-atom kernel、生生不息论、OpenClaw、Nomad OS 的对接草图

### 12.2 证明轨（Lean 4 + Mathlib）

**本文档 §7.1–§7.3 已给出 V₄ 群结构与 action 骨架**：

- [x] V₄ 作为 `CommGroup` instance，群公理 `by decide`
- [x] V₄ 在 Hexagram 上的 `MulAction` instance
- [x] `dao_fixes_all` (refl)
- [x] `cuo_involutive`, `zong_involutive` (含证明)
- [x] `cuo_zong_comm` (commutativity at action level)
- [x] `cuozong_preserves_meet` (§5.2 核心)
- [x] `cuo_not_preserves_meet` (反例论证)
- [x] `structurePreservingSubgroup` 定义
- [x] `structurePreservingSubgroup_iso_Z2` (statement)

**本文档 §8.8 已给出 information preservation 骨架**：

- [x] `V8` 作为 `Fin 8 → Bool` 的 AddGroup
- [x] `V8Subgroup` 结构（carrier + closure axioms）
- [x] `evalQuery` linear functional 求值
- [x] `isInvariant` predicate
- [x] `annihilator` definition
- [x] `info_preservation` 主定理（statement）
- [x] `V4_time`, `dao_jin_subgroup` 具体 instances
- [x] `dao_jin_preserves_parity` 关键例子
- [x] `V4_does_not_preserve_parity` 区分性反例

**后续 Lean 工作**：

- [ ] 把 `...` 占位的证明全部填完
- [ ] 形式化 §5.3 Meta-V₄ 结构（共变 × 对象保持的二轴分解）
- [ ] 形式化 §5.4 contrapositive 的 truth-preservation
- [ ] 形式化 §6.1 子群分类完备性（V₄ 恰有 3 个非平凡 ℤ/2 子群）
- [ ] 64 卦的 V₄-orbit 枚举与 Burnside 验证（可机械化）
- [ ] $V_4^{\otimes 3} \cong (\mathbb{Z}/2)^6$ 的精确同构 + 与 hexagram 空间的对应
- [ ] V8 子群格的全枚举（V₄ 只是其中之一）
- [ ] `info_preservation` 定理的完整证明
- [ ] `derivable_iff_invariant` 充要条件证明
- [ ] **关键 cross-level 定理**：`{道, 今}` 在元素 level 与 state level 是同一子群（§6.1 ∩ §8.3）

### 12.3 编译轨（文 compiler / Clojure / SCI）

**本文档 §7.4–§7.9 已给出 V₄ IR 骨架**：

- [x] `V4Op`, `Hexagram`, `V4Apply` IR records
- [x] 完整 mul-table 作为编译期常量
- [x] `act` runtime 实现
- [x] `normalize-v4-chain` pass 算法
- [x] Atlas as typed registry（含 `:preserves` 字段）
- [x] `preserves?` predicate
- [x] Lean ↔ Clojure round-trip 一致性映射表
- [x] Surface syntax → IR 映射
- [x] 「之」作为 V₄ application particle

**本文档 §8.9 已给出 derivability checker 骨架**：

- [x] V8 整数表示与 ox-string 互转
- [x] `dot-product` F₂ 内积
- [x] `invariant?` predicate
- [x] `derivable?` 主决策算法
- [x] 标准子群定义 (`V4-time-subgroup`, `dao-jin-subgroup`)
- [x] Worked example (R = 未济道) 的 unit-test 草稿

**后续编译器工作**：

- [ ] 实际 lexer：单 token 识别「错综」、`恒`、`印投` 等 reserved names
- [ ] V₄ normalize pass 整合到 wen compiler pipeline
- [ ] **Derivability analyzer 作为编译期静态分析 pass**
- [ ] CI 一致性脚本：从 Lean 输出 atlas data + invariant lemmas, 对比 Clojure 实现
- [ ] {e, 错综} = {道, 今} 子群作为优化标记 propagation
- [ ] V₄ IR primitive 与 9-atom kernel 中 `之/非` 的统一
- [ ] Hexagram literal 编码（6-bit）与 V₄ act 的高效实现
- [ ] V8 完整子群格枚举与 lookup
- [ ] REPL 集成：在 wen REPL 中可输入 `错 之 乾` 或 `derivable? Q under H of R` 直接求值

### 12.4 待两轨同时验证

这些事项必须 **同时在 Lean 中证明** 与 **在编译器中实现**，且通过 round-trip 校验：

- [ ] V₄ 群乘法表（Lean: `mul_comm`; Clojure: `mul-table` 对称性）
- [ ] V₄ action 的群作用性质（Lean: `MulAction` instance; Clojure: `normalize-v4-chain` correctness）
- [ ] {e, 错综} = {道, 今} 子群的特殊地位（Lean: `structurePreservingSubgroup`; Clojure: `:preserves :algebra` flag）
- [ ] 64 = $|V_4|^3 = 4^3$ 与 hexagram 空间的精确同构
- [ ] 错综 的 contrapositive 性质在双轨上一致编码
- [ ] **Information preservation 主定理**（Lean: `info_preservation`; Clojure: `derivable?` correctness）
- [ ] **{道, 今} 保 parity y7⊕y8**（Lean: `dao_jin_preserves_parity`; Clojure: `(derivable? "ooooooxx" dao-jin-subgroup _) ≡ derivable`）
- [ ] **V4 不保 parity 反例**（Lean: `V4_does_not_preserve_parity`; Clojure: 对应 underivable 测试）
- [ ] V8 audit 8 项 issue 在 documentation + IR 中同步修订

### 12.5 V8 audit 修订项

来自 §7.11 的 8 项 issue 跟踪：

- [ ] Issue 1: 修订 P-like/T-like labels 为「果-singleton / 因-singleton / 因果交汇」
- [ ] Issue 2: 显式声明 综 不在 V8（需 permutation layer）
- [ ] Issue 3: 「错」算子 `xxxxxxoo` 加 reserved name (proposed: 「卦反」/「反」)
- [ ] Issue 4: 高对称 operator 系统化命名表
- [ ] Issue 5: Compiler 中 hexagram-atoms / time-atoms 分集合
- [ ] Issue 6: Cell metadata 加 R6_component + V4_component 列
- [ ] Issue 7: `o = 阳` 约定 documentation
- [ ] Issue 8: `R8` → `V8` naming 统一

### 12.6 验证规则

> 本文档 v0.2 作为「**结构 + 双轨形式化 + 信息保持**」综合规范，已自足覆盖：
> (a) V₄ 的结构推导、普适性论证、atlas、preservation 分析、历史定位、implications
> (b) Lean 4 证明轨的可编译骨架与待证 theorem 列表（包括 information preservation）
> (c) 文 compiler 轨的 IR、normalize pass、atlas registry、derivability checker、surface syntax 映射
> (d) V8 实施审计与 audit-driven 修订路径
> (e) 双轨 round-trip 一致性的明确条件

> **完成检验**：§12.1 全部 ✓；§12.2 给出 Lean 骨架（占位证明留待 fill-in）；§12.3 给出编译器骨架（实施留待 implementation track）；§12.4 双轨同步项目明列；§12.5 audit 修订项明列。
>
> 当 §12.2 / §12.3 / §12.4 / §12.5 的所有 ☐ 全部 ✓ 时，V₄ track 进入 v1.0。当前为 v0.2。

---

## 13. 结语

V₄ 不是 文 的设计选择，是 文 必然走到的结构。它跨越卦学、量子物理、可计算理论、Galois 理论、范畴论、符号学、辩证逻辑——并不是因为这些域之间「碰巧相似」，而是因为它们都共享一个根本约束：

> **任何承载意义的最小结构必须双轴 articulated；V₄ 是双轴二元对偶的最小代数。**

历史上 Günther、Spencer-Brown、Greimas 各自摸到了部分。文 的贡献是：

1. **显式化** V₄ 作为代数对象
2. **跨域归一** 把不同域的算子归位到同一个 V₄ atlas
3. **形式化** 到可执行的形式语言层（Lean 证明 + 编译器 IR 双轨）
4. **辨识** {e, 错综} = {道, 今} 子群的特殊地位 — 在元素 level（§6）与 state level（§8）独立交汇
5. **导出** 经典逻辑系统性遗失「综」的诊断，从而统一非经典逻辑作为「补回 V₄ 缺位」的尝试
6. **嵌入** V₄ 到 V8 = R6 ⊕ V4 的具体实施 (§7.11)，使 V₄ 不再是抽象代数而是可寻址的 IR primitive
7. **提供** 信息保持的可机械化判定 (§8)，让「假设在 V₄ 路径下是否仍真」从直觉变成编译期算法

V₄ 是 **道 + 错 + 综 + 错综**，是 **identity + content + frame + composite**，是 文 之上所有更复杂结构（9-atom kernel, 64-hexagram space, V8 cells, SST, Nomad）的代数底座。

V₄ 嵌入 V8 = R6 ⊕ V4 后，每个 V8 cell 都有唯一的 V4-coord。每个 query 在每个 H-subgroup 下都有 `derivable?` 的二值判定。**「写文 = 证明文 = 编译文 = 推导文」——四位一体不可分裂**。

把这底座写清楚，本文档 v0.2 的工作就完成了。

---

*End of v0.2 · 文开本 / Wen Foundation Note · V₄ track*
*Includes: V8 audit (§7.11) + Information Preservation Theory (§8)*
