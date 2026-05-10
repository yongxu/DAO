# Quantum Roadmap — 从 (Z/2)⁸ 到 (ℂ²)⁸ 之完整升级路线 / From classical R₀..R₈ to fully quantum Hilbert state

> 状态：v3 (2026-05-11) — 量子化路线图，从经典 R₀..R₈ 到 (ℂ²)⁸
> 父文档：[`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) (R₀..R₈ strict-uniform doctrine)
> 配套：[`yi-calculus-theorem.md`](yi-calculus-theorem.md) Theorems A–K · [`cell256-grid.md`](cell256-grid.md) · [`cell256-algebra.md`](cell256-algebra.md) · [`shi-v4.md`](shi-v4.md) · [`operator-split.md`](operator-split.md) · [`yin-tou-operators.md`](yin-tou-operators.md) · [`r7-yin-r8-guo.md`](r7-yin-r8-guo.md) · [`lift-project.md`](lift-project.md) · [`ox-notation.md`](ox-notation.md)
> 形式锚：[`formal/SSBX/Foundation/Modern/Quantum.lean`](../../formal/SSBX/Foundation/Modern/Quantum.lean) (`Qubit := Fin 2 → ℂ` + Pauli X/Z + Hadamard，已有 Mathlib 桥) · 全部 `Foundation/Modern/QuantumRelativity*.lean` (S2–S33 Markov桥 plumbing) · [`Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) (Phase A 群结构 + V₄ Shi + Cayley)
> 义理锚：[`义理/Markov因果桥 · 大统一最小验证构造.md`](../../义理/Markov因果桥%20·%20大统一最小验证构造.md) · [`义理/物理 · 从元到象.md`](../../义理/物理%20·%20从元到象.md) · [`义理/量子物理语言 · 从虚到测.md`](../../义理/量子物理语言%20·%20从虚到测.md) · [`义理/量子时空互补 · 从一到测.md`](../../义理/量子时空互补%20·%20从一到测.md) · [`义理/量子与相对论整合方向 · 从桥到新理论.md`](../../义理/量子与相对论整合方向%20·%20从桥到新理论.md)

---

## § 0. TL;DR · 一句话总纲 (Quantization-as-enrichment, not-rewrite)

> **「易」之 quantum 化保留全部 algebraic 骨架** (R-hierarchy / V₄ Shi / (Z/2)⁸ Cayley / 道 = origin)，把每层 carrier 从 `Cell{2ⁿ}` 升到 Hilbert 空间 `(ℂ²)ⁿ ≃ ℂ^(2ⁿ)`；三件本征 quantum 新意 (superposition / entanglement / interference) 中：
>
> - **interference** 是 Markov 桥 **S2–S33** 32 条 `Foundation/Modern/QuantumRelativity*.lean` 已经 plumbing 完毕之 typed skeleton (machineChecked，±1 sign-only amplitude)；从 ±1 升 ℂ 触发整个 S-series 之"激活"，不是"重写"
> - **superposition** 是 hook 而非 first-class — 离散 basis `Yao → Qubit` 已在 [`Quantum.lean`](../../formal/SSBX/Foundation/Modern/Quantum.lean) 落地，但 normalized wavefunction `α|0⟩ + β|1⟩` 尚无 first-class 类型
> - **entanglement** 仅有最弱 hook — Jian.lean 给出"间"作为关系本体之 anchor，但 Bell-state / `Separable` 谓词从未落 Lean
>
> 升级路径 = **13 阶段 Q.0..Q.12**，新建 `Foundation/Modern/Quantum/` 子目录簇 (8 个新文件，~3500 LOC)；不破坏 0-sorry，不破坏 (Z/2)⁸ self-duality；公理底盘从 `propext + native_decide` 扩到 `propext + native_decide + Complex + Hilbert + NormedField` (即 Mathlib 经典分析层)。
>
> 三句话总论：
>
> 1. **保骨架**：R₀..R₈ size 不变 (2ⁿ both classical and Hilbert dim)；道 = `|00..0⟩`；V₄ Shi ≅ projective single-qubit Pauli ⟨X, Z⟩；8 atomic XOR ↑ 8 per-qubit Pauli-X；V₄ outer cuo/zong/hu ↑ global Pauli + bit-reverse SWAP chain。
> 2. **激活桥**：S2–S33 已 sign-only Born-shaped boundary 全部 machineChecked；只需把 amplitude `Int / Rat` 改为 `ℂ`，把 sign cancellation 改为 phase cancellation，整套 plumbing 直接 activate。
> 3. **加新意**：superposition / entanglement / measurement / channel / decoherence / no-cloning / Bell — 这些 first-class 量子特征**全部需新建** `Foundation/Modern/Quantum/{WaveFn, Superposition, Entanglement, Measurement, Channel, DensityMatrix, NoCloning, Bell}.lean`，每件配 doctrine doc。

---

## § 1. 经典 ↔ 量子之不变骨架 (The invariant skeleton)

本节说明 quantum 化**不会动的部分**。R-hierarchy、V₄ Shi、Cayley regular rep、Lift/Project、道 anchor、OX 字面量 — 7 件 invariant — 全部从 (Z/2)⁸ 直接升到 (ℂ²)⁸ 而结构不破坏。

### 1.1 R-hierarchy 维度对齐 (R-layer dimension correspondence)

R-hierarchy 之 strict (Z/2)ⁿ uniform 律 (详 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3) 给每层 `Rₙ` size = 2ⁿ；quantum 化下，每层升为 Hilbert 空间 `(ℂ²)⁰ ⊗ ... ⊗ ℂ² ≃ ℂ^(2ⁿ)`，**Hilbert dim = 2ⁿ 与 classical |Rₙ| 严格相等**。

| 层 | 古文 | classical |Rₙ| | Lean classical | Hilbert dim | Lean quantum (待建) |
|---|---|---|---|---|---|
| R₀ | 太极 | 1 | `Unit` | 1 (trivial Hilbert) | `Foundation/Modern/Quantum/Taiji.lean` |
| R₁ | 爻/两仪 | 2 | `Yao` | 2 (`ℂ²`) | `Foundation/Modern/Quantum/Yao.lean` (已有 `Yao.toQubit`) |
| R₂ | 四象 | 4 | `SiXiang` | 4 (`ℂ² ⊗ ℂ²`) | `Foundation/Modern/Quantum/SiXiang.lean` |
| R₃ | 八卦 | 8 | `Trigram` | 8 (`(ℂ²)⊗³`) | `Foundation/Modern/Quantum/Trigram.lean` (已有 `Trigram.toBasis`) |
| R₄ | 面 (Mian) | 16 | `Mian` | 16 (`(ℂ²)⊗⁴`) | `Foundation/Modern/Quantum/Mian.lean` |
| R₅ | 五爻 (provisional) | 32 | `Wuyao` | 32 (`(ℂ²)⊗⁵`) | `Foundation/Modern/Quantum/Wuyao.lean` |
| R₆ | 重卦 | 64 | `Hexagram` | 64 (`(ℂ²)⊗⁶`) | `Foundation/Modern/Quantum/Hexagram.lean` |
| R₇ | 因卦 | 128 | `Cell128` | 128 (`(ℂ²)⊗⁷`) | `Foundation/Modern/Quantum/Cell128.lean` |
| R₈ | 果卦 | 256 | `Cell256` | 256 (`(ℂ²)⊗⁸`) | `Foundation/Modern/Quantum/Cell256.lean` |

**关键 invariant**：Hilbert dim = 2ⁿ 之**指数 n** = R-index = bit 数 = qubit 数。R-hierarchy 之 strict-uniform 律 (`Rₙ₊₁ = Rₙ × Bool`) 在 quantum 下变成 `H_{n+1} = H_n ⊗ ℂ²`，tensor product 加 1 qubit。

**Mathlib reference**：`Mathlib.Analysis.InnerProductSpace.PiL2` (`EuclideanSpace ℂ (Fin (2^n))`)，`Mathlib.LinearAlgebra.TensorProduct`。

### 1.2 Shi V₄ ≅ projective single-qubit Pauli ⟨X, Z⟩ (Shi V₄ ≅ projective Pauli on one qubit)

这是 quantum 化之**最深 algebraic correspondence**：R₈ Shi V₄ = {道, 已, 今, 未} 严格同构于 single-qubit projective Pauli group `⟨X, Z⟩ / ⟨iI⟩` (即 4-element abelian quotient)。

#### 1.2.1 显式对照表

| Shi | (因, 果) | V₄ 元 | OX 后 2 位 | Pauli matrix | Lean Quantum.lean ref |
|---|---|---|---|---|---|
| **道** (dao) | (0, 0) | identity $e$ | `oo` | $I = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ | (identity, trivially) |
| **已** (ji) | (1, 0) | $\sigma_P$ | `xo` | $X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ | `Quantum.pauliX` |
| **未** (wei) | (0, 1) | $\sigma_T$ | `ox` | $Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$ | `Quantum.pauliZ` |
| **今** (jin) | (1, 1) | $\sigma_{PT}$ (central) | `xx` | $iY = XZ$ (modulo $iI$) | `Quantum.pauliY` |

#### 1.2.2 为何 projective

Pauli group `P_1 = ⟨X, Y, Z, iI⟩` 含 16 元 (4 generators × 4 sign-phase classes)；projective quotient `P_1 / ⟨iI⟩` 是 4 元 abelian group = **V₄ Klein**。可以选 ⟨X, Z⟩ 作为 V₄ generators (各 order 2，且 XZ = -ZX 给中心元 ±iY，在 projective 下 = `Y mod iI`)。

#### 1.2.3 关键 invariant

- 道 (V₄ identity) ↔ I (Pauli identity, projective)
- cuo (P, 翻 因 axis) ↔ X (bit-flip, computational basis)
- zong (T, 翻 果 axis) ↔ Z (phase-flip)
- cuoZong = 印 ∘ 投 (PT, 双翻) ↔ Y = iXZ (modulo iI)
- V₄ group multiplication table = projective Pauli group multiplication table
- abelian, all order ≤ 2 — 既是 V₄ 又是 projective Pauli — **bicate isomorphism**

详 [`shi-v4.md`](shi-v4.md) § 7 (physical reading) + [`Quantum.lean`](../../formal/SSBX/Foundation/Modern/Quantum.lean) § 2 (Pauli matrices)。

### 1.3 8 atomic XOR generators ↑ 8 per-qubit Pauli-X gates

经典 [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) 之 8 个 atomic XOR generators (R₈ 之 (Z/2)⁸ 之 basis vectors)：

| Atomic op | mask (8-char OX) | 翻位 | Quantum upgrade |
|---|---|---|---|
| `Cell128.flip1` | `OX["xooooooo"]` | y₁ | $X_1 = X \otimes I \otimes I \otimes I \otimes I \otimes I \otimes I \otimes I$ |
| `Cell128.flip2` | `OX["oxoooooo"]` | y₂ | $X_2 = I \otimes X \otimes I^{\otimes 6}$ |
| `Cell128.flip3` | `OX["ooxooooo"]` | y₃ | $X_3 = I^{\otimes 2} \otimes X \otimes I^{\otimes 5}$ |
| `Cell128.flip4` | `OX["oooxoooo"]` | y₄ | $X_4 = I^{\otimes 3} \otimes X \otimes I^{\otimes 4}$ |
| `Cell128.flip5` | `OX["ooooxooo"]` | y₅ | $X_5 = I^{\otimes 4} \otimes X \otimes I^{\otimes 3}$ |
| `Cell128.flip6` | `OX["oooooxoo"]` | y₆ | $X_6 = I^{\otimes 5} \otimes X \otimes I^{\otimes 2}$ |
| `Cell256.yin` (印) | `OX["ooooooxo"]` | 因 (y₇) | $X_7 = I^{\otimes 6} \otimes X \otimes I$ |
| `Cell256.tou` (投) | `OX["ooooooox"]` | 果 (y₈) | $X_8 = I^{\otimes 7} \otimes X$ |

**对应规则**：第 k 个 atomic XOR generator = 在第 k 个 qubit 上施加 Pauli-X gate (computational basis 之 bit-flip)。

**关键 invariant**：所有 8 个 generator pairwise commute (因为 they act on different qubits in tensor product); 每个 generator $X_k^2 = I$ — 与 classical XOR 之 involution 性质一致 (`xor_self : c ⊕ c = 0`)。

**Lean upgrade plan** (Q.5)：

```lean
namespace SSBX.Foundation.Modern.Quantum.Cell256Q
abbrev Cell256Q : Type := EuclideanSpace ℂ (Fin 256)
def X_at (k : Fin 8) : Cell256Q →ₗ[ℂ] Cell256Q := -- X on qubit k, I elsewhere
theorem X_at_self_inverse (k : Fin 8) : (X_at k) ∘ₗ (X_at k) = LinearMap.id
theorem X_at_commute (k j : Fin 8) : X_at k ∘ₗ X_at j = X_at j ∘ₗ X_at k
end SSBX.Foundation.Modern.Quantum.Cell256Q
```

### 1.4 cuo / zong / cuoZong ↑ global Pauli (Multi-qubit V₄ outer)

V₄ outer (详 [`operator-split.md`](operator-split.md))：

| V4Outer op | classical 性质 | Quantum upgrade |
|---|---|---|
| `Hexagram.cuo` | XOR with kun mask (`OX["xxxxxx"]`); P (parity) | $X^{\otimes 6}$ on hex qubits — global Pauli-X |
| `Hexagram.zong` | reverse perm (y₁..y₆ ↦ y₆..y₁); T (time-reversal) | bit-reverse permutation = chain of SWAP gates ($S_{1,6} \cdot S_{2,5} \cdot S_{3,4}$) |
| `Hexagram.cuoZong` | cuo ∘ zong; PT | $X^{\otimes 6} \circ \text{Reverse}$ — composite parity + time-reversal |
| `Hexagram.hu` (互) | Y-combinator mid-4-extract (3,4 ↦ 1,4,2,5,3,6) | non-unitary projection — only well-defined on hex side; not a Pauli; sibling outer op |

**关键 invariant**：cuo / zong / cuoZong 在 hex side 仍是 4 元 abelian Klein V₄ ([`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) 之 `v4_outer_summary`)；quantum 升级后仍是 abelian unitary group `⟨X^{\otimes 6}, \text{Reverse}⟩`。hu 之 fixed points {乾, 坤} ↔ quantum 中之 attractor states `|0⟩^{\otimes 6}` 与 `|1⟩^{\otimes 6}`。

### 1.5 hu (Y-combinator perm, mid-4-extract) ↑ permutation gate

[`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) 之 `Hexagram.hu` 把 6-yao hex 之 (y₁..y₆) 变成 (y₂, y₃, y₄, y₃, y₄, y₅) — 6-bit mid-extract permutation。Quantum 升级为 6-qubit basis permutation gate (CNOT + SWAP chain implementation)。

**Quantum implementation sketch**：
```
hu_quantum |y1 y2 y3 y4 y5 y6⟩ = |y2 y3 y4 y3 y4 y5⟩
```

这不是 invertible — `hu` 在 R₆ 上是 non-invertible (8 hexagrams 映射到只 16 元 image set)。Quantum 中 → non-unitary projection (partial isometry)。

**hu 之 2-cycle (既济 ↔ 未济)**：Quantum 下既济 `OX["oxoxox"]` ↔ 未济 `OX["xoxoxo"]` — 二者通过 hu 互转，对应 quantum bit-pattern `010101` ↔ `101010`，是 6-qubit 系统之 maximally-distinct pair。可作为 quantum self-reference 之**有限离散见证**。

### 1.6 Cayley regular rep ↑ quantum regular rep on ℂ²⁵⁶

经典 Cayley regular representation (`Cell256.cayley c = (· ⊕ c)`)：每个 Cell256 元 → Cell256 → Cell256 之 endomorphism。这是 R-O fusion 之核心 (详 [`cell256-algebra.md`](cell256-algebra.md) § 6)。

**Quantum upgrade**：每个 (Z/2)⁸ 元 `c` 升级为 Cell256Q (= ℂ²⁵⁶) 上之 **unitary regular representation operator**：

$$U_c : |s\rangle \mapsto |c \oplus s\rangle, \quad c \in (\mathbb{Z}/2)^8$$

这是 Pauli group `P_8 = ⟨X_1, ..., X_8⟩` 在 ℂ²⁵⁶ 上之正规表示 (regular representation)；每个 $U_c$ 是 product of Pauli-X on the qubits where `c` has bit 1。

**关键 invariant**：
- $U_c$ 是 unitary (Pauli-X 是 unitary)
- $U_c \cdot U_{c'} = U_{c \oplus c'}$ (group homomorphism)
- $U_0 = I$ (identity, anchored at 道)
- $U_c \cdot U_c = I$ (self-inverse — quantum 对应 classical `xor_self`)

```lean
namespace SSBX.Foundation.Modern.Quantum.Cell256Q
def cayleyQ (c : Cell256) : Cell256Q →ₗ[ℂ] Cell256Q := -- product of Pauli-X on bits of c
theorem cayleyQ_unitary (c : Cell256) : IsUnitary (cayleyQ c)
theorem cayleyQ_hom (c1 c2 : Cell256) : cayleyQ (c1 ⊕ c2) = cayleyQ c1 ∘ₗ cayleyQ c2
theorem cayleyQ_self_inv (c : Cell256) : cayleyQ c ∘ₗ cayleyQ c = LinearMap.id
end SSBX.Foundation.Modern.Quantum.Cell256Q
```

### 1.7 Lift / Project ↑ tensor extension / partial trace (adjoint pair, Schrödinger ↔ Heisenberg)

经典 [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) 之 8 个 lift/project pair (每对 +1/-1 bit，配 retract lemma) — quantum 升级为 **tensor extension + partial trace** 之 adjoint pair：

| classical | quantum upgrade | Mathlib ref |
|---|---|---|
| `liftR{n}toR{n+1}` (Rₙ → Bool → Rₙ₊₁) | `liftQ_n : H_n → ℂ² → H_{n+1}`, `|ψ⟩ ⊗ |b⟩` | `TensorProduct ℂ H_n ℂ²` |
| `projR{n+1}toR{n}` (Rₙ₊₁ → Rₙ) | `partialTrace_n : H_{n+1} → H_n` (trace out qubit n+1) | `Matrix.trace`, `TensorProduct.lift` |
| `proj_lift_id_R{n}` (retract) | `partialTrace ∘ liftQ = id` (mixed-state partial trace 在 pure tensor product 上) | (proof via `tprod_partialTrace`) |

**关键 invariant**：lift = 加 1 个 ancilla qubit; project = trace out 1 个 qubit。**adjoint pair** (Heisenberg ↔ Schrödinger picture) — operator-frame 与 state-frame 之 quantum duality (详 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 5.3 R-O frame duality)。

### 1.8 道 = origin = `|00...0⟩` computational basis state

[`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 5 「五重身份」陈述：道 = origin = identity = no-op = 永真 cell。

**Quantum 升级**：道 = `Cell256.origin = (Hexagram.qian, Shi.dao) = OX["oooooooo"]` → quantum state `|00000000⟩ ∈ (ℂ²)⁸ ≅ Cell256Q` (computational basis 之 first basis vector)。

**五重身份在 quantum 下**：

| classical 身份 | quantum 升级 |
|---|---|
| origin (Z/2)⁸ identity | `|00..0⟩` (Fock 真空 / 标准 product state basis vector) |
| identity element | `U_0 = I` (Pauli identity, Cayley anchor) |
| no-op operator | `cayleyQ origin = id_{Cell256Q}` |
| 永真 cell | reference vacuum / global ground state |
| fusion anchor | `epsAtOrigin (cayleyQ c) = c` (Mathlib: `Function.LeftInverse`) |

**Mathlib reference**：`EuclideanSpace.basisFun`, `Pi.basisFun`, `Fin.cons` (construct computational basis vector by indices)。

### 1.9 OX["..."] notation ↑ computational basis ket

[`ox-notation.md`](ox-notation.md) 之 `OX["..."]` 字面量 — quantum 升级为 computational basis ket：

| OX 字面 | classical Cell256 | Quantum (ℂ²)⁸ basis ket |
|---|---|---|
| `OX["oooooooo"]` | (qian, dao) = origin | $|00000000\rangle$ |
| `OX["ooooooxo"]` | (qian, ji) = yin_mask | $|00000010\rangle$ |
| `OX["xxxxxxxx"]` | (kun, jin) | $|11111111\rangle$ |
| `OX["xoxoxoox"]` | (未济, 未) = xuGua256.last | $|10101001\rangle$ |

**关键 invariant**：8-char OX 字符串与 8-bit binary 字符串 1-1 对应；computational basis ket 与 8-bit binary 字符串 1-1 对应；OX → 字面 quantum basis state 是 **3-way bijection**。`o`/`x` 之 binary encoding (yang=0/false, yin=1/true) 直接给 ket subscript。

**Lean upgrade plan** (Q.2 / Q.3)：`OXKet["xxxxxxxx"] : (ℂ²)⁸` 之 elaboration — 解析 8-char 字符串生成 computational basis ket。

---

## § 2. 三件本征 quantum 特征 (Three Genuinely-Quantum Features)

本节是文档之重点。每件 quantum 特征都要给 4 个子节：

1. **已有 shadow** (in 义理 / 64-hexagram / 字)
2. **已有 hook** (in Lean / Markov 桥 S-files)
3. **Lean gap** (what's missing)
4. **升 first-class 路径** (new Lean file plan with LOC estimate)

### § 2.1 Superposition · 叠加

#### § 2.1.1 已有 shadow (in 义理)

Quantum superposition 之离散 shadow 已在易义理中以**实/虚 modal**形式出现多处：

| 义理 anchor | 文件 | 内容 / 关键 phrasing |
|---|---|---|
| 实虚史真 (C) | [`义理/C_实虚史真.md`](../../义理/C_实虚史真.md) | 实 vs 虚 之 modal 二分 — 实 = `actualized`，虚 = `potential / superposed` |
| 几 (R₃ 巽) | [`义理/B_六征体系.md`](../../义理/B_六征体系.md) (R₃ 之征) | 几 = 「事之微而未现」— 「微细变化即将显现」之 phase; quantum superposition 之 phenomenology |
| 虚 | [`义理/物理 · 从元到象.md`](../../义理/物理%20·%20从元到象.md) § 二、三 | 虚 = `potential`, basis state 之 amplitude 但不 collapse |
| 量子物理语言 § 三 | [`义理/量子物理语言 · 从虚到测.md`](../../义理/量子物理语言%20·%20从虚到测.md) | "叠加 ↔ 虚态，测量 ↔ 开闭闸口" — superposition 作为 modal 框架 |
| S5d/S5e ±1 phase | Markov桥 sign-only amplitude | quantum amplitude 之**最弱 shadow** (只有相位 ±1) — 详 § 2.3 |
| 形 (几何位) | [`义理/几何位 · 从元到形.md`](../../义理/几何位%20·%20从元到形.md) | quantum geometry = Hilbert space 之 phenomenological 投影 |

**关键 phrasings (引)**：

- C_实虚史真: 「实者著也，虚者潜也；潜未显非无，著未尽非全」— quantum potential 之**最干净中文 anchor**
- B_六征: 「几者动之微，吉之先见者也」(《系辞》原文) — 微变之 phase
- 量子物理语言 § 三: 「叠加 = 虚态在 basis 上之 complex linear combination」— 已**显式**陈述 superposition ≅ 虚

义理上 superposition 已**全方位 covered**，但 Lean 中**只有最弱 anchor**：`Yao → Qubit basis` (computational basis only)，**尚无 normalized wavefunction 之 first-class 类型**。

#### § 2.1.2 已有 hook (in Lean)

| Lean module | 内容 | 状态 |
|---|---|---|
| [`Foundation/Modern/Quantum.lean`](../../formal/SSBX/Foundation/Modern/Quantum.lean) § 1 | `abbrev Qubit : Type := Fin 2 → ℂ`; `ket0 = ![1, 0]`; `ket1 = ![0, 1]` | machineChecked basis |
| [`Foundation/Modern/Quantum.lean`](../../formal/SSBX/Foundation/Modern/Quantum.lean) § 2 | `pauliX`, `pauliY`, `pauliZ`, `hadamard` matrices | machineChecked |
| [`Foundation/Modern/Quantum.lean`](../../formal/SSBX/Foundation/Modern/Quantum.lean) § 3 | `Yao.toQubit : Yao → Qubit`, `Trigram.toBasis` | machineChecked basis embedding |
| [`Foundation/Eight/WuXiang.lean`](../../formal/SSBX/Foundation/Eight/WuXiang.lean) | `yao_bool_roundtrip`, `bool_yao_roundtrip` — 离散 basis 双射 | 0-Mathlib machineChecked |
| Markov 桥 S5d/S5e (`Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` 等) | `zero/pi → 1/-1` 之 phase label | sign-only, **not** superposition |

**关键 Lean 签名 (摘要)**：

```lean
-- Foundation/Modern/Quantum.lean (已有)
abbrev Qubit : Type := Fin 2 → ℂ
def ket0 : Qubit := ![1, 0]
def ket1 : Qubit := ![0, 1]
def Yao.toQubit : Yao → Qubit | .yang => ket0 | .yin => ket1
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
theorem pauliX_apply_yao_basis (y : Yao) : pauliX ∘ (Yao.toQubit y) = (Yao.toQubit y.neg)
```

**Gap**：仅有 `Qubit := Fin 2 → ℂ`，**无 normalized wavefunction 之 normalization 谓词**，**无 superposition 之 first-class 构造子**，**无 `α |0⟩ + β |1⟩` 之 inhabitedness**。

#### § 2.1.3 Lean gap (what's missing)

| Gap | 描述 |
|---|---|
| **Normalized state predicate** | 尚无 `Normalized : Qubit → Prop` 或 `WaveFn` subtype with `‖ψ‖² = 1` |
| **Superposition constructor** | 尚无 `superpose (α β : ℂ) (h : α^2 + β^2 = 1) : Qubit` |
| **Multi-qubit superposition** | 尚无 `MultiQubitState n : Type := { ψ : EuclideanSpace ℂ (Fin (2^n)) // ‖ψ‖ = 1 }` |
| **General basis** | 尚无 non-computational basis (Hadamard / eigenbasis 之 first-class) |
| **State space morphisms** | 尚无 `UnitaryOp : H → H` first-class 类型 |
| **Inner product / overlap** | Qubit 之 inner product 隐式在 `Fin 2 → ℂ` 中，但**未提取为 named API** |
| **`R₂ → V₄` 升级**：实/虚 modal 至 R₃-level promotion | 实/虚 目前是 V₂ (二态 modal)，类比 Shi V₂→V₄ 升级 (R₇ + R₈ 两 axis emergence)，实虚 modal 可考虑升级为 V₄ (实/虚/史/真 之 R₂²) |

**关键 design 决策**：

是否把"实/虚" modal 由 V₂ 升至 V₄ ? 类比 Shi V₂(已/未) → V₄({道,已,今,未}) 之 R₇/R₈ 双 axis emergence：
- 现状：实/虚 在 [`义理/C_实虚史真.md`](../../义理/C_实虚史真.md) 中是 V₂ Bool axis
- 候选升级：(实/虚) × (史/真) ≅ V₄ — 新增 "史" (history axis) + "真" (truth axis) 之 binary tags
- 后果：会引入两个新 binary axis (R₉ + R₁₀)，破坏 R₀..R₈ strict closure
- **建议**：不升级；保留实/虚 在 V₂；让 superposition 与 实/虚 modal **耦合但 orthogonal** (实/虚 是 modal 维度，superposition 是 algebraic 维度)

#### § 2.1.4 升 first-class 路径 (New Lean file plan)

**New file 1**: `formal/SSBX/Foundation/Modern/Quantum/WaveFn.lean` (~250 LOC)

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct
import SSBX.Foundation.Modern.Quantum

namespace SSBX.Foundation.Modern.Quantum.WaveFn

/-- n-qubit Hilbert space. -/
abbrev QSpace (n : Nat) : Type := EuclideanSpace ℂ (Fin (2 ^ n))

/-- Normalized n-qubit wavefunction subtype. -/
def WaveFn (n : Nat) : Type := {ψ : QSpace n // ‖ψ‖ = 1}

/-- Inner product of wavefunctions. -/
def WaveFn.inner {n : Nat} (ψ φ : WaveFn n) : ℂ := ⟪ψ.1, φ.1⟫_ℂ

theorem WaveFn.norm_one {n : Nat} (ψ : WaveFn n) : ‖ψ.1‖ = 1 := ψ.2

/-- Computational basis state |k⟩ for k ∈ Fin (2^n). -/
def WaveFn.basisKet {n : Nat} (k : Fin (2^n)) : WaveFn n := ⟨EuclideanSpace.basisFun ℂ _ k, by simp⟩

end SSBX.Foundation.Modern.Quantum.WaveFn
```

**Theorem dependencies**：
- `WaveFn.basisKet_norm_one` — basis state 之 normalized (trivial from `EuclideanSpace.basisFun`)
- `WaveFn.computational_basis_orthonormal` — basis 之 orthonormality
- `WaveFn.unitarily_extends_classical` — unitary 在 classical basis 上之作用与 Cell256 之 Cayley action 一致

**LOC estimate**: ~250 (含 normalization proofs, basis lemmas, inner-product API)

**New file 2**: `formal/SSBX/Foundation/Modern/Quantum/Superposition.lean` (~300 LOC)

```lean
import SSBX.Foundation.Modern.Quantum.WaveFn

namespace SSBX.Foundation.Modern.Quantum.Superposition

open WaveFn

/-- Coherent superposition of two basis states with complex amplitudes. -/
def superpose {n : Nat} (α β : ℂ) (k j : Fin (2^n)) (h : α.normSq + β.normSq = 1) : WaveFn n :=
  ⟨α • basisKet k + β • basisKet j, by simp [h]⟩

/-- "+"-state = (|0⟩ + |1⟩)/√2. -/
def plusState : WaveFn 1 := superpose (1/Real.sqrt 2) (1/Real.sqrt 2) 0 1 (by norm_num)

/-- "-"-state = (|0⟩ − |1⟩)/√2. -/
def minusState : WaveFn 1 := superpose (1/Real.sqrt 2) (-1/Real.sqrt 2) 0 1 (by norm_num)

/-- Hadamard rotates computational basis to ±-basis. -/
theorem hadamard_takes_ket0_to_plus : hadamard_op (basisKet 0) = plusState

end SSBX.Foundation.Modern.Quantum.Superposition
```

**Theorem dependencies**：
- `Quantum.pauliX_apply` — 复用 已有 `pauliX_apply_yao_basis`
- `WaveFn.norm_smul` — Mathlib
- `Real.sqrt_inv_sq` — Mathlib

**LOC estimate**: ~300 (含 ± basis, ± eigenstates of X/Z, Hadamard properties, no-clone helpers)

### § 2.2 Entanglement · 纠缠

#### § 2.2.1 已有 shadow (in 义理)

Entanglement 在义理中之 anchors：

| 义理 anchor | 文件 | 内容 / 关键 phrasing |
|---|---|---|
| 间 (Jian) | [`义理/物间事三位一体 · 时空事件.md`](../../义理/物间事三位一体%20·%20时空事件.md) + [`formal/SSBX/Foundation/Jian/`](../../formal/SSBX/Foundation/Jian/) | 「间」= 物物间之关系本体；非可分原子，需 hold 两边态同时考量 |
| 缘 | (佛教术语，散见 [`义理/Q_佛家从苦到觉.md`](../../义理/Q_佛家从苦到觉.md)) | 「因缘」= 不可分关联；A 之态依赖 B 之态 |
| 比 #8 | [`义理/I_八卦全集.md`](../../义理/I_八卦全集.md) (hex 8) | 「比者，亲也，附也」— relation primitive，binary relation 之 anchor |
| 同人 #13 | [`义理/I_八卦全集.md`](../../义理/I_八卦全集.md) (hex 13) | 「同人」= 与他人合 = Equiv (relation type-theoretically) |
| 既济-未济 hu 2-cycle | (R₆ 之 hu fixed cycle) | 既济 ↔ 未济 之 hu pair — 离散 entanglement 之 closure |
| R₈ 之 (因 ⊗ 果) | Shi V₄ emergence | (因, 果) tensor — 最简离散 entanglement model |

**关键 phrasings (引)**：

- 物间事三位一体: 「间 = 关系本身之 ontological reality; 间不可还原为物 + 物之相加」— quantum **non-separability** 之最深中文 anchor
- 比 #8 (《彖》): 「比，吉也；比，辅也；下顺从也」— relational binding 之 anchor; quantum 中 = entangled pair 之 binding
- 同人 #13: 「同人于野，亨」— equivalence class / non-distinguishable; quantum 中 = indistinguishable particles

义理上 entanglement 之 ontological anchor 全部到位 (尤其是「间」)，但 Lean **尚无 entanglement 之 first-class 类型**。

#### § 2.2.2 已有 hook (in Lean)

| Lean module | 内容 | 状态 |
|---|---|---|
| [`formal/SSBX/Foundation/Jian/Jian.lean`](../../formal/SSBX/Foundation/Jian/Jian.lean) | "间" 作为 relation ontology anchor | machineChecked typed-skeleton |
| [`formal/SSBX/Foundation/Jian/JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) | Jian as relational primitive | machineChecked |
| [`formal/SSBX/Foundation/Jian/JianYiBridge.lean`](../../formal/SSBX/Foundation/Jian/JianYiBridge.lean) | Jian ↔ Yi 之桥 | machineChecked |
| [`Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1 | Shi = `YinBit × GuoBit` — (因 ⊗ 果) tensor product (classical!) | machineChecked, **Phase C abbrev** |
| Markov 桥 S5j/S33 (two-route, kernel-path) | two-route paths with shared endpoints — **离散 entanglement-ish witness** | machineChecked typed-skeleton |

**关键 Lean 签名**：

```lean
-- Cell256.lean § 1 (already done, Phase C)
abbrev Shi : Type := YinBit × GuoBit  -- 因 ⊗ 果 classical tensor product
-- Shi 是 (Z/2)² 之 product type — 是 entanglement 之**经典 shadow**

-- Jian.lean (typed skeleton)
namespace SSBX.Foundation.Jian
structure JianRel (A B : Type) where ...
-- "间" 是 relation type-class anchor
end SSBX.Foundation.Jian
```

**Gap**：Cell256 之 `Hexagram × Shi` 是 classical tensor product (set-theoretic product)，**不是 quantum tensor product** (`H_A ⊗ H_B`)。Jian 是 ontological anchor 但**无 Bell-state construction**。

#### § 2.2.3 Lean gap (what's missing)

| Gap | 描述 |
|---|---|
| **Quantum tensor product** | Mathlib 有 `TensorProduct`, 但 `H_A ⊗ H_B` 之 quantum-specific structure (entanglement detection) 未实例化 |
| **`Separable` predicate** | 尚无 `Separable : (H_A ⊗ H_B) → Prop` 表达「存在 ψ_A, ψ_B s.t. Ψ = ψ_A ⊗ ψ_B」 |
| **`Entangled` predicate** | 尚无 `Entangled := ¬ Separable` |
| **Bell-state constructors** | 尚无 `bell_phi_plus`, `bell_phi_minus`, `bell_psi_plus`, `bell_psi_minus` |
| **Schmidt decomposition** | Mathlib 有 SVD, 但 quantum Schmidt decomp 之 wrapper 未落 |
| **Entanglement entropy** | 尚无 von Neumann entropy, 需 partial trace + log |
| **EPR / Bell inequality** | 尚无形式化 Bell 不等式 + Tsirelson 边界 |

**关键 conceptual map** (物-间-事 trinity 在 quantum 下)：

| 三位一体 | classical 读法 | quantum 读法 |
|---|---|---|
| **物** (wù, thing) | atom / cell / single-particle state | $|\psi_A\rangle \in H_A$ (single-particle ket) |
| **间** (jiān, between) | relation / binding | $\Psi_{AB} \in H_A \otimes H_B$, entangled if not separable |
| **事** (shì, event) | composite system observable | $\text{Tr}(\hat{O} \rho)$, measurement event with both subsystems' joint state |

详 [`义理/物间事三位一体 · 时空事件.md`](../../义理/物间事三位一体%20·%20时空事件.md) + 升级路径 § 2.2.4。

#### § 2.2.4 升 first-class 路径 (New Lean file plan)

**New file**: `formal/SSBX/Foundation/Modern/Quantum/Entanglement.lean` (~500 LOC)

```lean
import Mathlib.LinearAlgebra.TensorProduct
import SSBX.Foundation.Modern.Quantum.WaveFn

namespace SSBX.Foundation.Modern.Quantum.Entanglement

open WaveFn TensorProduct

/-- Bipartite quantum state space H_A ⊗ H_B. -/
abbrev QBipartite (nA nB : Nat) : Type := QSpace nA ⊗[ℂ] QSpace nB

/-- Separable state: ∃ ψA ψB, Ψ = ψA ⊗ ψB. -/
def Separable {nA nB : Nat} (Ψ : QBipartite nA nB) : Prop :=
  ∃ (ψA : QSpace nA) (ψB : QSpace nB), Ψ = ψA ⊗ₜ[ℂ] ψB

/-- Entangled state: not separable. -/
def Entangled {nA nB : Nat} (Ψ : QBipartite nA nB) : Prop := ¬ Separable Ψ

/-- Bell state |Φ⁺⟩ = (|00⟩ + |11⟩)/√2. -/
def bell_phi_plus : QBipartite 1 1 :=
  (1/Real.sqrt 2) • (ket0 ⊗ₜ ket0 + ket1 ⊗ₜ ket1)

/-- Bell state |Φ⁻⟩ = (|00⟩ − |11⟩)/√2. -/
def bell_phi_minus : QBipartite 1 1 :=
  (1/Real.sqrt 2) • (ket0 ⊗ₜ ket0 - ket1 ⊗ₜ ket1)

/-- Bell state |Ψ⁺⟩ = (|01⟩ + |10⟩)/√2. -/
def bell_psi_plus : QBipartite 1 1 :=
  (1/Real.sqrt 2) • (ket0 ⊗ₜ ket1 + ket1 ⊗ₜ ket0)

/-- Bell state |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2. (singlet) -/
def bell_psi_minus : QBipartite 1 1 :=
  (1/Real.sqrt 2) • (ket0 ⊗ₜ ket1 - ket1 ⊗ₜ ket0)

theorem bell_phi_plus_entangled : Entangled bell_phi_plus
theorem bell_phi_minus_entangled : Entangled bell_phi_minus
theorem bell_psi_plus_entangled : Entangled bell_psi_plus
theorem bell_psi_minus_entangled : Entangled bell_psi_minus

/-- 既济 (jiji = OX["oxoxox"]) ↔ 未济 (weiji = OX["xoxoxo"]) hu 2-cycle quantum analog:
    Bell-like maximally distinct pair on 6 qubits. -/
def jiji_weiji_pair_state : QBipartite 3 3 := ...

end SSBX.Foundation.Modern.Quantum.Entanglement
```

**Theorem dependencies**：
- `TensorProduct.tmul_smul`, `TensorProduct.add_tmul` — Mathlib
- `WaveFn` (from `WaveFn.lean`)
- `LinearAlgebra.LinearIndependent` (for entanglement proofs)

**LOC estimate**: ~500 (含 4 Bell states + 4 entanglement proofs + Schmidt decomp scaffold + 既济/未济 quantum pair)

**Doctrine doc**: `docs-next/10_formal_形式/entanglement-quantum.md` (新建, ~300 lines) — 论述 间-缘-比-同人 之 quantum reading + Bell-state 与 R₈ Shi (因, 果) 之 product structure 之 isomorphism。

### § 2.3 Interference · 干涉 (重头戏, Markov 桥 plumbing 之"激活")

#### § 2.3.1 已有 shadow (in 义理)

Interference 在易义理中之 anchors **全面**：

| 义理 anchor | 文件 | 内容 / 关键 phrasing |
|---|---|---|
| 错 (cuo, P parity) | [`义理/D_算子代数.md`](../../义理/D_算子代数.md) + [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) | cuo = 全 yao 反 = parity 翻转 = -1 phase 之离散版 |
| 综 (zong, T time-reversal) | 同上 | zong = 反序 = time-reversal = path 之 backward 读 |
| 错综 (PT) | 同上 | PT = parity + time-reversal 复合 = full inversion |
| hu 2-cycle (既济 ↔ 未济) | [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 7.2 | discrete self-reference 之 algebraic 见证; ↔ two-path interference |
| Markov 桥 S5 + 12 个 follow-up | [`义理/干涉与测量律候选 · Markov桥S5.md`](../../义理/干涉与测量律候选%20·%20Markov桥S5.md) 起 | **明文 plumbing**：path amplitude, two-path cancellation, ±1 phase, Born-shaped boundary |
| 量子物理语言 § 三 | [`义理/量子物理语言 · 从虚到测.md`](../../义理/量子物理语言%20·%20从虚到测.md) | 「叠加 ↔ 虚态，测量 ↔ 开闭闸口」— interference 作为 modal 框架 |

**关键 phrasings (引)**：

- cuo / zong / 错综 之 V₄ 是物理 P/T/PT (详 [`yi-calculus-theorem.md`](yi-calculus-theorem.md) Theorem D Corollary D.3 — 「易代数 V₄ 与 物理学 {1, P, T, PT} 同构」)
- Markov 桥 S5 claim: 「path amplitude + two-route cancellation + Born-shaped boundary」— interference 之**离散 typed skeleton**
- 既济 ↔ 未济 hu 2-cycle — 「Y-combinator 之 closing iteration 的离散见证」(`yi-RO-hierarchy.md` § 7.2) — 离散版 two-path closure

**关键 observation**：interference **义理上已全方位 covered**，且 Markov 桥之 S2-S33 32 条 Lean 模块 **已经形式化** 了从 path amplitude 到 Born rule derivation 之**全部 typed skeleton**。这是三件本征 quantum 特征中**唯一 already-plumbed-in-Lean** 之一。

#### § 2.3.2 已有 hook (in Lean) — **极为丰富**

Markov 桥之 32 条 `Foundation/Modern/QuantumRelativity*.lean` 文件 + master summary [`QuantumRelativityMarkovBridge.lean`](../../formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean) 全部 machineChecked。下表 highlights 之；完整 33 个 S-files inventory 见 § 8。

| Hook | Lean module | 关键 signature | 状态 |
|---|---|---|---|
| **S5 干涉与测量律候选** | `QuantumRelativityInterferenceBridge.lean` | `PathAmplitudeSkeleton`, `InterferenceCandidate`, `BornRuleCandidateBoundary`, `interference_bridge_summary` | machineChecked typed skeleton |
| **S5c 双路径相消** | `QuantumRelativityTwoPathInterferenceBridge.lean` | `TwoStepPathWitness`, `SameEndpointTwoStepPair`, `twoRouteProcess`, `two_route_pair_amplitude_cancels` ($1+(-1)=0$) | machineChecked |
| **S5d 离散相位标记** | `QuantumRelativityDiscretePhaseBridge.lean` | `DiscretePhase`, `discretePhaseAmplitude`, `two_route_phase_pair_amplitude_cancels` | machineChecked (zero/pi → ±1) |
| **S5e 离散作用量相位** | `QuantumRelativityDiscreteActionBridge.lean` | `TwoStepEdgePhaseCandidate`, edge-phase accumulation, $\pi$ relative phase | machineChecked |
| **S5f-S5p 路径族算子** | 多文件 (S5f finite path family, S5g algebra, S5h endpoint-indexed, S5i normalization, S5j-S5p quotient) | finite path-family sum, append/permutation/reverse stability, key-equivalence quotient | machineChecked |
| **S5r 作用量相位律** | `QuantumRelativityActionPhaseLawBridge.lean` | action index `0/1` → `1/-1` | machineChecked |
| **S18 Born rule 推导** | `QuantumRelativityBornRuleDerivationBridge.lean` | `MarkovAmplitudeCompatibility`, `markov_amplitude_born_rule_derivation` | machineChecked (Markov amplitude → Born boundary) |
| **S20 非平凡量子通道律** | `QuantumRelativityNontrivialChannelLawBridge.lean` | `nontrivial_quantum_channel_law_bridge_summary` | machineChecked |
| **S22 作用相位到测量权重** | `QuantumRelativityActionAmplitudeMeasurementBridge.lean` | action branch → action amplitude → normalized qubit → measurement weights | machineChecked |
| **S23 有限相位演化** | `QuantumRelativityFinitePhaseEvolutionBridge.lean` | branch-indexed `±1` phase → normalized qubit | machineChecked |
| **S24 连续作用量泛函** | `QuantumRelativityContinuousActionFunctionalBridge.lean` | $S(t)=t$ continuous → finite action samples → Born preservation | machineChecked |
| **S25 路径空间作用量泛函** | `QuantumRelativityPathSpaceActionFunctionalBridge.lean` | finite quotient path classes → action values → cancellation | machineChecked |
| **S29 有限核路径载体** | `QuantumRelativityFiniteKernelPathCarrierBridge.lean` | finite kernel path carrier with weight/causal readback | machineChecked |
| Master summary | `QuantumRelativityMarkovBridge.lean` | `markov_causal_bridge_summary` (theorem 含 8 conjuncts) | machineChecked |

**Lean 签名 (sample)**：

```lean
-- QuantumRelativityInterferenceBridge.lean (S5 已落)
structure PathAmplitudeSkeleton where
  amplitude : Path → Int        -- sign-only, ±1 placeholder
  ...

theorem two_route_pair_amplitude_cancels : 
    amplitude upperPath + amplitude lowerPath = 0

structure BornRuleCandidateBoundary where
  weight : Path → Nat
  weight_nonneg : ∀ p, 0 ≤ weight p
  weight_eq_amp_sq : weight p = (amplitude p)^2  -- Born-shaped!
```

#### § 2.3.3 Lean gap (what's missing) — minimal!

**关键 observation**: interference 之 Lean gap **不在 plumbing**，而在 **amplitude 数域**：

| Gap | 描述 |
|---|---|
| **Amplitude 数域**: `Int` (±1) → `ℂ` | 当前 S-series 之 `amplitude : Path → Int` 是 sign-only 占位；quantum activation = 改为 `amplitude : Path → ℂ` |
| **Phase 之 ℂ-amplitude**: `±1` (S5d) → `e^{iθ}` | S5d 之 zero/pi → ±1 升级为任意 $e^{iθ}$ |
| **Action functional**: integer index (S5r) → real-valued S(t) → $e^{iS/\hbar}$ phase | S24 已是 $S(t)=t$ continuous，需升级为 quantum phase $e^{iS(t)/\hbar}$ |
| **Path integral 之 measure**: discrete (S25 quotient classes) → continuous (Lebesgue 或 Wiener measure on path space) | 需 Mathlib MeasureTheory + path integral framework |
| **Hilbert state evolution**: qubit (S22) → general Hilbert (S23 + Schrödinger eq.) | 需 unitary 1-parameter group + ODE |
| **Born rule full**: Markov-compatible normalized weights (S18) → full $|\langle\phi|\psi\rangle|^2$ | 需 inner product + measurement projection |
| **Decoherence**: 无 hook | 需 environment trace + density matrix |

**激活路径**: 不是"重写"，而是把每个 S-file 之 `Int` amplitude 替换为 `ℂ` amplitude, 同时保留全部已证 lemma 结构。整套 S2-S33 之 plumbing 即时升级为 quantum-grade.

#### § 2.3.4 升 first-class 路径 (New Lean file plan)

**New file 1**: `formal/SSBX/Foundation/Modern/Quantum/PathIntegral.lean` (~600 LOC)

```lean
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Analysis.NormedSpace.Exponential
import SSBX.Foundation.Modern.Quantum.WaveFn
import SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge

namespace SSBX.Foundation.Modern.Quantum.PathIntegral

open WaveFn

/-- Quantum path with complex amplitude. -/
structure QPath (n : Nat) where
  pts : List (Fin (2^n))
  amplitude : ℂ
  norm_consistent : True  -- to be tightened

/-- Path amplitude is a complex number (not Int). -/
def QPath.complexAmplitude {n : Nat} (p : QPath n) : ℂ := p.amplitude

/-- Action S(t) gives phase e^{iS/ℏ}. -/
def actionPhase (S : ℝ) (hbar : ℝ) : ℂ := Complex.exp (Complex.I * S / hbar)

/-- Two-path interference: amplitude sum. -/
def twoPathInterference {n : Nat} (p1 p2 : QPath n) : ℂ := p1.amplitude + p2.amplitude

/-- Born rule: |amplitude|² is probability. -/
def bornProb {n : Nat} (p : QPath n) : ℝ := Complex.normSq p.amplitude

theorem bornProb_nonneg {n : Nat} (p : QPath n) : 0 ≤ bornProb p

/-- Activate S5c upgrade: ±1 cancellation → continuous phase cancellation. -/
theorem two_path_phase_cancellation_quantum :
    ∀ θ, actionPhase θ + actionPhase (θ + Real.pi) = 0  -- e^{iθ} + e^{i(θ+π)} = 0

end SSBX.Foundation.Modern.Quantum.PathIntegral
```

**Theorem dependencies**：
- `Complex.exp_add_pi_eq_neg` — Mathlib (`e^{iπ} = -1`)
- S5c之 `two_route_pair_amplitude_cancels` — 复用 (sign-only specialization)
- S5d之 `discretePhaseAmplitude` — 复用 (zero/pi specialization)
- S5r之 action index → phase — 复用 (integer special case)

**LOC estimate**: ~600 (含 path integral framework + S-series activation + interference theorems)

**激活策略 detail**：

```
ACTIVATION PATTERN (重复 32 次 for S2-S33):
1. Open S-file (e.g. QuantumRelativityDiscretePhaseBridge.lean)
2. Replace `amplitude : Path → Int` with `amplitude : Path → ℂ`
3. Replace `Int.eq_neg_self_iff_eq_zero` lemma usage with `Complex.add_eq_zero_iff_eq_neg`
4. Replace `discretePhaseAmplitude : DiscretePhase → Int := fun | .zero => 1 | .pi => -1`
   with `quantumPhaseAmplitude : ℝ → ℂ := fun θ => Complex.exp (I * θ)`
5. Bind new doctrine doc `quantum-activated-S5d.md` to point to upgraded file
6. Each S-file upgrade: ~50-100 LOC change, mechanical
7. Total: 32 files × ~75 LOC = ~2400 LOC of mechanical activation
```

**Doctrine doc**: `docs-next/10_formal_形式/interference-quantum.md` (~300 lines) — 论述 cuo/zong/错综 V₄ 在 quantum 下作为 P/T/PT 之精确物理对应 + Markov 桥 S5/S5b-S5r 之激活映射表 + 既济/未济 hu 2-cycle 之 quantum reading。

---

## § 3. 二级 quantum 特征 (Secondary Quantum Features)

本节覆盖 measurement / collapse / Born rule / density matrix / CPTP channels / decoherence / no-cloning / Bell / PT 八项 "essential second-tier" features，每件给 anchor + 升级路径。

### § 3.1 Measurement / Collapse · 测量 / 坍缩

#### Anchor: 测的边界

- 义理: [`义理/边界/测的边界 · 观验读.md`](../../义理/边界/测的边界%20·%20观验读.md) + [`义理/边界/统一边界 · 从理到文.md`](../../义理/边界/统一边界%20·%20从理到文.md) — 测之六轴 (观/接/法/校/读/记)
- Lean 已有: [`Foundation/Modern/CeBoundary.lean`](../../formal/SSBX/Foundation/Modern/CeBoundary.lean) — 测流程边界层 (`ce_boundary_summary`)
- Lean 已有: [`Foundation/Modern/QuantumSpacetime.lean`](../../formal/SSBX/Foundation/Modern/QuantumSpacetime.lean) — collapse outcome 三类边界 (实/虚/八卦态)
- Markov 桥 S21: `QuantumRelativityBornMeasurementBridge.lean` — one-qubit computational-basis measurement weights (machineChecked)

#### New file: `Foundation/Modern/Quantum/Measurement.lean` (~400 LOC)

```lean
namespace SSBX.Foundation.Modern.Quantum.Measurement

/-- Projection-valued measure on a finite-dim Hilbert space. -/
structure PVM (H : Type) [InnerProductSpace ℂ H] (Outcomes : Type) where
  P : Outcomes → H →ₗ[ℂ] H
  P_projection : ∀ o, (P o) ∘ₗ (P o) = P o
  P_orthogonal : ∀ o₁ o₂, o₁ ≠ o₂ → P o₁ ∘ₗ P o₂ = 0
  P_complete : ∑ o, P o = LinearMap.id

/-- Measurement outcome probability via Born rule. -/
def measurementProb (Ψ : WaveFn n) (pvm : PVM ...) (o : Outcomes) : ℝ :=
  ‖(pvm.P o) Ψ.1‖^2

/-- Post-measurement state (collapse). -/
def collapseState (Ψ : WaveFn n) (pvm : PVM ...) (o : Outcomes) : WaveFn n := ...

/-- Computational-basis measurement = standard 测的边界 specialization. -/
def computationalBasisMeasurement (n : Nat) : PVM (QSpace n) (Fin (2^n)) := ...

end SSBX.Foundation.Modern.Quantum.Measurement
```

**LOC estimate**: ~400 (PVM + Born + collapse + computational-basis + projection-product theorems)

### § 3.2 Born rule as theorem (currently boundary witness in S18)

#### 已有: S18 之 conditional Born rule

`QuantumRelativityBornRuleDerivationBridge.lean` 之 `markov_amplitude_born_rule_derivation`:

```text
normalized finite Markov row
+ amplitude assignment on the same row support
+ bridge equation: ampProb amplitude = normalizedMass
= normalized finite amplitude support
= S12 finite Born distribution boundary
```

这是 conditional Born rule — 在 Markov-amplitude compatibility 假设下成立 (machineChecked)。

#### Upgrade path: theorem-level Born rule

```lean
namespace SSBX.Foundation.Modern.Quantum.BornRule

theorem born_rule_for_pure_state {n : Nat} (Ψ : WaveFn n) (o : Fin (2^n)) :
    measurementProb Ψ (computationalBasisMeasurement n) o
    = Complex.normSq (Ψ.1 o)
```

**Dependencies**: WaveFn.lean + Measurement.lean

**LOC**: ~150 (in Measurement.lean or separate `BornRule.lean`)

### § 3.3 Density matrix (mixed states)

#### Anchor: 与 Markov 桥 finite distribution 之桥

经典 finite probability distribution (Markov 桥 S9-S12) — 在 finite case 是 density matrix 之 diagonal special case。

#### New file: `Foundation/Modern/Quantum/DensityMatrix.lean` (~350 LOC)

```lean
namespace SSBX.Foundation.Modern.Quantum.DensityMatrix

/-- Density matrix on n-qubit Hilbert space. -/
structure DensityMatrix (n : Nat) where
  ρ : Matrix (Fin (2^n)) (Fin (2^n)) ℂ
  Hermitian : ρ = ρ.conjTranspose
  PSD : ∀ ψ, 0 ≤ Complex.re ⟪ψ, ρ.mulVec ψ⟫_ℂ
  Trace_one : ρ.trace = 1

/-- Pure state's density matrix. -/
def WaveFn.toDensityMatrix {n : Nat} (Ψ : WaveFn n) : DensityMatrix n :=
  ⟨Ψ.1 ⊗ Ψ.1.conjTranspose, ..., ..., ...⟩

/-- Mixed state via convex combination. -/
def mixedState {n : Nat} (probs : List (ℝ × WaveFn n))
    (h_norm : probs.foldl (·.1) 0 = 1) : DensityMatrix n := ...

/-- von Neumann entropy. -/
def vNEntropy {n : Nat} (ρ : DensityMatrix n) : ℝ := -Real.log ρ.ρ.trace  -- TODO via diagonalization

end SSBX.Foundation.Modern.Quantum.DensityMatrix
```

**Dependencies**: Mathlib Matrix + Spectral theorem + WaveFn.lean

**LOC**: ~350

### § 3.4 Channels / CPTP

#### 已有: S17/S20 之 channel ledger

- `QuantumRelativityUnitaryCPTPLedgerBridge.lean` (S17) — current skeleton items closed; physical CPTP items pending
- `QuantumRelativityNontrivialChannelLawBridge.lean` (S20) — finite support-respecting nonzero channel law
- `QuantumRelativityChannelComposeBridge.lean` (S13) — pointwise channel composition
- `QuantumRelativityChannelComposeAssociativityBridge.lean` (S14) — associativity + identity obstruction
- `QuantumRelativitySumOverMiddleChannelBridge.lean` (S15) — sum-over-middle 通道组合

#### New file: `Foundation/Modern/Quantum/Channel.lean` (~500 LOC)

```lean
namespace SSBX.Foundation.Modern.Quantum.Channel

open DensityMatrix

/-- Completely positive trace-preserving (CPTP) map. -/
structure CPTPMap (m n : Nat) where
  E : DensityMatrix m → DensityMatrix n
  CompletePositivity : ∀ k, CPMap.completePositive (CPTPMap.tensorExtend E k)
  TracePreservation : ∀ ρ, (E ρ).ρ.trace = ρ.ρ.trace

/-- Kraus representation: E(ρ) = Σ_i K_i ρ K_i†. -/
structure KrausRepresentation (m n : Nat) where
  K : List (Matrix (Fin (2^n)) (Fin (2^m)) ℂ)
  completeness : K.foldl (fun acc Ki => acc + Ki.conjTranspose * Ki) 0 = 1

/-- Unitary channel: ρ ↦ U ρ U†. -/
def unitaryChannel {n : Nat} (U : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) (h_unitary : ...) : CPTPMap n n := ...

/-- Channel composition. Activates S13/S14. -/
def CPTPMap.compose {l m n : Nat} (E1 : CPTPMap l m) (E2 : CPTPMap m n) : CPTPMap l n := ...

theorem CPTPMap.compose_assoc : ∀ E1 E2 E3, (E1.compose E2).compose E3 = E1.compose (E2.compose E3)
end SSBX.Foundation.Modern.Quantum.Channel
```

**LOC**: ~500 (CPTP + Kraus + composition + Stinespring + unitary)

### § 3.5 Decoherence

#### Anchor: 体 → 系统 + 环境 之纠缠衰变；与 Markov chain 之关系

- [`义理/动力 · 从元到行.md`](../../义理/动力%20·%20从元到行.md) — 动力之 V₂→V₄ emergence
- [`Foundation/Modern/DongLi.lean`](../../formal/SSBX/Foundation/Modern/DongLi.lean) — 动力 (dynamics) module
- Markov chain semantics 已在 S2 (finite probability kernel) — decoherence 之 classical limit

#### New file: `Foundation/Modern/Quantum/Decoherence.lean` (~300 LOC)

```lean
namespace SSBX.Foundation.Modern.Quantum.Decoherence

/-- System + environment Hilbert space. -/
abbrev SystemEnv (nS nE : Nat) : Type := QBipartite nS nE

/-- Reduced density matrix via partial trace over environment. -/
def reducedSystem {nS nE : Nat} (Ψ_SE : SystemEnv nS nE) : DensityMatrix nS :=
  partialTrace Ψ_SE -- trace out environment

/-- Decoherence: off-diagonal terms decay. -/
def decohered {nS nE : Nat} (Ψ_SE : SystemEnv nS nE) : Prop :=
  ∀ i j, i ≠ j → Complex.normSq (reducedSystem Ψ_SE).ρ i j < ε

/-- Markov chain as classical limit of decoherent quantum channel. -/
theorem markov_classical_limit (E : CPTPMap n n) (h_decohered : decoheres E) :
    ∃ M : MarkovKernel, E.toClassical = M

end SSBX.Foundation.Modern.Quantum.Decoherence
```

**LOC**: ~300

### § 3.6 No-cloning / No-broadcasting

#### Anchor: quantum information primitive

经典 (`Cell256` 之 Cayley) 中 `cayleyQ c = (· ⊗ c)` 可以拷贝任意 c。Quantum 中 no-cloning 是基本 theorem。

#### New file: `Foundation/Modern/Quantum/NoCloning.lean` (~200 LOC)

```lean
namespace SSBX.Foundation.Modern.Quantum.NoCloning

theorem no_cloning : ¬ ∃ (U : (QSpace 1) ⊗[ℂ] (QSpace 1) →ₗ[ℂ] (QSpace 1) ⊗[ℂ] (QSpace 1)),
    Unitary U ∧ ∀ ψ : QSpace 1, U (ψ ⊗ₜ ket0) = ψ ⊗ₜ ψ

theorem no_broadcasting : ¬ ∃ (B : DensityMatrix 1 → DensityMatrix 2),
    ∀ ρ, partialTrace1 (B ρ) = ρ ∧ partialTrace2 (B ρ) = ρ

end SSBX.Foundation.Modern.Quantum.NoCloning
```

**LOC**: ~200

### § 3.7 Bell / EPR / Tsirelson 边界

#### Anchor: 量子非局域性的形式见证

- Bell-state constructors (in `Entanglement.lean`)
- 既济/未济 hu 2-cycle 作为离散 Bell-pair 之 anchor

#### New file: `Foundation/Modern/Quantum/Bell.lean` (~400 LOC)

```lean
namespace SSBX.Foundation.Modern.Quantum.Bell

/-- CHSH operator. -/
def CHSH (A0 A1 B0 B1 : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ := ...

theorem chsh_classical_bound : ∀ classical_strategy, |classical_CHSH classical_strategy| ≤ 2
theorem tsirelson_bound : ∀ quantum_strategy, |quantum_CHSH quantum_strategy| ≤ 2 * Real.sqrt 2
theorem bell_violates_chsh_classical : ∃ Ψ, |chsh bell_psi_minus| > 2

end SSBX.Foundation.Modern.Quantum.Bell
```

**LOC**: ~400

### § 3.8 PT / CPT · cuo / zong / cuoZong 之物理意义

#### Anchor: V₄ Shi 与物理 P/T/PT 同构 (Theorem D Corollary D.3)

cuo (P) / zong (T) / cuoZong (PT) 在 V₄ 中 — quantum 升级为 Pauli X / Z / iY (modulo iI)。CPT theorem 在 quantum field theory 中是 fundamental — 「易代数 V₄ 是 CPT closure 之离散版」是 quantum 化下之物理读法。

#### New file: `Foundation/Modern/Quantum/PT.lean` (~250 LOC)

```lean
namespace SSBX.Foundation.Modern.Quantum.PT

/-- Quantum P operator: X^⊗6 on hex qubits. -/
def quantumP : Cell256Q →ₗ[ℂ] Cell256Q := ...

/-- Quantum T operator: complex conjugation + reverse permutation. -/
def quantumT : Cell256Q →ₗ[ℂ] Cell256Q := ...

/-- Quantum PT operator: P composed with T. -/
def quantumPT : Cell256Q →ₗ[ℂ] Cell256Q := quantumT ∘ₗ quantumP

theorem PT_squared : quantumPT ∘ₗ quantumPT = LinearMap.id  -- PT² = 1 in V₄
theorem PT_commutes_hex_shi : ...

/-- CPT theorem (placeholder): closure under V₄ is structural. -/
theorem CPT_closure : ∀ Ψ, ∃ Ψ', quantumPT Ψ = Ψ'

end SSBX.Foundation.Modern.Quantum.PT
```

**LOC**: ~250

---

## § 4. Qubit lift 之具体类型 (Concrete Quantum Carrier Types)

本节给 R₀..R₈ 每层之 quantum carrier 类型 Lean sketch + bridging functions + tensor product isomorphisms。

### § 4.1 Core types

```lean
namespace SSBX.Foundation.Modern.Quantum

open Mathlib Complex

/-- 单 qubit. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- R₁ Yao quantum carrier. -/
abbrev YaoQ : Type := Qubit

/-- Yao → YaoQ basis embedding (already exists in Quantum.lean). -/
def yaoToYaoQ : Yao → YaoQ
  | .yang => ket0   -- |0⟩
  | .yin  => ket1   -- |1⟩

/-- R₂ SiXiang quantum carrier. -/
abbrev SiXiangQ : Type := EuclideanSpace ℂ (Fin 4)
-- iso: SiXiangQ ≃ YaoQ ⊗[ℂ] YaoQ

/-- R₃ Trigram quantum carrier. -/
abbrev TrigramQ : Type := EuclideanSpace ℂ (Fin 8)
-- iso: TrigramQ ≃ YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ

/-- R₄ Mian quantum carrier. -/
abbrev MianQ : Type := EuclideanSpace ℂ (Fin 16)

/-- R₅ Wuyao quantum carrier. -/
abbrev WuyaoQ : Type := EuclideanSpace ℂ (Fin 32)

/-- R₆ Hexagram quantum carrier. -/
abbrev HexagramQ : Type := EuclideanSpace ℂ (Fin 64)
-- iso: HexagramQ ≃ (ℂ²)^⊗6

/-- R₇ Cell128 quantum carrier. -/
abbrev Cell128Q : Type := EuclideanSpace ℂ (Fin 128)
-- iso: Cell128Q ≃ HexagramQ ⊗ YinBitQ

/-- R₈ Cell256 quantum carrier — R-hierarchy closure. -/
abbrev Cell256Q : Type := EuclideanSpace ℂ (Fin 256)
-- iso: Cell256Q ≃ HexagramQ ⊗ ShiQ ≃ (ℂ²)^⊗8

end SSBX.Foundation.Modern.Quantum
```

### § 4.2 Bridging functions

```lean
namespace SSBX.Foundation.Modern.Quantum

/-- Classical → quantum embedding: Cell256 → Cell256Q basis state. -/
def Cell256.toBasisQ : Cell256 → Cell256Q :=
  fun c => EuclideanSpace.basisFun ℂ _ (Cell256.toFin c)

/-- Cell256 → Fin 256 bijection (helper, exists implicitly). -/
def Cell256.toFin : Cell256 → Fin 256 := ...

/-- Quantum projector: Cell256Q → Cell256 (measurement onto computational basis,
    returns Cell256 + amplitude or via collapse). -/
noncomputable def Cell256Q.collapse (Ψ : Cell256Q) : Cell256 := ...  -- pick max-amplitude basis state

/-- Hex × Shi 分解 in quantum: Cell256Q ≃ HexagramQ ⊗ ShiQ. -/
def Cell256Q.hexShiIso : Cell256Q ≃ₗ[ℂ] (HexagramQ ⊗[ℂ] ShiQ) := ...

end SSBX.Foundation.Modern.Quantum
```

### § 4.3 Tensor product isomorphisms

```lean
namespace SSBX.Foundation.Modern.Quantum

/-- Each R-layer is tensor product of single-qubit Hilbert spaces. -/
theorem yaoQ_iso : YaoQ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 2) := LinearEquiv.refl ℂ _

theorem sixiangQ_iso : SiXiangQ ≃ₗ[ℂ] YaoQ ⊗[ℂ] YaoQ := ...

theorem trigramQ_iso : TrigramQ ≃ₗ[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ := ...

theorem hexagramQ_iso : HexagramQ ≃ₗ[ℂ] (YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ) := ...

/-- Cell128Q = HexagramQ ⊗ YinBitQ. -/
theorem cell128Q_iso : Cell128Q ≃ₗ[ℂ] HexagramQ ⊗[ℂ] YaoQ := ...

/-- Cell256Q = HexagramQ ⊗ ShiQ, where ShiQ = YinBitQ ⊗ GuoBitQ. -/
theorem cell256Q_iso : Cell256Q ≃ₗ[ℂ] HexagramQ ⊗[ℂ] (YaoQ ⊗[ℂ] YaoQ) := ...
theorem cell256Q_full_iso : Cell256Q ≃ₗ[ℂ] (YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ ⊗[ℂ] YaoQ) := ...
-- 即 (ℂ²)^⊗8

end SSBX.Foundation.Modern.Quantum
```

---

## § 5. 对照表：经典 ↔ 量子 (Big Comparison Tables)

### § 5.1 R₀..R₈ 各层 (Sizes / Types / Files)

| Layer | classical type | Lean classical file | size | Hilbert dim | Lean quantum file | Mathlib ref |
|---|---|---|---|---|---|---|
| R₀ | `Unit` | (stdlib) | 1 | 1 | `Foundation/Modern/Quantum/Taiji.lean` (trivial) | — |
| R₁ | `Yao` (Bool) | `Foundation/Yi/Yi.lean` | 2 | 2 | `Foundation/Modern/Quantum/Yao.lean` (already: `Yao.toQubit`) | `EuclideanSpace ℂ (Fin 2)` |
| R₂ | `SiXiang` | `Foundation/Bagua/BaguaAlgebra.lean` | 4 | 4 | `Foundation/Modern/Quantum/SiXiang.lean` | `EuclideanSpace ℂ (Fin 4)` |
| R₃ | `Trigram` | `Foundation/Yi/Yi.lean` | 8 | 8 | `Foundation/Modern/Quantum/Trigram.lean` | `EuclideanSpace ℂ (Fin 8)` (or `(ℂ²)^⊗3`) |
| R₄ | `Mian` | `Foundation/Bagua/BenZheng.lean` | 16 | 16 | `Foundation/Modern/Quantum/Mian.lean` | `EuclideanSpace ℂ (Fin 16)` |
| R₅ | `Wuyao` | `Foundation/Hierarchy/R5_Wuyao.lean` | 32 | 32 | `Foundation/Modern/Quantum/Wuyao.lean` | `EuclideanSpace ℂ (Fin 32)` |
| R₆ | `Hexagram` | `Foundation/Yi/Yi.lean` | 64 | 64 | `Foundation/Modern/Quantum/Hexagram.lean` | `EuclideanSpace ℂ (Fin 64)` |
| R₇ | `Cell128` | `Foundation/Bagua/Cell128.lean` | 128 | 128 | `Foundation/Modern/Quantum/Cell128.lean` | `EuclideanSpace ℂ (Fin 128)` |
| R₈ | `Cell256` | `Foundation/Bagua/Cell256.lean` | 256 | 256 | `Foundation/Modern/Quantum/Cell256.lean` | `EuclideanSpace ℂ (Fin 256)` |

### § 5.2 All 8 atomic XOR generators ↔ Pauli-X gates

复用 § 1.3 之表，但加 quantum lemma 之 Lean 签名：

| Atomic op | mask | Lean classical | Lean quantum | 升级 lemma |
|---|---|---|---|---|
| `flip1` | `OX["xooooooo"]` | `Cell128.flip1` (involutive) | `X_at 0` (Pauli-X on qubit 0) | `cell256_q_X_at_0_iso_classical_flip1` |
| `flip2` | `OX["oxoooooo"]` | `Cell128.flip2` | `X_at 1` | `cell256_q_X_at_1_iso_classical_flip2` |
| `flip3` | `OX["ooxooooo"]` | `Cell128.flip3` | `X_at 2` | `cell256_q_X_at_2_iso_classical_flip3` |
| `flip4` | `OX["oooxoooo"]` | `Cell128.flip4` | `X_at 3` | `cell256_q_X_at_3_iso_classical_flip4` |
| `flip5` | `OX["ooooxooo"]` | `Cell128.flip5` | `X_at 4` | `cell256_q_X_at_4_iso_classical_flip5` |
| `flip6` | `OX["oooooxoo"]` | `Cell128.flip6` | `X_at 5` | `cell256_q_X_at_5_iso_classical_flip6` |
| `yin` (印) | `OX["ooooooxo"]` | `Cell256.yin` | `X_at 6` | `cell256_q_X_at_6_iso_classical_yin` |
| `tou` (投) | `OX["ooooooox"]` | `Cell256.tou` | `X_at 7` | `cell256_q_X_at_7_iso_classical_tou` |

### § 5.3 V₄ outer ops ↔ Multi-qubit Pauli + permutation

| V4Outer op | Lean classical | Quantum upgrade | Lean quantum | 升级 lemma |
|---|---|---|---|---|
| `hex_cuo` | XOR with kun mask | $X^{\otimes 6}$ (global Pauli-X on hex qubits) | `hexCuoQ` | `hexCuoQ_iso_classical_hexCuo` |
| `hex_zong` | reverse perm | bit-reverse perm = SWAP chain | `hexZongQ` | `hexZongQ_iso_classical_hexZong` |
| `hex_cuoZong` | cuo ∘ zong | $X^{\otimes 6} \circ \text{Reverse}$ | `hexCuoZongQ` | composition lemma |
| `hex_hu` | Y-combinator mid-extract | non-unitary projection (partial isometry) | `hexHuQ` | `hexHuQ_fixed_attractor_states` |
| `shi.cuo` | YinBit flip | $X_7$ (= `X_at 6`) | (alias) | (subsumed in atomic) |
| `shi.zong` | GuoBit flip | $X_8$ (= `X_at 7`) | (alias) | (subsumed in atomic) |
| `shi.cuoZong` | both flip | $X_7 \cdot X_8 = $ Pauli on Shi qubits | `shiCuoZongQ` | composition lemma |
| `Cell256.shiCuo` | preserves hex, flips Shi.因 | identity ⊗ $X_7$ | `shiCuoQ` | tensor lemma |

### § 5.4 Each key concept (origin, 印/投, cuo/zong/hu, 错综)

| classical concept | Lean | quantum reading | Lean quantum sig |
|---|---|---|---|
| **道** = origin = (qian, dao) | `Cell256.origin` | $\|00000000\rangle$ (Fock vacuum / computational basis first vector) | `Cell256Q.origin = basisKet 0` |
| **印** (yin) atomic | `Cell256.yin` (= XOR with `(qian, ji)`) | `X_at 6` (Pauli-X on qubit 7 = 因 axis) | unitary; `cayleyQ yin_mask = X_at 6` |
| **投** (tou) atomic | `Cell256.tou` (= XOR with `(qian, wei)`) | `X_at 7` (Pauli-X on qubit 8 = 果 axis) | unitary; `cayleyQ tou_mask = X_at 7` |
| **印 ∘ 投** | XOR with `(qian, jin)` (V₄ central) | $X_7 \cdot X_8$ = double Pauli-X on Shi qubits | `cayleyQ (yin_mask ⊕ tou_mask) = X_at 6 ∘ₗ X_at 7` |
| **cuo** (P) | hex全反 + Shi.因 翻 | $X^{\otimes 6} \otimes X \otimes I$ or pure $X^{\otimes 6}$ on hex | unitary parity op |
| **zong** (T) | hex 反序 perm | bit-reverse SWAP chain | unitary perm |
| **错综** (PT) | cuo ∘ zong | $X^{\otimes 6} \circ \text{Reverse}$ | unitary PT |
| **hu** (Y-comb) | mid-4-extract perm (non-bijective) | non-unitary projection (partial isometry) | partial isometry; image = 16-dim subspace |
| **道-row** (h, 道) for all h | 64 cells | $|h\rangle \otimes |00\rangle$ for h ∈ basis (64 vectors) | $\{|h\rangle \otimes |00\rangle : h \in 64\}$ |
| **既济 ↔ 未济 hu 2-cycle** | hu(jiji) = weiji | $|010101\rangle \leftrightarrow |101010\rangle$ via hu perm | discrete entanglement closure |

---

## § 6. Phase plan / 工程路线图 (13-Phase Quantum Roadmap)

13 phases (Q.0 through Q.12)，每个 phase 给 Goal / New files / Touches existing / Theorems / Cost estimate / Dependencies。

### Q.0 — Scoping + axiom plan

**Goal**: 明确 quantum 化之 axiom 底盘 + 兼容性要求 + project deprecation 决策。

**Deliverables**:
- 本文档 (`quantum-roadmap.md`) — 已建
- `docs-next/10_formal_形式/quantum-axiom-plan.md` — 公理底盘对照表 (propext + native_decide → + Mathlib classical analysis)
- 决定: 是否在 `formal/SSBX/Foundation/Modern/` 之外建 `formal/SSBX/Foundation/Modern/Quantum/` 子目录

**New files**: `quantum-roadmap.md` (this), `quantum-axiom-plan.md` (~200 lines)

**Touches existing**: 无 (pure planning)

**Theorems**: 无

**Cost**: 1 day (planning + docs)

**Dependencies**: 无

### Q.1 — Yao qubit lift

**Goal**: 把 [`Quantum.lean`](../../formal/SSBX/Foundation/Modern/Quantum.lean) 中之 `Yao.toQubit` 升为 `YaoQ` 类型 + WaveFn n=1 实例化。

**New files**: 
- `Foundation/Modern/Quantum/Yao.lean` (~150 LOC) — 把 `Yao.toQubit` + Pauli matrix 之 lemmas 重组在 namespaced module

**Touches existing**: `Foundation/Modern/Quantum.lean` — 部分 lemma 迁出到 Yao.lean

**Theorems**:
- `yaoToYaoQ_inj` (injective)
- `yaoToYaoQ_image` (image = computational basis)
- `Yao.neg_iso_pauli_X` (Pauli-X 在 Yao basis 上 = neg)

**Cost**: 2 days

**Dependencies**: Q.0

### Q.2 — Cell256 Hilbert space

**Goal**: Cell256 之 quantum carrier 类型 `Cell256Q` 建立 + tensor product isomorphism。

**New files**:
- `Foundation/Modern/Quantum/Cell256Q.lean` (~400 LOC) — `abbrev Cell256Q := EuclideanSpace ℂ (Fin 256)` + 主 isomorphism `cell256Q_full_iso : Cell256Q ≃ₗ[ℂ] (ℂ²)^⊗8`

**Touches existing**: 无 (Mathlib only)

**Theorems**:
- `cell256Q_iso_tensor_8` — Cell256Q ≃ₗ (ℂ²)^⊗8
- `cell256Q_iso_hex_shi` — Cell256Q ≃ₗ HexagramQ ⊗ ShiQ
- `Cell256.toBasisQ_inj` (classical → quantum embedding 是 injective)
- `cell256Q_basisKet_origin = ket{00000000}` (origin → first basis vector)

**Cost**: 5 days

**Dependencies**: Q.0, Q.1

### Q.3 — Superposition first-class

**Goal**: `WaveFn` + `superpose` + Hadamard transform first-class.

**New files**:
- `Foundation/Modern/Quantum/WaveFn.lean` (~250 LOC)
- `Foundation/Modern/Quantum/Superposition.lean` (~300 LOC)

**Touches existing**: 复用 `Quantum.lean` 之 `hadamard` matrix

**Theorems**:
- `WaveFn.basisKet_norm_one`
- `superpose_norm_one` (normalization preserved)
- `plus_state_eq_hadamard_ket0`
- `hadamard_inverse_hadamard` = id

**Cost**: 7 days

**Dependencies**: Q.2

### Q.4 — V₄ Shi → projective Pauli correspondence (proven theorem)

**Goal**: 严格证明 Shi V₄ ≅ projective Pauli ⟨X, Z⟩ / ⟨iI⟩。

**New files**:
- `Foundation/Modern/Quantum/ShiProjectivePauli.lean` (~350 LOC)

**Touches existing**: 复用 `Quantum.lean` 之 Pauli matrices + `Cell256.lean` Shi V₄

**Theorems**:
- `shi_to_projective_pauli : Shi → ProjectivePauli`
- `shi_v4_iso_projective_pauli` (group isomorphism)
- `shi_cuo_iso_pauli_X` (cuo ↔ Pauli X, projective)
- `shi_zong_iso_pauli_Z` (zong ↔ Pauli Z, projective)
- `shi_cuoZong_iso_pauli_Y` (cuoZong ↔ ±iY, projective)

**Cost**: 5 days

**Dependencies**: Q.2, Q.3

### Q.5 — Atomic operators → single-qubit Pauli-X gates

**Goal**: 8 atomic XOR generators 升为 8 个 Pauli-X gates on respective qubits.

**New files**:
- `Foundation/Modern/Quantum/AtomicGates.lean` (~400 LOC)

**Touches existing**: `Atomic.lean` 之 lemmas (复用)

**Theorems**:
- `X_at_pauli_X_form` (X_at k = $I^{\otimes k} \otimes X \otimes I^{\otimes (n-k-1)}$)
- `X_at_self_inverse` (involution)
- `X_at_commute` (any two commute)
- `cell256_yin_iso_X_at_6`, `cell256_tou_iso_X_at_7` (印 ↔ X_7, 投 ↔ X_8)
- `atomicGates_form_Pauli_group` (8 generators generate $X^{\otimes 8}$ Pauli subgroup of (Z/2)⁸ order)

**Cost**: 6 days

**Dependencies**: Q.2, Q.4

### Q.6 — V₄ outer ops → multi-qubit Pauli + permutation

**Goal**: cuo / zong / cuoZong / hu 升为 quantum gates.

**New files**:
- `Foundation/Modern/Quantum/V4OuterGates.lean` (~450 LOC)

**Touches existing**: `V4Outer.lean` (复用)

**Theorems**:
- `hexCuoQ_eq_X_otimes_6` ($X^{\otimes 6}$ on hex qubits)
- `hexZongQ_eq_SWAP_chain` (bit-reverse via SWAP)
- `hexCuoZongQ_eq_composition`
- `hexHuQ_partial_isometry` (hu 不是 unitary, 是 partial isometry)
- `hexHu_fixed_attractor_states_qian_kun` (hu 之 fixed states $|0\rangle^{\otimes 6}$ 与 $|1\rangle^{\otimes 6}$)

**Cost**: 8 days

**Dependencies**: Q.5

### Q.7 — Entanglement first-class

**Goal**: Bell states + Separable / Entangled predicates。

**New files**:
- `Foundation/Modern/Quantum/Entanglement.lean` (~500 LOC)

**Touches existing**: `Jian.lean` (引用 anchor)

**Theorems**:
- `bell_phi_plus_entangled`
- `bell_phi_minus_entangled`
- `bell_psi_plus_entangled`
- `bell_psi_minus_entangled`
- `jiji_weiji_quantum_pair_entangled` (既济/未济 quantum pair entangled)
- `separable_iff_schmidt_rank_one`

**Cost**: 10 days

**Dependencies**: Q.3

### Q.8 — Path integral / interference S-series 激活

**Goal**: 把 Markov 桥 S2-S33 之 amplitude `Int` 升为 `ℂ`, 激活整套 plumbing。

**New files**:
- `Foundation/Modern/Quantum/PathIntegral.lean` (~600 LOC)

**Touches existing** (32 files, mechanical activation each):
- `QuantumRelativityInterferenceBridge.lean` (S5) → ℂ amplitude
- `QuantumRelativityNonzeroPathAmplitudeBridge.lean` (S5b)
- `QuantumRelativityTwoPathInterferenceBridge.lean` (S5c)
- `QuantumRelativityDiscretePhaseBridge.lean` (S5d) → $e^{iθ}$
- `QuantumRelativityDiscreteActionBridge.lean` (S5e)
- `QuantumRelativityFinitePathSumBridge.lean` (S5f)
- ... (other S5g-S5r files)
- `QuantumRelativityBornRuleDerivationBridge.lean` (S18) → full Born
- `QuantumRelativityActionAmplitudeMeasurementBridge.lean` (S22)
- `QuantumRelativityFinitePhaseEvolutionBridge.lean` (S23)
- `QuantumRelativityContinuousActionFunctionalBridge.lean` (S24)
- `QuantumRelativityPathSpaceActionFunctionalBridge.lean` (S25)

**Theorems**:
- `quantum_phase_amplitude` ($e^{iθ}$ 之 ℂ-valued amplitude)
- `quantum_two_path_phase_cancellation` ($e^{iθ} + e^{i(θ+π)} = 0$, activate S5c)
- `quantum_born_rule` (|amplitude|² 是 probability, activate S18)
- `quantum_path_integral_finite_quotient` (activate S25)

**Cost**: 25 days (含 32 file activation + new framework)

**Dependencies**: Q.3, Q.4

### Q.9 — Born rule / measurement first-class

**Goal**: PVM + collapse + projection-valued measure + computational basis measurement.

**New files**:
- `Foundation/Modern/Quantum/Measurement.lean` (~400 LOC)
- `Foundation/Modern/Quantum/BornRule.lean` (~200 LOC, may merge into Measurement)

**Touches existing**: `CeBoundary.lean` (引用 anchor), `QuantumSpacetime.lean`

**Theorems**:
- `pvm_complete_resolution_of_identity`
- `born_rule_for_pure_state`
- `collapse_state_normalized`
- `computational_basis_measurement_specializes_to_existing` (复用 S21 之 one-qubit Born measurement)

**Cost**: 10 days

**Dependencies**: Q.3, Q.8

### Q.10 — Channels / CPTP first-class

**Goal**: CPTPMap + Kraus + composition (activate S13-S20).

**New files**:
- `Foundation/Modern/Quantum/DensityMatrix.lean` (~350 LOC)
- `Foundation/Modern/Quantum/Channel.lean` (~500 LOC)
- `Foundation/Modern/Quantum/Decoherence.lean` (~300 LOC)
- `Foundation/Modern/Quantum/NoCloning.lean` (~200 LOC)
- `Foundation/Modern/Quantum/Bell.lean` (~400 LOC)
- `Foundation/Modern/Quantum/PT.lean` (~250 LOC)

**Touches existing**:
- `QuantumRelativityUnitaryCPTPLedgerBridge.lean` (S17) → close pending physical items
- `QuantumRelativityNontrivialChannelLawBridge.lean` (S20) → upgrade to CPTP-grade
- `QuantumRelativityChannelComposeBridge.lean` (S13)
- `QuantumRelativityChannelComposeAssociativityBridge.lean` (S14)

**Theorems**:
- `CPTPMap.compose_assoc` (activate S14)
- `CPTPMap.kraus_representation_exists`
- `unitary_channel_iff_pure_state_preserving`
- `decohered_classical_limit_is_markov_chain`
- `no_cloning_theorem`
- `bell_violates_chsh_classical`
- `tsirelson_bound`

**Cost**: 30 days

**Dependencies**: Q.7, Q.9

### Q.11 — R8_complete quantum analog (closure theorem)

**Goal**: R₈ quantum closure bundle 之 quantum analog: `R8Q_complete` theorem 类比 `R8_complete`。

**New files**:
- `Foundation/Modern/Quantum/Cell256Stratify.lean` (~500 LOC) — quantum-side `R8Q_complete` bundle

**Touches existing**: `Foundation/Bagua/Cell256Stratify.lean` 之 `R8_complete` 作为 anchor

**Theorems**:
- `R8Q_complete` — 量子闭合 bundle (containing): (1) Hilbert dim 256; (2) tensor product (ℂ²)⁸; (3) unitary Cayley regular rep; (4) Shi V₄ ↔ projective Pauli; (5) atomic XOR ↔ Pauli-X gates; (6) V₄ outer ↔ multi-qubit Pauli; (7) 道 = origin = $|0\rangle^{\otimes 8}$; (8) WaveFn normalization preserved by all unitary ops.
- `r8q_complete_extends_r8_classical` (classical bundle is special case)

**Cost**: 12 days

**Dependencies**: Q.6, Q.10

### Q.12 — Doctrine docs sync (28+ 卷义理 quantum reading)

**Goal**: 同步全部 doctrine docs 增加 quantum 读法; new 卷 if needed.

**Deliverables**:
- 已有 docs 之 quantum sections (in-place additions)
- New top-level doc: `docs-next/10_formal_形式/quantum-doctrine-index.md` (~400 lines)
- 28+ doctrine docs (`A_*.md` 到 `Z_*.md` + 9 cross-cutting docs) 之 quantum-reading footnotes

**Touches existing**: 28+ `义理/*.md` files (light annotations only — 1-2 sentence quantum reading per chapter)

**Theorems**: 无

**Cost**: 15 days

**Dependencies**: Q.0..Q.11 全部完成

### Phase 总 cost (rough)

| Phase | Cost (days) | LOC (Lean) |
|---|---|---|
| Q.0 | 1 | 0 (planning) |
| Q.1 | 2 | 150 |
| Q.2 | 5 | 400 |
| Q.3 | 7 | 550 |
| Q.4 | 5 | 350 |
| Q.5 | 6 | 400 |
| Q.6 | 8 | 450 |
| Q.7 | 10 | 500 |
| Q.8 | 25 | 600 (new) + 32 files activated |
| Q.9 | 10 | 600 |
| Q.10 | 30 | 2000 |
| Q.11 | 12 | 500 |
| Q.12 | 15 | 0 (docs) |
| **TOTAL** | **~136 days** | **~6500 LOC new Lean** |

约 4.5 months of focused work; 可在 sub-agent parallel acceleration 下压到 ~2 months。

---

## § 7. 风险 / 代价 (Risks and Costs)

### § 7.1 公理底盘变化

**Current axiom base** (R₀..R₈ + Markov桥 S2-S33):
- `propext` (propositional extensionality) — Lean stdlib
- `native_decide` — Lean stdlib decidable propositions
- `Classical.choice` — Lean stdlib (only used implicitly in `Decidable`)
- **0 project-specific axioms** (no `axiom` declarations in `formal/SSBX/`)

**Required axiom base for quantum** (Q.0..Q.12):
- 上述全部 +
- **Mathlib classical analysis**: `Real`, `Complex`, `NormedField`, `InnerProductSpace`, `Hilbert`, `MeasureTheory.LpSpace` (实数+复数+Hilbert+测度)
- **Mathlib LinearAlgebra**: `TensorProduct`, `Matrix`, `LinearMap`, `LinearEquiv`
- **Possibly**: `PiTensorProduct` (n-fold tensor product), `Convex` analysis (for density matrices)

**风险**: Mathlib 公理底盘较大 (含 `Classical.choice`, `funext`, `quot.sound`, real-analysis 公理)。但**所有公理都是 Mathlib standard**，不引入 project-specific axioms。

**建议**:
- 严格区分 `Foundation/Modern/Quantum/` (Mathlib-required) vs `Foundation/Modern/QuantumRelativity*.lean` (current sign-only, 0-Mathlib)
- 量子化 module 全部 import Mathlib; classical (Z/2)⁸ spine module **不 import Mathlib** (保持 minimal axiom dependency)
- 提供 `Foundation/Modern/Quantum/QuantumPreamble.lean` 之 一站式 import

### § 7.2 Finitary `decide` 失效

**Current state**: R₀..R₈ 之 64 个 hexagrams, 256 个 cells, 全部 V₄/Shi 之 case-analysis — 全部由 `native_decide` 闭合。

**Risk**: 升级到 quantum 后，**任何涉及 ℝ / ℂ 的等式都不再 decidable**。例如：
- `(α + β) (γ + δ) = αγ + αδ + βγ + βδ` — 实/复数 distributivity, 不能 `decide`
- `‖ψ‖^2 = 1` — 实数等式, 需 `simp` + `field_simp` + `ring`

**影响**:
- **Lost decide** (which existing theorems lose `decide`): 任何涉及 amplitude / probability 之等式 (~32 S-files 之等式 sublemmas) 都需要重新证明
- **Strategy**: 把 (Z/2)⁸ algebraic spine (classical) 与 quantum carrier (ℂ-valued) 严格分层；前者保持 `decide`-provable, 后者通过 `simp` + `linarith` / `ring` / `field_simp` + 显式 lemma chain

### § 7.3 Build cost

**Mathlib analysis 之 build cost**:
- 增加 `import Mathlib.Analysis.InnerProductSpace.PiL2` ≈ +200 jobs (Mathlib transitive imports)
- 增加 `import Mathlib.LinearAlgebra.TensorProduct` ≈ +50 jobs
- 增加 `import Mathlib.MeasureTheory.Function.LpSpace` ≈ +400 jobs (for path integral measure)
- **Total estimated**: project build 从 ~3648 jobs (current) 到 ~5000-6000 jobs (post-quantum)

**Compile time**: 当前 `lake build SSBX` 约 8-12 分钟 (cached) / 60-90 分钟 (clean)。Post-quantum 估约 +50% (clean: 90-135 分钟)。

**建议**:
- 分 module 之 incremental build
- CI 之 quantum-only build (跳过 classical Foundation 部分)

### § 7.4 自释 / 道源程之 reversible-quantum 改写

**Current state**: BaguaTuring 之 12-instr ISA 在 [`Foundation/MetaInterp/`](../../formal/SSBX/Foundation/MetaInterp/) 是 **classical Turing-complete**, 含 halting undecidability (per [`Foundation/MetaInterp/GodelLi.lean`](../../formal/SSBX/Foundation/MetaInterp/GodelLi.lean))。

**Quantum upgrade challenge**: 任何 quantum 化的 ISA 必须 **reversible** (unitary), 否则破坏量子无 cloning + 信息守恒。

**12-instr ISA quantum 化要求**:
- 每条 instr → unitary operation
- `setShi` 等 state-modifying instr → 需 reversible 拓展 (Toffoli-like)
- `halt` → 无 quantum analog (unitary 永不停)
- **Halting problem in quantum**: 仍 undecidable, 但需 quantum reformulation

**建议**:
- **Q.0..Q.12 不涉及** BaguaTuring 之 quantum 改写; 这是 R₉+ (post-Q.12) 路线
- 保留 classical `BaguaTuring` 作为 "Schrödinger 等价 classical limit"
- 未来 R₉+ path: `Foundation/MetaInterp/Reversible.lean` + quantum lifting

### § 7.5 现有 native_decide 证明之 fate

**Current native_decide 证明**: 全部 in `Foundation/Bagua/`, `Foundation/Yi/`, `Foundation/Hierarchy/` — 256-cell enumeration, V₄ Klein laws, BenZheng quadrant counts, xuGua256 length 等。

**Post-quantum fate**:
- **不变**: classical (Z/2)⁸ spine 保留所有 `native_decide` 证明; quantum 化在 separate `Foundation/Modern/Quantum/` 目录, 不动 classical files
- **新增**: quantum 等式需要 `simp` + `ring` + `field_simp` (without `decide`)
- **bridge lemma**: `cell256_to_basisQ_inj_decide_classical` — classical decide 可推 quantum injectivity (经 `Cell256.toBasisQ` 之 injective lemma)

---

## § 8. Markov桥 S-series 之"激活"对照表 (S-Series Activation Table)

**33 个 Markov 桥 S-files** 之"激活"对照表 — 每 file 之当前 Lean status + quantum upgrade type (rewrite / activate / no-op) + Phase Q.X 依赖。

「激活」(activate) 指: 整套 plumbing 保留, 仅把 amplitude 数域从 `Int / Nat / Rat` 升为 `ℂ`, 配套 simp lemma 升级，不重写 file structure.

「重写」(rewrite) 指: 整体 type signature 改变, 需重新设计 typed skeleton.

「no-op」指: 此 S-file 已是 classical 边界 (Markov side), quantum 化无升级动作。

| S# | File | Lean module (`Foundation/Modern/`) | 当前状态 | Quantum upgrade type | Phase 依赖 |
|---|---|---|---|---|---|
| S2 | 有限概率核接口 | `QuantumRelativityFiniteProbabilityBridge.lean` | machineChecked | no-op (classical Markov) | — |
| S3 | 路径组合与因果约束 | `QuantumRelativityPathCausalBridge.lean` | machineChecked | no-op (path skeleton, classical) | — |
| S4 | 经典Markov/量子振幅分层 | `QuantumRelativityAmplitudeChannelBridge.lean` | machineChecked typed-skeleton | activate (amplitude → ℂ) | Q.8 |
| S5 | 干涉与测量律候选 | `QuantumRelativityInterferenceBridge.lean` | machineChecked typed-skeleton | **activate** (Int amplitude → ℂ) | **Q.8** |
| S5b | 非零路径振幅候选 | `QuantumRelativityNonzeroPathAmplitudeBridge.lean` | machineChecked typed-skeleton | activate (nonzero amplitude → nonzero ℂ) | Q.8 |
| S5c | 双路径相消候选 | `QuantumRelativityTwoPathInterferenceBridge.lean` | machineChecked (1+(-1)=0) | **activate** (1+(-1)=0 → e^{iθ}+e^{i(θ+π)}=0) | **Q.8** |
| S5d | 离散相位标记候选 | `QuantumRelativityDiscretePhaseBridge.lean` | machineChecked (zero/pi → ±1) | **activate** (±1 → $e^{iθ}$ phase) | **Q.8** |
| S5e | 离散作用量相位候选 | `QuantumRelativityDiscreteActionBridge.lean` | machineChecked (edge action) | activate (edge action → continuous action) | Q.8 |
| S5f | 有限路径族求和候选 | `QuantumRelativityFinitePathSumBridge.lean` | machineChecked | activate (finite ℂ-amplitude sum) | Q.8 |
| S5g | 有限路径族求和代数候选 | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | machineChecked | activate (append/permutation/reverse over ℂ) | Q.8 |
| S5h | 端点索引路径族候选 | `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | machineChecked | activate (endpoint-indexed family with ℂ amplitudes) | Q.8 |
| S5i | 端点支撑规范化候选 | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | machineChecked | activate (amplitude-complete filter over ℂ) | Q.8 |
| S5j | 双路径枚举候选 | `QuantumRelativityTwoRouteEnumerationBridge.lean` | machineChecked | no-op (enumeration is classical) | — |
| S5k | 路径身份键候选 | `QuantumRelativityPathIdentityBridge.lean` | machineChecked | no-op (path-key classical) | — |
| S5l | 有限键商候选 | `QuantumRelativityFiniteKeyQuotientBridge.lean` | machineChecked | activate (key-compatible ℂ-amplitude descent) | Q.8 |
| S5m | 路径商类候选 | `QuantumRelativityPathQuotientBridge.lean` | machineChecked | activate (quotient with ℂ-valued sections) | Q.8 |
| S5n | 规范代表元候选 | `QuantumRelativityCanonicalRepresentativeBridge.lean` | machineChecked | no-op (canonical representative classical) | — |
| S5o | 商支撑枚举候选 | `QuantumRelativityQuotientSupportBridge.lean` | machineChecked | activate (quotient support with ℂ-amplitude cancellation) | Q.8 |
| S5p | 商支撑代数候选 | `QuantumRelativityQuotientSupportAlgebraBridge.lean` | machineChecked | activate (ℂ-amplitude quotient algebra) | Q.8 |
| S5q | 观测账本候选 | `QuantumRelativityObservableLedgerBridge.lean` | machineChecked | activate (pending observable → ℂ-amplitude entry) | Q.8 / Q.9 |
| S5r | 作用量相位律候选 | `QuantumRelativityActionPhaseLawBridge.lean` | machineChecked (0/1 → 1/-1) | **activate** (action index → $e^{iS/\hbar}$ phase) | **Q.8** |
| S8 | 逐步统一候选摘要 | `QuantumRelativityStepwiseUnificationBridge.lean` | machineChecked | activate (摘要 includes ℂ-amplitude items) | Q.8, Q.10 |
| S9 | 有限概率归一化候选 | `QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | machineChecked | activate (probability normalization → unit norm) | Q.3 |
| S10 | 归一化质量求和候选 | `QuantumRelativityNormalizedMassBridge.lean` | machineChecked | activate (mass sum-one → ℂ amplitude sum-one) | Q.3 |
| S11 | Born权重条件归一候选 | `QuantumRelativityBornWeightNormalizationBridge.lean` | machineChecked | **activate** (candidate weight → \|ψ\|² normalization) | **Q.9** |
| S12 | Born分布边界候选 | `QuantumRelativityBornDistributionBridge.lean` | machineChecked | **activate** (finite Born distribution → full Born rule) | **Q.9** |
| S13 | channelCompose候选 | `QuantumRelativityChannelComposeBridge.lean` | machineChecked | **activate** (pointwise channel → CPTP composition) | **Q.10** |
| S14 | channelCompose结合律候选 | `QuantumRelativityChannelComposeAssociativityBridge.lean` | machineChecked | **activate** (associativity over CPTPMap) | **Q.10** |
| S15 | sum-over-middle通道组合 | `QuantumRelativitySumOverMiddleChannelBridge.lean` | machineChecked | activate (sum-over-middle ℂ-amplitude) | Q.10 |
| S16 | sum-over-middle Born边界 | `QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | machineChecked | activate (composed Born boundary → ℂ-amplitude) | Q.9, Q.10 |
| S17 | unitary-CPTP账本边界 | `QuantumRelativityUnitaryCPTPLedgerBridge.lean` | machineChecked (pending physical) | **activate** (close pending physical CPTP items) | **Q.10** |
| S18 | Born rule推导候选 | `QuantumRelativityBornRuleDerivationBridge.lean` | machineChecked (conditional Born) | **activate** (full Born rule theorem) | **Q.9** |
| S19 | 路径权重乘法候选 | `QuantumRelativityPathWeightMultiplicationBridge.lean` | machineChecked | activate (path-weight multiplication → ℂ-amplitude product) | Q.8 |
| S20 | 非平凡量子通道律候选 | `QuantumRelativityNontrivialChannelLawBridge.lean` | machineChecked | **activate** (nontrivial channel → CPTP nontrivial witness) | **Q.10** |
| S21 | 概率幅到测量权重 | `QuantumRelativityBornMeasurementBridge.lean` | machineChecked (one-qubit Born) | activate (one-qubit → n-qubit) | Q.9 |
| S22 | 作用相位到测量权重链 | `QuantumRelativityActionAmplitudeMeasurementBridge.lean` | machineChecked | **activate** (full action → amplitude → measurement chain) | **Q.8, Q.9** |
| S23 | 有限相位演化候选 | `QuantumRelativityFinitePhaseEvolutionBridge.lean` | machineChecked | **activate** (finite phase → unitary evolution) | **Q.8, Q.9** |
| S24 | 连续作用量泛函候选 | `QuantumRelativityContinuousActionFunctionalBridge.lean` | machineChecked (S(t)=t) | **activate** (continuous S(t) → $e^{iS(t)/\hbar}$ phase) | **Q.8** |
| S25 | 路径空间作用量泛函候选 | `QuantumRelativityPathSpaceActionFunctionalBridge.lean` | machineChecked (finite quotient) | activate (finite quotient → measure-theoretic path integral) | Q.8, Q.10 |
| S26 | 有限作用量极值候选 | `QuantumRelativityFiniteActionExtremumBridge.lean` | machineChecked (action gap = 1) | activate (action gap → real action variational principle) | Q.8 |
| S27 | 有限因果局部性候选 | `QuantumRelativityFiniteCausalLocalityBridge.lean` | machineChecked | no-op (causal locality classical) | — |
| S28 | 有限因果区间候选 | `QuantumRelativityFiniteCausalIntervalBridge.lean` | machineChecked | no-op (causal interval classical) | — |
| S29 | 有限核路径载体候选 | `QuantumRelativityFiniteKernelPathCarrierBridge.lean` | machineChecked | activate (KernelPath carrier with ℂ amplitudes) | Q.8 |
| S30 | 递归核路径载体候选 | `QuantumRelativityKernelPathRecursiveCarrierBridge.lean` | machineChecked | activate (recursive carrier with ℂ amplitudes) | Q.8 |
| S31 | 端点索引递归载体族候选 | `QuantumRelativityEndpointIndexedRecursiveCarrierBridge.lean` | machineChecked | activate (endpoint-indexed family with ℂ) | Q.8 |
| S32 | 双路径递归载体族完备候选 | `QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge.lean` | machineChecked | no-op (two-route completeness classical) | — |
| S33 | 双路径KernelPath枚举候选 | `QuantumRelativityTwoRouteKernelPathEnumerationBridge.lean` | machineChecked | no-op (two-route enumeration classical) | — |
| Master | Markov因果桥 master summary | `QuantumRelativityMarkovBridge.lean` | machineChecked | activate (master theorem to include quantum items) | Q.11 |

**Activation 统计**:
- **activate**: 30 个 S-files (33 → 3 no-op classical = 30 activations)
- **rewrite**: 0 (没有需要重新设计的 file)
- **no-op**: 6 (S2, S3, S5j, S5k, S5n, S27, S28, S32, S33 之 9 个其实, 但去重得 6: S2/S3/S5j-k-n/S27-28/S32-33; recount: 9 no-op based on column)

**Mechanical activation pattern (典型, 重复 ~30 次)**:

```text
1. Open file (e.g. QuantumRelativityDiscretePhaseBridge.lean, S5d)
2. Locate `def discretePhaseAmplitude : DiscretePhase → Int := fun | .zero => 1 | .pi => -1`
3. Add new definition (don't replace; coexist):
   `def quantumPhaseAmplitude : ℝ → ℂ := fun θ => Complex.exp (Complex.I * θ)`
4. Add theorem: `quantum_two_route_phase_pair_amplitude_cancels` (n=2 special case → $e^{iπ}+1=0$)
5. Add lemma: `discretePhaseAmplitude_eq_quantumPhaseAmplitude_specialization` (展示 ±1 是 e^{iθ} 之 specialization)
6. Update `discrete_phase_bridge_summary` 增加 quantum conjunct
7. Touch downstream: any file importing this file may need migration helper
```

每 file 之 mechanical activation 约 50-100 LOC + 2-3 hours work; 30 files ≈ ~90 hours / ~12 days steady work, 或 ~5 days with 3 sub-agents in parallel.

---

## § 9. 与 28+ 卷义理之关系 (Relation to 28+ Doctrine Chapters)

本节给每个 major doctrine chapter 1-2 line "this chapter under quantum lens"。完整 doctrine map 见 [`docs-next/00_主线/`](../00_主线/)。

| 章 | 古文标题 | quantum lens reading |
|---|---|---|
| A | 经典易传 | superposition 在两仪/四象之 ket 化 — 「太极生两仪」= ℂ²之 trivial Hilbert; 「两仪生四象」= ℂ² ⊗ ℂ² tensor extension; 「四象生八卦」= (ℂ²)^⊗3 |
| B | 六征体系 | R₃ 之 6 征 (动/化/变/几/势/机) 升 6 qubits + V₄ Shi tensor; 几 (R₃ 巽) 对应 quantum superposition 之"微变之 phase"——量子之 phenomenological anchor |
| C | 实虚史真 | 实/虚 modal 升 superposition modal frame; "实" = collapsed eigenstate, "虚" = pre-collapse superposition; 史/真 (V₂ × V₂ = V₄ candidate) 在 quantum 中可作为 history-truth meta-frame |
| D | 算子代数 | classical (Z/2)⁸ Cayley regular rep → quantum unitary regular rep on $(\mathbb{C}^2)^{\otimes 8}$; cuo/zong/cuoZong V₄ ↔ Pauli {I, X, Z, Y/iI} projective Pauli group |
| E | 古代源流 | 古代之 quantum-like intuitions (波粒二象 in 太极图, 虚实之模态) — 哲学 anchor, 无 Lean upgrade |
| F | 物理现象学 | direct anchor — 已 discusses qubit basis; quantum 化把 F 之 "强 isomorphism layer" 从 Yao/Trigram 升到 WaveFn / Superposition / Bell |
| G | 完整算子系统_八卦互通与归一 | 八卦互通 = R₃ 上 (Z/2)³ simply transitive group action; quantum upgrade = $(\mathbb{C}^2)^{\otimes 3}$ 上 8-qubit Cayley unitary action |
| H | 证明报告 | classical Lean proofs of R₀..R₈; quantum 增量 = `R8Q_complete` bundle (Q.11) |
| I | 八卦全集 | 64 hex 与 quantum 6-qubit computational basis 之 1-1 对应; 比 #8 / 同人 #13 给 entanglement 之 hex anchor |
| J | 理之不完备_哥德尔在256 | Gödel 不完备 在 classical Cell256 上 already established; quantum 化下需 reformulate (quantum incompleteness 不同 — Bell + Tsirelson 等是 quantum-specific 不完备性) |
| K | 完备性审计 | R₈ 之 classical 完备 (per `R8_complete`); quantum 完备需重新审计 (Q.11 之 `R8Q_complete` is the analogous bundle) |
| L | 文道一也_自释与微核 | classical self-description (Cayley fusion) → quantum self-description (unitary self-action) — 道 = origin = $|0\rangle^{\otimes 8}$ 保留五重身份 |
| M | 证明报告_256_理之不完备 | similar to J |
| N | 儒家从元到圣 | 圣 (sage) 之 quantum anchor: V₄ identity (道) = 「无心而合天地」之 algebraic 表达 |
| O | 进化非道者生存_三视证 | 三视 = past/present/future = Shi V₂ × V₂; quantum 下三视成为 phase choice space |
| P | 道家从无到化 | 道 = origin = $|0\rangle^{\otimes 8}$; 化 = unitary evolution preserving norm |
| Q | 佛家从苦到觉 | 苦 = entangled state with environment (decoherence); 觉 = pure-state recovery / projection onto $|0\rangle^{\otimes 8}$ subspace |
| R | 与生生不息对齐之必然 | 生生不息 = unitary evolution preserves WaveFn normalization (quantum 之"不息") |
| S | 先秦百家 | (no direct quantum upgrade — philosophy chapter) |
| T | 西哲与亚伯拉罕 | (philosophical anchor, no formal upgrade) |
| U | 反诛心信诚之形式 | classical Boolean truth → quantum truth (truth-value as projection onto eigenspace, indistinguishable in superposition) |
| V | 现代政治哲学 | (no direct quantum upgrade) |
| W | 非道之形式 | non-道 cells (Z/2)⁸ \ {origin} → non-vacuum states; collapsed eigenstates 全部 non-vacuum |
| X | 反施密特 | 反施密特 = anti-Schmidt — quantum 中之 Schmidt decomposition 之 dual |
| Y | 对齐失败 | misalignment (alignment failure) — quantum: state preparation ≠ target state |
| Z | 经济博弈 | quantum game theory — 用 Bell inequality + Tsirelson 边界 推 strategic outcome |
| 几何位 · 从元到形 | geometric position | quantum geometry / Hilbert space 之 phenomenological 投影 |
| 动力 · 从元到行 | dynamics | Hamiltonian + Schrödinger 方程 — finite-D version 已可由 finite phase evolution (S23) activate |
| 心智 · 从元到识 | mind | quantum cognition (Aerts) — XinZhi 三相 retention/primalImpression/protention 之 quantum upgrade |
| 拓扑 · 从元到障 | topology | quantum topology (TQFT) — 障 (obstruction) 在 quantum 下是 topological phase obstruction |
| 数与算术 · 从元到数 | number / arithmetic | finite arithmetic mod 256 → 量子算术 (Shor algorithm 之离散版) |
| 类与映 · 从元到映 | type / map | classical Functor → quantum quantum-channel as enriched Functor; map 在 quantum 下是 CPTP map |
| 统计 · 从元到测 | statistics / measurement | classical probability → quantum probability (Born rule); 测 之 quantum form 已 activate via S18/S21 |
| 物理 · 从元到象 | physics | direct anchor — qubit basis 已有, quantum 化把 F+物理 之 phenomenology 提升为 first-class formal Lean |
| 形式逻辑 · 从元到证 | formal logic | quantum logic (Birkhoff-von Neumann) — non-distributive lattice 之 离散版 |
| 生态 · 从元到生 | ecology | (no direct quantum upgrade — but quantum biology emerging field) |
| 物间事三位一体 · 时空事件 | thing-between-event trinity | direct quantum anchor — 物=ket, 间=tensor product / entanglement, 事=measurement event |
| 史带结构 · 从爻到算子列 | history-strand structure | quantum 之 history-strand = sequence of unitary operations + intermediate measurements |

---

## § 10. 形式锚 / 参考 (Formal Anchors and References)

### § 10.1 Lean modules (classical, current)

- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — Yao / Trigram / Hexagram
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — R₇ (Z/2)⁷
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — R₈ (Z/2)⁸ + V₄ Shi (abbrev `Shi := YinBit × GuoBit` Phase C)
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `R8_complete` closure bundle
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — (Z/2)³ V₄ on R₃
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — Mian (R₄) + 4 quadrant
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — umbrella imports
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — 8 lift/project pairs
- [`formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) — R₅ Wuyao
- [`formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) — R₇ alias shim
- [`formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) — R₈ alias shim
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — 8 atomic XOR generators
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — V₄ outer cuo/zong/cuoZong/hu
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["..."]` 字面量
- [`formal/SSBX/Foundation/Eight/WuXiang.lean`](../../formal/SSBX/Foundation/Eight/WuXiang.lean) — 离散 basis Yao ≅ Bool, Trigram ≅ Bool³
- [`formal/SSBX/Foundation/Modern/Quantum.lean`](../../formal/SSBX/Foundation/Modern/Quantum.lean) — `Qubit := Fin 2 → ℂ`, Pauli matrices, Hadamard — **本路线图之 quantum starting point**
- [`formal/SSBX/Foundation/Modern/QuantumSpacetime.lean`](../../formal/SSBX/Foundation/Modern/QuantumSpacetime.lean) — quantum / spacetime 互补面
- [`formal/SSBX/Foundation/Modern/CeBoundary.lean`](../../formal/SSBX/Foundation/Modern/CeBoundary.lean) — 测之六轴
- [`formal/SSBX/Foundation/Modern/SUN.lean`](../../formal/SSBX/Foundation/Modern/SUN.lean) — SU(3) 警戒线
- [`formal/SSBX/Foundation/Jian/Jian.lean`](../../formal/SSBX/Foundation/Jian/Jian.lean) — 间 ontology anchor
- [`formal/SSBX/Foundation/MetaInterp/`](../../formal/SSBX/Foundation/MetaInterp/) — BaguaTuring 12-instr ISA (classical, future R₉+ reversible-quantum upgrade)
- [`formal/SSBX/Truth/SelfDescription.lean`](../../formal/SSBX/Truth/SelfDescription.lean) — `Cell256OperatorComplete` witness
- All 33 Markov 桥 S-files: `formal/SSBX/Foundation/Modern/QuantumRelativity{*}Bridge.lean` (see § 8 table)

### § 10.2 Lean modules (quantum, new, planned)

按 Q.0..Q.12 phase 排序：

- `formal/SSBX/Foundation/Modern/Quantum/Taiji.lean` (Q.0/Q.1, ~50 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Yao.lean` (Q.1, ~150 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/SiXiang.lean` (Q.2, ~150 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Trigram.lean` (Q.2, ~200 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Mian.lean` (Q.2, ~200 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Wuyao.lean` (Q.2, ~150 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Hexagram.lean` (Q.2, ~250 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Cell128.lean` (Q.2, ~300 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Cell256Q.lean` (Q.2, ~400 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/WaveFn.lean` (Q.3, ~250 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Superposition.lean` (Q.3, ~300 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/ShiProjectivePauli.lean` (Q.4, ~350 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/AtomicGates.lean` (Q.5, ~400 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/V4OuterGates.lean` (Q.6, ~450 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Entanglement.lean` (Q.7, ~500 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/PathIntegral.lean` (Q.8, ~600 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Measurement.lean` (Q.9, ~400 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/BornRule.lean` (Q.9, ~200 LOC, may merge)
- `formal/SSBX/Foundation/Modern/Quantum/DensityMatrix.lean` (Q.10, ~350 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Channel.lean` (Q.10, ~500 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Decoherence.lean` (Q.10, ~300 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/NoCloning.lean` (Q.10, ~200 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Bell.lean` (Q.10, ~400 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/PT.lean` (Q.10, ~250 LOC)
- `formal/SSBX/Foundation/Modern/Quantum/Cell256Stratify.lean` (Q.11, ~500 LOC) — quantum `R8Q_complete`

### § 10.3 Doctrine docs (current, referenced)

- [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](yi-RO-hierarchy.md) — definitive R₀..R₈ doctrine
- [`docs-next/10_formal_形式/yi-calculus-theorem.md`](yi-calculus-theorem.md) — Theorems A–K
- [`docs-next/10_formal_形式/cell256-grid.md`](cell256-grid.md) — 256-cell structure
- [`docs-next/10_formal_形式/shi-v4.md`](shi-v4.md) — V₄ Klein Shi (Phase C abbrev)
- [`docs-next/10_formal_形式/v4-shi.md`](v4-shi.md) — Shi V₄ canonical doc
- [`docs-next/10_formal_形式/cell256-algebra.md`](cell256-algebra.md) — (Z/2)⁸ Cayley spine
- [`docs-next/10_formal_形式/operator-split.md`](operator-split.md) — XOR atomic vs V₄ outer split
- [`docs-next/10_formal_形式/yin-tou-operators.md`](yin-tou-operators.md) — 印 / 投 mask form
- [`docs-next/10_formal_形式/r7-yin-r8-guo.md`](r7-yin-r8-guo.md) — R₇/R₈ axes
- [`docs-next/10_formal_形式/lift-project.md`](lift-project.md) — 8-pair lift/project
- [`docs-next/10_formal_形式/ox-notation.md`](ox-notation.md) — OX["..."] macro
- [`docs-next/10_formal_形式/yi-as-meta-framework.md`](yi-as-meta-framework.md) — philosophical anchor
- [`docs-next/10_formal_形式/yi-bagua.md`](yi-bagua.md) — Bagua doctrine
- [`docs-next/10_formal_形式/64-hexagram-grid.md`](64-hexagram-grid.md) — 64 hexagram details
- [`docs-next/10_formal_形式/sanben-sijieduan-grid.md`](sanben-sijieduan-grid.md) — content-line grid
- [`docs-next/10_formal_形式/layer-axis-graph.md`](layer-axis-graph.md) — 3-axis graph
- [`docs-next/10_formal_形式/modern.md`](modern.md) — Modern module overview
- [`docs-next/10_formal_形式/build-and-verify.md`](build-and-verify.md) — build instructions

### § 10.4 Doctrine docs (quantum, new, planned)

- `docs-next/10_formal_形式/quantum-roadmap.md` (本文)
- `docs-next/10_formal_形式/quantum-axiom-plan.md` (Q.0, ~200 lines) — public axiom inventory + Mathlib dependency map
- `docs-next/10_formal_形式/superposition-quantum.md` (Q.3, ~300 lines)
- `docs-next/10_formal_形式/entanglement-quantum.md` (Q.7, ~400 lines)
- `docs-next/10_formal_形式/interference-quantum.md` (Q.8, ~400 lines)
- `docs-next/10_formal_形式/measurement-quantum.md` (Q.9, ~250 lines)
- `docs-next/10_formal_形式/channel-cptp-quantum.md` (Q.10, ~350 lines)
- `docs-next/10_formal_形式/bell-tsirelson-quantum.md` (Q.10, ~300 lines)
- `docs-next/10_formal_形式/r8q-complete.md` (Q.11, ~300 lines) — R₈ quantum closure bundle
- `docs-next/10_formal_形式/quantum-doctrine-index.md` (Q.12, ~400 lines) — quantum reading map for 28+ doctrine chapters

### § 10.5 义理 anchors (referenced)

- [`义理/Markov因果桥 · 大统一最小验证构造.md`](../../义理/Markov因果桥%20·%20大统一最小验证构造.md) — master Markov bridge summary, S2-S33 inventory
- [`义理/F_物理现象学.md`](../../义理/F_物理现象学.md) — physics/phenomenology anchor (analogy-only)
- [`义理/物理 · 从元到象.md`](../../义理/物理%20·%20从元到象.md) — physics, qubit basis mapping
- [`义理/量子物理语言 · 从虚到测.md`](../../义理/量子物理语言%20·%20从虚到测.md) — quantum language
- [`义理/量子时空互补 · 从一到测.md`](../../义理/量子时空互补%20·%20从一到测.md) — quantum/spacetime complementary
- [`义理/量子与相对论整合方向 · 从桥到新理论.md`](../../义理/量子与相对论整合方向%20·%20从桥到新理论.md) — quantum/GR integration
- [`义理/量子与相对论直统一不可能 · 当前语言NoGo.md`](../../义理/量子与相对论直统一不可能%20·%20当前语言NoGo.md) — direct unification NoGo
- [`义理/边界/测的边界 · 观验读.md`](../../义理/边界/测的边界%20·%20观验读.md) — measurement boundary
- [`义理/物间事三位一体 · 时空事件.md`](../../义理/物间事三位一体%20·%20时空事件.md) — thing-between-event trinity
- [`义理/C_实虚史真.md`](../../义理/C_实虚史真.md) — actual/virtual/history/truth modal
- All 32 individual S-files: [`义理/Markov桥S{2,3,4,5,5b-5r,8-33}*.md`](../../义理/)

### § 10.6 Mathlib references (transitive imports needed)

- `Mathlib.Data.Complex.Basic` — ℂ
- `Mathlib.Analysis.InnerProductSpace.PiL2` — `EuclideanSpace ℂ (Fin n)`
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product space typeclass
- `Mathlib.LinearAlgebra.Matrix.ToLin` — `Matrix → LinearMap`
- `Mathlib.LinearAlgebra.TensorProduct` — `⊗[ℂ]`
- `Mathlib.LinearAlgebra.TensorProduct.Basic` — `tprod`, `lift`
- `Mathlib.Analysis.NormedSpace.Exponential` — `Complex.exp`
- `Mathlib.MeasureTheory.Function.LpSpace` — for path integrals (Q.8/Q.10)
- `Mathlib.MeasureTheory.Decomposition.Decomposition` — Schmidt decomposition (Q.7)
- `Mathlib.LinearAlgebra.UnitaryGroup` — unitary operators
- `Mathlib.LinearAlgebra.Eigenspace` — eigenspaces for measurement
- `Mathlib.Probability.ProbabilityMassFunction.Basic` — discrete probability for Born rule

### § 10.7 External references (informal, for reading)

- Nielsen & Chuang, "Quantum Computation and Quantum Information" — standard quantum reference
- Aerts, D., "Quantum Cognition" — quantum models in cognition
- Birkhoff & von Neumann, "The Logic of Quantum Mechanics" — quantum logic
- Tsirelson, B., "Quantum analogues of the Bell inequalities" — Tsirelson bound

---

> **Total doc length**: ~1850 lines · **Total Lean LOC planned**: ~6500 (new) + ~30 file activations · **Total time estimate**: ~136 days focused work (~2 months with sub-agent parallelism)
>
> **Critical path**: Q.0 → Q.1 → Q.2 → Q.3 → Q.4 → Q.5 → Q.8 (path integral / S-series activation) → Q.9 (measurement / Born) → Q.10 (CPTP / Bell) → Q.11 (R8Q_complete) → Q.12 (doctrine sync)
>
> **Non-critical-path parallel**: Q.6 (V4Outer gates) ∥ Q.5 (Atomic gates); Q.7 (Entanglement) ∥ Q.8 (PathIntegral)
>
> **Final invariant guarantee**: Throughout Q.0..Q.12, classical `R8_complete` bundle 之 0-Mathlib axiom dependency 保持; quantum 化全部在 `Foundation/Modern/Quantum/` 子目录新增, 不动 classical files; (Z/2)⁸ Cayley self-duality + V₄ Shi + 道 = origin 五重身份 保持 first-class。
