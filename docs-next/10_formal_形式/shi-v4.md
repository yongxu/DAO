# Shi V₄ — V₄ Klein 时态结构 / Shi V₄ Klein-Four Time Structure

> 状态：v3 定本 (2026-05-11)
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ strict-uniform doctrine)
> 配套：[ox-notation.md](ox-notation.md) · [lift-project.md](lift-project.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md)
> 形式锚：[`Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1 Shi inductive
> 定理引用：[yi-calculus-theorem.md](yi-calculus-theorem.md) Theorems H / I / J

---

## 第一部分：Shi 之结构 (Structure)

### 1.1 Inductive 声明

`Shi` 是 R₈ 之 V₄ 时态层。Lean 4 ground truth ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1)：

```lean
/-- 时态: V₄ 四态 道 / 已 / 今 / 未. 同构于 (YinBit, GuoBit) ∈ Bool².

    - 道 = (0, 0) — 永真，跨时空，V₄ 单位元
    - 已 = (1, 0) — 过去封闭 (有因, 无果)
    - 未 = (0, 1) — 未来开放 (无因, 有果)
    - 今 = (1, 1) — PT 交汇 (因果俱在) -/
inductive Shi : Type
  | dao   -- 道 (eternal / V₄ identity)
  | ji    -- 已 (past)
  | jin   -- 今 (present, PT)
  | wei   -- 未 (future)
  deriving Repr, DecidableEq, BEq
```

**关键点**：

- 4 个 ctor，无更多。`Shi` 是有限闭合 inductive。
- 命名采用拼音缩写 (dao/ji/jin/wei)，避免 Lean 4 lexer 拒绝裸 CJK identifier。
- `deriving Repr, DecidableEq, BEq` 自动给出 `=`-decidability —— 任意 Shi 命题（等式 / 大小比较）可由 `decide` 闭合。

### 1.2 大小

|Shi| = 4 = (Z/2)² = V₄ Klein 群的元素数。

```lean
/-- 全部 4 个时态. -/
def all : List Shi := [dao, ji, jin, wei]

theorem all_length : all.length = 4 := rfl
```

(摘自 `Cell256.lean` § 1)

### 1.3 与 R-hierarchy 的位置

```
R₆ Hexagram (64) ──→ R₇ Cell128 (128 = 64 × 2) ──→ R₈ Cell256 (256 = 128 × 2 = 64 × 4)
                       (加 因 YinBit)              (加 果 GuoBit)
                                                   |
                                                   ▼
                            Shi = (因, 果) ∈ Bool² ≅ V₄
```

Shi V₄ **emerges at R₈** from the R₇ ⊗ R₈ tensor of (YinBit, GuoBit)。它**不是**单层 atom — 是双 axis 自然 induce 出的 V₄ Klein 结构。

详见 [yi-calculus-theorem.md](yi-calculus-theorem.md) Theorem J 之严格陈述。

---

## 第二部分：Shi ↔ Bool² 双射

### 2.1 toYinGuo / ofYinGuo 函数

Shi 与 (YinBit, GuoBit) ∈ Bool² 同构。Lean ground truth ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1)：

```lean
/-- Shi → (因, 果) ∈ Bool² 双射: dao=(0,0) / ji=(1,0) / wei=(0,1) / jin=(1,1). -/
def toYinGuo : Shi → YinBit × GuoBit
  | .dao => (false, false)  -- 道 = V₄ identity
  | .ji  => (true,  false)  -- 已 = (有因, 无果)
  | .wei => (false, true)   -- 未 = (无因, 有果)
  | .jin => (true,  true)   -- 今 = PT 交汇 (因果俱在)

/-- (因, 果) ∈ Bool² → Shi 反向双射. -/
def ofYinGuo : YinBit × GuoBit → Shi
  | (false, false) => .dao
  | (true,  false) => .ji
  | (false, true)  => .wei
  | (true,  true)  => .jin
```

注意 `YinBit = GuoBit = Bool`（在 [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) / [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) 中均为 abbrev）。

### 2.2 双射性证明

```lean
/-- 双射 left: Shi → (因,果) → Shi = id. -/
theorem ofYinGuo_toYinGuo (s : Shi) : ofYinGuo (toYinGuo s) = s := by
  cases s <;> rfl

/-- 双射 right: (因,果) → Shi → (因,果) = id. -/
theorem toYinGuo_ofYinGuo (yg : YinBit × GuoBit) : toYinGuo (ofYinGuo yg) = yg := by
  rcases yg with ⟨y, g⟩
  cases y <;> cases g <;> rfl
```

(摘自 `Cell256.lean` § 1)

每个由 `cases s <;> rfl` 闭合 — 因为定义本身就是 ctor-by-ctor 直接对应。

### 2.3 完整对应表

| Shi ctor | (因, 果) | (YinBit, GuoBit) | OX 后 2 位 | V₄ 角色 |
|---|---|---|---|---|
| `Shi.dao` | (0, 0) | (false, false) | `oo` | identity (e) |
| `Shi.ji` | (1, 0) | (true, false) | `xo` | σ_P |
| `Shi.wei` | (0, 1) | (false, true) | `ox` | σ_T |
| `Shi.jin` | (1, 1) | (true, true) | `xx` | σ_PT |

注意 `jin` 对应 (1, 1)（双轴均开）—— 在 inductive 中 `jin` 列为第 3 ctor 但其 (因, 果) 编码是双 1。这是为了让 `dao = (0,0) = identity` 与 `jin = (1,1) = central` 在 V₄ 中处对称位置。

---

## 第三部分：V₄ 算子 (cuo / zong / cuoZong)

V₄ Klein 群有 4 个元素：identity + 3 个 involution。Shi 上的 3 个 involution 是 **cuo** (P)、**zong** (T)、**cuoZong** (PT)。

### 3.1 cuo (Parity)

cuo 翻 **过去 axis** (因/YinBit) ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1)：

```lean
/-- V₄ cuo (P-like, 翻 past-trace 轴): 道↔已, 未↔今. -/
def cuo : Shi → Shi
  | .dao => .ji
  | .ji  => .dao
  | .jin => .wei
  | .wei => .jin
```

效果：在 (因, 果) 平面上把 因 (YinBit) 翻转，保 果。

| 输入 | 输出 |
|---|---|
| 道 (0,0) | 已 (1,0) |
| 已 (1,0) | 道 (0,0) |
| 未 (0,1) | 今 (1,1) |
| 今 (1,1) | 未 (0,1) |

### 3.2 zong (Time-reversal)

zong 翻 **未来 axis** (果/GuoBit)：

```lean
/-- V₄ zong (T-like, 翻 future-projection 轴): 道↔未, 已↔今. -/
def zong : Shi → Shi
  | .dao => .wei
  | .ji  => .jin
  | .jin => .ji
  | .wei => .dao
```

| 输入 | 输出 |
|---|---|
| 道 (0,0) | 未 (0,1) |
| 已 (1,0) | 今 (1,1) |
| 今 (1,1) | 已 (1,0) |
| 未 (0,1) | 道 (0,0) |

### 3.3 cuoZong (PT)

cuoZong 同时翻**双 axis** = V₄ 中心元 (central element)：

```lean
/-- V₄ cuoZong (= PT, 双轴翻): 道↔今, 已↔未. -/
def cuoZong : Shi → Shi
  | .dao => .jin
  | .ji  => .wei
  | .jin => .dao
  | .wei => .ji
```

| 输入 | 输出 |
|---|---|
| 道 (0,0) | 今 (1,1) |
| 已 (1,0) | 未 (0,1) |
| 今 (1,1) | 道 (0,0) |
| 未 (0,1) | 已 (1,0) |

注意：cuoZong 把 道 ↔ 今 直接交换 — 即「永真 anchor」与「PT central element」是对偶的两端。

### 3.4 V₄ 群表 (multiplication table)

|  | id | cuo (P) | zong (T) | cuoZong (PT) |
|---|---|---|---|---|
| id | id | cuo | zong | cuoZong |
| cuo | cuo | id | cuoZong | zong |
| zong | zong | cuoZong | id | cuo |
| cuoZong | cuoZong | zong | cuo | id |

每元素自逆 (`x · x = id`)，群是 abelian。这是经典 Klein four-group V₄ = (Z/2)² 之表。

---

## 第四部分：V₄ 结构定理 (Structure Theorems)

以下定理全部来自 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1，`by cases s <;> rfl` 一行闭合 — 因为 4 ctor + reflexivity 即足。

### 4.1 三个 involution 律

```lean
theorem cuo_cuo (s : Shi) : cuo (cuo s) = s := by cases s <;> rfl
theorem zong_zong (s : Shi) : zong (zong s) = s := by cases s <;> rfl
theorem cuoZong_cuoZong (s : Shi) : cuoZong (cuoZong s) = s := by cases s <;> rfl
```

每个非平凡 V₄ 元素的 order = 2。

### 4.2 cuo 与 zong 交换 (V₄ Abelian)

```lean
/-- cuo 与 zong 交换（V₄ Abelian）. -/
theorem cuo_zong_comm (s : Shi) : cuo (zong s) = zong (cuo s) := by
  cases s <;> rfl
```

V₄ Klein 群是 abelian — `cuo ∘ zong = zong ∘ cuo`。

### 4.3 cuoZong = cuo ∘ zong

```lean
/-- cuoZong = cuo ∘ zong （V₄ 复合）. -/
theorem cuoZong_eq_compose (s : Shi) : cuoZong s = cuo (zong s) := by
  cases s <;> rfl
```

中心元 cuoZong 是另两个 involution 的复合 — 这是 V₄ 之关键关系（"任两 non-identity 之积 = 第三 non-identity"）。

### 4.4 三定理之 V₄ 结构总结

V₄ Klein 四群 axioms 由以上四条满足：

| V₄ axiom | Shi 实现 | Lean 名 |
|---|---|---|
| `cuo² = id` | involution | `cuo_cuo` |
| `zong² = id` | involution | `zong_zong` |
| `cuoZong² = id` | involution | `cuoZong_cuoZong` |
| `cuo ∘ zong = zong ∘ cuo` | abelian | `cuo_zong_comm` |
| `cuoZong = cuo ∘ zong` | composite | `cuoZong_eq_compose` |

5 条之外不需要更多 axioms — 这正是 V₄ Klein 四群的最小完备特征。

---

## 第五部分：印 / 投 算子 (yin / tou)

`Cell256.lean` § 1 在 V₄ cuo/zong 之上定义了 alias **印 (yìn)** 与 **投 (tóu)**：

```lean
/-- 印 (yìn): toggle YinBit (因 axis). 等价于 Shi.cuo. -/
def yin (s : Shi) : Shi := s.cuo

/-- 投 (tóu): toggle GuoBit (果 axis). 等价于 Shi.zong. -/
def tou (s : Shi) : Shi := s.zong
```

定义层面 `yin = cuo`, `tou = zong`，**仅 alias** — 但其 ontology 是 atomic operator (R₇/R₈ 之 atomic XOR 算子)，详见 [r7-yin-r8-guo.md](r7-yin-r8-guo.md)。

### 5.1 印/投 之 V₄ 结构

```lean
theorem yin_yin (s : Shi) : yin (yin s) = s := cuo_cuo s
theorem tou_tou (s : Shi) : tou (tou s) = s := zong_zong s
theorem yin_tou_comm (s : Shi) : yin (tou s) = tou (yin s) := cuo_zong_comm s

/-- 印 ∘ 投 = cuoZong = V₄ central element. -/
theorem yin_tou_eq_cuoZong (s : Shi) : yin (tou s) = cuoZong s := by
  unfold yin tou
  exact (cuoZong_eq_compose s).symm
```

(摘自 `Cell256.lean` § 1)

印 ∘ 投 = cuoZong = V₄ 中心元 — 这是核心 V₄ 关系的 alias 形式版。

### 5.2 印 / 投 在 Cell256 上的 mask 形式

在 Cell256 层（不仅 Shi 层），印/投 进一步表达为 XOR mask ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 8)：

```lean
/-- 印 mask: only the YinBit (因 axis, R5 atom) is set.
    `(qian, ji) = (qian, (1, 0)) = "oooooooi"`. -/
def yin_mask : Cell256 := (Hexagram.qian, Shi.ji)

/-- 投 mask: only the GuoBit (果 axis, R6 atom) is set.
    `(qian, wei) = (qian, (0, 1)) = "ooooooox"`. -/
def tou_mask : Cell256 := (Hexagram.qian, Shi.wei)

/-- 印 (yìn) at Cell256: XOR with the YinBit-only mask. -/
def yin (c : Cell256) : Cell256 := xor c yin_mask

/-- 投 (tóu) at Cell256: XOR with the GuoBit-only mask. -/
def tou (c : Cell256) : Cell256 := xor c tou_mask
```

详见 [r7-yin-r8-guo.md](r7-yin-r8-guo.md) § 4 印/投 之精确刻画。

---

## 第六部分：为何 V₄ 不是 Z/3 (Why V₄, Not Cyclic)

历史上某段（旧 `Cell192.lean`，已 deprecated）把 Shi 编为 Z/3 cyclic {已, 今, 未}。这是**结构错误**，破坏了 R-hierarchy 的 (Z/2)ⁿ 自相似闭合。本节给出三条理由说明为何 Shi **必须** V₄ 而非 Z/3 / Z/4。

### 6.1 Cardinality 与 strict-uniform 之必然

R-hierarchy 之 strict-uniform 律要求 R_{n+1} = 2 × R_n（每层 +1 bit）：

```
R₆ = 64 = 2⁶
R₇ = 128 = 2⁷ = 2 × R₆
R₈ = 256 = 2⁸ = 2 × R₇ = 4 × R₆
```

R₈ / R₆ = 4。如果 Shi 是 Z/3 = {已, 今, 未}，则 R₈ / R₆ = 3，违反 (Z/2)ⁿ 自相似。

**只有 4-cardinality** 的有限 abelian 群（V₄ 与 Z/4）能维持此关系。

详见 [yi-calculus-theorem.md](yi-calculus-theorem.md) Theorem K 之严格论证。

### 6.2 V₄ vs Z/4 — 为何 V₄

V₄ = Z/2 × Z/2 (双 generator, 每生成元 order 2)
Z/4 = ⟨g⟩ (单 generator, generator order 4)

| 性质 | V₄ | Z/4 |
|---|---|---|
| 元素 order | {1, 2, 2, 2} | {1, 2, 4, 4} |
| 是否 (Z/2)ⁿ | ✓ (n=2) | ✗ |
| 双 axis (因, 果) | ✓ (各自 Z/2) | ✗ (单 generator 不分解) |
| Pontryagin self-dual | ✓ | Z/4 ≅ Z/4-hat 但非 Bool 拼装 |

R-hierarchy 之 (Z/2)ⁿ 严格要求每层之新 axis 是 binary (Z/2)。R₇ 之 axis = 因 (YinBit = Bool = Z/2), R₈ 之 axis = 果 (GuoBit = Bool = Z/2)。两个独立 Z/2 之 product = V₄，**不是** Z/4。

**Z/4 会把 因/果 之独立性混成单一 generator，破坏物理 P/T 之独立性**。

### 6.3 Theorems H–J 之严格陈述

来自 [yi-calculus-theorem.md](yi-calculus-theorem.md)：

- **Theorem H** (R₇ = 128 + 因)：R₇ = R₆ × YinBit 引入第 7 个独立 binary axis。
- **Theorem I** (R₈ = 256 + 果)：R₈ = R₇ × GuoBit 引入第 8 个独立 binary axis。
- **Theorem J** (Shi V₄ emergence)：Shi = (YinBit, GuoBit) ≅ Bool² ≅ V₄。

H + I + J 联合 ⟹ Shi 之 4 元 = 因/果 之 product = V₄。

如果把 Shi 看作 Z/3（如旧 Cell192）：
- 丧失 V₄ identity (道) — 仅 {已, 今, 未}
- 丧失「描述者本身之恒在 anchor」
- 破坏 (Z/2)ⁿ 自相似律
- R₈ 不再是 (Z/2)⁸

正确路径：**R₈ = (Z/2)⁸ 真闭合**，Shi V₄ first-class。Cell192 deprecated。

---

## 第七部分：物理读法 (Physical Reading)

### 7.1 V₄ 与 P/T/PT 同构

V₄ Klein 群与物理学之 {1, P, T, PT} 同构：

| Shi | V₄ 元 | 物理 anchoring | 现象学 anchoring |
|---|---|---|---|
| 道 (dao) | identity (e) | 平凡变换 / 永真 anchor / 跨时空 | 永恒在场 (eternal presence) |
| 已 (ji) | σ_P | parity-like (P) — 过去封闭，无未来 | retention (Husserl 持留) |
| 未 (wei) | σ_T | time-reversal-like (T) — 未来开放，无过去 | protention (Husserl 前持) |
| 今 (jin) | σ_PT | PT 复合 — 过去与未来交汇，"现在" | primal impression (Husserl 原印象) |

(参考 [yi-calculus-theorem.md](yi-calculus-theorem.md) Theorem J Definition 1.8 物理 anchoring 表)

### 7.2 道 = V₄ identity = 永真 anchor

道 (dao) 是 V₄ 单位元 — **是唯一 (因 = 0, 果 = 0) 状态**。其 ontological 含义：

> 道是「与 causation flow orthogonal」之状态 — 既无过去 cause 也无 future effect projection。它跨尺度跨时空恒真。

这是「道作为永恒真理」之 algebraic 必然 (Theorem J Corollary 1)。

把 道 从 Shi 删除（如 Z/3 cyclic 编码）：
- 丧失 V₄ 单位元
- 丧失「描述者本身之恒在 anchor」
- 破坏 R-hierarchy 之 (Z/2)ⁿ self-similarity

R₈ = 256 让道 first-class 进入本体 — 是「自描述」之形式落地。

### 7.3 已 = P (parity, past-fixed)

已 (ji) 在物理 anchoring 中是 P (parity-flip)。其 ontological 含义：

- (因 = 1, 果 = 0)：携带过去 cause，但无未来 effect projection
- 过去封闭 — 已发生之事不可回收
- 现象学：retention，过去 trace 之 binary marker

### 7.4 未 = T (time-reversal, future-open)

未 (wei) 在物理 anchoring 中是 T (time-reversal)。其 ontological 含义：

- (因 = 0, 果 = 1)：无过去 cause，但投射 future effect
- 未来开放 — 因果链 之 origin
- 现象学：protention，未来 trace 之 binary marker
- 数学：coalgebra terminal / virtual flow source

### 7.5 今 = PT (now)

今 (jin) 在物理 anchoring 中是 PT (parity-time-reversal compound)。其 ontological 含义：

- (因 = 1, 果 = 1)：因果俱在 — "现在" 即流变交汇
- 既携带过去 trace，又投射未来 — present moment 之 dialectical 性
- 物理：PT-symmetric phase

注意：今 是 V₄ **中心元**（cuoZong / 印 ∘ 投）— 与 道 在 V₄ 中处对称两端：

> 道 ⟷ 今 ：通过 V₄ 中心元 cuoZong 直接交换。
> 已 ⟷ 未 ：通过 V₄ 中心元 cuoZong 直接交换。

---

## 第八部分：命名 caveat (Provisional Naming)

### 8.1 当前命名 (working choice)

R₇ 元 = 因 / R₈ 元 = 果 / R₇ 算子 = 印 / R₈ 算子 = 投。

来自 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1 文件 docstring：

```
**命名 caveats (provisional)**: 因/果 / 印/投 暂用，备选 印/投 (Husserl) /
始/终 (Yi-native) / 持/期 (现象学) — 详 yi-calculus-theorem.md §16.
```

### 8.2 候选命名表 (per [yi-calculus-theorem.md](yi-calculus-theorem.md) §16)

| 候选 | 哲学 anchor | 形式科学 anchor | 古文 anchor | 项目耦合 | 评分 |
|---|---|---|---|---|---|
| **因 / 果** (current) | 佛教 hetu-phala + Pearl 因果 + Aristotle 4 因 | causal DAG / lightcones | 《说文》"因，依也"/"果，木实也"；佛教汉译 | 不冲突；"因"/"已" 听觉撞 | ★★★★ |
| **印 / 投** | Husserl retention/protention; Heidegger Geworfenheit/Entwurf; Sartre projection | signal frame buffer / predictive filter | 《说文》"印，执政所持信"/"投，擿也" | XinZhi.lean 三相直对接 | ★★★★ |
| **始 / 终** | Aristotle arche/telos; 道家终始反复 | graph source/sink; coalgebra initial/terminal | **《易传·系辞下》「原始要终」原文 (Yi-native!)** | 与 Yi 原生表述对齐 | ★★★ |
| **持 / 期** | 现象学 retention/protention 标准汉译 | 期 = E[X] expected value | 持守 / 期限 / 期待 | 概率 / 统计 anchor | ★★ |

### 8.3 回看时机 (When to revisit)

> Cell128.lean / Cell256.lean 落码 + Theorems H–K 形式化稳定后回看。

当前状态 (2026-05-11)：Lean 全 Cell256 + Theorems H/I/J 已稳定。**项目可在任何时点收 final 决定**。

最强候选：

- **因 / 果**（当前）：哲学最深 + Pearl 因果，但与 Shi.ji（已）听觉相撞
- **印 / 投**：与 XinZhi.lean 三相对接，且作为 *operator* 与 因/果 作为 *state* 的组合（即「印 = 翻 因 axis」「投 = 翻 果 axis」）已是项目当前实践
- **始 / 终**：唯一 Yi-native 候选 (《易传》原文)，但与「终」字之否定意涵相涉

### 8.4 当前实践

项目当前同时使用：

- **因 / 果** 作为 R₇ / R₈ 之 **state attribute** （bit 名 / axis 名）
- **印 / 投** 作为 R₇ / R₈ 之 **action operator** （toggle 因 / toggle 果）

这是 R-O 双层级 doctrine 之自然分工：state 与 operator 各有名。详见 [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 4 R-O 算子代数。

---

## 第九部分：Shi 在 Cell256 上的 lift

### 9.1 Cell256.shiCuo / shiZong / shiCuoZong

V₄ 算子从 Shi 层 lift 到 Cell256 层（保 hexagram 部分） ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 3)：

```lean
/-- 时态 cuo on Cell256 (P-like, 保 hex). -/
def shiCuo (c : Cell256) : Cell256 := (c.1, c.2.cuo)
/-- 时态 zong on Cell256 (T-like, 保 hex). -/
def shiZong (c : Cell256) : Cell256 := (c.1, c.2.zong)
/-- 时态 cuoZong on Cell256 (PT, 保 hex). -/
def shiCuoZong (c : Cell256) : Cell256 := (c.1, c.2.cuoZong)
```

### 9.2 Lift 之 involution 性

```lean
theorem shiCuo_shiCuo (c : Cell256) : shiCuo (shiCuo c) = c := by
  rcases c with ⟨h, s⟩; simp [shiCuo, Shi.cuo_cuo]

theorem shiZong_shiZong (c : Cell256) : shiZong (shiZong c) = c := by
  rcases c with ⟨h, s⟩; simp [shiZong, Shi.zong_zong]

theorem shiCuoZong_shiCuoZong (c : Cell256) : shiCuoZong (shiCuoZong c) = c := by
  rcases c with ⟨h, s⟩; simp [shiCuoZong, Shi.cuoZong_cuoZong]
```

每个 lift 通过 `simp` + Shi 层之 involution 律即得证。

### 9.3 Hex V₄ ⊗ Shi V₄ 双层 V₄ 结构

R₈ 上有 **两层 V₄** (Theorem J Corollary 2)：

- $V_4^{\text{hex}}$ = `{id, Hexagram.cuo, Hexagram.zong, Hexagram.cuoZong}` on Hexagram
- $V_4^{\text{shi}}$ = `{Shi.dao, Shi.ji, Shi.wei, Shi.jin}` on Shi V₄ (即 Shi 自身作为 V₄ 元素)

二者 tensor 起来给出 R₈ 上 16 个对称变换 (`V_4 × V_4 ≅ (Z/2)⁴`)。

```lean
theorem hexCuo_shiCuo_comm (c : Cell256) : hexCuo (shiCuo c) = shiCuo (hexCuo c) := by
  rcases c with ⟨h, s⟩; rfl

theorem hexZong_shiZong_comm (c : Cell256) : hexZong (shiZong c) = shiZong (hexZong c) := by
  rcases c with ⟨h, s⟩; rfl
```

(摘自 `Cell256.lean` § 3) — 两层 V₄ 之间互相交换，确认 tensor product 结构。

---

## 第十部分：边界 (Boundaries)

### 10.1 Shi V₄ **不**做的事

| 不做 | 原因 |
|---|---|
| 不刻画 hexagram 之 V₄ (cuo/zong/hu) | 那是 R₆ 层之 V₄；二者独立 |
| 不刻画动态时态演化 (e.g. 道 → 未 → 今 之 trajectory) | 那是 BaguaTuring 之 dynamic layer |
| 不接 continuous 时间 / 概率分布 | V₄ 是离散 4-state，不接 ℝ |

### 10.2 与其他 V₄ 实例

V₄ 在易系统中**至少**出现 4 次 (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 8.3)：

| 层 | V₄ 实例 | 元素 |
|---|---|---|
| R₂ Aut | V₄ on SiXiang | id, σ₁, σ₂, σ₁σ₂ |
| R₃ V₄ subgroup | {id, cuo₃, zong₃, 错综₃} | id, cuo (`xxx`), zong, 错综 |
| R₆ V₄ subgroup | {id, cuo₆, zong₆, 错综₆} | id, cuo (`xxxxxx`), zong, 错综 |
| **R₈ Shi V₄** (本文档) | **{道, 已, 今, 未}** | mask 后 2 位 `oo`/`xo`/`xx`/`ox` |

本文档专注 R₈ Shi V₄。其它三种 V₄ 见 [yi-RO-hierarchy.md](yi-RO-hierarchy.md) 与 [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean)。

---

## 附录 A：Shi 算子完整 Lean 签名摘要

来自 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1 与 § 3：

```lean
namespace SSBX.Foundation.Bagua.Cell256

/-- R6 atom: 果 (guǒ) — future-projection bit. Provisional naming. -/
abbrev GuoBit : Type := Bool

inductive Shi : Type
  | dao | ji | jin | wei
  deriving Repr, DecidableEq, BEq

namespace Shi

def all : List Shi := [dao, ji, jin, wei]
theorem all_length : all.length = 4 := rfl

-- V₄ 算子
def cuo : Shi → Shi
def zong : Shi → Shi
def cuoZong : Shi → Shi

-- V₄ 律
theorem cuo_cuo (s : Shi) : cuo (cuo s) = s
theorem zong_zong (s : Shi) : zong (zong s) = s
theorem cuoZong_cuoZong (s : Shi) : cuoZong (cuoZong s) = s
theorem cuo_zong_comm (s : Shi) : cuo (zong s) = zong (cuo s)
theorem cuoZong_eq_compose (s : Shi) : cuoZong s = cuo (zong s)

-- Bool² 双射
def toYinGuo : Shi → YinBit × GuoBit
def ofYinGuo : YinBit × GuoBit → Shi
theorem ofYinGuo_toYinGuo (s : Shi) : ofYinGuo (toYinGuo s) = s
theorem toYinGuo_ofYinGuo (yg : YinBit × GuoBit) : toYinGuo (ofYinGuo yg) = yg

-- 印 / 投 alias
def yin (s : Shi) : Shi := s.cuo
def tou (s : Shi) : Shi := s.zong
theorem yin_yin (s : Shi) : yin (yin s) = s
theorem tou_tou (s : Shi) : tou (tou s) = s
theorem yin_tou_comm (s : Shi) : yin (tou s) = tou (yin s)
theorem yin_tou_eq_cuoZong (s : Shi) : yin (tou s) = cuoZong s

end Shi

abbrev Cell256 : Type := Hexagram × Shi

-- Cell256 V₄ lift
namespace Cell256

def shiCuo (c : Cell256) : Cell256
def shiZong (c : Cell256) : Cell256
def shiCuoZong (c : Cell256) : Cell256

theorem shiCuo_shiCuo (c : Cell256) : shiCuo (shiCuo c) = c
theorem shiZong_shiZong (c : Cell256) : shiZong (shiZong c) = c
theorem shiCuoZong_shiCuoZong (c : Cell256) : shiCuoZong (shiCuoZong c) = c

end Cell256

end SSBX.Foundation.Bagua.Cell256
```

## 附录 B：术语对照

| 术语 | 在 Shi V₄ | 在抽象代数 | 在物理 |
|---|---|---|---|
| 道 (dao) | V₄ identity = (0,0) | identity element | reference vacuum |
| 已 (ji) | σ_P = (1,0) | involution | P (parity) |
| 未 (wei) | σ_T = (0,1) | involution | T (time-reversal) |
| 今 (jin) | σ_PT = (1,1) | central element | PT compound |
| 因 (yīn) | YinBit = R₇ axis | Z/2 generator | past-cone marker |
| 果 (guǒ) | GuoBit = R₈ axis | Z/2 generator | future-cone marker |
| 印 (yìn) | toggle 因 = Shi.cuo | XOR with YinBit-only mask | toggle past-cone |
| 投 (tóu) | toggle 果 = Shi.zong | XOR with GuoBit-only mask | toggle future-cone |
| V₄ 中心元 | cuoZong = 印 ∘ 投 | central element | PT compound |

## 附录 C：与其它文档之关系

| 文档 | 与本文关系 |
|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | parent doctrine — Shi V₄ 在 R₈ 之 emergence |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorems H/I/J 之严格陈述；§16 命名候选 |
| [ox-notation.md](ox-notation.md) | OX 后 2 位之精确含义 = Shi V₄ |
| [lift-project.md](lift-project.md) | R₇ → R₈ lift 经 Shi.ofYinGuo 加 GuoBit |
| [r5-wuyao-provisional.md](r5-wuyao-provisional.md) | R₅ 五爻 — Shi V₄ 不直接接触此层 |
| [r7-yin-r8-guo.md](r7-yin-r8-guo.md) | 因 / 果 axes 详 — Shi V₄ 之 (因, 果) tensor 来源 |
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | **本文档之 ground truth source** |
| [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | YinBit 定义；Shi 之第一 axis |
