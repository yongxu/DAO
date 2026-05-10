# 三本 / 四本 × 四阶段 — 内容线 grid (R₄ Mian = 4本×4征 canonical)

> 状态：v3 定本 (2026-05-11)
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ definitive, §3.4 R₄ Mian = Ben×Zheng)
>
> 作用：把内容线之 **本 (root) × 阶段 (phase)** 网格定位到 R₀..R₈ strict-uniform 之 R₄ Mian 层。
>
> **canonical (2026-05-10/11)** ：
>   - **R₄ Mian = Ben × Zheng = 4 × 4 = 16** (BenZheng.lean) — 这是当前 Lean 落地的 first-class 16-命之载体
>   - 旧 「3 本 (物/動/間) × 4 阶段 (差/识/间/事) = 12 格」**legacy view**, 已折叠到 4 本 / 4 征：物 / 動 / 間 / 事 = 4 本 (zong-fixed substrates), 幾 / 勢 / 機 / 時 = 4 征 (zong-mobile marks)
>
> **配套 v3 兄弟文档**：[yi-bagua.md](yi-bagua.md) (Yi+Bagua+R-hier hub) · [cell256-grid.md](cell256-grid.md) (R₈ 256-格全表) · [shi-v4.md](shi-v4.md) (V₄ Shi) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md) (R₇/R₈ 因/果) · [lift-project.md](lift-project.md) · [ox-notation.md](ox-notation.md) · [64-hexagram-grid.md](64-hexagram-grid.md) (R₆ 64-quadrant)
> 形式锚：[`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) (`Ben/Zheng/Mian` — canonical 16-命) · [`表一_六征本表.md`](../../docs/表一_六征本表.md) (per-cell 16 命表)

---

## 0. R-hierarchy 定位 — 本表的 4 个 mathematical 解读

```
R₀ (1) → R₁ (2) → R₂ (4) → R₃ (8) → R₄ (16) ← 本表主角
                                       ↓
                                       4 本 × 4 征 = 16 命 (Mian)
```

| 视角 | 行轴 | 列轴 | 总元数 | 在 R-hierarchy 之位置 |
|---|---|---|---|---|
| **canonical 4本×4征 (Mian)** | 4 本 (物/動/間/事) | 4 征 (幾/勢/機/時) | **16** | **R₄** = (Z/2)⁴ ✓ |
| legacy 3本×4阶段 (12-grid) | 3 本 (物/動/間) | 4 阶段 (差/识/间/事) | 12 | 不直接 fit (R-hierarchy 是 (Z/2)ⁿ 自相似, 12 = 3×4 含 Z/3 因子) |
| 4本×4阶段 (12 升 16) | 4 本 (物/動/間/事) | 4 阶段 (差/识/间/事) | 16 | R₄ alternate axis |
| 4本×Shi V₄ (R₄ × R₈ Shi 投影) | 4 本 | 4 Shi (道/已/今/未) | 16 | R₄ × R₈-Shi-projection |

**当前 canonical**: 4本×4征 = Mian (BenZheng.lean) — 这是 BenZheng + R₄ Lean 落地之 ground truth。

---

# 第一部分：canonical R₄ Mian = 4 本 × 4 征 = 16 命

## 1.1 4 本 (Ben) — zong-fixed substrate trigrams

R₃ Theorem A (BenZheng.lean): 8 trigrams = 4 zong-fixed (本) + 4 zong-mobile (征)。

```lean
inductive Ben : Type
  | wu      -- 物 ↔ 乾 (☰)
  | dong    -- 動 ↔ 离 (☲)
  | jian    -- 間 ↔ 坎 (☵)
  | shi     -- 事 ↔ 坤 (☷)

def Ben.toTrigram : Ben → Trigram
  | .wu   => Trigram.qian
  | .dong => Trigram.li
  | .jian => Trigram.kan
  | .shi  => Trigram.kun

def Ben.char : Ben → String
  | .wu   => "物"
  | .dong => "动"
  | .jian => "间"
  | .shi  => "事"
```

| Ben | 卦 | symbol | yao tuple | 形式 reading |
|---|---|---|---|---|
| 物 (wu) | 乾 | ☰ | (yang, yang, yang) | substantive / entity / ⊤ |
| 動 (dong) | 离 | ☲ | (yang, yin, yang) | processual / rewrite ⟶ |
| 間 (jian) | 坎 | ☵ | (yin, yang, yin) | relational / morphism ∘ |
| 事 (shi) | 坤 | ☷ | (yin, yin, yin) | enacted / void ⊥ |

**关键修正**: 传统 3-本 (物/動/間) **缺第 4 个 zong-fixed trigram** (坤 = 事)。新 4-本视角把「事」纳入 — 与 Yi 古文 (乾 / 坤 二极) 对齐。

## 1.2 4 征 (Zheng) — zong-mobile mark trigrams

```lean
inductive Zheng : Type
  | jiFaint    -- 幾 ↔ 巽 (☴)
  | shiForce   -- 勢 ↔ 震 (☳)
  | jiOccasion -- 機 ↔ 兑 (☱)
  | shiTime    -- 時 ↔ 艮 (☶)

def Zheng.toTrigram : Zheng → Trigram
  | .jiFaint    => Trigram.xun
  | .shiForce   => Trigram.zhen
  | .jiOccasion => Trigram.dui
  | .shiTime    => Trigram.gen
```

| Zheng | 卦 | symbol | yao tuple | 形式 reading |
|---|---|---|---|---|
| 幾 (jīFaint) | 巽 | ☴ | (yin, yang, yang) | nascent / d/dt at t→0⁺ |
| 勢 (shìForce) | 震 | ☳ | (yang, yin, yin) | momentum / d/dt at t≫0 |
| 機 (jīOccasion) | 兑 | ☱ | (yang, yang, yin) | impulse / δ(t-t*) |
| 時 (shíTime) | 艮 | ☶ | (yin, yin, yang) | step / H(t-t*) |

zong-orbit: {震↔艮}, {巽↔兑}.

## 1.3 R₄ Mian = Ben × Zheng = 16 命 (BenZheng.lean)

```lean
abbrev Mian : Type := Ben × Zheng
-- |Mian| = 4 × 4 = 16 = (Z/2)⁴

def Mian.all : List Mian := Ben.all.flatMap (fun b => Zheng.all.map (fun z => (b, z)))
theorem Mian.all_count : Mian.all.length = 16 := by native_decide
```

### 1.3.1 16 命 全表（Ben × Zheng → label）

```lean
def Mian.label : Mian → String
  | (.wu,   .jiFaint)    => "动"  -- 物之微
  | (.wu,   .shiForce)   => "行"  -- 物之进
  | (.wu,   .jiOccasion) => "化"  -- 物之转
  | (.wu,   .shiTime)    => "流"  -- 物之久
  | (.dong, .jiFaint)    => "萌"  -- 動之微
  | (.dong, .shiForce)   => "长"  -- 動之进
  | (.dong, .jiOccasion) => "发"  -- 動之转
  | (.dong, .shiTime)    => "续"  -- 動之久
  | (.jian, .jiFaint)    => "缘"  -- 間之微
  | (.jian, .shiForce)   => "通"  -- 間之进
  | (.jian, .jiOccasion) => "会"  -- 間之转
  | (.jian, .shiTime)    => "系"  -- 間之久
  | (.shi,  .jiFaint)    => "兆"  -- 事之微
  | (.shi,  .shiForce)   => "趋"  -- 事之进
  | (.shi,  .jiOccasion) => "变"  -- 事之转
  | (.shi,  .shiTime)    => "史"  -- 事之久
```

### 1.3.2 4 × 4 grid 布局

|  | 幾 (微) | 勢 (进) | 機 (转) | 時 (久) |
|---|---|---|---|---|
| **物 (wu)** | 动 | 行 | 化 | 流 |
| **動 (dong)** | 萌 | 长 | 发 | 续 |
| **間 (jian)** | 缘 | 通 | 会 | 系 |
| **事 (shi)** | 兆 | 趋 | 变 | 史 |

每 cell = 1 命 = (本, 征) ∈ Mian。 4 × 4 = 16 命。

### 1.3.3 行 / 列 解读

**行 (Ben fixed, Zheng varies)**: 一个 substrate 在 4 phase 之展开：

| 行 | 微 → 进 → 转 → 久 |
|---|---|
| 物 | 动 → 行 → 化 → 流 |
| 動 | 萌 → 长 → 发 → 续 |
| 間 | 缘 → 通 → 会 → 系 |
| 事 | 兆 → 趋 → 变 → 史 |

**列 (Zheng fixed, Ben varies)**: 一个 phase 在 4 substrate 之并置：

| 列 | 物 / 動 / 間 / 事 |
|---|---|
| 幾 (微) | 动 / 萌 / 缘 / 兆 |
| 勢 (进) | 行 / 长 / 通 / 趋 |
| 機 (转) | 化 / 发 / 会 / 变 |
| 時 (久) | 流 / 续 / 系 / 史 |

详 [`表一_六征本表.md`](../../docs/表一_六征本表.md) (per-cell 16 命之 古文 / 现代 / 形式逻辑 / 物理 anchoring)。

---

## 1.4 R₄ 在 R-hierarchy 中之上下游

```
R₃ (8) Trigram = 4 本 + 4 征
       │
       lift_3 (+1 bit)
       ↓
R₄ (16) Mian = Ben × Zheng = 4 × 4   ← 本表主角
       │
       lift_4 (+1 bit)
       ↓
R₅ (32) Wuyao = Mian × Bool (provisional)
       │
       lift_5 (+1 bit)
       ↓
R₆ (64) Hexagram = (Z/2)⁶
```

详 [lift-project.md](lift-project.md) (uniform Lift / Project + retract lemmas).

R₄ → R₆ 之 chong (重) = 3 步 lift composite (R₄ → R₅ → R₆), 给出 64 卦之 4-quadrant on Hexagram (16 hex / quadrant): 详 [64-hexagram-grid.md](64-hexagram-grid.md).

---

# 第二部分：legacy 3 本 × 4 阶段 = 12 格 view (folded into 4 本)

> **legacy view, see 4 本 / 4 征 for canonical**

旧版本把内容线写为 3 本 (物 / 動 / 間) × 4 阶段 (差 / 识 / 间 / 事) = 12 格。这个视角**有保留价值**, 但它**不直接对应 R-hierarchy 之 (Z/2)ⁿ 自相似** (12 = 3 × 4 含 Z/3 因子)。

折叠路径：
- 3 本 (物 / 動 / 間) → 4 本 (物 / 動 / 間 / **事**)：补加 「事」 (zong-fixed Trigram = 坤) 作为 zong-fixed 4-tuple 之第 4 元
- 4 阶段 (差 / 识 / 间 / 事) 之 「事」与 4 本之 「事」**字相同但语义不同**：阶段「事」= enacted phase, 本「事」= 坤 substrate
- 解决方案：阶段 axis 不再用 「事」字，改用 4 征 (幾 / 勢 / 機 / 時) 作为 phase axis

新格局 (canonical R₄)：4 本 × 4 征 = 16 命，无字符歧义。

## 2.1 旧 3 本 × 4 阶段 12 格 — 简表

|  | 差 | 识 | 间 | 事 |
|---|---|---|---|---|
| 物 | 物 (实体) | 注意 | 模 | 文 |
| 動 | 生 | 心 | 理 | 价值 |
| 間 | 人 | 审校 | 证明 | 真理 |

详 [layer-character-map.md](layer-character-map.md) (R0–L0 字根映射) + [layer-axis-graph.md](layer-axis-graph.md) (三轴汇聚)。

## 2.2 旧 4 阶段定义 — 还原读法

| 阶段 | 古文 | 当代 | 形式 |
|---|---|---|---|
| 差 (cha) | 差 / 异 / 别 | distinction / différance | bit / atomic difference |
| 识 (shi) | 识 / 名 / 指 | marking / nameable | reference / variable binding |
| 间 (jian) | 間 / 联 / 结 | structured / inter-related | structure ⟨M, I⟩ / interpretation |
| 事 (shi-event) | 事 / 行 / 用 | enacted / actualized | trace / execution / event |

升级链: 差 → 识 → 间 → 事 (单调认识链, 严格包含). 详 [root-layer-map.md §0](root-layer-map.md).

## 2.3 折叠到 canonical 4 本 × 4 征

| 旧 (3 本 × 4 阶段) | 新 (4 本 × 4 征) | 备注 |
|---|---|---|
| 物 / 動 / 間 (3 本) | 物 / 動 / 間 / **事** (4 本 = 4 zong-fixed) | 补 「事」 (= 坤 substrate) |
| 差 / 识 / 间 / 事 (4 阶段) | 幾 / 勢 / 機 / 時 (4 征 = 4 zong-mobile) | phase axis 改用 4 征, 避字符撞 |

**对应**:

| 旧阶段 | 新征 | 物理 anchoring |
|---|---|---|
| 差 (raw distinction) | 幾 (jīFaint, 微) | 萌动初起 = d/dt at t→0⁺ |
| 识 (marked) | 勢 (shìForce, 进) | 已识则有势 = 持续动量 |
| 间 (structured) | 機 (jīOccasion, 转) | 结构化 = phase 转换点 |
| 事 (enacted) | 時 (shíTime, 久) | 落地 = 持久态 = step H(t-t*) |

折叠后, **旧 12-grid 之 12 格** 嵌入新 16-grid 中之 12 cells (3 本 × 4 征), 留 4 cells (事 行 之 4 命 = 兆/趋/变/史) 作为新增。

阶段之时态升级链 (差→识→间→事) 在新视角下读为「征之 4 phase」 — 同一个 zong-orbit pair 中之 4 个时态 representative. 详见 [yi-as-meta-framework.md §3](yi-as-meta-framework.md) 4 mark = 谐振子 phase plane 4 quadrant。

---

# 第三部分：4 阶段 (时态 / 时间过程) 之 R-hierarchy 解读

如果坚持 4 阶段视角不折叠到 4 征，它在 R-hierarchy 中如何定位？

## 3.1 阶段 ≠ Shi V₄ — 但相关

V₄ Shi = {道, 已, 今, 未} 是 R₈ 之 (因, 果) emergence (R₇ ⊗ R₈ 双 axis), **不**等于阶段 (差/识/间/事).

| 阶段 | 是否 = Shi | 关系 |
|---|---|---|
| 差 (raw) | ≠ | 阶段是「认识升级链」, Shi 是「时态」 |
| 识 (marked) | ≠ | 阶段 = epistemic state, Shi = causal state |
| 间 (structured) | ≠ | 阶段 = formal state, Shi = (因, 果) state |
| 事 (enacted) | ≈ Shi.ji ∪ Shi.jin | 「已发生」近 P-row + PT-row |

阶段是**认识升级链** (epistemic ascent: 差 → 识 → 间 → 事), Shi 是**时态状态** (temporal state: 道 / 已 / 未 / 今). 两者**正交**。

## 3.2 4 阶段作为 R₄ 的 alternate Z-coord (不 canonical)

如果暂搁 R₄ Mian 之 canonical 定义 (Ben × Zheng), 把 4 阶段 (差/识/间/事) 作为 R₄ 之 Z-coord:

```
R₄_alt = Ben × SiJieduan = 4 × 4 = 16
```

数学上是 R₄ = (Z/2)⁴ 之另一种 4-axis 选择。但 BenZheng.lean 已 commit 到 Ben × Zheng — 此 alternate 仅作 conceptual 参考, 不进入 Lean。

详 [yi-RO-hierarchy.md §3.4](yi-RO-hierarchy.md): R₄ = Mian = Ben × Zheng 是 canonical (Z/2)⁴ anchor。

## 3.3 4 阶段作为 R₈ Shi 之 projection？— 不 canonical

理论上可把阶段映射到 Shi:
- 差 → 道 (V₄ identity = atemporal raw)
- 识 → 已 (P, marked = past closed)
- 间 → 未 (T, structured = future open potential)
- 事 → 今 (PT, enacted = present)

但这是**临时 conceptual 映射**, 非数学等价: 阶段是 epistemic 之 4-step ascent, Shi 是 V₄ 之 4-state symmetry。在 Lean 中保持区分: `SiJieduan : Type` (legacy 12-grid axis) ≠ `Shi : Type` (V₄ Klein on Cell256).

---

# 第四部分：6 行 / 6 列 — 4 × 4 内部关系

## 4.1 行邻接（同 Ben，相邻 Zheng）

每行之 4 命构成「一个 substrate 之 4 phase 演化」:

| 行 | 升级链 |
|---|---|
| 物 | 动 → 行 → 化 → 流 (物之微 → 进 → 转 → 久) |
| 動 | 萌 → 长 → 发 → 续 |
| 間 | 缘 → 通 → 会 → 系 |
| 事 | 兆 → 趋 → 变 → 史 |

## 4.2 列邻接（同 Zheng，相邻 Ben）

每列之 4 命构成「一个 phase 在 4 substrate 之并置」:

| 列 | 三本 + 事 在此 phase |
|---|---|
| 幾 (微) | 物之动, 動之萌, 間之缘, 事之兆 |
| 勢 (进) | 物之行, 動之长, 間之通, 事之趋 |
| 機 (转) | 物之化, 動之发, 間之会, 事之变 |
| 時 (久) | 物之流, 動之续, 間之系, 事之史 |

## 4.3 对角线 — 自我对应

Ben 与 Zheng 之间无 canonical bijection — 都是 4 元 set 但语义异质 (substrate vs phase)。

「自我相应」对角:
- (物, 幾) = 「动」: 物 substrate 在 微 phase = "物之初起" = 物自我之 micro 表达
- (動, 勢) = 「长」: 動 substrate 在 进 phase = "持续动量" = 動自我之 macro 表达
- (間, 機) = 「会」: 間 substrate 在 转 phase = "枢纽连接" = 間自我之 critical point
- (事, 時) = 「史」: 事 substrate 在 久 phase = "永久记录" = 事自我之 finalization

这 4 cells 是「每本之 essence phase」 — substrate 在自身最 expressive phase 上。

## 4.4 cuo / zong on Mian (in Lean)

```lean
-- BaguaAlgebra.lean 之 Trigram 算子 lift to Ben/Zheng:
-- cuo: 全反 6 yao on hex; on Trigram: ⟨t.y1.neg, t.y2.neg, t.y3.neg⟩
-- 在 Ben/Zheng 上: cuo 保 isZongFixed → cuo on Mian = 4-pair Ben swap × 4-pair Zheng swap
```

由 BenZheng.lean `cuo_preserves_isZongFixed`, cuo 保 Ben 集合且保 Zheng 集合, 同时在每 set 内部 swap (本之 cuo: 物↔事 / 動↔間 ; 征之 cuo: 幾↔機 / 勢↔時)。

类似 zong / cuoZong 在 Mian 上之 V₄ 作用 — 详 [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) §4 Trigram-level invariants。

---

# 第五部分：与 R₆ 4-quadrant 之 lift / project

## 5.1 R₄ → R₆ chong lift

R₄ Mian = (本_inner, 征_inner) | (本_outer, 征_outer)?。其实不是这样: R₆ Hexagram = inner_trigram × outer_trigram = 8 × 8 = 64. 4 quadrant on R₆ = (inner_isZongFixed, outer_isZongFixed) ∈ Bool²:

```
本本: inner ∈ Ben, outer ∈ Ben      → 4 × 4 = 16 hex
本征: inner ∈ Ben, outer ∈ Zheng    → 4 × 4 = 16 hex
征本: inner ∈ Zheng, outer ∈ Ben    → 4 × 4 = 16 hex
征征: inner ∈ Zheng, outer ∈ Zheng  → 4 × 4 = 16 hex
total: 64 ✓
```

**R₄ Mian 之 16 命** ⊂ **本本 quadrant** of R₆ ? — 不是。R₄ Mian 有 (Ben, Zheng) 二元 mixing；R₆ 之 4 quadrant 是 (innerType, outerType) 之 4 组合。两者维度不同：

| Layer | 维度 | size |
|---|---|---|
| R₄ Mian | (Ben, Zheng) | 16 |
| R₆ Hex 4-quadrant | (inner_isBen, outer_isBen) | 4 |
| R₆ 本征 quadrant | (Ben_inner, Zheng_outer) | 16 |

**所以 R₆ 本征 quadrant ≅ R₄ Mian** 之 cardinality 巧合, but inner/outer roles 不同。

## 5.2 R₆ 4 quadrant 是 R₄ Mian × Mian 之 isMixed projection

更精确：R₆ 本征 quadrant = 16 hex with (inner ∈ Ben, outer ∈ Zheng) = 4 × 4 = 16, same as R₄ Mian cardinality but two different (Ben, Zheng) selections (inner + outer). 详 [64-hexagram-grid.md §3 本征 16](64-hexagram-grid.md)。

## 5.3 R₈ 上 之 R₄ × Shi V₄ projection

R₈ Cell256 = Hexagram × Shi = 64 × 4 = 256. 投影到 (Mian × Shi):
- 取 Hex inner_trigram → Ben (if zongFixed) or Zheng (if mobile)
- Hex outer_trigram → Ben/Zheng 同上
- 给一个 (innerType, outerType) ∈ Mian × Mian inflation

不直接是 R₄ × Shi V₄ = 16 × 4 = 64 — 因为 R₄ Mian 是单 trigram-pair 之 (Ben, Zheng) 不对称组合, 不是 hex 之 (inner, outer) 选择。

---

# 第六部分：跨语言对应 (4 本 × 4 征)

## 6.1 古文（最简一字）

|  | 幾 | 勢 | 機 | 時 |
|---|---|---|---|---|
| 物 | 动 | 行 | 化 | 流 |
| 動 | 萌 | 长 | 发 | 续 |
| 間 | 缘 | 通 | 会 | 系 |
| 事 | 兆 | 趋 | 变 | 史 |

## 6.2 当代汉语（标准双字）

|  | 微细 | 进展 | 转折 | 持久 |
|---|---|---|---|---|
| 实体 | 萌动 | 进行 | 化转 | 流变 |
| 过程 | 萌发 | 增长 | 发起 | 持续 |
| 关系 | 因缘 | 联通 | 会合 | 维系 |
| 事件 | 征兆 | 趋势 | 变化 | 历史 |

## 6.3 形式逻辑 / category theory

|  | initial | continuing | critical-point | persistent |
|---|---|---|---|---|
| substantive | nascent value | accumulating value | rewriting value | persisting value |
| processual | budding step | extending derivation | branching reduction | invariant trajectory |
| relational | new edge | propagating edge | critical morphism | preserved diagram |
| event | triggered event | progressing event | branching event | committed event |

详 [`表一_六征本表.md`](../../docs/表一_六征本表.md)。

---

# 第七部分：Code refactor 路径

## 7.1 当前状态 (post-2026-05-10)

- BenZheng.lean: `Ben`, `Zheng`, `Mian = Ben × Zheng` 已 first-class 落地
- `Mian.label` 16 entries, `Mian.all_count = 16` by native_decide
- 旧 `MonadRoot.lean Face inductive (12 ctors)` 已删除 (P5b — Face 完全删除)
- 旧 `JianOntology.lean OnticRoot/Manifestation/DynamicMark` (3-元 placeholder) 已 deprecated, 4 本 / 4 征 是 primary

## 7.2 仍在使用的 12 / 16 grid

- `表一_六征本表.md`: per-cell 16 命表 (canonical 4本×4征)
- 旧 12-grid (3 本 × 4 阶段) 概念在 `layer-character-map.md` / `root-layer-map.md` 中保留作 conceptual companion, 但 Lean 锚是 4本×4征 / 16 Mian

## 7.3 命名约定

| 概念 | Lean type | 说明 |
|---|---|---|
| 本 (substrate) | `Ben` (4 ctors) | 物 / 動 / 間 / 事 — zong-fixed trigrams |
| 征 (mark) | `Zheng` (4 ctors) | 幾 / 勢 / 機 / 時 — zong-mobile trigrams |
| 命 (cell) | `Mian = Ben × Zheng` | 16 命之载体 (R₄) |
| 阶段 (legacy) | (no Lean type, conceptual) | 差 / 识 / 间 / 事 — 在 layer-character-map.md |
| Shi (V₄ 时态) | `Shi` (4 ctors) | 道 / 已 / 今 / 未 — V₄ Klein at R₈ |

注意：「事」字在 Ben (= 坤 substrate) 与 阶段 (= enacted) 中**相同字, 不同 type** — 在 Lean 不混淆 (Ben.shi vs SiJieduan.shi if defined)。docs 中需明确区分。

## 7.4 迁移建议

旧 atom 字典从 12-face 迁到 4本×4征+(R₄ Mian):
```
旧: «文面» / «物面» / «生面» / ... / «真理面»  (12 ctors, 单一 face axis)
新: (Ben.X, Zheng.Y) ∈ Mian                  (16 cells, 双 axis)
```

旧 12-grid 字 (物/注意/模/文/生/心/理/价值/人/审校/证明/真理) 不直接 1-to-1 对应到 16 命 (动/行/化/流/萌/...). 这 12 字 reside in **layer-character-map.md** 作为「内容线 epistemic ascent」, 与 4 本 × 4 征 之 mathematical Mian **正交**。

---

# 第八部分：开放问题

1. **legacy 12-grid 与 canonical 16-Mian 之 reconciliation**：12 grid (3 本 × 4 阶段, 字根映射) 与 16 Mian (4 本 × 4 征, R₄ ontology) 是 conceptually different axes — 一个是 epistemic ascent, 一个是 substrate × mark dynamic phase。是否值得维护双 grid？建议保留二者 (12 在 layer-character-map.md, 16 在本文 + BenZheng.lean), 显式标注差异。

2. **「事」字之消歧**：Ben.shi (坤, substrate) vs SiJieduan.shi (enacted, phase). Lean 中通过 namespace 区分; docs 中需明示。

3. **R₄ 之 Z-coord canonical 选**：BenZheng.lean commit 到 (Ben, Zheng). 是否考虑 alternative R₄ axis (e.g., Ben × SiJieduan = 4 × 4)? — 当前不需要; canonical 已 stable。

4. **R₅ Wuyao 与 16-Mian 之 lift**: R₅ = Mian × Bool = 32. R₅ 之 32 cells 之 ontological 内容是什么？详 [r5-wuyao-provisional.md](r5-wuyao-provisional.md)。

5. **Shi V₄ 与 4 阶段 之关系**: §3.3 conceptual 映射不 canonical。是否值得在某层 explicit 形式化阶段-到-Shi 之 mapping？目前看 Shi 与 SiJieduan 是 orthogonal axes, 不必要。

---

# 附：与其它 v3 文档之关系

| 文档 | 主题 | 与本文关系 |
|---|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) §3.4 | R₄ Mian definitive | parent specification |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) Theorem A/B/C/D | 4+4 强制 + substrate=∫ + mark=phase | 4 本 / 4 征之 mathematical 根据 |
| [yi-bagua.md](yi-bagua.md) | Yi+Bagua+R-hier hub | R₄ Mian context navigation |
| [64-hexagram-grid.md](64-hexagram-grid.md) | R₆ 4-quadrant on hex | downstream R₆: 16 hex / quadrant via 4 本 / 4 征 |
| [cell256-grid.md](cell256-grid.md) | R₈ 256-格全表 | R₄ × Shi V₄ projection 在 Cell256 中 |
| [shi-v4.md](shi-v4.md) | V₄ Shi 专文 | §3 区分 SiJieduan vs Shi |
| [r5-wuyao-provisional.md](r5-wuyao-provisional.md) | R₅ provisional | R₅ = Mian × Bool 是 R₄ 之 lift |
| [r7-yin-r8-guo.md](r7-yin-r8-guo.md) | R₇/R₈ atomic axes | upstream Cell256 context |
| [lift-project.md](lift-project.md) | uniform Lift / Project | R₃ → R₄ → R₅ → R₆ chong composite |
| [ox-notation.md](ox-notation.md) | OX literal | 8-char OX → Cell256 |
| [layer-character-map.md](layer-character-map.md) | R0–L0 字根 | legacy 12-grid 字根来源 |
| [root-layer-map.md](root-layer-map.md) §0 | 本体读法 | legacy 4 阶段 (差/识/间/事) anchor |
| [layer-axis-graph.md](layer-axis-graph.md) | 三轴汇聚图 | conceptual companion |
| [`表一_六征本表.md`](../../docs/表一_六征本表.md) | 16 命之 per-cell 表 | full label expansion |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | Ben/Zheng/Mian | ground truth Lean |
