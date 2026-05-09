# Cell192：64 × 3 时态算子空间

> 状态：定本（2026-05-10）。
> 作用：把 64 卦每一个升到 3 个时态版本（已/今/未），得到 192 cells 的完整时态算子空间。这是 [`64-hexagram-grid.md`](64-hexagram-grid.md) 的时态扩展——加上时间维度后，每个 formal claim 不只是"是什么"，还有"在什么模态/时态下是"。
> 配套：
> - [64-hexagram-grid.md](64-hexagram-grid.md) — 64 卦 4 象限基础
> - [layer-axis-graph.md](layer-axis-graph.md) — 三轴图谱
> - [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) — 形式锚 (Cell192 = Hexagram × Shi)
> - [`KleeneInternal.lean`](../../formal/SSBX/Foundation/Bagua/KleeneInternal.lean) — Shi-as-Bool 当前 conflation
> - [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) — 已/今/未 + 迁/溯 + 置

---

## 0. 结构总览

```
Cell192 = Hexagram × Shi
        = 64       × 3
        = 192

按 4 象限拆：
        本本(16)        本征(16)        征本(16)        征征(16)
   已 ┌────────┐    ┌────────┐    ┌────────┐    ┌────────┐
   今 │  16   │    │  16   │    │  16   │    │  16   │   = 12 sub-quadrants
   未 └────────┘    └────────┘    └────────┘    └────────┘
   
        each shi-row: 16 cells; each quadrant-column: 48 cells
        total = 4 × 3 × 16 = 192
```

## 0.1 字根回顾（来自 [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean)）

| 类 | 字 | 个数 |
|---|---|---|
| Shi | 已 / 今 / 未 | 3 |
| 单爻 flip | 改 / 化 / 变 / 临 / 主 / 极 | 6 |
| 整卦 | 错 / 综 / 互 / 错综 | 4 |
| Cell-level | 错格 / 综格 / 互格 | 3 |
| Cell-level flip | 改格 / 化格 / 变格 / 临格 / 主格 / 极格 | 6 |
| Shi 转换 | 迁 / 溯 | 2 |
| Shi setter | 置 | 1 |

合计 25 个 cell-级字根。

---

## 1. 三时态 (Shi) 的形式义

### 1.1 已 (Shi.ji) — past / settled / fact

| 系统 | 名 | 形式义 |
|---|---|---|
| 古文 | 已 / 既 | 已然 / 完成 |
| 现代 | 已经 / 过去 | past tense / perfect aspect |
| 形式逻辑 | postcondition / fact / ⊨ | proven, committed to ledger |
| Curry-Howard | inhabited type / proof exists | term : Type |
| 时态逻辑 | □_past φ | "has been" |
| 计算 | result / output | evaluated value |
| Hoare | {Q} | postcondition |

**字根读法**：已 = "事在我之后"——它已发生，已成定局，**已被 commit**。

### 1.2 今 (Shi.jin) — present / active / in-progress

| 系统 | 名 | 形式义 |
|---|---|---|
| 古文 | 今 / 当 / 方 | 当下 / 正在 |
| 现代 | 现在 / 正在 | present continuous |
| 形式逻辑 | invariant / current state / ⊢ | being elaborated |
| Curry-Howard | elaboration / typechecking | term being built |
| 时态逻辑 | φ (untimed / now) | currently holding |
| 计算 | execution state | running |
| Hoare | {I} (invariant) | mid-computation |

**字根读法**：今 = "事在我之中"——它正在发生，**未 commit, 已 ≠ 未**。

### 1.3 未 (Shi.wei) — future / pending / proposed

| 系统 | 名 | 形式义 |
|---|---|---|
| 古文 | 未 / 将 / 待 | 未然 / 将至 |
| 现代 | 未来 / 待 | future tense / prospective |
| 形式逻辑 | precondition / goal / ⊭ | not-yet, hypothesis |
| Curry-Howard | type / goal type | proposition without proof |
| 时态逻辑 | ◇_future φ | "may yet be" |
| 计算 | spec / target | unevaluated thunk |
| Hoare | {P} | precondition |

**字根读法**：未 = "事在我之前"——它尚未发生，**仅是 proposal/specification**。

### 1.4 三时态作为完整 modal 三角

```
            未 (proposal/goal)
              ↘
                ↓ (active 化)
                  ↓
                今 (active/computing)
                  ↓
                ↓ (settling)
              ↙
            已 (settled/fact)
              ↘
                ↓ (cycle)
                  ↘
                未'  (next proposal)
```

3 时态形成 cycle：每次 commit 完成（已），就成为下一轮 proposal（未）的基础。这是**计算/证明/认知的 minimal complete cycle**。

---

## 2. 12 sub-quadrant 总览

4 hex-quadrant × 3 shi = 12 元类，每元类 16 cells。

| sub-quadrant | 元义 | formal 类型 | 例子 |
|---|---|---|---|
| **本本-已** | 已成 value | proven theorems | 已成 (1乾, 已), 已济 (63既济, 已) |
| **本本-今** | 当下 value | active types / propositions | 正实 (1乾, 今) |
| **本本-未** | 待成 value | type specifications | 待实 (1乾, 未) |
| **本征-已** | 已成 modification | applied transformations | 已饰 (22贲, 已), 已革 (49革, 已) |
| **本征-今** | 当下 modification | ongoing transformations | 正革 (49革, 今) |
| **本征-未** | 待成 modification | pending transformations | 待革 (49革, 未) |
| **征本-已** | 已成 construction | built artifacts | 已器 (50鼎, 已) |
| **征本-今** | 当下 construction | building in progress | 正建 (3屯, 今) |
| **征本-未** | 待成 construction | construction blueprint | 待建 (3屯, 未) |
| **征征-已** | 已成 dynamics | terminated processes | 已止 (52艮, 已) |
| **征征-今** | 当下 dynamics | running processes | 正起 (51震, 今) |
| **征征-未** | 待成 dynamics | scheduled processes | 待起 (51震, 未) |

每 sub-quadrant 16 cells——它们是**完整 formal artifact lifecycle 的 12 个 phase**。

---

## 3. 三时态对各算子的 modulation 模式

时态如何 modulate 一个 cell 的读法？答案：每个 hex 的 base reading 加上 shi-prefix。

### 3.1 古文 modulation 公式

| Shi | 前缀 | 例（以 "1乾 = 健"为基） |
|---|---|---|
| 已 | 已 / 既 | **已健** / 既成 |
| 今 | 当 / 方 / 正 | **当健** / 方实 / 正成 |
| 未 | 将 / 待 / 未 | **将健** / 待成 / 未实 |

### 3.2 现代汉语 modulation

| Shi | 前缀 | 例（以 "1乾 = 实在"为基） |
|---|---|---|
| 已 | 已 + V / V 过 | **已实** / 实现过 |
| 今 | 正在 + V / 在 V | **正实** / 正实现 |
| 未 | 待 + V / 将 + V | **待实** / 将实现 |

### 3.3 形式逻辑 modulation

| Shi | logic prefix | 例 |
|---|---|---|
| 已 | ⊨ φ / `proof : φ` | proven |
| 今 | ⊢ φ in elaboration / `?proof_term` | being constructed |
| 未 | φ as goal / `goal : φ` | pending |

### 3.4 Hoare-triple modulation（最强 mapping）

每个 hex 在三 shi 上构成完整 Hoare 三元组：

| (hex, 已) | + | (hex, 今) | + | (hex, 未) |
|---|---|---|---|---|
| postcondition Q | ← | invariant I | ← | precondition P |
| {hex_after} | | {hex_during} | | {hex_before} |

例：(11泰, 未) = 期通 = 期望此 composition 成功 = precondition；(11泰, 今) = 正通 = 正在 compose = invariant；(11泰, 已) = 已通 = composition 已成 = postcondition。

---

## 4. 192 cells 完整列表

每 hex 给 **3 shi modal reading**。古/现/形式 已隐含在 shi-prefix + base reading 的组合里（详 §3）。这里只标 **(hex, shi) 的 modal 单字字根**。

格式：
- **"shi-prefix + hex-base-字"** = cell 字根
- 形式 column = (hex's formal role) + (shi modal)

### 4.1 本本-shi 全表（16 hex × 3 shi = 48 cells）

| # | hex 古字 | (·, 已) | (·, 今) | (·, 未) | 形式 |
|---|---|---|---|---|---|
| 1 乾 | 健 | 已健 | 当健 | 将健 | ⊤ : (proven / active / pending) |
| 2 坤 | 顺 | 已顺 | 当顺 | 将顺 | ⊥ : (committed / current / proposed) |
| 5 需 | 待 | 已待 | 当待 | 将待 | promise : (resolved / awaiting / specified) |
| 6 讼 | 争 | 已争 | 当争 | 将争 | conflict : (resolved / in dispute / anticipated) |
| 7 师 | 众 | 已众 | 当众 | 将众 | quotient : (formed / forming / planned) |
| 8 比 | 亲 | 已亲 | 当亲 | 将亲 | relation : (established / forming / proposed) |
| 11 泰 | 通 | 已通 | 当通 | 将通 | composition : (succeeded / running / specified) |
| 12 否 | 塞 | 已塞 | 当塞 | 将塞 | block : (committed / blocking / anticipated) |
| 13 同人 | 同 | 已同 | 当同 | 将同 | equiv : (proven / verifying / proposed) |
| 14 大有 | 富 | 已富 | 当富 | 将富 | total : (saturated / saturating / target) |
| 29 坎 | 险 | 已险 | 当险 | 将险 | nesting : (settled / running / projected) |
| 30 离 | 丽 | 已丽 | 当丽 | 将丽 | iter : (terminated / iterating / planned) |
| 35 晋 | 进 | 已进 | 当进 | 将进 | lift : (lifted / lifting / to-lift) |
| 36 明夷 | 隐 | 已隐 | 当隐 | 将隐 | occult : (hidden / obscuring / scheduled) |
| 63 既济 | 成 | 已成 | 当成 | 将成 | ⊨ : (validated / validating / proposed) |
| 64 未济 | 未 | 已未 | 当未 | 将未 | ⊭ : (left-pending / pending / projected) |

**特别观察**：
- (1乾, 已) = "**已健**" = 已实证之 ⊤ = "fact"
- (2坤, 已) = "**已顺**" = 已成已受 = "void/null committed"
- (63既济, 已) = "**已成**" = double-committed (hex 已是"既济"，shi 又"已"了一次) = "doubly proven"
- (64未济, 未) = "**已未**" / "**将未**" = 双未 = "still pending in pending state"

(63, 已) 和 (64, 未) 是 4-attractor 的"shi-aligned 极" — 它们是 192 cells 中 **modal 一致性最强** 的两个。

### 4.2 本征-shi 全表（16 hex × 3 shi = 48 cells）

| # | hex 古字 | (·, 已) | (·, 今) | (·, 未) | 形式 |
|---|---|---|---|---|---|
| 4 蒙 | 启 | 已启 | 当启 | 将启 | opaque : (revealed / revealing / awaiting) |
| 9 小畜 | 畜 | 已畜 | 当畜 | 将畜 | accum : (accumulated / accumulating / planned) |
| 16 豫 | 备 | 已备 | 当备 | 将备 | thunk : (forced / preparing / lazy) |
| 20 观 | 观 | 已观 | 当观 | 将观 | observe : (observed / observing / anticipated) |
| 22 贲 | 饰 | 已饰 | 当饰 | 将饰 | annotate : (annotated / annotating / to-annotate) |
| 23 剥 | 剥 | 已剥 | 当剥 | 将剥 | erode : (eroded / eroding / scheduled) |
| 26 大畜 | 畜 | 已蓄 | 当蓄 | 将蓄 | bulk-fold : (folded / folding / pending) |
| 34 大壮 | 壮 | 已壮 | 当壮 | 将壮 | force : (forced / forcing / strict-pending) |
| 37 家人 | 家 | 已家 | 当家 | 将家 | scope : (closed / closing / declared) |
| 40 解 | 解 | 已解 | 当解 | 将解 | release : (released / releasing / triggered) |
| 43 夬 | 决 | 已决 | 当决 | 将决 | commit : (committed / deciding / pending) |
| 45 萃 | 聚 | 已聚 | 当聚 | 将聚 | aggregate : (gathered / gathering / planned) |
| 47 困 | 困 | 已困 | 当困 | 将困 | stuck : (deadlocked / livelocking / risk) |
| 49 革 | 革 | 已革 | 当革 | 将革 | rewrite : (rewritten / rewriting / planned) |
| 55 丰 | 盛 | 已盛 | 当盛 | 将盛 | saturated : (full / filling / target) |
| 59 涣 | 散 | 已涣 | 当涣 | 将涣 | scatter : (scattered / scattering / scheduled) |

**特别观察**：(43夬, 已) = "**已决**" = decision-committed = 这是版本控制 (git commit) 的精确语义 — "决"在已 mode 等于"提交"。(43, 今) = 正在决 = 准备 commit 但尚未 commit；(43, 未) = 待决 = 提议待决议。

### 4.3 征本-shi 全表（16 hex × 3 shi = 48 cells）

| # | hex 古字 | (·, 已) | (·, 今) | (·, 未) | 形式 |
|---|---|---|---|---|---|
| 3 屯 | 难 | 已屯 | 当屯 | 将屯 | bootstrap : (initialized / initializing / planned) |
| 10 履 | 履 | 已履 | 当履 | 将履 | step : (taken / taking / scheduled) |
| 15 谦 | 谦 | 已谦 | 当谦 | 将谦 | restrict : (restricted / restricting / proposed) |
| 19 临 | 临 | 已临 | 当临 | 将临 | observe : (observed / overseeing / scheduled) |
| 21 噬嗑 | 噬 | 已噬 | 当噬 | 将噬 | unify : (unified / unifying / awaiting) |
| 24 复 | 复 | 已复 | 当复 | 将复 | recurse : (returned / recurring / scheduled) |
| 25 无妄 | 妄 | 已妄 | 当妄 | 将妄 | pure : (committed / running pure / planned) |
| 33 遁 | 遁 | 已遁 | 当遁 | 将遁 | weaken : (weakened / weakening / planned) |
| 38 睽 | 离 | 已睽 | 当睽 | 将睽 | divergence : (diverged / diverging / risk) |
| 39 蹇 | 阻 | 已蹇 | 当蹇 | 将蹇 | block : (blocked / blocking / anticipated) |
| 44 姤 | 遇 | 已姤 | 当姤 | 将姤 | encounter : (met / meeting / scheduled) |
| 46 升 | 升 | 已升 | 当升 | 将升 | lift : (lifted / lifting / to-lift) |
| 48 井 | 井 | 已井 | 当井 | 将井 | source : (drawn / streaming / available) |
| 50 鼎 | 器 | 已器 | 当器 | 将器 | container : (formed / forming / specified) |
| 56 旅 | 旅 | 已旅 | 当旅 | 将旅 | traverse : (traversed / traversing / planned) |
| 60 节 | 节 | 已节 | 当节 | 将节 | constrain : (constrained / restricting / declared) |

**特别观察**：(24复, 已) = "**已复**" = 复归已成 = recursion 的 base case 已达；(24, 今) = 正复 = 递归正在展开；(24, 未) = 待复 = 递归待启动 = lazy 递归。这是函数式编程里 fix-point 的 3-shi 视角。

### 4.4 征征-shi 全表（16 hex × 3 shi = 48 cells）

| # | hex 古字 | (·, 已) | (·, 今) | (·, 未) | 形式 |
|---|---|---|---|---|---|
| 17 随 | 随 | 已随 | 当随 | 将随 | seq : (sequenced / executing / queued) |
| 18 蛊 | 治 | 已治 | 当治 | 将治 | debug : (fixed / fixing / scheduled) |
| 27 颐 | 养 | 已养 | 当养 | 将养 | supply : (supplied / streaming / requested) |
| 28 大过 | 过 | 已过 | 当过 | 将过 | overflow : (occurred / occurring / risk) |
| 31 咸 | 感 | 已咸 | 当咸 | 将咸 | sync : (synced / syncing / awaiting) |
| 32 恒 | 恒 | 已恒 | 当恒 | 将恒 | loop : (terminated / looping / scheduled) |
| 41 损 | 损 | 已损 | 当损 | 将损 | decrement : (done / decrementing / planned) |
| 42 益 | 益 | 已益 | 当益 | 将益 | increment : (done / incrementing / planned) |
| 51 震 | 起 | 已起 | 当起 | 将起 | trigger : (fired / firing / scheduled) |
| 52 艮 | 止 | 已止 | 当止 | 将止 | halt : (halted / halting / target) |
| 53 渐 | 渐 | 已渐 | 当渐 | 将渐 | monotone : (converged / progressing / projected) |
| 54 归妹 | 归 | 已归 | 当归 | 将归 | adjoint : (adjoined / pairing / specified) |
| 57 巽 | 入 | 已入 | 当入 | 将入 | inject : (injected / injecting / scheduled) |
| 58 兑 | 悦 | 已悦 | 当悦 | 将悦 | choose : (chosen / choosing / branching) |
| 61 中孚 | 信 | 已信 | 当信 | 将信 | bisim : (verified / bisimulating / proposed) |
| 62 小过 | 微 | 已微 | 当微 | 将微 | drift : (drifted / drifting / projected) |

**特别观察**：(51震, 已) = "**已起**" = event 已 fire；(51, 今) = 正起 = event 正在 fire；(51, 未) = 将起 = event scheduled。这是事件驱动系统 (event-driven systems) 的核心 3-shi 视角——event 的整个生命周期就是 (51震, 未) → (51震, 今) → (51震, 已)。

(52艮, 已) = "**已止**" = halted = process 终结。这是任何 fix-point computation 的 final state.

---

## 5. 算子代数 — 6 类算子在 192 cells 上的行动

### 5.1 6 个 cell-flip（改格 / 化格 / 变格 / 临格 / 主格 / 极格）

每个**保 shi**，改 hex 中一个 yao：
```
(hex, shi) →改格→ (改 hex, shi)
```

shi 不变。所以这 6 个算子在 (Z/2)⁶ 群作用下保 shi-fiber。

### 5.2 4 个 cell-整卦（错格 / 综格 / 互格 / 错综格）

也保 shi。
```
(hex, shi) →错格→ (cuo hex, shi)
```

### 5.3 1 个 chong（重）— 跨 hex 维

`chong : (R3 trigram pair, shi) → (R4 hex, shi)`，从 trigram 升到 hexagram，shi 不变。

### 5.4 2 个 shi-only（迁 / 溯）

每个**保 hex**，cycle shi：
```
(hex, 已) →迁→ (hex, 今) →迁→ (hex, 未) →迁→ (hex, 已)  (Z/3)
(hex, 已) ←溯← (hex, 今) ←溯← (hex, 未) ←溯← (hex, 已)
```

迁 / 溯 互为逆元。

### 5.5 1 个 shi-setter（置）

`置 sh : (hex, _) → (hex, sh)` — 直接跳到指定 shi。

### 5.6 全算子群结构

总共 (改格 / 化格 / 变格 / 临格 / 主格 / 极格 / 错格 / 综格 / 互格 / 迁 / 溯 / 置) 12 个原子算子，组合起来生成 **(Z/2)⁶ × Z/3 = 192-阶群**——刚好等于 cell 数。

这意味着：**算子群在 Cell192 上 simply transitive**——任何两个 cell 之间存在唯一的算子组合把一个变成另一个。这是 Cell192 作为 **homogeneous space** 的形式描述。

### 5.7 算子组合规则（commute / non-commute）

| 组合 | 是否交换 |
|---|---|
| 改格 ∘ 化格 = 化格 ∘ 改格 | ✓（Abel） |
| 错格 ∘ 综格 = 综格 ∘ 错格 = 错综格 | ✓ |
| 改格 ∘ 迁 = 迁 ∘ 改格 | ✓（hex 维与 shi 维独立） |
| 错格 ∘ 迁 = 迁 ∘ 错格 | ✓ |
| 迁 ∘ 溯 = 溯 ∘ 迁 = id | ✓ (互逆) |
| 置 ∘ 任何 hex 算子 = 任何 hex 算子 ∘ 置 | ✓ (置只动 shi) |

所有 hex 算子与 shi 算子 commute，因为它们作用在 Cell192 的不同分量上。Cell192 = Hexagram × Shi 是 **direct product**。

### 5.8 互 (hu) attractor 在 192 cells 上的对应

§5.3 of [64-grid](64-hexagram-grid.md) 说 hu 的 4 attractors 是 {1乾, 2坤, 63既济, 64未济}。在 192 cells 上变成 **12 attractors**：
- (1乾, 已), (1乾, 今), (1乾, 未) — 3 个
- (2坤, 已), (2坤, 今), (2坤, 未) — 3 个
- (63既济, 已), (63既济, 今), (63既济, 未) — 3 个
- (64未济, 已), (64未济, 今), (64未济, 未) — 3 个

合计 12 attractors。它们是 192 cells 的"代数核心"——**最强对称性的 12 个 cell**。

而其中 4 个是**真 fixed point** (对所有算子都不动)：
- (1乾, 已) = ⊤_proven = "fully validated TOP"
- (2坤, 已) = ⊥_committed = "void committed"
- (63既济, 已) = ⊨_full = "completely satisfied"
- (64未济, 未) = ⊭_pending = "completely pending"

**这 4 个 (hex, shi) 对是任何形式系统的 4 个真理值常数**：
- (1乾, 已) = **TRUE**
- (2坤, 已) = **FALSE**
- (63既济, 已) = **VERIFIED**
- (64未济, 未) = **UNVERIFIED**

这是 truth-value 论的精确实现——**Belnap 4-valued logic 的 易经 表达**。

---

## 6. 12 sub-quadrant 作为完整 formal artifact lifecycle

这是本文最深的一节——把 192 cells 解读为一个完整 formal artifact (theorem / program / claim / scientific theory) 的生命周期。

### 6.1 总览：3 shi × 4 quadrant = 12 lifecycle phases

任何形式 artifact 都经历 12 个明确 phase：

```
                未 (specify)        今 (build)         已 (validate)
本本 (value)    spec/type goal     elaboration         proven theorem
                "我要什么"          "正在 derive"       "已证 commit"
                
本征 (modify)   modification plan  ongoing rewrite     applied refactor
                "需要改什么"        "正在改"           "已改 commit"
                
征本 (build)    construction blueprint  building       built artifact
                "如何造"           "正在造"           "造成 commit"
                
征征 (run)      execution schedule  running             terminated
                "何时运行"         "正在运行"         "运行 over"
```

### 6.2 各 phase 详解

#### **Phase 1: (本本, 未) — 类型规范 / 提议**

16 cells: (1, 未) / (2, 未) / (5, 未) / ... / (64, 未)

读法：**待 X**——X 还没确立，是一个 type signature / specification。

形式对应：
- (1乾, 未) = "待实" = TOP type 待实化 = goal of type ⊤
- (5需, 未) = "将待" = double-pending = `Future<Future<T>>` (specification of an awaiting computation)
- (63既济, 未) = "**将成**" = specification of completion = "我们要得到 ⊨"
- (64未济, 未) = "**将未**" = specification of pending = double-pending = "我们规划一个 hole"

软件工程对应：**编写 type signature / API 接口 / 测试 spec**。
科研对应：**提出假设 / 设计实验**。
日常对应：**计划 / 立志 / 立约**。

#### **Phase 2: (本本, 今) — 类型 elaboration**

16 cells: (1, 今) / ... / (64, 今)

读法：**当 X**——X 正在被 derive / type-check / 验证。

形式对应：
- (1乾, 今) = "当实" = ⊤ being asserted right now
- (29坎, 今) = "当险" = recursion in progress = "正在展开 nested ∘"
- (63既济, 今) = "当成" = currently validating

工程对应：**编译 / type-check / live debug**。
日常对应：**正在做 / 进行中**。

#### **Phase 3: (本本, 已) — 已成 type / 已证 theorem**

16 cells: (1, 已) / ... / (64, 已)

读法：**已 X**——X 已确立、已 commit、已成定理。

形式对应：
- (1乾, 已) = "**已健**" = TRUE (proven top)
- (2坤, 已) = "**已顺**" = FALSE / void committed
- (11泰, 已) = "已通" = composition succeeded = `g.f` 已运行
- (63既济, 已) = "**已成**" = double-committed proof = ⊨ + ⊨

工程对应：**已发布的 API / 已证的定理 / 已部署的 artifact**。
日常对应：**已成 / 已得 / 已立**。

#### **Phase 4-6: (本征, 未/今/已) — modification lifecycle**

读法：**待改 / 当改 / 已改**——transformation 的三相。

例：
- (49革, 未) = "将革" = "this code 待 rewrite" / refactor proposal
- (49革, 今) = "当革" = currently rewriting / live refactor in progress
- (49革, 已) = "已革" = refactor applied / commit pushed

工程对应：**Pull request lifecycle**：proposed → in review → merged。

#### **Phase 7-9: (征本, 未/今/已) — construction lifecycle**

读法：**待建 / 当建 / 已建**——artifact 构造的三相。

例：
- (50鼎, 未) = "将器" = "container API spec / future class design"
- (50鼎, 今) = "当器" = "正在 implement container"
- (50鼎, 已) = "已器" = "container implementation complete"

工程对应：**新功能 / 新模块的 lifecycle**。

#### **Phase 10-12: (征征, 未/今/已) — execution lifecycle**

读法：**待运行 / 当运行 / 已运行**——dynamics 三相。

例：
- (51震, 未) = "将起" = event scheduled
- (51震, 今) = "当起" = event firing now
- (51震, 已) = "已起" = event fired (in event log)

工程对应：**event-driven system**：scheduled → firing → fired。
日常对应：**事 之 三时**：将至、正发生、已过。

### 6.3 12-phase cycle 是 formal lifecycle 的 minimum

任何"完整的 formal 生命周期"都需要：
- **价值** (value) 维度：types, propositions, contracts
- **修改** (modify) 维度：refactor, edit, refine
- **构造** (construct) 维度：build, define, declare
- **运行** (run) 维度：execute, verify, deploy

× 3 个 shi:
- **未** (proposed)
- **今** (active)
- **已** (committed)

= **12 phase**——这是 formal 工程学的 minimum complete lifecycle taxonomy。SDLC、TDD、CI/CD、proof 开发、scientific method 全都可以重新解读为这 12 phase 的特定路径。

### 6.4 12-phase 在工程世界的具体 instantiation

| 12-phase | 软件工程 | 数学证明 | 科学方法 | 日常 |
|---|---|---|---|---|
| 本本-未 | spec / API design | conjecture | hypothesis | 立志 |
| 本本-今 | type-check / live | proof in progress | data analysis | 正成 |
| 本本-已 | shipped feature | proven theorem | confirmed law | 已成 |
| 本征-未 | refactor RFC | reformulation plan | model revision | 待改 |
| 本征-今 | live refactor | mid-reformulation | model adjusting | 当改 |
| 本征-已 | merged refactor | clean reformulation | model published | 已改 |
| 征本-未 | feature design | construction plan | experiment design | 待建 |
| 征本-今 | implementation | construction in proof | experiment running | 当建 |
| 征本-已 | feature ready | construction complete | experiment done | 已建 |
| 征征-未 | scheduled job | proof checker queue | upcoming observation | 待行 |
| 征征-今 | running job | proof checker running | observation in progress | 当行 |
| 征征-已 | completed run | proof verified | observation logged | 已行 |

每一行都是同一个 phase 在不同 domain 的 instantiation。**这是为什么这套 framework 能在多 domain 一致**——因为 12-phase 是 lifecycle 的本体最小集。

### 6.5 phase transitions 的算子

```
本本-未 ──(elaboration 算子, ⊢ derive)→ 本本-今
本本-今 ──(commit 算子, 提交)→ 本本-已
本本-已 ──(再用 算子, 把 fact 当 base)→ 本本-未'  (cycle)

本征-未 → 本征-今 → 本征-已: refactor cycle
征本-未 → 征本-今 → 征本-已: build cycle
征征-未 → 征征-今 → 征征-已: run cycle
```

每条 cycle 由 **迁 (shiNext)** 算子驱动——这就是 [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) 中 `Shi.next` 在 lifecycle 上的精确语义。

而 **溯 (shiPrev)** 是反向 — "把已成 fact 重读为 spec / hypothesis" = 学习 / 教学 / 文献综述的方向。

跨 quadrant 的 transition：
- 本本-已 → 本征-未: "we proved theorem T, now propose using T to refactor"
- 本征-已 → 征本-未: "we refactored, now propose new construction on top"
- 征本-已 → 征征-未: "we built it, now propose execution"
- 征征-已 → 本本-未: "we ran it, now propose new theorem from data"

这 4 个 inter-quadrant transitions 构成了 **大循环**：value → modify → construct → run → value' → ...。

这正是 **scientific method**：theory → revise → predict → experiment → theory'。

### 6.6 Phase 与时间的非线性

注意：**phase 并不严格按 12 个顺序**。一个 artifact 可以在 phase 之间任意跳转：
- (本本, 已) → (本本, 未) (从已知定理回到提议新定理)
- (征征, 今) → (征本, 未) (运行中发现需要新的构造)
- (本征, 未) → (本征, 已) (规划的修改 直接 commit 没经今 phase) — **bug! 跳过 review**

实际过程是 **192 cells 上的非线性 walk**——正常路径用迁，但用置可以任意跳转。

这是为什么 **置 (set Shi)** 是危险的"特权操作"——它能跳过中间 phase。良好的工程纪律要求 **置 仅用于初始化和重置**，正常 lifecycle 必须经迁。

---

## 7. 与传统形式系统的对比

### 7.1 vs Hoare Logic

```
Hoare triple:    {P} c {Q}
易经 mapping:    (P-hex, 未) [c-hex, 今] (Q-hex, 已)
```

每个 Hoare 三元组是 192-space 中 **3 个 cells 的有序排列**。

### 7.2 vs Curry-Howard

| Curry-Howard | 易经 192 |
|---|---|
| Type | (hex, 未) |
| Term being built | (hex, 今) |
| Inhabited type / proof | (hex, 已) |

CH 的 type-term 二元论在 易 是 **3-shi modal** ——多了一个"正在 build"的中间相。

### 7.3 vs Linear Temporal Logic

| LTL | 易经 192 |
|---|---|
| Pφ (past) | (φ, 已) |
| φ (now) | (φ, 今) |
| Fφ (future) | (φ, 未) |

LTL 的过去/现在/未来 在 易 是 已/今/未 — 同构。

### 7.4 vs Belnap 4-valued logic

Belnap 4-values: {True, False, Both, Neither}

| Belnap | 易经 192 attractor |
|---|---|
| True | (1乾, 已) |
| False | (2坤, 已) |
| Both / over-defined | (63既济, 已) (双 commit) |
| Neither / under-defined | (64未济, 未) (双 pending) |

**4 truth-value 是 192 的 4 个 attractor**——Belnap 4-valued logic 的精确 易经 化。

### 7.5 vs Reactive Programming / Event-Driven

```
RxJS / event stream:    Future → Subscribe → Resolved
易经 mapping:           (51震, 未) → (51震, 今) → (51震, 已)
```

事件驱动的 stream lifecycle 直接 instantiate 在 (51震, *) 三 cells 上。

### 7.6 vs Process Algebra (CCS / CSP / π-calculus)

```
P ∥ Q (parallel composition):    (31咸, 今)  // sync state
P → Q (sequencing):              (17随, *)
P + Q (choice):                  (58兑, *)
```

**Process algebra primitives 全部在 征征-今 phase**——这印证 §6.4 的 mapping。

---

## 8. 192 = 完整 ontology 状态空间的下一步扩展

### 8.1 192 是 conflated time-truth space

注意：当前 [`KleeneInternal.lean`](../../formal/SSBX/Foundation/Bagua/KleeneInternal.lean) 把 shi 当作 truth value 的 conflation：
```
已 = past = settled = TRUE
未 = future = unsettled = FALSE
今 = present = mid-computing = UNDEFINED
```

这是 **Diodorean modality**（"已发生 = 真"）的设计选择，对一类计算 OK 但有损。

### 8.2 192 → 576: 解耦 time 和 truth

如果未来想给"昨天 X 并不真"或"明天 X 一定真"这类 claim 形式空间，需要把 shi 拆为 (time, truth)：

```
192 (current)    = 64 hex × 3 (time = truth conflated)
576 (proposed)   = 64 hex × 3 time × 3 truth
```

576 cells 给完整 (内容 × 时态 × 真值) 三元 product，是真正完整的 modal-temporal-content space。

但 192 已经够用于大量场景。576 是后续的扩展余地。

### 8.3 192 → 108 grid 接合

[layer-character-map.md §G](layer-character-map.md) 讨论的 108-grid (3 本 × 4 阶段 × 3 时态 × 3 真值) 与 192-grid (64 hex × 3 shi) 是 **正交不重合的两个网格**：

- 108 给"内容范畴 × 显化阶段 × 时间 × 真值"
- 192 给"形式位置 × 时间"

一个具体 claim 同时占 1 个 108-cell + 1 个 192-cell——两者是不同 axis 的 indexing。

---

## 9. Lean 形式化建议

### 9.1 Cell192 quadrant + shi-phase 已可加

```lean
def Cell192.quadrant (c : Cell192) : HexQuadrant :=
  c.fst.quadrant  -- 来自 hexagram 的 quadrant

inductive ShiPhase
  | proposal    -- 未
  | active      -- 今
  | committed   -- 已

def Cell192.shiPhase (c : Cell192) : ShiPhase :=
  match c.snd with
  | .wei => .proposal
  | .jin => .active
  | .ji  => .committed

def Cell192.lifecyclePhase (c : Cell192) : HexQuadrant × ShiPhase :=
  (c.quadrant, c.shiPhase)

-- 12 phases 可枚举
def allPhases : List (HexQuadrant × ShiPhase) := [
  (.benBen, .proposal), (.benBen, .active), (.benBen, .committed),
  (.benZheng, .proposal), (.benZheng, .active), (.benZheng, .committed),
  (.zhengBen, .proposal), (.zhengBen, .active), (.zhengBen, .committed),
  (.zhengZheng, .proposal), (.zhengZheng, .active), (.zhengZheng, .committed)
]

theorem allPhases_length : allPhases.length = 12 := by native_decide

theorem cell192_phases_partition_192 :
  (List.range 192).all (fun n =>
    let c := someEnum n
    c.lifecyclePhase ∈ allPhases) := by sorry  -- 需要 enum cell
```

### 9.2 4 attractor 形式化

```lean
def truthAttractors : List Cell192 := [
  (Hexagram.qian, Shi.ji),    -- TRUE
  (Hexagram.kun,  Shi.ji),    -- FALSE
  (Hexagram.jiJi, Shi.ji),    -- VERIFIED
  (Hexagram.weiJi, Shi.wei)   -- UNVERIFIED
]

theorem attractors_are_belnap_4 :
  truthAttractors.length = 4 ∧
  -- 在 cuo / zong / hu / 单爻 flip / 迁 / 溯 算子下保持自身或在 4 之内循环
  ∀ c ∈ truthAttractors, ∀ op : Cell192Op,
    op.apply c ∈ truthAttractors := by sorry
```

### 9.3 lifecycle transition 算子

```lean
/-- 标准 lifecycle 路径: 未 → 今 → 已 -/
def standardLifecycle (c : Cell192) (steps : Nat) : Cell192 :=
  Nat.iterate Cell192.shiNext steps (Cell192.fst c, Shi.wei)

-- 任何 cell 在 3 步内回到自己 (Z/3 cyclic)
theorem lifecycle_period_3 (c : Cell192) :
  Cell192.shiNext (Cell192.shiNext (Cell192.shiNext c)) = c := by ...
```

---

## 10. 与其它文件的关系

| 文件 | 关系 |
|---|---|
| [64-hexagram-grid.md](64-hexagram-grid.md) | 本文是 64-grid 的时态扩展（× 3） |
| [layer-character-map.md](layer-character-map.md) | 本文 §0.1 的字根都源自 §R5 |
| [layer-axis-graph.md](layer-axis-graph.md) | 本文 §6 的 12 phase 是 §6 三轴汇聚的 cell-level instantiation |
| [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) | 本文 § 8.3 与该文 12 网格正交并存 |
| [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) | 形式锚 (Cell192 = Hexagram × Shi) |
| [`KleeneInternal.lean`](../../formal/SSBX/Foundation/Bagua/KleeneInternal.lean) | shi-as-Bool conflation 现状 |
| [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) | 已/今/未 + 迁/溯 + 置 + 6 flip + 4 整卦 字根 ground truth |

---

## 11. 关键结论

1. **192 = Cell192 = Hexagram × Shi 是 formal claim 的完整时态空间**。
2. **3 shi (已/今/未) 是 modal 三角**：past-active-future / postcondition-invariant-precondition / proven-being-proven-pending。
3. **12 sub-quadrant = 3 shi × 4 hex-quadrant 是 formal artifact 的完整 12-phase lifecycle**。
4. **cell-level 算子代数 ((Z/2)⁶ × Z/3 = 192) 在 Cell192 上 simply transitive**——任两 cell 间存在唯一组合算子。
5. **4 attractor (1乾-已 / 2坤-已 / 63既济-已 / 64未济-未) = Belnap 4-valued logic 的精确实现**：TRUE / FALSE / VERIFIED / UNVERIFIED。
6. **192 在所有 formal domain (软件 / 数学 / 科学 / 日常) 上都是 minimal complete lifecycle taxonomy**——这是它能跨 domain 一致的代数解释。
7. **192 可以扩展到 576**（解耦 time 和 truth），但 192 已是 minimum complete for most purposes。

---

## 12. 待办

- [ ] 在 [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) 加 `Cell192.lifecyclePhase` + `allPhases` 12 enumeration + `truthAttractors` 4 enumeration
- [ ] 加 cell-level operator group structure theorem: `(Z/2)⁶ × Z/3 acts simply transitively on Cell192`
- [ ] 把 192 cells 的 4-language reading 系统化进 [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) 作为新 dimension
- [ ] 解耦 [`KleeneInternal.lean`](../../formal/SSBX/Foundation/Bagua/KleeneInternal.lean) 的 shi-Bool conflation——加独立 `TruthValue` enum 同时保留旧 mapping 作为可切换 default
- [ ] 把 12-phase lifecycle 与 software lifecycle / proof lifecycle / scientific method 的 mapping 写为 case studies
