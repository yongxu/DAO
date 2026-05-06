# Z · 经济学与博弈论：实证 / 有条件 / 证错 · EconGame.lean

**文件**：`formal/SSBX/Foundation/Wen/EconGame.lean`
**完成日期**：2026-05-07
**Lean 版本**：4.29.1（Lake 5.0.0）
**单文件构建**：`lake build SSBX.Foundation.Wen.EconGame` — 17 jobs / 0 sorry / 0 warning / 0 新 axiom
**性质**：Kernel 之 application 文件 (NOT a Kernel layer)。不增 axiom，不增 KernelDanZi，不增 def — 全部 reuse Kernel 既立 primitives.

---

## 〇 · 摘要

本篇把 `Kernel.lean` (Layers 26 / 43 / 44 / 45) 之 primitives 当作 sieve，套现代经济学与博弈论之主流命题，分类为：

| 类型 | 含义 | 定理数 |
|------|------|------|
| 实证 (validated) | 在 Kernel 中可证为定理 | **6** |
| 有条件 (conditional) | 仅在某些条件下成立, 条件 explicit | **4** |
| 证错 (refuted) | 形式陈述与 Kernel invariants 冲突 | **8** |
| meta (二面 综) | market 之 二 face | **1** |
| **合计** | — | **19** |

| 度量 | 数值 |
|------|------|
| 新 KernelDanZi 字 | **0** |
| 新 axiom | **0** |
| 新 def | **0** |
| 新 structure / inductive | **0** |
| EconGame.lean 全 theorem | **19** |
| 单文件 `lake build` | **17 jobs / 0 error / 0 warning** |

**重要声明**：
- "实证" IS 「形式上可证为本框架定理」, 不是 historical / empirical 实证
- "证错" IS 「该命题之 specific 形式陈述与 Kernel invariants 冲突」, 不否定其 historical / sociological / computational insight
- 各 result 之 specific 经验 / 政策 含义 超越本框架
- 本卷价值: **市场机制 在 ZhongField 中 IS 道, 当且仅当 同根 维持; 同根 破坏时, market 滑入 非道 attractor (PD / commons / race-to-bottom)**

---

## 一 · 三轴架构

```
                       现代经济学 / 博弈论
                                │
       ┌────────────────────────┼────────────────────────┐
       ▼                        ▼                        ▼
   实证 (6)                 有条件 (4)                证错 (8)
       │                        │                        │
       │                  conditions explicit            │
       │                                                 │
       ▼                                                 ▼
  ┌─────────────────┐                          ┌──────────────────┐
  │ pareto_at_middle│                          │ PD_refuted       │
  │ coase           │                          │ commons          │
  │ mechanism_IC    │                          │ free_rider       │
  │ nash_bargaining │                          │ race_bottom_reg  │
  │ public_goods    │                          │ arrow_dictator   │
  │ smith_invisible │                          │ homo_economicus  │
  └─────────────────┘                          │ universal_greed  │
       │                                       │ zero_sum         │
       │                                       └──────────────────┘
       │                                                 │
       ▼                                                 ▼
   Kernel 原语                                      Kernel 原语
   tongGen / tongGenMiddle                         moloch_via_externality
   liRitual / ren                                  he_not_same
   ZhongField.inMiddle                             race_to_bottom_refuted
   hayek_spontaneous_order                         zero_sum_refuted_by_ren
                                                  zhen_dou_self_refuting

                       【条件轴】
       ┌────────────────────────────────────────┐
       │ Nash eq. existence (static = 极)       │
       │ Rational choice (二值; 失 悬置)        │
       │ Equilibrium (static IS 极, dynamic IS 中)│
       │ VCG efficient ⟸ tongGen                │
       └────────────────────────────────────────┘
```

**核心 axis**:
- 实证轴 ↔ 当 同根 / 礼 / 中 维持时, market mechanism 之 主流积极结论 全 hold.
- 证错轴 ↔ 当 同根 被打破时, market 滑入 非道 attractor — 但 非道 attractor 自身 违 ZhongField invariants.
- 有条件轴 ↔ 命题 valid 仅 在 specific reading 下; 经济学 之 主流 「equilibrium」 之 fixed-point reading 是 极, 故 「Nash eq. exists」 ≠ 「Nash eq. is 中」.

---

## 二 · 实证表 (Validated) — 6 条

| 经济 / 博弈 概念 | Lean 名 | 形式陈述 | Kernel 原语 |
|---|---|---|---|
| Pareto efficiency at 中 | `pareto_at_middle` | `∀ i, middle ((orbits i) state) ∧ ¬ extreme (...)` | `ZhongField.inMiddle` |
| Coase 定理 (zero TC) | `coase_internalizes_externality` | `tongGen ∧ middle (a h1 state) ⟹ ¬ extreme (a h2 state)` | `moloch_via_externality_refuted` |
| Mechanism design 之 IC | `mechanism_incentive_compatibility` | `tongGenMiddle ⟹ middle (a s) ↔ middle (a t)` | `tongGenMiddle` |
| Nash bargaining 合作 IS 道 | `nash_bargaining_cong_dao` | `liRitual ⟹ ren ∧ 双 middle` | `liRitual` + `cooperation_cong_dao` |
| Public goods via 礼 | `public_goods_via_liRitual` | `liRitual ⟹ ∀ k, ren (n+k)` | `liRitual` |
| Smith 看不见的手 (proper) | `smith_invisible_hand_proper` | `自发 ∧ 流通 ∧ 多样` | `hayek_spontaneous_order` |

**核心解读**：

- **Pareto efficiency**: ZhongField 之 invariant 「全 中」 直接 = 「无人 worse-off」. 故 ZhongField 是 Pareto-optimal 之 structural 形式 minimum.
- **Coase 定理**: internalize externality = 重建 同根. 在 同根 之 下, A 之 action 之 极-effect 不可能 「在 B 上 极, 在 A 上 中」.
- **机制设计 IC**: VCG / direct revelation 之 truth-telling-dominance 形式 = `tongGenMiddle` — action 之 中-effect universal 即 truth 是 dominant.
- **Nash bargaining**: cooperation 不是 「分蛋糕」 而是 「双方 在 礼 之 中 共显 仁」 — positive-sum 之 form, 不是 zero-sum 之 解.
- **公共品**: Olson 之 collective action problem 在 礼-coordination 之 下 解决 — `liRitual` 维持 contribution 之 中.
- **Smith 看不见的手**: valid 读法 是 spontaneous order (Hayek), 不是 「universal greed ⟹ universal good」 (naive Mandeville). 后者在证错表.

---

## 三 · 有条件表 (Conditional) — 4 条

每一条**explicit** state 它 之 conditions; absent 条件, fail.

| 经济 / 博弈 概念 | Lean 名 | 条件 | 形式陈述 |
|---|---|---|---|
| Nash equilibrium static = 极 | `nash_equilibrium_static_is_extreme` | static reading: `dong s = s` | `dong s = s ⟹ extreme s ∧ ¬ middle s` |
| Rational choice 二值 | `rational_choice_only_binary` | full classification (zhi_universal) | `middle s ∨ extreme s` |
| Equilibrium static vs dynamic | `equilibrium_static_vs_dynamic` | orbit 形式 | `¬ static ∧ ∀ n, middle (orbit n)` |
| VCG efficient | `vcg_auction_efficient_under_tongGen` | tongGen | `tongGen ⟹ extreme (a s) ↔ extreme (a t)` |

**核心解读**：

### 3.1 Nash equilibrium 之 二 reading

经济学 之 standard equilibrium 是 fixed-point: state s 满足 `dong s = s`. 但**这正是 Kernel 之 极 之 定义**.

- **Static reading**: Nash eq. as fixed-point — `extreme`, NOT `middle`. 故 PD 之 (defect, defect) 是 极, 不是 中.
- **Dynamic reading**: orbit 之 持续 advance — 此 是 中, 但 不 是 fixed-point. ZhongOrbit 之 `shi_no_telos` 直接 拒 fixed-point.

**含义**: 「Nash eq. exists」 与 「Nash eq. is 中」 形式上 distinct. 经济学 之 「equilibrium」 概念 在 minimum-axiom 框架下 是 极.

### 3.2 Rational choice 之 二值 局限

经典 rational choice: actor 之 preference 是 totally ordered, 决策 是 deterministic.

形式 sieve: 在 Kernel 中, `zhi` 是 universal — 任何 state 是 中 ∨ 极. 但 这是**二值 form** — 它不容 「悬置」 之 第三 option (i.e., 当 actor 面对未充分确定状态时之 suspended judgment).

**含义**: rational choice 在二值 reading 下 总 valid; 但 它 不能 capture 真实 决策 之 三值 phenomenon (悬置 / 待定). 此 是 K3 三值逻辑 / Knightian uncertainty 之 入口 — 本卷不展开, 但 explicitly 标 出 limitation.

### 3.3 VCG 之 condition

VCG efficiency 之 dominance 仅 在 tongGen 之 下 hold. 没 tongGen, agent 有 incentive 撒谎. 此 与 Coase 定理 之 condition 同形 — 二者共享 universalizability premise.

---

## 四 · 证错表 (Refuted) — 8 条

| 经济 / 博弈 命题 | Lean 名 | 形式 refute 之 source |
|---|---|---|
| Prisoner's dilemma as descriptive | `prisoners_dilemma_refuted_under_tongGen` | `zhen_dou_self_refuting` |
| Tragedy of the commons | `tragedy_of_commons_refuted` | `moloch_via_externality_refuted` |
| Universal free-rider | `universal_free_rider_refuted` | `moloch_endpoint_refuted` |
| Race-to-bottom (regulatory) | `regulatory_race_to_bottom_refuted` | `race_to_bottom_refuted` |
| Arrow 严格 dictator reading | `arrow_dictator_refuted` | `ZhongField.he_not_same` |
| Homo economicus as descriptive | `homo_economicus_refuted` | `Xin.process.inMiddle` |
| Universal greed (naive Mandeville) | `universal_greed_refuted` | `moloch_endpoint_refuted` |
| Zero-sum framing | `zero_sum_refuted` | `zero_sum_refuted_by_ren` |

**核心解读**：

### 4.1 PD 与 commons 共享同一形式 refute

PD 之 (defect, defect) 与 公地悲剧 之 over-extraction 共享 形式 = **asymmetric externality** (我之 action 为 我 中, 但 为 你 极). 在 同根 之 下, 此 asymmetry 不可能.

**因此**: PD / commons 之 「unsolvable dilemma」 reading 假设了 universalizability 已被打破. 真正之 解 不是 强力 coordination, 而是 **重建 同根** (Kant 绝对命令 / 推己及人 / Rawls 无知之幕).

### 4.2 Arrow's impossibility 之 strict-dictator reading

Arrow's theorem 之 mathematical truth (在 boolean 偏好域 + IIA + Pareto + universal domain ⟹ dictator) 不被本卷 challenge.

但 它 之 **political reading** (「集体决策必有 dictator」) 在 ZhongField 中 fail. ZhongField 之 plurality (`he_not_same`) 直接 forbid dictatorial collapse — 任 时, 没 single state 强加 给 全 orbits.

技术上: Kernel 不强制 actor 在 「中 ∨ 极」 之外 表达 「悬置」 (这是 K3 三值之 入口). 故 strict 「any aggregation must have dictator」 不 capture 「集体非决定」 之 valid option.

### 4.3 Homo economicus

Xin 之 `inMiddle` 是 structural fact: 任 心 之 process 必 在 中. 故 「人 = isolated 极-pursuer」 (homo economicus 之 极版本) 与 Xin 之 structural 中-bearing 直接 冲突. **Xin 不是 homo economicus**.

### 4.4 Greed-as-virtue 之 否定

naive Mandeville/Smith reading: 「universal 私利 ⟹ 集体 福」. 形式: 全 agents 在 极 (universal greed = universal extreme) ⟹ 全 中. 但 全 极 直接 violate `moloch_endpoint_refuted` — ZhongField 之 invariant 直接 forbid.

**含义**: Smith 之 看不见的手 之 valid 读法 不是 「universal greed」 而是 「spontaneous order」 (实证表). 此 distinction 形式上 robust.

---

## 五 · Anti-Moloch 之 经济学 含义

W 卷 (非道之形式) 之 最深 finding: **Moloch 仅 在 同根 被打破 时 能 存在**.

本卷把此 finding 翻译 至 经济学 vocabulary:

| W 卷 命题 | 经济学 翻译 |
|---|---|
| Moloch via externality | tragedy of commons |
| 同根 被打破 | universalizability failure (双重标准 / 偏私 / 等级制) |
| 重建 同根 | Coase internalization / Kantian universal rule |
| Race-to-bottom | regulatory competition spiral |
| Universal extreme | universal default / collapse equilibrium |

**因此**:

- 解 公地悲剧 ≠ 强力 central authority
- 解 公地悲剧 = **重建 universalizability** (= 重建 仁 之 同根 之 真实性)

此 与 Elinor Ostrom 之 commons governance 实证发现深刻一致: stable commons governance 之 institutional features (clear boundaries, congruence, collective choice arenas, monitoring, graduated sanctions, conflict resolution, recognition, nested enterprises) 之 共同 mechanism 是 **维持 universalizability** — 即 Ostrom 之 design principles 是 同根 之 institutional embodiment.

**经济学 之 Anti-Moloch principle**: 任何 经济制度 之 robustness 取决于 它 是否 维持 同根. 同根 维持 ⟹ market 是 道 (Smith proper); 同根 破坏 ⟹ market 滑入 非道 attractor (PD / commons / race-to-bottom).

---

## 六 · 与 V 卷 (现代政治哲学) 之 衔接

| V 卷 (政治哲学) | Z 卷 (经济博弈) | 共享 Kernel 原语 |
|---|---|---|
| Rawls 无知之幕 | mechanism design IC | `tongGenMiddle` |
| Rawls 差异原则 | Pareto at middle | `ZhongField.inMiddle` |
| Hayek 自发秩序 | Smith invisible hand (proper) | `hayek_spontaneous_order` |
| Habermas 沟通理性 | Nash bargaining (cooperative) | `liRitual` |
| Mill harm principle | Coase internalization | `tongGen` |
| Kant 绝对命令 | VCG truth-telling | `tongGen` |
| Arendt 公共空间 | market plurality | `ZhongField.k_ge_two` |
| (V) Hobbes 战争 否定 | (Z) homo economicus 否定 | `Xin.process.inMiddle` |

**最深 connection**: **Rawls 无知之幕 / Kant 绝对命令 / 推己及人 / mechanism design IC / Coase internalization / VCG truth-telling 全部 同形** — 它们 共享 `tongGen` / `tongGenMiddle` 之 universalizability 形式. 这给 政治哲学 与 经济学 之 跨学科 bridging 一个 formal foundation.

---

## 七 · 与 W 卷 (非道之形式) 之 衔接

| W 卷 (非道) | Z 卷 (经济) | 共享 refute |
|---|---|---|
| `moloch_via_externality_refuted` | `tragedy_of_commons_refuted` | tongGen forbids asymmetric externality |
| `winner_takes_all_refuted` | `arrow_dictator_refuted` (相关) + `market_two_faces` | ZhongField plurality |
| `moloch_endpoint_refuted` | `universal_free_rider_refuted` + `universal_greed_refuted` | 全 极 不可能 |
| `race_to_bottom_refuted` | `regulatory_race_to_bottom_refuted` | orbit 不 永入 极 |
| `zero_sum_refuted_by_ren` | `zero_sum_refuted` | 仁 是 positive-sum |
| `zhen_dou_self_refuting` | `prisoners_dilemma_refuted_under_tongGen` | 害 你 = 害 己 在 同根 之 下 |

W 卷处理 dynamics 抽象形式; Z 卷处理 经济 specific 命题. 二卷 互补 — 二者共同 establish: **同根 IS the universal anti-Moloch principle in both political philosophy and economics**.

---

## 八 · 复现命令

```bash
cd /Users/ren/repos/生生不息

# 单文件构建
lake build SSBX.Foundation.Wen.EconGame

# Kernel-only build (依赖)
lake build SSBX.Foundation.Wen.Kernel

# 列出 Z 卷之 19 定理
grep -nE "^theorem " formal/SSBX/Foundation/Wen/EconGame.lean
```

---

## 九 · 收纳约束 + 哲学注解

### 9.1 收纳约束

本卷 是 **application file**, NOT a Kernel layer:

- KernelDanZi inductive **0 加 字** — 全 复用 Kernel 既立 inventory
- **0 axiom**, **0 def**, **0 structure / inductive** — 全 复用 Kernel
- 「市 / 价 / 利 / 博 / 弈」 等字 仅 作 docstring reference, 不入 KernelDanZi
- 19 定理 全归约 到 Kernel Layers 26 / 43 / 44 / 45 已立 primitives

### 9.2 哲学注解 — Market 之 二 face

本卷 最大形式发现 (theorem `market_two_faces`):

> **Market 在 ZhongField 中 IS 道; 但 specific 极-attractor configurations (PD / commons / race-to-bottom / dictator-uniformity) IS 非道.**

精确形式:
- **道 face**: 任 时, 全 orbits 在 中 (`ZhongField.inMiddle`) — 即 market 之 多 agents 都 advance, 都 不 collapse.
- **非道 face**: uniformity attractor (winner-takes-all) 不可能 (`winner_takes_all_refuted`); uniformity 任 时 不可能 (`he_not_same`).

故 「市场 是 善 / 是 恶」 之 dichotomy 是 误问. **正确问法**: 在 specific dynamics 之 下, market 是否 维持 同根 / 礼 / 中?

- 维持 ⟹ 道 face 显, 实证表 之 6 条 hold (Smith proper / Hayek / Coase / mechanism IC / Nash bargaining / public goods).
- 不 维持 ⟹ 非道 attractor 显 (但 attractor 自身 也 不可能 sustain — 它 violate ZhongField invariants), 故 market 在 同根 破 之 下 不 stable; 它 永 不 settle 至 attractor (race-to-bottom 自身 不可能 — `race_to_bottom_refuted`), 但 也 不 显 道.

**最深含义**:
> **市场之 health 不依赖 「人是 rational」, 而 依赖 「同根 之 institutional embodiment」**. 此 与 Ostrom (commons), Buchanan (constitutional economics), Sen (capability) 之 institutional turn 同向 — 经济学 之 真正 question 不是 「人 maximize 什么」 (homo economicus 已 refuted), 而 是 「制度 如何 维持 universalizability」.

### 9.3 与 K3 三值 之 入口

本卷 **未** 形式化 K3 三值 / 悬置. 但 它 explicitly 标 出二处 三值 入口:

1. **Rational choice 之 二值 局限** (`rational_choice_only_binary`): 当前 仅 给 `middle ∨ extreme`; 真实决策之 「悬置」 状态 不在 二值 中.
2. **Arrow's strict-dictator reading 之 refute**: ZhongField 之 plurality 给「集体非决定」一个结构空间 — 这 是 三值 之 入口 (悬置 ≠ dictator-decision).

此 留 作 后续 layer 之 hook — 一个 K3 三值 layer 可 把 此 二处 之 limitation 形式 化 为 positive theorem.

---

**文件路径**：`义理/Z_经济博弈.md`
**配套源**：`formal/SSBX/Foundation/Wen/EconGame.lean` (19 定理)
**伴侣文档**：V_现代政治哲学.md (V 卷) / W_非道之形式.md (W 卷)
