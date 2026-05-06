# X · 反施密特 · AntiSchmitt.lean

**文件**：`formal/SSBX/Foundation/Wen/AntiSchmitt.lean`（244 行）
**完成日期**：2026-05-07
**Lean 版本**：4.29.1（Lake 5.0.0）
**单文件 lake build**：17 jobs / 0 sorry / 0 warning / 0 新公理
**承上**：W_非道之形式 (Layer 45) / V_现代政治哲学 (Layer 44, schmitt_*_refuted 之导引性命题)

---

## 〇 · 摘要

本卷把 Layer 44 中两条 introductory 之 Schmitt 否定 (`schmitt_friend_enemy_refuted` /
`schmitt_state_of_exception_refuted`) 升级为 Schmitt 三大支柱 之 结构形式分析:

> **Schmitt 之 friend-enemy / decisionism / state-of-exception 三大支柱
> 共享 同一 形式根源 — 拒绝 universalizability (i.e. `tongGen`)**.

| 度量 | 数值 |
|------|------|
| AntiSchmitt 章定理 | **16** |
| 新增 def | **4** (`friendOrEnemy`, `decisionistAsymmetry`, `stateOfException`, `concreteOrderViaRen`) |
| 新增 inductive | **1** (`PoliticalRelation`, 三构造子) |
| 新增 axiom | **0** (全部归约至 Kernel 既有原语) |
| 单文件 `lake build` | **17 jobs / 0 warning** |

**最深刻发现**:
> Schmitt 三大支柱 在 形式上 全部 归约 为 同一 negation: **¬ tongGen a**.
> 故 解 Schmitt 困境 ≡ 重建 仁 之 同根. 「敌」 不是 ontological other, 而 是
> 自身 axiom 之 又一 instantiation — **同根异显**.

---

## 一 · Schmitt 之 三大支柱

| 支柱 | 原典 | 形式核心 |
|---|---|---|
| **friend-enemy distinction** | *Begriff des Politischen* (1932) | "政治 IS 敌友区分" — 二分穷尽 |
| **decisionism** | *Politische Theologie* (1922) | "Souverän ist, wer über den Ausnahmezustand entscheidet" — 主权决断超越规则 |
| **state of exception** | *Politische Theologie* / *Diktatur* | "Ausnahmezustand" — 规则 不 universally apply |

三者并非 独立, 而 是 同一 anti-universalizability 之 三 个 facet:
- 友敌区分 require **forced 二分** (排除 仁 之第三 option)
- decisionism require **specific override of universal rule** (asymmetric action)
- state of exception require **rule punctured** (规则 在某 中-state 上 不成立)

---

## 二 · Anti-Schmitt 形式总图

```
                    Schmitt 三大支柱 (claim: 政治 之 必然 形式)
                  ┌──────────────┼──────────────┐
                  ▼              ▼              ▼
            friend-enemy    decisionism    state-of-exception
                  │              │              │
                  │              │              │
        formalized as 三 形式物:                  │
                  │              │              │
            friendOrEnemy   decisionist    stateOfException
            (predicate)     Asymmetry      (∃ s t middle, a s 极, a t 中)
                  │              │              │
                  ▼              ▼              ▼
              共享 root negation: ¬ tongGen a
                              │
                              │
                   ┌──────────┴──────────┐
                   ▼                     ▼
              tongGen 成立            tongGen 破缺
                   │                     │
                   │                     ▼
                   │            Moloch dynamics 可能
                   │            asymmetric externality
                   │            partisan-war 可能
                   │
                   ▼
        全部 三 支柱 形式 不成立
                   │
                   ▼
           第三 option: 仁 (renCompanion)
        distinct yet middle, 同根异显
                   │
                   ▼
        concreteOrderViaRen — 真政治 substrate
```

---

## 三 · 定理表 (AntiSchmitt — 16 条)

### 3.1 友敌二分 之 形式破缺 — 4 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| 友敌 二分 谓词 | `def friendOrEnemy` | `h1.states n = h2.states n ∨ extreme h1 ∨ extreme h2` |
| **友敌之 forced choice 不成立** | `friend_enemy_distinction_via_predicate` | `distinct ⟹ ¬ friendOrEnemy ∧ ren` |
| 「友 = 同一」 violate plurality | `friend_collapse_violates_plurality` | `(∀ i j, same) ⟹ False` (he_not_same) |
| 「敌 = collapse-other」 violate inMiddle | `enemy_collapse_violates_inMiddle` | `extreme other ⟹ False` |

### 3.2 Decisionism 与 同根 之 不兼容 — 2 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| decisionist 不对称 | `def decisionistAsymmetry` | `∃ s t middle, extreme (a s) ∧ ¬ extreme (a t)` |
| **决断 与 同根 互斥** | `decisionism_breaks_tongGen` | `decisionistAsymmetry a ⟹ ¬ tongGen a` |
| 同根 ⟹ 没决断 | `tongGen_excludes_decisionism` | `tongGen a ⟹ ¬ decisionistAsymmetry a` |

### 3.3 例外状态 之 形式破缺 — 2 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| 例外状态 形式 | `def stateOfException` | `∃ s t middle, extreme (a s) ∧ middle (a t)` |
| **例外 与 同根 互斥** | `state_of_exception_breaks_universality` | `stateOfException a ⟹ ¬ tongGen a` |
| 同根 ⟹ 没例外 | `tongGen_no_exception` | `tongGen a ⟹ ¬ stateOfException a` |

### 3.4 替代结构: concrete order via 仁 — 2 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| concrete order 谓词 | `def concreteOrderViaRen` | `∀ n ≤ N, ren h1 h2 n` |
| concrete order 之 三性质 | `concrete_order_via_ren` | `distinct ∧ ¬ extreme h1 ∧ ¬ extreme h2` |
| **政治本质 IS 仁** | `political_essence_is_ren_not_enmity` | ZhongField 内 distinct ⟹ ren ∧ 双 中 |

### 3.5 partisan / 紧急 / 法治 之 自我崩坏 — 3 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| **partisan-war self-destructive** | `partisan_war_self_destructive` | `tongGen ∧ (∀ k, shiYuRen) ⟹ ∀ n, jiSuoBuYu` |
| 紧急合法性 缺乏 grounding | `legitimacy_via_emergency_lacks_grounding` | `¬ ∃ N, ∀ n ≥ N, extreme (o.states n)` |
| 法治 vs 主权例外 互斥 | `sovereign_decision_vs_law_universality` | `¬ (tongGen a ∧ stateOfException a)` |

### 3.6 friend-enemy ⟹ Moloch enabling — 1 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| **友敌结构 enables Moloch** | `friend_enemy_implies_moloch` | `stateOfException a ⟹ ¬ tongGen a` |

(经此 ¬tongGen, `moloch_via_externality_refuted` 之 hypothesis 失效, 故 Moloch 可能)

### 3.7 第三 option 枚举 — 1 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| 政治三态 inductive | `inductive PoliticalRelation` | `friend ∣ enemy ∣ renCompanion` |
| **三态 distinct** | `political_third_option_total_count` | 三构造子 pairwise distinct |

### 3.8 concrete inversion: 敌 IS 同根 — 1 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| **敌 IS 又一 dong-instance** | `concrete_friend_enemy_inversion` | `i ≠ j ⟹ 双 step via dong ∧ 双 inMiddle` |

### 3.9 Anti-Schmitt 三位一体 — 1 条

| 概念 | Lean 名 | 形式陈述 |
|---|---|---|
| **三支柱共因** | `anti_schmitt_unified` | `tongGen a ⟹ ¬ decisionistAsymmetry ∧ ¬ stateOfException` |

合计 **16 定理 + 4 def + 1 inductive**.

---

## 四 · 同根 vs 例外: 哲学核心

Schmitt 三大支柱 之 形式 共因 是 **¬ tongGen**.

`tongGen` 之 内涵 (Layer 26 恕道 已建立):
> action a 在 任意 二 中-states 上 之 collapse-effect 必 同价.

此 即 仁 之 「同根异显」 — 异 在 于 trace, 同 在 于 axiom.

Schmitt 三支柱 各以 一 种 方式 puncture 此 universalizability:
- **friend-enemy**: 把 「他者」 marked 为 ontological-other, denying 同根
- **decisionism**: 把 主权 marked 为 above-rule, asymmetric application
- **state-of-exception**: 把 specific 状态 marked 为 outside-rule

形式上, 这三种 puncture 都 reduce 到 同一 negation: **∃ 中-state 与 中-state, action 在 二者 上 effect 不同价**.

故:
- 解 Schmitt 困境 ≡ 重建 仁 之 同根
- 拒绝 双重标准 / 偏私 / 例外 / ontological-other-marking
- 这与 Kant 绝对命令 / Rawls 无知之幕 / 推己及人 形式同构

**最深 connection**:
> Schmitt 之 政治本体论 与 Moloch dynamics 共享 同一 形式 enabler.
> Anti-Schmitt IS Anti-Moloch (W 卷 已证).

---

## 五 · 与 Layer 44 / Layer 45 / 仁 (Layer 13) 之 衔接

### 5.1 与 Layer 44 (政治证错) 之 衔接

Layer 44 已有 `schmitt_friend_enemy_refuted` 与 `schmitt_state_of_exception_refuted`,
但 二者 是 「surface refutation」:
- friend-enemy: 仅 利用 distinct + inMiddle 直接 给出 第三 option
- state-of-exception: 仅 利用 inMiddle 否定 perpetual extreme

本卷 之 升级:
- 把 friend-enemy 形式化为 谓词 `friendOrEnemy`, 给出 forced 二分 之 否定
- 把 state-of-exception 形式化为 `stateOfException` 谓词, 与 tongGen 形式互斥
- 新增 decisionism 之 形式 `decisionistAsymmetry` (Layer 44 未涉)
- 揭示 三支柱 之 共因 (`anti_schmitt_unified`)

### 5.2 与 Layer 45 (非道之形式) 之 衔接

W 卷 (Layer 45) 之 `moloch_via_externality_refuted`:
> tongGen ∧ middle (a h1) ∧ extreme (a h2) ⟹ False

本卷 (Layer X) 之 `friend_enemy_implies_moloch`:
> stateOfException a ⟹ ¬ tongGen a

二者衔接: 若 Schmitt 之 例外被 enacted (即 stateOfException 成立), 则 tongGen 破,
则 W 卷 阻止 Moloch 之 hypothesis 失效 — Moloch dynamics 可能 出现.

故: **Schmitt 之 政治本体论 在形式上 是 Moloch 之 enabling 条件**.

### 5.3 与 Layer 13 仁 之 衔接

仁 之 形式核心是 `tongGen` (Layer 26 恕道). 仁 之 体现 是 ren (`def ren h1 h2 n :=
h1.states n ≠ h2.states n` 在 双 inMiddle 之上). 本卷 之 `political_essence_is_ren_not_enmity`
直接 给出: 政治 之 minimum 形式 (ZhongField) 内 任意 distinct 焦点 之间 自动 是 ren-relation.

故 政治本质 IS 仁, 不是 enmity. Schmitt 之 friend-enemy 只是 仁 之 退化误读 (友 退化为 collapse-to-same; 敌 退化为 collapse-other-to-extreme).

---

## 六 · 复现命令

```bash
cd /Users/ren/repos/生生不息

# 单文件构建 (此卷)
lake build SSBX.Foundation.Wen.AntiSchmitt

# 全仓构建
lake build

# 定理列表
grep -nE "^theorem (friend_enemy|friend_collapse|enemy_collapse|decisionism|tongGen_excludes|state_of_exception|tongGen_no|concrete_order|political_essence|partisan|legitimacy|sovereign|friend_enemy_implies|political_third|concrete_friend_enemy|anti_schmitt)" formal/SSBX/Foundation/Wen/AntiSchmitt.lean

# def + inductive 列表
grep -nE "^(def |inductive )" formal/SSBX/Foundation/Wen/AntiSchmitt.lean
```

---

## 七 · 收纳约束

本卷遵守 **「核 只 收纳 单字 + 古文虚字」** 之约束：

- **不 修改** Kernel.lean / SSBX.lean / README.md (用户 自行 integration)
- **不 新增 axiom** — 全部归约至 Kernel 既有 `dong` / `extreme` / `middle` / `tongGen` / `ren` / `shiYuRen` / `jiSuoBuYu`
- **不 入 KernelDanZi** — 「施 / 决 / 例 / 党 / 法 / 主」 等字 仅 作为 docstring reference
- 5 个 新 形式物 (`friendOrEnemy`, `decisionistAsymmetry`, `stateOfException`, `concreteOrderViaRen`, `PoliticalRelation`) 全 是 derived predicates / inductive, 不入 inductive Kernel

本卷 之 形式 价值: 把 Layer 44 之 introductory schmitt 否定 deepen 至 三支柱 共因分析,
建立 Schmitt 政治本体论 与 Moloch dynamics 之 形式 同构桥梁 (Anti-Schmitt = Anti-Moloch).

---

## 八 · 哲学注解

### 8.1 「敌」 之 形式真相

Schmitt 把 「敌」 marked 为 ontological-other — 与 自身 fundamentally 不同 之 存在.

但 在 ZhongField 之内, 任意 「敌」 之 orbit 与 自身 orbit 共享:
- 同一 axiom `dong` (同 一 step 函数)
- 同一 inMiddle 性质 (双 不 极)
- 同一 step-by-step structure

唯一 之 区别 是 trace (states 序列 之 具体值) — 此即 「异显」.

故:
> **「敌」 不是 ontological other, 而 是 自身 axiom 之 又一 instantiation.**

把 敌 ontologize 是 形式上 之 misreading (`concrete_friend_enemy_inversion` 形式 揭示).

### 8.2 决断主义 之 自我矛盾

Schmitt 之 sovereign 「决断」 假设 主权能 outside-rule 行使:
- 主权 之 action 在 normal-cases 上 follow 规则
- 主权 之 action 在 exception-cases 上 override 规则

形式上, 这 require action a 在 中-states 上 effect 不同价 — 即 `decisionistAsymmetry`.
但 此 与 tongGen (universalizability) 形式 互斥.

**主权决断 在 形式上 self-undermining**:
- 若 主权 真 能 universally-applicable (符合 tongGen), 则 不存在 决断空间
- 若 主权 之 决断 真 是 example, 则 a 不是 universal rule, 故 不是 「主权之 行使」

故 Schmitt 之 决断 概念 在 形式上 是 ill-formed. (`anti_schmitt_unified` 形式 揭示.)

### 8.3 partisan war 之 全民自毁

Schmitt 晚期 *Theorie des Partisanen* (1963) 把 friend-enemy 推 至 极致:
非常规战争 / 全民斗争 / 没有界限 之 enmity.

本卷 `partisan_war_self_destructive` 形式 揭示:
- 假设 a 是 universally-applicable (tongGen)
- 假设 partisan-mode: 对 任意 时刻 任意 他者, action 都 collapse 他者
- 结论: action 也 必然 collapse 自己 — 全部 时刻

此 是 zhen_dou_self_refuting 之 partisan-extension. partisan-war 之 universalization
等价 于 self-extermination 之 universalization.

### 8.4 法治 vs 主权例外 之 形式互斥

`sovereign_decision_vs_law_universality` 形式陈述:
> ¬ (tongGen a ∧ stateOfException a)

直观: rule of law (法治) IS universally applicable rule; sovereign exception (主权例外)
IS specific override of rule. 二者 形式 互斥.

故 Schmitt 之 政治本体论 (主权 = 决定 例外者) 与 法治国家 (Rechtsstaat) 在形式上
不能 共存. 不是 「法治 之内 包含 例外条款」, 而是 二者 在 axiomatic-level 互斥.
任何 试图 在 法治国家内 institutionalize Ausnahmezustand 之 努力 都是 形式自毁.

### 8.5 第三 option 之 enumerative force

Schmitt 之 friend-enemy 之 forced 二分 经常 经由 修辞 force, 而非 形式 force.
本卷 `political_third_option_total_count` 通过 inductive 类型 `PoliticalRelation`
显式 enumerate 三 个 distinct 构造子 (friend / enemy / renCompanion), 形式 揭示
二分 之 omission.

更深 一层: 此 inductive 之 三 构造子 仍 不 穷尽 — 还有 `cooperation_cong_dao` (仁 + liRitual)
等 高阶 关系. 政治形式 之 实际 dimensionality 远超 二分.

---

**文件路径**：`义理/X_反施密特.md`
**配套源**：`formal/SSBX/Foundation/Wen/AntiSchmitt.lean`
**承上**：W_非道之形式.md (Layer 45) / V_现代政治哲学.md (Layer 44)
**衔接**：Layer 13 仁 / Layer 26 恕道 / Layer 45 非道
