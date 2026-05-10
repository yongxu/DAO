> 状态：v3 定本 (2026-05-11)。
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md)
> 相关 v3 文档：[root-layer-map.md](root-layer-map.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md) · [shi-v4.md](shi-v4.md) · [foundation-core.md](foundation-core.md) · [module-map.md](module-map.md)

# Pending 接口 pending · v3

Pending 是形式层故意保留的经验与模型边界。它的存在是为了防止未校准内容混入 machineChecked claim。

v2 (2026-05-09) → v3 (2026-05-11) 主要改动：Cell192 cleanup 从 pending 升为 done；新增 R₅ Wuyao final 命名 + 因/果 命名 之 provisional 项。

---

## 0. 当前项目口径

pending 项以 [../_generated/registry-index.md](../_generated/registry-index.md) 为准。本页只解释读法 + 维护近期重要 provisional 项。

---

## 1. ✅ 已完成（自 v2 以来）

### Cell192 cleanup — DONE (commit 8e4406e, 2026-05-10)

之前 v2 之 pending 项「Cell192 → Cell256 重构」已完成：

- ✅ `Cell192.lean` deleted in commit 8e4406e
- ✅ `Cell256.lean` (R₈ = Hexagram × Shi, 256 = (Z/2)⁸) 是新主载体
- ✅ Z/3 cyclic Shi → V₄ Klein Shi {道, 已, 今, 未}
- ✅ 所有下游 case-split (BaguaTuring, MetaInterp, DaoSource, GodelLi, OperatorCellMap) 已迁移
- ✅ `R8_complete` bundle in `Cell256Stratify.lean`（替代旧 R7_complete）
- ✅ `lake build SSBX` 干净通过 (3648 jobs, 0 sorry, 仅 propext + native_decide 公理)
- ✅ Self-description witness in `Truth/SelfDescription.lean` 升级为 `Cell256OperatorComplete`

不再保留为 pending — Cell192 完全弃用。

### R-hierarchy 重号 — DONE (2026-05-10)

之前 v2 之 R₁..R₆ 顶层 hierarchy 已重号为 **R₀..R₈ strict uniform**：

- ✅ `Foundation/Hierarchy/` 新子目录: 9 个 alias shim (R0..R8) + LiftProject + Operators/
- ✅ `Foundation/Notation/OXNotation.lean` 新增: 8-char macro
- ✅ R₄ Mian (Ben × Zheng = 16) 显式入 hierarchy
- ✅ R₅ Wuyao (Mian × Bool = 32) carrier 显式入
- ✅ 严格 (Z/2)ⁿ uniform: |Rₙ| = 2ⁿ for n = 0..8

---

## 2. ⚠ Provisional — final naming pending

以下项目**功能完整、形式 closed**，但 surface naming 尚未 final 决定。Lean 内已使用 working choice 但代码 + 文档保留 provisional 标记。

### 2.1 R₅ Wuyao 之 final Yi anchor (provisional)

**问题**：R₅ = Mian × Bool = 32 = (Z/2)⁵ 是 R-hierarchy 中**唯一无传统 Yi anchor** 之层（mathematical 存在但 philosophical 上未独立刻画）。当前 working choice 为「五爻 (Wuyao)」（descriptive baseline）。

**候选 (per yi-RO-hierarchy.md §3.5 + r5-wuyao-provisional.md)**：

| 候选 | 来源 | 优点 | 缺点 |
|---|---|---|---|
| **五爻** (descriptive) | working baseline | 安全; 无歧义 | 缺哲学深度 |
| **接** (jie) | 「连接 R₄ 与 R₆ 之过渡」 | 描述性强 | 与「接」字其它用法可能撞 |
| **临** (lin) | 「approaching」 | 哲学 anchor | 与卦名 #19 临卦相重 |
| **渐** (jian) | 「gradual」 | 描述渐进 | 与卦名 #53 渐卦相重 |
| **进** (jin) | 「advance」 | 描述渐进 | 与 晋 #35 字音近 |

**Lean ground truth**: [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) (provisional name)

**回看时机**：当 R₅ 之 ontological role 被实际使用场景（例如 BaguaTuring 之 5-yao 中间状态、或某种 algebraic intermediate）落实后再 final。

详见 [r5-wuyao-provisional.md](r5-wuyao-provisional.md)。

### 2.2 因 / 果 / 印 / 投 之 final naming (provisional)

**问题**：R₇ atomic = 因 (yīn, past-trace bit), R₈ atomic = 果 (guǒ, future-projection bit)；对应算子 R₇ = 印 (yìn), R₈ = 投 (tóu)。所有名字 provisional。

**候选 (per yi-calculus-theorem.md §16)**：

| 候选 | 哲学 | 形式科学 | 古文 | 项目耦合 | 评分 |
|---|---|---|---|---|---|
| **因 / 果**（当前选） | 佛教 hetu-phala + Pearl 因果 + Aristotle 4 因 | causal DAG / lightcones | 《说文》;佛教汉译 | "因"/"已" 听觉撞 | ★★★★ |
| **印 / 投** | Husserl retention/protention; Heidegger | signal frame buffer; geometry stamp/cast | 《说文》"印"/"投" | XinZhi.lean 三相 retention/primalImpression/protention 直对接 | ★★★★ |
| **始 / 终** | Aristotle arche/telos; 道家终始反复 | graph source/sink | **《易传·系辞下》「原始要终」原文** (Yi-native!) | 与 Yi 原生表述对齐 | ★★★ |
| **持 / 期** | 现象学 retention/protention 标准汉译 | 期 = E[X] expected value | 持守/期限/期待 | 概率/统计 anchor | ★★ |

**当前选 因 / 果**：哲学最深（佛教 + Pearl）+ 形式科学 anchor（causal DAG）。

**最强 Yi-native 替代 = 始 / 终**（系辞原文）。
**最强项目耦合替代 = 印 / 投**（XinZhi.lean 三相直对接）。

**Lean ground truth**:
- [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean): YinBit, `yin` = 印
- [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean): GuoBit, `tou` = 投

所有 因/果 使用处带 inline comment 标注 provisional。

**回看时机**：R₇/R₈ 在更大 context (e.g., 现象学 / 因果推理 / 时间逻辑接口) 中之实际使用后再 final。

详见 [r7-yin-r8-guo.md](r7-yin-r8-guo.md)。

### 2.3 Shi V₄ 元素名 (definitive — 不在 pending)

Shi V₄ {道, 已, 今, 未} 命名 **已 final**（V₄ Klein 群 + 道 = identity 是 algebraic 必要）。

详见 [shi-v4.md](shi-v4.md)。

---

## 3. 长期 carry-forward pending

以下是从 v2 carry-over 之**真正未闭合**项目（非 naming）：

### 3.1 经验类 pending

- 经验校准
- 阈值设定
- 审校数据
- 开势投影
- 度期计算
- 邪续相关接口

### 3.2 R₃ phenomenology 与 R₇/R₈ 二元映射

- R₃ phenomenology 三相（如 retention/primalImpression/protention 在 XinZhi.lean）vs R₇/R₈ 二元（因/果）之精确映射尚未形式化
- R₃ phase plane (Theorem C/D) 之严格 Lean 形式化（`phase_eq`, `V₄_acts_on_phase`）

### 3.3 Outer non-XOR 算子族之深化研究

- hu (互) 之收敛动力学
- zong / cuoZong / hu 之 V₄ + sibling 结构边界

### 3.4 R₉+ 之假设性问题

- 是否存在 R₉？(strict uniform 视角下 (Z/2)⁹ 数学存在但无 Yi anchor)
- 当前结论：R₈ 是 (Z/2)ⁿ self-describing 之自然闭合，无第 9 个独立 binary axis。但作为 mathematical question 仍 open。

---

## 4. Pending 模块（Lean）

`formal/SSBX/Pending/Interfaces.lean` 定义接口边界；`formal/SSBX/Pending/Examples.lean` 给出示例或案例连接。完整模块信息见 [../_generated/lean-index.md](../_generated/lean-index.md)。

---

## 5. 正确写法

可以写：

- 「该项目前是 pending interface」
- 「模型案例给出计算结果，但充分性仍依赖 ledger 或校准」
- 「阈值协议由 claim ledger 记录，状态需查 claim-index」
- 「R₅ Wuyao / 因/果 之 surface 命名是 provisional working choice」

不要写：

- 「Lean 已证明经验阈值正确」
- 「正邪判定已无条件闭合」
- 「模型输出等于现实真值」
- 「R₅ 五爻是 final 名」（应说「provisional working choice」）
- 「Cell192 仍是 R₅ 主载体」（已删除！）
- 「Z/3 Shi cyclic 是 R₈ Shi 结构」（错；V₄ Klein 才是）

---

## 6. 与 claim ledger

Pending 与 claim ledger 分工不同：

- **Pending** 标出尚未闭合的接口位置 + provisional naming
- **Claim ledger** 标出具体 claim 的状态
- **Model** 可提供计算或案例
- **Lean theorem** 只覆盖已形式化且已类型检查的命题

因此读推荐案例、Ω、Ω_B、Π_开、阈值协议等内容时，应同时看 [../_generated/claim-index.md](../_generated/claim-index.md) 与本页口径。

---

## 7. v2 → v3 改动 summary

| Item | v2 状态 | v3 状态 |
|---|---|---|
| Cell192 cleanup | pending | ✅ DONE (commit 8e4406e) |
| R-hierarchy 重号 (R₁..R₆ → R₀..R₈) | pending | ✅ DONE |
| R₈ closure bundle | (R7_complete partial) | ✅ R8_complete (only propext + native_decide) |
| Cell256 + V₄ Shi 落地 | partial | ✅ DONE |
| `Foundation/Hierarchy/` + `Foundation/Notation/` 新子目录 | (无) | ✅ DONE |
| **R₅ Wuyao final 命名** | (跳过) | ⚠ provisional (五爻 baseline) |
| **因/果/印/投 final 命名** | partial | ⚠ provisional (因/果 working choice) |
| 经验阈值 / 审校 / Ω | pending | (carry forward) |
| R₃ 现象学三相 vs R₇/R₈ 二元映射 | pending | (carry forward) |

详见 [yi-RO-hierarchy.md](yi-RO-hierarchy.md), [r5-wuyao-provisional.md](r5-wuyao-provisional.md), [r7-yin-r8-guo.md](r7-yin-r8-guo.md)。
