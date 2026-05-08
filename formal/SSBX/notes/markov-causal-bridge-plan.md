# Markov-Causal Bridge Plan

目标：用最省力的有限构造，尝试把“中介桥”从方向定理推进到可验证骨架。核心不是先造完整量子引力，而是先证明同一个有限过程结构可以同时读成 Markov/测量过程与因果事件结构。

工作分支：`codex/markov-causal-bridge`

工作区：`/Users/ren/repos/生生不息-markov-causal-bridge`

## 当前状态

- [x] 单独 worktree 已创建，基于 `origin/main`
- [x] 探索计划已建立
- [x] 最小 Lean 模块 `QuantumRelativityMarkovBridge.lean` 已创建
- [x] 最小义理文档 `Markov因果桥 · 大统一最小验证构造.md` 已创建
- [x] 第一轮 `lake build` 通过
- [x] 与上一层 `QuantumRelativityIntegration` 的桥接摘要已闭合

## 打勾规则

每个勾只表示当前仓库中有对应的可检查产物：

| 勾选对象 | 必须满足 |
|---|---|
| Lean 项 | 有 theorem / def / structure，且目标模块 build 通过 |
| 文档项 | 有对应 Markdown 段落，写明 machineChecked / typed skeleton / 未纳入边界 |
| 验证项 | 记录实际命令；失败则不打勾 |
| 理论突破项 | 至少新增一个可复用 theorem，不只新增解释文字 |

## 结果记录规则

- 成功和失败都必须记录在本文的“探索日志”中。
- 失败记录至少写明：尝试目标、失败命令或失败 theorem、失败原因、保留的下一步。
- 不因失败而删除中间判断；失败本身作为边界信息保留。
- 只有机器检查通过的 Lean 项才打勾；解释文字不能替代 theorem。

## 核心设想

最省力中介不从连续几何或 Hilbert 空间开始，而从有限过程开始：

```text
Finite Markov-Causal Process
├─ Markov 读法：状态、转移、路径、终端测量
├─ 因果读法：事件、可达边、过去/未来
└─ 桥接读法：同一终端状态既是测量结果，也是事件记录
```

这条路的优势：

| 优势 | 说明 |
|---|---|
| 有限化 | 初版不碰连续流形、测度论、泛函分析 |
| 可验证 | Lean 可先证明结构性命题 |
| 双投影 | 同一载体天然有过程/概率读法与事件/因果读法 |
| 可升级 | 后续可从权重升级到概率核、复幅、量子通道 |

## 探索方向

### A. 有限过程载体

- [x] 定义 `FiniteProcess`：状态类型、有界状态编码、初态、终态谓词、一步转移关系
- [x] 定义 `ProcessPath` 的 typed skeleton：不追求完整列表证明，先保留“起点/终点/有效性”
- [x] 证明每条有效路径给出一个可达关系：`path_implies_reachable`
- [x] 证明终端状态可以被读成候选测量结果：`terminal_as_measurement_candidate`

目的：先有同一个“过程体”，作为中介的最小载体。

### B. Markov 读法

- [x] 定义 `MarkovKernelSkeleton`：从状态到下一状态支持集或权重
- [x] 初版用 `Nat` 权重，不先证明归一化概率
- [x] 证明若转移权重非零，则存在一步可达：`positive_weight_implies_step`
- [x] 定义路径权重的占位接口：`pathWeight`

目的：把“可能历史 / 转移 / 测量分布”纳入同一有限结构。

### C. 因果读法

- [x] 定义 `CausalEvent` 为状态投影或终端状态投影
- [x] 定义 `causalBefore` 为一步转移的可达闭包骨架
- [x] 证明因果读法保留事件方向：`step_implies_causal_before`
- [x] 标出暂不证明反对称性 / Lorentzian geometry / 度规恢复

目的：把相对论侧先压成最小事件-因果接口，而不是直接上时空流形。

### D. 测量-事件对齐

- [x] 定义 `MeasurementEventBridge`：测量结果与终端事件共享同一底层状态
- [x] 证明 `measurement_event_alignment`：同一终端状态在两种投影下对齐
- [x] 证明该对齐不是 tagged physical-language collapse：复用 `tagged_addition_noncollapse`
- [x] 给出 public summary theorem

目的：突破点在这里：证明“测量结果成为事件”至少有一个有限 typed skeleton。

### E. 与既有中介桥层对接

- [x] 从 `MeasurementEventBridge` 构造或解释为 `BridgeTerm` 的实例读法
- [x] 证明保留两面：`markov_bridge_keeps_quantum_and_relativity_faces`
- [x] 证明仍是同根非同一：`markov_bridge_same_one_not_identity`
- [x] 更新 `QuantumRelativityIntegration` 或新模块摘要，不破坏 tagged physical-language noncollapse 边界

目的：不是否定 `192 × 371` 文构造覆盖，而是在 tagged physical-language noncollapse 边界内给出最小中介构造。

### F. 后续升级，不纳入第一轮

- [ ] 从 `Nat` 权重升级到归一化概率
- [ ] 从经典 Markov kernel 升级到 quantum channel / amplitude skeleton
- [ ] 加入干涉：路径权重不只是概率相加
- [ ] 加入因果局部性：下一步只依赖局部过去
- [ ] 探索经典极限：稳定可达结构是否能读成粗粒度时空
- [ ] 探索经验接口：候选可测差异如何进入 pending ledger

这些项先列方向，不在第一轮证明里关闭。

## 第一轮最小目标

第一轮只追求一个可构建的 Lean 骨架：

```lean
theorem markov_causal_bridge_summary :
    HasMarkovProjection P
    ∧ HasCausalProjection P
    ∧ MeasurementEventsAlign b
    ∧ keepsQuantumFace MarkovCausalRoute = true
    ∧ keepsRelativityFace MarkovCausalRoute = true
    ∧ sameOne .quantumSpace .relativisticSpacetime
    ∧ ¬ CurrentPhysicalUnity .quantumSpace .relativisticSpacetime
    ∧ ¬ DirectUnificationByAddition
```

如果这个 theorem 通过，才算完成第一轮突破。

## 文件清单

| 文件 | 作用 |
|---|---|
| `formal/SSBX/Foundation/Modern/QuantumRelativityNoGo.lean` | tagged 物理语言非坍缩边界与兼容旧入口 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityWenBoundary.lean` | `192 × 371` 文构造覆盖与 tagged 边界相容性 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean` | 最小 Markov/因果桥 Lean 骨架 |
| `formal/SSBX/notes/markov-causal-bridge-verification-plan.md` | 回归验证、边界审计、失败记录与下一轮升级验证路线 |
| `义理/文构造完备与直相加边界.md` | 用户提出 `192 × 371` 修正后的边界说明 |
| `义理/Markov因果桥 · 大统一最小验证构造.md` | 义理说明、边界声明、Lean 锚点 |
| `formal/SSBX.lean` | 已加入顶层 import |
| `docs-next/10_formal_形式/modern.md` | 已登记 Modern 模块 |

## 当前判断

Markov 不是最终统一理论；它是最省力的第一块脚手架。它能把“过程、转移、路径、测量、事件、因果”放进同一个有限结构里，让我们先证明一个最小双读模型，再决定哪些部分需要升级成量子通道、复幅、因果集或几何极限。

## 探索日志

### 2026-05-08 · 开局

- 成功：创建独立 worktree `/Users/ren/repos/生生不息-markov-causal-bridge`。
- 成功：创建计划文件 `formal/SSBX/notes/markov-causal-bridge-plan.md`。
- 成功：用户授权并行 agents 后，启动并行探索。
- 成功：Explorer Franklin 完成概率/Markov/转移模式检索。
  - 结论：仓库没有现成 Lean Markov kernel 定义。
  - 可复用根基：`KolmogorovExt` 的概率边界锚点、`BaguaAlgebra` 与 `OperatorReachabilitySemantics` 的有限转移模式、`MonadRoot.Reachable` 的抽象可达模式。
  - 建议：第一轮不引入重型 `IIDWlln`，除非要证明独立/极限定理。
- 成功：Explorer James 完成事件/因果/测量边界命名检索。
  - 结论：应复用 `QuantumRelativityIntegration` 的 `mediatedBridge`、`BridgeTerm`、同根非同一边界语言。
  - 文档边界：使用 “finite typed skeleton”、“measurement-event interface”、“same carrier, two readings”，避免 “proves quantum gravity” 等强话。
- 成功：Worker Poincare 创建 companion Markdown `义理/Markov因果桥 · 大统一最小验证构造.md`，并通过 `git diff --check -- '义理/Markov因果桥 · 大统一最小验证构造.md'`。
- 成功：创建最小 Lean 模块草案 `formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean`。
- 成功：补充 `FiniteProcess.stateCode/stateBound/stateCode_lt_bound/stateCode_injective`，把“有限过程”至少编码为有界状态码骨架；保留完整 `Fintype`/概率归一化为后续升级。
- 成功：补充 `MeasurementEventBridge.toBridgeTerm` 与 `measurement_event_bridge_term_keeps_faces`，把本层测量-事件桥接到上一层 `BridgeTerm` tag-level 读法。
- 成功：采纳 `192 × 371` 修正，新增 `QuantumRelativityWenBoundary.lean` 与 `文构造完备与直相加边界.md`；将 `current-language no-go` 旧说法降级为 tagged physical-language noncollapse，不再把它读成文构造不可能性。
- 失败 / 基础设施阻塞：首次在新 worktree 原生运行 `lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge` 时，进程卡在 `git clone https://github.com/leanprover-community/mathlib4.git` 超过十分钟，尚未进入 Lean 检查；保留结论为“依赖克隆阻塞”，不是 theorem 失败。
- 成功：改用主 worktree 同 revision 依赖缓存，复制 `.lake/build` 到本 worktree，并重新运行 `lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge`。
- 成功：`lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge` 通过，输出 `Build completed successfully (6 jobs).`
- 成功：补齐顶层 import `SSBX.Foundation.Modern.QuantumRelativityMarkovBridge` 与 Modern 文档索引。
- 成功：`lake build SSBX.Foundation.Modern.QuantumRelativityWenBoundary` 通过，输出 `Build completed successfully (28 jobs).`
- 成功：`lake build SSBX` 通过，输出 `Build completed successfully (2886 jobs).`
- 备注：`lake build SSBX` 输出了既有 Wen 模块的 unused simp argument linter 警告；本轮新增 `QuantumRelativityMarkovBridge.lean` 与 `QuantumRelativityWenBoundary.lean` 无警告。
- 成功：新增验证计划 `formal/SSBX/notes/markov-causal-bridge-verification-plan.md`，单独记录回归命令、锚点审计、边界审计、升级路线与失败模板。
