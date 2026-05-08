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
- [x] S2 有限概率核接口已闭合：非终端行分母非零，权重受分母约束
- [x] S3 路径组合与局部因果约束已闭合：组合 path witness 给出可达 / 因果读法，code-successor 排除一步自环
- [x] S4 经典 Markov / 量子振幅-通道分层候选已闭合：layer separation、channel 到 S2 边界投影、非零振幅支持精化
- [x] S5 干涉与测量律候选接口已闭合：path amplitude candidate、相消 witness、Born-shaped boundary
- [x] S5b 非零路径振幅候选已闭合：非零 path amplitude 推出 valid / Reachable / causalBefore，并给 concrete bridge 一个非零 witness
- [x] S5c 双路径相消候选已闭合：同端点、不同中间态的 two-step candidate paths 携带 `1` 与 `-1`，有限和为 `0`
- [x] S5d 离散相位标记候选已闭合：`zero/pi` 标签导出 `1/-1`，并保持 two-path cancellation
- [x] S5e 离散作用量相位候选已闭合：edge phase increments 累积为 path phase，upper/lower 相对相位为 `pi`，并保持 two-path cancellation
- [x] S5f 有限路径族求和候选已闭合：two-route upper/lower pair 被改写为 finite same-endpoint path family，family sum 为 `0`
- [x] S5g 有限路径族求和代数候选已闭合：append / permutation / reverse stability 与 cancellation stability 已形式化
- [x] S5h 端点索引路径族候选已闭合：same-endpoint ledger 可转换为 endpoint-indexed finite family，且保持 sum/weight
- [x] S5i 端点支撑规范化候选已闭合：amplitude-complete filter 保持 sum/weight，duplicate expansion 显式给出 `sum + sum`
- [x] S5j 双路径枚举候选已闭合：twoRoute source/target two-step middle 只能是 `upper` 或 `lower`
- [x] S5k 路径身份键候选已闭合：two-step path key 保留 `start/middle/stop`，upper/lower keys 不同
- [x] S5l 有限键商候选已闭合：visible-key equivalence、key-compatible amplitude descent 与 two-route key-level cancellation 已形式化
- [x] S5m 路径商类候选已闭合：visible-key quotient class、quotient descent 与 two-route quotient completeness 已形式化
- [x] S5n 规范代表元候选已闭合：two-route toy quotient classes 的 displayed canonical representative boundary 已形式化
- [x] S5o 商支撑枚举候选已闭合：two-route toy quotient support enumeration 与 quotient-level finite cancellation 已形式化
- [x] S5p 商支撑代数候选已闭合：quotient-support append / permutation / reverse / duplicate cancellation stability 已形式化
- [x] S5q 观测账本候选已闭合：two-route quotient-support cancellation 可登记为 pending observable ledger entry，且 pending entry 不等于 empirical closure
- [x] S5r 作用量相位律候选已闭合：finite period-two action index 可导出 `1/-1`，在 quotient support 上相消，并接回 pending observable ledger
- [x] S8 逐步统一候选摘要已闭合：concrete bridge、finite probability、`71232` grid、S5r action-phase cancellation、pending ledger 与未闭合边界列表已合取成 public summary theorem
- [x] S9 有限概率归一化候选已闭合：concrete 与 `71232` grid kernel 有显式 row support，非终端行 normalized-row-total candidate 为 `1`
- [x] S10 归一化质量求和候选已闭合：`rowWeightSum_eq_rowTotal` 有命名出口，且 concrete/grid 非终端行的逐项 `normalizedMass` 求和为 `1`
- [x] S11 Born 权重条件归一候选已闭合：有限 amplitude support 若已由 `ampProb` 归一，则 `candidateWeight` 非负且求和为 `1`
- [x] S12 Born 分布边界候选已闭合：normalized amplitude support 可打包进 finite probability distribution interface，并保留 amplitude sum / support / candidateWeight 投影

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
- [x] 初版用 `Nat` 权重，不先证明 sum-one 概率律
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

### F. 后续升级

- [x] 从 `Nat` 权重升级到有限概率核 denominator interface
- [x] 加入最小路径组合与 code-successor/no-self-loop 因果约束
- [x] 从经典 Markov kernel 旁开 quantum amplitude / channel skeleton candidate
- [x] 加入 path amplitude / interference / Born-shaped candidate interface
- [x] 加入非零 path-amplitude candidate witness，并证明非零候选振幅不跑出 path / causal boundary
- [x] 加入 two-path finite cancellation candidate，并证明同端点、不同中间态两路径候选振幅相消
- [x] 加入 discrete phase-label candidate，并证明相反候选振幅可由 `zero/pi` 标签导出
- [x] 加入 discrete edge-action phase candidate，并证明 path phase 可由 edge increments 累积得到
- [x] 加入 finite family path-sum candidate，把 two-path sum 推到有限路径族
- [x] 加入 finite path-sum algebra candidate，证明 append / permutation / reverse stability
- [x] 加入 endpoint-indexed finite family candidate，把同端点 ledger 收进路径族索引
- [x] 加入 endpoint support normalization candidate，证明 amplitude-complete filter 与 duplicate handling boundary
- [x] 加入 two-route source/target two-step enumeration candidate，证明 toy middle enumeration complete
- [x] 加入 finite two-step path identity key candidate，证明 toy source/target key enumeration complete
- [x] 加入 finite visible-key quotient candidate，证明 key-compatible amplitude 可降到 key 层且 two-route key sum 相消
- [x] 加入 visible-key quotient class construction，证明 quotient descent 与 toy source/target quotient completeness
- [x] 加入 two-route canonical representative candidate，证明 toy source/target quotient classes 由 displayed paths 代表
- [x] 加入 finite quotient-support enumeration 与 algebra，证明 quotient-level cancellation、append/permutation/reverse/duplicate stability
- [x] 加入 observable ledger candidate boundary，把 quotient-support cancellation 登记为 pending observable entry
- [x] 加入 finite action-to-phase law candidate，把 action index `0/1` 导出的相消接回 quotient support 与 pending ledger
- [x] 加入 stepwise unification candidate summary，把本分支已关闭结构合取，并显式列出未关闭物理边界
- [x] 证明 finite row sum-one 概率律：concrete 与 `71232` grid 的非终端行归一为 `1`
- [ ] 证明真实 quantum channel law：unitary evolution / CPTP / Kraus 或 density-matrix law
- [ ] 证明真实干涉律：一般 path integral、连续相位/作用量演化与可测相消
- [ ] 加入更强因果局部性：下一步只依赖局部过去或邻域
- [ ] 探索经典极限：稳定可达结构是否能读成粗粒度时空
- [x] 探索经验接口：候选可测差异如何进入 pending ledger 的最小形式，已由 S5q 关闭 pending observable entry boundary
- [ ] 探索经验接口：外部数据、误差模型、阈值与可测预言 theorem

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
| `formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean` | 三状态 concrete bridge witness |
| `formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean` | `71232` operator-cell grid bridge process |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | S2 有限概率核接口：row denominator、normalizable row、bounded weight |
| `formal/SSBX/Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | S3 路径组合与局部因果约束：composable path、causalBefore、no self step |
| `formal/SSBX/Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | S4 经典 Markov / quantum amplitude-channel 分层候选接口 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | S5 path amplitude / interference / Born-shaped candidate interface |
| `formal/SSBX/Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | S5b nonzero path-amplitude candidate witness 与 path/causal boundary |
| `formal/SSBX/Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | S5c two-path finite cancellation candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | S5d discrete phase-label candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | S5e discrete edge-action phase accumulation candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | S5f finite path-family sum candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | S5g finite path-sum algebra candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | S5h endpoint-indexed finite path-family candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | S5i endpoint support normalization candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean` | S5j two-route source/target two-step enumeration candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityPathIdentityBridge.lean` | S5k finite two-step path identity-key candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | S5l finite visible-key quotient candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityPathQuotientBridge.lean` | S5m visible-key quotient class candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityCanonicalRepresentativeBridge.lean` | S5n two-route canonical representative candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityQuotientSupportBridge.lean` | S5o finite quotient-support candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityQuotientSupportAlgebraBridge.lean` | S5p quotient-support algebra candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | S5q observable ledger candidate boundary |
| `formal/SSBX/Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | S5r finite action-to-phase law candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityStepwiseUnificationBridge.lean` | S8 current stepwise unification candidate summary |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | S9 finite probability normalization candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | S10 normalized finite mass probability law |
| `formal/SSBX/Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | S11 conditional Born-weight normalization law |
| `formal/SSBX/Foundation/Modern/QuantumRelativityBornDistributionBridge.lean` | S12 finite Born distribution boundary |
| `formal/SSBX/notes/markov-causal-bridge-verification-plan.md` | 回归验证、边界审计、失败记录与下一轮升级验证路线 |
| `formal/SSBX/notes/unification-stepwise-plan.md` | 逐步完善到候选统一的阶段路线 |
| `义理/文构造完备与直相加边界.md` | 用户提出 `192 × 371` 修正后的边界说明 |
| `义理/Markov因果桥 · 大统一最小验证构造.md` | 义理说明、边界声明、Lean 锚点 |
| `义理/有限概率核接口 · Markov桥S2.md` | S2 companion 文档，记录有限概率核接口与未关闭范围 |
| `义理/路径组合与因果约束 · Markov桥S3.md` | S3 companion 文档，记录路径组合、code-successor 与 no-self-loop 边界 |
| `义理/经典Markov与量子振幅分层 · Markov桥S4.md` | S4 companion 文档，记录 classical Markov 与 amplitude/channel candidate 的分层边界 |
| `义理/干涉与测量律候选 · Markov桥S5.md` | S5 companion 文档，记录 path amplitude、interference candidate 与 Born-shaped boundary |
| `义理/非零路径振幅候选 · Markov桥S5b.md` | S5b companion 文档，记录非零候选 witness 与未关闭的真实干涉边界 |
| `义理/双路径相消候选 · Markov桥S5c.md` | S5c companion 文档，记录 two-path finite cancellation candidate 与未关闭的真实干涉边界 |
| `义理/离散相位标记候选 · Markov桥S5d.md` | S5d companion 文档，记录 discrete phase-label candidate 与未关闭的相位动力学边界 |
| `义理/离散作用量相位候选 · Markov桥S5e.md` | S5e companion 文档，记录 edge-action phase accumulation candidate 与后续 action/path-sum 结构 |
| `义理/有限路径族求和候选 · Markov桥S5f.md` | S5f companion 文档，记录 finite path-family sum candidate；path-sum 代数由 S5g 承接 |
| `义理/有限路径族求和代数候选 · Markov桥S5g.md` | S5g companion 文档，记录 finite path-sum algebra candidate 与后续 finite enumeration boundary |
| `义理/端点索引路径族候选 · Markov桥S5h.md` | S5h companion 文档，记录 endpoint-indexed finite path-family candidate；support normalization 已由 S5i 承接 |
| `义理/端点支撑规范化候选 · Markov桥S5i.md` | S5i companion 文档，记录 amplitude-complete filter、sum/weight preservation 与 duplicate handling boundary |
| `义理/双路径枚举候选 · Markov桥S5j.md` | S5j companion 文档，记录 two-route toy source/target middle enumeration |
| `义理/路径身份键候选 · Markov桥S5k.md` | S5k companion 文档，记录 visible path-key boundary 与 toy key completeness |
| `义理/有限键商候选 · Markov桥S5l.md` | S5l companion 文档，记录 finite visible-key quotient candidate 与 key-level cancellation |
| `义理/路径商类候选 · Markov桥S5m.md` | S5m companion 文档，记录 visible-key quotient class construction 与 quotient completeness |
| `义理/规范代表元候选 · Markov桥S5n.md` | S5n companion 文档，记录 two-route canonical representative boundary |
| `义理/商支撑枚举候选 · Markov桥S5o.md` | S5o companion 文档，记录 quotient support enumeration 与 quotient-level cancellation |
| `义理/商支撑代数候选 · Markov桥S5p.md` | S5p companion 文档，记录 quotient-support algebra 与 cancellation stability |
| `义理/观测账本候选 · Markov桥S5q.md` | S5q companion 文档，记录 observable ledger candidate boundary 与 pending empirical status |
| `义理/作用量相位律候选 · Markov桥S5r.md` | S5r companion 文档，记录 finite action-to-phase law candidate |
| `义理/逐步统一候选摘要 · Markov桥S8.md` | S8 companion 文档，记录 current stepwise unification candidate summary |
| `义理/有限概率归一化候选 · Markov桥S9.md` | S9 companion 文档，记录 finite row sum-one normalization boundary |
| `义理/归一化质量求和候选 · Markov桥S10.md` | S10 companion 文档，记录 normalized mass sum-one boundary |
| `义理/Born权重条件归一候选 · Markov桥S11.md` | S11 companion 文档，记录 conditional Born-weight normalization boundary |
| `义理/Born分布边界候选 · Markov桥S12.md` | S12 companion 文档，记录 finite Born distribution boundary |
| `formal/SSBX.lean` | 已加入顶层 import |
| `docs-next/10_formal_形式/modern.md` | 已登记 Modern 模块 |

## 当前判断

Markov 不是最终统一理论；它是最省力的第一块脚手架。它能把“过程、转移、路径、测量、事件、因果”放进同一个有限结构里。S4 已经把经典 Markov 层与量子振幅 / 通道候选层分开，S5 已经把 path amplitude、相消候选和 Born-shaped boundary 接上，S5b 已经给出非零候选振幅 witness 并把它投回 valid / Reachable / causalBefore，S5c 已经给出同端点、不同中间态的 two-path finite cancellation candidate，S5d 已经给出 discrete phase-label candidate，S5e 已经把 path phase 推到 edge increments 的有限累积，S5f 已经把 two-path sum 推到 finite path-family sum，S5g 已经补上 append / permutation / reverse stability，S5h 已经把同端点 ledger 收进 endpoint-indexed family，S5i 已经补上 amplitude-complete filter 与 duplicate handling boundary，S5j 已经关闭 two-route toy source/target middle enumeration，S5k 已经补上 visible path-key boundary，S5l 已经补上 finite visible-key quotient candidate，S5m 已经构造 visible-key quotient class，S5n 已经补上 two-route canonical representatives，S5o 已经补上 finite quotient-support enumeration，S5p 已经补上 quotient-support algebra，S5q 已经把 quotient-support cancellation 登记为 pending observable ledger entry，S5r 已经把 finite action-to-phase law 接到 quotient support 与 pending ledger，S8 已经把当前已关闭结构合取为 stepwise unification candidate summary，S9 已经把 concrete 与 grid kernel 的有限行归一化为 `1`，S10 已经把逐项 `normalizedMass` 的有限和证明为 `1`，S11 已经关闭 normalized amplitude support 条件下的 candidateWeight 非负与 sum-one，S12 已经把 amplitude support / amplitude sum / candidateWeight projection 装入 finite probability distribution interface；后续应处理 channelCompose、Born rule derivation、可测预言 ledger、连续相位/作用量律、一般 path integral、真实 channel law、因果集或几何极限。

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
- 成功：补充 `FiniteProcess.stateCode/stateBound/stateCode_lt_bound/stateCode_injective`，把“有限过程”至少编码为有界状态码骨架；保留完整 `Fintype`/sum-one 概率律为后续升级。
- 成功：补充 `MeasurementEventBridge.toBridgeTerm` 与 `measurement_event_bridge_term_keeps_faces`，把本层测量-事件桥接到上一层 `BridgeTerm` tag-level 读法。
- 成功：采纳 `192 × 371` 修正，新增 `QuantumRelativityWenBoundary.lean` 与 `文构造完备与直相加边界.md`；将 `current-language no-go` 旧说法正名为 tagged physical-language noncollapse，不再把它读成文构造不可能性。
- 失败 / 基础设施阻塞：首次在新 worktree 原生运行 `lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge` 时，进程卡在 `git clone https://github.com/leanprover-community/mathlib4.git` 超过十分钟，尚未进入 Lean 检查；保留结论为“依赖克隆阻塞”，不是 theorem 失败。
- 成功：改用主 worktree 同 revision 依赖缓存，复制 `.lake/build` 到本 worktree，并重新运行 `lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge`。
- 成功：`lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge` 通过，输出 `Build completed successfully (6 jobs).`
- 成功：补齐顶层 import `SSBX.Foundation.Modern.QuantumRelativityMarkovBridge` 与 Modern 文档索引。
- 成功：`lake build SSBX.Foundation.Modern.QuantumRelativityWenBoundary` 通过，输出 `Build completed successfully (28 jobs).`
- 成功：`lake build SSBX` 通过，输出 `Build completed successfully (2886 jobs).`
- 备注：`lake build SSBX` 输出了既有 Wen 模块的 unused simp argument linter 警告；本轮新增 `QuantumRelativityMarkovBridge.lean` 与 `QuantumRelativityWenBoundary.lean` 无警告。
- 成功：新增验证计划 `formal/SSBX/notes/markov-causal-bridge-verification-plan.md`，单独记录回归命令、锚点审计、边界审计、升级路线与失败模板。

### 2026-05-08 · 逐步完善轮

- 成功：rebase 当前 head，确认 `codex/markov-causal-bridge` 已在最新 `origin/main` 上。
- 成功：按用户要求启动并行 agents。
  - Explorer Raman 给出 `Fin allOperatorCells.length` 的 `71232` 状态 grid bridge 方案。
  - Worker Boyle 新增 `QuantumRelativityConcreteBridge.lean`，关闭三状态 `prepared → evolved → measured` concrete witness。
  - Worker Descartes 新增 `unification-stepwise-plan.md`，给出 S0-S8 逐步验证路线。
- 成功：新增 `OperatorCellGridMarkovBridge.lean`，把 `371 × 192 = 71232` operator-cell grid 本身用作 `FiniteProcess` 状态空间。
- 成功：`lake build SSBX.Foundation.Modern.QuantumRelativityConcreteBridge` 通过。
- 成功：`lake build SSBX.Foundation.Modern.OperatorCellGridMarkovBridge` 通过。
- 成功：接入顶层 import 后，`lake build SSBX` 通过，输出 `Build completed successfully (2888 jobs).`

### 2026-05-08 · S2 有限概率核接口

- 成功：新增 `QuantumRelativityFiniteProbabilityBridge.lean`，定义 `FiniteProbabilityKernelSkeleton`、`RowNormalizable` 与 `FiniteMassCandidate`。
- 成功：为三状态 concrete bridge 和 `371 × 192 = 71232` operator-cell grid bridge 各给出有限概率核接口。
- 成功：关闭 `finite_probability_bridge_summary`；该 theorem 只证明非终端行分母非零与权重上界，不证明 sum-one 概率律、Born rule、真实 quantum channel law 或经验闭合。

### 2026-05-08 · S3 路径组合与局部因果约束

- 成功：确认最新 `origin/main` 与当前 HEAD 同为 `ac63df3`，无需额外 merge。
- 成功：新增 `QuantumRelativityPathCausalBridge.lean`，定义 `ComposableProcessPaths`、`composeProcessPaths`、`CodeSuccessorStep` 与 `CodeMonotoneStep`。
- 成功：关闭 `path_causal_bridge_summary`；该 theorem 证明组合 path witness 给出 reachability / `causalBefore`，并证明 concrete 与 `71232` grid 的 code-successor/no-self-loop。
- 保留边界：仍不证明 `pathWeight` 乘法、完整偏序、局部有限 causal set、light cone、Lorentzian metric 或经验闭合。

### 2026-05-08 · S4 经典 Markov 与量子振幅分层

- 成功：确认当前 worktree 在 `origin/main` 的 `7b2dc4f` 上继续，未发现需要先合并的更新。
- 成功：新增 `QuantumRelativityAmplitudeChannelBridge.lean`，定义 `BridgeLayerKind`、`QuantumAmplitudeSkeleton`、`QuantumChannelSkeleton`。
- 成功：关闭 `amplitude_channel_bridge_summary`；该 theorem 证明 concrete 与 `71232` grid bridge 同时承载 S2 classical boundary、quantum amplitude candidate 与 channel candidate。
- 成功：关闭 `amplitude_layer_is_not_markov_kernel`、`channel_layer_is_not_markov_kernel`、`channel_projection_keeps_markov_boundary` 与 `channel_amplitude_support_implies_step`。
- 保留边界：S4 使用 zero amplitude placeholder，不证明非零物理振幅、干涉、Born rule 从 Markov 桥的推导、unitary evolution、CPTP channel law、量子引力或经验闭合。

### 2026-05-08 · S5 干涉与测量律候选

- 成功：rebase 到最新 `origin/main`，当前基线为 `3c5acf1`。
- 成功：新增 `QuantumRelativityInterferenceBridge.lean`，定义 `PathAmplitudeSkeleton`、`InterferenceCandidate` 与 `BornRuleCandidateBoundary`。
- 成功：关闭 `interference_bridge_summary`；该 theorem 合取 concrete/grid path amplitude candidate、interference candidate、Born-shaped boundary、S4 channel candidate 与 Wen coverage。
- 成功：关闭 `amplitude_path_composition`、`interference_candidate`、`born_rule_candidate_boundary` 与 `born_rule_candidate_nonnegative`。
- 保留边界：S5 使用 zero path-amplitude placeholder；S5b 后续另关非零候选 witness；仍不证明物理相位动力学、真实干涉律、Born rule 从 Markov 桥的推导、unitary/CPTP channel law、decoherence 或经验闭合。

### 2026-05-08 · S5b 非零路径振幅候选

- 成功：新增 `QuantumRelativityNonzeroPathAmplitudeBridge.lean`，定义 `validPathIndicatorPathAmplitudeSkeleton`、concrete composed path witness 与非零候选振幅 theorem。
- 成功：关闭 `nonzero_path_amplitude_bridge_summary`；该 theorem 证明非零 path amplitude 推出 `valid`、`Reachable` 与 `causalBefore`，并给 concrete `prepared -> measured` path 一个非零候选振幅。
- 成功：关闭 `nonzero_path_amplitude_implies_valid`、`nonzero_path_amplitude_implies_reachable`、`nonzero_path_amplitude_implies_causal_before` 与 `concrete_prepared_measured_path_nonzero_amplitude`。
- 保留边界：S5b 的 indicator amplitude 不是相位动力学、路径积分、真实干涉律、Born rule 推导、unitary/CPTP channel law、decoherence 或经验闭合。

### 2026-05-08 · S5c 双路径相消候选

- 成功：新增 `QuantumRelativityTwoPathInterferenceBridge.lean`，定义 `TwoStepPathWitness`、`SameEndpointTwoStepPair`、`twoRouteProcess` 与 `TwoStepPathAmplitudeCandidate`。
- 成功：关闭 `two_path_interference_bridge_summary`；该 theorem 证明 two-route toy process 承载 finite probability / channel / path-amplitude / two-step amplitude candidate，并关闭 upper/lower 两路径有限相消。
- 成功：关闭 `two_route_paths_same_endpoints`、`two_route_paths_distinct_middle`、`two_route_upper_amplitude`、`two_route_lower_amplitude`、`two_route_pair_amplitude_cancels` 与 `two_route_cancelled_born_weight_zero`。
- 保留边界：S5c 只证明 two-path finite cancellation candidate；不证明 path integral、相位动力学、真实干涉律、Born rule 推导、unitary/CPTP channel law、decoherence 或经验闭合。

### 2026-05-08 · S5d 离散相位标记候选

- 成功：新增 `QuantumRelativityDiscretePhaseBridge.lean`，定义 `DiscretePhase`、`discretePhaseAmplitude`、`TwoStepPhaseCandidate` 与 `phaseInducedTwoStepAmplitudeCandidate`。
- 成功：关闭 `discrete_phase_bridge_summary`；该 theorem 证明 upper/lower two-step paths 可分别标记为 `zero/pi`，并由标签导出 `1/-1` 候选振幅和 two-path finite cancellation。
- 成功：关闭 `discrete_phase_amplitudes_cancel`、`two_route_upper_phase`、`two_route_lower_phase`、`two_route_phase_pair_amplitude_cancels` 与 `two_route_phase_cancelled_born_weight_zero`。
- 保留边界：S5d 只证明 discrete phase-label candidate；不证明 continuous phase group、action/Hamiltonian law、path integral、Born rule 推导、unitary/CPTP law、decoherence 或经验闭合。

### 2026-05-08 · S5e 离散作用量相位候选

- 成功：新增 `QuantumRelativityDiscreteActionBridge.lean`，定义 `discretePhaseAdd`、`TwoStepEdgePhaseCandidate`、`edgePhaseInducedTwoStepPhaseCandidate` 与 `edgePhaseInducedTwoStepAmplitudeCandidate`。
- 成功：关闭 `discrete_action_phase_bridge_summary`；该 theorem 证明 upper route 的 edge phase increments 累积为 `zero`，lower route 累积为 `pi`，二者 relative phase 为 `pi`，并继续导出 two-path finite cancellation 与 Born-shaped zero boundary。
- 成功：关闭 `two_route_upper_accumulated_phase`、`two_route_lower_accumulated_phase`、`two_route_edge_action_phase_difference`、`two_route_edge_action_pair_amplitude_cancels` 与 `two_route_edge_action_cancelled_born_weight_zero`。
- 保留边界：S5e 只证明 discrete edge-action phase accumulation candidate；finite path-family sum 已由 S5f 关闭，continuous phase group、action functional、Hamiltonian/unitary law、path integral、Born rule 推导、decoherence 与经验闭合作为后续结构。

### 2026-05-08 · S5f 有限路径族求和候选

- 成功：新增 `QuantumRelativityFinitePathSumBridge.lean`，定义 `FiniteTwoStepPathFamily`、`finitePathFamilyAmplitudeSum` 与 `finitePathFamilyBornWeight`。
- 成功：关闭 `finite_path_sum_bridge_summary`；该 theorem 证明 upper/lower two-route witness 可作为 finite same-endpoint path family，family amplitude sum 等于 S5c/S5e 的 pair sum，并继续相消为 `0`。
- 成功：关闭 `two_route_family_sum_eq_pair_sum`、`two_route_finite_family_amplitude_cancels` 与 `two_route_finite_family_born_weight_zero`。
- 保留边界：S5f 只证明 finite path-family sum candidate；path-sum algebra 已由 S5g 承接，arbitrary all-path enumeration、path integral、Born rule 推导、unitary/CPTP law、decoherence 与经验闭合作为后续结构。

### 2026-05-08 · S5g 有限路径族求和代数候选

- 成功：新增 `QuantumRelativityFinitePathSumAlgebraBridge.lean`，定义 `appendFiniteTwoStepPathFamilies` 与 `reverseFiniteTwoStepPathFamily`。
- 成功：关闭 `finite_path_sum_algebra_bridge_summary`；该 theorem 证明 finite path-family sums 的 append / permutation / reverse stability，并给出 two-route reversed 与 double-canceling family witnesses。
- 成功：关闭 `finite_path_family_amplitude_sum_append`、`finite_path_family_amplitude_sum_perm`、`finite_path_family_amplitude_sum_reverse` 与 `finite_path_family_append_cancels_of_canceling_summands`。
- 保留边界：S5g 只证明 finite list algebra over candidate amplitudes；endpoint-indexed family 已由 S5h 承接，all-path enumeration、filter / duplicate normalization、path integral、Born rule 推导、unitary/CPTP law、decoherence 与经验闭合作为后续结构。

### 2026-05-08 · S5h 端点索引路径族候选

- 成功：新增 `QuantumRelativityEndpointIndexedPathFamilyBridge.lean`，定义 `EndpointPair`、`EndpointTwoStepPath` 与 `EndpointIndexedTwoStepPathFamily`。
- 成功：关闭 `endpoint_indexed_path_family_bridge_summary`；该 theorem 证明 S5f finite family 可转换为 endpoint-indexed family，且候选振幅和与 Born-shaped weight 保持不变。
- 成功：关闭 `endpoint_indexed_family_sum_of_finite_family`、`endpoint_indexed_family_born_weight_of_finite_family`、`two_route_endpoint_indexed_family_amplitude_cancels` 与 `two_route_endpoint_indexed_family_born_weight_zero`。
- 保留边界：S5h 只证明 endpoint-indexed finite family conversion；filter / support normalization 已由 S5i 承接，all-path enumeration、path integral、Born rule 推导、unitary/CPTP law、decoherence 与经验闭合作为后续结构。

### 2026-05-08 · S5i 端点支撑规范化候选

- 成功：新增 `QuantumRelativityEndpointSupportNormalizationBridge.lean`，定义 `filterEndpointIndexedTwoStepPathFamily`、`EndpointFamilyFilterComplete` 与 `duplicateEndpointIndexedTwoStepPathFamily`。
- 成功：关闭 `endpoint_support_normalization_bridge_summary`；该 theorem 证明 amplitude-complete finite filter 保持候选振幅和与 Born-shaped weight，duplicate expansion 显式给出 `sum + sum`，且 duplicated zero-sum family 仍相消。
- 成功：关闭 `endpoint_indexed_family_filter_sum_eq_of_removed_zero`、`endpoint_indexed_family_filter_born_weight_eq_of_removed_zero`、`endpoint_indexed_family_duplicate_sum`、`two_route_filtered_endpoint_family_amplitude_cancels` 与 `two_route_duplicated_endpoint_family_amplitude_cancels`。
- 保留边界：S5i 只证明给定 endpoint-indexed finite family 上的 filter / duplicate boundary；two-route toy enumeration 已由 S5j 承接，quotient 去重、general all-path enumeration、path integral、Born rule 推导、unitary/CPTP law、decoherence 与经验闭合作为后续结构。

### 2026-05-08 · S5j 双路径枚举候选

- 成功：新增 `QuantumRelativityTwoRouteEnumerationBridge.lean`，定义 `endpointIndexedMiddleList` 与 `twoRouteSourceTargetMiddleEnumeration`。
- 成功：关闭 `two_route_enumeration_bridge_summary`；该 theorem 证明 S5h endpoint-indexed two-route family 的 middle list 为 `[upper, lower]`，且任意 `source -> _ -> target` two-step witness 的 middle 只能是 `upper` 或 `lower`。
- 成功：关闭 `two_route_source_target_middle_mem_endpoint_family` 与 `two_route_source_target_middle_complete`，把 toy source/target middle exhaustion 接回 endpoint-indexed family。
- 保留边界：S5j 只证明 two-route toy process 的 two-step middle enumeration；visible path-key boundary 已由 S5k 承接，proof-field path equality、quotient 去重、general all-path enumeration、path integral、Born rule 推导、unitary/CPTP law、decoherence 与经验闭合作为后续结构。

### 2026-05-08 · S5k 路径身份键候选

- 成功：新增 `QuantumRelativityPathIdentityBridge.lean`，定义 `TwoStepPathKey` 与 `twoStepPathKey`，把 `TwoStepPathWitness` 的 proof fields 与可见路径身份分开。
- 成功：关闭 `path_identity_bridge_summary`；该 theorem 证明 key equality 保持 `start/middle/stop`，two-route upper/lower keys 不同，toy source/target path key 落在 displayed key enumeration 中。
- 成功：新增《路径身份键候选 · Markov桥S5k》，并更新总文档、验证计划、逐步路线与 docs-next 索引。
- 保留边界：S5k 只证明 visible path-key boundary；finite visible-key quotient candidate 已由 S5l 承接，visible-key quotient class 已由 S5m 承接，two-route canonical representative 已由 S5n 承接；proof-field path equality、general choice function、general all-path enumeration、path integral、Born rule 推导、unitary/CPTP law、decoherence 与经验闭合作为后续结构。

### 2026-05-08 · S5l 有限键商候选

- 成功：新增 `QuantumRelativityFiniteKeyQuotientBridge.lean`，定义 `TwoStepPathKeyEquivalent`、`TwoStepKeyAmplitudeCandidate`、`PathAmplitudeFactorsThroughKey` 与 finite key-list sum。
- 成功：关闭 `finite_key_quotient_bridge_summary`；该 theorem 证明 visible-key equality 是 quotient-candidate equivalence relation，key-compatible amplitudes 在同 key paths 上相同，duplicate key list 显式给出 `sum + sum`，two-route key-level sum 与 Born-shaped weight 为 `0`。
- 成功：新增《有限键商候选 · Markov桥S5l》，并更新总文档、验证计划、逐步路线与 docs-next 索引。
- 保留边界：S5l 不构造 quotient class；该结构已由 S5m 承接。S5l 仍不证明 proof-field path equality、general all-path enumeration、path integral、Born rule 推导、unitary/CPTP law、decoherence 或经验闭合。

### 2026-05-08 · S5m 路径商类候选

- 成功：新增 `QuantumRelativityPathQuotientBridge.lean`，定义 `twoStepPathKeySetoid`、`TwoStepPathKeyQuotient`、`twoStepPathQuotientClass`、`quotientVisibleKey` 与 `quotientKeyAmplitude`。
- 成功：关闭 `path_quotient_bridge_summary`；该 theorem 证明 same-key paths 进入同 quotient class，visible key 与 key-level amplitude 可下降到 quotient class，two-route upper/lower quotient classes 不同，toy source/target quotient enumeration complete。
- 成功：新增《路径商类候选 · Markov桥S5m》，并更新总文档、验证计划、逐步路线与 docs-next 索引。
- 保留边界：S5m 不证明 proof-field path equality；two-route canonical representative 已由 S5n 承接，general choice function、general all-path enumeration、path integral、Born rule 推导、unitary/CPTP law、decoherence 或经验闭合作为后续结构。

### 2026-05-08 · S5n 规范代表元候选

- 成功：新增 `QuantumRelativityCanonicalRepresentativeBridge.lean`，定义 `CanonicalRepresentativeFor` 与 two-route displayed representatives。
- 成功：关闭 `canonical_representative_bridge_summary`；该 theorem 证明 upper/lower displayed paths 代表自身 quotient class，任意 toy source/target two-step path 的 quotient class 由 upper/lower displayed path 代表。
- 成功：新增《规范代表元候选 · Markov桥S5n》，并更新总文档、验证计划、逐步路线与 docs-next 索引。
- 保留边界：S5n 不构造 general choice function；finite quotient-support enumeration 已由 S5o 承接；不证明 proof-field path equality、general all-path enumeration、path integral、Born rule 推导、unitary/CPTP law、decoherence 或经验闭合。

### 2026-05-08 · S5o 商支撑枚举候选

- 成功：新增 `QuantumRelativityQuotientSupportBridge.lean`，定义 `quotientSupportAmplitudeSum`、`quotientSupportBornWeight` 与 `quotientSupportVisibleKeys`。
- 成功：关闭 `quotient_support_bridge_summary`；该 theorem 证明 displayed representatives 的 quotient classes 正是 two-route source/target quotient support，任意 toy source/target quotient class 在该 support 中，并且 quotient support 可回读到 visible-key list。
- 成功：证明 quotient-support 层保持 two-route key-level cancellation 与 Born-shaped zero boundary。
- 失败记录：第一次 `lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge` 失败在 `quotient_support_sum_eq_visible_key_sum` 使用 `rfl`；原因是 `quotientKeyAmplitude` 与 function composition 不是定义等式；修正为展开 `quotientKeyAmplitude` 与 `Function.comp_def` 后通过。
- 成功：新增《商支撑枚举候选 · Markov桥S5o》，并更新总文档、验证计划、逐步路线与 docs-next 索引。
- 保留边界：S5o 不证明 general all-path enumeration、general choice function、quotient-level path integral、continuous action law、Born rule 推导、unitary/CPTP law、decoherence 或经验闭合；quotient-support algebra 已由 S5p 承接。

### 2026-05-08 · S5p 商支撑代数候选

- 成功：新增 `QuantumRelativityQuotientSupportAlgebraBridge.lean`，定义 `appendQuotientSupports`、`reverseQuotientSupport` 与 `duplicateQuotientSupport`。
- 成功：关闭 `quotient_support_algebra_bridge_summary`；该 theorem 证明 quotient-support sums 的 append / permutation / reverse stability，以及 duplicate zero-sum cancellation。
- 成功：证明 two-route quotient support 反序后仍相消，support append reversed support 后仍相消，并保持 Born-shaped zero boundary。
- 失败记录：第一次 `lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge` 失败在显式 `twoRouteProcess` 类型标注；原因是 Lean 解析到不同 namespace 下的同名 process；移除显式返回类型后通过。
- 成功：新增《商支撑代数候选 · Markov桥S5p》，并更新总文档、验证计划、逐步路线与 docs-next 索引。
- 保留边界：S5p 不证明 general all-path enumeration、path integral、continuous action law、Born rule 推导、unitary/CPTP law、decoherence 或经验闭合。

### 2026-05-09 · S5q 观测账本候选

- 成功：新增 `QuantumRelativityObservableLedgerBridge.lean`，定义 `EmpiricalClosureStatus`、`ObservableLedgerEntry`、`ObservableLedgerPending` 与 `EmpiricallyClosed`。
- 成功：关闭 `pending_not_empirically_closed`；该 theorem 明确 pending entry 与 externally closed status 不相容。
- 成功：新增 `twoRouteCancellationObservableLedgerEntry`，把 two-route quotient-support cancellation 登记为 pending observable ledger entry。
- 成功：关闭 `observable_ledger_bridge_summary`；该 theorem 合取 zero displayed amplitude sum、zero Born-shaped candidate weight、pending boundary、S5p double-support cancellation 与 Wen coverage。
- 成功：`lake build SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge` 通过；输出中只有既有 Wen 模块 unused simp argument 警告。
- 保留边界：S5q 不证明实验闭合、数据校准、可测预言 theorem、Born rule 推导、path integral、continuous action law、unitary/CPTP law 或 decoherence。

### 2026-05-09 · S5r 作用量相位律候选

- 成功：新增 `QuantumRelativityActionPhaseLawBridge.lean`，定义 `actionIndexPhase`、`actionIndexAmplitude` 与 `QuotientActionPhaseLawCandidate`。
- 成功：关闭 `action_index_zero_one_amplitudes_cancel`；finite action index `0/1` 分别导出 `1/-1` 并相消。
- 成功：关闭 `two_route_action_phase_support_amplitude_cancels` 与 `two_route_action_phase_support_born_weight_zero`；two-route quotient support 在 finite action-to-phase law 下相消并保持 Born-shaped zero boundary。
- 成功：新增 `twoRouteActionPhaseObservableLedgerEntry`，把 action-phase law 的 cancellation 登记为 pending observable ledger entry。
- 失败记录：第一次 `lake build SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge` 失败在 quotient readback 化简；原因是 proof 展开 `quotientVisibleKey` 后暴露 `Quot.lift`，修正为保留 quotient readback 形状，让 `quotient_visible_key_mk` 关闭计算。
- 成功：关闭 `action_phase_law_bridge_summary`；该 theorem 合取 finite action-to-phase law boundary、ledger boundary 与 Wen coverage。
- 保留边界：S5r 不证明 continuous action functional、Hamiltonian/unitary dynamics、path integral、Born rule 推导、数据校准或经验闭合。

### 2026-05-09 · S8 逐步统一候选摘要

- 成功：新增 `QuantumRelativityStepwiseUnificationBridge.lean`，定义 `PendingBeyondS5r` 与 `ClosedByStepwiseS5r`。
- 成功：关闭 `pending_boundary_not_closed_by_s5r`，把 sum-one probability、Born-rule derivation、continuous action law、path integral、measurable prediction data、unitary/CPTP channel law、metric recovery 与 empirical closure 显式标为本层未关闭。
- 成功：关闭 `stepwise_unification_candidate_summary`；该 theorem 合取 concrete Markov/causal bridge、finite probability projection、`71232` operator-cell grid、S5r action-phase cancellation、S5q ledger boundary、tagged noncollapse 与 Wen coverage。
- 失败记录：第一次 `lake build SSBX.Foundation.Modern.QuantumRelativityStepwiseUnificationBridge` 失败在 `allOperatorCells` 与 quotient support namespace/defeq 解析；修正为显式 import `OperatorCellGridMarkovBridge`、`QuantumRelativityPathQuotientBridge`，并加入 local aliases。
- 保留边界：S8 是 current stepwise candidate summary；不证明终局物理统一、连续动力学、一般路径积分、真实量子通道、度规恢复或实验闭合。

### 2026-05-09 · S9 有限概率归一化候选

- 成功：新增 `QuantumRelativityFiniteProbabilityNormalizationBridge.lean`，定义 `rowWeightSum`、`normalizedMass`、`normalizedRowTotalCandidate` 与 `FiniteRowSupportNormalization`。
- 成功：关闭 `finite_probability_normalization_bridge_summary`；concrete 与 `71232` grid kernel 都有 sound/complete row support，且非终端行 normalized-row-total candidate 为 `1`。
- 成功：新增 `PendingBeyondS9`；finite sum-one row boundary 不再列入 pending，Born-rule derivation、continuous action、path integral、unitary/CPTP、metric recovery 与 empirical closure 仍列入 pending。
- 失败记录：第一次 S9 build 失败在 concrete row list-sum、grid singleton `Fin` 化简与 grid theorem 的 Rat coercion；修正为 concrete `native_decide`、grid terminal/non-terminal 直接分支和先证 rowTotal = `1`。
- 保留边界：S9 只证明 finite Markov row normalization，不证明 Born rule 推导、真实测量律、unitary/CPTP law、度规恢复或经验闭合。

### 2026-05-09 · S10 归一化质量求和候选

- 成功：在 S9 模块补出 `rowWeightSum_eq_rowTotal`，作为 row support 权重和等于 rowTotal 的命名 theorem。
- 成功：新增 `QuantumRelativityNormalizedMassBridge.lean`，定义 `normalizedMassSum`，并证明 `normalizedMassSum_eq_normalizedRowTotalCandidate`。
- 成功：关闭泛型 theorem `normalizedMass_sum_one`；任一 normalizable row 若有 `FiniteRowSupportNormalization`，则显式支撑上的逐项 normalized mass 求和为 `1`。
- 成功：关闭 `normalized_mass_bridge_summary`；concrete 与 `71232` grid kernel 的非终端行都形成 rational finite probability law。
- 失败记录：先试探 direct concrete/grid 展开 proof，能过但只给孤立计算；改为泛型 algebra bridge 后更适合后续 Born/channel 接口。
- 保留边界：S10 只证明 classical finite normalized mass law，不证明 Born rule 推导、amplitude normalized support、unitary/CPTP law、路径积分、度规恢复或经验闭合。

### 2026-05-09 · S11 Born 权重条件归一候选

- 成功：新增 `QuantumRelativityBornWeightNormalizationBridge.lean`，定义 `amplitudeSupportWeightSum`、`AmplitudeSupportNormalized`、`bornCandidateBoundarySupport` 与 `bornCandidateWeightSum`。
- 成功：关闭 `bornCandidateWeightSum_eq_amplitudeSupportWeightSum`；`BornRuleCandidateBoundary.candidateWeight` 的有限和等于同一 support 上的 `ampProb` 有限和。
- 成功：关闭 `born_weight_nonnegative_and_sum_one_if_normalized`；若有限 amplitude support 已由 `ampProb` 归一，则所有 candidate weights 非负且求和为 `1`。
- 成功：关闭 `born_weight_normalization_bridge_summary`，并给出 `unitAmplitudeSupport = [1]` 的最小 normalized support witness。
- 失败记录：第一次 proof 试探中，`simp` 不能直接穿过 `(candidateWeight ∘ bornRuleCandidate)` 的 list sum；改用 list induction 和 `rw [born_rule_candidate_boundary, ih]` 后闭合。
- 保留边界：S11 是条件式 finite Born-shaped probability law；不证明 Born rule 推导、无条件 amplitude support normalized、真实测量律、unitary/CPTP law、路径积分、度规恢复或经验闭合。

### 2026-05-09 · S12 Born 分布边界候选

- 成功：新增 `QuantumRelativityBornDistributionBridge.lean`，定义 `FiniteProbabilityDistributionInterface` 与 `BornDistributionBoundary`。
- 成功：关闭 `born_distribution_boundary`；任一 normalized finite amplitude support 可给出包含 amplitude sum、candidate support、candidateWeight projection 与 sum-one distribution 的 boundary object。
- 成功：关闭 `born_distribution_bridge_summary`，合取 S9/S10/S11 与 S12 的概率侧边界。
- 失败记录：第一次 theorem 试探中，`simp [bornDistributionBoundary]` 未自动拆出 distribution fields；修正为显式 existential witness、逐项 `rfl` 与 `weight_sum_one`。
- 保留边界：S12 只是 finite distribution packaging；不证明 Born rule 推导、channel composition、真实测量律、unitary/CPTP law、路径积分、度规恢复或经验闭合。
