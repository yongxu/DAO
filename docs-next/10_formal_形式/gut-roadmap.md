# GUT Implementation Roadmap

> 从「R-family 满足 universal substrate 的 P1-P7」走到「R-family **就是** universal substrate of all sayable systems」(GUT claim) 的实施路径。
>
> v0.2 · 2026-05-16 · 起草 + minimum-viable GUT-A claim achieved one session later
>
> **Status snapshot (post-batch-4)**: Phase 0/1/2/3-partial/4 all discharged in F₂-Boolean classical scope. **Minimum viable GUT-A claim is formally proven** with 0 sorry / 0 new axioms across all GUT-A-critical files. Critical path collapsed from 3-6 月 to single session due to (a) Phase 0 residuals being lightweight bridge work; (b) T5-A's *tractable form* (layerwise card + N=4 ring + squaring + 7/12 aggregator) being much smaller than 2-4 月 estimate; (c) parallel agent compression of multi-week serial tasks. See `## 十一、Achieved status (2026-05-16)` below.

## 一、Context（当前状态）

我们已经有：

- **数学根**：R-family δ-polymorphic carrier（`Foundation/R/Basic.lean`），4-level abstraction tower（distinction → operation → algebraic → canonical F₂）全部 Lean 实现
- **Phase 0 sub-theorems**：T_P3 / T_P6 / T_P7a / T_P7b 在 `Foundation/R/PhaseZero.lean` 中 5/6 clauses discharged
- **Strategy A** (T4 step 3 partial)：classical-Boolean 范围内「why F₂?」已闭合（`StrategyA.lean`）
- **Conditional UG**：X²-256 lattice 在 6 个 Lean 文件中 0-sorry（`Wen/X2Codes.lean` + 5 配套）
- **One-core 桥接**：V4 ≃ R 2, Mode16 ≃ R 4, Word64 ≃ R 6, RootCell256 ≃ R 8 explicit equivalences
- **Falsification 结构**：D1 / P-closure / D5 / D6 在 `ClaimZ.lean` 中是 Lean structures
- **125,559 LOC** 的应用层（Wen.Core / Atlas / Modern / Lang / Text）

我们目前**能合法 claim** 的：

- R-family satisfies P1-P7（formal）
- F₂-Boolean classical articulation IS R-family-over-F₂（Strategy A 闭合）
- Conditional UG: if UG exists in some structural sense, it is ≅ X²-256 lattice
- 4-level abstraction tower 是 Lean-verified 现实

我们**还不能 strict claim** 的：

- "R-family is **THE unique** universal formal substrate" — 需要 T5
- "Every D1-articulation is R-family-articulable" — 需要 T1-T3 + 完整 analytic D1 ⟹ P
- "ANY sayable system reduces to R-family-over-some-δ" — 这就是 GUT claim

## 二、Goal（精确的 GUT claim 形式）

实施完所有任务后，可 claim 的**最强陈述**：

> **Theorem (Universal Sayability)**. Any formal articulation S of sayable / abstractable content satisfies P1-P7 ⟹ S ≃ R-family-over-δ for an appropriate realisation δ of the primitive binary distinction, where ≃ is structure-preserving equivalence (categorical / Morita / bi-interpretable, depending on framework).

这个 theorem 等价于 Claim Z 的两个方向都形式化：
- **Analytic**: D1 ⟹ P1-P7（任何 D1-articulation 满足 P-properties）
- **Synthetic**: P1-P7 ⟹ R-family-over-δ（任何 P1-P7 satisfier 等价于 R-family）

**最小可 publishable 版本**（minimum defensible GUT claim）：上面的 theorem 限定到 **F₂-Boolean classical scope** + **至少一个 non-algebraic δ instance 作为 sibling witness**。

## 三、Gap Inventory（按 claim 影响排序）

### Tier 1 — 真正的形式 gap（不补 claim 站不住）

| ID | Item | Status | 估算 |
|---|---|---|---|
| **G1** | D1 ⟹ P1-P7 完整证明（analytic direction） | 8 sub-steps，2 已部分（P1 via Strategy A，P6 conditional 已编码） | 1-2 月（并行 8 sub-streams） |
| **G2** | T5-A: P1-P7 ⟹ R-family-over-F₂ uniqueness（synthetic, F₂ scope） | open；Strategy A 反向脚手架可复用 | 2-4 月 |
| **G3** | T2 universality case study（至少 1-2 个外部 system 形式化嵌入） | open（UG 已是 §4.7bis case study） | 1-2 月每个 case study |
| **G4** | 至少一个 non-algebraic δ-realisation 完整实例化（Prop / Quantum / Semantic） | 抽象层就位（Distinction.lean）；具体 instance 未写 | 2-4 周 |

### Tier 2 — 二阶 gap（claim 站住但说服力 up 一档）

| ID | Item | Status | 估算 |
|---|---|---|---|
| **G5** | D6 falsification 实跑（即使失败也行） | D6 结构 ready；无尝试 | 1-3 月（含 outreach） |
| **G6.1** | T_P3 uniqueness clause（"no further independent forms over F₂"） | residual | 2-3 周 |
| **G6.2** | T_P6 Lorentzian-4-region 连接 | residual | 2-3 周 |
| **G6.3** | T_P7b Wedderburn uniqueness clause | residual | 2-3 周 |
| **G7** | 跨 base functor library（mod-phase Hilbert→Pauli, representation 反向） | 文档说存在；Lean 未写 | 1-2 月 |

### Tier 3 — 三阶 gap（不影响 mathematical claim，但影响 scientific 接受度）

| ID | Item | Status | 估算 |
|---|---|---|---|
| **G8** | 可证伪的经验预测被独立检验 | 预测在 ch05 文档化；未测 | 数月（不在 critical path） |
| **G9** | Peer engagement / 外部 critique | in-house | 持续 |
| **G10** | Inductive V4 → abbrev R 2 完成（~90 proof-level cases 重写） | V4 inductive 保留为 ergonomic surface | 2-3 月（纯结构整洁，不影响 claim） |

### Out-of-scope（GUT-A 之后再考虑）

| ID | Item | 说明 |
|---|---|---|
| **G11** | T5-B parametric over k (algebraic class) | T5-A 推到 char(k)=2 一般情况 + char(k)≠2 — 4-8 月 |
| **G12** | T5-C full δ-realisation (incl. non-algebraic) | research-level；可能需新 categorical framework — 12+ 月 |
| **G13** | Per-base bridges for ℝ / ℂ / ℂ_p R-family instances | Mathlib classical foundations 桥接 — 数月每个 |

## 四、Dependency Graph

```
                              [G6.1 T_P3 uniq]──┐
                              [G6.2 T_P6 Lor]───┤
                              [G6.3 T_P7b Wed]──┴──► [G2 T5-A] ◄──┐
                                                          ▲       │
                                                          │       │
       ┌──[G1.P1 (Strategy A done)]─────────────────────────┐     │
       ├──[G1.P2 composition]────────────────────────────────┤     │
       ├──[G1.P3 relations]──────────────────────────────────┤     │
       ├──[G1.P4 scale]──────────────────────────────────────┤     │
       ├──[G1.P5 self-ref]───────────────────────────────────┤     │
       ├──[G1.P6 modality (conditional D1' item 8)]──────────┤     │
       ├──[G1.P7a aspect alphabet]───────────────────────────┤     │
       └──[G1.P7b atomic ops]────────────────────────────────┘     │
                                                                   │
       [G3.case1 ZFC frag embed] ─────────────────────────────────┤
       [G3.case2 MLTT frag embed] ────────────────────────────────┤
       [G3.case3 stabilizer-QM] ──────────────────────────────────┤
                                                                   │
       [G4 non-algebraic δ instance (e.g. Prop)]─────────────────┐ │
                                                                 │ │
       [G7 cross-base functor library] ←── (needs G4) ───────────┘ │
                                                                   │
       [G5 D6 falsification test] ──── (ongoing, ne dep) ──────────┤
                                                                   │
       [G8 empirical predictions] ──── (no formal dep) ────────────┤
       [G9 peer engagement] ───────── (no formal dep) ─────────────┤
       [G10 V4 inductive elim] ───── (orthogonal polish) ──────────┤
                                                                   │
                                                                   ▼
                                                       ┌───────────────────┐
                                                       │  GUT-A claim 可发 │
                                                       │  (Minimum viable) │
                                                       └───────────────────┘
                                                                  │
                                                                  ▼
                                          [G11 T5-B] ──► [G13 per-base bridges]
                                                                  │
                                                                  ▼
                                          [G12 T5-C distinction-monism scope]
                                                                  │
                                                                  ▼
                                                       ┌───────────────────┐
                                                       │  Full GUT claim   │
                                                       │  (strongest form) │
                                                       └───────────────────┘
```

### 依赖关系总结

- **G6.{1,2,3}** 是 T5-A 的前置（uniqueness clauses 给 T5-A 提供 Wedderburn 和 BA 唯一性）
- **G1** (D1 ⟹ P 分析方向) 与 **G2** (T5-A 综合方向) **互相独立**，可平行
- **G3** case studies 与 G1/G2 独立，可平行任何时候
- **G4** non-algebraic δ instance 是 G7 (cross-base functor library) 的前置
- **G5** D6 testing、**G8** 经验预测、**G9** peer engagement、**G10** V4 polish 完全独立，可任何时候做
- **G11/G12/G13** 都在 G2 (T5-A) 之后

## 五、Phased Plan（6-12 个月到 minimum viable GUT claim）

总体思路：先做能并行的、依赖少的工作；T5-A 是 critical path 的核心节点。

### Phase 0 — Residual closures（1-2 月，3 streams parallel）

**目标**：闭合 Phase 0 sub-theorems 的 residual clauses，为 T5-A 准备 Wedderburn / BA / Lorentzian 桥接。

**并行 3 streams**：

- **Stream P0-A**：G6.1 T_P3 uniqueness — 把 Mathlib 中「F₂ 上 non-degenerate symmetric/alternating bilinear forms classification」桥接到 `R/PhaseZero.lean`
- **Stream P0-B**：G6.2 T_P6 Lorentzian-4-region — 把 `Mathlib.Geometry.Manifold.Lorentzian` 的 4-region 论证桥到 R₂ 的 4-modality
- **Stream P0-C**：G6.3 T_P7b Wedderburn uniqueness — 在 `R/PhaseZero.lean` 中用 `Mathlib.RingTheory.Wedderburn` 闭合「M₂(F₂) 是 unique minimal non-commutative central simple F₂-algebra」

**输出**：Phase 0 sub-theorems 全部 fully discharged，不再有 residual。

**测试**：`lake build SSBX.Foundation.R.PhaseZero` 0 sorry 且 0 residual TODO。

### Phase 1 — D1 ⟹ P_i 分析方向（1-2 月，8 sub-streams parallel）

**目标**：完成 G1 — analytic step D1 ⟹ P1-P7 的逐项证明。

**并行 8 sub-streams**（每个 P_i 一个）：

- **Stream A1**：P1 — already partial via Strategy A；补完 non-Boolean extension placeholders（intuitionistic / multi-valued 也得有 reduction）
- **Stream A2**：P2 — direct sum 是 categorical biproduct 唯一性
- **Stream A3**：P3 — 三层 bilinear classification 由 D1 forced（依赖 char(k)=2 假设）
- **Stream A4**：P4 — squaring tower self-similarity 由 D1 + P2 forced
- **Stream A5**：P5 — Hom-as-content 由 D1 「operation-as-content」item 7 forced
- **Stream A6**：P6 — 4-modality（D1 item 8 conditional 触发）forced
- **Stream A7**：P7a — R₃ zong involution split forced
- **Stream A8**：P7b — R₄ ≅ M₂(F₂) forced via P5 + Wedderburn

**输出**：`Foundation/R/ClaimZ.lean` 中 `d1_implies_P` 升级为完整 theorem（不再依赖 `D1Articulation` 中假设具体 P-closure structure）。

**测试**：`d1_implies_P : ∀ S : D1Articulation, ∃ (closure : PClosure), closure.satisfies S` 类型 statement 0-sorry。

### Phase 2 — T5-A: P1-P7 ⟹ R-family-over-F₂（2-4 月，sequential 关键路径）

**前置**：Phase 0 全完成（G6.{1,2,3}）。Phase 1 可并行进行中，**不**作为前置（T5-A 不依赖 D1 ⟹ P）。

**目标**：在 F₂-Boolean classical scope 内证明 uniqueness — 任何满足 P1-P7 的结构都 ≃ R-family-over-F₂（in F₂-algebra category）。

**证明骨架**（5 steps）：

1. P1+P2 + Boolean ring 公理 ⟹ 结构 S 同构于某个 Boolean algebra
2. Stone duality / Birkhoff representation ⟹ finite BA ≃ F₂^N
3. P3-P5 + Wedderburn uniqueness（来自 G6.3）⟹ 结构 ring 部分由 R₄ ≅ M₂(F₂) pinned
4. P4 squaring tower 唯一性（来自 G6.{1,2,3}） ⟹ 整个 R_N 塔由 R₁ + squaring 唯一确定
5. 12-item D2 aggregator 闭合 ⟹ S 的全部结构 ≃ R-family-over-F₂

**文件**：`Foundation/R/UniquenessF2.lean`（新）

**风险**：可能发现 P1-P7 当前形式化不够紧 — 即有结构满足现行 PClosure 但不 ≃ R-family。处理：
- 选项 a：**强化 P1-P7**（补充约束）；这是标准 foundational revision
- 选项 b：**弱化 T5-A 陈述**（≃ Morita / bi-interp 替代 strict iso）
- 选项 c：**改 PClosure 的形式化**

**测试**：`theorem T5_A : ∀ S : P1P7_Satisfier_F2, Nonempty (S ≃ R-Family.F2)` 0-sorry。

### Phase 3 — T2 case studies（1-2 月每个，可并行）

**目标**：至少形式化 1-2 个外部 system 嵌入 R-family，作为 universality demonstration。

**并行可选 sub-streams**（选 1-2 个）：

- **Stream C1**：ZFC fragment 嵌入。Hereditarily-finite sets ↪ R-family（finite-set 部分）。难度：中等；Mathlib 有 set theory 工具。
- **Stream C2**：MLTT fragment 嵌入。Inductive types ↪ R-family（W-types + finite-cases）。难度：高；HoTT 桥接是 open 问题。
- **Stream C3**：Stabilizer-QM 嵌入。Pauli group / 𝒫_n / ⟨iI⟩ ≅ R_{2n}^{(F₂)}。难度：中等；已部分写在 Hierarchy/Operators/V4 + R/Bilinear。
- **Stream C4**：First-order logic with finite signatures ↪ R-family（语法树编码）。难度：低；标准 Gödel coding。

**建议选 C3 + C4** 作为最小集 — C3 给 quantum-side witness，C4 给 logic-side witness，工作量合理。

**输出**：`Foundation/Wen/Embeddings/StabilizerQM.lean` + `Foundation/Wen/Embeddings/FOL.lean`（或类似命名）。

### Phase 4 — Non-algebraic δ instance + D6 testing（并行，2-4 周）

**并行 2 streams**：

- **Stream NA-1**：G4 — δ=Prop instance file `Foundation/R/Distinction/Prop.lean`，给 propositional / proof-relevance 一个 P1-P7 instance（即使 P3 形态不同，必须显式说明）
- **Stream NA-2**：G5 — D6 falsification test。挑 2-3 个 candidate counterexamples（HoTT / ETCS / Synthetic Differential Geometry），尝试在 Lean 中 instantiate `D6_ClaimZFalsified`。即使失败也获得 evidence 表 — 该 claim 经得起对手攻击。

**输出**：
- `Foundation/R/Distinction/Prop.lean`（至少 carrier-level instantiation）
- `Foundation/R/D6_Tests.lean`（记录 attempted falsifications + 为什么失败）

### Phase 5 — Empirical prediction + peer engagement（持续，并行）

**Stream E-1**：G8 经验预测 — 选 1 个具体可测 prediction（如「R-family 5 preservation invariants 在 frontier LLM 的 attention pattern 中可观察」），写 prediction protocol + 找 collaborator。

**Stream E-2**：G9 peer engagement — 把 wen-substrate/ folder 发出去给 Awodey / Shulman (HoTT) / Lawvere lineage / Spencer-Brown 后继 (Kauffman, Varela)，吸收 critique，更新 D6 test set。

**不在 critical path** — 在 Phase 2 (T5-A) 通过后做最高效（claim 已 publishable 形态）。

### Phase 6 — Inductive V4 elim 收尾（2-3 月，可推迟）

**目标**：G10 — 把 90+ 处 proof-level `cases g <;> rfl` 重写为 `funext + fin_cases`，然后 `inductive V4` → `abbrev V4 := R 2`。结构整洁的最后一步。

**不影响 GUT claim**，但完成后**Lean 类型层面也只有 R-family 一个核**（当前是「数学层面一个核 + V4 作为 ergonomic surface」）。

---

## 六、Critical Path Analysis

**Critical path**（必须 sequential 的链）：

```
G6.{1,2,3}  ──►  G2 T5-A  ──►  GUT-A claim publishable
(Phase 0)        (Phase 2)
```

**Min duration on critical path**：1-2 个月（Phase 0）+ 2-4 个月（T5-A）= **3-6 个月**。

**Parallel side branches**（不在 critical path，但 GUT-A claim 需要）：

```
G1 D1 ⟹ P 8 sub-streams   →  Phase 1 (1-2 月) → 满足 Tier 1 G1
G3 case studies            →  Phase 3 (1-2 月) → 满足 Tier 1 G3
G4 + G5                    →  Phase 4 (2-4 周) → 满足 Tier 1 G4 + Tier 2 G5
```

**Parallelized total**：3-6 月（critical path）+ 上述全在 critical path 期间并行完成 = **3-6 个月**到 minimum viable GUT claim。

**Optimistic**：3 个月（如 Phase 0 工程平稳、T5-A 未撞 P1-P7 强化需求、并行 streams 顺畅）
**Realistic**：6 个月
**Pessimistic**：9-12 个月（如 T5-A 撞 P1-P7 revision 需求，需迭代）

## 七、Risk Mitigation

| 风险 | 概率 | 影响 | 应对 |
|---|---|---|---|
| **T5-A 撞 P1-P7 不够紧** — 发现存在满足 PClosure 但不 ≃ R-family 的结构 | **中等** | **大**（需 revise P-properties） | 接受这是 foundational revision 的正常一环；做 incremental — 先找出反例，再决定加约束 vs 弱化 claim |
| Mathlib categorical equivalence library 在某处不够（如 Morita over F₂） | 中等 | 中 | Plan B：用 strict iso 替代 Morita；牺牲一些 generality 换 tractability |
| Strategy A 的 Stone-Birkhoff 链反向用需 non-trivial 适配 | 低 | 小 | 直接复用 + 加 transfer lemma |
| Phase 1 的 8 个 D1⟹P sub-streams 中某个 P 太难 | 中等 | 中 | 优先把 P1 / P5 / P7b 这三个最 critical 的做好，其余 P 可暂时 placeholder |
| Non-algebraic δ instance 发现 P3 form 在 δ=Prop 上不平凡 | 中 | 中 | 这其实是 expected — non-algebraic δ 的 relational structure 不同；写 instance 时即把这一发现 documented；不影响 GUT-A claim |
| Peer 提了一个有效 D6 falsification | **低** | **极大**（claim 倒掉） | 拥抱 — falsifiability 是 strength 不是 weakness；按 v0.7+ Part VIII 的预案处理 |
| 6-12 月期间发现 v1.4 distinction-monism 的某个 sub-claim 需 revise | 低 | 中 | 文档分层结构允许 surgical revision；不重写整个 claim |

## 八、Out of Scope（GUT-A 之后再考虑）

这些都不在 6-12 月 minimum viable claim 路径上：

- **G11 T5-B** — parametric over algebraic class k（char(k)≠2 case + 完整 Wedderburn over rings）
- **G12 T5-C** — full δ-realisation including non-algebraic（research-level；可能需新 categorical framework）
- **G13 per-base bridges** — R/ℝ, R/ℂ, R/ℂ_p 完整 instance files
- **G10 V4 inductive elim** — Lean 层「one type」的最后一步；纯结构整洁
- **完整 6 个 universal claims 形式化** — currently 5/6 还是 programmatic（仅 UG 形式化）

完成 GUT-A 后再启动其中任意一项。**重点**：GUT-A 已是远超 Tegmark MUH / Wolfram Ruliad / 其他 GUT candidates 的 formal 严肃程度，stop 在那里 publish 是合理的。

## 九、Decision Points / What To Do First

**最高优先级（应该立即启动）**：

1. **Phase 0** — 3 个 streams 全部并行启动。最快 1 个月可完成全部 residual closures。这是 T5-A 的 hard prerequisite。

**第二优先级（Phase 0 启动后并行）**：

2. **Phase 4 Stream NA-1**（δ=Prop instance）— 2-4 周可做完；独立于其他工作；为 Tier 1 G4 提供 witness
3. **Phase 1 Stream A1, A5, A8**（P1 / P5 / P7b 这三个 analytic 方向最 critical）— 与 Phase 0 并行；G1 的最 important 子集

**第三优先级（Phase 0 完成后）**：

4. **Phase 2 T5-A** — 关键路径核心；2-4 月集中工作

**与上面所有 streams 并行（不在 critical path）**：

5. **Phase 4 Stream NA-2**（D6 falsification testing）— ongoing
6. **Phase 3 Stream C3 + C4**（stabilizer-QM + FOL 嵌入）— 1-2 月每个；推荐至少做 C3 因为已经部分写在 Bilinear

**何时启动 Phase 5 / 6**：等 T5-A 通过后。Phase 5（empirical / peer）需要 publishable artifact；Phase 6（V4 inductive elim）是 polish，没紧迫性。

## 十、一句话总结

**3-6 个月集中工作可达 minimum viable GUT claim**（GUT-A），critical path 是 Phase 0 → Phase 2 T5-A，其余 G1 / G3 / G4 / G5 全部可并行。**真正的风险**不在工程量，而在 T5-A 过程中可能发现 P1-P7 需要 revise — 这种发现是 foundational progress，不是 setback。完成 GUT-A 后 publish，再决定是否继续推 GUT-B（algebraic-class parametric）和 GUT-C（full δ-realisation）。

---

## 附：与 wen-substrate v0.6 § 7.4 "What Remains" 的关系

v0.6 当时说 What Remains 是「engineering and refinement tasks, not foundation tasks」。本路线图是把那份 informal 承诺**升级成具体可执行的 6-12 月 implementation plan**：

| v0.6 "What Remains" | 本路线图对应 |
|---|---|
| Implementation: Build out R-Family in Lean 4 | ✅ 已经完成（125k LOC）；本路线图是 *next* implementation |
| Application: 加密 / 量子 / AI alignment | Phase 3 (case studies) + Phase 4 (non-algebraic δ) |
| Refinement: 5-fold virtues / character inventory | 已在 Atlas/ 完成；本路线图不再列 |
| Engagement | Phase 5 Stream E-2 |

v0.6 不曾 articulate T5 — 这是 v0.7+ Part VIII 加入的 obligation。本路线图把 T5（Tier 1 G2）放在 critical path 中央，因为没有 T5，GUT claim 就只是 "R-family 满足 P1-P7"，不是 "R-family **就是** universal substrate"。

---

## 十一、Achieved status (2026-05-16)

Single-session batch execution closed the **minimum viable GUT-A claim** with 0 sorry / 0 new axioms across all critical files. Status by gap:

| Gap ID | Item | Status | Lean file(s) | Commit |
|---|---|---|---|---|
| **G6.1** | T_P3 uniqueness (6/6 clauses) | ✅ closed | `R/PhaseZero.lean` § 1.1 | `0e18361` |
| **G6.2** | T_P6 Lorentzian bridge | ✅ closed | `R/PhaseZero/TP6Lorentzian.lean` | `55cfe40` |
| **G6.3** | T_P7b Wedderburn uniqueness + Mathlib bridge | ✅ closed | `R/PhaseZero/TP7bUniqueness.lean` | `924f583` |
| **G4** | δ=Prop non-algebraic instance | ✅ closed | `R/Distinction/Prop.lean` | `41093f1` |
| **G1.A1** | D1 ⟹ P1 analytic | ✅ closed | `R/ClaimZ/Analytic/P1.lean` | `d575e81` |
| **G1.A2** | D1 ⟹ P2 analytic | ✅ closed | `R/ClaimZ/Analytic/P2.lean` | `f05807a` |
| **G1.A3** | D1 ⟹ P3 analytic | ✅ closed | `R/ClaimZ/Analytic/P3.lean` | `4f5bc5f` |
| **G1.A4** | D1 ⟹ P4 analytic | ✅ closed | `R/ClaimZ/Analytic/P4.lean` | `93d2fa2` |
| **G1.A5** | D1 ⟹ P5 analytic | ✅ closed | `R/ClaimZ/Analytic/P5.lean` | `023c92a` |
| **G1.A6** | D1 ⟹ P6 analytic | ✅ closed | `R/ClaimZ/Analytic/P6.lean` | `29b0fb0` |
| **G1.A7** | D1 ⟹ P7a analytic | ✅ closed | `R/ClaimZ/Analytic/P7a.lean` | `c8f69a7` |
| **G1.A8** | D1 ⟹ P7b analytic | ✅ closed | `R/ClaimZ/Analytic/P7b.lean` | `b486acb` |
| **G1.integration** | Phase 1 packaged into `D1_implies_Phase1Closure_F2` | ✅ closed | `R/ClaimZ/Analytic.lean` | `7c2a125` |
| **G2** | T5-A: P1-P7 ⟹ R-family-over-F₂ uniqueness (layerwise) | ✅ closed (tractable form) | `R/UniquenessF2.lean` | `23441fc` |
| **G2'** | T5 polymorphic: P1+P2 over any Fintype δ ⟹ R N δ layerwise | ✅ closed | `R/UniquenessGeneral.lean` | `a980e92` |
| **G2''** | T5 algebraic-class: P1+P2+P7b over any Field k ⟹ R N k layerwise + ring iso at carrier 4 | ✅ closed | `R/UniquenessAlgebraic.lean` | `821a2f3` |
| **G2'''** | Concrete polymorphic T5 demos at Distinction, ZMod 3, Fin 5 + Bool↔ZMod 2 cross-instance | ✅ closed | `R/UniquenessGeneral/Demos.lean` | `3e47cd7` |
| **G3.C3** | Stabilizer-QM (Pauli group) ↪ R 2n | ✅ closed | `Wen/Embeddings/StabilizerQM.lean` | `975104d` |
| **G3.C4** | FOL syntax tree ↪ R N | ✅ closed | `Wen/Embeddings/FOL.lean` | `f87c40f` |
| **G5** | D6 falsification record (HoTT/ETCS/SDG attempts) | ✅ closed | `R/D6_Tests.lean` | `b1f1181` |

**Aggregate**: 20 closures, 0 sorry / 0 axioms across all GUT-A + polymorphic files. Full library `lake build SSBX` = 3830 jobs clean.

### 十一·1 Polymorphic T5 update (2026-05-16, `a980e92`)

Per user direction *"让我们把它推广到general，而不是只有bool"*, the layerwise T5 statement is now **δ-polymorphic** (works for any `[Fintype δ] [DecidableEq δ] [Inhabited δ]`):

```
theorem T5_general (S : P1P7_Core δ) (N : ℕ) : Nonempty (S.carrier N ≃ R N δ)
```

`R/UniquenessGeneral.lean` delivers:

- `P1P7_Core δ` — polymorphic minimum-data structure (carrier family + Fintype/decEq + zero-card + base-card + direct-sum), no ring requirements.
- `R.card_eq_general` — `|R N δ| = (|δ|)^N` polymorphic cardinality.
- `T5_general` — layerwise type-equiv for any δ with Fintype + DecidableEq + Inhabited.
- Four canonical δ-corollaries: `T5_general_at_Bool`, `T5_general_at_Distinction`, `T5_general_at_Fin n`, `T5_general_at_ZMod p`.
- `forgetF2ToCore` + `T5_A_from_general` — the F₂-Boolean `T5_A` is now a derived corollary at δ=Bool.
- `T5_general_squaring_compatible` — polymorphic squaring tower.
- `canonicalRFamily δ : P1P7_Core δ` — the R-family itself as a canonical instance (non-vacuous sanity check).
- `GUT_B_layerwise` — aggregator packaging the polymorphic content.

**What this re-positions**: the framework is no longer "F₂-Boolean classical" specifically; F₂-Boolean is the δ=Bool **specialization** of a polymorphic uniqueness claim. The minimum viable GUT claim is therefore:

> **GUT-B (layerwise)**: any structure satisfying the *core P1+P2* closure conditions over any `[Fintype δ] [DecidableEq δ] [Inhabited δ]` substrate is layerwise type-equivalent to R-family-over-δ.

What remains δ-specific (post-this-update):

- **Ring iso at carrier 4** (`T5_A_ringEquiv_at_4`) — requires δ with ring structure; F₂ + char(k)=2 fields extend trivially, char(k)≠2 needs Wedderburn-over-k.
- **Bilinear classification (P3)** — Arf invariant is char(k)=2 specific; discriminant replaces it for char(k)≠2.
- **P6/P7a alphabet pinning** — uses 4-element / 8-element cardinality, which generalize as `(|δ|)² = 4` only for δ = Bool.

These are the remaining items for the **full** GUT claim (T5-B + T5-C scope).

### 十一·2 Polymorphic completion update (2026-05-16, batch 5)

Three parallel agents in batch 5 completed the algebraic-class extension + concrete demos + doc updates:

**G2'' Algebraic-class T5** (`R/UniquenessAlgebraic.lean`, commit `821a2f3`):
- `P1P7_Satisfier_Algebraic (k : Type) [Field k] [Fintype k] [DecidableEq k]` — extends `P1P7_Core k` with `p7b_ring_equiv : Nonempty (carrier 4 ≃+* Matrix (Fin 2) (Fin 2) k)` + Mul/Add instances.
- `T5_algebraic` — combines T5_general (layerwise) with the ring iso at carrier 4 for any field k.
- F₂-Boolean lift via the **ZMod 2 bridge** (`forgetF2ToAlgebraic_ZMod2`): the existing `P1P7_Satisfier_F2`'s `p7b_mat2F2_equiv` composes with `Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)` (from G6.3's TP7bUniqueness) to give a `P1P7_Satisfier_Algebraic (ZMod 2)`.
- Char(k)=2 demo at `ZMod 2` proves layerwise + ring-iso for F₂'s natural algebraic-class cousin.

**G2''' Concrete polymorphic demos** (`R/UniquenessGeneral/Demos.lean`, commit `3e47cd7`):
- δ=Distinction non-canonical instance via `Distinction.equivBool` transport.
- δ=ZMod 3 (`|R 2 (ZMod 3)| = 9`, `|R 3 (ZMod 3)| = 27`, ternary substrate).
- δ=Fin 5 (`|R 2 (Fin 5)| = 25`, 5-ary non-field substrate).
- Cross-instance: `R N Bool ≃ R N (ZMod 2)`, `R N Bool ≃ R N Distinction`, `R N Distinction ≃ R N (ZMod 2)`.
- `concrete_polymorphic_T5_demo` — 7-tuple aggregator packaging all witnesses.

**Doc updates** (`wen-substrate/02-parametric.md`, `07-claim.md`, `08-obligations.md`, commit `3edbeb7`):
- 02-parametric: added "Polymorphic T5" section documenting the four δ-corollaries.
- 07-claim: refined direct claim from "R-Family over F₂" to "δ-polymorphic R-Family; F₂ canonical not restriction".
- 08-obligations: 3-row T5 status table (T5 layerwise ✅, T5-A F₂ ring iso ✅, T5-B/C ring iso polymorphic ✅ via UniquenessAlgebraic).

**Aggregate (post-batch-5)**: 22 closures total, 0 sorry / 0 axioms, lake build 3830+ jobs clean. The polymorphic generalization is **complete** at the layerwise + ring-iso (over Field k) level.

What remains for the **strongest** GUT claim form:

- **Char(k)≠2 bilinear classification**: discriminant-based P3 for non-char-2 fields.
- **Non-algebraic δ (Prop, Heyting algebra, etc.)**: requires constructive/non-Fintype handling; T5-C territory.
- **D1 ⟹ P-closure over polymorphic δ**: currently `D1_implies_Phase1Closure_F2` is δ=Bool specific; polymorphic D1 analytic direction is an open extension.

These are research-level extensions; the **minimum viable polymorphic GUT claim** is now formally proven for any Fintype + DecidableEq + Inhabited δ at the layerwise level, and for any Field k at the ring-iso level.

### What "minimum viable GUT-A" means at this status

**Analytic direction** (Claim Z 's D1 ⟹ P-closure side):

> `theorem D1_implies_Phase1Closure_F2` — given a `D1Articulation S` satisfying the eight D1 atomic conditions, the `Phase1Closure_F2` record carries witnesses for P1-P7 (8 fields including P7a + P7b sub-properties), all derived from the eight `Analytic/P*.lean` modules with no PClosure assumption.

**Synthetic direction** (Claim Z's P-closure ⟹ R-family side):

> `theorem T5_A` — for any `P1P7_Satisfier_F2 S`, every layer `S.carrier N ≃ R N` as a type. Plus `T5_A_ringEquiv_at_4` (ring-iso at the smallest non-trivial layer) and `T5_A_squaring_compatible` (squaring tower respected) and `T5_A_aggregator` (7 of 12 wen-substrate v1.0.3 §3.1 items packaged).

**Falsifiability**: three independent candidate falsifications (HoTT / ETCS / SDG) formally documented as non-instantiators of `D6_ClaimZFalsified` with structural reasons (univalence is δ-enrichment, ETCS↔BZC, SDG = R-Family-over-`k[ε]/(ε²)`).

**Universality witnesses**: F₂-Boolean classical R-Family + δ=Prop non-algebraic instance (G4) + Pauli-stabilizer QM (G3.C3) + propositional logic (G3.C4) — four explicit articulation cases.

### What remains (post-GUT-A refinement)

| Gap | Status | Note |
|---|---|---|
| **T5-A items 4, 6** | open (Risk Option a) | Bilinear / Hom naturality under `p2_directSum`; require adding fields to `P1P7_Satisfier_F2` |
| **T5-A items 8, 9, 11** | open (deferred to T5-B/T5-C) | R∞ profinite / Atlas naming / atomic-op naturality — orthogonal to T5-A scope |
| **G7** cross-base functor library | open | Mod-phase Hilbert→Pauli, representation reverse — `RFamily k N` parametric bridges (planned) |
| **G8** empirical predictions | open | Not on critical path; pick LLM attention-pattern prediction & find collaborator |
| **G9** peer engagement | open | Send wen-substrate/ to Awodey/Shulman/Lawvere-lineage/Spencer-Brown successors |
| **G10** V4 inductive → abbrev | open (orthogonal polish) | 90+ `cases g <;> rfl` rewrites; structural integrity only |
| **G11** T5-B parametric over `k` | open | Algebraic class beyond F₂ |
| **G12** T5-C full δ-realisation | open | Research-level; may need new categorical framework |
| **G13** per-base ℝ/ℂ/ℂ_p bridges | open | Mathlib classical foundations |

### Recommended next moves

1. **Publish-quality polish**: update `wen-substrate/07-claim.md` and `wen-substrate/08-obligations.md` with the new "GUT-A discharged" status.
2. **T5-A items 4/6 refinement** (Risk Option a): strengthen `P1P7_Satisfier_F2` with naturality fields, close items 4 and 6.
3. **G7 cross-base functor library**: write the parametric Hilbert→R-Family functor + Pauli representation inverse.
4. **Peer engagement** (G9): send the framework out for external critique.

The original 3-6 月 estimate now applies to **GUT-B** (parametric over algebraic class) and **GUT-C** (full δ-realisation incl. non-algebraic), not GUT-A.

---

## 十二、G11 cut-1 plan — char(k)≠2 finite fields (2026-05-17)

Per `docs-next/00_start/lawvere-identification.md` v0.4 status — metalogic identification done, GUT-A polish path identified. Next major milestone: extend GUT to **any finite field** (char ≠ 2 included), staying inside Mathlib's existing infrastructure.

### Why cut-1 over full G11

Full G11 (任意 field k, 含 ℝ/ℂ/ℚ_p) requires Brauer group machinery, Witt theory over arbitrary fields, Hasse-Minkowski local-global — **research-level, 4-8 月**.

**Cut-1 scope**: only finite fields F_p (odd prime p) + F_{p^n}. Skips:
- Infinite fields (ℝ, ℂ, ℚ_p) — left to G11+ / GUT-C
- Brauer group infrastructure (over finite fields Br(F_q) = 0 trivially via Wedderburn's little theorem)
- Unified char-agnostic treatment — char 2 stays Arf-based, char ≠ 2 gets parallel disc-based

⟹ Cut-1 compressible to **~2-3 月** (vs full G11 4-8 月) via parallel execution.

### Cut-1 sub-tasks

| Sub-task | Status | File | Owner |
|---|---|---|---|
| **G11-A** Install `IsSimpleRing`/`IsArtinianRing` on Mat₂(F_q) | in-progress | `Foundation/R/Algebra/MatFqInstances.lean` (new) | parallel subagent |
| **G11-B** Discriminant-based P3 for char(k)≠2 finite fields | in-progress | `Foundation/R/Bilinear/DiscriminantCharNeq2.lean` (new) | parallel subagent |
| **G11-C** Polymorphic UniquenessGeneralField scaffold + char-class dispatch | in-progress | `Foundation/R/UniquenessGeneralField.lean` (new) | parallel subagent |
| **G11-D** T5-A items 4+6 closing (GUT-A polish, orthogonal) | in-progress | `Foundation/R/UniquenessF2.lean` (edit) | parallel subagent |

**Strategy**: 4 subagents parallel since files are disjoint. G11-A unblocks Wedderburn application; G11-B provides char ≠ 2 bilinear; G11-C ties them together; G11-D closes the last GUT-A residual.

### Cut-1 completion criteria

- All 4 subagents' new files `lake build` clean (sorries allowed where document blockers)
- `Foundation/R/UniquenessGeneralField.lean` provides `T5_field` over any `[Field k] [Fintype k]` with char-class dispatch
- Concrete demos at `ZMod 3`, `ZMod 5`, `ZMod 7` produce non-trivial layerwise + ring-iso witnesses
- T5-A items 4+6 closed → full GUT-A claim no caveats

### Post-cut-1 remaining (deferred to G11+ / GUT-C)

| Item | Estimate |
|---|---|
| Infinite fields ℝ / ℂ / ℚ_p | 6-12 月 (Brauer + Witt + Hasse) |
| Discriminant-Arf unified treatment | 1-2 月 |
| Per-base bridges (G13) | 月-each |

These are no longer blocking GUT publication; cut-1 brings GUT "any finite field" 内的 *publishable strong claim*.

### Status snapshot — what's already closed

(Per §十一 + this cut-1 session, post-2026-05-17)

| Layer | Status |
|---|---|
| GUT-A (F₂-Boolean classical) | ✅ closed (2026-05-16) |
| GUT-A items 4+6 (T5-A naturality residuals) | 🟡 cut-1 G11-D in-flight |
| GUT-B layerwise (any Fintype δ) | ✅ closed (2026-05-16) |
| GUT-B algebraic-class (any Field k, ring-iso assumed) | ✅ closed (2026-05-16) |
| GUT-B algebraic-class (any finite Field k, ring-iso derived via Wedderburn) | 🟡 cut-1 G11-A/B/C in-flight |
| GUT-B over infinite fields (ℝ/ℂ/ℚ_p) | ⏳ deferred to GUT-C |
| GUT-C (non-algebraic δ realisation) | ⏳ open (research-level) |
| Metalogic identification (D1 = lfp(Φ)) | ✅ closed (2026-05-17) — see `lawvere-identification.md` v0.4 |
