# Phase Status — main @ 1c76a55 (2026-05-11)

> 状态：v3 (2026-05-11) — 与 main = 1c76a55 (Phase C R-aliases + RHierarchy umbrella) 对齐。Cell192 已删；Shi 已升 V₄ Klein {道, 已, 今, 未}；R₀..R₈ strict (Z/2)ⁿ uniform 是当前形式 spine。
> 作用：本文件是 main 的"现在长什么样"快照，给未来读者作 ground truth。任何 commit 信息或文档与本文不一致时，**以代码为准、以本文为辅**。
> 配套：[research-position.md](research-position.md)（学术 positioning）、[yi-RO-hierarchy.md](../10_formal_形式/yi-RO-hierarchy.md)（v2.1 doctrine）、[root-layer-map.md](../10_formal_形式/root-layer-map.md)（结构定义）。

---

## 1. 当前 main 是什么状态

```
main = origin/main = 1c76a55 (Phase C: R₀..R₈ index alias + RHierarchy)
最近 commits:
  1c76a55 Phase C: R₀..R₈ index-named alias files + RHierarchy umbrella
  8e4406e Phase F.6 + G + B.1: cleanup + doc sync + YinBit dedup
  0003224 Phase F.x.5: complete Cell192 → Cell256 migration in Modern/* cascades
  7de5064 Phase A-F: doctrine alignment — Cell192 → Cell256 (V₄ Shi)
  e4c07a4 docs: add phase-status.md (旧版 — 即本文)
  687eac1 P6: downstream alignment (旧 BenZheng + Face line)
  9dd29ed Merge claude/pensive-meitner-c79a1f — MetaInterp Phase 2.3 + wenyan CLI
```

**Build**：`lake build SSBX` 3656/3656 jobs（在 1c76a55 上）。0 errors、0 sorry 净增、0 项目自定义 axiom（R8_complete 仍只依赖 propext + native_decide）。

**两份 wenyan exe 双 CLI**（Phase F 之后仍在）：
- `wenyan-surface` (~1949 行，speaks WenSurface 文言)
- `wenyan` (speaks baguaWen IL；底盘已迁 Cell256；新 `MetaInterp/Assembly.lean` 已承接 base-256 structural assembly，legacy `WenyanSelfInterp.lean` universal route 仍不是 full arbitrary-program interpreter — 详 §5.3)

---

## 2. v3 的形式 spine：R₀..R₈ + V₄ Shi + Cell256

main 在 7de5064/0003224/8e4406e/1c76a55 之后的关键事实：

### 2.1 Cell192 已删（Phase F.6）

[`formal/SSBX/Foundation/Bagua/Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) 已不存在（commit 8e4406e 删除）。Shi 不再是 3 元 {ji, jin, wei} 之 Z/3，而是 4 元 V₄ Klein 群 {dao, ji, jin, wei}（commit 7de5064 升级）。所有 192-cell 之 callsite 已迁移到 256-cell（commit 7de5064 + 0003224 共 ~50+5 个文件）。

### 2.2 R₀..R₈ strict (Z/2)ⁿ uniform 是 spine

[`Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)（umbrella）一处导入，得到 R₀ 到 R₈ 共 9 层：

| R | type | 卡 | Lean 锚 |
|---|---|---|---|
| R₀ | Unit | 1 | [`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) |
| R₁ | Yao | 2 | [`R1_Yao.lean`](../../formal/SSBX/Foundation/Hierarchy/R1_Yao.lean) |
| R₂ | SiXiang | 4 | [`R2_SiXiang.lean`](../../formal/SSBX/Foundation/Hierarchy/R2_SiXiang.lean) |
| R₃ | Trigram | 8 | [`R3_Trigram.lean`](../../formal/SSBX/Foundation/Hierarchy/R3_Trigram.lean) |
| R₄ | Mian = Ben × Zheng | 16 | [`R4_Mian.lean`](../../formal/SSBX/Foundation/Hierarchy/R4_Mian.lean) |
| R₅ | Wuyao = Mian × Bool | 32 | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) |
| R₆ | Hexagram | 64 | [`R6_Hexagram.lean`](../../formal/SSBX/Foundation/Hierarchy/R6_Hexagram.lean) |
| R₇ | Cell128 = Hex × YinBit | 128 | [`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) |
| R₈ | Cell256 = Hex × Shi | 256 | [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) |

每相邻 (Rₙ, R_{n+1}) 在 [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) 内有 uniform `liftR{n}toR{n+1}` / `projR{n+1}toR{n}` + `proj_lift_id_R{n}` retract 引理。

### 2.3 Shi V₄ Klein 是 R₈ 闭合

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) 内 `Shi` = {dao, ji, jin, wei}，即 V₄ Klein 群（每元自逆，cuo involution period 2）。Shi ↔ YinBit × GuoBit 的双射 `Shi.toYinGuo` 给出 R₈ = Hexagram × Shi = (Z/2)⁸ 之 strict 256 = (Z/2)⁸ 闭合。Shi V₄ 之 4 元对应 Cell256 后 2 位：

| Shi | (因, 果) | mask 后 2 位 | V₄ 元 |
|---|---|---|---|
| 道 | (0, 0) | `oo` | identity |
| 已 | (1, 0) | `xo` | σ_P |
| 未 | (0, 1) | `ox` | σ_T |
| 今 | (1, 1) | `xx` | σ_PT |

### 2.4 algebraic spine（Phase A）

`Cell128` / `Cell256` 现在是 abelian 群（`AddCommGroup` 风格 Add/Zero/Neg/Sub）+ `SMul` 自身作用（Cayley regular representation）。origin = (qian, dao) = V₄ identity = (Z/2)⁸ zero。同构 ι : R₈ → Aut(R₈), c ↦ (· ⊕ c) 与 ε(f) := f(道) 互逆。

印 (yìn) = XOR mask `(qian, ji)`，投 (tóu) = XOR mask `(qian, wei)` — 都已 atomic。

Self-similarity v1.1 补齐：[`SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean) 现含 R₁ ≃ R₀⊕R₀、R₆ 三路汇聚、R₈ ≃ R₇×Bool；[`V4Tensor.lean`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean) 现含 R₈ = R₆ × trace bit × projection bit、4 个 temporal-state-indexed R₆ slices、Way (道) origin/no-op、cell-as-operator 单射。

### 2.5 OX 字面 macro

[`Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) 提供 `OX["xxxxxxxx"]` 8-char 字面，把 8 个 `o`/`x` 字符串编为 Cell256 立即数。位 7/8 编 YinBit/GuoBit → Shi。

### 2.6 BenZheng + Face 仍并存（v2 之事实未变）

[`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) 内的 4 本 / 4 征 / 16-Mian / 4-Quadrant 与 [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 内的 12-Face inductive **仍然并存**（与 main @ 687eac1 一致）。Mian 现在被显式认作 R₄（v2.1 doctrine 之 first-class layer）。

| 维度 | Face | BenZheng / Mian |
|---|---|---|
| 形式锚 | M-line 的 M1 层 | R₄ trigram-level + R₆ quadrant |
| 作用 | 把 333 atom 分类到 12 domain | 把 8 trigram 分成 4+4 + 64 卦 4-quadrant |
| Lean type | `inductive Face` (12 ctors) | `Ben × Zheng = 16` |

---

## 3. 已完成 / 待办的 phase 矩阵

下面的 phase 矩阵反映 commit 7de5064 之 task 计划之实际状态：

| Phase | 任务 | 状态 | 落地 commit |
|---|---|---|---|
| **A** | Cell128/256 algebraic spine + Cayley ι/ε + 印/投 atomic | done | 7de5064 |
| **B.1** | YinBit dedup（canonical 在 Cell128） | done | 8e4406e |
| **B.2** | temporal state → Bool × Bool abbrev（trace bit × projection bit） | done | `R8.lean` + `V4Tensor.r8_temporal_coordinate_summary` |
| **C** | Foundation/Hierarchy/R{0..8}_*.lean alias files + umbrella | done | 1c76a55 |
| **D** | LiftProject uniform R₀..R₈ pairs | done | 7de5064 |
| **E** | Operators/{Atomic, V4Outer}.lean inner/outer split | done | 7de5064 |
| **F.1–F.5** | Shi 3-元 → V₄；下游 Cell192→Cell256 | done | 7de5064 |
| **F.x.5** | Modern/* cascades 数值迁移 | done | 0003224 |
| **F.6** | Cell192.lean 删除 | done | 8e4406e |
| **G** | Doc sync (yi-RO-hierarchy / yi-calculus-theorem / yi-as-meta-framework / SSBX/README) | done | 8e4406e |
| **G+** | docs-next/ 系列 v3 重写（本轮工作） | in progress | (本提交) |
| **F.7a** | base-256 concrete dispatch/assembly structural summary | done | `MetaInterp/Assembly.metaInterpProg_base256_structural_summary` |
| **F.7b** | exact-fuel semantic-compose frontier interface | done | `MetaInterp/Universal.metaStart_runFuel_five_eq_postPrologue` + `semantic_compose_frontier_summary` |
| **F.7c.1** | expose U.1/U.2/U.3 as no-sorry semantic-obligation interface + prove generic META halted padding | done | `SemanticLoopObligations`, `semantic_loop_obligation_frontier_summary`, `metaInterpProg_meta_halted_padding` |
| **F.7c.2** | close unconditional zero-step compose and make Strategy-B fixed-parameter boundary machine-checkable | done | `metaInterpProg_simulates_zero_steps`, `StrategyBCompatibleProgram`, `universal_compose_current_boundary_summary` |
| **F.7c.3** | strengthen pc=0 fetch scaffold from hand-off to exact dispatch route | done | `Fetch.fetchProtocol_simulates_pc0_to_dispatch` |
| **F.7c.4** | expose exact-fuel route wrappers for concrete `FetchProg` peel witnesses | done | `fetchProg_routes_halted_at_fuel`, `fetchProg_routes_running_to_dispatch_at_fuel` |
| **F.7c.5** | specialize concrete fetch route wrappers to assembled `metaInterpProg` segment | done | `metaInterpProg_fetchProg_at_offset`, `metaInterpProg_fetch_routes_*_at_fuel` |
| **F.7c** | construct concrete U.1/U.2/U.3 semantic witnesses from fetch peel/decode + hard-block effects | pending | — |
| **B.3** | Cell192 archive 引用扫尾（docs-next 之外）| pending | — |

---

## 4. 已确立的事实（可作 ground truth）

### 4.1 代数事实（数学层）

- 8 trigram = (Z/2)³，**zong-orbit 分解 = 4 palindromic + 4 non-palindromic** —— 这是结构必然，不是设计选择
- 64 hexagram = 4 quadrant × 16，**cuo 永远象限内，zong swap 本征↔征本，hu 4-attractor 全在本本**
- 256 cell = 64 hex × 4 Shi，Shi 是 V₄ Klein 群，cuo on R₈ = `xxxxxxoo` (R₆ side)
- 这些都有 `native_decide` 可证的 Lean theorem（在 [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) / [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) / [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)）

### 4.2 命名事实（surface 层）

[`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean)（已 Cell256-migrated）已 register（与 v2 表大体一致；R₈ 行新增 V₄ Shi 之 道/已/今/未 字位）：

| 层 | 字根 | 状态 |
|---|---|---|
| R₁ | 实/虚 (Yao essence) | done build pass |
| R₂ | 春/夏/秋/冬 (SiXiang season) | done |
| R₃ | 健/悦/显/起/入/险/止/顺 (trigram virtue) | done |
| R₃ | 乾/兑/离/震/巽/坎/艮/坤 (trigram literal) | done |
| R₄ (= R₆ outer flip in old numbering) | 改/化/变/临/主/极 (6-yao flip) | done |
| R₇ | 印 (yìn, toggle 因) | done Cell128 atom |
| R₈ | 投 (tóu, toggle 果) + Shi V₄ {道,已,今,未} | done Cell256 atom |
| L0 | 静/置/翻/互/错/综/侔/会/跳/推/取/终 | done |
| 全表 | `allLayerChars` | done |

### 4.3 文档已落地 / v3-aligned

| 文件 | 状态 | 内容 |
|---|---|---|
| [yi-RO-hierarchy.md](../10_formal_形式/yi-RO-hierarchy.md) | v2.1 定本 | R₀..R₈ strict uniform 主 doctrine |
| [yi-calculus-theorem.md](../10_formal_形式/yi-calculus-theorem.md) | Phase G done | Theorems A–K + R₀..R₈ status table |
| [yi-as-meta-framework.md](../10_formal_形式/yi-as-meta-framework.md) | Phase G done | self-description GUT 解读 |
| [cell256-grid.md](../10_formal_形式/cell256-grid.md) | v3 sibling | 256 cell × Shi V₄ 全表（并行 agent 写作中）|
| [v4-shi.md](../10_formal_形式/v4-shi.md) | v3 sibling | V₄ Klein Shi 之代数（并行）|
| [cell256-algebra.md](../10_formal_形式/cell256-algebra.md) | v3 sibling | Cayley ι/ε / abelian spine（并行）|
| [yin-tou-operators.md](../10_formal_形式/yin-tou-operators.md) | v3 sibling | 印/投 XOR mask 详解（并行）|
| [ox-notation.md](../10_formal_形式/ox-notation.md) | v3 sibling | `OX["..."]` macro 用法（并行）|
| [operator-split.md](../10_formal_形式/operator-split.md) | v3 sibling | inner/outer 算子拆（并行）|
| [lift-project.md](../10_formal_形式/lift-project.md) | v3 sibling | R₀..R₈ Lift/Project pairs（并行）|
| [layer-character-map.md](../10_formal_形式/layer-character-map.md) | v3 本轮重写 | R0–L0 字根映射 |
| [layer-axis-graph.md](../10_formal_形式/layer-axis-graph.md) | 待审 | 三轴汇聚 Mermaid |
| [sanben-sijieduan-grid.md](../10_formal_形式/sanben-sijieduan-grid.md) | v3 本轮重写 | 12-grid (3×4) |
| [64-hexagram-grid.md](../10_formal_形式/64-hexagram-grid.md) | v3 本轮重写 | 64 卦 4-quadrant + 算子 invariant + Cell256 扩展 |
| [position-operator-tree.md](../10_formal_形式/position-operator-tree.md) | v3 本轮重写 | 算子树 R₀..R₈ 全程 |
| [core.md](../10_formal_形式/core.md) | v3 本轮重写 | 形式层入口 |
| [foundation-core.md](../10_formal_形式/foundation-core.md) | v3 本轮重写 | Foundation/{Core,Bagua} 模块 |
| [module-map.md](../10_formal_形式/module-map.md) | v3 本轮重写 | 模块簇地图 |
| [research-position.md](research-position.md) | 既往 | 学术 positioning（已立 vs novel）|
| [roadmap-self-similarity-v1.md](roadmap-self-similarity-v1.md) | v1.1 本轮完成 | self-similarity gaps closed + classical-language/Quantum typed skeleton boundaries |

---

## 5. 已知不一致 / 需注意的点

### 5.1 commit message 历史断层

`687eac1` 的 commit message 说 "Face 12-enum gone" — 但实际 diff 把 Face 加了回来。`0b07636` 当时确实删了 Face；后续 687eac1 又加回来了。**实际状态以代码为准**：当前 main（1c76a55）下 Face inductive **仍然存在** 在 [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean)，与 BenZheng / Mian 并存。

### 5.2 root-layer-map.md 的旧 12-Face 列表

[`root-layer-map.md`](../10_formal_形式/root-layer-map.md) §3.1 仍列出 12 Face 名（文面/物面/生面/...）—— **这是正确的、与现状一致**。Face 在代码中确实有，所以这个列表不需要改。但顶部的 status block 应被本 v3 phase-status 覆写为最新。

### 5.3 WenyanSelfInterp.lean 的 base-256 dispatch 待重派生

commit 7de5064 之 status 说：
> WenyanSelfInterp.lean dropped legacy dispatchProg + universalMetaInterp (base-192-specific routing); Phase 2.3 12/12 cur-effect simulation theorems retained. Re-derive base-256 dispatch in follow-up.

这意味着 wenyan IL 可执行/ Phase 2.3 cur-effect 同步证明都仍在。base-256 structural assembly 已转移到 `MetaInterp/Assembly.lean`，exact-fuel composition frontier、zero-step/prologue compose、U.1/U.2/U.3 obligation interface 与 Strategy-B fixed-parameter boundary 已在 `MetaInterp/Universal.lean`；`Fetch.lean` 已把 pc=0 scaffold 推进到 exact dispatch route；`FetchProg.lean` 已暴露 halted/running peel-witness route 的 exact fuel；`Assembly.lean` 已把这些 route wrappers 专门化到 `metaInterpProg` 的 fetch segment。full arbitrary-program universal compose 仍 pending，原因是 concrete fetch peel/decode、hard-block semantic effects、parameterized sub-dispatch 还未全部构造。

### 5.4 docs-next 之外的 archive 引用

`docs-next/` 之外（特别是 `史料/` 与 `义理/` 旧文）仍有大量 `Cell192` / `192格` 字样 — 按 [scope.md](scope.md) 之"不删除或移动旧 文档"原则，这些 archive 引用不必处理；只 docs-next 内须 v3-align。

---

## 6. 下一阶段（如果继续）

### 6.1 必要 cleanup

- [x] Phase B.2: temporal state is already a Bool × Bool abbrev; see `R8.lean` and `V4Tensor.r8_temporal_coordinate_summary`
- [x] Phase F.7a: base-256 concrete dispatch/assembly structural summary
- [x] Phase F.7b: exact-fuel semantic-compose frontier interface
- [x] Phase F.7c.1: U.1/U.2/U.3 semantic-obligation interface + generic META halted-padding lemma
- [x] Phase F.7c.2: zero-step/prologue compose + Strategy-B fixed-parameter boundary
- [x] Phase F.7c.3: pc=0 fetch scaffold reaches dispatch route
- [x] Phase F.7c.4: exact-fuel route wrappers for concrete FetchProg peel witnesses
- [x] Phase F.7c.5: assembly-specialized fetch route wrappers
- [ ] Phase F.7c: construct concrete U.1/U.2/U.3 witnesses（重新对接 fetch peel/decode、hard-block semantic effects、parameterized sub-dispatch + arbitrary-program simulation）
- [ ] 审查所有老 doc 的代码锚点是否还指向有效路径（Cell192 引用）

### 6.2 可选扩展

- [ ] 把 R5 Wuyao 之 32 元 给一组 surface 字根（目前只有 mathematical type，无传统 Yi anchor — 详 [yi-RO-hierarchy.md §3.5](../10_formal_形式/yi-RO-hierarchy.md)）
- [ ] Lean 化 "4 mark = phase-space 4 quadrant"（[research-position.md §4.2](research-position.md)，需要 ℝ 嵌入框架）
- [ ] Lean 化 "hu attractors = 4 truth values"（[research-position.md §4.6](research-position.md)）

---

## 7. 给后来读者：怎么验证当前状态

```bash
# 1. 确认 build pass
lake build SSBX        # 应该 3656 jobs success
lake build wenyan-surface  # WenSurface CLI
lake build wenyan          # baguaWen CLI

# 2. 确认 Cell192 已删
test ! -e formal/SSBX/Foundation/Bagua/Cell192.lean

# 3. 确认 Cell256 + Shi V₄ 在
grep -c "inductive Shi\b" formal/SSBX/Foundation/Bagua/Cell256.lean   # = 1
grep -E "\| dao\| ji\| jin\| wei" formal/SSBX/Foundation/Bagua/Cell256.lean

# 4. 确认 RHierarchy umbrella 在
test -f formal/SSBX/Foundation/Hierarchy/RHierarchy.lean
ls formal/SSBX/Foundation/Hierarchy/R{0..8}_*.lean | wc -l   # = 9 alias files (R5_Wuyao 真实，其余 alias)

# 5. 确认 BenZheng + Face 并存（v2 旧事实仍在）
grep -c "inductive Face\b" formal/SSBX/Foundation/Core/MonadRoot.lean   # = 1
grep -c "inductive Ben\b" formal/SSBX/Foundation/Bagua/BenZheng.lean    # = 1

# 6. 确认 LayerCharacterMap 全 build
lake build SSBX.Text.LayerCharacterMap

# 7. 字根映射查 spot-check
# (跑 wenyan / wenyan-surface 给样本输入)
```

---

## 8. 一行总结

**main @ 1c76a55 是 Phase A–G + Phase C R-aliases 之收口点**：

- R₀..R₈ strict (Z/2)ⁿ uniform spine（RHierarchy umbrella 一处 import）
- Cell192 已删；Cell256 + Shi V₄ {道, 已, 今, 未} 是 R₈ 之 (Z/2)⁸ 闭合
- Cell128 / Cell256 algebraic spine（AddCommGroup + SMul + Cayley ι/ε）+ 印/投 XOR atomic
- 下游 ~50+5 文件已迁移、Modern/* cascades 数值已对齐
- 0 sorry 净增、0 项目自定义 axiom（R8_complete 仅用 propext + native_decide）
- 双 CLI（wenyan / wenyan-surface），但 wenyan universalMetaInterp base-256 dispatch 待重新派生（Phase F.7）
- v3 docs-next 重写本轮进行中

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella import
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — Lift/Project + R0..R8 abbrevs
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — R₇ + 印 (yin)
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — R₈ + 投 (tou) + Shi V₄
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — R8_complete bundle
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — Mian = R₄
- [`formal/SSBX/Foundation/Squaring/SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean) — self-similarity v1.1 closure
- [`formal/SSBX/Foundation/Squaring/V4Tensor.lean`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean) — R₈ V₄ partition + cell/operator anchors
- [`formal/SSBX/Foundation/Wen/ClassicalTextRHierarchyBridge.lean`](../../formal/SSBX/Foundation/Wen/ClassicalTextRHierarchyBridge.lean) — classical-language direct typed bridge
- [`formal/SSBX/Foundation/Modern/QuantumR8Bridge.lean`](../../formal/SSBX/Foundation/Modern/QuantumR8Bridge.lean) — Quantum/R₈ finite typed bridge
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["..."]` macro
- [`formal/SSBX/Foundation/Core/MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) — Face 12 inductive (并存于 Mian)
- [`formal/SSBX.lean`](../../formal/SSBX.lean) — 顶层 import 树
