# Phase Status — main @ 687eac1 (2026-05-10)

> 状态：本文件是 main 的"现在长什么样"快照，给未来读者作 ground truth。
> 任何 commit 信息或文档与本文不一致时，**以代码为准、以本文为辅**。
> 配套：[research-position.md](research-position.md)（学术 positioning）、[root-layer-map.md](../10_formal_形式/root-layer-map.md)（结构定义）。

---

## 1. 当前 main 是什么状态

```
main = origin/main = 687eac1 (P6 downstream alignment)
最近 commits:
  687eac1 P6: downstream alignment
  9dd29ed Merge claude/pensive-meitner-c79a1f — MetaInterp Phase 2.3 + wenyan CLI
  44c78cc merge: brahmagupta P5/P5b
  0b07636 P5b: delete Face inductive (later partially reverted by 687eac1)
  6ab4c61 docs: add yi-as-meta-framework.md
  172487c formal: BenZheng (alternate version)
  b892756 docs: add research-position.md
  087f288 formal: 4本/4征 layer-character map + LayerCharacterMap.lean
```

**Build**：`lake build` 整体通过（1683 jobs）。

**两份 wenyan exe 双 CLI**：
- `wenyan-surface` (1949 行，speaks WenSurface 文言)
- `wenyan` (speaks baguaWen 22-token IL)

---

## 2. 实际并存的两套 ontology

main 的**重要事实**：经过 P5b → P6 折腾后，**Face 12-枚举 与 BenZheng 4×4 并存**，不是替代关系。

### 2.1 Face（M-line / 名册线）—— **存在**

[`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 中：

```lean
inductive Face where
  | «文面» | «物面» | «生面» | «理面» | «心面» | «人面»
  | «模面» | «审校面» | «价值面» | «证明面» | «注意面» | «真理面»
```

加上 `atomPrimaryFace : AtomName → Face`、`atomExtraFaces`、`allFaces`、`all_faces_complete` 等——**全套都在**。

**用途**：
- AtomName roster 的"领域归属" projection
- 333 个登记字到 12 个 Face 的多对一映射
- 给 AtomName 一个 categorical 分类底盘

### 2.2 BenZheng（Trigram-level algebraic core）—— **存在**

[`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) 中：

```lean
inductive Ben : Type | wu | dong | jian | shi      -- 4 substrates
inductive Zheng : Type | jiFaint | shiForce        -- 4 marks
                       | jiOccasion | shiTime
abbrev Mian : Type := Ben × Zheng                    -- = 16
inductive Quadrant | benBen | benZheng | zhengBen | zhengZheng
```

加上 zong-orbit 分解、cuo/zong/hu 在 Quadrant 上的 invariants、isZongFixed/isZongMobile 谓词等。

**用途**：
- Trigram-level (Z/2)³ 群的 Z/2-quotient
- 64 卦的 4-quadrant 分类
- 形式逻辑 4-phase 解读

### 2.3 为什么并存（不冲突）

它们**不在同一层**：

| 维度 | Face | BenZheng / Mian |
|---|---|---|
| 形式锚 | M-line 的 M1 层 | R3 trigram 的代数 substructure |
| 作用 | 把 333 atom 分类到 12 domain | 把 8 trigram 分成 4+4 |
| Lean type | `inductive Face` (12 constructors) | `Ben × Zheng = 16` |
| 服务对象 | AtomName 注册系统 | trigram / hexagram 算子代数 |

P5b 试图用 Mian (16) **完全替代** Face (12)——但导致下游 atom 系统大改，所以 P6 (687eac1) **保留了 Face 的全套 API**，让 Mian 作为 trigram-level 增强。

---

## 3. Plan P1-P8 的实际完成状态

参考 [.claude/plans/...md](../../.claude/plans/docs-next-10-formal-root-layer-map-md-c-ticklish-sun.md):

| 阶段 | 计划内容 | 实际状态 |
|---|---|---|
| **P1** | BenZheng.lean: 4本/4征 + zong-orbit invariants | ✅ 完成 (172487c, 73c94a3) |
| **P2** | HexQuadrant + cuo/zong/hu/flip invariants | ✅ 完成 (172487c) |
| **P3** | LayerCharacterMap 加 Rh 层 + 16-grid table | ✅ 完成 (087f288 + P6) |
| **P4** | Yi.JianMode 加 displayChar 投影 | ⚠️ 部分（character roundtrip 已证，但 JianMode-displayChar 接口未完整） |
| **P5** | Roster 加 ~16 缺字 + MonadRoot 接 Face | ✅ 完成（保留了 Face）|
| **P5b** | Fully delete Face inductive（试） | ⚠️ **Partially reverted by P6**——Face 在 main 中仍存在 |
| **P6** | JianOntology 重写主体 + Legacy 拆分 | ✅ 完成（JianOntology 作为 legacy 3-元 surface 存在） |
| **P7** | JianModeKernel / JianYiBridge 修小处 | 📝 未开始 |
| **P8** | docs 更新代码锚点 | ⚠️ 部分（layer-character-map 等已写，root-layer-map 等老 doc 未审查）|

---

## 4. 已确立的事实（可作 ground truth）

### 4.1 代数事实（数学层）

- 8 trigram = (Z/2)³，**zong-orbit 分解 = 4 palindromic + 4 non-palindromic**——这是结构必然，不是设计选择
- 64 hexagram = 4 quadrant × 16，**cuo 永远象限内，zong swap 本征↔征本，hu 4-attractor 全在本本**
- 这些都有 `native_decide` 可证的 Lean theorem (在 [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean))

### 4.2 命名事实（surface 层）

[`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) 已 register：

| 层 | 字根 | 状态 |
|---|---|---|
| R1 | 实/虚 (Yao essence) | ✅ build pass |
| R2 | 春/夏/秋/冬 (SiXiang season) | ✅ |
| R3 | 健/悦/显/起/入/险/止/顺 (trigram virtue) | ✅ |
| R3 | 乾/兑/离/震/巽/坎/艮/坤 (trigram literal) | ✅ |
| R4 | 改/化/变/临/主/极 (6-yao flip) | ✅ |
| R5 | 迁/溯 (shi transition) | ✅ |
| L0 | 静/置/翻/互/错/综/侔/会/跳/推/取/终 | ✅ |
| 全表 | `allLayerChars` 42 entries | ✅ |

### 4.3 文档已落地

| 文件 | 内容 |
|---|---|
| [`docs-next/10_formal_形式/root-layer-map.md`](../10_formal_形式/root-layer-map.md) | 三轴结构定义 |
| [`layer-character-map.md`](../10_formal_形式/layer-character-map.md) | R0-L0 字根映射详细 |
| [`layer-axis-graph.md`](../10_formal_形式/layer-axis-graph.md) | 三轴汇聚 Mermaid |
| [`sanben-sijieduan-grid.md`](../10_formal_形式/sanben-sijieduan-grid.md) | 12-grid (3×4) |
| [`64-hexagram-grid.md`](../10_formal_形式/64-hexagram-grid.md) | 64 卦 4-quadrant 分类 + 算子 invariants |
| [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) | 易代数定理框架 |
| [`yi-as-meta-framework.md`](../10_formal_形式/yi-as-meta-framework.md) | self-description GUT 解读 |
| [`research-position.md`](research-position.md) | 学术 positioning（已立 vs novel）|

---

## 5. 已知不一致 / 需注意的点

### 5.1 commit 687eac1 message 与代码不符

`687eac1` 的 commit message 写："Face 12-enum gone" —— 但实际 diff 把 Face 加了回来。**实际状态以代码为准**，commit message 表述不准确。

补正：本 phase-status.md 是当前 main 状态的**正式 narrative**。如阅读 git log 时遇到 P5b/P6 commit message 的"Face gone"表述，请以本文记载的 "Face 与 BenZheng 并存" 为准。

### 5.2 root-layer-map.md 的旧 12-Face 列表

[`root-layer-map.md`](../10_formal_形式/root-layer-map.md) §3.1 仍列出 12 Face 名（文面/物面/生面/...）——**这是正确的、与现状一致**。Face 在代码中确实有，所以这个列表不需要改。但顶部的 status block 提到的"6 处 default 字变更"是早期 P3 时的 character map 工作，不涉及 Face 删除。

### 5.3 P5b 的 commit message 仍说"fully delete Face"

历史性的：commit 0b07636 当时确实删了 Face；后续 687eac1 又加回来了。**git log 阅读时这一点要在意**。

---

## 6. 下一阶段（如果继续）

### 6.1 必要 cleanup

- [ ] P5b commit message 与最终代码不符——可考虑加一个明确"P5b 部分回滚"的 commit message clarification（不是 force-push，而是新 commit 加注释）
- [ ] P7：JianModeKernel / JianYiBridge 小处（小工作，可单 commit）
- [ ] P8：审查所有老 doc 的代码锚点是否还指向有效路径

### 6.2 可选扩展

- [ ] Lean 化"4 mark = phase-space 4 quadrant"（[research-position.md §4.2](research-position.md)，需要 ℝ 嵌入框架）
- [ ] Lean 化"积分/微分对应"（[research-position.md §4.3](research-position.md)）
- [ ] Lean 化"hu attractors = 4 truth values"（[research-position.md §4.6](research-position.md)）

### 6.3 不在范围（按用户指示）

- [ ] codex/* 7 个分支不动
- [ ] claude/sad-edison-12179e 已 obsolete

---

## 7. 给后来读者：怎么验证当前状态

```bash
# 1. 确认 build pass
lake build           # 应该 1683 jobs success
lake build wenyan-surface  # WenSurface CLI
lake build wenyan          # baguaWen CLI

# 2. 确认 BenZheng + Face 并存
grep -c "inductive Face\b" formal/SSBX/Foundation/Core/MonadRoot.lean   # = 1
grep -c "inductive Ben\b" formal/SSBX/Foundation/Bagua/BenZheng.lean   # = 1

# 3. 确认 LayerCharacterMap 全 build
lake build SSBX.Text.LayerCharacterMap

# 4. 字根映射查 spot-check
# (跑 wenyan / wenyan-surface 给样本输入)
```

---

## 8. 一行总结

**main @ 687eac1 是 P5+P6 的稳定收口点：**
- 代数核心（4本/4征/16-Mian/4-Quadrant）✓ 与名册线（12-Face）并存
- 64 卦 algebra invariants ✓
- 字根全表 ✓
- 双 CLI ✓
- 8 个文档已落地 ✓
- P7/P8 留作下一阶段
