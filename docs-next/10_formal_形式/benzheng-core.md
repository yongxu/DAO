# BenZheng 新本体核心

> 状态：定本（2026-05-10）。Lean 端落地完成。

## 概览

把 (Z/2)³ 群 zong-orbit 的 4+4 划分作为 ontology basis，取代旧 3-本/3-显/3-征 placeholder 体系。

```
Ben  : 4 本 (substrates, palindromic) ↔ {qian, li, kan, kun}
       wu (物) / dong (動) / jian (間) / shi (事)

Zheng: 4 征 (marks, directional)      ↔ {xun, zhen, dui, gen}
       jiFaint (幾) / shiForce (勢) / jiOccasion (機) / shiTime (時)

Mian : abbrev := Ben × Zheng = 16 cells
       label: 动/行/化/流/萌/长/发/续/缘/通/会/系/兆/趋/变/史

Quadrant: 4 象限
       benBen / benZheng / zhengBen / zhengZheng

Virtue : 8 mode (was JianMode)
       displayChar: 健/顺/起/入/险/显/止/悦
```

## 核心文件

| 文件 | 作用 |
|---|---|
| [`Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | 新核心：Ben/Zheng/Mian/Quadrant + 全部 invariants |
| [`Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) | `Virtue` (8 mode) + `displayChar` |
| [`Foundation/Core/MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) | `atomPrimaryMian / atomExtraMians / atomMians` (Mian 作为新 primary) |
| [`Foundation/Wen/Kernel.lean`](../../formal/SSBX/Foundation/Wen/Kernel.lean) | `kernelDanZiMian` (27 字 Mian 映射) |
| [`Text/LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) | R1-L0 + Rh 全部 66 字 ground truth |
| [`Roster.lean`](../../formal/SSBX/Roster.lean) | 14 个新 AtomName: 健/悦/起/止/顺/改/化/迁/溯/萌/长/缘/兆/趋 |

## 核心定理 (全部 native_decide 通过)

### Trigram-level
- `cuo_preserves_isZongFixed`: 错卦保本/征
- `hua_preserves_isZongFixed`: 中爻翻转保本/征
- `dong_flips_isZongFixed`: 初爻翻转翻本/征
- `bian_flips_isZongFixed`: 上爻翻转翻本/征

### Hexagram-level (64 卦 4 象限)
- `benBen_count = 16`、`benZheng_count = 16`、`zhengBen_count = 16`、`zhengZheng_count = 16`
- `quadrant_partition_complete = 64`
- `cuo_preserves_quadrant`: 错卦永远在象限内
- `zong_quadrant`: 统一定理，本本/征征 自闭，本征↔征本 互换
- `huaInner_preserves_quadrant`、`huaOuter_preserves_quadrant`: 中爻 (y2/y5) 保象限
- `dongInner_flips_inner / bianInner_flips_inner / dongOuter_flips_outer / bianOuter_flips_outer`: 初/三/四/上爻跨象限

### hu attractors 全在本本
- `qian_quadrant = .benBen`, `kun_quadrant = .benBen`
- `jiji_quadrant = .benBen`, `weiji_quadrant = .benBen`
- `jiji_hu_eq_weiji`, `weiji_hu_eq_jiji` (2-cycle)

## 删除的 legacy

| 旧 | 状态 |
|---|---|
| `inductive Face` 12-枚举 | 仍存在 (作 backward-compat label, P5b 待清) |
| `JianMode` 8-枚举 | 已重命名为 `Virtue` |
| `Foundation/Jian/JianOntology.lean` | **整个文件已删** |
| `Core.lean` 中 OnticRoot/Manifestation/DynamicMark/StaticFace/Gate/EventResult/CompositeForm | **已删** |

## 已知后续 (P5b)

- 完全删除 `inductive Face` 12-枚举，改为 atomPrimaryMian 直接到 16-cell（不经 Face.toMian projection）
- 这要求每个 ~333 atom 的 Mian 坐标人工细化（粗到细：从 12 face 自然投影到 12 of 16，到选取最贴的细 cell）

## 验证

```bash
lake build SSBX.Foundation.Bagua.BenZheng    # 新核心 build
lake build SSBX.Foundation.Yi.Yi              # Virtue rename
lake build SSBX.Text.LayerCharacterMap        # 字根表
lake build SSBX.Foundation.Core.MonadRoot     # Mian 集成
lake build SSBX.Foundation.Wen.Kernel         # kernelDanZiMian
lake build SSBX                               # 全 repo (3639 jobs)
```

全部 ✓ as of 2026-05-10。

## 相关文档（在另一 worktree 有详细分析）

参考 `infallible-leakey-a7a603` worktree 中的：
- `docs-next/10_formal_形式/sanben-sijieduan-grid.md` (12-grid 详细分析)
- `docs-next/10_formal_形式/64-hexagram-grid.md` (64 卦 × 4 quadrant 全表)
- `docs-next/10_formal_形式/layer-axis-graph.md` (三轴汇聚图)
- `docs-next/10_formal_形式/layer-character-map.md` (R1-L0 字根映射)
