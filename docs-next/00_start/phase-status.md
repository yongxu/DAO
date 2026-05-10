# Phase Status — main @ 1c76a55 (2026-05-11)

> 状态：本文件是 main 的"现在长什么样"快照，给未来读者作 ground truth。
> 任何 commit 信息或文档与本文不一致时，**以代码为准、以本文为辅**。
> 配套：[final-theory.md](final-theory.md)（v3 速览）、[research-position.md](research-position.md)（学术 positioning）、[`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md)（R₀..R₈ definitive spec）。

---

## 1. 当前 main 是什么状态

```
main = origin/main = 1c76a55 (Phase C: R-index aliases + RHierarchy umbrella)
最近 commits:
  1c76a55 Phase C: R₀..R₈ index-named alias files + RHierarchy umbrella
  8e4406e Phase F.6 + G + B.1: cleanup + doc sync + YinBit dedup
  0003224 Phase F.x.5: complete Cell192 → Cell256 migration in Modern/* cascades
  7de5064 Phase A-F: doctrine alignment — Cell192 → Cell256 (V₄ Shi)
  e4c07a4 docs: add phase-status.md — record actual state of main @ 687eac1
  687eac1 P6: downstream alignment — BenZheng (4本/4征) becomes primary
  9dd29ed Merge claude/pensive-meitner-c79a1f — MetaInterp Phase 2.3 + wenyan CLI
  44c78cc merge: pull main; keep HEAD BenZheng
  0b07636 P5b: delete Face inductive (later partially reverted by 687eac1)
```

**Build**：`lake build SSBX` 通过 **3656 jobs**, 0 errors, 0 sorry, axiom audit = `{propext, native_decide}`（无项目自定义 axiom）。

**两份 wenyan exe 双 CLI**（与 687eac1 同）：
- `wenyan-surface` (1949 行，speaks WenSurface 文言)
- `wenyan` (speaks baguaWen 22-token IL)

---

## 2. v3 定本结构 (Cell256 / V₄ Shi / R₀..R₈ uniform)

### 2.1 R₀..R₈ 严格 (Z/2)ⁿ uniform

```
R₀ Taiji      = Unit                           |·| = 1
R₁ Yao        = Bool                           |·| = 2     = (Z/2)¹
R₂ SiXiang    = Yao²                           |·| = 4     = (Z/2)²
R₃ Trigram    = Yao³                           |·| = 8     = (Z/2)³
R₄ Mian       = Ben × Zheng                    |·| = 16    = (Z/2)⁴
R₅ Wuyao      = Mian × Bool   (provisional)    |·| = 32    = (Z/2)⁵
R₆ Hexagram   = Yao⁶                           |·| = 64    = (Z/2)⁶
R₇ YinHex     = Hexagram × YinBit (Cell128)    |·| = 128   = (Z/2)⁷
R₈ GuoHex     = Hexagram × Shi    (Cell256)    |·| = 256   = (Z/2)⁸
```

每行 size = 2^(R-index)，每行恰好比上行多一 binary axis。**no jumps, no gaps**。

### 2.2 Shi V₄ Klein 在 R₈ emerge

`Shi = {道, 已, 今, 未}` ≅ `YinBit × GuoBit` ≅ V₄ = (Z/2)²：

| Shi | (因, 果) | V₄ 元 |
|---|---|---|
| 道 | (0, 0) | identity |
| 已 | (1, 0) | $\sigma_P$ |
| 未 | (0, 1) | $\sigma_T$ |
| 今 | (1, 1) | $\sigma_{PT}$ |

**道 = (0, 0) = V₄ identity = (Z/2)⁸ origin = no-op operator = 永真 cell**（一字承担五重身份）。`oooooooo` 字符串就是道。

### 2.3 BenZheng (R₃/R₄/R₆) 与 Face (M-line) 仍并存

R₃ 之 zong-fixed partition (4 本 + 4 征) 与 BenZheng quadrant (R₆ 4 quadrant × 16) 是数学事实, 已 native_decide 证。
- [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — `Ben/Zheng/Mian/Quadrant`，Mian = R₄ first-class (16)
- [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) — `Face` inductive (12 ctors) **仍在**，作 atom 名册线（与 BenZheng 不同层）

P5b 试图删 Face / P6 保留 Face 的并存关系自 687eac1 起未变。详 §6.

---

## 3. v3 升级 — 4 个 phase 的实际完成状态

### 3.1 Phase A–F (commit `7de5064`, 2026-05-10) — 教义对齐 / Cell192 → Cell256

| 子 phase | 内容 | 状态 |
|---|---|---|
| **A** | Algebraic spine: Cell128/Cell256 carry Add/Zero/Neg/Sub/SMul + Cayley `ι/ε` | ✅ |
| **B** | Cell128 `YinBit := Bool` + `yin` toggle (R₇ 中间层); Cell256 `Shi` inductive + `Shi.toYinGuo` 双射 + `tou` toggle (R₈ 闭合层) | ✅ |
| **C** | XOR-mask atomics: 印 (yin), 投 (tou), flip1..6, hexCuo/hexZong/hexHu, shiCuo/shiZong/shiCuoZong | ✅ |
| **D** | V₄ Shi (取代 Z/3 cyclic): Z/3 `shiNext +1` 全部移除；新 `Shi.cuo / .zong / .cuoZong` involutions | ✅ |
| **E** | `R8_complete` bundle theorem (replaces `R7_complete`); R-hierarchy abbrevs in Cell256Stratify | ✅ |
| **F** | 上层文档第一轮 sync (yi-RO-hierarchy v2.1 + yi-calculus-theorem K-theorem); cell192 stratify removed | ✅ |

### 3.2 Phase F.x.5 (commit `0003224`, 2026-05-10) — Modern/* cascades

完成 Cell192 → Cell256 之 ~80 文件下游级联：
- BaguaTuring: `YiInstr.setShi` 增加 `Shi.dao`
- DaoSource.lean: 道源程在 Shi=道 状态语义 review
- GodelLi.lean: Halts 谓词 + Rice 不变
- MetaInterp/*: Shi case-split 全 4 例
- OperatorCellMap.lean: 192 → 256
- Modern/* directories: case-split 全 4 例升级

**Verified**: 0 sorry added, build 通过。

### 3.3 Phase F.6 + G + B.1 (commit `8e4406e`, 2026-05-10) — cleanup + doc sync + YinBit dedup

**F.6 — Cell192 物理删除**:
- `Cell192.lean` 文件**从树中删除**
- `SSBX.lean` 移除 import line
- Build 从 3648 → 3647 jobs（恰减 1 文件）

**G — 4 份文档与 Lean 路径 sync**:
- `yi-RO-hierarchy-v2.md` (now v2.1): 新 §9.4 Lean implementation map
- `yi-calculus-theorem.md`: Theorems A–K 表加「Lean 文件」列；§15.1 R₀..R₈ status；§15.2 banner update
- `yi-as-meta-framework.md`: §4.1 R-hierarchy 表加 Lean 列 + Hierarchy/ + Notation/ pointers
- `formal/SSBX/README.md`: foundation tree 更新 Hierarchy/, Notation/, Cell128/256, BenZheng

**B.1 — YinBit dedup**:
- 移除 Cell256.lean 中重复 `abbrev YinBit := Bool`
- canonical now lives in `Cell128.lean` (R₇ origin)
- Cell256 imports + opens Cell128 (YinBit)

**Verified**: lake build SSBX 3647/3647, 0 errors, 0 sorry added。

### 3.4 Phase C (commit `1c76a55`, 2026-05-11) — R-index 命名 alias 文件 + RHierarchy umbrella

新 9 个文件 in `Foundation/Hierarchy/` 提供 R-index 命名导航：

| 文件 | 角色 |
|---|---|
| `R0_Taiji.lean` | Unit wrapper (Taiji = ()) |
| `R1_Yao.lean` | Yao re-export from Yi/Yi.lean |
| `R2_SiXiang.lean` | SiXiang re-export from Bagua/BaguaAlgebra.lean |
| `R3_Trigram.lean` | Trigram re-export from Yi/Yi.lean |
| `R4_Mian.lean` | Mian re-export from Bagua/BenZheng.lean |
| `R6_Hexagram.lean` | Hexagram re-export from Yi/Yi.lean |
| `R7_YinHex.lean` | Cell128 + atomic-ops re-export |
| `R8_GuoHex.lean` | Cell256 + Shi + cayley + XOR-mask ops re-export |
| `RHierarchy.lean` | **umbrella entry**: imports R0..R8 + LiftProject + Operators |

(R₅ `R5_Wuyao.lean` 在 Phase A-F 已建立。)

**Backward compat**: 原 cardinality-named 文件 (`Cell128.lean`, `Cell256.lean`) 保持不变并行存在，新 alias 仅是 thin re-export shim, 无新逻辑。

`SSBX.lean`: 一行新增 `import SSBX.Foundation.Hierarchy.RHierarchy`（pulls in R0..R8 transitively）。

**Verified**: lake build SSBX 3656/3656 jobs (3647 + 9 新 alias)。0 errors, 0 sorry added。`R8_complete` axiom audit 不变 = `{propext, native_decide}`。

---

## 4. 已确立的事实（可作 ground truth）

### 4.1 代数事实（数学层）— v3 升级完整

- **R₀..R₈ 全 (Z/2)ⁿ closure**: `R8_complete` bundle in [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean), 仅依赖 propext + native_decide。
- **Shi V₄ Klein 同构**: `Shi.toYinGuo : Shi → YinBit × GuoBit` is bijection。`道 = (false, false) = V₄ identity` 已证。
- **Cayley action on (Z/2)⁸**: `cayley : Cell256 → Cell256 → Cell256` 等价 XOR (in Algebraic spine). 同态/单射雏形已铺。
- **Lift / Project (8 layers)**: `proj_lift_id_Rn` retract lemma 全部证 in [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)。
- **|Cell256| = 256**: `Cell256.all_length = 256` via native_decide。
- **R₃ zong-fixed partition (4+4)**: 不变 (BenZheng.lean)。
- **R₆ 4 quadrant × 16**: 不变 (BenZheng.lean)。

### 4.2 命名事实（surface 层）

[`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) 已 register（不变 from 687eac1）：

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
| [`docs-next/00_start/final-theory.md`](final-theory.md) | **v3 速览** (本 phase 新增) |
| [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) | **v2.1 R-O 双层级 definitive** (R₀..R₈ strict uniform + §9.4 Lean map) |
| [`docs-next/10_formal_形式/yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) | **Theorems A–K 完整稿** (R₀..R₈ + Shi V₄, 含 Lean 文件列) |
| [`docs-next/10_formal_形式/yi-as-meta-framework.md`](../10_formal_形式/yi-as-meta-framework.md) | **self-description GUT** (含 R₀..R₈ Lean 列) |
| [`docs-next/10_formal_形式/root-layer-map.md`](../10_formal_形式/root-layer-map.md) | 三轴结构定义 |
| [`layer-character-map.md`](../10_formal_形式/layer-character-map.md) | R0-L0 字根映射详细 |
| [`layer-axis-graph.md`](../10_formal_形式/layer-axis-graph.md) | 三轴汇聚 Mermaid |
| [`sanben-sijieduan-grid.md`](../10_formal_形式/sanben-sijieduan-grid.md) | 12-grid (3×4) |
| [`64-hexagram-grid.md`](../10_formal_形式/64-hexagram-grid.md) | 64 卦 4-quadrant 分类 + 算子 invariants |
| [`research-position.md`](research-position.md) | 学术 positioning（含 v3 novelty claims）|

### 4.4 形式锚 highlights (post-v3)

| 模块 | 文件 | 关键定理 / 元素 | 状态 |
|---|---|---|---|
| R₀ Taiji | [`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) | `Unit` wrapper | ✅ |
| R₁ Yao | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean), [`R1_Yao.lean`](../../formal/SSBX/Foundation/Hierarchy/R1_Yao.lean) | `Yao.neg_neg` | ✅ |
| R₂/R₃ + V₄ | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean), [`R2_SiXiang.lean`](../../formal/SSBX/Foundation/Hierarchy/R2_SiXiang.lean), [`R3_Trigram.lean`](../../formal/SSBX/Foundation/Hierarchy/R3_Trigram.lean) | `cuo_eq_compose`, `bagua_intercommunication` | ✅ |
| R₃ substrate–mark | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | `ben_count = 4`, `zheng_count = 4`, `cuo_preserves_isZongFixed` | ✅ |
| R₄ Mian (16) | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean), [`R4_Mian.lean`](../../formal/SSBX/Foundation/Hierarchy/R4_Mian.lean) | `Mian = Ben × Zheng`, `Mian.all.length = 16` | ✅ |
| R₅ Wuyao (32) | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | `Wuyao = Mian × Bool`, `flip5` involution, lift/project | ✅ |
| R₆ Hexagram + quadrant | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean), [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean), [`R6_Hexagram.lean`](../../formal/SSBX/Foundation/Hierarchy/R6_Hexagram.lean) | `quadrant_partition_complete`, `zong_quadrant` | ✅ |
| R₇ Cell128 + 因 | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean), [`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) | `Cell128 = Hexagram × YinBit`, `yin` toggle | ✅ |
| R₈ Cell256 + 果 + Shi V₄ | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean), [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean), [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) | `Shi.toYinGuo` 双射, `R8_complete` bundle, `cayley` Cayley action | ✅ |
| Atomic / V₄-outer | [`Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean), [`Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | XOR-subgroup re-export + zong/hu/cuoZong | ✅ |
| Lift / Project | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | 8 R-layer pairs + `proj_lift_id_Rn` retract | ✅ |
| OX 8-char macro | [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) | `OX["xxxxxxxx"]` → Cell256 | ✅ |
| Self-description witness | [`SelfDescription.lean`](../../formal/SSBX/Truth/SelfDescription.lean) | `Cell256OperatorComplete` (V₄ 升级版) | ✅ |
| Umbrella | [`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) | 9 R-layer + Lift/Project + Operators 一行入口 | ✅ |

---

## 5. 已知不一致 / 需注意的点

### 5.1 旧 phase-status (e4c07a4) 已被本文取代

旧 phase-status.md 记录 main @ 687eac1 时的 P5/P6 状态；本文记录 main @ 1c76a55 = P5/P6 + Phase A-F + F.x.5 + F.6/G/B.1 + Phase C 之全部叠加状态。两者**不冲突**——本文是叠加之后的最新 narrative。

### 5.2 历史更正条目（如阅读老文档遇到）

| 旧表述 (legacy, 已删) | 现表述 (v3 定本) | 备注 |
|---|---|---|
| `Cell192.lean` (R₆ 闭合) | **不存在** (deleted in `8e4406e`) | 物理删除 |
| Z/3 Shi cyclic {已, 今, 未} | V₄ Klein {道, 已, 今, 未} | 4 元 Klein 含 identity (道) |
| `shiNext : Shi → Shi` (Z/3 +1 cycle) | `Shi.cuo` / `.zong` / `.cuoZong` (V₄ involutions) | involutive, 非 cyclic |
| 192 = 64 × 3 | 256 = 64 × 4 | + 64 道-cells |
| 表六_192格全表.md | 表六_256格全表.md | 升级 64 × 4 + 因/果 标注 |
| `R7_complete` bundle | `R8_complete` bundle | (重号 + V₄ 升级) |
| R₁..R₆ 编号 (R₃→R₄ chong jump) | **R₀..R₈ strict uniform** (no jumps) | (重号 + R₀/R₄/R₅ 显式纳入) |
| chong = +3 bit jump | chong = 3-step composite (R₃→R₄→R₅→R₆ via Lift) | 不消失，显式认识为 3 步 +1 bit |

### 5.3 Cell192 commit messages（仅历史阅读）

如阅读 git log 时遇到旧 commits 提及 Cell192 / Z/3 Shi / shiNext, 这些表述在 `8e4406e` 起**已不再适用**。任何 doc 残留 Cell192 表述应视为 stale; 当前正确表述以本文与 [yi-RO-hierarchy.md v2.1](../10_formal_形式/yi-RO-hierarchy.md) 为准。

### 5.4 P5b 的 commit message 仍说"fully delete Face"

历史性的：commit 0b07636 当时确实删了 Face；后续 687eac1 又加回来了。Face 在 `MonadRoot.lean` 中**仍存在**至 main @ 1c76a55. **git log 阅读时这一点要在意**。Face 与 BenZheng 不在同一层（Face = M-line atom 名册线 12 ctors；BenZheng = R₃/R₄/R₆ 代数线）— 二者不冲突。

### 5.5 root-layer-map.md 的旧 R₁..R₆ 编号

[`root-layer-map.md`](../10_formal_形式/root-layer-map.md) 中可能仍出现 R₁..R₆ 旧编号。**新口径**: 以 [`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) v2.1 为 definitive — R₀..R₈ strict uniform, R₆ = Hexagram (旧 R₄), R₇ = Cell128 (旧 R₅), R₈ = Cell256 (旧 R₆)。后续维护应在 root-layer-map.md 之 §1 顶部标注重号 mapping（详见 §6 待办）。

---

## 6. 下一阶段（如果继续）

### 6.1 必要 cleanup

- [ ] [`root-layer-map.md`](../10_formal_形式/root-layer-map.md) 顶部加 v1 → v2.1 重号 mapping (R₁..R₆ → R₀..R₈ + Mian/五爻 显式纳入)
- [ ] 旧 `Cell192` / `shiNext` 残留之 doc lint pass（任何 docs/ 与 _generated/ 中残留表述）
- [ ] 表六_192格全表.md → 表六_256格全表.md 升级（64 × 4 + 因/果 标注）
- [ ] Theorem G (连续 1D 标量场对应) 的 informal → formal 桥接探索

### 6.2 可选扩展

- [ ] R₅ Lean type final 选择 (`Mian × Bool` vs 独立 `Cell32`)
- [ ] Cayley `ι/ε` 双向 inverse 完整定理（Algebraic spine 已铺基础，需要补完 `R₈ ≅ XOR(R₈)` 同构定理）
- [ ] `R8_complete` 之逐项展开 + 11 项 within-closure 完整性详查（[yi-RO-hierarchy §6.2]）形式化
- [ ] 因/果/印/投 final naming vote (after 下游使用模式收口)
- [ ] R₉+ 是否存在 (无 candidate, 但 (Z/2)⁹ 数学存在; ontological role 待研究)

### 6.3 不在范围（按用户指示）

- [ ] codex/* 7 个分支不动
- [ ] claude/sad-edison-12179e 已 obsolete

---

## 7. 给后来读者：怎么验证当前状态

```bash
# 1. 确认 build pass
lake build SSBX           # 应该 3656 jobs success
lake build wenyan-surface
lake build wenyan

# 2. 确认 Cell192 已删除
test ! -e formal/SSBX/Foundation/Bagua/Cell192.lean   # 应该 0 (file absent)

# 3. 确认 Cell256 + V₄ Shi
grep -c "inductive Shi\b" formal/SSBX/Foundation/Bagua/Cell256.lean   # = 1
grep -c "Shi.toYinGuo" formal/SSBX/Foundation/Bagua/Cell256.lean      # ≥ 1

# 4. 确认 R-index alias files 全在
ls formal/SSBX/Foundation/Hierarchy/R{0,1,2,3,4,5,6,7,8}_*.lean   # 9 files

# 5. 确认 RHierarchy umbrella
ls formal/SSBX/Foundation/Hierarchy/RHierarchy.lean    # exists

# 6. 确认 OX notation
grep -c "OX\\[" formal/SSBX/Foundation/Notation/OXNotation.lean   # ≥ 1

# 7. 确认 R8_complete axiom audit
# 在 Lean: #print axioms R8_complete  → 应只有 propext + native_decide

# 8. 字根映射查 spot-check
lake build SSBX.Text.LayerCharacterMap
```

---

## 8. 一行总结

**main @ 1c76a55 是 v3 定本收口点：**
- R₀..R₈ 严格 (Z/2)ⁿ uniform 9 层闭合 ✓ (Hierarchy/ + RHierarchy umbrella)
- Cell256 = Hexagram × Shi 256-cell with V₄ Klein Shi ✓ (Cell256.lean + Cell256Stratify.lean)
- 道 = V₄ identity = (Z/2)⁸ origin = no-op = 永真 cell 五重身份 ✓
- Cell192 / Z/3 cyclic Shi 完全删除 ✓ (`8e4406e`)
- 上层文档（4 份）与 Lean 路径全 sync ✓
- `R8_complete` axiom audit = {propext + native_decide}，无项目自定义 axiom ✓
- 双 CLI ✓ (wenyan-surface + wenyan)
- BenZheng (4本/4征) ✓ 与 Face (M-line 12 ctors) 并存（与 687eac1 不变）
- 字根全表 ✓
- v3 定本三大 doctrine 文档（yi-RO-hierarchy v2.1 + yi-calculus-theorem A–K + yi-as-meta-framework）已落地
