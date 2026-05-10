# 六表参考 · Six-Tables Reference

> 状态：v3 定本 (2026-05-11)
> 父链：[`docs-next/40_reference_参考/`](./) · 上层导航见 [`docs-next/`](../)
> 配套：[`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) (R₀..R₈ definitive) · [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) · [`glossary.md`](glossary.md) · [`operators.md`](operators.md)

六表位于根目录 [`六表_实虚史真/`](../../六表_实虚史真/), 是实、虚、史、真和六十四卦 × Shi V₄ 的人工表格入口. docs-next 只提供读法和指针.

---

## § 1 表格入口 · Table index

| 表 | 路径 | 读法 |
|---|---|---|
| 表一 · 六征本表 | [`六表_实虚史真/表一_六征本表.md`](../../六表_实虚史真/表一_六征本表.md) | 六征基础表 (显隐 / 限许 / 实虚 三对); 项目分类骨架 |
| 表二 · 史维三态 | [`六表_实虚史真/表二_史维三态.md`](../../六表_实虚史真/表二_史维三态.md) | 史维三态 已 / 今 / 未 (实虚之时间投影) |
| 表三 · 实虚 modal 三态 | [`六表_实虚史真/表三_实虚modal三态.md`](../../六表_实虚史真/表三_实虚modal三态.md) | modal decomposition 实 / 虚 / 几 |
| 表四 · 真假认识三态 | [`六表_实虚史真/表四_真假认识三态.md`](../../六表_实虚史真/表四_真假认识三态.md) | 真 / 假 / 疑 (实虚之认识投影) |
| 表五 · 三轴 27 格 | [`六表_实虚史真/表五_三轴27格.md`](../../六表_实虚史真/表五_三轴27格.md) | modal × 史 × 真假 = 3 × 3 × 3 = 27 cells |
| **表六 · 256 格全表** | [`六表_实虚史真/表六_256格全表.md`](../../六表_实虚史真/表六_256格全表.md) | 64 卦 × **Shi V₄** = 256 格 (renamed from 表六_192格全表.md) |

---

## § 2 表六 · 64 卦 × Shi V₄ = 256 格

### 2.1 Cell256 表六 — current canonical (2026-05-11)

**文件**: [`六表_实虚史真/表六_256格全表.md`](../../六表_实虚史真/表六_256格全表.md) (renamed from `表六_192格全表.md`).

**结构**: 64 卦 (依《序卦》序) × **Shi V₄** = 4 时态 = **256 格**.

| Shi state | (因, 果) | V₄ element | 解读 |
|---|---|---|---|
| **道** (dào) | (0, 0) | identity | 永真 / 跨时空 / V₄ 单位元 |
| **已** (jǐ) | (1, 0) | σ_P | 有因无果 — 过去封闭 |
| **未** (wèi) | (0, 1) | σ_T | 无因有果 — 未来开放 |
| **今** (jīn) | (1, 1) | σ_PT | 因果俱在 — 现在 |

**形式锚**: [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256 := Hexagram × Shi`, |Cell256| = 64 × 4 = 256 (`Cell256.all_length`); `Cell256.all_nodup` (no duplicates); `cell256_summary` bundle.

### 2.2 历史更正 — Cell192 / Z/3 cyclic Shi (deprecated)

**Cell192 已废.** 旧 `表六_192格全表.md` 把 Shi 编为 Z/3 cyclic {已, 今, 未} (192 = 64 × 3), 丧失:
- V₄ Klein 单位元 (道 first-class anchor);
- (ℤ/2)ⁿ self-similar closure (R₈ = 256 = (ℤ/2)⁸);
- 与 8-bit ASCII cardinal 同构 (yi-calculus § Cor I.1 / Cor K.3).

正确路径 (definitive 2026-05-10/11): R₈ = Cell256 = Hexagram × **Shi V₄**, 道 = (因=0, 果=0) = V₄ identity = first-class 入本体. 详 [yi-calculus-theorem.md § 11–12 (Theorems I–J)](../10_formal_形式/yi-calculus-theorem.md). Cell192 / Z/3 Shi 仅作历史更正出现在文档中.

### 2.3 表六 中的 64 × 4 排列 · Reading 表六

每行一卦 (依《序卦》编号 1..64), 每列一 Shi state. 每格记单字 / 双字 cell name (e.g., 道乾 / 已乾 / 今乾 / 未乾 for hexagram 1 across the four Shi states). 道 列即每卦的 V₄-identity 永真 anchor.

由 Cell192 升级到 Cell256 之 cell-rename 路径:
- 旧 已·X / 今·X / 未·X 列保留语义;
- 新增 道·X 列 = 跨时空 anchor 列 (64 个 道-cells);
- 命名风格 (e.g., 道乾 / 已乾) 与 Cell256.lean 之 `(Hexagram, Shi.dao)` 等 1-1 对应.

---

## § 3 与形式层的关系 · Formal-layer alignment

六表不是 Lean 生成文件. 需要形式核对时, 优先查:

| 入口 | 用途 |
|---|---|
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | 表六 256 格的 Lean ground truth (`Cell256`, `Shi`, `xuGua`, `Cell256.all_length = 256`) |
| [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | R₇ 中间层 (Cell128 = Hexagram × YinBit, 128 = 64 × 2) |
| [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | (ℤ/2)³ + (ℤ/2)⁶ 与 V₄ 算子 (cuo / zong / hu) 在 Trigram / Hexagram 上 |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | 4 本 + 4 征 + 4 quadrant + Mian (R₄) — 表六之 hexagram quadrant 划分 |
| [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | R₀..R₈ stratification + `R8_complete` bundle |
| `../_generated/lean-index.md` | `Foundation/Bagua` cluster 索引 |
| `../_generated/diagram-index.md` | Position Operator Graph (与表六之 256 格交叉) |
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `xuGua` | 64-hexagram《序卦》King Wen 序的 Lean 实现 (依此排表六行) |
| `formal/SSBX/notes/zhouyi-position-operator-report.md` (legacy) | 旧 Cell192 时期的 position-operator notes; **以 Cell256 为准** |

---

## § 4 读法边界 · Reading boundaries

- 表格可作为义理分类和审计导航.
- 表格本身不等于 Lean theorem.
- 表六 256 格的覆盖口径要区分:
  1. **表格覆盖** (256 格人写) — 表六文件本身;
  2. **算子空间覆盖** ((ℤ/2)⁸ XOR + V₄ outer + Cayley) — Lean Cell256;
  3. **证明覆盖** (`Cell256.all_length`, `R8_complete` 等) — Lean theorems.
- 涉及不完备 / 可判定 / 对角化时, 应回到 BaguaTuring 与 GodelLi 相关模块.
- 涉及 R-hierarchy 重号 (R₁..R₆ 旧编号 → R₀..R₈ 新编号) 时优先查 [yi-RO-hierarchy.md](../10_formal_形式/yi-RO-hierarchy.md) 之 v1→v2.1 mapping.
- Shi 必为 V₄ Klein four-group, **不是** Z/3 cyclic. 见 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Shi` 与 yi-calculus § 12 Theorem J.

---

## § 5 表一/二/三/四/五 一致性核对 · Consistency check

各表应与 v3 (R₀..R₈ + Shi V₄) 一致, 无 Cell192 / Z/3 cyclic Shi 残留:

| 表 | 当前内容 | 与 v3 是否冲突? |
|---|---|---|
| 表一 · 六征本表 | 显隐 / 限许 / 实虚 三对; 与 R-hierarchy 正交 (六征是 doctrine 分类骨架, 不直接索引 Cell256). | ✓ 不冲突 (表一不引用 Cell192) |
| 表二 · 史维三态 | 已 / 今 / 未 三态; **史 = 实虚在时间维之投影**. 注: 这是 doctrine-level 三态, 与 Shi V₄ 之 4 元结构 emergence 在 R₈ 处对齐 (道 多于三态, 是 V₄ identity 之 first-class anchor — 详 §2.1). | ⚠ doctrine-level 三态保留; Shi V₄ 在 Lean / 表六中是 4 元 |
| 表三 · 实虚 modal 三态 | 实 / 虚 / 几 (互含); 法则 21. | ✓ 不冲突 |
| 表四 · 真假认识三态 | 真 / 假 / 疑; 注意 "虚 ≠ 假"、"玄 ≠ 疑" (modal/epistemic 正交). | ✓ 不冲突 |
| 表五 · 三轴 27 格 | modal × 史 × 真假 = 3 × 3 × 3 = 27 cells. | ✓ 不冲突 (27 格之史轴是 doctrine-level, 与 R₈ 之 V₄ Shi 不对应) |
| 表六 · 256 格全表 | 64 卦 × Shi V₄ = 256 格 (renamed from 表六_192格全表.md). | ✓ definitive (current page) |

**Doctrine-level 史 三态 vs algebraic Shi V₄**: 表二 / 表五 之 "史 = 已/今/未 三态" 是 doctrine-level 时间维 modal projection (沿用法则 21 / 24); R₈ 之 Shi V₄ = 4 元 ((因, 果) ∈ Bool²), 道 是 V₄ identity 跨时空 anchor. 二者在 R₈ 处自然 reconcile: 道 = 跨时空 anchor (无 causation flow 约束); 已/今/未 之 doctrine 三态对应 Shi V₄ 之 σ_P / σ_PT / σ_T 三个非 identity 元. 道 是 first-class 之第四元. 详 [yi-calculus § 12 Theorem J + § 14.3](../10_formal_形式/yi-calculus-theorem.md).

---

## § 6 更新规则 · Maintenance

若六表变动, 应重新生成 docs-next 索引并检查:

- `../_generated/markdown-index.md` 是否收录新路径.
- `../_generated/crossrefs.md` 是否出现新的 Lean path mention 或 symbol hit.
- [`../20_theory_义理/core-framework.md`](../20_theory_义理/core-framework.md) 与 [`../20_theory_义理/formal-and-proof.md`](../20_theory_义理/formal-and-proof.md) 是否需要调整摘要.
- 表六任何 Cell192 / Z/3 cyclic Shi 残留要清除 (definitive doctrine: Cell256 / V₄ Klein).
- 新增/重命名后, 同步本页 §1 入口表 + §3 形式锚映射.
