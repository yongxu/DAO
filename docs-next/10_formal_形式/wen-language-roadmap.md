# Wen 语言栈 — 决策路线图

**状态**: 2026-05-17 · Yongxu Ren (v2 doctrine break 已交付)

## 现状（post-PR B' v2）

| 层 | 表面 | 实现 | 覆盖率 / 状态 |
|---|---|---|---|
| **Bagua-ISA** | 24-token 汇编 (v2: +「比阳」) | `wenyan` CLI + `BaguaTuring.YiInstr` (13 instr) | universal Hex → Hex (v2 doctrine break, 含 `branchYaoYang`) |
| **WenDef.Tm** | 类型化 lambda (Hex/Bool/Pair/List/Arr) | `WenDefEval` | 22 builtin + helper body 全套 |
| **WenSurface** | 文言级 prose | `wenyanCompile + theoremBackedSemanticsFor?` | **desugar 100%** (375/375, 形式见证 [Semantics.lean:1142-1153](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean#L1142)) |
| **Bridge WenSurface→ISA** | — | `wenyanCompileToYiInstr?` | ✓ universal Hex → Hex (v2, 含 `推`/`損` 等 non-equivariant) |

已落地的 4-步收顶进度：

| 修法 | 状态 |
|---|---|
| catalogue 改 desugar 表 | ✅ 100%（46 个学派关系算子 placeholder body — 是 domain caveat 不是 desugar gap） |
| Tm 立唯一 core，CoreForm/R8 折叠为 view | ❌ 未启 |
| Bagua-ISA 作 Tm 后端 | ✅ universal (v2, B' merged 2026-05-17) |
| 5 evaluator 收敛到 1 | ❌ 未启 |

## 待决策项

下面三个**仍需用户判定**才能进 PR，不属 single-turn agent 可单方面操作的范围。

---

### Slice C1 — 句末虚词 乎/矣/哉/兮

#### 价值

让文言**看起来像文言**而非函数链。当前文言 prose 形如 `推 之 一`、`凡 甲 同 甲 甲`，句末没有任何 modal flair；加上 4 个 final particle 后可写 `推 一 矣`、`凡 甲 同 甲 甲 哉`、`不知 乎` 等。

#### 实施成本

**Path A · 仅添 glyph alias**（~5 行）
- `formal/SSBX/Text/Glyph.lean` 加 `«矣1»`、`«乎1»`、`«哉1»`、`«兮1»` GlyphSense
- `formal/SSBX/Text/WenyanOperators/Forms.lean` 把 矣 加入 `S_14 (也)` 的 form 列表
- 结果：lex 识别这些字；但因 S_14 当前是 **prefix** fixity（不是 postfix），`推 一 矣` 仍**无法 parse**，只有 `矣 推 一` 可 parse —— 与古文相反
- 评价：**伪解决**。glyph 进入系统但 surface 用法不对

**Path B · 真 postfix 解析**（~250-350 LOC，~12 文件）
1. `WenSurface/Syntax.lean` — 加 `postfixSurfaceSyntaxEntriesForOperator` + 修 Pratt parser `parseSurfaceExprAux` 处理 `.postfix prec` 分支（当前只声明未实现，[Syntax.lean:49](../../formal/SSBX/Foundation/Wen/WenSurface/Syntax.lean#L49)）
2. 加 4 个新 OperatorId 构造子（S_21..S_24）：
   - `Text/WenyanOperators/Core.lean` — inductive 4 行
   - `Code.lean` / `Title.lean` / `Group.lean` / `Forms.lean` — 各 4 行
   - `Table.lean` — `allOperatorIds` 加 4 项
   - `Audit/S.lean` — `mem_S_21..mem_S_24` 4 个 theorem
   - `Audit.lean` — covered 列表更新
   - `OperatorSignatures.lean` — `catalogueSignatureShapeFor` 4 个 case
3. **更新 pinned length 定理**：
   - `theorem allOperatorIds.length = 371` → 375
   - `theorem theoremBackedOperatorIds.length = 371` → 375
   - 任何用字面 371 的地方（含 wenyan-operators.md 的 "371 × 256 = 95,776" 表述）
4. `Foundation/Wen/WenSurface/Semantics.lean` 加 4 个 `coreTheoremBackedSemanticsFor?` 入口 + 4 个 native_decide
5. `formal/SSBX/Text/OperatorCellMap.lean` — 4 × 256 = 1024 个新 cell-pair 入口

**Path C · 跳过**
- 保持现状。文言级 prose 已可表达大量含义；缺最末层 modal flair 是 surface beauty 损失，不阻塞 metatheory。

#### 风险

- Path B 改 `allOperatorIds.length = 371` 这一组定理 — 项目 v4 公示 v2.1 中明文 "371 算子" 是出版口径；改成 375 等于改公示数字
- Path B 需要 1-2 小时聚焦工作 + lake build 验证（cold cache ~30-60min）
- Path A 既无收益又增噪声

#### 推荐

**Path C（跳过）或 Path B（聚焦 PR）**。Path A 不推荐 — 半生不熟。

#### 触发条件

用户明确说："开 C1 Path B" → 我会规划成单独的 1-2 PR 序列（先加构造子 + 长度定理，再加 parser），每步独立 cold-build 验证。

---

### Slice B' — 扩 YiInstr 破 complement-equivariance ceiling **【已完成 v2 doctrine, 2026-05-17】**

#### 价值（已交付）

让 `wenyanCompileToYiInstr?` 成为 **universal compile** —— `推/损` 等 non-equivariant 项现可桥到 Bagua-ISA。后端目标 ISA 覆盖 WenDef.Tm 全 Hex → Hex 子集。

#### Doctrine 变更

**v1 doctrine 已破**: [`WenDefCompile.lean` 文件头](../../formal/SSBX/Foundation/Wen/WenDefCompile.lean#L1) 之「未尽之业」改为 §「v2 扩展」。详 before / after 对比表见 `BaguaTuring.lean` 之 § 8 与 `WenDefCompile.lean` 文件头之表。

`BaguaTuring.lean` 加第 13 条原语 `branchYaoYang (i : Fin 6) (target : Nat)` —— absolute yao test (若 yao i = yang, 跳 target). 此原语 **不与 complement 通约**, 故 doctrine 破之.

#### 已交付清单

1. ✅ `formal/SSBX/Foundation/Atlas/Yi/Classical/Computation/BaguaTuring.lean` 加 `branchYaoYang` + `complementEquivariantInstr` predicate + 12 v1 原语 之 equivariant 见证 + branchYaoYang 之 non-equivariant 反例
2. ✅ 12 v1 原语的"与 complement 通约"定理: 由全集事实改为子集事实, guard 为 `complementEquivariantProg` (子集 program). `halts_cuo_invariant` 加 `AllEquivariant P` hypothesis. `cuoState_step_equivariant` 加 instr-level equivariance guard.
3. ✅ `WenDefCompile.lean` 之 `compileHexFunCertified?` 扩 pattern: `.tuiBody` (mod-64 +1) 与 `.sunBody` (mod-64 -1) 经 propagate-carry/borrow adder (27 instr) 现可 compile
4. ✅ 64-Hex `compiledHexFunAgrees` 复用 (native_decide 见证)
5. ✅ **narrative 改完**：本文件之 § B' 章节 + `wen-substrate/03-operation-monism.md` 之 cuo-equivariance ceiling 段 + `WenDefCompile.lean` 文件头之 v2 doctrine 文档

#### 风险（mitigated）

- ✅ doctrine 改之 — 由 `complementEquivariantInstr` 谓词 + `AllEquivariant` 子集事实双重 guard 平滑迁移
- ✅ MetaInterp 之 universalMetaInterp dispatch: `branchYaoYang` 暂 route 到 `haltTag` slot (placeholder, 见 Dispatch.lean v2 注). 完整 self-interp 之 13 instr support 留作 follow-up
- ✅ Atlas/Yi 多处 narrative：通过 `complementEquivariantInstr` predicate 显式表达 v1 子集事实

#### 实现 highlights

**Propagate-carry adder 算法** (`tui` = +1 mod 64):
- bit 0 (y1, LSB) 起 propagate carry 向 bit 5 (y6, MSB)
- 每 level 5 instructions: `branchYaoYang i (P+3); flipYao i; jump next; flipYao i; halt`
- yang case (bit = 0): jump P+3, flip bit (now 1), halt
- yin case (bit = 1): flip bit (now 0), jump next level (carry up)
- 终层 y6 (MSB) 简化: `flipYao 5; halt` (mod-64 之 overflow 自然丢弃)
- Total: 5 × 5 + 2 = 27 instructions (含 wrapper appended halt)

`sun` (mod-64 -1) 算法 dual: bit yin → flip + halt; bit yang → flip + borrow propagate.

---

## "做完"的现实读法

A1 / B 已合并主线。C1 / B' 待明确授权。

若用户答 "全部跳过": 当前主线就是「Wen 1.0」可发布状态 —— desugar 100%, 错等变桥已证, 7+8 prose 样本上链。

若用户答 "执 C1 Path B": 会开 2-3 PR 序列（构造子 + 长度定理 + parser），耗时 1-2 工作日。

若用户答 "执 B'": 先改 doctrine narrative（v4-foundation.md 等），再扩 ISA，再扩 compile —— 3-4 工作日 + 重证若干形式 invariant。

---

**相关文件**

- [`samples/README.md`](../../formal/SSBX/Foundation/Wen/samples/README.md) — 双层 sample 总览
- [`Wen/WenSurface/Semantics.lean`](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean) — desugar 表 + length theorems
- [`Wen/WenDefCompile.lean`](../../formal/SSBX/Foundation/Wen/WenDefCompile.lean) — Bagua-ISA 桥 + 错等变 doctrine
- [`Wen/WenSurface/ISABridge.lean`](../../formal/SSBX/Foundation/Wen/WenSurface/ISABridge.lean) — String→YiInstr 端到端
- [`Wen/WenSurface/ProseSample.lean`](../../formal/SSBX/Foundation/Wen/WenSurface/ProseSample.lean) — 7-行文言 round-trip
