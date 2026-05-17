# Wen 语言栈 — 决策路线图

**状态**: 2026-05-17 · Yongxu Ren

## 现状（post-PR #27/#28）

| 层 | 表面 | 实现 | 覆盖率 / 状态 |
|---|---|---|---|
| **Bagua-ISA** | 22-token 汇编 | `wenyan` CLI + `BaguaTuring.YiInstr` | 自封闭，complement-equivariant universal |
| **WenDef.Tm** | 类型化 lambda (Hex/Bool/Pair/List/Arr) | `WenDefEval` | 22 builtin + helper body 全套 |
| **WenSurface** | 文言级 prose | `wenyanCompile + theoremBackedSemanticsFor?` | **desugar 100%** (375/375, 形式见证 [Semantics.lean:1142-1153](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean#L1142)) |
| **Bridge WenSurface→ISA** | — | `wenyanCompileToYiInstr?` | ✓ Slice B (PR #27), complement-equivariant 子集 |

已落地的 4-步收顶进度：

| 修法 | 状态 |
|---|---|
| catalogue 改 desugar 表 | ✅ 100%（46 个学派关系算子 placeholder body — 是 domain caveat 不是 desugar gap） |
| Tm 立唯一 core，CoreForm/R8 折叠为 view | ❌ 未启 |
| Bagua-ISA 作 Tm 后端 | ✅ 错等变子集（PR #27） |
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

### Slice B' — 扩 YiInstr 破 complement-equivariance ceiling

#### 价值

让 `wenyanCompileToYiInstr?` 成为 **total compile** —— 不再有"推/损/生"等 non-equivariant 项被拒。后端目标 ISA 真正覆盖 WenDef.Tm 全 Hex→Hex 子集。

#### Doctrine collision

[`WenDefCompile.lean` 文件头](../../formal/SSBX/Foundation/Wen/WenDefCompile.lean#L1) 明文：

> **替代方案**：扩展 YiInstr 加 absolute yao test (`branchYaoYang i t`) 或加 hexLit-style 常量载入 — 此皆破 complement-symmetry，得任意 Hex → Hex compile 能力。**本文不行此路，留作 future work。**

亦即「错等变」是 ISA 的**结构性 invariant**，不是 oversight。破之相当于改 Path 丙 的 doctrine。

#### 实施成本

约 200-300 LOC + 重写：
1. `formal/SSBX/Foundation/Atlas/Yi/Classical/Computation/BaguaTuring.lean` 加新原语（如 `.branchYaoYang i target`）
2. 重证现有 12 原语的"与 complement 通约"定理 — **这些定理会失效**，必须删或重新陈述
3. `WenDefCompile.lean` 之 `compileHexFunCertified?` 扩 Tm 模式覆盖 `.tuiBody`、`.sunBody`、`.jia` 等
4. 64-Hex `compiledHexFunAgrees` 复用，但语义不变
5. **形式公示**：v4-foundation.md / wen-substrate.md 之 Path 丙 章节须改写

#### 风险

- 改 doctrine — 项目曾用 ★ 错等变作为「YiInstr 之代数边界」的招牌定理；破之等于改基础理论叙事
- 可能影响 MetaInterp 之 universalMetaInterp dispatch（69 instruction）— 增 instruction 后 dispatch 表扩
- wen-substrate.md / Atlas/Yi 多处 narrative 引用错等变 — 全要 review

#### 推荐

**先不做**。理由：

1. ISA 的错等变约束不仅是工程选择，是 doctrine —— 它把 ISA 标识为"代数封闭机器"而非"通用图灵机"
2. 真要 universal Tm→ISA compile，**更好的路线是不用 ISA 作后端**，而用 LLVM-style 多后端：保留 ISA 作 equivariant 子集的封闭目标，另加 native Lean 求值器作 universal 目标
3. WenDef.Tm 的 universal 求值已由 `WenDefEval.denoteHex / denoteBool` 提供 — universal compile 路径**已有**, 不需要破 ISA

#### 触发条件

只有当用户明确说："我要 ISA 是 universal 后端，错等变 ceiling 是 bug 不是 feature" → 才开 PR. 否则保持现状.

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
