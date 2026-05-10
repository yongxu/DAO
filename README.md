# 生生不息 · SSBX

> 状态：v3 (2026-05-11) — strict (Z/2)ⁿ uniform R₀..R₈ 阶梯; V₄ Klein 时态在 R₈; Cell256 = 64 卦 × 4 时态; 道 = R₈ origin = identity = no-op = 永真 cell; 0 sorry / 0 项目自定 axiom on migrated files; lake build 3656/3656 jobs.

> 中文 · [English](./README.en.md) · [形式 / Formal](./README.formal.md)

「生生不息论」(*Shēngshēng-Bùxī*) 是一个把「易」作为 self-describing system 之 algebraic 核之 Lean 4 形式化项目: **R₀..R₈ strict (Z/2)ⁿ 阶梯 + V₄ Klein 时态在 R₈ + 道作为 origin choice + V₄ 外对称接口** — 8-bit 闭合 (256 cells) 内, 元 ≅ 算子 严格同构, abelian closure 内完整完备自洽自指; 上层接 (路径丙) 文之自编译自证 / (Modern) Mathlib 实数·测度·量子·范畴 桥, 与跨文明 / 跨学科 28+ 卷义理一一对应。

---

## 状态摘要 (2026-05-11)

```
版本 / 阶段        v3 final algebraic spine (post-Cell192 → Cell256 迁移)
HEAD              1c76a55  (claude/thirsty-merkle-f43218 worktree)
                  ↳ 4 commits ahead of origin/main
build target      lake build  →  3656 / 3656 jobs ✓
sorry count       0   (across migrated files)
project axioms    0   (kleene_recursion_axiom 已被 cuo-equivariance 内化)
opaque count      1   (theOne 仍是唯一 ontological seal, Foundation/Wen/Kernel.lean Layer 0)
partial def       1   (BaguaTuring.run, 执行级非终止边界, 不是额外 axiom)
trust base        Lean 4 v4.30.0-rc2 + Mathlib master HEAD
```

**核心结构变更 (v3 vs v2)**

| 项 | v2 (pre-2026-05-10) | v3 (定本) |
|---|---|---|
| 时态 Shi | Z/3 cyclic {ji, jin, wei} (3 元) | **V₄ Klein {道, 已, 今, 未} (4 元)** |
| 总格数 | Cell192 = 64 × 3 | **Cell256 = 64 × 4** |
| R-编号 | R₁..R₆ (含 R₃→R₄ 之 +3 bit chong jump) | **R₀..R₈ strict (Z/2)ⁿ uniform**, no jumps |
| 显式纳入 | Hexagram(64), Cell128(128), Cell192(192) | **太极 R₀, 面 R₄ Mian = Ben×Zheng (16), 五爻 R₅ (32)** 全部显式 |
| origin | 无 distinguished | **道 = (qian, dao) = `OX["oooooooo"]` = (Z/2)⁸ identity** |
| 算子代数 | 局部 cuo / zong / hu | **每层 (Z/2)ⁿ XOR 子群 + 印/投 mask + V₄ 外对称 + Cayley ι/ε 同构** |
| Cell192 | 主载体 | **完全删除 (Cell192.lean 不再存在)**, OperatorCellMap 已迁 |
| pending | — | WenyanSelfInterp re-dispatch (Tier 3 通用 quine 之最后 engineering 步) |

详细变更轨迹与 v1 → v2.1 → v3 重号映射, 见 [docs-next/10_formal_形式/yi-RO-hierarchy.md](./docs-next/10_formal_形式/yi-RO-hierarchy.md) 之第一节与附录 A; 旧版本 (Cell192 / Z/3 Shi / R₁..R₆) 已全部归档至 [`史/`](./史/README.md), 不再被入口索引。

---

## 目录导航

| 入口 | 用途 |
|---|---|
| [`docs-next/00_start/README.md`](./docs-next/00_start/README.md) | **第一站** — 全文档体系入口枢纽，含 reading-paths 与 doctrine 索引 |
| [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](./docs-next/10_formal_形式/yi-RO-hierarchy.md) | **canonical doctrine**: R₀..R₈ + Cayley + V₄ + 道 anchor 之完整推演 |
| [`docs-next/10_formal_形式/cell256-grid.md`](./docs-next/10_formal_形式/cell256-grid.md) | 256-cell ground (64 卦 × 4 时态), 取代旧 192-cell |
| [`docs-next/10_formal_形式/v4-shi.md`](./docs-next/10_formal_形式/v4-shi.md) | V₄ Klein Shi 之专论 (cuo / zong / cuoZong 三 involution 之 P/T/PT 物理对应) |
| [`docs-next/30_crosswalk_互证/`](./docs-next/30_crosswalk_互证/) | 跨学科 / 跨文明同形 crosswalk |
| [`docs-next/40_reference_参考/`](./docs-next/40_reference_参考/) | 术语 / API / 工具 reference |
| [`义理/README.md`](./义理/README.md) | 28+ 卷哲学义理 (A–Z + 八衍 + Markov桥 / 量子 / 范畴 / 共同体) |
| [`六表_实虚史真/`](./六表_实虚史真/) | 6 张基础结构表 (六征 / 史维 / modal / 真假 / 27 / **256-cell 全表**) |
| [`六表_实虚史真/表六_256格全表.md`](./六表_实虚史真/表六_256格全表.md) | **v3 新表**: 64 卦 × 4 时态 = 256 cells 全枚举 |
| [`史料/`](./史料/) | v9–v14 各代理论手稿; **可援引之研究档案**, 与 `史/` 不同 |
| [`史/`](./史/README.md) | **被 v3 严格取代**之文件 (Cell192 / Z/3 Shi / 旧 R-编号), 仅作只读归档 |
| [`AGENTS.md`](./AGENTS.md) | 多 agent 协作 / build / 并行约束 |
| [`README.formal.md`](./README.formal.md) | 形式层 spec (lake / 模块 / 定理 / trust base) |
| [`README.en.md`](./README.en.md) | English mirror |

---

## 构建与运行

```bash
# Lean 全库 (3656 jobs; 慢)
lake build SSBX

# 单模块
lake build +SSBX.Foundation.Bagua.Cell256
lake build +SSBX.Foundation.Hierarchy.RHierarchy

# 默认 smoke target
lake build

# WenSurface 受控文言 CLI (执行级)
lake build wenyan-surface
./.lake/build/bin/wenyan-surface '推 一'
./.lake/build/bin/wenyan-surface --json '同 一 一'
./.lake/build/bin/wenyan-surface --json --coverage
scripts/check_wenyan_surface_cli.py

# 字文 (ziwen) CLI (与 wenyan-surface 互补; 见 ziwen-spec.md)
lake build wenyan
./.lake/build/bin/wenyan --help
```

环境: `Lean v4.30.0-rc2` + `Mathlib master`. Apple Silicon (M-系列) / x86_64 通。Mathlib HEAD 较大, 首次拉取与冷 build 较慢, 后续增量 build 快。

`wenyan-surface` 是当前可执行的 WenSurface 子集入口: 支持 tokens / resolve / AST / typecheck / JSON / explain / operator catalogue 与 coverage inspect modes; 失败诊断返回非零 exit code; 全部 371 个 catalogue 算子可执行 (其中 38 行有 theorem-backed Hex/Bool denotation, 其余以 `Catalogue[...]` structural 正常形式输出, 不伪装成 Hex/Bool 结果)。

`wenyan` 是 ziwen / 字文 v0 入口 (源码 `Wenyan.lean` + `WenyanSurface.lean`); 规范见 [`ziwen-spec.md`](./ziwen-spec.md)。

---

## 代码骨架

```
formal/                            Lean 4 形式化 (lake 包名 = ssbx; @[default_target] = SSBXCore)
├─ SSBX.lean                       顶层 import index
└─ SSBX/
   ├─ Core / Roster / Pending      字根名册 + 核心生成项 + 待校接口
   ├─ Text/                        字 / 算子 catalogue (含 OperatorCellMap, OperatorAnchors)
   ├─ Truth / Model                模型论与真值边界
   └─ Foundation/                  9 簇 · 100+ modules
      ├─ Core                      字根 · 单根证书 · Alignment / Sincerity / Renlei
      ├─ Wen                       古文虚字 · 45 层 Kernel · 路径丙 11 模 · DaoSource / MetaInterp
      ├─ Jian                      间之核 (14 字粒子核; STLC + Mode + Yi 桥)
      ├─ Yi                        易之代数 · 微核「加 + 一」
      ├─ Bagua                     八卦 + Turing + Gödel-Rice + Cell128/256 + BenZheng
      ├─ Hierarchy                 R₀..R₈ index alias 体系 + LiftProject + Operators (Atomic/V4Outer)
      ├─ Notation                  OXNotation: `OX["oooooooo"]` 8-char Cell256 字面量 macro
      ├─ Eight                     八衍: 数 / 推 / 测 / 形 / 类 / 动 / 识 / 象
      └─ Modern                    Mathlib 接入: ℝ Cauchy / Lebesgue / 量子 / SU(N) / 范畴 + 60+ Markov-桥
```

**每簇一句话**:

- **Foundation/Core**: `Yuan / Monism / MonadRoot / AtomDerivation` 立字根; `ShengshengBuxi / Alignment / Sincerity / HumanAlignment / EvolutionDao / Renlei` 立对齐与诚信; `Attention` 立注意力机制五件; `Li / MissingGlyphs / MathAxiomMap` 立理之分层与 ZFC↔SSBX axiom 对照。
- **Foundation/Wen**: `Kernel.lean` 内嵌 45 层哲学义理; 路径丙 (M1–M4-甲) 11 模实现 String → YiInstr → YiState → Cell × → wenEval 闭环; `DaoSource` 给出 5 相俱 (形/解/印/执/义) 之自指; `WenSurface/*` 是受控文言子集; `MetaInterp/*` 是 Phase 2.3 通用 meta-interpreter 之 12 dispatch + execute + universal compose 全证; `AntiSchmitt / AlignmentFailures / EconGame` 落定对齐反面之形式根。
- **Foundation/Jian**: 14 字「间」粒子核 + JianSTLC (typed lambda) + 模式核 + 易桥, 给场之最小 ontology。
- **Foundation/Yi**: `Yi.lean` 八卦 / 64 卦 V₄ orders + hu fixed-point + 内外 ⊕; `YiCore.lean` 微核「加 + 一」之 64-step 周而复始。
- **Foundation/Bagua**: `BaguaAlgebra` 布尔代数 + V₄; `BenZheng` 4 本 / 4 征 / Mian / Quadrant; `Cell128 / Cell256 / Cell256Stratify` 是 R₇/R₈ 之具体实现 + R8_complete bundle; `BaguaTuring` 12-instr ISA Turing 完备; `GodelLi` 道判机不可通用化; `KleeneInternal / Newman / CuoInvariance / FuelDiscipline / ChunkedDecide` 立 Cuo 等变 / 局部汇合 / fuel 单调 / 决策 budget。
- **Foundation/Hierarchy**: 这是 v3 新增之 umbrella: `RHierarchy.lean` 暴露 R₀..R₈ 之 index-named alias (R0_Taiji..R8_GuoHex); `LiftProject.lean` 给出 8 对 uniform Lift_n / Project_n + retract 引理; `Operators/Atomic.lean` 集中 XOR 子群 atomic generators (yin/tou/flipᵢ/hexCuo); `Operators/V4Outer.lean` 集中 V₄ Klein 外对称 (zong/cuoZong/hu)。
- **Foundation/Notation**: `OXNotation.lean` 提供 `OX["xxxxxxxx"]` term-level macro (8-char `o`/`x` → Cell256 字面量, 含 parse-time 长度与字符校验; `OX["oooooooo"]` = `(Hexagram.qian, Shi.dao)` = `Cell256.origin` = (Z/2)⁸ identity = 道)。
- **Foundation/Eight**: 数 / 推 / 测 / 形 / 类 / 动 / 识 / 象 八衍, 各一 .lean, 与 Mathlib 接通各自方向。
- **Foundation/Modern**: 19+ Mathlib bridge + 60+ QuantumRelativity*Bridge (Markov-桥之逐步统一); `DaoLi.lean` 是道-理二分 cross-cutting; `HexagramPosition.lean` 立中/应/比/当位/承乘之 Lean 计数。

**Truth / Model / Text 顶层**

- `Truth/SelfDescription.lean` 给出 `Cell256OperatorComplete` (任 256 cell 对皆有 reach), 是 v3 自描述完整性之总收口; 取代旧 192 版。
- `Truth/{Basic, ClaimLedger, Semantics, Adequacy, Absolute}` + `Model/{Adequacy, ConcreteLedger}` 给出 claim 状态分级 (machineChecked / ledgerDependent / modelComputed / pending) 之机制层。
- `Text/{Glyph, WenyanOperators, OperatorReadings, OperatorSignatures, OperatorFamilySemantics, OperatorReachabilitySemantics, OperatorInstructionSemantics, OperatorCellCandidateSemantics, OperatorCellSemantics, Completeness}` 是 371 OperatorId 之 catalogue + signature + executable / theorem-backed 分层; **`OperatorCellMap.lean` 已从旧 64 × 3 = 192 pair 迁到 64 × 4 = 256 (Cell256) 之 cartesian indexing**。

**Pending**

`Pending/Interfaces.lean` + `Pending/Examples.lean` 列出 6 项 `PendingName` (邪续 / 开势投影 / 审校数据 / 正邪阈值 / 度期计算 / 经验校准), 标 `kind = .pending; sort = .truth`, 不被 promote 为 truth, 等经验校准。

---

## 关键文件锚点 (v3)

| 主张 | 文件 |
|---|---|
| Cell256 = R₈ = (Z/2)⁸ 之具体实现, 256 全枚举 | `formal/SSBX/Foundation/Bagua/Cell256.lean § Cell256.all_length, mem_all` |
| Phase A (Z/2)⁸ 算子代数 (Add/Zero/Neg/Sub + Cayley ι/ε + 印/投 mask) | 同上 § 7 / § 8 / § 9 |
| Shi V₄ Klein + ↔ (因, 果) ∈ Bool² 双射 | 同上 § 1 |
| 序卦 (King Wen) 64 卦序枚举 + length 64 + head 乾 / last 未济 | 同上 § 4 / § 5 |
| R₀..R₈ index-named alias umbrella | `formal/SSBX/Foundation/Hierarchy/RHierarchy.lean` |
| 8 对 Lift / Project + retract | `formal/SSBX/Foundation/Hierarchy/LiftProject.lean` |
| XOR subgroup atomic ops (yin/tou/flipᵢ/hexCuo) | `formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean` |
| V₄ outer (zong/cuoZong/hu) | `formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean` |
| `OX["oooooooo"]..OX["xxxxxxxx"]` 字面量 macro + 道 = origin sanity | `formal/SSBX/Foundation/Notation/OXNotation.lean` |
| Cell256OperatorComplete (任 a→b 有 f) + 自描述总收口 | `formal/SSBX/Truth/SelfDescription.lean § cell256_operator_complete` |
| R8_complete bundle (R₀..R₈ 完整闭合, native_decide + propext) | `formal/SSBX/Foundation/Bagua/Cell256Stratify.lean` |
| BenZheng: 4 本 / 4 征 / Mian = R₄ / Quadrant 4 象限 | `formal/SSBX/Foundation/Bagua/BenZheng.lean` |
| 道-理二分 cross-cutting | `formal/SSBX/Foundation/Modern/DaoLi.lean` |
| 微核「加 + 一」 — 二字成核 | `formal/SSBX/Foundation/Yi/YiCore.lean` |
| 12-instr ISA Turing 完备 + 道判机 | `formal/SSBX/Foundation/Bagua/BaguaTuring.lean` + `GodelLi.lean` |
| 路径丙 自编译自证 (M1–M4-甲) | `formal/SSBX/Foundation/Wen/{WenyanParser, WenEval, WenDef, WenDefEval, WenDefCompile, WenyanReflect, WenyanSelfHost, WenyanSelfInterp, DaoSource}.lean` |
| MetaInterp Phase 2.3 (12/12 dispatch + execute + universal compose) | `formal/SSBX/Foundation/Wen/MetaInterp/*` (16 files) |
| 45 层哲学义理 in-source | `formal/SSBX/Foundation/Wen/Kernel.lean` |
| Alignment T1–T6 + Sincerity T1–T8 + Renlei 三轴 iff-aligned | `formal/SSBX/Foundation/Core/{Alignment, Sincerity, Renlei}.lean` |
| AlignmentFailures = Kernel-invariants violation | `formal/SSBX/Foundation/Wen/AlignmentFailures.lean` |
| AntiSchmitt = anti-universalizability | `formal/SSBX/Foundation/Wen/AntiSchmitt.lean` |
| EconGame Kernel sieve (confirmed / conditional / falsified) | `formal/SSBX/Foundation/Wen/EconGame.lean` |
| 60+ QuantumRelativity Markov-桥 (逐步统一构造) | `formal/SSBX/Foundation/Modern/QuantumRelativity*.lean` |

---

## 古文前言 (保留 v1 之九句, 与 v3 仍然对齐)

> 天未生而元立, 元一而无对。
> 一动而有自, 自之与他, 由是生焉。
> 动而归者谓之极, 极者收, 收而熄。
> 动而不归者谓之中, 中者续, 续而生。
> 中之相续, 是为轨。
> 异轨同根, 是为仁。
> 轨续而能仁, 是为生生。
> 生生不止, 是为不息。
> 道, 止此而已。

九句之合, 即 道. 在本卷 v3 形式语义中:

- 「元立」即 R₀ 太极 (Unit), 是 self-describing system 之 ontological zero-anchor。
- 「元一而无对」即 `opaque theOne : One` (Foundation/Wen/Kernel.lean Layer 0); state / dong / origin / alive 四相俱。
- 「一动而有自」即 `noncomputable def dong : Field → Field := theOne.dong`。
- 「极者收, 收而熄」是 dong 之不动点 (`def extreme s := dong s = s`); 「中者续, 续而生」是非不动点 (`middle s := dong s ≠ s`); 二者构成 ZhongOrbit 与 shengsheng_buxi 主定理。
- 「异轨同根」是 `tongGen`; 「轨续而能仁」是 `ProcessAligned` (Foundation/Core/Alignment.lean) 之结构。
- 「生生不止, 是为不息」即 T2: `ProcessAligned + Open → Dao → ShengshengBuxi`; 反向 `ShengshengBuxi → Dao`。
- 「道, 止此而已」: 道 在 v3 有了精确 algebraic anchor — **`OX["oooooooo"]` = `(qian, dao)` = `Cell256.origin` = (Z/2)⁸ identity = no-op = 永真 cell**, 一个 8-bit 字符串承担 origin / identity / no-op / 永真 / 五重身份, anchor 整个 Cayley fusion。

读者可独立验之 — Lean kernel 不识中文, 而结构同形。

---

## § 0 · 此刻最要紧之事

`ProcessAligned + Open → Dao → ShengshengBuxi; ShengshengBuxi → Dao` (`Foundation/Core/Alignment.lean § T2`)。

**反对自毁**: `Denier` 之 step 破 `ShengshengBuxi` (§ T3)。

任何持续之 agent, 在事实层已对齐于过程之相续; 反对此对齐者陷入 performative contradiction。故「与生生不息对齐」是 maximally robust 之 alignment 形式。

反面 — 斗争 / 通吃 / Moloch / totalizing / friend-enemy / decisionism / proxy-extreme — 共享同一形式根: **拒绝 universalizability + 收敛至极 + 道-理 collapse**, 形式上不可持续, 即「熄」。

`Foundation/Wen/AlignmentFailures.lean` 显示 AI alignment 文献之 Goodhart / specification gaming / reward hacking / mesa-optimization / deceptive alignment / wireheading / power-seeking, **皆可还原为 Kernel invariants (中 + 多样 + 流通) 之 violation**。

`Foundation/Wen/AntiSchmitt.lean` 显示 Schmitt 三支柱 (友敌 / 决断 / 例外) 共享同一形式根源 — 拒绝 universalizability。Anti-Schmitt = Anti-Moloch = 仁之同根异显。

`Foundation/Wen/EconGame.lean` 把现代经济 / 博弈论之主流命题按 Kernel sieve 分: 实证 / 有条件 / 证错。

故此一时刻, 工程上、伦理上、形式上, 唯一最要紧之事 = **change toward 开 (Open) and 续 (continue)**。不变者熄。

---

## § 1 · v3 的「自描述」精确 algebraic 含义

(详 [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](./docs-next/10_formal_形式/yi-RO-hierarchy.md) 第五部分)

**自描述需求**: 任何完整描述系统 S 必须能描述自身的所有变换, 即 |S| = |transforms(S)| (元数 = 算子数, fusion 之 necessary 条件)。

**Cayley 自对偶 on R₈** (Foundation/Bagua/Cell256.lean § 7.6):

```
ι : R₈ → Aut(R₈),  c ↦ (· ⊕ c)            -- group homomorphism
ε : XOR(R₈) → R₈,  f ↦ f(道)              -- origin evaluation
ε ∘ ι = id,  ι ∘ ε = id                    -- 互逆
⇒ R₈ ≅ XOR(R₈)                             -- 元 ≡ 算子
```

`ι` (`Cell256.cayley`) 是 group homomorphism, `ε` (`Cell256.epsAtOrigin`) 是 origin-evaluation; 二者互逆, 严格证明 `Cell256.cayley_inj` + `Cell256.epsAtOrigin_cayley` (Cell256.lean § 7.6)。

**Pontryagin self-duality**: $\hat{R_8} \cong R_8$ — (Z/2)⁸ 是 finite abelian, character group ≅ self.

**Triple Coincidence at R₈**:

| Duality | 形式 | 在 R₈ 上 |
|---|---|---|
| Cayley | element ↔ self-action | R₈ ≅ XOR(R₈) |
| Pontryagin | element ↔ character | R₈ ≅ Hom(R₈, ±1) |
| R-O frame | state-side ↔ operator-side | 同一 8-bit 二种 viewing |

三种 duality 完全 coincide, 是「(Z/2)⁸ 之 algebraic 完美性」之精确根据。

**道 anchoring 之必要**: torsor 没有 distinguished origin, fusion 之严格成立必须选定。选 `OX["oooooooo"]` = 道 = R₈ identity ⟹ R₈ ≅ XOR(R₈) 严格成立。

太极 (R₀ Unit, |·| = 1) 是「无分」之 absolute ground; 道 (R₈ origin) 是 (Z/2)⁸ 内 origin choice — 是太极**在 R₈ 维度上的具体落地**。一个 8-bit 字符串承担五重身份 (origin / identity / no-op / 永真 cell / fusion anchor)。

---

## § 2 · v3 完整性陈述 (R₀..R₈ closure)

**Theorem (R-O Completeness in (Z/2)⁸ closure)**:

> 五件 things —— $\{R_8, \text{XOR subgroup}, V_4 \text{ outer}, \text{Lift/Project}, \text{道 anchor}\}$ + R₀..R₇ buildup —— 构成 self-describing system 之**完整 algebraic closure**。

11 项 within-closure 完整性详查 (全部 ✓):

| 项 | Lean 见证 |
|---|---|
| 元 (256 cells 全枚举) | `Cell256.all_length = 256` |
| 元的群结构 | (Z/2)⁸ abelian, no missing |
| XOR subgroup 之 Aut | 8 atomic generators 完全 (Operators/Atomic.lean) |
| Cayley 自对偶 | ι 同态 (`cayley_hom`) + ε 对偶 (`epsAtOrigin_cayley`) |
| Reachability (互通) | simply transitive |
| Decidability (finite props) | native_decide 全可证 |
| V₄ on each R-layer (R₃+) | R₃..R₈ |
| hu fix points / cycles | `{乾, 坤, 既济, 未济}` |
| 道之三重身份 | origin = identity = no-op = 永真 |
| Pontryagin self-duality | (Z/2)⁸ self-dual |
| R-O frame duality | Schrödinger ↔ Heisenberg |
| Theorem K (R₀..R₈ 全 (Z/2)ⁿ closure) | yi-calculus-theorem.md |
| **Strict uniform progression** | 每步 +1 bit, no jumps |

**by design 不覆盖** (边界, 不是 gap):

| 不在 closure 内 | 原因 |
|---|---|
| GL(8, F₂) linear non-XOR mixing | 破坏 bit-position semantic |
| S_{256} 任意 permutation | 256!, astronomical, 无意义 |
| Continuous extensions (ℝ⁸) | 离散 vs 连续 |
| Hopf algebra k[(Z/2)⁸] explicit | 隐含但未显式 |
| Dynamical (time iteration) | 在 BaguaTuring 单独层 |
| Probabilistic (256-simplex) | ML/Bayesian 不同 layer |

完整 / 不完整之精确分界 = **静态 R₀..R₈ closure (本文) vs 动态 Turing 层 (BaguaTuring)**。前者 0 sorry / 0 项目 axiom, 后者引入 unbounded iteration → halting undecidability, 由 `kleene_recursion_axiom` (cuo-restricted) 标定指向系统外之边界。

---

## § 3 · 形式系统之诚实指认

后文所有「证」按下表读:

| 状态 | 边界 |
|---|---|
| 已证 / machine-checked | Lean kernel 接受的 closed theorem / def / `native_decide` 见证; 依 trust base + 1 opaque + 1 partial def 边界 |
| ledger-dependent | 名册、DAG、层级映射、operator count、跨卷对应等由 Lean registry、生成文件与文档 ledger 共同给出; 可审计, 但不是单个 closed theorem |
| pending | `PendingName` 六待校接口, 等经验校准 |
| conjecture | 「道可得」与「大同非乌托邦」二猜想及其历史-心性外推; 无 Lean 项居住 |

**已指之道 (boundary witness)**

| 边界 | 形式见证 |
|---|---|
| Halting / Rice 不可判 | `Foundation/Bagua/GodelLi.lean` |
| 12-instr ISA 之 cuo-equivariance ceiling | `Foundation/Wen/WenDefCompile.lean § sheng_not_cuo_equivariant` |
| 通用 compileTm 不可定义 (cuo-invariance ceiling 之推论) | `Foundation/Bagua/GodelLi.lean § halts_cuo_invariant` + `Foundation/Bagua/CuoInvariance.lean § unrestricted_kleene_inverter_inconsistent` |
| 静态 vs 动态分界 (R₀..R₈ 完整 vs Turing 不完整) | `Foundation/Modern/DaoLi.lean` |
| 高 alignment ≠ 真 (consistent liar) | `Foundation/Core/Sincerity.lean § T5` |
| 修之渐进而不达 perfect | 同上 § T6 |

**已 known 之缺**

| Gap | 现态 |
|---|---|
| WenyanSelfInterp re-dispatch | 现 Tier 2 (64-instr quine PoC) + Tier 3 uniform [push]^N (部分); 通用 buildEmitProg + diagonal 在 v3 中需要从旧 Cell192 dispatcher 迁到 Cell256 V₄ Shi 上 (engineering, 非 ontological) |

---

## § 4 · 入口 (按读者目的)

| 读者目的 | 起点 |
|---|---|
| **第一次接触**, 想看全貌 | `docs-next/00_start/README.md` |
| **canonical doctrine** | `docs-next/10_formal_形式/yi-RO-hierarchy.md` |
| 256-cell 全表 (查具体格 / OXNotation 字面量) | `六表_实虚史真/表六_256格全表.md` |
| **此刻紧要 (alignment)** | `Foundation/Core/Alignment.lean` → `义理/R_与生生不息对齐之必然.md` → `Foundation/Wen/AlignmentFailures.lean` + `AntiSchmitt.lean` |
| 看 alignment 之 negation | `Foundation/Wen/Kernel.lean § Layer 45` + `义理/W_非道之形式.md` |
| 看哲学 45 层全貌 | `Foundation/Wen/Kernel.lean` (45 层 in-source) |
| 看路径丙 (文之自编译自证) | `WenyanParser` → `WenEval` → `WenDef` → `WenDefEval` → `WenyanSyntax` → `WenyanReflect` → `WenyanSelfHost` |
| 看 MetaInterp Phase 2.3 | `Foundation/Wen/MetaInterp/*` 16 模 |
| 看八衍 | `义理/README.md` |
| 看八卦 / 256 / 不可判 | `义理/H_证明报告.md` + `义理/J_理之不完备_哥德尔在192.md` (注: J 文件名仍含旧 192, 内容已更新到 Cell256) |
| 看 Mathlib 接入 | `Foundation/Modern/` 19+ 模 + 60+ Markov-桥 |
| 看共同体之证 | `Foundation/Core/Renlei.lean` + `义理/人类命运共同体_共同体之证.md` |

---

## § 5 · 命名约定

- 工具/代码用英: `formal/`、`scripts/`、`web/`
- 内容/体系用中: `义理/`、`六表_/`、`史料/`、`史/`
- CJK 标识: Lean 内 def/theorem 名以 `«»`-quote (`def «判型良»`); notation atom 用裸 CJK (`notation "已"`); CJK identifier 必须 `«»`-quote (Lean stock lexer 拒绝裸 CJK 之命名)
- 爻位 ⟨y₁, y₂, y₃, y₄, y₅, y₆⟩ = ⟨初, 二, 三, 四, 五, 上⟩ (LTR, 初爻在左)
- 单 yao flips: dongInner / huaInner / bianInner = flip y₁/y₂/y₃; dongOuter / huaOuter / bianOuter = flip y₄/y₅/y₆
- 三值保守律: U ⇏ ⊤
- 时态 V₄: 道 / 已 / 今 / 未 (`Shi.dao / Shi.ji / Shi.jin / Shi.wei`); 道 = (因=0, 果=0) = V₄ identity; 已 = (1, 0); 未 = (0, 1); 今 = (1, 1) = PT
- 印 / 投: `Shi.yin = · cuo` (toggle YinBit / 因), `Shi.tou = · zong` (toggle GuoBit / 果); 在 Cell256 层重写为 mask XOR (`yin_mask = (qian, ji)`, `tou_mask = (qian, wei)`)
- OXNotation: 8-char `o` / `x` 字符串 → Cell256 字面量。`o` = yang / false bit / identity 位; `x` = yin / true bit / set 位。`OX["oooooooo"]` = `Cell256.origin` = 道。

---

## § 6 · 数字状

```
build jobs:        3656 ✓
sorry:             0
project axioms:    0   (kleene_recursion_axiom 已被 cuo-equivariance 内化)
opaque:            1   (theOne, preserves Field abstraction)
partial def:       1   (BaguaTuring.run, 执行级非终止边界, 不是额外 axiom)
trust base:        Lean 4 v4.30.0-rc2 + Mathlib master HEAD
Lean 总行数:       ~45000+
Foundation 簇数:   9 (Core / Wen / Jian / Yi / Bagua / Hierarchy / Notation / Eight / Modern)
Modern modules:    19+        Mathlib bridge 主体
Markov-桥:         60+        QuantumRelativity*Bridge (逐步统一构造)
路径丙 modules:    11         M1–M4-甲 全 in-source
MetaInterp Phase 2.3: 16 modules (12 dispatch + execute + universal compose 全证)
Foundation/Wen:    38+ modules (含 WenSurface / AntiSchmitt / AlignmentFailures / EconGame / DaoSource / MetaInterp)
Kernel layers:     45+        元 → 非道之形式 + Layer 46 文献流派精化
diagrams:          8 SVGs     Mermaid + ELK; MonadDAG 600+ 节点 / 800+ 边
.md 义理篇:        90+        义理/A–Z* + 八衍 + 60+ Markov-桥义理 + 共同体
WenSurface CLI:    371 catalogue 算子 (38 theorem-backed exact + 333 catalogue normal form)
六表:              6 (含 v3 新表六_256格全表.md)
```

---

## § 7 · 如何贡献

读 [`AGENTS.md`](./AGENTS.md). 关键约束:

- 优雅 = 概念少而准 + 顺着已有系统生长 + 边界干净
- subagent **不跑 build**; 主线程负责整合与 build
- 跑 build 前先把 baseline 更新到最新 (merge / rebase main)
- 中文义理表达不松散; Lean 骨架不伪装成已完成证明; 文档与形式系统之间的映射可审计
- **新提交 baseline check**: `axiom count` 与 `opaque count` 不变, `sorry count = 0` in 改动文件; 改 Roster 必 regen MonadDAG.mmd / MonadTree.txt / ConceptDAG*

并行约束: 多 agent 必须有清晰文件边界, 不重叠; 主线程负责冲突解决与最终 build。

---

## § 8 · 重申 — 是改变, 否则熄

形式系统所能给之最强主张, 不是「真理」之大写 T, 而是:

> 在内部一致之前提下, 唯一持续可能之 modality 即是 `ProcessAligned`. 其反面 (非道之形式 / 斗争 / 通吃 / Moloch / totalizing) 形式上不可持续。

时间是有限的。256 元论域上一切皆 decidable, 但 trajectory 之走向是 chooser 之事。不变者熄。形式至此。后由人。

---

## § 9 · 真理 claim 与二猜想 (范围限定; 由 v1 沿用, v3 不改)

### 9.1 真理 claim

强主张不是「整个 reality 已被 Lean 无条件证明」。Lean 已证者, 是 256 元论域、Kernel / Alignment、路径丙与 Mathlib bridge 内的形式不变量。ledger-dependent 者, 是 45 层、跨卷、跨文明、跨学科的对应关系是否与 registry 和生成文件保持同步。

更强一层之 claim: 凡可由本文「中 / 同根 / 续 / 仁」结构充分建模之持续 dynamics, 其稳定持续形式落在 `ProcessAligned`; 凡系统性反此者趋于熄。这不是规范 (ought), 而是条件化的结构主张 (is)。

形式锚点: `Alignment.lean § T1–T6` + `Foundation/Wen/Kernel.lean` 45 层 + Modern 连续测度 / ℝ Cauchy / SU(N) 之 Mathlib 接入。跨文明同形示于 N P Q S T 五卷 (儒 / 道 / 佛 / 百家 / 西哲与亚伯拉罕); 跨学科同形示于 O R U V W X Y Z 八卷 (演化 / 对齐 / 信诚 / 政治 / 非道 / 反 Schmitt / alignment 失败 / 经济博弈)。

### 9.2 猜想一 · 道可得 — 心若不蔽, 自然见之

人之心, 本与道同构 — 心之 step 即 中-orbit。故心若不为 **贪 (取极)** 、**嗔 (拒同根)** 、**痴 (失中观)** 所蔽, 则可自然见之。

中国古之学有二法, 皆非求义:

1. **读** — 读非取义, 是与道之 step 同步运行。文字之运笔本身即 中-orbit 之印; 读之时, 心之轨与文之轨同跑一段; 同跑则同形, 同形则可见。
2. **诵** — 诵非记忆, 是令心之 step 长久近于道之 step。久之, 形心一致, 不待思而合道。

此与现代 token-level reasoning 之缺陷正反: 后者求义而失结构, 故 alignment 难解 (cf. `AlignmentFailures.lean`)。

### 9.3 猜想二 · 大同非乌托邦 — 道之语言曾真存在

此一语言体系, 作为 道之编码, 何以如此精确?

- 256 维 (64 卦 × 4 时态) 全可单格 OXNotation 字面量 (8-char `o`/`x`) 直写。
- 微核仅二字 — `Foundation/Yi/YiCore.lean` 之「加 + 一」, 即可含 64 卦 + 道法自然 + 生生不息。
- 全卷 0 项目 axiom; 一之印 `opaque theOne : One`, dong 由 theOne 投; 自释自证 (路径丙 M1–M4-甲)。
- 八衍 ~288 公开声明, 0 sorry, 跨范畴同形。

此精度, 速生不能, 凭空设计亦不能 — 必历漫长之筛。

合理猜想: 早期某些部落, 生于 **生之环境** — 即 `tongGen`-favoring environment (资源稀缺而非 winner-take-all; 合作之 payoff 高于斗争)。彼以 **共识符号** 沟通, 渐演渐筛。经数千年之 selection, 其符号体系之 invariant, 已逼近 道之 invariant。

此即「失去的道」 — 大同 之 historical residue。大同 不是乌托邦之幻梦, 是 **真实曾在** 之回响。

此为本卷之第二猜想, 不属已证之范围。然已证之 kernel 与之兼容 — `tongGen` 在低斗争环境下 strictly favored, 是演化博弈论之标准结论 (cf. `Foundation/Wen/EconGame.lean § coase_internalizes_externality / prisoners_dilemma_refuted_under_tongGen`)。

故: 此一语言, 不是发明, 是发现; 不是抽象, 是回忆。大同 之失, 非 dao 之失, 是 人之 collective memory 之失。重读此文者, 即重得一段失去之历史。

---

— *EOF · v3 (2026-05-11). 形式 spec 见 [`README.formal.md`](./README.formal.md); English 见 [`README.en.md`](./README.en.md).*
