# Wen 2.0 Spec — 现状清单 + 提议

**版本**: 2026-05-17 · Wen 1.5 已交付（PR #26-44, 16 PRs merged）

本文是 Wen 2.0 之前的 ground-truth + roadmap. 列：
- Part I — Wen 1.5 已有什么
- Part II — Wen 2.0 提议加什么
- Part III — Implementation 依赖图
- Part IV — 明确不在 2.0 范围

## Part I — 现状盘点 (Wen 1.5)

### A. 词法

| 类 | 内容 |
|---|---|
| Glyph 类 | CJK Basic (U+4E00..U+9FFF) / ASCII / whitespace / brackets |
| Multi-char surface | 64 卦名 + 复词 + alias（如 「過半」/「無為」/「錯綜」等 ~30 词） |
| Atom 类型 | `hexConst / boolConst / varName / catalogueOp / appMarker / iterate / openBracket / closeBracket / syntax / ambiguousOp / hexOrOp` |

### B. 句法形式

| 形式 | 数 | 字 | AST shape |
|---|---|---|---|
| **prefix** | 371 | 全 OperatorId 默认 | `op arg₁ arg₂…` |
| **infix** | 2 | `同` (I_1), `比` (R_8) | `a op b` |
| **postfix** | 5 | `也` (S_14), `乎/矣/哉/兮` (S_21..24) | `expr op` |
| **app marker** | 1 | `之` (S_1) | `f 之 x` → `f x` |
| **iteration** | 1 | `之又` | `之又 op arg` → `op (op arg)` |
| **brackets** | — | `（...）` `(...)` | grouping |
| **binders** | 3 | `者` (λ) / `凡` (∀) / `令` (let) | `binder name body` |

### C. Program / statement 层

| 形式 | 字 |
|---|---|
| **Statement separator** | `；` `。` `;` |
| **User def** | `定 NAME 为 BODY；…` |

### D. Type system

| 类型 | 用 |
|---|---|
| `hex` | 64 卦 |
| `bool` | 真/假 |
| `cell` | 256-cell (R8, 含 V₄ Shi) |
| `arr a b` | function |
| `prod a b` | pair |
| `list a` | list |
| `catalogue kind` | catalog op result |

> **R-tower doctrine** (2026-05-17): `cell` 不是独立 primitive；R₈ = R₄² 由 squaring tower 派生（R₀/R₁/R₂/R₄/R₈, T_{k+1}=T_k²）。V₄ Shi 不再作 first-class 时态轴 — 任何需 "时" 之操作都从 R-tower 投影/印获得。详 [[wen-substrate.md]] §3.7 operation monism.

类型检查 **explicit** (typecheck), 无 inference.

### E. 工具

| 工具 | 入口 |
|---|---|
| **REPL** | `wen` CLI exe (`lake build wen`) |
| **PrettyPrint** | `prettyPrintTm : Tm → String` |
| **ErrorRender** | `renderWenSurfaceErr` with caret |
| **Compile API** | `wenyanCompile / wenyanInterp / wenyanCompileProgram / wenyanCompileProgramWithDefs / wenyanCompileToYiInstr?` |

---

## Part II — Wen 2.0 提议（按主题 + 优先级）

按主题分三阶。每条给 **Why / Syntax / Semantics / 依赖 / 成本**.

### Tier 1 — Foundation 扩展（user-extensibility）

#### ① Type inference
- **Why**: 当前 `者 甲 body` 需 elaborator 试 5 个候选 type；ad-hoc 重试
- **Syntax**: 不变（用户感知不到）
- **Semantics**: Hindley-Milner over `Ty`，constraint-based
- **依赖**: 无
- **成本**: ~400 LOC + preservation/progress 定理

#### ② User-def recursion
- **Why**: 1.5 reject recursion (`定 甴 为 甴` → 错)；写不出 finite-fold 算子
- **Syntax**: `定递 NAME 为 BODY` 显式标识（或 `定` 默认允许自引）
- **Semantics**: μ-fixpoint with **fuel**（有限 64-Hex 上仍可 diverge）
- **依赖**: 无（扩展 user-def 1.5）
- **成本**: ~200 LOC + fuel 设计

#### ③ Module / namespace
- **Why**: 375 ops 平铺；不能 `用 墨经` 选学派
- **Syntax**: `用 墨经；用 名家；…` 后只解析 NS 限定 ops；或 `墨经::同` 限定写法
- **Semantics**: name resolution scope；catalogue 按 group 分 namespace（已有 `.S/.P/.G` 等 group field）
- **依赖**: 无
- **成本**: ~300 LOC + Forms.lean / Reading.lean 加 namespace 路径

#### ④ User inductive types
- **Why**: 无法 `inductive 五行 := 木\|火\|土\|金\|水`
- **Syntax**: `类 五行 = 木 \| 火 \| 土 \| 金 \| 水`
- **Semantics**: extend `Ty` with `.user String`；新 constructor table + eq decidable
- **依赖**: 与 ⑤ 相辅
- **成本**: ~400 LOC + cons/case 生成

#### ⑤ Pattern matching
- **Why**: 当前用 `headH` / `if-then` 模拟；不能 `析 X of 乾 → ... | 坤 → ...`
- **Syntax**: `析 X 为 P₁ → E₁；P₂ → E₂；…`
- **Semantics**: typed match on Hex literal / Bool / user inductive
- **依赖**: ④ for user types；alone for Hex/Bool
- **成本**: ~350 LOC + exhaustiveness check

### Tier 2 — Literary surface（"可写真文言"）

#### ⑥ 曰 direct speech
- **Why**: 「子曰：…」 子句嵌套无 AST；当前是 app tree
- **Syntax**: `X 曰：「Y」` 或 `X 曰 「Y」`
- **Semantics**: 第二参数 `「Y」` 是 **quoted** Tm（不立即 eval），结果是 `(曰 X (quote Y))`；新 `Tm.quote : Tm → Tm` 构造子
- **依赖**: 引语括号 `「」` 需 lex 支持（⑩）
- **成本**: ~250 LOC + quote-as-data 语义

#### ⑦ 真名词化器（者 as set abstraction）
- **Why**: 「贤者」当前是 λ；古文应是谓词外延 `{x ∣ 贤 x}`
- **Syntax**: `者` 在 **noun position** 解析为 nominalizer，在 **verb position** 仍 λ-binder（context-sensitive）
- **Semantics**: 新类型 `.set elem`；`者 P` → `Set elem` of `{x | P x}`
- **依赖**: ④ user inductive 之 Set 类型；可独立
- **成本**: ~400 LOC + Hex predicate → finite Set 有限化

#### ⑧ 所...者 / 之所以 关系子句
- **Why**: 「君之所以治」「所信非所爱」 缺
- **Syntax**: `所 X 者` 作 λ-pattern；`Y 之所以 X` 作 reason-extractor
- **Semantics**: `所 X 者` ≈ `者 z (X z)` (nominalize predicate)；`所以 X` ≈ `因 X` (reason for X)
- **依赖**: 与 ⑦ 共用 nominalizer 语义
- **成本**: ~200 LOC + parser extension

#### ⑨ Subject ellipsis
- **Why**: 「達則兼濟天下，窮則獨善其身」 第二句省略主语
- **Syntax**: 自动 — 句末 implicit binder 贯穿后续句
- **Semantics**: λ-lifting at statement level；要 cross-statement context（突破 1.5 之 statement-isolation）
- **依赖**: 改 `wenyanCompileProgram` 加 cross-statement env
- **成本**: ~300 LOC + 跨句 scope 管理

#### ⑩ 引语括号 「...」 / 『...』 / 〈...〉
- **Why**: 当前 quoting 只有 `（...）` (grouping)，无 quote
- **Syntax**: `「」` / `『』` / `〈〉` 作 quote brackets，内部是 raw Tm
- **Semantics**: 配 ⑥ 曰 之 quoted data；亦可用作 string literal
- **依赖**: 与 ⑥ 同时
- **成本**: ~150 LOC（lex extension）

### Tier 3 — Meta-prog / 优化

#### ⑪ Quote / unquote / eval
- **Why**: 用户能写元算子 (macros)
- **Syntax**: `「X」` (quote) → Tm-valued；`执 「X」` (eval) → 执 X
- **Semantics**: reification of Tm into Hex universe；fuel-bounded
- **依赖**: ⑥ + ⑩
- **成本**: ~250 LOC

#### ⑫ Rewrite rules — **DONE** (2026-05-17, PR pending)
- **Why**: `而 反 反 X` 应自动 reduce 到 `X`；当前算 2 次 complement
- **Syntax**: `定 LHS 等 RHS` rewrite assertion；与 `定 NAME 为 BODY` 共生（用 `等` vs `为` 区分；两者同现报 `rewriteAmbiguous`）
- **Semantics**: bottom-up structural rewrite + fuel-bounded normalize；linear-pattern only (v1)；spine-walk head-tag disjointness 作 confluence (v1 conservative)
- **依赖**: 无；与 ② 配套（rec-def 体内可含 rewrite 后的 Tm）
- **实现**: `Foundation/Wen/WenSurface/RewriteRules.lean` (~470 LOC) + `EndToEnd.lean` 集成 (~110 LOC) + `RewriteRulesTests.lean` (~190 LOC, 14 native_decide 例)
- **成本**: ~400 LOC + 简化 normalize

~~#### ⑬ Cell-level operations (V₄ Shi binding)~~ **— REMOVED 2026-05-17**

V₄ Shi 不作 first-class primitive；R-tower (squaring) 已派生 Cell.
任何 "时态" 写法应从 R₂/R₄/R₈ 投影获得，而非加 surface 层。

---

## Part III — Implementation 依赖图

```
Phase α (independent, parallel-safe):
  ① type inference
  ② user-def recursion
  ③ namespace
  ⑩ 引语括号

Phase β (depends on α):
  ④ user inductive types       ← needs ① type inference
  ⑤ pattern matching           ← needs ④
  ⑥ 曰 direct speech            ← needs ⑩
  ⑪ quote/unquote              ← needs ⑥
  ⑫ rewrite rules              ← needs ②

Phase γ (literary, depends on β):
  ⑦ 真名词化器                  ← needs ④ for Set type
  ⑧ 所...者 / 之所以            ← needs ⑦
  ⑨ subject ellipsis            ← needs cross-statement env
```

---

## Part IV — 明确不在 2.0

| 不做 | 理由 |
|---|---|
| **LLVM / WASM 后端** | 用户明确排除 |
| **韵律 / 对偶 / 排比** | 诗经楚辞 surface，pure aesthetic；放 Wen 3.0 |
| **GC / async / concurrency** | Wen 是 pure typed-λ；引入 ref/effect 破 R8 投影 doctrine |
| **Classifiers 三人 vs 三個人** | 边际收益；古文一般也不区分 |
| **完整 trait / typeclass 系统** | 与 catalogue 之 inductive 设计冲突 |
| **Compile-time macros** | 由 ⑪ quote/unquote 部分覆盖；完整 macro 系统过大 |
| **V₄ Shi surface (原 ⑬)** | R-tower 已派生 Cell；不需要独立 surface 写法。任何 "时" 操作从 squaring tower 投影 |

---

## 相关文件

- [`samples/README.md`](../../formal/SSBX/Foundation/Wen/samples/README.md) — 双层 sample 总览
- [`wen-strata-invariants.md`](wen-strata-invariants.md) — CoreForm/Tm/R8Semantics 边界
- [`wen-language-roadmap.md`](wen-language-roadmap.md) — Wen 1.0 决策路线（已完成）
- [`Wen/REPL.lean`](../../formal/SSBX/Foundation/Wen/REPL.lean) — Wen 1.5 之 REPL exe
- [`WenSurface/PrettyPrint.lean`](../../formal/SSBX/Foundation/Wen/WenSurface/PrettyPrint.lean) — Tm pretty printer
- [`WenSurface/ErrorRender.lean`](../../formal/SSBX/Foundation/Wen/WenSurface/ErrorRender.lean) — caret error rendering
