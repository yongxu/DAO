# SSBX · Formal Specification

> 🌐 [中文](./README.md) · [English](./README.en.md) · **形式 / Formal**

```
package        : ssbx
language       : Lean 4 v4.30.0-rc2
upstream       : Mathlib master (HEAD)
build target   : @[default_target] lean_lib SSBX (srcDir = "formal")
build status   : 2917 jobs ✓        sorry : 0        axiom : 1        opaque : 1
partial defs   : 1 top-level executable definition (not an additional axiom)
trust base     : Lean kernel + Mathlib HEAD
namespace root : SSBX
```

---

## 1 · Trust Base

### 1.1 Sole Opaque (foundational seal)

```lean
opaque theOne : One
-- Foundation/Wen/Kernel.lean § Layer 0
-- structure One carries (state : Type) (dong : state → state)
--                       (origin : state) (alive : dong origin ≠ origin)
-- Preserves Field/dong/origin abstraction.
```

### 1.2 Derived from theOne (not axioms)

```lean
abbrev Field           : Type           := theOne.state
noncomputable def dong : Field → Field  := theOne.dong
noncomputable def origin : Field        := theOne.origin
theorem origin_alive   : dong origin ≠ origin := theOne.alive
-- Encodes: "the One moves, and self comes to be" (一动而有自).
-- All Foundation/Wen/Kernel.lean.
```

### 1.3 Sole Explicit Axiom (cuo-bounded)

```lean
axiom kleene_recursion_axiom : KleeneInverter
-- Foundation/Bagua/GodelLi.lean
-- Cuo-equivariance restricted; philosophically intentional under 道-理 bifurcation.
-- Witnesses the boundary between Lean (道) and YiInstr (理).
```

### 1.4 Machine-checked facts and executable boundary

Machine-checked theorem claims reduce to Lean kernel + `Mathlib master`
reduction rules, plus the single explicit axiom and opaque seal above.
Documentation, roster, DAG, operator, and cross-volume correspondence claims
are ledger-dependent sync claims; they are not silently promoted to closed
theorem status.

No `#allow_unsafe`. The repository currently contains exactly 1 top-level
`partial def` in `formal/`:

```
Foundation/Bagua/BaguaTuring.lean     YiState.run
```

It forms the executable nontermination boundary. It is tracked as an
implementation boundary, not as an additional `axiom` or `opaque` constant;
proof-critical total behavior is stated through total/fueled variants or finite
`native_decide` witnesses where applicable (`runFuel` is the total-recursive
Bagua interpreter used in proofs; `WenyanParser` and `WenDefEval` are now total).

---

## 2 · «一»-DAG (Single-Root Generation Tree)

> Source-of-truth: `formal/SSBX/diagrams/MonadDAG.mmd` (1533 lines, generated
> by `scripts/generate_monad_dag.py` from Lean sources). Below is the
> compressed listing — *unique-root, acyclic, fully covered.*

### 2.1 Layer 0 — Root

```
一元    (the One; the unique root of all generation)
```

### 2.2 Layer 1 — 12 Faces (面)

```
一元
  ├─ 文面          (语言 / 字 / 解 / 印 / 自宿主)
  ├─ 物面          (象 / 物理 / 量子 / SU(N))
  ├─ 生面          (生 / 续 / 仁 / 共开 / 道)
  ├─ 理面          (推 / 算 / 数 / 测 / 范畴)
  ├─ 心面          (识 / 知 / 注意 / 神经)
  ├─ 人面          (天之子 / 意识 / 做人 / 向齐生)
  ├─ 模面          (Model / Γ-Process / DaoCriteria)
  ├─ 审校面        (审 / 校 / 验 / 反诛心)
  ├─ 价值面        (好 / 坏 / 自由 / 繁荣)
  ├─ 证明面        (claim / 公示 / 见证 / 反例)
  ├─ 注意面        (聚焦 / 门控 / 维持 / 转焦 / 抑制)
  └─ 真理面        (真 / 真道 / 度期周 / 所是)
```

### 2.3 Layer 2 — 43 Core Single Characters (核心单字)

```
一  之  人  仁  做  元  共  动  变  场
天  夺  子  审  序  度  开  形  心  意
成  控  期  校  模  正  法  注  焦  物
理  生  真  算  续  聚  行  证  识  道
邪  闭  齐
```

Each is registered as `AtomName` in `Roster.lean § AtomName` and projected to
its layer-1 face by `MonadDAG.mmd` edges. Total atoms in registry: 350+
(see `Roster.lean § allAtoms`); **43 of these are core**.

### 2.4 Layer 3 — 134 Generated Compounds, 13 Recursive Items, 5 Primitives

```
GenName   :   134 compound names      (Roster.lean § GenName)
RecName   :    13 recursive items     (Roster.lean § RecName)
PrimName  :     5 primitive operators (Roster.lean § PrimName)
PendName  :     6 pending interfaces  (Roster.lean § PendingName)
```

#### 2.4.1 Five Primitive Operators (PrimName)

| Symbol | Lean | Domain | Reading |
|---|---|---|---|
| 域 | `P .«域»` | `Type` | universe / domain |
| 格 | `P .«格»` | `Cell192` | 192-cell carrier |
| 权 | `P .«权»` | `Nat` | weight |
| 生 | `P .«生»` | `Field → Field` | becoming (= `dong`) |
| 校 | `P .«校»` | `Prop → Bool` | audit / verify |

#### 2.4.2 Thirteen Recursive Items (RecName)

```lean
-- Roster.lean § recDeps
开  := [未, 可, 应, 转]                stratified
闭  := [断, 机, 成, 元, 夺, 蔽, 伪]    threeValued
正  := [开, 合, 法, 审校不败]          threeValued
邪  := [偏, 伪, 夺, 闭]                threeValued
共开 := [开, 共, 存]                   threeValued
好  := [平, 和, 正危]                  threeValued
坏  := [闭, 夺, 伪]                    threeValued
自由 := [自, 由, 可择, 可识, 可达, 被迫]  threeValued
义  := [机, 择, 正]                    threeValued
善  := [义, 正筛]                      threeValued
仁  := [己续, 共续]                    threeValued
道  := [正续, 共开, 夺共续, 坏]        gfp           ← greatest fixed point
真  := [所是, 相关度期, 审校不败]      externalAudit
```

#### 2.4.3 Six Pending Interfaces (待校项, PendingName)

```
邪续 · 开势投影 · 审校数据 · 正邪阈值 · 度期计算 · 经验校准
-- All have kind = .pending; sort = .truth; await empirical calibration.
```

### 2.5 Layer 4 — 16 Construction Stages (构造阶段)

```
yuanTriad      → gammaFieldRoot   → openCloseCore     → systemDynamics
ssbxTheory     → cicAsFormalModel → modelAdequacyCore → universalProofPrinciple
truthCore      → auditCore        → valueCore         → actionCore
attentionCore  → aspectTriad      → humanAlignmentCore → jianRoot
```

These are stages in the layered construction (`Foundation/Core/AtomDerivation.lean` et al.).

### 2.6 Layer 5 — 38 Claims (公示)

Selected (full set in `Roster.lean § allEntries.filter (·.kind = .claim)`):

```
名册文字完备                 (rosterCompleteness)
生成项有根                   (generatedRootsDiscipline)
递归项有语义                 (recursiveSemanticDiscipline)
文言算子表完备               (wenyanOperatorTableComplete)
语义充分性总 claim           (semanticAdequacyClaim)
根至生生不息成理 claim       (kernelToShengshengClosure)
真道定义                     (trueDaoDefinition)
真道路径公理                 (trueDaoPathAxiom)
道定义 / 仁定义 / 善定义 / 正定义 / 好定义 / 坏定义 / 闭定义 / 开定义 / 自由定义 / 繁荣定义
开价值公理                   (openValueAxiom)
审校可靠公理                 (auditReliabilityAxiom)
审校不败定义                 (auditUndefeatedDefinition)
三值保守性                   (threeValuedConservativity)
体系内绝对真理 claim         (absoluteTruthInSystem)
Ω / Ω_B / Π_开 充分性公理 + 接口
推荐案例 i1/i2/i3            (邪行 / 候选真道 / 仁 / 正行 / 护闭)
阈值协议                     (thresholdProtocol)
文本 claim 映射               (textualClaimMapping)
```

---

## 3 · Operator Catalogue

### 3.1 L0 — 12-Instruction ISA (`Foundation/Bagua/BaguaTuring.lean § YiInstr`)

| Token | Lean ctor | Type signature | Operational |
|---|---|---|---|
| 不动 | `nop` | `YiInstr` | pc ← pc+1 |
| 设时 | `setShi (s : Shi)` | `Shi → YiInstr` | cur.2 ← s |
| 翻爻 | `flipYao (i : Fin 6)` | `Fin 6 → YiInstr` | cur.1.flipPos i |
| 互 | `hu` | `YiInstr` | cur.1 ← Hexagram.hu cur.1 |
| 错 | `cuo` | `YiInstr` | cur.1 ← Hexagram.cuo cur.1 |
| 综 | `zong` | `YiInstr` | cur.1 ← Hexagram.zong cur.1 |
| 比爻 | `branchYaoEq (i j : Fin 6) (t : Nat)` | `Fin 6 → Fin 6 → Nat → YiInstr` | if y_i = y_j then pc ← t else pc ← pc+1 |
| 比时 | `branchShiEq (s : Shi) (t : Nat)` | `Shi → Nat → YiInstr` | if cur.2 = s then pc ← t else pc ← pc+1 |
| 跳 | `jump (t : Nat)` | `Nat → YiInstr` | pc ← t |
| 推 | `push` | `YiInstr` | history ← cur :: history |
| 取 | `pop` | `YiInstr` | (cur, history) ← head/tail history (∅ ⇒ halt) |
| 终 | `halt` | `YiInstr` | halted ← true |

```
Carrier:
  Hexagram        := Yao⁶                                (Yi.lean)
  Shi             := { ji, jin, wei }                    (Cell192.lean)
  Cell192         := Hexagram × Shi                      (Cell192.lean)
  YiState         := { cur, history, pc, prog, halted }  (BaguaTuring.lean)

Frozen surface tokens (BaguaWenSpec.lean § reservedTokens, |·| = 22):
  primaryTokens   = [不动 设时 翻爻 互 错 综 比爻 比时 跳 推 取 终]   (12)
  shiTokens       = [已 今 未]                                       (3)
  yaoTokens       = [初爻 二爻 三爻 四爻 五爻 上爻]                  (6)
  atKeyword       = [至]                                             (1)

Numeral range: 1..64 (parseNumeral covers full range; round-trip witnessed
on numeralRange = (List.range 64).map (·+1)).
```

#### Expressive ceiling

```lean
theorem sheng_not_cuo_equivariant :
    ¬ ∃ (p : List YiInstr) (init : Hexagram),
        ∀ h : Hexagram, runHex p init h = h.shengSucc
-- Foundation/Wen/WenDefCompile.lean
-- The 12-instr ISA cannot compute non-cuo-equivariant Hex→Hex functions.
-- «生», «一» are structurally unreachable; Hex→Hex computability ceiling = cuo-equivariance.
```

### 3.2 L1 — Typed Lambda Layer (`Foundation/Wen/WenDef.lean § Tm`)

```lean
inductive Ty  | hex | bool | arr (dom cod : Ty)
inductive Tm
  | var | abs | app | hexLit | boolLit
  | jia    -- 加  : Hex → Hex → Hex
  | yi     -- 一  : Hex
  | notB   -- 不  : Bool → Bool
  | andB   -- 並  : Bool → Bool → Bool
  | orB    -- 或  : Bool → Bool → Bool
  | eqHex  -- 同  : Hex → Hex → Bool
  | forallH -- 凡 : (Hex → Bool) → Bool        (64-fold ∧, decidable)

typeCheck : Ctx → Tm → Option Ty                        -- total
eval      : Tm → Tm                                      -- structural
```

### 3.3 Operator catalogue — 371 OperatorId rows

L1 type-layer is in `WenDef.lean § Stdlib` (representative constructors:
{tui, bi, bu, biModal, tong, fan, sun, yiBenefit, cuo, zong, hu, fanReverse,
imp, neqHex, existsH, noneH, endoComp}); a subset of the surface particles
(之 / 者 / 而 / 也 / 不 / 凡 / 自 / 相 / 似 / 要 etc.) is named in
`Foundation/Wen/Operators.lean` with ASCII aliases. The full 371-OperatorId
catalogue is machine-tracked in `Text/WenyanOperators.lean` and `Text/OperatorCellMap.lean`.
WenSurface exposes all 371 rows as executable entries: 33 rows have exact
theorem-backed Hex/Bool denotation, and the rest evaluate to symbolic
`Catalogue[...]` normal forms.

### 3.4 受控文言 (Controlled Wenyan, M1 grammar)

```ebnf
程       ::= 句*
句       ::= 命 sep
sep      ::= "；" | ";"
命       ::= 不动 | 互 | 错 | 综 | 推 | 取 | 终
           | 设时 时
           | 翻爻 爻
           | 比爻 爻 爻 至 数
           | 比时 时 至 数
           | 跳 至 数
时       ::= 已 | 今 | 未
爻       ::= 初爻 | 二爻 | 三爻 | 四爻 | 五爻 | 上爻
数       ::= ⟨1..64⟩
```

Round-trip witness:

```lean
theorem daoJudgeProg_roundtrip :
    «解程» («印程» daoJudgeProg) = some daoJudgeProg     -- by native_decide

theorem testPrograms_roundtrip :
    testPrograms.all (fun p => «解程» («印程» p) = some p) = true
                                                          -- by native_decide
```

---

## 4 · Module Path → Theorem (Compressed Inventory)

### 4.1 Foundation/Yi (algebra of 易)

```
Yi.lean             v4_orders, hu_fixed_point, oplus_not_comm, pi_ne_tai
YiCore.lean         «微核之至», «周而复始», «生生不息», «法即卦», «道生一也»
```

### 4.2 Foundation/Bagua (192 / Turing / Gödel)

```
Cell192.lean              all_length = 192, mem_all (exhaustion)
BaguaAlgebra.lean         Boolean algebra of trigrams + V₄ orders
BaguaTuring.lean          daoJudge_correct, loopProg_unbounded (TC witness)
BaguaWenSpec.lean         reservedTokens.length = 22, primaryToken_in_primaryTokens
GodelLi.lean              halts_undecidable_internally; kleene_recursion_axiom (cuo-restricted)
KleeneInternal.lean       kleene fixpoint internalized
Newman.lean               Newman's lemma local form
CuoInvariance.lean        cuo-equivariance machinery (CuoInvariantDecide etc.)
ChunkedDecide.lean        decision-procedure budget framework
FuelDiscipline.lean       runFuel monotonicity + fuel-extension lemmas
```

### 4.3 Foundation/Wen (path 丙: self-compilation, self-validation)

```
BaguaWenSpec → WenyanParser → WenyanParserGeneral
              ↘             ↘
                WenEval → WenDef → WenDefEval → WenDefCompile
                       ↘                              ↘
                         WenyanSyntax → WenyanReflect → WenyanSelfHost → DaoSource
                                                    ↘                     ↘
                                                      WenyanSelfInterp     Demo
                                            ↘
                                            AntiSchmitt, AlignmentFailures, EconGame

WenyanParser.lean         daoJudgeProg_{print,roundtrip}, allKindReprs_singleton_roundtrip
WenyanParserGeneral.lean  parseProgN_tokensOfProg (full generality, non-partial)
WenEval.lean              «端到端_乾», «端到端_坤», «端到端_否»
WenDef.lean               typeCheck total + 17-body Stdlib (core Hex/Bool + logic aliases)
WenDefEval.lean           tui_eq_sheng + exact Hex transforms + promoted logic examples
WenDefCompile.lean        {idProg, add32Prog, cuoProg}_correct, sheng_not_cuo_equivariant
WenyanReflect.lean        «文核同源» (rfl), «判型良»/«判停»/«验程»
WenyanSelfHost.lean       «微核自验», «微核自释_total» (Tier 2 quine PoC)
DaoSource.lean            «道之自指» (form / parse / print / halt / semantics 5-fold)
Demo.lean                 daojudge_{qian, kun, pi, tai}
Kernel.lean               45-layer doctrine in-source
AntiSchmitt.lean          friend-enemy / decisionism / exception ⊨ ¬universalizable
AlignmentFailures.lean    Goodhart / mesa / wireheading ⊨ Kernel-invariant violation
EconGame.lean             coase_internalizes_externality, prisoners_dilemma_refuted_under_tongGen
```

### 4.4 Foundation/Core (alignment / sincerity / human / community)

```
Yuan.lean                Yuan := Yao; yi := Yao.neg; 元/爻/易 identifications
Monism.lean              proof-principle: 一切回 一; explicit (no Lean axiom)
MonadRoot.lean           single-root proof-shape lemmas
AtomDerivation.lean      every AtomName ∈ allAtoms (decide)
ShengshengBuxi.lean      ShengshengBuxi 主公示
Alignment.lean           T1–T6: ProcessAligned + Open → Dao → ShengshengBuxi; ShengshengBuxi → Dao; Denier 自毁
Sincerity.lean           T1–T8: 信/诚 = alignment(化(T), 化(E)) + 反诛心五律
HumanAlignment.lean      structure HumanDefinition / DoingHumanDefinition; 12 stages
Attention.lean           注意机制 5 components (动态权重分配/门控/维持/转焦/抑制)
EvolutionDao.lean        scale/value/reflexive 三视: σ_F ⊉ Σ_真道
Renlei.lean              «人类命运共同体_之证» (3-axis CommunityState, iff-aligned)
Li.lean                  理之分层
MissingGlyphs.lean       missing-character coverage
MathAxiomMap.lean        ZFC↔SSBX axiom mapping
```

### 4.5 Foundation/Eight (eight expansions)

```
ShuSuan.lean             algebra of computation
LuoJi.lean               logic / deduction
TongJi.lean              statistics
XingWei.lean             geometric position
LeiYing.lean             category / isomorphism
DongLi.lean              dynamics / ODE
XinZhi.lean              mind / neuroscience
WuXiang.lean             physics / quantum
```

### 4.6 Foundation/Modern (Mathlib bridge)

```
RCauchy / RCauchyExt          Real Cauchy-completeness
Kolmogorov / KolmogorovExt    Kolmogorov measure
Lebesgue / LebesgueDepth      MCT / DCT / Fubini
ODESmoothness                 ODE smoothness
PicardLindelofGen / BochnerPL Picard-Lindelöf (incl. Mathlib instance)
NaturalDeduction              K3/NK collapse + Curry-Howard
Quantum / SUN                 quantum mechanics + SU(N)
Neuro                         neuroscience integration
HexagramPosition              中/应/比/当位/承乘
CatExt / CatOp / YonedaFull   category theory + Yoneda functor
IIDWlln                       WLLN (Chebyshev + IID-aware)
DaoLi                         道-理 bifurcation, cross-cutting
```

---

## 5 · Headline Theorems (one-liner statements)

```lean
-- A. micro-kernel
theorem «微核之至»    : YiCore covers 64 hexagrams in ≤ 64 steps      (YiCore.lean)
theorem «生生不息»    : ∀ h₁ h₂ : Hexagram, ∃ n < 64, step^n h₁ = h₂  (YiCore.lean)

-- B. 易 algebra
theorem v4_orders     : ∀ h, h.cuo.cuo = h ∧ h.zong.zong = h ∧ h.cuoZong.cuoZong = h
theorem hu_fixed_point: h.hu = h ↔ h = qian ∨ h = kun

-- C. Turing-completeness
theorem loopProg_unbounded : ∀ n, ¬ (...runFuel n...).halted = true   (BaguaTuring.lean)

-- D. Gödel-Li
theorem halts_undecidable_internally :
    ¬ ∃ (decide : List YiInstr → Hexagram → Bool),
        ∀ P h, decide P h = true ↔ Halts P h                          (GodelLi.lean)

-- E. cuo-equivariance ceiling
theorem sheng_not_cuo_equivariant : ¬ ∃ p, runHex p init = sheng       (WenDefCompile.lean)

-- F. self-host (Tier 2 quine PoC)
theorem «微核自验» :
    «判型良_basic» «微核源» = true ∧
    ProgEnc.decInstrs «微核源».length «微核数» = some («微核源», [])    (WenyanSelfHost.lean)
theorem «微核自释_total» :
    ∀ h, ((YiState.init h «微核源»).runFuel 200).halted = true

-- G. dao source (5-fold self-reference)
theorem «道之自指» :
    («判型良» «道程» = true) ∧
    («解程» «道源» = some «道程») ∧
    («印程» «道程» = «道源») ∧
    (∀ h, ((YiState.init h «道程»).runFuel 64).halted = true) ∧
    (∀ h, ((YiState.init h «道程»).runFuel 64).cur.2 = .ji ↔ h.y3 = h.y4)
                                                                       (DaoSource.lean)

-- H. alignment
theorem process_alignment_dao_shengshengbuxi_summary
    : (ProcessAligned + Open → Dao) ∧ (Dao → ShengshengBuxi) ∧
      (ShengshengBuxi → Dao)                                                   (Alignment T2)
theorem denier_breaks_shengshengbuxi
    : Denier.policy 之 step 破 ShengshengBuxi                                  (Alignment T3)

-- I. sincerity (anti-conjecture)
theorem sincerity_main_theorem : T1 ∧ T2 ∧ T3 ∧ T4 ∧ T5 ∧ T6 ∧ T7 ∧ T8        (Sincerity.lean)

-- J. human community
theorem «人类命运共同体_之证» :
    (∃ g, TrueDao communityModel communityDao communityPath g) ∧
    (∃ g, ¬ TrueDao ...) ∧
    (∀ g, TrueDao ... ↔ g = aligned) ∧
    ((entryOf (R .«道»)).deps = [G .«正续», R .«共开», G .«夺共续», R .«坏»])
                                                                       (Renlei.lean)

-- K. dao-li bifurcation
theorem dao_proves_about_li : ¬ ∃ decide, ∀ P h, decide P h = true ↔ Halts P h
theorem li_cannot_encode_dao : ∀ N, ∃ n > N, Nonempty (Sheng n)        (DaoLi.lean)
```

---

## 6 · Build Invariants

```
∀ commit ∈ main:
  lake build                  ⇒  smoke target exit 0
  lake build SSBX             ⇒  full library exit 0
  count(sorry, formal/)       =  0
  count(axiom, formal/)       =  1          (kleene_recursion_axiom; cuo-restricted)
  count(opaque, formal/)      =  1          (theOne; carries Field/dong/origin/alive)
  count(partial def, formal/) =  1          (YiState.run)
```

### 6.1 Continuous regression check

```bash
$ lake build SSBX                           # full library
$ lake build +SSBX.Foundation.Wen.DaoSource # single module
$ scripts/generate_monad_dag.py             # regen «一»-DAG
$ scripts/render_monad_dag.sh               # render to SVG
```

### 6.2 New module checklist

```
☐ axiom count unchanged (= 1)
☐ opaque count unchanged (= 1)
☐ sorry count = 0 in this file
☐ all theorems machine-witnessed (native_decide / by exact / by rfl / by induction)
☐ added to formal/SSBX.lean import index
☐ if Roster-touching: regen MonadDAG.mmd, MonadTree.txt, ConceptDAG*.{mmd,svg}
```

---

## 7 · Cross-Reference Index

```
Doctrine layer → Lean module          Foundation/Wen/Kernel.lean § Layer N
Lean module → doctrine layer          Wen/Kernel.lean inverse (in-source comments)
AtomName → registry entry             Roster.lean § entryOf
GenName → roots + deps                Roster.lean § rootsOfGenerated, depsOfGenerated
RecName → recursive semantics         Roster.lean § recDeps, recSemOf
PrimName / PendingName                Roster.lean § allPrimitives, allPending

Surface wenyan → 12-instr ISA          Foundation/Wen/WenyanParser.lean § parseInstr
ISA → wenyan                          same § printInstr
Tm → ISA (cuo-equivariant subset)     Foundation/Wen/WenDefCompile.lean
ISA → YiState transition              Foundation/Bagua/BaguaTuring.lean § execute / step / runFuel
Cell192 ↔ List Cell192 (encoding)     Foundation/Wen/WenyanSelfInterp.lean § ProgEnc
```

---

## 8 · Two Conjectures (out-of-scope, marked)

Documented in prose at `README.md § 9.2 / 9.3` and `README.en.md § 9.2 / 9.3`.

```
ConjOne   Dao-attainability via reading-and-recitation
          not formally claimed; compatible with proven kernel

ConjTwo   大同 (Great Concord) as historical residue
          not formally claimed; tongGen-favoring environment
          consistent with EconGame.lean § coase_internalizes_externality
```

Scope sieve:

| Status | Included | Excluded |
|---|---|---|
| machine-proven | closed Lean declarations accepted by the build, under the trust base in §1 and the executable boundary above | prose extrapolations; ledger sync claims; the six pending interfaces |
| ledger-dependent | generated DAG / roster summaries, operator counts, layer-to-essay mappings, module counts, and cross-volume correspondences | not single closed theorems unless separately named by a Lean declaration |
| pending | §§ 2.4.3 six `PendingName` interfaces awaiting empirical calibration | not used as established truth |
| conjecture | ConjOne / ConjTwo and the historical or practice claims in prose | no Lean term inhabits these |

The reality-scope claim in `README.md § 9.1` / `README.en.md § 9.1` is a
defended philosophical extrapolation from machine-proven invariants plus
ledger-dependent correspondences. It is not a theorem named by this formal
specification.

---

## 9 · Ledger

```
Foundation Lean LOC       ~33000+ across 97 Foundation modules (7 clusters)
Foundation/Core modules   14    (incl. Alignment, Sincerity, HumanAlignment, EvolutionDao, Renlei)
Foundation/Wen modules    38    (incl. WenSurface, DaoSource, AntiSchmitt, AlignmentFailures, EconGame)
Foundation/Modern modules 19    (~5746 lines, Mathlib bridge)
Path-丙 modules           11    (M1 → M4-甲)
Kernel layers             45    (元 → 非道之形式)
义理 essays               28+   (义理/A_..Z_*.md, plus 人类命运共同体_共同体之证.md)
六表 tables               6     (六表_实虚史真/)
wenyan operators          371   (`Text/WenyanOperators.lean` OperatorId catalogue)
```

```
trust:    Lean kernel (v4.30.0-rc2) + Mathlib HEAD
machine:  2917 build jobs · 0 sorry · 1 axiom (kleene_recursion_axiom; cuo-restricted)
opaque:   1 (theOne)
partial:  1 top-level executable partial def (BaguaTuring.run nontermination boundary)
ledger:   DAG / roster / operator / layer / essay correspondences are sync claims
pending:  6 PendingName interfaces
conj:     ConjOne / ConjTwo, no Lean term claimed
boundary: cuo-equivariance ceiling, universal-compileTm undefinable
          (halts_cuo_invariant + unrestricted_kleene_inverter_inconsistent),
          halting-undecidability, dao-li bifurcation
```

— *EOF · this is a specification, not an introduction. For prose, see `README.md` (中文) or `README.en.md` (English).*
