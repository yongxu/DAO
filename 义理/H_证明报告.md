# H · v3 证明状态报告 · R₀..R₈ strict (Z/2)ⁿ + V₄ Shi at R₈

> 状态：v3 重写 (2026-05-11) — pre-v3 版本（Cell192 时代之 BaguaAlgebra 75 定理报告）已归档至 `史/义理-pre-v3/`。

**报告范围**：R₀..R₈ strict (Z/2)ⁿ uniform + V₄ Klein Shi at R₈，从 BaguaAlgebra 之 R₃ 75-定理底盘升级到 R₈ Cell256 闭合层之完整 algebraic spine + 11 项完整性审计。

**主 HEAD**：main @ commit `1c76a55` (post-V₄-Shi-migration); `lake build SSBX` 通过 **3656 jobs**，0 sorry / 0 项目自定义 axiom（仅 Lean 标准 propext + native_decide），唯一项目 axiom `kleene_recursion_axiom` 在 KleeneInternal.lean / GodelLi.lean 之动力层（与静态 (Z/2)⁸ closure 正交）。

---

## 〇 · 摘要

| 维度 | 数值 |
|---|---|
| 总 lake build jobs | **3656** ✓ |
| Foundation/{Bagua,Hierarchy,Notation,Yi,Wen,Eight,Core,Jian,...} 总规模 | ~12000 行 Lean |
| 0 sorry | ✓ (across all migrated files) |
| 项目自定义 axioms | 1 (kleene_recursion_axiom 仅在 GodelLi/KleeneInternal) |
| Lean 标准 axioms 依赖 | propext, native_decide |
| 公开主定理 (proven) | A, B, C, D, E, F, H, I, J, K + Cell256OperatorComplete + ~ 30 sub-theorems |
| Phase A 之 (Z/2)⁷/(Z/2)⁸ AddCommGroup + Cayley | Phase A `cell{128,256}_phaseA_summary` |
| R8_complete 11-item closure bundle | ✓ (Cell256Stratify.lean) |

---

## 一 · Phase A — R₇/R₈ Algebraic Spine ✓

R₇ Cell128 + R₈ Cell256 现在带 (Z/2)⁷/(Z/2)⁸ Abelian 群结构 + Cayley 自对偶 + 印/投 mask XOR 形式。

### 1.1 Cell128 (R₇) Phase A — `formal/SSBX/Foundation/Bagua/Cell128.lean`

**已证**：

| 定理 | 内容 |
|---|---|
| `Cell128.all_length` | `Cell128.all.length = 128` (native_decide) |
| `Cell128.mem_all` | every Cell128 ∈ all (exhaustion) |
| `Cell128.origin_xor` | `xor origin c = c` (left identity) |
| `Cell128.xor_origin` | `xor c origin = c` (right identity) |
| `Cell128.xor_self` | `xor c c = origin` (self-inverse, (Z/2)⁷ property) |
| `Cell128.xor_comm` | commutativity |
| `Cell128.xor_assoc` | associativity |
| `Cell128.cayley_inj` | `Function.Injective Cell128.cayley` |
| `Cell128.epsAtOrigin_cayley` | `ε ∘ ι = id` (Cayley retraction) |
| `Cell128.cayley_hom` | `cayley (a + b) = cayley a ∘ cayley b` (group hom) |
| `Cell128.yinM_eq_yin` | mask-form 印 = legacy direct toggle |
| `Cell128.yinM_yinM` | 印 involution (mask 自抵) |
| `Cell128.yin_yin` | legacy 印 involution |
| `cell128_phaseA_summary` | bundle of 7 Phase A properties |

**Lean instance**：
```lean
instance : Add Cell128 := ⟨Cell128.xor⟩
instance : Zero Cell128 := ⟨Cell128.origin⟩  -- = (Hexagram.qian, false) = (Z/2)⁷ identity
instance : Neg Cell128 := ⟨id⟩               -- (Z/2)ⁿ self-inverse
instance : Sub Cell128 := ⟨Cell128.xor⟩
instance : SMul Cell128 Cell128 := ⟨Cell128.xor⟩
```

### 1.2 Cell256 (R₈) Phase A — `formal/SSBX/Foundation/Bagua/Cell256.lean`

**已证**：

| 定理 | 内容 |
|---|---|
| `Cell256.all_length` | `Cell256.all.length = 256` (native_decide) |
| `Cell256.all_nodup` | no duplicates |
| `Cell256.mem_all` | exhaustion |
| `Cell256.origin_xor` / `xor_origin` | identity laws |
| `Cell256.xor_self` | (Z/2)⁸ self-inverse |
| `Cell256.xor_comm` / `xor_assoc` | abelian group laws |
| `Cell256.cayley_inj` | Cayley injection |
| `Cell256.epsAtOrigin_cayley` | retraction ε ∘ ι = id |
| `Cell256.cayley_hom` | group hom |
| `Cell256.yin_yin` / `tou_tou` | 印 / 投 involutions (mask self-inverse) |
| `Cell256.yin_tou_comm` | 印 与 投 交换 |
| `Cell256.yin_tou_eq_central` | 印 ∘ 投 = (qian, jin) = V₄ central element |
| `Cell256.yin_mask_xor_tou_mask` | yin_mask ⊕ tou_mask = (qian, jin) |
| `cell256_phaseA_summary` | bundle of 9 Phase A properties |

**Lean instance**：
```lean
instance : Add Cell256 := ⟨Cell256.xor⟩
instance : Zero Cell256 := ⟨Cell256.origin⟩  -- = (Hexagram.qian, Shi.dao) = OX["oooooooo"] = 道
instance : Neg Cell256 := ⟨id⟩
instance : Sub Cell256 := ⟨Cell256.xor⟩
instance : SMul Cell256 Cell256 := ⟨Cell256.xor⟩
```

**关键**：`Cell256.origin = (Hexagram.qian, Shi.dao)` — 即 `OX["oooooooo"]` — 同时是：
- (Z/2)⁸ identity element
- Cell256.cayley 之 origin (任 c 满足 `cayley c origin = c`)
- (qian, dao) cell — 道作为 R₈ identity = 永真 anchor
- Shi.dao 是 V₄ 单位元 (per Shi.toYinGuo (false, false))

道之**五重身份**（per yi-RO-hierarchy.md §5.6）—  origin / identity / no-op / 永真 cell / fusion anchor — 由 `Cell256.origin` 一个 Lean def 同时承担。

### 1.3 Shi V₄ Klein 群 — `Cell256.lean` § 1

**已证**：

| 定理 | 内容 |
|---|---|
| `Shi.all_length` | `[dao, ji, jin, wei].length = 4` |
| `Shi.cuo_cuo` | cuo² = id (V₄ involution) |
| `Shi.zong_zong` | zong² = id |
| `Shi.cuoZong_cuoZong` | cuoZong² = id |
| `Shi.cuo_zong_comm` | cuo ∘ zong = zong ∘ cuo (V₄ abelian) |
| `Shi.cuoZong_eq_compose` | cuoZong = cuo ∘ zong |
| `Shi.toYinGuo` / `ofYinGuo` | bijection to (Bool × Bool) |
| `Shi.ofYinGuo_toYinGuo` / `toYinGuo_ofYinGuo` | round-trip |
| `Shi.yin_yin` / `tou_tou` | legacy yin/tou (= Shi.cuo / Shi.zong) involutions |
| `Shi.yin_tou_eq_cuoZong` | yin ∘ tou = cuoZong (V₄ central) |

**关键事实**（Theorem J, per yi-calculus-theorem.md）：

> Shi V₄ = {道, 已, 今, 未} 不是 R₇ 单层 atom，是 R₇ (因 axis) ⊗ R₈ (果 axis) 双层 emergence。Shi.toYinGuo 双射给出此 emergence 之精确实现。

---

## 二 · Phase F — Migration to V₄ Shi (Cell192 → Cell256) ✓

旧 Cell192 = Hexagram × Z/3 (Z/3 cyclic Shi {已, 今, 未}) 之深层 bug：

- 丧失 V₄ 单位元 (道) → R-hierarchy (Z/2)ⁿ 自相似性破坏
- 把第二维强行编为 Z/3 → 与 (Z/2)⁸ closure 不相容

V₄ Shi migration (commits `7de5064` + `0003224`, 2026-05-10) 把 Cell192 整体替换为 Cell256，覆盖 ~80 个文件：

| 文件 | 状态 |
|---|---|
| `Cell192.lean` (deprecated) → `Cell256.lean` (new) | ✓ |
| `Cell192Stratify.lean` → `Cell256Stratify.lean` | ✓ |
| `BaguaTuring.lean` (YiInstr.setShi 4 case) | ✓ (Phase F.2 migration note 在文件头) |
| `GodelLi.lean` (Halts on Cell256) | ✓ |
| `KleeneInternal.lean` | ✓ |
| `OperatorCellMap.lean` (371 × 256 = 94976) | ✓ |
| `Truth/SelfDescription.lean` (Cell256OperatorComplete) | ✓ |
| `MetaInterp/*` (Shi 4 case dispatch) | ✓ |

**Migration 不变量**:
- 0 sorry 增加（所有迁移文件保持 0 sorry）
- 0 axiom 新增
- `lake build SSBX` 干净通过 3656 jobs
- 命名一致：`Cell192` 在所有 active code 中已替换为 `Cell256`

---

## 三 · Phase G — Foundation Theorems (A through K) ✓

### 3.1 Theorem A — R₃ 4本 + 4征 partition

**Lean**: `formal/SSBX/Foundation/Bagua/BenZheng.lean`

```lean
theorem Ben.all_count : Ben.all.length = 4
theorem Zheng.all_count : Zheng.all.length = 4
theorem cuo_preserves_isZongFixed : ∀ t, Trigram.zongFixed (Trigram.cuo t) = Trigram.zongFixed t
theorem ben_zheng_partition_complete : ...
```

**结果**：R₃ 之 (Z/2)³ 在 zong-orbit 下唯一 4+4 划分；本 = palindromic (zong-fixed)，征 = directional (zong-mobile)。

### 3.2 Theorem B — substrate = 定常波

**Lean**: 同上 `BenZheng.lean`

substrate = `{y : δ(y) = 0}` (boundary-preserving)：乾坤是 DC component (zero mode)；离坎是 Nyquist mode (highest frequency)。4 个 substrate trigram = 离散三点 Fourier basis 之 4 stationary waves。

### 3.3 Theorem C — mark = phase plane 4 quadrant

**Lean**: 同上 `BenZheng.lean`

mark = phase coordinate $\phi(y) = (\delta(y), S(y))$ 之 4 quadrant representative；巽 / 震 / 兑 / 艮 各占一象限，对应谐振子 4 phase。

### 3.4 Theorem D — V₄ 与物理 P/T/PT 同构

**Lean**: `Foundation/Bagua/BaguaAlgebra.lean` + `Foundation/Hierarchy/Operators/V4Outer.lean`

`{e, R, N, RN}` ≅ V₄ Klein 四群；
- N (cuo) = parity (P)
- R (zong) = time-reversal (T)  
- NR (错综) = PT

### 3.5 Theorem E — substrate–mark = ∫–d 划分

**Lean**: `BenZheng.lean` (`δ`-zero ↔ ben partition)

离散 Newton-Leibniz duality：substrate ($\delta = 0$) = 积分饱和；mark ($\delta \neq 0$) = 导数主导。

### 3.6 Theorem F — R₆ 4 quadrant 强制分解

**Lean**: `BenZheng.lean`

```lean
theorem Hexagram.quadrant_partition_complete : ...
theorem Hexagram.quadrant_count_each : ∀ q : Quadrant, |hex_in q| = 16
theorem zong_quadrant : zong 在 4 quadrant 上之具体 mapping (本本/征征 自闭, 本征↔征本)
```

64 = 16 (本本) + 16 (本征) + 16 (征本) + 16 (征征)；cuo 保 quadrant；zong 跨换 mixed quadrants。

### 3.7 Theorem G — 与连续 1D 标量场对应

**状态**: informal (no Lean form — meta-mathematical correspondence to ℝ-valued continuous fields)

8 trigram = 离散 1D scalar field 在 3 sample 下之 sign-pattern complete enumeration。

### 3.8 Theorem H — R₇ = (Z/2)⁷ = 128 + 因 axis ✓

**Lean**: `Foundation/Bagua/Cell128.lean`

```lean
abbrev Cell128 : Type := Hexagram × YinBit
theorem Cell128.all_length : all.length = 128 := by native_decide
def Cell128.yin (c : Cell128) : Cell128 := (c.1, !c.2)  -- toggle 因
theorem Cell128.yin_yin : ∀ c, yin (yin c) = c
```

R₇ 引入第 7 个 binary axis = 因 (yīn, past-trace bit)；Cell128 是 (Z/2)⁷ self-action group。

### 3.9 Theorem I — R₈ = (Z/2)⁸ = 256 + 果 axis ✓

**Lean**: `Foundation/Bagua/Cell256.lean`

```lean
abbrev Cell256 : Type := Hexagram × Shi   -- Shi V₄ = (因, 果) ∈ Bool²
theorem Cell256.all_length : all.length = 256 := by native_decide
```

R₈ 引入第 8 个 binary axis = 果 (guǒ, future-projection bit)；Cell256 = (Z/2)⁸ = 1-byte cardinality。

### 3.10 Theorem J — Shi V₄ emergence at R₈ ✓

**Lean**: `Foundation/Bagua/Cell256.lean` (`Shi.toYinGuo` 双射)

```lean
def Shi.toYinGuo : Shi → YinBit × GuoBit
  | .dao => (false, false)  -- V₄ identity
  | .ji  => (true,  false)
  | .wei => (false, true)
  | .jin => (true,  true)
theorem Shi.ofYinGuo_toYinGuo : ∀ s, ofYinGuo (toYinGuo s) = s
theorem Shi.toYinGuo_ofYinGuo : ∀ yg, toYinGuo (ofYinGuo yg) = yg
```

Shi V₄ = R₇ ⊗ R₈ 双 axis 之 emergent 4-state；不是单层 atom。**道 = (因=0, 果=0) = V₄ identity** = 永真 anchor first-class 入本体。

### 3.11 Theorem K — R₀..R₈ strict (Z/2)ⁿ closure ✓ (`R8_complete`)

**Lean**: `formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`

```lean
abbrev R0 := Unit
abbrev R1 := Yao
abbrev R2 := SiXiang
abbrev R3 := Trigram
abbrev R4 := Mian        -- = Ben × Zheng = (Z/2)⁴ = 16
abbrev R5 := Mian × Bool -- (provisional 五爻) = (Z/2)⁵ = 32
abbrev R6 := Hexagram    -- = (Z/2)⁶ = 64
abbrev R7 := Cell128     -- = (Z/2)⁷ = 128
abbrev R8 := Cell256     -- = (Z/2)⁸ = 256

theorem R0_card_eq_1 / R1_card_eq_2 / ... / R8_card_eq_256
theorem R8_complete : ⟨R0..R8 strict uniform + V₄ + Cayley + Lift/Project + 道 anchor⟩
```

11-item completeness checklist (per yi-RO-hierarchy.md §6.2)，全部 ✓ (详 K_完备性审计.md)：

1. 元枚举（256 cells 全枚举）
2. 元的群结构 ((Z/2)⁸ abelian)
3. XOR subgroup 的 Aut (8 atomic generators 完整)
4. Cayley 自对偶 (ι 同态 + ε 对偶)
5. Reachability (simply transitive)
6. Decidability (finite props)
7. V₄ on each R-layer (R₃+)
8. hu fixed points / cycles ({乾, 坤, 既济, 未济})
9. 道之三重身份 (origin = identity = no-op = 永真)
10. Pontryagin self-duality
11. R-O frame duality (Schrödinger ↔ Heisenberg)
+ Theorem K (strict uniform progression, 每步 +1 bit)

### 3.12 Cell256OperatorComplete — Truth-side self-description ✓

**Lean**: `formal/SSBX/Truth/SelfDescription.lean`

```lean
theorem Cell256OperatorComplete : ⟨...⟩
-- V₄ extension of legacy 192-cell self-description:
-- R₈ Cell256 = 256 cells, 8 atomic XOR generators + V₄ outer, fully describes its own structure.
```

R₈ 之 self-description witness：(Z/2)⁸ closure 配上 Cayley fusion 让系统能描述自身的所有变换 (per yi-as-meta-framework.md §1)。

---

## 四 · Phase C — Hierarchy Infrastructure ✓

### 4.1 R-hierarchy umbrella — `Foundation/Hierarchy/RHierarchy.lean`

```lean
import SSBX.Foundation.Hierarchy.R0_Taiji
import SSBX.Foundation.Hierarchy.R1_Yao
import SSBX.Foundation.Hierarchy.R2_SiXiang
import SSBX.Foundation.Hierarchy.R3_Trigram
import SSBX.Foundation.Hierarchy.R4_Mian
import SSBX.Foundation.Hierarchy.R5_Wuyao
import SSBX.Foundation.Hierarchy.R6_Hexagram
import SSBX.Foundation.Hierarchy.R7_YinHex
import SSBX.Foundation.Hierarchy.R8_GuoHex
import SSBX.Foundation.Hierarchy.LiftProject
import SSBX.Foundation.Hierarchy.Operators.Atomic
import SSBX.Foundation.Hierarchy.Operators.V4Outer
```

### 4.2 R₅ Wuyao — `Foundation/Hierarchy/R5_Wuyao.lean`

```lean
abbrev Wuyao := Mian × Bool
def Wuyao.all : List Wuyao := ...  -- 32 元
theorem Wuyao.all_length : all.length = 32
def Wuyao.flip5 : Wuyao → Wuyao
theorem Wuyao.flip5_flip5 : ∀ w, flip5 (flip5 w) = w  -- involution
```

R₅ 之 (Z/2)⁵ = 32 carrier；provisional naming (无传统 Yi anchor)。候选: 接 / 临 / 渐 / 进，详 yi-RO-hierarchy.md §3.5。

### 4.3 Uniform Lift / Project — `Foundation/Hierarchy/LiftProject.lean`

8 R-layer pairs，每对带 retract 引理：

```lean
def liftR0 : R0 → Bool → R1 := ...
def projR0 : R1 → R0 := ...
theorem proj_lift_id_R0 : ∀ a b, projR0 (liftR0 a b) = a
-- ... R1..R7 各一对
def liftR7 : R7 → Bool → R8 := ...
def projR7 : R8 → R7 := ...
theorem proj_lift_id_R7 : ∀ c g, projR7 (liftR7 c g) = c
```

### 4.4 Atomic / V₄-outer Operators

`Foundation/Hierarchy/Operators/Atomic.lean` — 8 atomic XOR generators (re-export)
`Foundation/Hierarchy/Operators/V4Outer.lean` — zong / hu / cuoZong (non-XOR permutations)

### 4.5 OX 字面 macro — `Foundation/Notation/OXNotation.lean`

```lean
syntax (name := oxLiteral) "OX[" str "]" : term
-- OX["xxxxxxxx"] : Cell256 = (kun, jin) = "all-yin, present-time"
-- OX["oooooooo"] : Cell256 = (qian, dao) = 道 = origin
```

8-char `o`/`x` string → Cell256 literal；位置 0..5 = yao (内→外)，位置 6 = YinBit (因)，位置 7 = GuoBit (果)。

---

## 五 · Build & 检验

### 5.1 lake build 状态

```bash
$ lake build SSBX
✔ ... 3656/3656 ...
Build completed successfully (3656 jobs).
```

- 0 sorry across migrated files
- 0 项目自定义 axioms in static layer (Cell{128,256}, Cell256Stratify, BenZheng, BaguaAlgebra, Hierarchy/*)
- 仅 Lean 标准 axioms: `propext`, `native_decide`
- 唯一项目 axiom: `kleene_recursion_axiom` 在动力层 (GodelLi.lean / KleeneInternal.lean) — captures Church-Turing 论题对 BaguaTuring 之应用，与静态 (Z/2)⁸ closure **正交**

### 5.2 检验命令

```bash
# Verify no sorry in migrated files:
$ rg "sorry" formal/SSBX/Foundation/Bagua/Cell{128,256,256Stratify}.lean
# (no matches expected)

# Verify Phase A summary bundles type-check:
$ lake env lean -e 'open SSBX.Foundation.Bagua.Cell256 in #check @cell256_phaseA_summary'

# Verify R8_complete bundle:
$ lake env lean -e 'open SSBX.Foundation.Bagua.Cell256Stratify in #check @R8_complete'
```

---

## 六 · 待办 (Pending)

| # | 任务 | 状态 | 备注 |
|---|---|---|---|
| P1 | Phase B.2 — Shi → Bool×Bool abbrev cleanup | 待 | Shi 之 inductive 4 ctor + Shi.toYinGuo 双射；可考虑改为 abbrev `Shi := Bool × Bool` 减少 cases，但损失 named constructors |
| P2 | WenyanSelfInterp base-256 dispatch re-derivation | 待 | 旧 base-192 dispatch 在 V₄ migration 后需要 re-derive；MetaInterp 已从 3-case 升 4-case |
| P3 | R₅ 五爻 final naming 定案 | 待 | provisional "五爻"; 候选 接/临/渐/进 — 详 yi-RO-hierarchy.md §3.5 |
| P4 | 因/果 / 印/投 命名 final 定案 | 待 | provisional 因/果 (state) / 印/投 (action); 备选 始/终 (Yi-native), 持/期 (Husserl) — 详 yi-calculus-theorem.md §16 |
| P5 | 去除 kleene_recursion_axiom | 待 (≈500 行 Lean) | 需在 YiInstr 显式构造 quine + universal interpreter; KleeneInternal.lean 已 sketch path-to-zero-axiom |
| P6 | Theorem G 严格 Lean 形式化 | 不计划 | 涉及 ℝ-valued continuous fields, meta-mathematical |

---

## 七 · 与 v1 报告之关键区别

| Aspect | v1 (BaguaAlgebra 75 定理) | v3 (本报告) |
|---|---|---|
| 主对象 | R₃ Trigram + R₆ Hexagram | R₀..R₈ uniform + R₈ Cell256 闭合 |
| Shi 编码 | (无；Cell192 之 Z/3 Shi) | V₄ Klein 4-state (道/已/今/未) at R₈ |
| 道 anchor | 无 first-class | first-class = (Z/2)⁸ identity = 五重身份 |
| Cayley 自对偶 | 无 | ✓ Cell{128,256}.cayley + epsAtOrigin retraction |
| Algebraic spine | (Z/2)³ + ⟨综⟩ on R₃ | (Z/2)⁸ Phase A on R₈ + V₄ outer |
| (Z/2)ⁿ uniform | R₁..R₆ (含 R₃→R₄ chong jump) | R₀..R₈ strict, no jumps |
| Mian (R₄) | BenZheng 内部 | first-class R₄ anchor |
| R₅ (五爻) | 跳过 | 显式 (provisional) |
| 印 / 投 算子 | 无 | ✓ 作为 R₇/R₈ 之 atomic XOR mask |
| Lake build | 36 jobs | 3656 jobs |
| 0 sorry | ✓ (75 定理范围内) | ✓ (across all migrated files) |
| 项目 axioms | 0 (static) + 1 (Kleene 在 GodelLi) | 0 (static) + 1 (Kleene 在 GodelLi/KleeneInternal) — 不变 |

---

## 八 · 道-理二分立场（保留 from v1）

本报告之全部 Lean 定理 (Phase A/F/G/C) 皆属**理层** —— 在 Lean kernel 内部由类型检查通过之命题。

但**报告本身**（即「3656 jobs / 0 sorry / 0 静态 axiom」之总命题）属**道层** —— 是关于理层的元陈述，由项目维护者 (人 + Lean kernel) 共同保证。

| 范畴 | 例 | 属 |
|---|---|---|
| `Cell256.xor_self : ∀ c, xor c c = origin` | 在 Lean 内可证 | 理 |
| `cell256_phaseA_summary : ⟨...⟩` | 在 Lean 内可证 | 理 |
| `R8_complete : ⟨...⟩` | 在 Lean 内可证 | 理 |
| `Cell256OperatorComplete` | 在 Lean 内可证 | 理 |
| 「此 collection 0 sorry / 3656 jobs 通过」 | grep / build 统计 | 道（元）|
| 「Lean kernel 一致」 | Coq / Lean 之 meta 信任 | 道（元元）|
| 「Sheng : ℕ → Type」 | 类型族, kind level | 道（外延 ω-tower）|

详见 [`J_理之不完备_哥德尔在256.md`](J_理之不完备_哥德尔在256.md) §一 + [`K_完备性审计.md`](K_完备性审计.md) §三。

> **完备性范围声明**：本报告之「完备」严格限于**静态 (Z/2)⁸ closure 之 R₀..R₈ algebraic spine** —— 即 `R8_complete` bundle + Phase A 各 summary + Theorems A/F/H/I/J/K + Cell256OperatorComplete。**不**主张项目整体 Gödel 意义下完备 —— 参 J 之 `halts_undecidable_internally` (在 BaguaTuring 动力层，与本静态 closure 正交)。

---

## 九 · Reproduce 命令

```bash
git clone https://github.com/<repo> 生生不息
cd 生生不息
elan default leanprover/lean4:v4.30.0-rc2  # or current toolchain
lake build SSBX
# expect:
#   Build completed successfully (3656 jobs).

# Verify Phase A bundles:
lake env lean -e '
open SSBX.Foundation.Bagua.Cell128 in #check @cell128_phaseA_summary;
open SSBX.Foundation.Bagua.Cell256 in #check @cell256_phaseA_summary;
'

# Verify R8_complete:
lake env lean -e '
open SSBX.Foundation.Bagua.Cell256Stratify in #check @R8_complete;
'

# Verify static-layer axioms (Cell256.lean):
lake env lean -e '#print axioms SSBX.Foundation.Bagua.Cell256.cell256_phaseA_summary'
# Expected: propext, Quot.sound, native_decide  (Lean stdlib only)
```

任何 sorry / error / warning 之出现皆为回归。

---

## 十 · 总结

> **2026-05-11 状态**:
>
> - **静态 (Z/2)⁸ closure**: ✓ 0 sorry / 0 项目 axioms (Cell{128,256}/Cell256Stratify/BenZheng/Hierarchy/*)
> - **R₀..R₈ uniform**: ✓ 全 9 层 (Z/2)ⁿ + Lift/Project + V₄ + Cayley + 道 anchor
> - **Theorems A–K 已 Lean 落地**: ✓ (G 是 informal continuous correspondence)
> - **Cell256OperatorComplete**: ✓ self-description witness at R₈
> - **lake build SSBX**: ✓ 3656 jobs 通过
> - **唯一动态 axiom**: kleene_recursion_axiom (在 GodelLi/KleeneInternal, BaguaTuring 动力层，与本静态 closure 正交)
> - **Pending**: P1–P5 (主要是 naming 定案 + Kleene 去公理化工程)

**v3 之 H 报告之主张** (与 v1 一致 但 scope 大幅扩展):

> R₀..R₈ strict (Z/2)ⁿ uniform + V₄ Shi at R₈ 是「自描述系统」之最 minimal algebraic 核之 **Lean 完整落地**。每层 simply transitive，每相邻层 Lift/Project 函子，R₈ 闭合于 Cayley 自对偶 + 道 anchor + V₄ 外对称三件合一。0 sorry / 0 静态 axiom / 3656 jobs verified — 可被任何具有 Lean 4 toolchain 之第三方完整 reproduce。

---

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — 8 lift/project pairs
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — XOR generators
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — non-XOR permutations
- [`formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean`](../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) — R₅ provisional carrier
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — R₃ (Z/2)³
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) — R₄ Mian + Theorems A/F
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../formal/SSBX/Foundation/Bagua/Cell128.lean) — R₇ + 因 + Phase A
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) — R₈ + 果 + Shi V₄ + Phase A + Cayley
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — R₀..R₈ display + R8_complete bundle
- [`formal/SSBX/Foundation/Bagua/GodelLi.lean`](../formal/SSBX/Foundation/Bagua/GodelLi.lean) — Halting undecidability (动力层)
- [`formal/SSBX/Foundation/Bagua/KleeneInternal.lean`](../formal/SSBX/Foundation/Bagua/KleeneInternal.lean) — kleene_recursion_axiom 唯一项目 axiom
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["xxxxxxxx"]` macro
- [`formal/SSBX/Truth/SelfDescription.lean`](../formal/SSBX/Truth/SelfDescription.lean) — `Cell256OperatorComplete`
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../formal/SSBX/Foundation/Yi/Yi.lean) — base Yao/Trigram/Hexagram
