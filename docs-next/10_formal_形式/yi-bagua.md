# Yi 与 Bagua — R₀..R₈ 形式概览 + BaguaTuring/Kleene/Gödel 边界

> 状态：v3 定本 (2026-05-11)
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ definitive)
>
> 作用：把 **Yi (爻 / 四象 / 八卦 / 重卦)**、**Bagua (BenZheng + Mian + Quadrant)**、**BaguaTuring (受控计算)** 与**不完备边界 (Kleene/Rice/Gödel)** 整合到同一 R-hierarchy 阅读路径。本页是 R₀..R₈ 形式系统的入口 hub。
>
> 配套 v3 兄弟文档：[ox-notation.md](ox-notation.md) · [shi-v4.md](shi-v4.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md) · [lift-project.md](lift-project.md) · [cell256-grid.md](cell256-grid.md) · [64-hexagram-grid.md](64-hexagram-grid.md) · [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md)
> 形式锚：[`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) · [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) · [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) · [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) · [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) · [`BaguaTuring.lean`](../../formal/SSBX/Foundation/Bagua/BaguaTuring.lean) · [`GodelLi.lean`](../../formal/SSBX/Foundation/Bagua/GodelLi.lean) · [`KleeneInternal.lean`](../../formal/SSBX/Foundation/Bagua/KleeneInternal.lean)

---

## 0. 一句话总览

```
Yi 层  (R₁..R₆) — 静态本体   : 爻 → 四象 → 八卦 → 面 → (五爻) → 重卦 = (Z/2)⁶ × ... = 64
Bagua 层 (R₃..R₆) — 内容线分类: BenZheng 4本/4征 / R₄ Mian = Ben×Zheng = 16 / 4 quadrant on R₆
R₇/R₈   — 闭合层             : Cell128 (因) → Cell256 (果) = (Z/2)⁸ = 256, V₄ Shi emerge
BaguaTuring — 动态层           : YiInstr ISA on Cell256, 引入 unbounded iteration → halting undecidability
Kleene/Rice/Gödel — 不完备边界 : 在 BaguaTuring 之上, 形式边界明确
```

R₀..R₈ 共 9 层 strict (Z/2)ⁿ uniform：每层 +1 bit, 共 8 bits，闭合于 R₈ Cell256 = 256 = ASCII 字符空间 cardinality。

---

## 1. Yi 层 — 爻 / 四象 / 八卦 / 面 / 重卦

### 1.1 R₁ Yao (爻 / 两仪) — `Yi.lean:30`

```lean
inductive Yao : Type
  | yang   -- 阳 +1 / `o`
  | yin    -- 阴 -1 / `x`
  deriving Repr, DecidableEq, BEq

def Yao.neg : Yao → Yao
  | .yang => .yin
  | .yin  => .yang

theorem Yao.neg_neg (y : Yao) : y.neg.neg = y
```

R₁ = (Z/2)¹ = 2, 一个 binary distinction。 这是 ontology 的零点 — Spencer-Brown "draw a distinction"。

### 1.2 R₂ SiXiang (四象) — `BaguaAlgebra.lean`

```lean
inductive SiXiang : Type
  | taiyang  -- 太阳 oo
  | shaoyin  -- 少阴 ox
  | shaoyang -- 少阳 xo
  | taiyin   -- 太阴 xx
```

R₂ = (Z/2)² = 4 = V₄ Klein 结构。

### 1.3 R₃ Trigram (八卦) — `Yi.lean:54`

```lean
structure Trigram where
  y1 : Yao  -- 初爻
  y2 : Yao  -- 中爻
  y3 : Yao  -- 上爻
  deriving Repr, DecidableEq, BEq

namespace Trigram
def qian : Trigram := ⟨.yang, .yang, .yang⟩  -- ☰ 天
def dui  : Trigram := ⟨.yang, .yang, .yin⟩   -- ☱ 泽
def li   : Trigram := ⟨.yang, .yin, .yang⟩   -- ☲ 火
def zhen : Trigram := ⟨.yang, .yin, .yin⟩    -- ☳ 雷
def xun  : Trigram := ⟨.yin, .yang, .yang⟩   -- ☴ 风
def kan  : Trigram := ⟨.yin, .yang, .yin⟩    -- ☵ 水
def gen  : Trigram := ⟨.yin, .yin, .yang⟩    -- ☶ 山
def kun  : Trigram := ⟨.yin, .yin, .yin⟩     -- ☷ 地
end Trigram

theorem Trigram.all_length : Trigram.all.length = 8 := rfl

def Trigram.cuo  (t : Trigram) : Trigram := ⟨t.y1.neg, t.y2.neg, t.y3.neg⟩
def Trigram.zong (t : Trigram) : Trigram := ⟨t.y3, t.y2, t.y1⟩

theorem Trigram.cuo_cuo (t : Trigram) : t.cuo.cuo = t
theorem Trigram.zong_zong (t : Trigram) : t.zong.zong = t
```

R₃ = (Z/2)³ = 8 = 4 本 (zong-fixed) + 4 征 (zong-mobile)。详 §2 BenZheng。

### 1.4 R₄ Mian (面) — `BenZheng.lean:230`

R₄ = (Z/2)⁴ = 16, **显式纳入**为 strict-uniform 之 R-layer (旧 v1 把 R₃→R₆ 视为 chong jump 跳过 R₄/R₅)。

```lean
abbrev Mian : Type := Ben × Zheng
-- |Mian| = 4 × 4 = 16

def Mian.all : List Mian := Ben.all.flatMap (fun b => Zheng.all.map (fun z => (b, z)))
theorem Mian.all_count : Mian.all.length = 16 := by native_decide
```

详见 [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) (R₄ Mian = Ben × Zheng = 16 命之载体)。

### 1.5 R₅ Wuyao (五爻) provisional — `Hierarchy/R5_Wuyao.lean`

R₅ = (Z/2)⁵ = 32, **provisional layer** (无传统 Yi anchor)。

```lean
abbrev Wuyao : Type := Mian × Bool
-- |Wuyao| = 16 × 2 = 32 = (Z/2)⁵
def flip5 : Wuyao → Wuyao := ...   -- involution
```

详见 [r5-wuyao-provisional.md](r5-wuyao-provisional.md) (R₅ 命名 caveat + 候选 接/临/渐/进)。

### 1.6 R₆ Hexagram (重卦) — `Yi.lean:104`

```lean
structure Hexagram where
  y1 : Yao  -- 初爻
  y2 : Yao  -- 二爻
  y3 : Yao  -- 三爻
  y4 : Yao  -- 四爻
  y5 : Yao  -- 五爻
  y6 : Yao  -- 上爻
  deriving Repr, DecidableEq, BEq

namespace Hexagram
def qian : Hexagram := ⟨.yang, .yang, .yang, .yang, .yang, .yang⟩
def kun  : Hexagram := ⟨.yin, .yin, .yin, .yin, .yin, .yin⟩

def cuo  (h : Hexagram) : Hexagram   -- 6-yao 全反
def zong (h : Hexagram) : Hexagram   -- 6-yao 反序
def cuoZong (h : Hexagram) : Hexagram := h.cuo.zong
def hu   (h : Hexagram) : Hexagram   -- 取中四爻 (y₂,y₃,y₄,y₃,y₄,y₅)

theorem cuo_cuo  (h : Hexagram) : h.cuo.cuo = h
theorem zong_zong (h : Hexagram) : h.zong.zong = h
theorem cuo_zong_comm (h : Hexagram) : h.cuo.zong = h.zong.cuo

theorem hu_qian : qian.hu = qian
theorem hu_kun  : kun.hu = kun
theorem two_hu_fixed_points (h : Hexagram) : ...   -- 乾, 坤, 既济, 未济
```

R₆ = (Z/2)⁶ = 64. V₄ = {id, cuo, zong, cuoZong} acts on Hexagram。详见 [64-hexagram-grid.md](64-hexagram-grid.md)。

---

## 2. Bagua 层 — BenZheng + Mian + Quadrant

`BenZheng.lean` 给出 R₃ 之 4+4 划分 (Theorem A) 之 first-class 形式化：

### 2.1 4 本 Ben (zong-fixed substrates)

```lean
inductive Ben : Type
  | wu      -- 物 (乾)
  | dong    -- 動 (离)
  | jian    -- 間 (坎)
  | shi     -- 事 (坤)

def Ben.toTrigram : Ben → Trigram
  | .wu   => Trigram.qian
  | .dong => Trigram.li
  | .jian => Trigram.kan
  | .shi  => Trigram.kun
```

4 个 zong-fixed (palindromic) trigrams = 4 substrate.

### 2.2 4 征 Zheng (zong-mobile marks)

```lean
inductive Zheng : Type
  | jiFaint    -- 幾 (巽)
  | shiForce   -- 勢 (震)
  | jiOccasion -- 機 (兑)
  | shiTime    -- 時 (艮)

def Zheng.toTrigram : Zheng → Trigram
  | .jiFaint    => Trigram.xun
  | .shiForce   => Trigram.zhen
  | .jiOccasion => Trigram.dui
  | .shiTime    => Trigram.gen
```

4 个 zong-mobile trigrams = 4 mark, 形成 2 个 zong-orbit: {震↔艮}, {巽↔兑}.

### 2.3 R₃ Theorem A: 4+4 partition (BenZheng.lean)

```lean
def Trigram.isZongFixed  (t : Trigram) : Bool   -- y1 = y3
def Trigram.isZongMobile (t : Trigram) : Bool := !t.isZongFixed

theorem ben_count    : (Trigram.all.filter Trigram.isZongFixed).length  = 4 := by native_decide
theorem zheng_count  : (Trigram.all.filter Trigram.isZongMobile).length = 4 := by native_decide
theorem ben_zheng_complement (t : Trigram) :
    t.isZongFixed = !t.isZongMobile

theorem cuo_preserves_isZongFixed  (t : Trigram) : t.cuo.isZongFixed  = t.isZongFixed
theorem hua_preserves_isZongFixed  (t : Trigram) : (hua t).isZongFixed = t.isZongFixed
theorem dong_flips_isZongFixed     (t : Trigram) : (dong t).isZongFixed = !t.isZongFixed
theorem bian_flips_isZongFixed     (t : Trigram) : (bian t).isZongFixed = !t.isZongFixed
```

### 2.4 R₄ Mian = Ben × Zheng = 16 命

```lean
abbrev Mian : Type := Ben × Zheng

def Mian.label : Mian → String
  | (.wu,   .jiFaint)    => "动"  -- 物之微
  | (.wu,   .shiForce)   => "行"
  | (.wu,   .jiOccasion) => "化"
  | (.wu,   .shiTime)    => "流"
  | (.dong, .jiFaint)    => "萌"
  | (.dong, .shiForce)   => "长"
  | ... -- 16 entries
```

详见 [`表一_六征本表.md`](../../docs/表一_六征本表.md) + [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md)。

### 2.5 R₆ 4-Quadrant on Hexagram

```lean
inductive Quadrant : Type
  | benBen      -- 本本
  | benZheng    -- 本征
  | zhengBen    -- 征本
  | zhengZheng  -- 征征

def Hexagram.quadrant (h : Hexagram) : Quadrant :=
  match h.innerTrigram.isZongFixed, h.outerTrigram.isZongFixed with
  | true,  true  => .benBen
  | true,  false => .benZheng
  | false, true  => .zhengBen
  | false, false => .zhengZheng
```

各 16, 共 64:

```lean
theorem benBen_count       : (Hexagram.quadrantList .benBen).length     = 16
theorem benZheng_count     : (Hexagram.quadrantList .benZheng).length   = 16
theorem zhengBen_count     : (Hexagram.quadrantList .zhengBen).length   = 16
theorem zhengZheng_count   : (Hexagram.quadrantList .zhengZheng).length = 16
theorem quadrant_partition_complete : 16 + 16 + 16 + 16 = 64
```

cuo/zong/hu invariants:

```lean
theorem cuo_preserves_quadrant       (h : Hexagram) : h.cuo.quadrant = h.quadrant
theorem zong_preserves_benBen        : ... -- 本本 自闭
theorem zong_preserves_zhengZheng    : ... -- 征征 自闭
theorem zong_swap_benZheng_to_zhengBen : ... -- 跨换
theorem zong_swap_zhengBen_to_benZheng : ... -- 跨换
theorem huaInner_preserves_quadrant  -- 中爻保象限
theorem huaOuter_preserves_quadrant
theorem dongInner_flips_inner / bianInner_flips_inner / dongOuter_flips_outer / bianOuter_flips_outer
theorem hu_attractors_in_benBen      -- {1乾, 2坤, 63既济, 64未济} ⊂ 本本
```

详 [64-hexagram-grid.md](64-hexagram-grid.md)。

---

## 3. R-hierarchy 全景图 (R₀..R₈)

| R | 名 | 类型 | 群 | 元数 | atom (state) | atom (operator) | 传统 Yi anchor |
|---|---|---|---|---|---|---|---|
| R₀ | 太极 | `Unit` | trivial | 1 | (无) | (无) | 无极 / 太极 |
| R₁ | 爻 / 两仪 | `Yao` (Bool) | Z/2 | 2 | yang/yin | neg | 两仪 |
| R₂ | 四象 | `SiXiang` (Bool²) | V₄ | 4 | (lift 2 爻) | — | 四象 |
| R₃ | 八卦 | `Trigram` | (Z/2)³ | 8 | 4本 + 4征 | dong/hua/bian + cuo/zong/hu | 八卦 |
| **R₄** | **面 Mian** | `Mian = Ben × Zheng` | (Z/2)⁴ | **16** | 4本 × 4征 | (lift) | 面 (Mian) |
| **R₅** | 五爻 (provisional) | `Wuyao = Mian × Bool` | (Z/2)⁵ | **32** | (no canonical) | flip5 | (无传统) |
| R₆ | 重卦 | `Hexagram` | (Z/2)⁶ | 64 | dongOuter/huaOuter/bianOuter + Hexagram.cuo/zong/hu | (lift) | 重卦 |
| **R₇** | 因卦 | `Cell128` | (Z/2)⁷ | **128** | 因 (yīn, past-trace bit) | 印 (yìn) | (新, R-hier 派生) |
| **R₈** | 果卦 | `Cell256` | (Z/2)⁸ | **256** | 果 (guǒ, future-projection bit) + Shi V₄ | 投 (tóu) | (新, R-hier 闭合) |

详见 [yi-RO-hierarchy.md](yi-RO-hierarchy.md) §3 完整阶梯 + §9.4 Lean implementation map。

**Strict uniform 进展**：每层 +1 bit, no jumps。 v1 旧编号之「chong (重) = R₃ → R₆ 之 +3 bit jump」在 v2.1 strict-uniform 下显式拆为 R₃ → R₄ → R₅ → R₆ 三步 lift。

---

## 4. BaguaTuring — 动态层 (YiInstr ISA on Cell256)

### 4.1 文件结构

`Foundation/Bagua/BaguaTuring.lean` 提供 YiInstr 指令集 + 解释器 + 道判机:

```lean
inductive YiInstr : Type
  -- atomic XOR ops on Cell256 components
  | dongInner | huaInner | bianInner          -- inner trigram flips
  | dongOuter | huaOuter | bianOuter          -- outer trigram flips
  | hexCuo | hexZong | hexHu                  -- V₄ outer perms on hex
  | shiCuo | shiZong | shiCuoZong             -- V₄ outer perms on Shi
  | yin | tou                                 -- 印 / 投 (R₇/R₈ atomic)
  -- input/output / control flow
  | setShi (s : Shi)                          -- direct set Shi (incl. Shi.dao)
  | branchYaoEq (i : Fin 6) (target : Nat)    -- conditional jump on yao
  | branchShiEq (s : Shi) (target : Nat)      -- conditional jump on Shi (4 cases)
  | jump (target : Nat)                       -- unconditional
  | halt
  | nop
  ...
```

### 4.2 解释器 boundary

```lean
-- 有 fuel 的总执行 (theorem-friendly)
def YiState.runFuel (st : YiState) (fuel : Nat) : YiState

-- 无界执行 (partial, 可能不返回)
partial def YiState.run (st : YiState) : YiState
```

正确读法：
- `runFuel` 进入 theorem 证明
- `run` 是真实无界 → 可能不停机
- `partial` 边界**不是漏洞**，是非停机语义之诚实表达

### 4.3 Phase F.2 migration: Cell192 → Cell256

`BaguaTuring.lean` 之前操作 Cell192 = Hexagram × Z/3 cyclic Shi。Phase F doctrine alignment 后 (2026-05-10/11):

| 旧 | 新 |
|---|---|
| Hexagram × Shi_Z3 (`{已, 今, 未}`) | Hexagram × Shi_V₄ (`{道, 已, 今, 未}`) |
| 192 cells | **256 cells** |
| `shiNext` Z/3 cycle 已→今→未→已 | **Shi.cuo** (因-axis involution dao↔已, 今↔未) — order 2 not order 3 |
| 3 setShi / 3 branchShiEq cases | **4 setShi / 4 branchShiEq cases (含 .dao)** |

道判机 verdict 不变 (天道 ↦ Shi.ji, 心道 ↦ Shi.wei); Shi.dao 为 V₄ identity, 可 reachable but not emitted by daoJudgeProg.

### 4.4 Turing-completeness ingredients

- **State unbounded**: history : List Cell256 grows
- **Branching data-dependent**: branchYaoEq / branchShiEq
- **Jumps unbounded**: jump target : Nat

⇒ BaguaTuring is Turing-complete (mod fuel discipline)。`run` 不停机性是 TC 之必然。

---

## 5. Kleene / Rice / GodelLi — 不完备边界

### 5.1 GodelLi.lean — 理之不完备

`Foundation/Bagua/GodelLi.lean` 形式化「**理之不完备**」 (incompleteness-of-Li) 在 Cell256 layer:

```lean
-- § 1: Halts predicate (Σ₁) + concrete witnesses
def Halts (prog : List YiInstr) (input : Cell256) (fuel : Nat) : Bool := ...
-- daoJudge halts on every input within 10 fuel
-- loopProg never halts

-- § 2: Finite-fuel incompleteness
theorem finite_fuel_incomplete :
    ∀ N : Nat, ∃ prog input, ¬ Halts prog input N
-- 「理之停机不被任何均一燃料 N 所封闭」

-- § 3: Universality witness (needs Kleene)
-- § 4: Diagonal main theorem
theorem halts_undecidable_internally : ...   -- Lean theorem
-- § 5: Rice corollary
theorem dao_judge_not_universal : ...
```

### 5.2 KleeneInternal.lean — 去公理化路径

唯一项目 axiom: **`kleene_recursion_axiom`** — 用于 cuo-restricted 相关结论。

写法：
- 「在 `kleene_recursion_axiom` 下」
- 「当前路线尚有去公理化 roadmap」 (KleeneInternal.lean 提供 path_to_zero_axiom)
- 「不把它说成 Lean 已内部证明的 Church-Turing 定理」

```lean
-- KleeneInternal.lean
def YiComputable (decide : List YiInstr → Hexagram → Bool) : Prop := ...
def UniversalInterpSpec : Prop := ...
def SmnSpec : Prop := ...

-- 给定 primitives + diagonal:
theorem path_to_zero_axiom :
    UniversalInterpSpec ∧ SmnSpec ∧ Diagonal → kleene_recursion_axiom
```

### 5.3 道理二分 (Dao-Li bifurcation)

```
道 (Dao) = meta-theory (Lean kernel + Sheng : ℕ → Type ω-tower)
理 (Li)  = object theory (Cell256 + YiInstr Turing machine, recursively enumerable)
```

GodelLi 证一个 **道-level theorem about 理**: 「Li, if consistent, is incomplete」 — Halting 不被 Li 内任何 YiProg 决定。

**这是「道可道，非常道」的精确形式化**：可被 object theory (理) 描述者非永真之道 — 永真之道在 meta theory (道) 内陈述。

---

## 6. 静 / 动 分界 — 完整 vs 不完整之精确

| 静态层 (R₀..R₈ closure) | 动态层 (BaguaTuring 之上) |
|---|---|
| 全 finite, 全 decidable | 引入 unbounded iteration → halting undecidability |
| (Z/2)⁸ Cayley fusion + V₄ × V₄ outer | YiInstr ISA on Cell256 + history list |
| 自指 = hu fixed point (Y-comb) + Cayley | 自指 = quine + universal interpreter |
| 0 sorry / 0 axiom (依 propext + native_decide) | 1 axiom (`kleene_recursion_axiom`), 去公理 roadmap 在 KleeneInternal.lean |
| **完整 / 完备 / 自洽 / 自指** | **理之不完备 (GodelLi.lean)** |
| Cell256Stratify.lean R8_complete bundle | GodelLi.halts_undecidable_internally |

**完整 / 不完整之精确分界 = 静态/动态界面**.

---

## 7. Lean 文件 → R-layer 锚定

| Lean 文件 | R/O 范围 | 关键定义 |
|---|---|---|
| (Lean stdlib `Unit`) | R₀ | 太极 |
| [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) | R₁ / R₃ / R₆ + V₄ outer | `Yao`, `Trigram`, `Hexagram`, `cuo/zong/hu` |
| [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | O₁..O₆ 主体 | `dong/hua/bian`, `FlipCombo`, `Sheng`, `chong` |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | **R₄ (Mian)** + R₃ 4+4 + R₆ quadrant | `Ben/Zheng/Mian/Quadrant` |
| [`Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | R₅ (provisional) | `Wuyao = Mian × Bool`, `flip5` |
| [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | R₇ + O₇.印 | `Cell128`, `YinBit`, `yin` (= 印) |
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | R₈ + O₈.投 + Shi V₄ | `Cell256`, `Shi`, `tou`, `Shi.toYinGuo` 双射 |
| [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | R₀..R₈ explicit + R8_complete | R-hierarchy abbrevs, `R8_complete` bundle |
| [`Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | uniform Lift / Project | 8 R-layer pairs, `proj_lift_id_Rn` retracts |
| [`Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | XOR subgroup | Atomic re-export |
| [`Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | V₄ outer | `zong / hu / cuoZong` |
| [`Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) | OX literal | `OX["xxxxxxxx"]` 8-char macro → Cell256 |
| [`BaguaTuring.lean`](../../formal/SSBX/Foundation/Bagua/BaguaTuring.lean) | dynamics on Cell256 | `YiInstr`, `YiState.run / runFuel`, `daoJudgeProg` |
| [`GodelLi.lean`](../../formal/SSBX/Foundation/Bagua/GodelLi.lean) | 不完备 | `Halts`, `halts_undecidable_internally`, Rice |
| [`KleeneInternal.lean`](../../formal/SSBX/Foundation/Bagua/KleeneInternal.lean) | 去公理化路径 | `YiComputable`, `path_to_zero_axiom` |
| [`Truth/SelfDescription.lean`](../../formal/SSBX/Truth/SelfDescription.lean) | 自描述见证 | `Cell256OperatorComplete` |

详 [yi-RO-hierarchy.md §9.4](yi-RO-hierarchy.md) Lean implementation map。

---

## 8. (Z/2)⁸ closure 之 Triple Coincidence

R₈ Cell256 是 R-hierarchy 之自然闭合层。三种经典对偶在 Cell256 上 **完全 coincide**:

| Duality | 形式 | 在 R₈ 上 |
|---|---|---|
| **Cayley** | element ↔ self-action | `Cell256 ≅ XOR(Cell256)` (cayley_inj + epsAtOrigin retraction) |
| **Pontryagin** | element ↔ character | `Cell256 ≅ Hom(Cell256, ±1)` |
| **R-O frame** | state-side ↔ operator-side | 同一 8-bit 二种 viewing |

「(Z/2)⁸ 之 algebraic 完美性」之精确根据 = 三种 duality 在 Cell256 之 coincidence。

---

## 9. 自指 (Self-Reference)

| 自指层次 | 机制 | Lean 锚 |
|---|---|---|
| Object level | elements 是 system 之 atomic ontology | Cell256 (R₈) |
| Action level | operators 是 system 之 atomic transformation | XOR subgroup + V₄ × V₄ outer |
| Fusion level | 元 ≡ 算子 (Cayley) | `cayley_inj` |
| Meta level | ι 是同态 | `cayley_hom` |
| Origin level | 道 anchor identifies all levels | `Cell256.origin = (qian, dao)` |
| Zero level | 太极 (R₀) absolute ground | `Unit` |
| Y-combinator level | hu fixed points | `hu_qian / hu_kun / two_hu_fixed_points` |
| **Universal interpreter level** | quine | `BaguaTuring.lean` (动态层) |

不动点之存在 = self-reference 之 algebraic 见证。

---

## 10. 信任边界 / Audit

- **0 sorry**：全 SSBX 项目, 静态 R₀..R₈ closure 部分。
- **0 项目自定义 axiom in Cell256Stratify R8_complete bundle**：仅依赖 propext + native_decide。
- **1 axiom in GodelLi.lean**：`kleene_recursion_axiom` (cuo-restricted), 去公理化 roadmap 在 KleeneInternal.lean。
- **1 partial def boundary in BaguaTuring.lean**：`YiState.run` (无界执行), 是非停机语义之诚实表达。

详 [trust-boundaries.md](trust-boundaries.md)、`义理/Cell192_BaguaTuring_理层全集与不完备.md` (旧文, 主旨保留 — Cell192 → Cell256 之升级不影响 GodelLi 之主结构) 与 `义理/J_理之不完备_哥德尔在192.md`、`义理/M_证明报告_192_理之不完备.md`。最终强度以 Lean + claim ledger 为准。

---

## 11. 开放方向

1. **R₅ 命名 final 定**：五爻 (descriptive baseline) vs 接 / 临 / 渐 / 进 (philosophical anchor)。详 [r5-wuyao-provisional.md](r5-wuyao-provisional.md).
2. **R₅ Lean type final 定**：`Wuyao = Mian × Bool` vs 独立 `Cell32`.
3. **印/投 atomic vs fancy** (state-modifying)。
4. **R₃ phenomenology 三相 vs R₇/R₈ 二元** 之精确映射。
5. **命名 final 定**：因/果/印/投 vs 印/投/始/终/持/期。详 [yi-calculus-theorem.md §16](yi-calculus-theorem.md).
6. **R₉+ 是否存在**：无 candidate。strict uniform 视角下 (Z/2)⁹ 数学存在但无独立 binary axis anchor。
7. **去公理化**：`kleene_recursion_axiom` 之消除 — KleeneInternal.lean 已铺路。

---

## 12. 一句话三层总论

1. **Algebraic**: R₀..R₈ strict (Z/2)ⁿ uniform; (Z/2)⁸ at R₈ 完成 Cayley regular representation; 元 ≅ 算子 严格同构, abelian closure 内完整。

2. **Ontological**: 太极 = R₀ = absolute zero-anchor; 道 = R₈ origin = identity = no-op = 永真 cell, 一字承担五重身份, anchor 整个 fusion。

3. **Self-referential**: hu (Y-combinator) 之不动点 + Cayley fusion + 道 anchor + 太极 ground 四者合一 = 完整 self-referential closure。 BaguaTuring 上加 unbounded iteration 后转动态: GodelLi 严格证明 Li 之不完备 — Lawvere/Gödel/Y 三个经典自指原理 之 minimal 离散统一实现。

---

## 附：与 v3 兄弟文档关系

| 文档 | 主题 | 与本文关系 |
|---|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | R₀..R₈ definitive | parent specification |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorems A–K | A–K 严格证明全集 |
| [yi-as-meta-framework.md](yi-as-meta-framework.md) | 易作为 meta-framework | 哲学层 companion |
| [shi-v4.md](shi-v4.md) | V₄ Klein on Shi | R₈ Shi 专文 |
| [ox-notation.md](ox-notation.md) | OX["xxxxxxxx"] macro | 8-char OX literal 详解 |
| [r5-wuyao-provisional.md](r5-wuyao-provisional.md) | R₅ 五爻 provisional | R₅ 命名 + Lean type |
| [r7-yin-r8-guo.md](r7-yin-r8-guo.md) | R₇/R₈ atomic axes | 因 / 果 详尽剖析 |
| [lift-project.md](lift-project.md) | uniform Lift / Project | 8 R-layer pairs + retract lemmas |
| [cell256-grid.md](cell256-grid.md) | Cell256 256-格全表 | R₈ 之几何 + 枚举 + 代数 |
| [64-hexagram-grid.md](64-hexagram-grid.md) | 64 卦 4 quadrant 表 | R₆ 层 hex 之 BenZheng 分类 |
| [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) | Mian = Ben × Zheng (R₄) | R₄ 层 16 命之载体 |
