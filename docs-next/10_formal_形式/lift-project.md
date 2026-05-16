# Lift / Project — 跨层 R₀ ↔ R₈ uniform API + retract lemmas

> 状态：v3 canonical (2026-05-11) — R₀..R₈ strict (Z/2)ⁿ uniform 之**升降函子对** 8 套：每对 (Rₙ, Rₙ₊₁) 都有 `liftRntoR{n+1}` (+1 bit) 与 `projR{n+1}toRn` (-1 bit)，并伴 `proj_lift_id_R{n}` retract lemma 给出 faithful Rₙ ↪ Rₙ₊₁。
> 角色：本文是 R-层之"梯级 API"专文。R-hierarchy doctrine 见 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3；R₈ 闭合层之 algebraic spine 见 [`cell256-algebra.md`](cell256-algebra.md)；Cell256 之 256 元清单见 [`cell256-grid.md`](cell256-grid.md)。
> 形式锚：[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) 全文 (8 pair, 8 retract lemmas, `liftProject_summary` bundle)；[`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) umbrella import。

---

## 0. 一句话总纲

> **每加 1 bit 上一层，每丢 1 bit 下一层；下行后再上行 = 原数据**（faithful injection）。R-hierarchy 是 8 个这样的 lift/project pair 顺次串成。`chong` (重) 不是 +3 bit jump，而是 **R₃ → R₄ → R₅ → R₆** 之 3-step composite。

---

## 1. R-layer abbreviations

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 0：

```lean
abbrev R0 : Type := Unit                    -- 太极 (1)
abbrev R1 : Type := Yao                     -- 两仪 (2 = (Z/2)¹)
abbrev R2 : Type := SiXiang                 -- 四象 (4 = (Z/2)²)
abbrev R3 : Type := Trigram                 -- 八卦 (8 = (Z/2)³)
abbrev R4 : Type := Mian                    -- 16-命 = Ben × Zheng (16 = (Z/2)⁴)
abbrev R5 : Type := Wuyao                   -- 32-五爻 = Mian × Bool (32 = (Z/2)⁵)
abbrev R6 : Type := Hexagram                -- 六十四卦 (64 = (Z/2)⁶)
abbrev R7 : Type := Cell128                 -- 128-格 = Hexagram × YinBit (128 = (Z/2)⁷)
abbrev R8 : Type := Cell256                 -- 256-格 = Hexagram × Shi (256 = (Z/2)⁸)
```

每层 size = 2^index。

---

## 2. uniform 之 8 个 lift / project pair

每对 (Rₙ, Rₙ₊₁) 给出：

```
liftRntoR{n+1} : Rₙ → <new bit type> → Rₙ₊₁    -- 加 1 bit
projR{n+1}toRn : Rₙ₊₁ → Rₙ                      -- 丢 1 bit
proj_lift_id_R{n} : ∀ rₙ b, proj (lift rₙ b) = rₙ    -- retract: faithful Rₙ ↪ Rₙ₊₁
```

| layer pair | new bit | 加在哪 |
|---|---|---|
| R₀ ↔ R₁ | Yao | 引入第一个 binary distinction |
| R₁ ↔ R₂ | Yao | y₂ |
| R₂ ↔ R₃ | Yao | y₃ |
| R₃ ↔ R₄ | Yao | y₄ — split via Ben/Zheng (详 § 4) |
| R₄ ↔ R₅ | Bool | 五爻 bit (Mian extension) |
| R₅ ↔ R₆ | Yao | y₆ |
| R₆ ↔ R₇ | YinBit (= Bool) | 因 axis (R₇ atom) |
| R₇ ↔ R₈ | GuoBit (= Bool) | 果 axis (R₈ atom) — 与 YinBit 一并封 Shi |

---

## 3. R₀ ↔ R₃ — 简单尾部

### 3.1 R₀ ↔ R₁ (太极 ↔ 两仪)

```lean
def liftR0toR1 (_ : R0) (y : Yao) : R1 := y
def projR1toR0 (_ : R1) : R0 := ()
theorem proj_lift_id_R0 (r0 : R0) (y : Yao) : projR1toR0 (liftR0toR1 r0 y) = r0 := rfl
```

R₀ 是 Unit (1 元)，lift 完全由 Yao 决定；project 总返回 `()`。

### 3.2 R₁ ↔ R₂ (爻 ↔ 四象)

```lean
def liftR1toR2 (y1 : R1) (y2 : Yao) : R2 := ⟨y1, y2⟩
def projR2toR1 (s : R2) : R1 := s.y1
theorem proj_lift_id_R1 (y1 : R1) (y2 : Yao) : projR2toR1 (liftR1toR2 y1 y2) = y1 := rfl
```

四象是 SiXiang `⟨y1, y2⟩`；project 取 y₁，完全失 y₂。

### 3.3 R₂ ↔ R₃ (四象 ↔ 八卦)

```lean
def liftR2toR3 (s : R2) (y3 : Yao) : R3 := ⟨s.y1, s.y2, y3⟩
def projR3toR2 (t : R3) : R2 := ⟨t.y1, t.y2⟩
theorem proj_lift_id_R2 (s : R2) (y3 : Yao) : projR3toR2 (liftR2toR3 s y3) = s
```

八卦 = trigram `⟨y1, y2, y3⟩`；project 取 (y₁, y₂)。

---

## 4. R₃ ↔ R₄ — 设计选择 (Trigram ↔ Mian)

|R₃| = 8 = 2³ but |R₄| = 16 = 2⁴；R₃ → R₄ lift 需加 1 个 extra Yao。**Mian = Ben × Zheng** 是 (Z/2)² × (Z/2)² = (Z/2)⁴ 之 anchor（详 [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) § 5）。

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 4 docstring：

> Strategy: encode Yao²-pairs as Ben/Zheng via canonical 2-bit bijections.
> - (y1, y2) → Ben      (4 inhabitants)
> - (y3, extra) → Zheng (4 inhabitants)
> - Project drops `extra` (the 4th yao) and recovers a trigram.

### 4.1 Yao² ↔ Ben canonical bijection

```lean
/-- Yao² → Ben canonical bijection.
    (yang, yang) → wu   / (yang, yin) → dong
    (yin,  yang) → jian / (yin,  yin) → shi -/
def benFromYao (y1 y2 : Yao) : Ben :=
  match y1, y2 with
  | .yang, .yang => .wu     -- 物
  | .yang, .yin  => .dong   -- 動
  | .yin,  .yang => .jian   -- 間
  | .yin,  .yin  => .shi    -- 事

def benToYao1 : Ben → Yao
  | .wu | .dong => .yang
  | .jian | .shi => .yin

def benToYao2 : Ben → Yao
  | .wu | .jian => .yang
  | .dong | .shi => .yin

theorem benFromYao_yao1 (y1 y2 : Yao) : benToYao1 (benFromYao y1 y2) = y1 := by
  cases y1 <;> cases y2 <;> rfl

theorem benFromYao_yao2 (y1 y2 : Yao) : benToYao2 (benFromYao y1 y2) = y2 := by
  cases y1 <;> cases y2 <;> rfl
```

两条 `benFromYao_yao*` 之证明都是 4-case `cases <;> rfl` —— 4 inhabitants 之每枚都 definitional 等。

### 4.2 Yao² ↔ Zheng canonical bijection

```lean
/-- Yao² → Zheng canonical bijection.
    (yang, yang) → jiFaint    / (yang, yin) → shiForce
    (yin,  yang) → jiOccasion / (yin,  yin) → shiTime -/
def zhengFromYao (y3 y4 : Yao) : Zheng :=
  match y3, y4 with
  | .yang, .yang => .jiFaint     -- 幾
  | .yang, .yin  => .shiForce    -- 勢
  | .yin,  .yang => .jiOccasion  -- 機
  | .yin,  .yin  => .shiTime     -- 時

def zhengToYao1 : Zheng → Yao
  | .jiFaint | .shiForce => .yang
  | .jiOccasion | .shiTime => .yin

def zhengToYao2 : Zheng → Yao
  | .jiFaint | .jiOccasion => .yang
  | .shiForce | .shiTime => .yin

theorem zhengFromYao_yao1 (y3 y4 : Yao) :
    zhengToYao1 (zhengFromYao y3 y4) = y3 := by
  cases y3 <;> cases y4 <;> rfl

theorem zhengFromYao_yao2 (y3 y4 : Yao) :
    zhengToYao2 (zhengFromYao y3 y4) = y4 := by
  cases y3 <;> cases y4 <;> rfl
```

### 4.3 lift / project R₃ ↔ R₄

```lean
/-- 八卦 ↪ 命: combine Trigram + extra Yao into Mian = Ben × Zheng.
    (y1, y2) → Ben, (y3, extra) → Zheng. -/
def liftR3toR4 (t : R3) (y4 : Yao) : R4 :=
  (benFromYao t.y1 t.y2, zhengFromYao t.y3 y4)

/-- 命 ↠ 八卦: extract trigram y1, y2 from Ben, y3 from Zheng (drop y4). -/
def projR4toR3 (m : R4) : R3 :=
  ⟨benToYao1 m.1, benToYao2 m.1, zhengToYao1 m.2⟩

theorem proj_lift_id_R3 (t : R3) (y4 : Yao) :
    projR4toR3 (liftR3toR4 t y4) = t := by
  cases t with
  | mk y1 y2 y3 =>
    simp [projR4toR3, liftR3toR4,
          benFromYao_yao1, benFromYao_yao2, zhengFromYao_yao1]
```

注意：retract 仅 drop `y4`（即 R₄ 中的 extra bit = Zheng 之 second yao），其它 3 个 yao 通过 `benTo*` / `zhengToYao1` 完整恢复。

**关键设计取舍**：(y₁, y₂) → Ben，(y₃, extra) → Zheng；project 丢 extra（即 4th yao），不丢 trigram 的任意 1 yao。这是 canonical 选择；其他 partition (例如 (y₁, y₃) → Ben + (y₂, extra) → Zheng) 也合法 — 选 (y₁,y₂) + (y₃,extra) 是因为它最自然地把 trigram "前 2 yao = base / 后 1 yao + extra = mark" 对接 Ben/Zheng 之 4-本/4-征 划分。

---

## 5. R₄ ↔ R₅ — Mian ↔ Wuyao

R₅ = Wuyao = Mian × Bool（[`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean)）；本 lift 加 Bool 即可：

```lean
def liftR4toR5 (m : R4) (b : Bool) : R5 := R5_Wuyao.liftR4toR5 m b   -- = (m, b)
def projR5toR4 (w : R5) : R4 := R5_Wuyao.projR5toR4 w                 -- = w.1

theorem proj_lift_id_R4 (m : R4) (b : Bool) :
    projR5toR4 (liftR4toR5 m b) = m
```

`R5_Wuyao` 中之 `flip5` (= toggle Bool) 是 R₅ 的 atomic XOR generator。

---

## 6. R₅ ↔ R₆ — Wuyao ↔ Hexagram

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 6 之策略：

> y1 = ben.bit1, y2 = ben.bit2, y3 = zheng.bit1, y4 = zheng.bit2, y5 = Bool→Yao (false→yang, true→yin), y6 = extra.

#### Bool ↔ Yao helpers

```lean
/-- Bool → Yao canonical: false = yang (default), true = yin. -/
def boolToYao (b : Bool) : Yao := if b then .yin else .yang

/-- Yao → Bool inverse. -/
def yaoToBool (y : Yao) : Bool := match y with | .yang => false | .yin => true

theorem yaoToBool_boolToYao (b : Bool) : yaoToBool (boolToYao b) = b := by
  cases b <;> rfl
```

#### R₅ ↔ R₆ Lift / Project

```lean
/-- 五爻 ↪ 六爻: combine Wuyao (32 cells = 5 bits) with a 6th Yao to form
    a Hexagram (64 cells = 6 bits).

    Layout: y1, y2 ← ben (Mian.1) bit-pair; y3, y4 ← zheng (Mian.2) bit-pair;
    y5 ← Bool bit; y6 ← extra Yao. -/
def liftR5toR6 (w : R5) (y6 : Yao) : R6 :=
  let m := w.1
  let b := w.2
  ⟨benToYao1 m.1, benToYao2 m.1, zhengToYao1 m.2, zhengToYao2 m.2,
   boolToYao b, y6⟩

/-- 六爻 ↠ 五爻: drop y6, decode (y1, y2) → Ben, (y3, y4) → Zheng,
    y5 → Bool. -/
def projR6toR5 (h : R6) : R5 :=
  ((benFromYao h.y1 h.y2, zhengFromYao h.y3 h.y4), yaoToBool h.y5)

theorem proj_lift_id_R5 (w : R5) (y6 : Yao) :
    projR6toR5 (liftR5toR6 w y6) = w := by
  rcases w with ⟨⟨b, z⟩, bit⟩
  simp [projR6toR5, liftR5toR6,
        benFromYao_benToYao, zhengFromYao_zhengToYao,
        yaoToBool_boolToYao]
```

5 bits 之 Wuyao 直接 unpack 进 hex 之 y₁..y₅；y₆ 是 lift 添加的 extra。注意 retract 仅丢 `y6`（hexagram 之 top yao），所有 5 个底部 bits 完整恢复。**关键 round-trip helper** 是 `benFromYao_benToYao` 与 `zhengFromYao_zhengToYao`：

```lean
theorem benFromYao_benToYao (b : Ben) :
    benFromYao (benToYao1 b) (benToYao2 b) = b := by
  cases b <;> rfl

theorem zhengFromYao_zhengToYao (z : Zheng) :
    zhengFromYao (zhengToYao1 z) (zhengToYao2 z) = z := by
  cases z <;> rfl
```

二者都是 4-case `cases <;> rfl`。

---

## 7. R₆ ↔ R₇ — Hexagram ↔ Cell128 (加 因 / YinBit)

```lean
def liftR6toR7 (h : R6) (y : Cell128.YinBit) : R7 := (h, y)
def projR7toR6 (c : R7) : R6 := c.1

theorem proj_lift_id_R6 (h : R6) (y : Cell128.YinBit) :
    projR7toR6 (liftR6toR7 h y) = h := rfl
```

R₇ atom = 因 (YinBit) — 详 [`yin-tou-operators.md`](yin-tou-operators.md) § 1。这是最简单的 product extension。

---

## 8. R₇ ↔ R₈ — Cell128 ↔ Cell256 (加 果 / GuoBit, 封装 Shi)

R₈ = Cell256 = Hexagram × Shi；R₇ = Cell128 = Hexagram × YinBit。Shi ≅ YinBit × GuoBit (详 [`v4-shi.md`](v4-shi.md) § 3)。所以 R₇ → R₈ lift 需要 attach 一个 GuoBit，然后 package 成 Shi：

```lean
def liftR7toR8 (c : R7) (g : Cell256.GuoBit) : R8 :=
  (c.1, Shi.ofYinGuo (c.2, g))

def projR8toR7 (c : R8) : R7 :=
  (c.1, (Shi.toYinGuo c.2).1)

theorem proj_lift_id_R7 (c : R7) (g : Cell256.GuoBit) :
    projR8toR7 (liftR7toR8 c g) = c := by
  rcases c with ⟨h, y⟩
  simp [projR8toR7, liftR7toR8, Shi.toYinGuo_ofYinGuo]
```

证明用了 `Shi.toYinGuo_ofYinGuo` (one of the 双射 round-trip lemmas)。这是 8 个 retract 中**唯一**需要 R₂ 之 Klein-four 结构工具（即 Shi 之 (因, 果) 双射，legacy 称作 V₄ tools），其余都是 trivial structural projection。

---

## 9. chong (重) — 现在 = R₃ → R₄ → R₅ → R₆ 之 3-step composite

### 9.1 旧 v1 vs v2.1 / v3 之差

旧 v1 把 `chong : R₃ × R₃ → R₆` 看作单 +3 bit 之「chong 跳跃」，跳过 (Z/2)⁴ 与 (Z/2)⁵（即 R₄ / R₅ 不显式）。

v2.1 / v3 strict-uniform 下 chong **不是基础 lift**，而是 3 步 +1 bit composite (per [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3.9)：

$$\text{chong} : R_3 \times R_3 \to R_6 \quad \cong \quad R_3 \xrightarrow{\text{liftR3toR4}} R_4 \xrightarrow{\text{liftR4toR5}} R_5 \xrightarrow{\text{liftR5toR6}} R_6$$

```
chong : R₃ → R₆ 之实质 = 3 步 +1 bit lift composite
        R₃ → R₄ → R₅ → R₆
        =     +1 bit  +1 bit  +1 bit
```

### 9.2 3 步 lift 之参数

```
liftR3toR4 :  R₃ × Yao  → R₄    (extra y4)
liftR4toR5 :  R₄ × Bool → R₅    (extra Bool / 5th yao)
liftR5toR6 :  R₅ × Yao  → R₆    (extra y6 / 6th yao)
```

合计参数：1 个 R₃ + (1 yao + 1 Bool + 1 yao) = 3 个 binary bits = 加到 hexagram 之 outer 3 yaos。

具体在 [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) 中可这样组合：

```lean
example (t : R3) (y4 y6 : Yao) (b : Bool) : R6 :=
  liftR5toR6 (liftR4toR5 (liftR3toR4 t y4) b) y6
```

### 9.3 chong 之 3 步分解 (inner / outer trigram 视角)

R₆ Hexagram 之 6 yaos 分为 inner trigram (y₁ y₂ y₃) + outer trigram (y₄ y₅ y₆)。chong 把 inner trigram 与 outer trigram 拼起来。在 strict-uniform 视角下：

| 步 | input | output | 意义 |
|---|---|---|---|
| 1 (R₃→R₄) | inner trigram + y₄ | Mian (Ben × Zheng) | 加 outer trigram 之 first yao |
| 2 (R₄→R₅) | Mian + Bool | Wuyao | 加 outer trigram 之 second yao (encoded as Bool) |
| 3 (R₅→R₆) | Wuyao + y₆ | Hexagram | 加 outer trigram 之 third yao |

详见 [`r5-wuyao-provisional.md`](r5-wuyao-provisional.md) § 4 chong 分解。

### 9.4 chong (existing R₆ ctor) 与 3-step composite 之关系

R₆ Hexagram 已有 ctor `chong : Trigram → Trigram → Hexagram` (在 [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) 中)，亦有 `BaguaAlgebra.lean` 之 traditional `chong inner outer = Hexagram.oplus inner outer`（直接拼两个 trigram → hex）。3-step composite 之 lift 与 chong ctor **不直接 definitional equal**，但二者**计算同 64 个 hexagrams**（仅 bit 之内部排列不同）。

具体见 [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 6 之 layout 注释：

```
Concrete: y1 = ben.bit1, y2 = ben.bit2, y3 = zheng.bit1, y4 = zheng.bit2,
y5 = Bool→Yao (false→yang, true→yin), y6 = extra.
```

— 即 R₅→R₆ lift 之 hexagram 之 y₁..y₅ 来自 Mian + Bool 之 5 bits encoding，y₆ 是 extra。这与传统 chong（inner⊕outer trigram）之 layout 不直接相同，但每个组合都精确对应 64 hexagrams 中之一。v3 的 doctrine 强调**strict uniform 视角下 chong 是 lift composite**。详 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3.9。

---

## 10. 8-pair retract 摘要定理

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 9 之 `liftProject_summary`：

```lean
theorem liftProject_summary :
    (∀ r0 y, projR1toR0 (liftR0toR1 r0 y) = r0)
    ∧ (∀ y1 y2, projR2toR1 (liftR1toR2 y1 y2) = y1)
    ∧ (∀ s y3, projR3toR2 (liftR2toR3 s y3) = s)
    ∧ (∀ t y4, projR4toR3 (liftR3toR4 t y4) = t)
    ∧ (∀ m b, projR5toR4 (liftR4toR5 m b) = m)
    ∧ (∀ w y6, projR6toR5 (liftR5toR6 w y6) = w)
    ∧ (∀ h y, projR7toR6 (liftR6toR7 h y) = h)
    ∧ (∀ c g, projR8toR7 (liftR7toR8 c g) = c)
```

8 项 retracts 全证 — 整 R-hierarchy 之 strict uniform `(Rₙ ↪ Rₙ₊₁)` faithful injection 链完全闭合。

---

## 11. RHierarchy umbrella

[`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) 是 R-index 之**一站式 import**：

```lean
-- R-index alias shims (R₀..R₈)
import SSBX.Foundation.Hierarchy.R0_Taiji
import SSBX.Foundation.Hierarchy.R1_Yao
import SSBX.Foundation.Hierarchy.R2_SiXiang
import SSBX.Foundation.Hierarchy.R3_Trigram
import SSBX.Foundation.Hierarchy.R4_Mian
import SSBX.Foundation.Hierarchy.R5_Wuyao
import SSBX.Foundation.Hierarchy.R6_Hexagram
import SSBX.Foundation.Hierarchy.R7_YinHex
import SSBX.Foundation.Hierarchy.R8_GuoHex

-- Cross-cutting structure
import SSBX.Foundation.Hierarchy.LiftProject
import SSBX.Foundation.Hierarchy.Operators.Atomic
import SSBX.Foundation.Hierarchy.Operators.V4Outer
```

下游模块只需 `import SSBX.Foundation.Hierarchy.RHierarchy` 即得：
- 9 个 R-index 别名（R₀..R₈ shims）
- 全 8 套 lift / project pairs + retract lemmas
- 全 atomic XOR ops + V4Outer perms
- 全相关 docstrings

每个 `R{n}_*.lean` shim 是**纯 re-export**（无新逻辑）— 它们的存在是为了 R-index discoverability（读者可直接 `R7.yin` / `R8.tou` 而不需 `Cell128.yin` / `Cell256.tou`）。

---

## 12. retract = id 是 faithful injection 的精确含义

`proj ∘ lift = id` 定理告诉我们：

- **lift 是 injective**: 若 `lift r b = lift r' b'`，则 `proj (lift r b) = proj (lift r' b')`，即 `r = r'`（再用 + bit 也可推 `b = b'`）。
- **Rₙ ↪ Rₙ₊₁ faithful**: 把 `b = default` 之 lift 看作嵌入 `e_n : Rₙ → Rₙ₊₁` 即 `e_n r := lift r default`；`proj ∘ e_n = id` 是 retract。
- **Rₙ 是 Rₙ₊₁ 的 retract**: 范畴论术语，意味 `Rₙ` 在升降序列中**信息无损**。

对反方向 `lift ∘ proj = id` **不**成立 — 因为 lift 自带 1 bit 之自由度，proj 必须丢这个 bit，所以 round-trip 后那个 bit "重新选默认值" 不会等于原来。这是 **product type 的不对称信息 flow** 之精确写法。

---

## 13. 与 algebraic spine 之关系

`Cell128.lean` / `Cell256.lean` 之 Phase A spine（详 [`cell256-algebra.md`](cell256-algebra.md)）给的是 **Rₙ 内部** 的 (Z/2)ⁿ Abelian 群结构 + Cayley fusion。

`LiftProject.lean` 给的是 **Rₙ 与 Rₙ₊₁ 之间** 的 functorial relation — uniform +1 bit lift / -1 bit project + retract。

两者结合 = R₀..R₈ 之**完整 strict-uniform abelian closure**：

| 维度 | 来源 |
|---|---|
| 元数 = 2ⁿ | `Cell{128,256}.all_length` |
| (Z/2)ⁿ AddCommGroup | `Cell{128,256}` Phase A spine |
| Cayley `ι/ε` | `cayley_inj / epsAtOrigin_cayley` |
| layer-内 atomic ops (XOR) | `Atomic.lean` |
| layer-内 V₄ outer ops | `V4Outer.lean` |
| **layer-间 lift / project** | **本文 / LiftProject.lean** |

[`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) 之 `R8_complete` bundle 把所有这些保证一起 ack 出来。

---

## 14. 与其他文档之关系

| 文档 | 关系 |
|---|---|
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3.0–3.9 | 每层 R₀..R₈ 之 doctrine 总论（含 lift 描述） |
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 4.3 | Cross-layer Lift / Project 函子之 doctrine 表 |
| [`cell256-grid.md`](cell256-grid.md) | Cell256 256 元清单 + R-layer 基数 |
| [`cell256-algebra.md`](cell256-algebra.md) | layer-内 (Z/2)ⁿ AddCommGroup spine |
| [`yin-tou-operators.md`](yin-tou-operators.md) | R₇ / R₈ atom 之 因 / 果 binary axes |
| [`v4-shi.md`](v4-shi.md) | R₇ ↔ R₈ lift 中 Shi V₄ 之 (因, 果) packaging |
| [`yi-calculus-theorem.md`](yi-calculus-theorem.md) Theorem K | R-hierarchy 全 (Z/2)ⁿ closure |

---

## 形式锚 (Lean modules)

- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — R₀..R₈ abbrev + 8 lift/project pairs + 8 retract lemmas + `liftProject_summary`
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — umbrella import (R₀..R₈ shims + LiftProject + Operators)
- [`formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) — R₅ Wuyao = Mian × Bool 之主文件 (independent module)
- [`formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) ... [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) — 9 个 R-index re-export shims
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — `Ben / Zheng / Mian / Quadrant` (R₃ 4+4 分 + R₄ Mian anchor)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — `Cell128 = Hexagram × YinBit` (R₇)
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `Cell256 = Hexagram × Shi` (R₈), `Shi.ofYinGuo / toYinGuo`
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — 平行 `liftR7toR8 / projR8toR7` + R-layer 基数定理 + `R8_complete`
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Yao / SiXiang / Trigram / Hexagram`
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — `chong = Hexagram.oplus`, `fenToTrigram`, traditional R₂/R₃ algebra
