# Lift / Project — R₀..R₈ uniform 升降函子

> 状态：v3 定本 (2026-05-11)
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ strict-uniform doctrine)
> 配套：[ox-notation.md](ox-notation.md) · [shi-v4.md](shi-v4.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md)
> 形式锚：[`Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)

---

## 第一部分：核心思想 (Core Idea)

R-hierarchy 是 strict-uniform (Z/2)ⁿ —— 每层 R_n 之大小恰为 2ⁿ，每升一层加 1 binary axis。Lift / Project 函子把这「+1 bit / -1 bit」的层间关系**显式形式化**为 8 对 (Lift, Project) 函数 + 8 条 `proj ∘ lift = id` 引理。

```
R₀ ──liftR0toR1──→ R₁ ──liftR1toR2──→ R₂ ──liftR2toR3──→ R₃ ──liftR3toR4──→ R₄
 ↑                  ↑                  ↑                  ↑                  ↑
 projR1toR0       projR2toR1         projR3toR2         projR4toR3         projR5toR4
                                                                            │
                                                                            ▼
                                                                            R₅
                                                                            │
                                                                          liftR5toR6 / projR6toR5
                                                                            │
                                                                            ▼
R₅ ──liftR5toR6──→ R₆ ──liftR6toR7──→ R₇ ──liftR7toR8──→ R₈
```

每一对的核心定理 ([`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 1–9)：

```
proj_lift_id_Rn :  ∀ rₙ extraBit, projR(n+1)toRn (liftRntoR(n+1) rₙ extraBit) = rₙ
```

即 **proj ∘ lift = id**, 是 retract（faithful injection R_n ↪ R_{n+1}）。

---

## 第二部分：R-layer abbrevations

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 0：

```lean
namespace SSBX.Foundation.Hierarchy.LiftProject

/-- R₀ = 太极 = Unit. -/
abbrev R0 : Type := Unit
/-- R₁ = 两仪 = Yao. -/
abbrev R1 : Type := Yao
/-- R₂ = 四象 = SiXiang. -/
abbrev R2 : Type := SiXiang
/-- R₃ = 八卦 = Trigram. -/
abbrev R3 : Type := Trigram
/-- R₄ = 16-命 = Mian = Ben × Zheng. -/
abbrev R4 : Type := Mian
/-- R₅ = 32-五爻 = Wuyao = Mian × Bool. -/
abbrev R5 : Type := Wuyao
/-- R₆ = 六十四卦 = Hexagram. -/
abbrev R6 : Type := Hexagram
/-- R₇ = 128-格 = Cell128 = Hexagram × YinBit. -/
abbrev R7 : Type := Cell128
/-- R₈ = 256-格 = Cell256 = Hexagram × Shi. -/
abbrev R8 : Type := Cell256
```

每层基数：

| Layer | Type | size |
|---|---|---|
| R₀ | `Unit` | 1 |
| R₁ | `Yao` | 2 |
| R₂ | `SiXiang` | 4 |
| R₃ | `Trigram` | 8 |
| R₄ | `Mian = Ben × Zheng` | 16 |
| R₅ | `Wuyao = Mian × Bool` | 32 |
| R₆ | `Hexagram` | 64 |
| R₇ | `Cell128 = Hexagram × YinBit` | 128 |
| R₈ | `Cell256 = Hexagram × Shi` | 256 |

---

## 第三部分：8 对 Lift / Project (with retract laws)

### 3.1 R₀ ↔ R₁

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 1：

```lean
/-- 太极 ↪ 两仪: lift the Unit root by attaching a Yao. -/
def liftR0toR1 (_ : R0) (y : Yao) : R1 := y

/-- 两仪 ↠ 太极: forget the Yao. -/
def projR1toR0 (_ : R1) : R0 := ()

theorem proj_lift_id_R0 (r0 : R0) (y : Yao) :
    projR1toR0 (liftR0toR1 r0 y) = r0 := rfl
```

最简单一对：从 Unit 升到 Yao 加一 binary axis；project 丢弃 yao。`rfl` 直接闭合（Unit 之唯一 inhabitant）。

### 3.2 R₁ ↔ R₂

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 2：

```lean
/-- 两仪 ↪ 四象: extend a Yao by a 2nd Yao. -/
def liftR1toR2 (y1 : R1) (y2 : Yao) : R2 := ⟨y1, y2⟩

/-- 四象 ↠ 两仪: forget the 2nd Yao (keep y1). -/
def projR2toR1 (s : R2) : R1 := s.y1

theorem proj_lift_id_R1 (y1 : R1) (y2 : Yao) :
    projR2toR1 (liftR1toR2 y1 y2) = y1 := rfl
```

SiXiang 是 record `⟨y1, y2⟩`；retract 取 `.y1`。

### 3.3 R₂ ↔ R₃

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 3：

```lean
/-- 四象 ↪ 八卦: extend a SiXiang by a 3rd Yao. -/
def liftR2toR3 (s : R2) (y3 : Yao) : R3 := ⟨s.y1, s.y2, y3⟩

/-- 八卦 ↠ 四象: forget the 3rd Yao (keep y1, y2). -/
def projR3toR2 (t : R3) : R2 := ⟨t.y1, t.y2⟩

theorem proj_lift_id_R2 (s : R2) (y3 : Yao) :
    projR3toR2 (liftR2toR3 s y3) = s := by
  cases s; rfl
```

### 3.4 R₃ ↔ R₄ (Trigram ↔ Mian)

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 4：

R₃ → R₄ 是**最复杂**一对，因为 Mian = Ben × Zheng 用 enum-style ctor 而非 yao tuple。设计选择如下 (来自源文件 docstring)：

```
|R₃| = 8 = 2³ but |R₄| = 16 = 2⁴, so the R₃ → R₄ lift takes one extra Yao
(the 4th bit). Mian = Ben × Zheng has the canonical decomposition

  Ben   ≅ Yao²   (4 inhabitants)
  Zheng ≅ Yao²   (4 inhabitants)

We choose: split Trigram's 3 yaos as `(y1, y2)` → Ben and `(y3, extra)` →
Zheng. The projection drops the `extra` bit and recovers the trigram from
the Ben-pair plus the first Zheng-bit.
```

#### Yao² ↔ Ben 双射

```lean
/-- Yao² → Ben canonical bijection.
    (yang, yang) → wu   / (yang, yin) → dong
    (yin,  yang) → jian / (yin,  yin) → shi -/
def benFromYao (y1 y2 : Yao) : Ben :=
  match y1, y2 with
  | .yang, .yang => .wu
  | .yang, .yin  => .dong
  | .yin,  .yang => .jian
  | .yin,  .yin  => .shi

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

#### Yao² ↔ Zheng 双射

```lean
/-- Yao² → Zheng canonical bijection.
    (yang, yang) → jiFaint    / (yang, yin) → shiForce
    (yin,  yang) → jiOccasion / (yin,  yin) → shiTime -/
def zhengFromYao (y3 y4 : Yao) : Zheng :=
  match y3, y4 with
  | .yang, .yang => .jiFaint
  | .yang, .yin  => .shiForce
  | .yin,  .yang => .jiOccasion
  | .yin,  .yin  => .shiTime

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

#### R₃ ↔ R₄ Lift / Project

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

### 3.5 R₄ ↔ R₅ (Mian ↔ Wuyao)

R₄ → R₅ 之 Lift / Project 在 [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) § 3 定义，[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 5 重新 export：

```lean
-- 在 R5_Wuyao.lean § 3 中:
def liftR4toR5 (m : Mian) (b : Bool) : Wuyao := (m, b)
def projR5toR4 (w : Wuyao) : Mian := w.1
theorem proj_lift_id_R4 (m : Mian) (b : Bool) :
    projR5toR4 (liftR4toR5 m b) = m := rfl

-- 在 LiftProject.lean § 5 中重新 export:
def liftR4toR5 (m : R4) (b : Bool) : R5 := R5_Wuyao.liftR4toR5 m b
def projR5toR4 (w : R5) : R4 := R5_Wuyao.projR5toR4 w

theorem proj_lift_id_R4 (m : R4) (b : Bool) :
    projR5toR4 (liftR4toR5 m b) = m :=
  R5_Wuyao.proj_lift_id_R4 m b
```

最简：Wuyao = Mian × Bool 之 product-type，lift 加一 Bool，project 取第一分量。

详见 [r5-wuyao-provisional.md](r5-wuyao-provisional.md)。

### 3.6 R₅ ↔ R₆ (Wuyao ↔ Hexagram)

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 6：

R₅ → R₆ 之 Lift 把 (Mian × Bool) 之 5 bits 与一 extra Yao 拼成 Hexagram 之 6 yaos。设计如下 (源文件 docstring)：

```
Concrete: y1 = ben.bit1, y2 = ben.bit2, y3 = zheng.bit1, y4 = zheng.bit2,
y5 = Bool→Yao (false→yang, true→yin), y6 = extra.
```

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

-- helpers needed for retract proof:
theorem benFromYao_benToYao (b : Ben) :
    benFromYao (benToYao1 b) (benToYao2 b) = b := by
  cases b <;> rfl

theorem zhengFromYao_zhengToYao (z : Zheng) :
    zhengFromYao (zhengToYao1 z) (zhengToYao2 z) = z := by
  cases z <;> rfl

theorem proj_lift_id_R5 (w : R5) (y6 : Yao) :
    projR6toR5 (liftR5toR6 w y6) = w := by
  rcases w with ⟨⟨b, z⟩, bit⟩
  simp [projR6toR5, liftR5toR6,
        benFromYao_benToYao, zhengFromYao_zhengToYao,
        yaoToBool_boolToYao]
```

注意：retract 仅丢 `y6`（hexagram 之 top yao），所有 5 个底部 bits 完整恢复。

### 3.7 R₆ ↔ R₇ (Hexagram ↔ Cell128)

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 7：

```lean
/-- 六爻 ↪ 128-格: attach YinBit (R5/R7 atom 因 bit). -/
def liftR6toR7 (h : R6) (y : SSBX.Foundation.Bagua.Cell128.YinBit) : R7 := (h, y)

/-- 128-格 ↠ 六爻: drop YinBit. -/
def projR7toR6 (c : R7) : R6 := c.1

theorem proj_lift_id_R6 (h : R6) (y : SSBX.Foundation.Bagua.Cell128.YinBit) :
    projR7toR6 (liftR6toR7 h y) = h := rfl
```

最简：Cell128 = Hexagram × YinBit，lift 加 YinBit，project 取 .1。

### 3.8 R₇ ↔ R₈ (Cell128 ↔ Cell256)

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 8：

R₇ → R₈ 之 lift 把 Cell128 之 (Hexagram, YinBit) 中的 YinBit 与新 GuoBit 拼成 Shi V₄：

```lean
/-- 128-格 ↪ 256-格: attach GuoBit to YinBit, package as Shi. -/
def liftR7toR8 (c : R7) (g : SSBX.Foundation.Bagua.Cell256.GuoBit) : R8 :=
  (c.1, Shi.ofYinGuo (c.2, g))

/-- 256-格 ↠ 128-格: extract YinBit from Shi (drop GuoBit). -/
def projR8toR7 (c : R8) : R7 :=
  (c.1, (Shi.toYinGuo c.2).1)

theorem proj_lift_id_R7 (c : R7) (g : SSBX.Foundation.Bagua.Cell256.GuoBit) :
    projR8toR7 (liftR7toR8 c g) = c := by
  rcases c with ⟨h, y⟩
  simp [projR8toR7, liftR7toR8, Shi.toYinGuo_ofYinGuo]
```

注意：retract 通过 `Shi.toYinGuo_ofYinGuo` （[shi-v4.md](shi-v4.md) § 2.2）恢复 (因, 果) ↔ Shi 双射的 right inverse。

---

## 第四部分：8-对 Public Summary

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 9 把 8 条 retract law bundle 起来：

```lean
/-- 8-pair lift/project retract summary: every consecutive R-layer pair
    has `proj ∘ lift = id` (faithful Rₙ ↪ R_{n+1}). -/
theorem liftProject_summary :
    (∀ r0 y, projR1toR0 (liftR0toR1 r0 y) = r0)
    ∧ (∀ y1 y2, projR2toR1 (liftR1toR2 y1 y2) = y1)
    ∧ (∀ s y3, projR3toR2 (liftR2toR3 s y3) = s)
    ∧ (∀ t y4, projR4toR3 (liftR3toR4 t y4) = t)
    ∧ (∀ m b, projR5toR4 (liftR4toR5 m b) = m)
    ∧ (∀ w y6, projR6toR5 (liftR5toR6 w y6) = w)
    ∧ (∀ h y, projR7toR6 (liftR6toR7 h y) = h)
    ∧ (∀ c g, projR8toR7 (liftR7toR8 c g) = c) :=
  ⟨proj_lift_id_R0,
   proj_lift_id_R1,
   proj_lift_id_R2,
   proj_lift_id_R3,
   proj_lift_id_R4,
   proj_lift_id_R5,
   proj_lift_id_R6,
   proj_lift_id_R7⟩
```

这是 R-hierarchy strict-uniform 之 **形式化 hand-off 接口** —— 任何下游 doctrine 引用「R 层之 retract 可达」时，可直接 `liftProject_summary` 返回 8 条全证。

---

## 第五部分：Chong (重) — R₃ → R₆ 之 3 步 composite

### 5.1 旧 v1 vs v2.1 之差

旧 v1 把 R₃ → 重卦 (R₄ in v1) 看作单 +3 bit 之「chong 跳跃」， 跳过 (Z/2)⁴ 与 (Z/2)⁵。

v2.1 strict-uniform 下 chong **不是基础 lift**，而是 3 步 +1 bit 之 composite (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.9)：

$$\text{chong} : R_3 \times R_3 \to R_6 \quad \cong \quad R_3 \xrightarrow{\text{liftR3toR4}} R_4 \xrightarrow{\text{liftR4toR5}} R_5 \xrightarrow{\text{liftR5toR6}} R_6$$

### 5.2 3 步 lift 之参数

```
liftR3toR4 :  R₃ × Yao  → R₄    (extra y4)
liftR4toR5 :  R₄ × Bool → R₅    (extra Bool / 5th yao)
liftR5toR6 :  R₅ × Yao  → R₆    (extra y6 / 6th yao)
```

合计参数：1 个 R₃ + (1 yao + 1 Bool + 1 yao) = 3 个 binary bits = 加到 hexagram 之 outer 3 yaos。

### 5.3 chong 之 3 步分解

R₆ Hexagram 之 6 yaos 分为 inner trigram (y₁ y₂ y₃) + outer trigram (y₄ y₅ y₆)。chong 把 inner trigram 与 outer trigram 拼起来。在 strict-uniform 视角下：

| 步 | input | output | 意义 |
|---|---|---|---|
| 1 (R₃→R₄) | inner trigram + y₄ | Mian (Ben × Zheng) | 加 outer trigram 之 first yao |
| 2 (R₄→R₅) | Mian + Bool | Wuyao | 加 outer trigram 之 second yao (encoded as Bool) |
| 3 (R₅→R₆) | Wuyao + y₆ | Hexagram | 加 outer trigram 之 third yao |

详见 [r5-wuyao-provisional.md](r5-wuyao-provisional.md) § 4 chong 分解。

### 5.4 chong (existing R₆ ctor) 与 3-step composite 之关系

R₆ Hexagram 已有 ctor `chong : Trigram → Trigram → Hexagram` (在 [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) 中)。3-step composite 之 lift 与 chong ctor **不直接 definitional equal**，但二者**计算同 64 个 hexagrams**（仅 bit 之内部排列不同）。

具体见 [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) § 6 之 layout 注释：

```
Concrete: y1 = ben.bit1, y2 = ben.bit2, y3 = zheng.bit1, y4 = zheng.bit2,
y5 = Bool→Yao (false→yang, true→yin), y6 = extra.
```

— 即 R₅→R₆ lift 之 hexagram 之 y₁..y₅ 来自 Mian + Bool 之 5 bits encoding，y₆ 是 extra。这与传统 chong（inner⊕outer trigram）之 layout 不直接相同，但每个组合都精确对应 64 hexagrams 中之一。

---

## 第六部分：Cross-layer XOR action (lift 与 XOR 交换)

### 6.1 命题

设 R_n 之 group law 为 ⊕_n (XOR)。对任意 lift `liftRntoR(n+1) : R_n × X → R_{n+1}` 与对应的 X 之 group law ⊕_X：

$$\text{liftRntoR(n+1)}\, (a \oplus_n b)\, (x \oplus_X y) \;=\; \text{liftRntoR(n+1)}\, a\, x \;\oplus_{n+1}\; \text{liftRntoR(n+1)}\, b\, y$$

即 lift 是 group homomorphism (R_n × X) → R_{n+1}。

### 6.2 R₆ ↔ R₇ 之具体例

R₇ = Cell128 = Hexagram × YinBit。Cell128 之 XOR ([`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 6.3)：

```lean
/-- Cell128 XOR = (hexXor on Hexagram, Bool.xor on YinBit). -/
def xor (c1 c2 : Cell128) : Cell128 :=
  (hexXor c1.1 c2.1, Bool.xor c1.2 c2.2)
```

这正是 product group structure — Hexagram 部分用 hexXor，YinBit 部分用 Bool.xor，二者独立。

`liftR6toR7 (h, y) = (h, y)` 之 group hom 性来自 product group 之定义，不需特别证明 — 是 *trivially homomorphic*。

### 6.3 R₇ ↔ R₈ 之具体例

R₈ = Cell256 = Hexagram × Shi。Cell256 之 XOR ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.4)：

```lean
/-- Cell256 XOR = (hexXor on Hexagram, shiXor on Shi). -/
def xor (c1 c2 : Cell256) : Cell256 :=
  (hexXor c1.1 c2.1, shiXor c1.2 c2.2)
```

Shi 之 XOR 通过 (因, 果) 之 component-wise Bool XOR：

```lean
/-- Shi XOR via componentwise Bool XOR on (因, 果). -/
def shiXor (s1 s2 : Shi) : Shi :=
  let (y1, g1) := Shi.toYinGuo s1
  let (y2, g2) := Shi.toYinGuo s2
  Shi.ofYinGuo (Bool.xor y1 y2, Bool.xor g1 g2)
```

`liftR7toR8` 把 (c, g) 包成 `(c.1, Shi.ofYinGuo (c.2, g))` — 通过 `Shi.toYinGuo_ofYinGuo` 双射，product XOR 与 Shi XOR 互相 commute。

### 6.4 各层 XOR 群结构总览

| Layer | XOR 实现 | identity |
|---|---|---|
| R₀ | trivial | `()` |
| R₁ | `Yao.xor` | `Yao.yang` |
| R₂ | yao²-componentwise | `(yang, yang)` |
| R₃ | yao³-componentwise | `(yang, yang, yang)` = 乾 |
| R₄ | Mian as (Ben, Zheng) — encoded via Yao² | `(.wu, .jiFaint)` |
| R₅ | (Mian XOR, Bool XOR) | `(.wu, .jiFaint)`-paired-with-`false` |
| R₆ | `Hexagram.xor` (yao⁶-componentwise) | `Hexagram.qian` |
| R₇ | `Cell128.xor` = `(hexXor, Bool.xor)` | `(qian, false)` |
| R₈ | `Cell256.xor` = `(hexXor, shiXor)` | `(qian, dao)` = origin |

详见 [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 6 / [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7。

---

## 第七部分：算法层 (Iterated Lifts)

### 7.1 R₀ → R₈ 之全 lift 链

由 8 对 lift 顺次复合，可从 R₀ (Unit) 加 8 个 binary bits 一次走到 R₈ (Cell256)：

```
R₀ × Yao × Yao × Yao × Yao × Bool × Yao × YinBit × GuoBit  →  R₈

(*, y₁, y₂, y₃, y₄, b, y₆, yi, gu) ↦ ...
```

合计 8 个 input bits（前 6 为 hexagram yaos，后 2 为 Shi 之 因/果），匹配 R₈ = (Z/2)⁸ 之 size。

### 7.2 R₈ → R₀ 之全 project 链

由 8 对 project 顺次复合，从 R₈ 一路丢到 R₀：

```
R₈ → R₇ → R₆ → R₅ → R₄ → R₃ → R₂ → R₁ → R₀
```

每步丢一 bit，最终得到 R₀ = Unit 之 唯一元素 `()`。

### 7.3 Project ∘ Lift = id_R₀ 之多步版

8 条 retract law 通过 `proj_lift_id_Rn` 逐步 chain 起来即得：

```
projR1toR0 (liftR0toR1 r y) = r
↓ + projR2toR1 (liftR1toR2 _ _) = _
↓ + ...
↓ + projR8toR7 (liftR7toR8 _ _) = _
↓ ⇒
∀ r0 y₁ y₂ y₃ y₄ b y₆ yi gu,
  projR1toR0 ∘ projR2toR1 ∘ ... ∘ projR8toR7 ∘
  liftR7toR8 ∘ ... ∘ liftR1toR2 ∘ liftR0toR1
    r₀ y₁ y₂ y₃ y₄ b y₆ yi gu = r₀
```

— 即 R₀ 在 8 步 lift + project 之后保留不变。在 R-hierarchy 内任意层之 retract 可由 8 条原子 retract law 复合得到。

---

## 第八部分：边界 (Boundaries)

### 8.1 Lift / Project **不**做的事

| 不做 | 原因 |
|---|---|
| 不刻画 V₄ outer 算子 (zong / hu) 之 lift | 那是 `Operators/V4Outer.lean`，与 strict-uniform 之 binary axis 无关 |
| 不刻画 cross-layer 算子 (例如 R₃ → R₆ 之 chong) | chong 是 3 步 lift composite，本文 § 5 |
| 不刻画 dual-Lift (即 R_n → R_{n+1} × R_{n+1}) | 不在 strict-uniform 之 single-bit-axis 范围 |
| 不接 GL(8, F₂) 类 non-XOR linear | 那破坏 bit-position semantic，不在 R-hierarchy 之 algebraic closure 中 |

### 8.2 不在 Lift / Project 之内 (但相邻)

- **Cayley 自作用** (R_n × R_n → R_n): 不是 lift / project，是 within-layer XOR action ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.6)。
- **印 / 投 mask form**: 不是 lift，是 within-R₈ XOR with fixed mask ([`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 8)。
- **R₈ → BenZheng quadrant projection** (`R8.quadrant` in [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) § 3): 不是 strict-uniform retract — 是 R₈ 对 R₃ 之 4-class quotient projection。

---

## 附录 A：8-对 Lift / Project Lean 签名摘要

来自 [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)：

```lean
namespace SSBX.Foundation.Hierarchy.LiftProject

abbrev R0 : Type := Unit
abbrev R1 : Type := Yao
abbrev R2 : Type := SiXiang
abbrev R3 : Type := Trigram
abbrev R4 : Type := Mian
abbrev R5 : Type := Wuyao
abbrev R6 : Type := Hexagram
abbrev R7 : Type := Cell128
abbrev R8 : Type := Cell256

-- § 1 R₀ ↔ R₁
def liftR0toR1 (_ : R0) (y : Yao) : R1
def projR1toR0 (_ : R1) : R0
theorem proj_lift_id_R0 : ∀ r0 y, projR1toR0 (liftR0toR1 r0 y) = r0

-- § 2 R₁ ↔ R₂
def liftR1toR2 (y1 : R1) (y2 : Yao) : R2
def projR2toR1 (s : R2) : R1
theorem proj_lift_id_R1 : ∀ y1 y2, projR2toR1 (liftR1toR2 y1 y2) = y1

-- § 3 R₂ ↔ R₃
def liftR2toR3 (s : R2) (y3 : Yao) : R3
def projR3toR2 (t : R3) : R2
theorem proj_lift_id_R2 : ∀ s y3, projR3toR2 (liftR2toR3 s y3) = s

-- § 4 R₃ ↔ R₄
def benFromYao (y1 y2 : Yao) : Ben
def benToYao1 : Ben → Yao
def benToYao2 : Ben → Yao
def zhengFromYao (y3 y4 : Yao) : Zheng
def zhengToYao1 : Zheng → Yao
def zhengToYao2 : Zheng → Yao
def liftR3toR4 (t : R3) (y4 : Yao) : R4
def projR4toR3 (m : R4) : R3
theorem proj_lift_id_R3 : ∀ t y4, projR4toR3 (liftR3toR4 t y4) = t

-- § 5 R₄ ↔ R₅
def liftR4toR5 (m : R4) (b : Bool) : R5
def projR5toR4 (w : R5) : R4
theorem proj_lift_id_R4 : ∀ m b, projR5toR4 (liftR4toR5 m b) = m

-- § 6 R₅ ↔ R₆
def boolToYao (b : Bool) : Yao
def yaoToBool (y : Yao) : Bool
def liftR5toR6 (w : R5) (y6 : Yao) : R6
def projR6toR5 (h : R6) : R5
theorem proj_lift_id_R5 : ∀ w y6, projR6toR5 (liftR5toR6 w y6) = w

-- § 7 R₆ ↔ R₇
def liftR6toR7 (h : R6) (y : YinBit) : R7
def projR7toR6 (c : R7) : R6
theorem proj_lift_id_R6 : ∀ h y, projR7toR6 (liftR6toR7 h y) = h

-- § 8 R₇ ↔ R₈
def liftR7toR8 (c : R7) (g : GuoBit) : R8
def projR8toR7 (c : R8) : R7
theorem proj_lift_id_R7 : ∀ c g, projR8toR7 (liftR7toR8 c g) = c

-- § 9 Public summary
theorem liftProject_summary : ∧ over all 8 retract laws

end SSBX.Foundation.Hierarchy.LiftProject
```

## 附录 B：Cell128 / Cell256 之 ε / cayley pair (与 Lift/Project 之关系)

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 6.5 与 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.6 各自定义了 within-layer 之 Cayley 自作用：

```lean
-- Cell128:
def cayley (c : Cell128) : Cell128 → Cell128 := fun s => xor c s
def epsAtOrigin (f : Cell128 → Cell128) : Cell128 := f origin
@[simp] theorem epsAtOrigin_cayley (c : Cell128) :
    epsAtOrigin (cayley c) = c := by ...

-- Cell256 (analogous):
def cayley (c : Cell256) : Cell256 → Cell256 := fun s => xor c s
def epsAtOrigin (f : Cell256 → Cell256) : Cell256 := f origin
@[simp] theorem epsAtOrigin_cayley (c : Cell256) :
    epsAtOrigin (cayley c) = c := by ...
```

这是 **within-layer R-O fusion**（state ↔ operator 同基数），**不是** cross-layer Lift / Project。两类 retract law 名义相似但作用对象不同：

| Retract law | Source | Target | 作用 |
|---|---|---|---|
| `proj_lift_id_Rn` | (R_n, extra bit) | R_n | cross-layer (向下) |
| `epsAtOrigin_cayley` | R_n | R_n | within-layer (Cayley fusion) |

详见 [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 5 Cayley 自对偶。

## 附录 C：与其它文档之关系

| 文档 | 与本文关系 |
|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | parent doctrine — Lift/Project 是 § 4.3 cross-layer 函子之 Lean 落地 |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorem K 之 Lean 落地（R₀..R₈ 全 (Z/2)ⁿ closure 经 8-pair retract） |
| [ox-notation.md](ox-notation.md) | OX 字面量 ↔ R₈; lift/project 给出向 R₇..R₀ 之投影 |
| [shi-v4.md](shi-v4.md) | R₇ → R₈ lift 经 `Shi.ofYinGuo` 加 GuoBit |
| [r5-wuyao-provisional.md](r5-wuyao-provisional.md) | R₄ ↔ R₅ ↔ R₆ 三 lift 之中介，详见专文 |
| [r7-yin-r8-guo.md](r7-yin-r8-guo.md) | R₆ → R₇ lift 加 因 (YinBit); R₇ → R₈ lift 加 果 (GuoBit via Shi) |
| [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | **本文档之 ground truth source** |
| [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | R₄ ↔ R₅ 之 source-of-truth (`liftR4toR5` / `projR5toR4`) |
