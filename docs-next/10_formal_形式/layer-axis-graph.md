> 状态：v3 定本 (2026-05-11)。
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md)
> Lean 入口：[`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) · [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)
> 相关 v3 文档：[root-layer-map.md](root-layer-map.md) · [shi-v4.md](shi-v4.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md) · [lift-project.md](lift-project.md) · [ox-notation.md](ox-notation.md) · [cell256-grid.md](cell256-grid.md)

# 层级轴图全景 layer-axis-graph · v3

> 本文是**全景图谱**——把 R₀..R₈ 严格 (Z/2)ⁿ uniform R-轴、内容线、Lift/Project 函子、V₄ outer 对称、Shi V₄ Klein 闭合统一作图。
> v2 (2026-05-09) 含 R₁..R₆ + Cell192 旧 surface；v3 (2026-05-11) 切换到 **R₀..R₈ + Cell256 + V₄ Klein Shi** 之 definitive。

---

## 0. 全景速览（一图）

```text
                          ┌─────────────────────────────┐
                          │  R₀  太极 / 一元 / Unit       │   1
                          │     极 / 一 / 元              │
                          └────────────┬────────────────┘
                                       │ liftR0toR1 / projR1toR0
                          ┌────────────▼────────────────┐
                          │  R₁  爻 / 两仪 / Yao         │   2 = (Z/2)¹
                          │     实 / 虚 (essence)        │
                          └────────────┬────────────────┘
                                       │ liftR1toR2 / projR2toR1
                          ┌────────────▼────────────────┐
                          │  R₂  四象 / SiXiang          │   4 = (Z/2)²
                          │     春/夏/秋/冬             │
                          └────────────┬────────────────┘
                                       │ liftR2toR3 / projR3toR2
                          ┌────────────▼────────────────┐
                          │  R₃  八卦 / Trigram          │   8 = (Z/2)³
                          │     健悦显起入险止顺         │
                          │     V₄ outer: cuo/zong/hu     │
                          └────────────┬────────────────┘
                                       │ liftR3toR4 / projR4toR3   (Trigram + 1 yao → Mian)
                          ┌────────────▼────────────────┐
                          │  R₄  面 / Mian = Ben×Zheng   │  16 = (Z/2)⁴
                          │     16-命 (本×征)            │
                          └────────────┬────────────────┘
                                       │ liftR4toR5 / projR5toR4    ⚠ provisional
                          ┌────────────▼────────────────┐
                          │  R₅  五爻 / Wuyao = Mian×Bool│  32 = (Z/2)⁵
                          │     无传统 anchor (provisional)│
                          └────────────┬────────────────┘
                                       │ liftR5toR6 / projR6toR5
                          ┌────────────▼────────────────┐
                          │  R₆  重卦 / Hexagram          │  64 = (Z/2)⁶
                          │     y₁..y₆ (改/化/变/临/主/极) │
                          │     V₄ outer: cuo/zong/hu     │
                          └────────────┬────────────────┘
                                       │ liftR6toR7 / projR7toR6   (+ YinBit / 因)
                          ┌────────────▼────────────────┐
                          │  R₇  因卦 / Cell128           │ 128 = (Z/2)⁷
                          │     + 因 axis; 印 = toggle   │
                          └────────────┬────────────────┘
                                       │ liftR7toR8 / projR8toR7   (+ GuoBit / 果)
                          ┌────────────▼────────────────┐
                          │  R₈  果卦 / Cell256           │ 256 = (Z/2)⁸
                          │     + 果 axis; 投 = toggle   │
                          │     V₄ Shi {道, 已, 今, 未}   │
                          │     V₄ outer (hex) ⊗ V₄ (Shi) │
                          └─────────────────────────────┘
```

每层之 Lean 锚见 §11。

---

## 1. R-轴主干（R₀..R₈）— Mermaid

```mermaid
graph TD
    R0["R₀ 太极<br>Unit (1)"]
    R1["R₁ 爻 / 两仪<br>Yao (2)"]
    R2["R₂ 四象<br>SiXiang (4)"]
    R3["R₃ 八卦<br>Trigram (8)"]
    R4["R₄ 面<br>Mian = Ben×Zheng (16)"]
    R5["R₅ 五爻<br>Wuyao = Mian×Bool (32)<br>⚠ provisional"]
    R6["R₆ 重卦<br>Hexagram (64)"]
    R7["R₇ 因卦<br>Cell128 = Hex×YinBit (128)"]
    R8["R₈ 果卦<br>Cell256 = Hex×Shi (256)<br>V₄ Klein 闭合"]

    R0 -->|liftR0toR1| R1
    R1 -->|projR1toR0| R0

    R1 -->|liftR1toR2| R2
    R2 -->|projR2toR1| R1

    R2 -->|liftR2toR3| R3
    R3 -->|projR3toR2| R2

    R3 -->|liftR3toR4| R4
    R4 -->|projR4toR3| R3

    R4 -->|liftR4toR5| R5
    R5 -->|projR5toR4| R4

    R5 -->|liftR5toR6| R6
    R6 -->|projR6toR5| R5

    R6 -->|liftR6toR7| R7
    R7 -->|projR7toR6| R6

    R7 -->|liftR7toR8| R8
    R8 -->|projR8toR7| R7

    classDef r0 fill:#fce4ec,stroke:#880e4f,stroke-width:2px
    classDef r1 fill:#f3e5f5,stroke:#4a148c
    classDef r2 fill:#e8eaf6,stroke:#1a237e
    classDef r3 fill:#e3f2fd,stroke:#0d47a1
    classDef r4 fill:#e1f5fe,stroke:#01579b
    classDef r5 fill:#fff3e0,stroke:#bf360c,stroke-dasharray: 5 5
    classDef r6 fill:#e8f5e9,stroke:#1b5e20
    classDef r7 fill:#fff9c4,stroke:#f57f17
    classDef r8 fill:#ffebee,stroke:#b71c1c,stroke-width:3px

    class R0 r0
    class R1 r1
    class R2 r2
    class R3 r3
    class R4 r4
    class R5 r5
    class R6 r6
    class R7 r7
    class R8 r8
```

每对 (Rₙ, R_{n+1}) 之 lift/project 满足 `proj ∘ lift = id`（retract lemma `proj_lift_id_Rn` in [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)）。

---

## 2. R₀ 入口与 R₈ 闭合：双端点显式

R-axis 的两个 special points：

```mermaid
graph LR
    subgraph Endpoints["R₀ origin ↔ R₈ closure"]
      direction LR
      R0_end["R₀ 太极<br>(absolute zero-anchor)<br>|·| = 1"]
      DOTS["···"]
      R8_end["R₈ 果卦<br>(8-bit closure)<br>|·| = 256<br>道 = V₄ identity"]
      R0_end -->|分 / +1 bit × 8| DOTS
      DOTS -->|→ Cayley closure| R8_end
    end
```

- **R₀ Taiji** = absolute zero-anchor，1 元 set，所有 binary distinction 之前的 origin singleton。
- **R₈ Cell256** = (Z/2)⁸ Cayley regular representation 之 closure。无 R₉（无第 9 个独立 binary axis）。
- **道 (R₈ origin)** = V₄ Klein identity = (因, 果) = (0, 0) = `oooooooo`，是太极在 R₈ 维度上的具体落地。

---

## 3. R₃ → R₄ → R₅ → R₆: chong 之 3-step composite

旧 v2 视角下「R₃ → 重卦」是 +3 bit chong jump（跳过 (Z/2)⁴ 与 (Z/2)⁵）。v3 strict-uniform 下显式拆为 3 步：

```mermaid
graph LR
    R3["R₃ Trigram (8)"]
    R4["R₄ Mian = Ben×Zheng (16)"]
    R5["R₅ Wuyao (32)<br>⚠ provisional"]
    R6["R₆ Hexagram (64)"]

    R3 -->|+1 yao →liftR3toR4| R4
    R4 -->|+1 bit →liftR4toR5| R5
    R5 -->|+1 yao →liftR5toR6| R6

    R3 -.->|"chong (重) — 3-step composite"| R6

    classDef step fill:#e3f2fd,stroke:#0d47a1
    classDef provisional fill:#fff3e0,stroke:#bf360c,stroke-dasharray: 5 5
    classDef composite fill:#f5f5f5,stroke:#424242,stroke-dasharray: 3 3
    class R3,R4,R6 step
    class R5 provisional
```

`chong : R₃ × R₃ → R₆` 在 v3 解读为 **3 步 +1 bit lift composite**；不再是单步 jump。

---

## 4. R₈ V₄ Shi 双层 emergence (因, 果)

V₄ Shi `{道, 已, 今, 未}` 不是 R₇ 单层 atom，而是 R₇ (因 axis) ⊗ R₈ (果 axis) 双 axis 之 emergent 结构：

```mermaid
graph TD
    R6["R₆ Hexagram (64)"]
    R7["R₇ = R₆ × YinBit<br>+ 因 (yin bit)"]
    R8["R₈ = R₆ × Shi<br>= R₆ × YinBit × GuoBit<br>+ 果 (guo bit)"]

    subgraph V4Shi["V₄ Klein 四群 (Shi)"]
      direction LR
      DAO["道 (0,0)<br>= V₄ identity"]
      JI["已 (1,0)<br>= σ_P"]
      WEI["未 (0,1)<br>= σ_T"]
      JIN["今 (1,1)<br>= σ_PT"]
    end

    R6 -->|+ YinBit / 因| R7
    R7 -->|+ GuoBit / 果| R8
    R8 -.->|"Shi.toYinGuo (bijection)"| V4Shi

    classDef atom fill:#fff9c4,stroke:#f57f17
    classDef shi fill:#ffebee,stroke:#b71c1c,stroke-width:2px
    classDef dao fill:#fff,stroke:#000,stroke-width:3px
    class R7,R8 atom
    class JI,WEI,JIN shi
    class DAO dao
```

- 因 axis (R₇): 印 (yìn) = toggle 因 = mask `ooooooxo`
- 果 axis (R₈): 投 (tóu) = toggle 果 = mask `ooooooox`
- Shi.dao = (因=0, 果=0) = V₄ identity = `oo` 后缀 = origin choice
- Shi V₄ block branches from R₇ to R₈

详见 [shi-v4.md](shi-v4.md), [r7-yin-r8-guo.md](r7-yin-r8-guo.md)。

---

## 5. R₃ 与 R₆ 之 V₄ outer (cuo / zong / hu / cuoZong) 对称

V₄ outer 对称在 R₃ / R₆ / R₈ (hex side) 各自存在；R₈ 上 hex-side V₄ 与 Shi-side V₄ tensor 起来给 V₄ × V₄ ≅ (Z/2)⁴。

```mermaid
graph TD
    subgraph V4_R3["R₃ V₄ outer"]
      direction LR
      ID3["id"]
      CUO3["cuo (P)"]
      ZONG3["zong (T)"]
      CZ3["cuoZong (PT)"]
    end

    subgraph V4_R6["R₆ V₄ outer"]
      direction LR
      ID6["id"]
      CUO6["cuo (P)"]
      ZONG6["zong (T)"]
      CZ6["cuoZong (PT)"]
    end

    subgraph V4_R8_hex["R₈ V₄ outer (hex side)"]
      direction LR
      ID8h["id"]
      CUO8h["hexCuo"]
      ZONG8h["hexZong"]
      CZ8h["cuoZongHex"]
    end

    subgraph V4_R8_shi["R₈ V₄ Shi"]
      direction LR
      DAO8["道"]
      JI8["已"]
      JIN8["今"]
      WEI8["未"]
    end

    V4_R3 -.->|"lift (preserves V₄)"| V4_R6
    V4_R6 -.->|"lift (preserves V₄)"| V4_R8_hex
    V4_R8_hex -.->|"⊗ Shi V₄"| V4_R8_shi

    classDef v4 fill:#e1f5fe,stroke:#01579b
    class ID3,CUO3,ZONG3,CZ3 v4
    class ID6,CUO6,ZONG6,CZ6 v4
    class ID8h,CUO8h,ZONG8h,CZ8h v4
    class DAO8,JI8,JIN8,WEI8 v4
```

- `hu (互)` 不在 V₄ — 它有 fixed points 乾/坤，是 sibling 非 V₄ 之 outer op
- Shi-side V₄ 用 `shiCuo / shiZong / shiCuoZong`（in [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)）

详见 [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)。

---

## 6. 八卦内部 (Z/2)³ 群结构 — Mermaid

8 trigram 通过 `改/化/变` 三个 single-bit-flip 形成 (Z/2)³ 群（每两卦最多 3 跳互达）：

```mermaid
graph LR
    QIAN["乾 健<br>(阳,阳,阳)"]
    DUI["兑 悦<br>(阳,阳,阴)"]
    LI["离 显<br>(阳,阴,阳)"]
    ZHEN["震 起<br>(阳,阴,阴)"]
    XUN["巽 入<br>(阴,阳,阳)"]
    KAN["坎 险<br>(阴,阳,阴)"]
    GEN["艮 止<br>(阴,阴,阳)"]
    KUN["坤 顺<br>(阴,阴,阴)"]

    QIAN <-->|改| XUN
    DUI <-->|改| KAN
    LI <-->|改| GEN
    ZHEN <-->|改| KUN

    QIAN <-->|化| LI
    DUI <-->|化| ZHEN
    XUN <-->|化| KAN
    GEN <-->|化| KUN

    QIAN <-->|变| DUI
    LI <-->|变| ZHEN
    XUN <-->|变| GEN
    KAN <-->|变| KUN

    classDef yangCorner fill:#ffebee,stroke:#b71c1c
    classDef yinCorner fill:#e0f2f1,stroke:#004d40
    classDef mixed fill:#f5f5f5,stroke:#424242
    class QIAN yangCorner
    class KUN yinCorner
    class DUI,LI,ZHEN,XUN,KAN,GEN mixed
```

cuo (对待) 由对角线给出: 乾↔坤、兑↔艮、离↔坎、震↔巽。

---

## 7. R₈ 8-bit layout 与 algorithmic atomic generators

R₈ 之 8-bit string layout: `[y₁ y₂ y₃ y₄ y₅ y₆ 因 果]`，初爻在左。

| Generator | mask (8-bit) | 翻位 | 字根 |
|---|---|---|---|
| flip1 (dongInner) | `xooooooo` | y₁ | 改 |
| flip2 (huaInner)  | `oxoooooo` | y₂ | 化 |
| flip3 (bianInner) | `ooxooooo` | y₃ | 变 |
| flip4 (dongOuter) | `oooxoooo` | y₄ | 临 |
| flip5 (huaOuter)  | `ooooxooo` | y₅ | 主 |
| flip6 (bianOuter) | `oooooxoo` | y₆ | 极 |
| **印 (yìn)** | `ooooooxo` | y₇ (因) | 印 (provisional) |
| **投 (tóu)** | `ooooooox` | y₈ (果) | 投 (provisional) |

8 atomic generators 完全生成 (Z/2)⁸ 之 256 个 XOR 算子。

详见 [position-operator-tree.md](position-operator-tree.md), [ox-notation.md](ox-notation.md)。

---

## 8. 内容线垂直结构 — Mermaid

内容线（[`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean)）与 R-轴正交：

```mermaid
graph TD
    GAMMA["Γ 论域 / 当前范畴"]

    subgraph SanBen["三本 (内容根)"]
      direction LR
      WU["物<br>discrete individuality"]
      DONG["動<br>continuous process"]
      JIAN["間<br>relational structure"]
    end

    subgraph SanXian["三显 (manifestations)"]
      direction LR
      WEI["位<br>position"]
      CHANG["場<br>field"]
      JI_INTERFACE["際<br>interface"]
    end

    subgraph SanZheng["三征 (dynamic marks)"]
      direction LR
      JI_FAINT["幾<br>contingency"]
      SHI["勢<br>tendency"]
      JI_MOMENT["機<br>occasion"]
    end

    NETFLOW["开闭闸口 + 网体流"]
    SHENG["生生不息论"]

    GAMMA --> SanBen
    WU --> WEI
    DONG --> CHANG
    JIAN --> JI_INTERFACE
    WEI --> JI_FAINT
    CHANG --> SHI
    JI_INTERFACE --> JI_MOMENT
    SanZheng --> NETFLOW
    NETFLOW --> SHENG

    classDef root fill:#fff9c4,stroke:#f57f17
    classDef sanBen fill:#ffe0b2,stroke:#bf360c
    classDef sanXian fill:#c8e6c9,stroke:#1b5e20
    classDef sanZheng fill:#b3e5fc,stroke:#01579b
    class GAMMA root
    class WU,DONG,JIAN sanBen
    class WEI,CHANG,JI_INTERFACE sanXian
    class JI_FAINT,SHI,JI_MOMENT sanZheng
```

每 三本 引出一个 三显，每 三显 带一个 三征 — 9 字 ordered grid。

---

## 9. cuo 对待跨层全图

```mermaid
graph TB
    subgraph R1Pair["R₁ (1 对)"]
      Y1["阳 / 实"]
      Y2["阴 / 虚"]
      Y1 <-->|cuo| Y2
    end

    subgraph R2Pair["R₂ (2 对)"]
      X1["太阳 / 夏"]
      X2["太阴 / 冬"]
      X3["少阴 / 秋"]
      X4["少阳 / 春"]
      X1 <-->|cuo| X2
      X3 <-->|cuo| X4
    end

    subgraph R3Pair["R₃ (4 对)"]
      A1["乾 健"]
      A2["坤 顺"]
      A3["兑 悦"]
      A4["艮 止"]
      A5["离 显"]
      A6["坎 险"]
      A7["震 起"]
      A8["巽 入"]
      A1 <-->|cuo 三爻反| A2
      A3 <-->|cuo| A4
      A5 <-->|cuo| A6
      A7 <-->|cuo| A8
    end

    subgraph R6Pair["R₆ (6 个 flip 对)"]
      F1["改 (y₁)"]
      F2["化 (y₂)"]
      F3["变 (y₃)"]
      F4["临 (y₄)"]
      F5["主 (y₅)"]
      F6["极 (y₆)"]
    end

    subgraph R7Pair["R₇ (因 axis)"]
      Y7["印 = toggle 因"]
    end

    subgraph R8Pair["R₈ (果 axis + Shi V₄)"]
      Y8["投 = toggle 果"]
      DAOJI["道 ↔ 已 (cuo Shi-side)"]
      DAOWEI["道 ↔ 未 (zong Shi-side)"]
      DAOJIN["道 ↔ 今 (cuoZong Shi-side)"]
    end
```

各层 cuo 对都是 (Z/2) 反演结构的 reflection；R₈ 上 hex-side cuo 与 Shi-side cuo 复合给 V₄ × V₄ 之 16 个对称变换。

---

## 10. 三轴汇聚（八卦层之 demonstration）

```mermaid
graph TD
    ROOT["R₀ 一元 / 太极<br>(R-axis ∩ M-axis ∩ 字根轴)"]

    BAGUA["R₃ 八卦层<br>(Z/2)³ = 8 trigrams"]

    subgraph Raxis["R-axis (alias chain)"]
      direction TB
      G_R3["R₃ Trigram"]
      G_R2["R₂ SiXiang"]
      G_R1["R₁ Yao"]
      G_R0["R₀ Unit"]
      G_R3 -->|projR3toR2| G_R2
      G_R2 -->|projR2toR1| G_R1
      G_R1 -->|projR1toR0| G_R0
    end

    subgraph Maxis["M-axis (content names)"]
      direction TB
      M_T["八卦 / Trigram"]
      M_S["四象 / SiXiang"]
      M_Y["两仪 / Yao"]
      M_TJ["太极 / Unit"]
    end

    subgraph CharAxis["字根轴 (default chars)"]
      direction TB
      C_BAG["健悦显起入险止顺"]
      C_SX["春夏秋冬"]
      C_YAO["实虚"]
      C_TJ["极"]
    end

    BAGUA --> Raxis
    BAGUA --> Maxis
    BAGUA --> CharAxis
    Raxis --> ROOT
    Maxis --> ROOT
    CharAxis --> ROOT

    classDef root fill:#fff9c4,stroke:#f57f17,stroke-width:3px
    classDef bagua fill:#bbdefb,stroke:#0d47a1,stroke-width:2px
    class ROOT root
    class BAGUA bagua
```

三轴在 R₀..R₂ 几乎重合，R₃ 起开始分化但仍指向同一 algebraic 对象。

---

## 11. Lean 锚定速查

| 节点 | Lean 文件 |
|---|---|
| R₀ Taiji | [`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) (alias) + Lean stdlib `Unit` |
| R₁ Yao | [`R1_Yao.lean`](../../formal/SSBX/Foundation/Hierarchy/R1_Yao.lean) (alias) + [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₂ SiXiang | [`R2_SiXiang.lean`](../../formal/SSBX/Foundation/Hierarchy/R2_SiXiang.lean) (alias) + [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| R₃ Trigram | [`R3_Trigram.lean`](../../formal/SSBX/Foundation/Hierarchy/R3_Trigram.lean) (alias) + [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₄ Mian | [`R4_Mian.lean`](../../formal/SSBX/Foundation/Hierarchy/R4_Mian.lean) (alias) + [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| R₅ Wuyao | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) (carrier; provisional) |
| R₆ Hexagram | [`R6_Hexagram.lean`](../../formal/SSBX/Foundation/Hierarchy/R6_Hexagram.lean) (alias) + [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₇ Cell128 | [`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) (alias) + [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| R₈ Cell256 | [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) (alias) + [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) + [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) |
| Lift/Project (8 对) | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |
| Atomic XOR ops | [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) |
| V₄ outer ops | [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |
| 字根 ground truth | [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) |
| umbrella | [`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) |
| OX 字面量 | [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |

---

## 12. v2 → v3 之关键改动（migration map）

| v2 | v3 |
|---|---|
| R₁..R₆ 顶层 | **R₀..R₈** strict uniform，每层 +1 bit |
| R₃ → R₄ chong jump (跳过 16, 32) | **3-step composite**: R₃→R₄→R₅→R₆ |
| Cell192 (Z/3 cyclic Shi) | **Cell256 (V₄ Klein Shi)**, Cell192 已删 |
| Hexagram = R₄ | Hexagram = R₆ |
| Cell192 = R₅ | Cell256 = R₈ |
| 已/今/未 | **道/已/今/未** (V₄ + identity 道) |

详见 [yi-RO-hierarchy.md §11](yi-RO-hierarchy.md) v1→v2.1 重号表 + [pending.md](pending.md) cleanup 状态。
