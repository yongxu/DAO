> 状态：v3 定本 (2026-05-11)。
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md)（R₀..R₈ 严格 (Z/2)ⁿ uniform 之 definitive）
> Lean 入口：[`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)（umbrella import）
> 相关 v3 文档：[r4-r8-character-ladder.md](r4-r8-character-ladder.md) · [ox-notation.md](ox-notation.md) · [shi-v4.md](shi-v4.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md) · [lift-project.md](lift-project.md) · [cell256-grid.md](cell256-grid.md)

# 根层映射 root-layer-map · v3

> 本文是**结构地图**——把 R₀..R₈ 的 R-轴（layer-index）、M-轴（meta-content）、字根轴（layer-character）三者并置。
> 历史变迁：v2 (2026-05-09) 含 R₁..R₆ + 192 格旧 surface；v3 (2026-05-11) 切换到 **R₀..R₈ + Cell256 + V₄ Klein Shi** 之 definitive 编号。
> 不再保留 Cell192 / R₁..R₆ 顶层 claim — 仅在「历史修正」附录中作 archive pointer。

---

## 0. 三轴并置定义

| 轴 | 含义 | 锚定 | 是否定本 |
|---|---|---|---|
| **R-轴**（layer index） | 严格 (Z/2)ⁿ uniform 层级，n = 0..8 | [`Foundation/Hierarchy/`](../../formal/SSBX/Foundation/Hierarchy/) | ✅ definitive (2026-05-10/11) |
| **M-轴**（meta-content name） | 每层之内容名（Yao / SiXiang / Trigram / Mian / Wuyao / Hexagram / Cell128 / Cell256） | [`Foundation/Yi/`](../../formal/SSBX/Foundation/Yi/) + [`Foundation/Bagua/`](../../formal/SSBX/Foundation/Bagua/) | ✅ definitive |
| **字根轴**（layer-character） | 每层 default 单字（义理读法） | [`Text/LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) + [r4-r8-character-ladder.md](r4-r8-character-ladder.md) | ⚠ R4..R8 surface 已有 v0.1 决议；Lean registry 尚待同步 |

三轴**正交但同点**——同一 R-layer 之 M-name 与 character 是同一对象之不同 viewing。

---

## 1. 主表：R-轴 / M-轴 / 字根 三者交叉

| R | size | M-name (内容轴) | 字根 (default 单字) | Hierarchy alias 文件 | Original-name 文件 |
|---|---|---|---|---|---|
| **R₀** | 1 | 太极 (Taiji) | 极 / 一 / 元 | [`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) | (Lean stdlib `Unit`) |
| **R₁** | 2 | 爻 / 两仪 (Yao) | 实 / 虚 (邵雍《观物外篇》) | [`R1_Yao.lean`](../../formal/SSBX/Foundation/Hierarchy/R1_Yao.lean) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| **R₂** | 4 | 四象 (SiXiang) | 春 / 夏 / 秋 / 冬 (邵雍先天图) | [`R2_SiXiang.lean`](../../formal/SSBX/Foundation/Hierarchy/R2_SiXiang.lean) | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| **R₃** | 8 | 八卦 (Trigram) | 健 / 悦 / 显 / 起 / 入 / 险 / 止 / 顺 (说卦回归) | [`R3_Trigram.lean`](../../formal/SSBX/Foundation/Hierarchy/R3_Trigram.lean) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| **R₄** | 16 | 面 (Mian) = Ben × Zheng | 動/行/化/流 · 萌/長/發/續 · 緣/通/會/系 · 兆/趨/變/史 | [`R4_Mian.lean`](../../formal/SSBX/Foundation/Hierarchy/R4_Mian.lean) | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| **R₅** | 32 | 五爻 / 內 (Wuyao) = Mian × Bool | 內本 / 內征；32 单字 alias 见 [r4-r8-character-ladder.md](r4-r8-character-ladder.md)；算子 易內 | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | (与 alias 同文件) |
| **R₆** | 64 | 重卦 (Hexagram) | 重：本本 / 本征 / 征本 / 征征；64 卦名为强 alias；算子 易外 + 六位 flip 字 | [`R6_Hexagram.lean`](../../formal/SSBX/Foundation/Hierarchy/R6_Hexagram.lean) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| **R₇** | 128 | 因卦 (Cell128) = Hexagram × YinBit | 因：無因 / 有因；算子 印 | [`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| **R₈** | 256 | 果卦 (Cell256) = Hexagram × Shi | 果：無果 / 有果；算子 投；Shi V₄ {道, 已, 未, 今} | [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) + [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) |

**严格 uniform 守则**：`|Rₙ| = 2ⁿ`，每加一个 binary axis = 一个独立 R-layer。无跳跃，无压缩。

---

## 2. R-轴：(Z/2)ⁿ 严格 uniform 升降

```text
R₀ Unit (太极)
   ↓ liftR0toR1 / projR1toR0
R₁ Yao
   ↓ liftR1toR2 / projR2toR1
R₂ SiXiang  = Yao²
   ↓ liftR2toR3 / projR3toR2
R₃ Trigram  = Yao³
   ↓ liftR3toR4 / projR4toR3            （此处编码 Trigram + 1 yao → Mian）
R₄ Mian     = Ben × Zheng               (R₃ 重卦传统跳过此层之物理 anchor)
   ↓ liftR4toR5 / projR5toR4
R₅ Wuyao    = Mian × Bool               (surface 讀「內」；Lean carrier 名仍 Wuyao)
   ↓ liftR5toR6 / projR6toR5
R₆ Hexagram = Yao⁶                       (传统重卦)
   ↓ liftR6toR7 / projR7toR6
R₇ Cell128  = Hexagram × YinBit         (+ 因)
   ↓ liftR7toR8 / projR8toR7
R₈ Cell256  = Hexagram × Shi             (+ 果, V₄ Klein 闭合)
```

每对 (Rₙ, R_{n+1}) 在 [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) 给出 `liftRntoR{n+1}` / `projR{n+1}toRn` + retract lemma `proj_lift_id_Rn`。

详见 [lift-project.md](lift-project.md)。

---

## 3. M-轴：内容轴（meta-content names）

M-axis 是「内容侧的命名 backbone」——它给每个 R-layer 一个 ontologically motivated 的名字（不是层号）。

| R-axis | M-axis name | 古文出处 | 物理 anchor |
|---|---|---|---|
| R₀ | 太极 / Wuji | 周敦颐「无极而太极」 | vacuum (no distinction) |
| R₁ | 两仪 / Yao | 系辞「太极生两仪」 | qubit basis |
| R₂ | 四象 / SiXiang | 系辞「两仪生四象」 | 2-qubit |
| R₃ | 八卦 / Trigram | 系辞「四象生八卦」 | 3-qubit + V₄ outer |
| R₄ | 面 / Mian = Ben × Zheng | 项目内 BenZheng 自创 | 4-qubit (本×征 16-命) |
| R₅ | 五爻 / 內 / Wuyao | surface 讀「內」；Lean carrier 名仍 Wuyao | transitional 5-qubit |
| R₆ | 重卦 / Hexagram | 系辞「重卦」 | 6-qubit + V₄ outer |
| R₇ | 因卦 / Cell128 | 因 (yīn, past-trace bit) + 印 | 7-qubit + past-cone marker |
| R₈ | 果卦 / Cell256 | 果 (guǒ, future-projection bit) + 投 + Shi V₄ | 8-qubit + future-cone, V₄ Klein 闭合 |

注：R₄ Mian 与 R₅ Wuyao 在 v2 之前隐式跳过，v3 重号下显式纳入。R₅ 是**唯一无传统 Yi anchor** 之层（mathematical 存在但 philosophical 上未独立刻画）。

---

## 4. 字根轴：layer-character defaults

R4..R8 的公开字 v0.1 见 [r4-r8-character-ladder.md](r4-r8-character-ladder.md)。这里记录的是 surface default；Lean declaration / parser registry 尚待同步。

| Layer | 元素层 | 算子层 | Lean ground truth |
|---|---|---|---|
| R₁ | 阳/阴 → **实/虚** (essence) | 易 (yi / Yao.neg) | `Yao.essenceChar` |
| R₂ | 太阳/少阴/少阳/太阴 → **夏/秋/春/冬** | (lift R₁) | `SiXiang.seasonChar` |
| R₃ | 乾兑离震巽坎艮坤 → **健/悦/显/起/入/险/止/顺** | 改/化/变（y₁/y₂/y₃ flip） + 错/综/互 | `Trigram.virtueChar` / `Trigram.literalChar` |
| R₄ | 面之 16 字：動..史 | (lift R₃ + 第 4 yao) | (BenZheng 16-命 in [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean)) |
| R₅ | 內本 / 內征 + R4 面名；32 单字 alias | 易內 / flip5 (toggle 第 5 bit) | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) |
| R₆ | 重：本本 / 本征 / 征本 / 征征 + R4 面名；64 卦名 alias | 易外；另有 改/化/变/**临/主/极** (y₁..y₆ flip) + 错/综/互/错综 | `flipPositionChar` + [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) quadrant |
| R₇ | (Hexagram + 因 bit) | **印 (yìn)** = toggle 因 | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `yin` |
| R₈ | (Hexagram + Shi V₄) | **投 (tóu)** = toggle 果; Shi-side 错/综/错综 | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `tou` + Shi V₄ ops |

**同步边界**：R4..R8 的公开字已先在文档层收口；`Text/LayerCharacterMap.lean`、root-language generated pages、WenScript / Native parser 仍需后续同步。

---

## 5. 三轴之同一性（八卦层 R₃ 之 demonstration）

八卦层是三轴**唯一最早出现明确交点**的位置（R₀..R₂ 三轴几乎重合，R₃ 起开始分化）。

| 同一对象「乾」 | R-轴 | M-轴 | 字根轴 |
|---|---|---|---|
| | R₃ 之 (阳, 阳, 阳) 状态 | M₃ 八卦 (Trigram) 的 `qian` 构造子 | 字根 `健`（义理读）+ `乾`（literal） |
| Lean 锚 | `Trigram` (R₃ alias) | `Trigram.qian` (Yi.lean) | `Trigram.virtueChar .qian = "健"` |

三轴在每层都各自有 ground truth，但指向同一 algebraic 对象。

---

## 6. 与「物动间事」内容线的关系

「**物 / 動 / 間 / 事**」属于**内容线**（[`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean)），不在 R-轴 / M-轴 / 字根轴这三个 ground-truth 轴上：

- R-轴 = 形式 (Z/2)ⁿ 升降之 algebraic 阶梯
- M-轴 = 内容侧元素名 backbone
- 字根轴 = 单字 surface alias
- 内容线（三本/三显/三征） = 范畴论 / 现象学 motivated 之独立 layer，**不替代 R-轴**

详见 [layer-axis-graph.md](layer-axis-graph.md) §7（内容线垂直结构）。

---

## 7. 历史修正附录

### v2 → v3 之主要重号

| v2 surface (旧) | v3 (新) | 说明 |
|---|---|---|
| R₁..R₆ 顶层 | **R₀..R₈** | 显式纳入 R₀ Taiji + R₄ Mian + R₅ Wuyao；R₆ Hexagram → R₆，R₇ Cell128，R₈ Cell256 |
| Cell192 | **Cell256** | Z/3 cyclic Shi 是层级压缩错误；V₄ Klein {道, 已, 今, 未} 才是正确 Shi 结构 |
| 192 格 | **256 格** | 64 hex × 4 Shi (V₄) = 256 = (Z/2)⁸；道 = (因, 果) = (0, 0) = V₄ identity first-class 入本体 |
| 已/今/未 (Z/3) | **道/已/今/未 (V₄)** | 道作为 V₄ identity 是 algebraic 必要，不是哲学附加 |
| chong (R₃ → R₄ jump) | **chong (R₃ → R₄ → R₅ → R₆ 三步 composite)** | strict uniform 视角下 chong 是 lift 之 multi-step composite |

### Cell192 完全弃用

- [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) — **已删除**（commit 8e4406e）
- 与之配套的 `Cell192Stratify.lean`、表六_192格全表.md — 已弃用
- 全部下游接入点已迁移到 Cell256 + Shi V₄

### Lean 重号

```lean
abbrev R0 := Unit
abbrev R1 := Yao
abbrev R2 := SiXiang
abbrev R3 := Trigram
abbrev R4 := Mian
abbrev R5 := Wuyao        -- = Mian × Bool
abbrev R6 := Hexagram
abbrev R7 := Cell128      -- = Hexagram × YinBit
abbrev R8 := Cell256      -- = Hexagram × Shi
```

详见 [`LiftProject.lean §0`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)。

---

## 8. 与其它 v3 文档之关系

| 文档 | 与本文关系 |
|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | **父文档** — R₀..R₈ definitive，本文 §1 主表是其结构性投影 |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorems A–K — 严格证明 R₀..R₈ closure |
| [layer-axis-graph.md](layer-axis-graph.md) | Mermaid 图谱 — 本文 §1 之可视化 |
| [r4-r8-character-ladder.md](r4-r8-character-ladder.md) | R4..R8 结构字梯、reader grammar、备选字与形式逻辑读法 |
| [position-operator-tree.md](position-operator-tree.md) | 8 yao 位置之算子树 |
| [ox-notation.md](ox-notation.md) | `OX["xxxxxxxx"]` 8-char Cell256 字面量 macro |
| [shi-v4.md](shi-v4.md) | Shi V₄ {道, 已, 今, 未} 详解 |
| [r5-wuyao-provisional.md](r5-wuyao-provisional.md) | R₅ 命名候选 + 哲学 anchor 待定 |
| [r7-yin-r8-guo.md](r7-yin-r8-guo.md) | R₇/R₈ 因/果 拆层之论证 |
| [lift-project.md](lift-project.md) | 8 对 Lift/Project 函子之 retract lemma |
| [cell256-grid.md](cell256-grid.md) | 256 格全表 (替代旧 192 格) |
| [foundation-core.md](foundation-core.md) | Foundation 主目录布局 |
| [module-map.md](module-map.md) | 模块簇职责 |
| [pending.md](pending.md) | provisional / pending 边界 |

## 9. Lean 入口速查

| 概念 | 入口 |
|---|---|
| umbrella | [`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) |
| 9 个 alias shim | [`R{0..8}_*.lean`](../../formal/SSBX/Foundation/Hierarchy/) |
| Lift/Project | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |
| atomic XOR ops | [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) |
| V₄ outer ops | [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |
| OX 字面量 macro | [`Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |
| 字根 ground truth | [`Text/LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) |
