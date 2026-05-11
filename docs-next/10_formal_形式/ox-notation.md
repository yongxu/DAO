# OX["..."] 字面量 — 8-char Cell256 macro 完整参考

> 状态：v3 canonical (2026-05-11) — `OX["..."]` 是 Cell256 之首选字面量记法，8 个 `o` / `x` 字符直接编码 (Z/2)⁸ = 256 元中的任意一格。
> 角色：本文是 OX 宏的语法 / 语义 / 错误 / 用例完整参考。Cell256 之内容清单见 [`cell256-grid.md`](cell256-grid.md)；位 6/7 = (因, 果) 之 V₄ 重构见 [`v4-shi.md`](v4-shi.md)；印 / 投 之 OX mask 形式见 [`yin-tou-operators.md`](yin-tou-operators.md)。
> 形式锚：[`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) 全文。

---

## 0. 一句话总纲

> **`OX["abcdefgh"]` : Cell256** — 8 个字符必须全为 `o` 或 `x`；前 6 个 `(a..f)` 是 hexagram 的 6 爻 (inner-to-outer = 初爻..上爻，`o` = yang, `x` = yin)；第 7 字符 `g` 是 因 / YinBit；第 8 字符 `h` 是 果 / GuoBit；macro 在 parse-time 验证长度与字符集，错误抛 `Macro.throwError`。

---

## 0.5 动机 (Motivation)

### 0.5.1 为何需要这个记号

在没有 OX 之前，写一个具体的 256-cell 需要构造 `(Hexagram.mk Yao.yin Yao.yang ..., Shi.ofYinGuo (true, false))` 这样的长式。OX 把这压缩为单一 8-字符字面量：

```lean
-- 长式：
example : Cell256 := (Hexagram.mk Yao.yin Yao.yang Yao.yin Yao.yang Yao.yin Yao.yang,
                      Shi.ofYinGuo (false, true))

-- OX 等价：
example : Cell256 := OX["xoxoxoox"]
```

OX 是 R₈ 全 256 格之**唯一规范字符串字面量**，承担以下三件事：

| 用途 | 例子 |
|---|---|
| 写定具体 cell（教学/文档/示例） | `OX["oooooooo"] = 道 = (Z/2)⁸ identity` |
| `decide` / `native_decide` 可用 | `example : OX["..."] = ... := rfl` |
| 跨文档统一 ASCII 表达 | 在 64-hexagram-grid 等文中引用 cells |

### 0.5.2 与 R-hierarchy 的关系

OX 仅刻画 R₈（256-cell）层。低维层（R₁..R₇）通过 OX 的**前缀**或**投影**间接表达：例如 `OX["oooooooo"]` 的前 6 字符 `oooooo` 即 Hexagram.qian (R₆ identity)，前 3 字符 `ooo` 即 Trigram 乾 (R₃)。低维 → 高维之提升 / 高维 → 低维之投影由 [`lift-project.md`](lift-project.md) 给出精确函数。

---

## 1. 语法

```
OX[ "<8 chars from {o, x}>" ]
```

- **最外层**：term-level 语法，可以出现在任何 Cell256 表达式位置。
- **字符串内**：必须长度 = 8，每字符 ∈ `{'o', 'x'}`，否则 macro elaboration 失败。
- **类型**：always elaborates to `Cell256 = Hexagram × Shi`，其中 `abbrev Shi := YinBit × GuoBit` (Phase C 2026-05-11)。

宏定义（[`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) § 2）：

```lean
syntax (name := oxLit) "OX[" str "]" : term
```

---

## 2. 位置语义

8-char layout：

```
位置:  0   1   2   3   4   5   6   7
字符:  c0  c1  c2  c3  c4  c5  c6  c7
意义:  y₁  y₂  y₃  y₄  y₅  y₆  因  果
       └──── 6 yao (inner-to-outer) ────┘ └ Shi V₄ ┘
       初爻..上爻
```

- **chars 0..5 (positions 1..6)**：六爻 of Hexagram，**inner-to-outer**（即 string[0] = y₁ = 初爻；string[5] = y₆ = 上爻）。
  - `o` → identity bit → `Yao.yang`
  - `x` → set bit → `Yao.yin`
  - 此约定使 `OX["oooooo··"] = Hexagram.qian`（即 (Z/2)⁶ identity）和 `OX["xxxxxx··"] = Hexagram.kun`。
- **char 6 (position 7)**：YinBit (因 axis, R₇ atom)，`o` → `false`, `x` → `true`。
- **char 7 (position 8)**：GuoBit (果 axis, R₈ atom)，`o` → `false`, `x` → `true`。

每位含义详表（位置 0-indexed）：

| 位置 | 角色 | 名称 | 类型 | `o` 含义 | `x` 含义 |
|---|---|---|---|---|---|
| 0 | y₁ (初爻 / 内卦 1st) | Hexagram.y1 | Yao | yang | yin |
| 1 | y₂ (二爻 / 内卦 2nd) | Hexagram.y2 | Yao | yang | yin |
| 2 | y₃ (三爻 / 内卦 3rd) | Hexagram.y3 | Yao | yang | yin |
| 3 | y₄ (四爻 / 外卦 1st) | Hexagram.y4 | Yao | yang | yin |
| 4 | y₅ (五爻 / 外卦 2nd) | Hexagram.y5 | Yao | yang | yin |
| 5 | y₆ (上爻 / 外卦 3rd) | Hexagram.y6 | Yao | yang | yin |
| 6 | 因 (yīn) | YinBit | Bool | false | true |
| 7 | 果 (guǒ) | GuoBit | Bool | false | true |

### 2.1 Inner-to-outer 顺序

OX 之 6 个 hexagram 字符**自内向外**（initial-yao 首先），与 King Wen 文献某些版本（自上而下）相反。这与 `Hexagram.mk y1 y2 y3 y4 y5 y6` 之 Lean 字段序一致。

| OX 位置 | Lean 字段 | 通常文献位置 (上至下) |
|---|---|---|
| 0 | y1 | 第 6（最下）|
| 1 | y2 | 第 5 |
| 2 | y3 | 第 4 |
| 3 | y4 | 第 3 |
| 4 | y5 | 第 2 |
| 5 | y6 | 第 1（最上）|

在文档中**始终按 Lean 顺序**读 OX：左 = 初爻 / 内卦底；右 = 上爻 / 外卦顶。

### 2.2 Shi 之 (因, 果) 编码

Shi 通过 `Shi.ofYinGuo (yinBit, guoBit)` 重构（详 [`v4-shi.md`](v4-shi.md) § 3）。注意 `abbrev Shi := YinBit × GuoBit`（Phase C 2026-05-11）— Shi 即 Bool × Bool 之 type abbrev。

| char 6 | char 7 | (因, 果) | Shi | V₄ 角色 |
|---|---|---|---|---|
| `o` | `o` | (false, false) | 道 (dao) | identity (V₄ identity) |
| `x` | `o` | (true,  false) | 已 (ji)  | σ_P |
| `o` | `x` | (false, true)  | 未 (wei) | σ_T |
| `x` | `x` | (true,  true)  | 今 (jin, PT central) | σ_PT |

详见 [`v4-shi.md`](v4-shi.md) Klein V₄ 结构。

---

## 3. 实现细节

OX 之实现核心是 Lean 4 之 **`syntax` + `Macro.expand` 双层**：在 elaboration 阶段把 `OX["..."]` 替换为 `(Hexagram.mk ..., Shi.ofYinGuo (..., ...))` term。本节细分 4 个子部分：字符 → Lean 之映射、字符串 → Cell256 helper、Syntax 声明、Macro 展开。

### 3.1 字符到 Lean 之映射

[`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) § 1 之运行时 helper：

```lean
@[inline] def yaoOfChar : Char → Yao
  | 'x' => Yao.yin
  | _   => Yao.yang  -- 'o' 与其他都视为 yang (但 macro 已验过字符集)

@[inline] def boolOfChar : Char → Bool
  | 'x' => true
  | _   => false
```

### 3.2 字符串到 Cell256 (runtime helper)

```lean
def cellOfString (s : String) : Cell256 :=
  match s.toList with
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      (⟨yaoOfChar c0, yaoOfChar c1, yaoOfChar c2,
        yaoOfChar c3, yaoOfChar c4, yaoOfChar c5⟩,
       Shi.ofYinGuo (boolOfChar c6, boolOfChar c7))
  | _ => (Hexagram.qian, Shi.dao)  -- unreachable when macro validates length
```

注意：此 helper 是 runtime 路径；macro 在 elab-time 走另一路径见 § 3.4。

### 3.3 Syntax 声明

```lean
/-- `OX[" o/x ×8 "]` term-level macro producing a `Cell256`. -/
syntax (name := oxLit) "OX[" str "]" : term
```

声明 `OX[ <str> ]` 是 term-level 语法。`<str>` 是任意 Lean 字符串字面量。

### 3.4 Macro 展开

§ 2 之 macro expansion 主体：

```lean
@[macro oxLit]
def expandOxLit : Macro := fun stx => do
  match stx with
  | `(OX[ $s:str ]) =>
    let str := s.getString
    match str.toList with
    | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      -- Validate: every char must be 'o' or 'x'
      for c in [c0, c1, c2, c3, c4, c5, c6, c7] do
        unless c = 'o' || c = 'x' do
          Macro.throwError
            s!"OX: invalid char '{c}' in \"{str}\" (only 'o' and 'x' allowed)"
      let y1 ← yaoStxOfChar c0
      let y2 ← yaoStxOfChar c1
      let y3 ← yaoStxOfChar c2
      let y4 ← yaoStxOfChar c3
      let y5 ← yaoStxOfChar c4
      let y6 ← yaoStxOfChar c5
      let yinB ← boolStxOfChar c6
      let guoB ← boolStxOfChar c7
      `((SSBX.Foundation.Yi.Yi.Hexagram.mk
            $y1 $y2 $y3 $y4 $y5 $y6,
         SSBX.Foundation.Bagua.Cell256.Shi.ofYinGuo ($yinB, $guoB)))
    | _ =>
      Macro.throwError
        s!"OX: string must have length 8, got {str.length} (\"{str}\")"
  | _ => Macro.throwUnsupported
```

字符 → Lean term 之子函数：

```lean
private def yaoStxOfChar (c : Char) : MacroM (TSyntax `term) :=
  match c with
  | 'o' => `(SSBX.Foundation.Yi.Yi.Yao.yang)
  | 'x' => `(SSBX.Foundation.Yi.Yi.Yao.yin)
  | _   => Macro.throwError s!"OX: invalid char '{c}' (only 'o' and 'x' allowed)"

private def boolStxOfChar (c : Char) : MacroM (TSyntax `term) :=
  match c with
  | 'o' => `(false)
  | 'x' => `(true)
  | _   => Macro.throwError s!"OX: invalid char '{c}' (only 'o' and 'x' allowed)"
```

### 3.5 Pipeline 流程

```
"OX[\"oxxoxxox\"]"  -- (Lean source)
   ↓ (parser)
syntax tree: OX[ <str: "oxxoxxox"> ]
   ↓ (Macro.expand)
   ↓ length-check (= 8)
   ↓ char-check (∈ {'o', 'x'})
   ↓ build 6 Yao terms + 2 Bool terms
syntax tree: (Hexagram.mk Yao.yang Yao.yin Yao.yin Yao.yang Yao.yin Yao.yin Yao.yang Yao.yin,
              Shi.ofYinGuo (true, true))
   ↓ (elaboration → core term)
Cell256 value
```

整个展开发生在 **elaboration time**（编译期），不在 runtime。所以 `OX["..."]` 与手写 ctor 等价（**reduces by `rfl`**）。

---

## 4. 错误语义 (parse-time)

| 错误 | 触发 | 错信息 |
|---|---|---|
| 长度 ≠ 8 | `OX["ooooo"]` (5 字符), `OX["ooooooooo"]` (9 字符), `OX[""]` (0 字符) | `OX: string must have length 8, got N ("...")` |
| 字符 ∉ `{o, x}` | `OX["aoooooooo"]`, `OX["oooo1ooo"]`, 大写 `OX["XXXXXXXX"]`, 中文 `OX["o好oooooo"]` | `OX: invalid char 'c' in "..." (only 'o' and 'x' allowed)` |

错误在 **macro elaboration time** 抛出（即 Lean 编译/elaboration 阶段），所以 invalid OX literals **绝不会** runtime fail — 它们根本无法过编译。

### 4.1 长度 ≠ 8

```lean
/- Expected: error -/
-- example : Cell256 := OX["ooo"]
-- elab error: OX: string must have length 8, got 3 ("ooo")

-- example : Cell256 := OX["oooooooooo"]
-- elab error: OX: string must have length 8, got 10 ("oooooooooo")
```

错误信息精确到字符串内容与实际长度。

### 4.2 字符 ∉ {`o`, `x`}

```lean
/- Expected: error -/
-- example : Cell256 := OX["oooooooy"]
-- elab error: OX: invalid char 'y' in "oooooooy" (only 'o' and 'x' allowed)

-- example : Cell256 := OX["AAAAAAAA"]
-- elab error: OX: invalid char 'A' in "AAAAAAAA" (only 'o' and 'x' allowed)

-- example : Cell256 := OX["oooooooo "]  -- 含空格
-- elab error: OX: string must have length 8, got 9 (...)
```

错误信息精确到第一个非 `o`/`x` 字符。

### 4.3 大小写 / Unicode

OX 仅接受 ASCII `'o'` 和 `'x'`。大写 `'O'` / `'X'` **被拒绝**（不是 lookup-failure 默认到 yang，是显式 elab error）。Unicode 全角 `'ｏ'` / `'ｘ'` 同被拒绝。

---

## 5. 端到端示例 — `rfl` 可证

[`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) § 3 / § 4 之 examples 全部 `:= rfl` — 也就是说每个 OX 字面量在 elaboration 后**直接** equal 到对应的 Lean 显式构造，无需 simp / decide。

### 5.1 origin / 道

```lean
/-- All-`o` 8-string = (qian, dao) = Cell256.origin = (Z/2)⁸ identity. -/
example : OX["oooooooo"] = (Hexagram.qian, Shi.dao) := rfl

/-- `OX["oooooooo"]` 是 Cell256.origin. -/
example : OX["oooooooo"] = (Cell256.origin : Cell256) := rfl
```

`OX["oooooooo"]` 是整个 R₈ 的 origin / identity / 道（参考 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3.0 道之 anchor 角色）。

### 5.2 Shi 之四态（hex 部分 = 乾）

```lean
/-- Char 7 = `x` flips YinBit only ⇒ Shi.ji (已). -/
example : OX["ooooooxo"] = (Hexagram.qian, Shi.ji) := rfl

/-- Char 8 = `x` flips GuoBit only ⇒ Shi.wei (未). -/
example : OX["ooooooox"] = (Hexagram.qian, Shi.wei) := rfl

/-- Both Shi bits set ⇒ Shi.jin (今, PT central element). -/
example : OX["ooooooxx"] = (Hexagram.qian, Shi.jin) := rfl
```

| OX | (Hexagram, Shi) | 物理 anchoring |
|---|---|---|
| `OX["oooooooo"]` | (乾, 道) | identity / 永真 anchor |
| `OX["ooooooxo"]` | (乾, 已) | parity-like (P) |
| `OX["ooooooox"]` | (乾, 未) | time-reversal-like (T) |
| `OX["ooooooxx"]` | (乾, 今) | PT 复合（中心元）|

### 5.3 hex 部分 = 坤

```lean
/-- All-`x` Hexagram part = Hexagram.kun (all yin); Shi.jin (PT). -/
example : OX["xxxxxxxx"] = (Hexagram.kun, Shi.jin) := rfl
```

注意：`OX["xxxxxxxx"]` 不是 (kun, 道)，因为最后两位 `xx` 编码为 Shi.jin (PT)。如果想要 (kun, 道)，需写 `OX["xxxxxxoo"]`。

### 5.4 单爻翻转 (single yao flip)

```lean
/-- char 0 = y1 = `x` flips initial yao only.
    Result is Hexagram with y1 = yin, y2..y6 = yang. -/
example :
    OX["xooooooo"] =
      (Hexagram.mk Yao.yin Yao.yang Yao.yang Yao.yang Yao.yang Yao.yang,
       Shi.dao) := rfl

/-- char 5 = y6 = `x` flips top yao only. -/
example :
    OX["oooooxoo"] =
      (Hexagram.mk Yao.yang Yao.yang Yao.yang Yao.yang Yao.yang Yao.yin,
       Shi.dao) := rfl
```

### 5.5 混合 (mixed: hexagram + Shi.wei)

```lean
/-- Mixed cell: hexagram-internal flip + Shi.wei. -/
example :
    OX["xoxoxoox"] =
      (Hexagram.mk Yao.yin Yao.yang Yao.yin Yao.yang Yao.yin Yao.yang,
       Shi.wei) := rfl
```

读法：

- y₁=yin, y₂=yang, y₃=yin, y₄=yang, y₅=yin, y₆=yang → `离 ☲ 重` 卦的某 hex（实际 hexagram 命名见 [`64-hexagram-grid.md`](64-hexagram-grid.md)）
- (因, 果) = (`o`, `x`) = (false, true) = Shi.wei (未)

### 5.6 256 个具体 cell 之全集

OX 是 R₈ 的全枚举字面量化器：256 个不同 8-字符字符串恰好对应 256 cells（`o`/`x` 共 2⁸ = 256 种）。8 个 examples 一齐 ack 了 macro 的端到端 round-trip：字符 → 6 yao + (因, 果) → Shi reconstruction → Cell256 字面量。

### 5.7 在 `decide` / `native_decide` 中

OX 字面量在 `decide` 中**直接**化简，可用于 finite property check：

```lean
example : Cell256.flip1 OX["oooooooo"] = OX["xooooooo"] := by decide
example : Cell256.tou OX["oooooooo"] = OX["ooooooox"] := by decide
example : Cell256.yin (Cell256.tou OX["oooooooo"]) = OX["ooooooxx"] := by decide
```

（最后一行：印 ∘ 投 = V₄ 中心元，把 (因, 果) 同时翻 ⇒ Shi.jin = `xx`）

---

## 6. 印 / 投 mask 之 OX 字面写法

按本约定：

| OX | 解读 |
|---|---|
| `OX["ooooooxo"]` | Cell256.yin_mask = (qian, ji) — 印之 mask |
| `OX["ooooooox"]` | Cell256.tou_mask = (qian, wei) — 投之 mask |
| `OX["ooooooxx"]` | yin_mask ⊕ tou_mask = (qian, jin) — V₄ 中央元 = 错综 (cuoZong) |

在算子声明中：

```lean
-- 印 mask: only YinBit set
def yin_mask_alt : Cell256 := OX["ooooooxo"]
example : yin_mask_alt = Cell256.yin_mask := rfl

-- 投 mask: only GuoBit set
def tou_mask_alt : Cell256 := OX["ooooooox"]
example : tou_mask_alt = Cell256.tou_mask := rfl
```

`Cell256.yin / Cell256.tou` 之 effect 完全由 OX 后两位描述：

| 输入 | 操作 | 输出 |
|---|---|---|
| `OX["......oo"]` | yin | `OX["......xo"]` |
| `OX["......xo"]` | yin | `OX["......oo"]` |
| `OX["......oo"]` | tou | `OX["......ox"]` |
| `OX["......oo"]` | yin ∘ tou | `OX["......xx"]` |

详 [`yin-tou-operators.md`](yin-tou-operators.md) § 3.1 与 [`v4-shi.md`](v4-shi.md) § 5 V₄ Klein 群运算表。

Lean anchors for mask readings:

| Anchor | 读法 |
|---|---|
| `V4Tensor.ox_origin_eq_origin` | `OX["oooooooo"]` is R₈ origin / Way |
| `V4Tensor.ox_imprint_mask_eq` | `OX["ooooooxo"]` toggles the trace bit |
| `V4Tensor.ox_project_mask_eq` | `OX["ooooooox"]` toggles the projection bit |
| `V4Tensor.ox_temporal_pt_mask_eq` | `OX["ooooooxx"]` toggles both temporal bits |

---

## 7. R₃ / R₆ 之 OX 子集

虽然 OX 宏专门是 Cell256 (8-char)，但下列子串 / 子位置等价：

| 位置 | 等价 type |
|---|---|
| chars 0..2 (= y₁..y₃) | Trigram (R₃) — 3 yao 内卦 |
| chars 3..5 (= y₄..y₆) | Trigram (R₃) — 3 yao 外卦 |
| chars 0..5 (= y₁..y₆) | Hexagram (R₆) — 6 yao |
| chars 0..6 (= y₁..y₆ + 因) | Cell128 (R₇) |
| chars 0..7 (full) | Cell256 (R₈) |

例如 `OX["oooooo??"]` 之 hex 部分恒为 `Hexagram.qian` (☰ × 2)；`OX["ooo???oo"]` 之 inner trigram 恒 = qian。

OX ↔ R-hierarchy 投影对应表：

| 操作 | OX 形式 | 说明 |
|---|---|---|
| 取前 6 字符 → R₆ | `OX["abcdef--"]` 之 `abcdef` 段 | Hexagram (drop Shi) |
| 取前 3 字符 → R₃ | `OX["abc-----"]` 之 `abc` 段 | inner Trigram |
| 第 6/7 字符 → R₈ Shi | `OX["------yg"]` 之 `yg` 段 | (因, 果) ∈ Bool² |
| 第 6 字符 → R₇ YinBit | `OX["------y-"]` 之 `y` 字符 | YinBit 仅 |

参考 [`lift-project.md`](lift-project.md) 给出的精确 Lift / Project 函数。

---

## 8. 与其他 doctrine 之对齐

### 8.1 Mask 之 8 atomic generators

R₈ (Z/2)⁸ 的 8 atomic XOR generators 在 OX 下：

| Generator | OX mask | 翻位 |
|---|---|---|
| dongInner | `OX["xooooooo"]` | y₁ |
| huaInner  | `OX["oxoooooo"]` | y₂ |
| bianInner | `OX["ooxooooo"]` | y₃ |
| dongOuter | `OX["oooxoooo"]` | y₄ |
| huaOuter  | `OX["ooooxooo"]` | y₅ |
| bianOuter | `OX["oooooxoo"]` | y₆ |
| 印 (yin)  | `OX["ooooooxo"]` | y₇ (因) |
| 投 (tou)  | `OX["ooooooox"]` | y₈ (果) |

8 个 mask 之每一个都是 (Z/2)⁸ 群中的一个 standard basis vector — 它们任意 XOR 组合可生成全 256 cells。

### 8.2 complement / negation masks

| Mask | OX | Lean anchor |
|---|---|
| Hexagram complement mask | `OX["xxxxxxoo"]` (preserves temporal bits) | `V4Tensor.ox_hex_neg_mask_eq`, `V4Tensor.r8_hexCuo_eq_xor_earth_mask` |
| Trace-bit toggle | `OX["ooooooxo"]` | `V4Tensor.ox_imprint_mask_eq` |
| Projection-bit toggle | `OX["ooooooox"]` | `V4Tensor.ox_project_mask_eq` |
| Temporal PT mask | `OX["ooooooxx"]` | `V4Tensor.ox_temporal_pt_mask_eq` |
| Full 8-bit negation mask | `OX["xxxxxxxx"]` | `V4Tensor.ox_full_neg_mask_eq`, `V4Tensor.fullNegOperator_involutive` |

`OX["xxxxxxoo"]` means “negate the six hexagram coordinates only.” `OX["xxxxxxxx"]` means “negate all eight coordinates”: six hexagram bits plus trace bit plus projection bit. Lean records the decomposition as `V4Tensor.fullNegOperator_eq_hexCuo_shiCuoZong`.

### 8.3 OX ↔ Lean ctor 速查

| OX | Lean 等价 |
|---|---|
| `OX["oooooooo"]` | `(Hexagram.qian, Shi.dao)` 即 `Cell256.origin` |
| `OX["xxxxxxoo"]` | `(Hexagram.kun, Shi.dao)` |
| `OX["xxxxxxxx"]` | `(Hexagram.kun, Shi.jin)` |
| `OX["ooooooxo"]` | `(Hexagram.qian, Shi.ji)` 即 `Cell256.yin_mask` |
| `OX["ooooooox"]` | `(Hexagram.qian, Shi.wei)` 即 `Cell256.tou_mask` |
| `OX["ooooooxx"]` | `(Hexagram.qian, Shi.jin)` 即 印 ∘ 投 之 V₄ 中心 mask |

---

## 9. 设计取舍 / 边界

### 9.1 为何 inner-to-outer (而不是相反)

约定 `string[0] = y₁ = 初爻` 是因为 [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) 的 `Hexagram` 结构 field 顺序就是 `y1, y2, ..., y6`，且 `Hexagram.qian = ⟨yang, yang, yang, yang, yang, yang⟩` 即 `OX["oooooooo"]`。这与古典 Yi 之"自下而上读爻"一致。

代价：与某些 King Wen 文献 (1=最上) 顺序相反。
收益：与 Lean ground truth 字面一致；macro 展开零字段重排。

### 9.2 为何 `o` = yang, `x` = yin

`o` 是「圆 / 满 / 无形破」之直观；`x` 是「断 / 截 / 形破」。配 (Z/2)⁸ origin 设计：

- `Hexagram.qian` (全 yang) = `OX["oooooo··"]` — 即 (Z/2)⁶ zero / additive identity
- `Cell256.origin` = (qian, dao) = `OX["oooooooo"]` — (Z/2)⁸ zero
- 任何 mask 之非零位用 `x` — 与 XOR 的「翻位」语义一致

候选记号比较：

| 候选 | 优点 | 缺点 |
|---|---|---|
| **`o`/`x`** (当前) | 视觉对称, 1-char ASCII, 与古文「阳」「阴」之笔划疏密对应（o 圆=空=阳；x 交=塞=阴）| 与英文 yang/yin 首字母不齐 |
| `0`/`1` | 与 (Z/2)⁸ binary 直接 | `0` 与 `O` 视觉混淆；缺乏阴阳 anchoring |
| `+`/`-` | 物理 anchoring (sign) | 在 string 中作为字符不直观 |
| `T`/`F` | 与 Bool 直接 | `T` 在 trigram 表达上歧义（T=top? T=tao?）|

`o`/`x` 是项目早期约定，已贯穿全文档与 Lean 代码。

### 9.3 为何不支持空白 / 分隔

设计上 `OX["ooo|oooo|x"]` (含分隔符) 会触发 length > 8 之 error。如果未来需要可读分组（如 `OX["oooooo|xx"]`），可在宏前预过滤分隔符，但当前版本**不支持**以保 macro 之 minimal 与 unambiguous。

可读性：`OX["xxxxxxoo"]` 与 `OX["xxxxxx_oo"]` 之差是 1 字符，节省。
解析速度：固定 8 字符，无需 separator-split。
ground truth：Lean 之 `Hexagram × YinBit × GuoBit` 是 6+1+1 但作为 (Z/2)⁸ 整体处理。

### 9.4 为何 case-sensitive

只接受小写 `o` / `x`；`X` / `O` 都触发 invalid-char error。这是为了**保证 grep-able**（搜索 `OX["x` 总是命中合法 set bit；`OX["X` 命中错误 input）。

### 9.5 OX **不**做的事

| 不做 | 原因 |
|---|---|
| 不接受动态字符串 (runtime String) | macro 仅展开**编译期已知**字符串字面量 |
| 不支持低于 R₈ 的层（R₇ Cell128, R₆ Hexagram, ...）字面量 | 设计专注 R₈；低维通过 OX 之投影获得 |
| 不接受其它字符（即使 `_` 作 placeholder） | 设计严格；任何非 `o`/`x` 字符都视为错误 |
| 不参与 V₄ outer 算子（zong/hu）的 syntax-level rewriting | OX 仅是字面量；算子另用 fn 形式调用 |

### 9.6 不在 OX 之内 (但相邻)

- **Trigram OX**：未实现。可考虑 `OX3["..."]` 接受 3-char 字符串展开为 Trigram。当前需 `Trigram.mk Yao.yang Yao.yin Yao.yang` 直接写。
- **Cell128 OX**：未实现。可考虑 `OX7["..."]` 接受 7-char 字符串展开为 Cell128 = Hex × YinBit。当前对应需 `(Hexagram.mk ..., true)` 形式。
- **Mian OX**：可考虑 `OX4["..."]` 但 Mian 之 4 字符到 (Ben, Zheng) 双射有命名歧义，未急。

均为后续可选扩展，**不属当前 v3 scope**。

---

## 10. 与其他文档之关系

| 文档 | 关系 |
|---|---|
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) | parent doctrine — R-O 双层级 strict-uniform |
| [`yi-calculus-theorem.md`](yi-calculus-theorem.md) | Theorem H/I/J 给 R₇/R₈/Shi V₄ 形式陈述 |
| [`cell256-grid.md`](cell256-grid.md) | 用 OX 字面表 256 元清单 |
| [`v4-shi.md`](v4-shi.md) § 3 | 位 6/7 之 (因, 果) → Shi V₄ 重构 |
| [`yin-tou-operators.md`](yin-tou-operators.md) | 印/投 之 mask 字面 |
| [`lift-project.md`](lift-project.md) | Lift/Project 函数 — OX 字符串之投影语义 |
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 2.1 | 元 (state) — bit string 命名约定 |
| [`cell256-algebra.md`](cell256-algebra.md) | OX 字面对应的 Cell256 群操作语义 |
| [`r5-wuyao-provisional.md`](r5-wuyao-provisional.md) | R₅ 五爻 — OX 不直接接触此层（5-char OX 未实现）|
| [`r7-yin-r8-guo.md`](r7-yin-r8-guo.md) | R₇/R₈ 因/果 axes — OX 第 6/7 位之 ontology |

---

## 附录 A：术语对照

| OX 概念 | 在 R-hierarchy | 在 Lean | 在物理 |
|---|---|---|---|
| 8-char string | R₈ literal | Cell256 term | 8-bit byte |
| `o` | identity bit | Yao.yang / false | +1 |
| `x` | set bit | Yao.yin / true | -1 |
| 位置 0..5 | R₆ Hexagram (内→外) | Hexagram.y1..y6 | 6-spin chain |
| 位置 6 | R₇ atom 因 | YinBit | past-cone marker |
| 位置 7 | R₈ atom 果 | GuoBit | future-cone marker |
| 位置 6+7 | R₈ Shi V₄ | Shi via ofYinGuo | (P, T) 双 axis |
| `OX["oooooooo"]` | R₈ origin = 道 | Cell256.origin | reference vacuum |

---

## 附录 B：完整 macro 源码

来自 [`Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean)：

```lean
namespace SSBX.Foundation.Notation.OXNotation

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open Lean

/-- `OX[" o/x ×8 "]` term-level macro producing a `Cell256`. -/
syntax (name := oxLit) "OX[" str "]" : term

private def yaoStxOfChar (c : Char) : MacroM (TSyntax `term) :=
  match c with
  | 'o' => `(SSBX.Foundation.Yi.Yi.Yao.yang)
  | 'x' => `(SSBX.Foundation.Yi.Yi.Yao.yin)
  | _   => Macro.throwError s!"OX: invalid char '{c}' (only 'o' and 'x' allowed)"

private def boolStxOfChar (c : Char) : MacroM (TSyntax `term) :=
  match c with
  | 'o' => `(false)
  | 'x' => `(true)
  | _   => Macro.throwError s!"OX: invalid char '{c}' (only 'o' and 'x' allowed)"

@[macro oxLit]
def expandOxLit : Macro := fun stx => do
  match stx with
  | `(OX[ $s:str ]) =>
    let str := s.getString
    match str.toList with
    | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      for c in [c0, c1, c2, c3, c4, c5, c6, c7] do
        unless c = 'o' || c = 'x' do
          Macro.throwError
            s!"OX: invalid char '{c}' in \"{str}\" (only 'o' and 'x' allowed)"
      let y1 ← yaoStxOfChar c0
      let y2 ← yaoStxOfChar c1
      let y3 ← yaoStxOfChar c2
      let y4 ← yaoStxOfChar c3
      let y5 ← yaoStxOfChar c4
      let y6 ← yaoStxOfChar c5
      let yinB ← boolStxOfChar c6
      let guoB ← boolStxOfChar c7
      `((SSBX.Foundation.Yi.Yi.Hexagram.mk
            $y1 $y2 $y3 $y4 $y5 $y6,
         SSBX.Foundation.Bagua.Cell256.Shi.ofYinGuo ($yinB, $guoB)))
    | _ =>
      Macro.throwError
        s!"OX: string must have length 8, got {str.length} (\"{str}\")"
  | _ => Macro.throwUnsupported

end SSBX.Foundation.Notation.OXNotation
```

---

## 形式锚 (Lean modules)

- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["..."]` macro 全文（语法、validation、expansion、8 examples）
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `Cell256`, `Shi.ofYinGuo`, `Cell256.origin`
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — YinBit 定义；OX 第 6 位之 type
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Yao.yang / yin`, `Hexagram.mk`, `Hexagram.qian / kun`
