# OX 8-字符记号 — `OX["..."]` Cell256 字面量宏

> 状态：v3 定本 (2026-05-11)
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ strict-uniform doctrine)
> 配套：[shi-v4.md](shi-v4.md) · [lift-project.md](lift-project.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md)
> 形式锚：[`Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean)

---

## 第一部分：目的 (Purpose)

`OX["xxxxxxxx"]` 是一个 **Lean 4 macro**，把 8 字符 ASCII 字符串（仅含 `o` 与 `x`）展开为 `Cell256 = Hexagram × Shi`，即 R₈ 之 256 格中的某个 cell。

### 1.1 为何需要这个记号

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

### 1.2 与 R-hierarchy 的关系

OX 仅刻画 R₈（256-cell）层。低维层（R₁..R₇）通过 OX 的**前缀**或**投影**间接表达：例如 `OX["oooooooo"]` 的前 6 字符 `oooooo` 即 Hexagram.qian (R₆ identity)，前 3 字符 `ooo` 即 Trigram 乾 (R₃)。

---

## 第二部分：字符布局 (Char Layout)

OX 字符串 **必须为 8 字符**，每位含义如下（位置 0-indexed）：

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

**Lean ground truth** ([`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) 文件 docstring)：

```
- chars 0..5 (positions 1..6): six yao of the Hexagram, **inner-to-outer**
                                (string[0] = y1 = 初爻, string[5] = y6 = 上爻).
                                `o` → identity bit → `Yao.yang`,
                                `x` →   set    bit → `Yao.yin`.
- char 6 : YinBit (因 axis, R5)   `o` → false, `x` → true.
- char 7 : GuoBit (果 axis, R6)   `o` → false, `x` → true.
```

### 2.1 Inner-to-outer 顺序

注意：OX 之 6 个 hexagram 字符**自内向外**（initial-yao 首先），与 King Wen 文献某些版本（自上而下）相反。这与 `Hexagram.mk y1 y2 y3 y4 y5 y6` 之 Lean 字段序一致。

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

位置 6+7 之 (`o`/`x`) 双字符通过 `Shi.ofYinGuo` 映回 V₄ 四态：

| (位置 6, 位置 7) = (因, 果) | Shi | V₄ 角色 |
|---|---|---|
| (`o`, `o`) = (false, false) | 道 (dao) | identity |
| (`x`, `o`) = (true, false) | 已 (ji) | σ_P |
| (`o`, `x`) = (false, true) | 未 (wei) | σ_T |
| (`x`, `x`) = (true, true) | 今 (jin) | σ_PT |

详见 [shi-v4.md](shi-v4.md)。

---

## 第三部分：编码规则 (Encoding)

### 3.1 字符到 Lean 之映射

```lean
@[inline] def yaoOfChar : Char → Yao
  | 'x' => Yao.yin
  | _   => Yao.yang  -- treats 'o' (and anything else, validated by macro) as yang

@[inline] def boolOfChar : Char → Bool
  | 'x' => true
  | _   => false
```

(摘自 `OXNotation.lean` § 1)

### 3.2 字符串到 Cell256 (helper)

```lean
def cellOfString (s : String) : Cell256 :=
  match s.toList with
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      (⟨yaoOfChar c0, yaoOfChar c1, yaoOfChar c2,
        yaoOfChar c3, yaoOfChar c4, yaoOfChar c5⟩,
       Shi.ofYinGuo (boolOfChar c6, boolOfChar c7))
  | _ => (Hexagram.qian, Shi.dao)  -- unreachable when macro validates length
```

(摘自 `OXNotation.lean` § 1，runtime helper；macro 在 elab-time 走另一路径见下文 § 4。)

---

## 第四部分：Macro 实现 (Macro Implementation)

OX 之实现核心是 Lean 4 之 **`syntax` + `Macro.expand` 双层**：在 elaboration 阶段把 `OX["..."]` 替换为 `(Hexagram.mk ..., Shi.ofYinGuo (..., ...))` term。

### 4.1 Syntax 声明

```lean
/-- `OX[" o/x ×8 "]` term-level macro producing a `Cell256`. -/
syntax (name := oxLit) "OX[" str "]" : term
```

(摘自 `OXNotation.lean` § 2)

声明 `OX[ <str> ]` 是 term-level 语法。`<str>` 是任意 Lean 字符串字面量。

### 4.2 Macro 展开

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

(摘自 `OXNotation.lean` § 2)

### 4.3 字符 → Lean term 之子函数

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

(摘自 `OXNotation.lean` § 2)

### 4.4 流程 (Pipeline)

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

## 第五部分：示例 (Examples)

以下是 `OXNotation.lean` § 3 / § 4 中之 `example`，每条都用 `:= rfl` 闭合 — 即编译器**当时**化简到字面相等。

### 5.1 Origin / 道

```lean
/-- All-`o` 8-string = (qian, dao) = Cell256.origin = (Z/2)⁸ identity. -/
example : OX["oooooooo"] = (Hexagram.qian, Shi.dao) := rfl

/-- `OX["oooooooo"]` is exactly `Cell256.origin`. -/
example : OX["oooooooo"] = (Cell256.origin : Cell256) := rfl
```

`OX["oooooooo"]` 是整个 R₈ 的 origin / identity / 道（参考 [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.0 道之 anchor 角色）。

### 5.2 Shi 四态在 (qian, ·) 上

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

### 5.3 Hexagram 全反 + Shi.jin

```lean
/-- All-`x` Hexagram part = Hexagram.kun (all yin); Shi.jin (PT). -/
example : OX["xxxxxxxx"] = (Hexagram.kun, Shi.jin) := rfl
```

注意：`OX["xxxxxxxx"]` 不是 (kun, 道)，因为最后两位 `xx` 编码为 Shi.jin (PT)。如果想要 (kun, 道)，需写 `OX["xxxxxxoo"]`。

### 5.4 单爻翻 (single yao flip)

```lean
/-- Hexagram only (Shi = dao): char 0 = y1 = `x` flips initial yao only. -/
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

### 5.5 混合 (mixed): hexagram 部分翻 + Shi.wei

```lean
/-- Mixed cell: hexagram-internal flip + Shi.wei. -/
example :
    OX["xoxoxoox"] =
      (Hexagram.mk Yao.yin Yao.yang Yao.yin Yao.yang Yao.yin Yao.yang,
       Shi.wei) := rfl
```

读法：

- y₁=yin, y₂=yang, y₃=yin, y₄=yang, y₅=yin, y₆=yang → `离 ☲ 重` 卦的某 hex (注：实际 hexagram 命名见 64-hexagram-grid.md)
- (因, 果) = (`o`, `x`) = (false, true) = Shi.wei (未)

### 5.6 256 个具体 cell 之全集

OX 是 R₈ 的全枚举字面量化器：256 个不同 8-字符字符串恰好对应 256 cells（`o`/`x` 共 2⁸ = 256 种）。

---

## 第六部分：错误情形 (Error Cases)

OX 在 macro expansion 阶段（编译期）做两类校验，错误**直接报告 elaboration error**，不会进入 runtime。

### 6.1 长度 ≠ 8

```lean
/- Expected: error -/
-- example : Cell256 := OX["ooo"]
-- elab error: OX: string must have length 8, got 3 ("ooo")

-- example : Cell256 := OX["oooooooooo"]
-- elab error: OX: string must have length 8, got 10 ("oooooooooo")
```

错误信息精确到字符串内容与实际长度。源代码：

```lean
| _ =>
  Macro.throwError
    s!"OX: string must have length 8, got {str.length} (\"{str}\")"
```

### 6.2 字符 ∉ {`o`, `x`}

```lean
/- Expected: error -/
-- example : Cell256 := OX["oooooooy"]
-- elab error: OX: invalid char 'y' in "oooooooy" (only 'o' and 'x' allowed)

-- example : Cell256 := OX["AAAAAAAA"]
-- elab error: OX: invalid char 'A' in "AAAAAAAA" (only 'o' and 'x' allowed)

-- example : Cell256 := OX["oooooooo "]  -- 含空格
-- elab error: OX: string must have length 8, got 9 (...)
```

错误信息精确到第一个非 `o`/`x` 字符。源代码：

```lean
for c in [c0, c1, c2, c3, c4, c5, c6, c7] do
  unless c = 'o' || c = 'x' do
    Macro.throwError
      s!"OX: invalid char '{c}' in \"{str}\" (only 'o' and 'x' allowed)"
```

### 6.3 大小写 / Unicode

OX 仅接受 ASCII `'o'` 和 `'x'`。大写 `'O'` / `'X'` **被拒绝**（不是 lookup-failure 默认到 yang，是显式 elab error）。Unicode 全角 `'ｏ'` / `'ｘ'` 同被拒绝。

---

## 第七部分：在证明 / `decide` 中之使用

### 7.1 `rfl` 闭合（最常见）

任意 OX 字面量 `=` 等价之 ctor 形式可由 `rfl` 闭合，因为 macro 展开是 *definitional*。

```lean
example : OX["oooooooo"] = Cell256.origin := rfl
example : OX["xxxxxxoo"] = (Hexagram.kun, Shi.dao) := rfl
```

### 7.2 在 `decide` / `native_decide` 中

OX 字面量在 `decide` 中**直接**化简，可用于 finite property check：

```lean
example : Cell256.flip1 OX["oooooooo"] = OX["xooooooo"] := by decide
example : Cell256.tou OX["oooooooo"] = OX["ooooooox"] := by decide
example : Cell256.yin (Cell256.tou OX["oooooooo"]) = OX["ooooooxx"] := by decide
```

（最后一行：印 ∘ 投 = V₄ 中心元，把 (因, 果) 同时翻 ⇒ Shi.jin = `xx`）

### 7.3 在算子声明中

OX 适合写出 mask（即 V₄ atomic XOR 之 fixed mask）：

```lean
-- 印 mask: only YinBit set
def yin_mask_alt : Cell256 := OX["ooooooxo"]
example : yin_mask_alt = Cell256.yin_mask := rfl

-- 投 mask: only GuoBit set
def tou_mask_alt : Cell256 := OX["ooooooox"]
example : tou_mask_alt = Cell256.tou_mask := rfl
```

参考 [r7-yin-r8-guo.md](r7-yin-r8-guo.md) § 4 印/投 mask 之刻画。

### 7.4 在表格 / 文档中

OX 之最大价值在跨文档一致：64-hexagram-grid.md / sanben-sijieduan-grid.md 等所有 cell 引用都用 OX 形式。

---

## 第八部分：与其它表示之对应

### 8.1 OX ↔ Lean ctor

| OX | Lean 等价 |
|---|---|
| `OX["oooooooo"]` | `(Hexagram.qian, Shi.dao)` 即 `Cell256.origin` |
| `OX["xxxxxxoo"]` | `(Hexagram.kun, Shi.dao)` |
| `OX["xxxxxxxx"]` | `(Hexagram.kun, Shi.jin)` |
| `OX["ooooooxo"]` | `(Hexagram.qian, Shi.ji)` 即 `Cell256.yin_mask` |
| `OX["ooooooox"]` | `(Hexagram.qian, Shi.wei)` 即 `Cell256.tou_mask` |
| `OX["ooooooxx"]` | `(Hexagram.qian, Shi.jin)` 即 印 ∘ 投 之 V₄ 中心 mask |

### 8.2 OX ↔ R-hierarchy 投影

| 操作 | OX 形式 | 说明 |
|---|---|---|
| 取前 6 字符 → R₆ | `OX["abcdef--"]` 之 `abcdef` 段 | Hexagram (drop Shi) |
| 取前 3 字符 → R₃ | `OX["abc-----"]` 之 `abc` 段 | inner Trigram |
| 第 6/7 字符 → R₈ Shi | `OX["------yg"]` 之 `yg` 段 | (因, 果) ∈ Bool² |
| 第 6 字符 → R₇ YinBit | `OX["------y-"]` 之 `y` 字符 | YinBit 仅 |

参考 [lift-project.md](lift-project.md) 给出的精确 Lift / Project 函数。

### 8.3 OX ↔ V₄ 算子作用

`Cell256.yin / Cell256.tou` 之 effect 完全由 OX 后两位描述：

| 输入 | 操作 | 输出 |
|---|---|---|
| `OX["......oo"]` | yin | `OX["......xo"]` |
| `OX["......xo"]` | yin | `OX["......oo"]` |
| `OX["......oo"]` | tou | `OX["......ox"]` |
| `OX["......oo"]` | yin ∘ tou | `OX["......xx"]` |

详见 [shi-v4.md](shi-v4.md) § 5 V₄ Klein 群运算表。

---

## 第九部分：设计 trade-offs

### 9.1 为何 inner-to-outer (vs outer-to-inner)

Lean 之 `Hexagram.mk y1 ... y6` 字段顺序 = inner-to-outer（y1 = 初爻 = 最内）。OX 与之严格对齐，避免读写时反序。

代价：与某些 King Wen 文献 (1=最上) 顺序相反。
收益：与 Lean ground truth 字面一致；macro 展开零字段重排。

### 9.2 为何 `o`/`x` (vs 0/1, +/-, T/F)

| 候选 | 优点 | 缺点 |
|---|---|---|
| **`o`/`x`** (当前) | 视觉对称, 1-char ASCII, 与古文「阳」「阴」之笔划疏密对应（o 圆=空=阳；x 交=塞=阴）| 与英文 yang/yin 首字母不齐 |
| `0`/`1` | 与 (Z/2)⁸ binary 直接 | `0` 与 `O` 视觉混淆；缺乏阴阳 anchoring |
| `+`/`-` | 物理 anchoring (sign) | 在 string 中作为字符不直观 |
| `T`/`F` | 与 Bool 直接 | `T` 在 trigram 表达上歧义（T=top? T=tao?）|

`o`/`x` 是项目早期约定，已贯穿全文档与 Lean 代码。

### 9.3 为何 8 字符 (vs 6+1+1 separators)

可读性：`OX["xxxxxxoo"]` 与 `OX["xxxxxx_oo"]` 之差是 1 字符，节省。
解析速度：固定 8 字符，无需 separator-split。
ground truth：Lean 之 `Hexagram × YinBit × GuoBit` 是 6+1+1 但作为 (Z/2)⁸ 整体处理。

---

## 第十部分：边界 (Boundaries)

### 10.1 OX **不**做的事

| 不做 | 原因 |
|---|---|
| 不接受动态字符串 (runtime String) | macro 仅展开**编译期已知**字符串字面量 |
| 不支持低于 R₈ 的层（R₇ Cell128, R₆ Hexagram, ...）字面量 | 设计专注 R₈；低维通过 OX 之投影获得 |
| 不接受其它字符（即使 `_` 作 placeholder） | 设计严格；任何非 `o`/`x` 字符都视为错误 |
| 不参与 V₄ outer 算子（zong/hu）的 syntax-level rewriting | OX 仅是字面量；算子另用 fn 形式调用 |

### 10.2 不在 OX 之内 (但相邻)

- **Trigram OX**：未实现。可考虑 `OX3["..."]` 接受 3-char 字符串展开为 Trigram。当前需 `Trigram.mk Yao.yang Yao.yin Yao.yang` 直接写。
- **Cell128 OX**：未实现。可考虑 `OX7["..."]` 接受 7-char 字符串展开为 Cell128 = Hex × YinBit。当前对应需 `(Hexagram.mk ..., true)` 形式。
- **Mian OX**：可考虑 `OX4["..."]` 但 Mian 之 4 字符到 (Ben, Zheng) 双射有命名歧义，未急。

均为后续可选扩展，**不属当前 v3 scope**。

---

## 附录 A：完整 macro 源码摘要

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

## 附录 B：术语对照

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

## 附录 C：与其它文档之关系

| 文档 | 与本文关系 |
|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | parent doctrine — R-O 双层级 strict-uniform |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorem H/I/J 给 R₇/R₈/Shi V₄ 形式陈述 |
| [shi-v4.md](shi-v4.md) | Shi V₄ Klein 结构 — OX 后 2 位之精确含义 |
| [lift-project.md](lift-project.md) | Lift/Project 函数 — OX 字符串之投影语义 |
| [r5-wuyao-provisional.md](r5-wuyao-provisional.md) | R₅ 五爻 — OX 不直接接触此层（5-char OX 未实现）|
| [r7-yin-r8-guo.md](r7-yin-r8-guo.md) | R₇/R₈ 因/果 axes — OX 第 6/7 位之 ontology |
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | OX 之展开目标 type Cell256 |
| [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | YinBit 定义；OX 第 6 位之 type |
| [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) | **本文档之 ground truth source** |
