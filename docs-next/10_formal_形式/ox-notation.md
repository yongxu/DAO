# OX["..."] 字面量 — 8-char Cell256 macro 完整参考

> 状态：v3 canonical (2026-05-11) — `OX["..."]` 是 Cell256 之首选字面量记法，8 个 `o` / `x` 字符直接编码 (Z/2)⁸ = 256 元中的任意一格。
> 角色：本文是 OX 宏的语法 / 语义 / 错误 / 用例完整参考。Cell256 之内容清单见 [`cell256-grid.md`](cell256-grid.md)；位 6/7 = (因, 果) 之 V₄ 重构见 [`v4-shi.md`](v4-shi.md)；印 / 投 之 OX mask 形式见 [`yin-tou-operators.md`](yin-tou-operators.md)。
> 形式锚：[`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) 全文。

---

## 0. 一句话总纲

> **`OX["abcdefgh"]` : Cell256** — 8 个字符必须全为 `o` 或 `x`；前 6 个 `(a..f)` 是 hexagram 的 6 爻 (inner-to-outer = 初爻..上爻，`o` = yang, `x` = yin)；第 7 字符 `g` 是 因 / YinBit；第 8 字符 `h` 是 果 / GuoBit；macro 在 parse-time 验证长度与字符集，错误抛 `Macro.throwError`。

---

## 1. 语法

```
OX[ "<8 chars from {o, x}>" ]
```

- **最外层**：term-level 语法，可以出现在任何 Cell256 表达式位置。
- **字符串内**：必须长度 = 8，每字符 ∈ `{'o', 'x'}`，否则 macro elaboration 失败。
- **类型**：always elaborates to `Cell256 = Hexagram × Shi`。

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

Shi 通过 `Shi.ofYinGuo (yinBit, guoBit)` 重构（详 [`v4-shi.md`](v4-shi.md) § 3）：

| char 6 | char 7 | (因, 果) | Shi |
|---|---|---|---|
| `o` | `o` | (false, false) | 道 (dao, V₄ identity) |
| `x` | `o` | (true,  false) | 已 (ji) |
| `o` | `x` | (false, true)  | 未 (wei) |
| `x` | `x` | (true,  true)  | 今 (jin, PT central) |

---

## 3. 实现细节

[`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) § 1 之运行时 helper：

```lean
@[inline] def yaoOfChar : Char → Yao
  | 'x' => Yao.yin
  | _   => Yao.yang  -- 'o' 与其他都视为 yang (但 macro 已验过字符集)

@[inline] def boolOfChar : Char → Bool
  | 'x' => true
  | _   => false

def cellOfString (s : String) : Cell256 :=
  match s.toList with
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      (⟨yaoOfChar c0, yaoOfChar c1, yaoOfChar c2,
        yaoOfChar c3, yaoOfChar c4, yaoOfChar c5⟩,
       Shi.ofYinGuo (boolOfChar c6, boolOfChar c7))
  | _ => (Hexagram.qian, Shi.dao)  -- unreachable when macro validates length
```

§ 2 之 macro expansion：

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
      -- 然后构造 Hexagram.mk + Shi.ofYinGuo
      ...
    | _ =>
      Macro.throwError
        s!"OX: string must have length 8, got {str.length} (\"{str}\")"
  | _ => Macro.throwUnsupported
```

---

## 4. 错误语义 (parse-time)

| 错误 | 触发 | 错信息 |
|---|---|---|
| 长度 ≠ 8 | `OX["ooooo"]` (5 字符), `OX["ooooooooo"]` (9 字符), `OX[""]` (0 字符) | `OX: string must have length 8, got N ("...")` |
| 字符 ∉ `{o, x}` | `OX["aoooooooo"]`, `OX["oooo1ooo"]`, 大写 `OX["XXXXXXXX"]`, 中文 `OX["o好oooooo"]` | `OX: invalid char 'c' in "..." (only 'o' and 'x' allowed)` |

错误在 **macro elaboration time** 抛出（即 Lean 编译/elaboration 阶段），所以 invalid OX literals **绝不会** runtime fail — 它们根本无法过编译。

---

## 5. 端到端示例 — `rfl` 可证

[`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) § 3 / § 4 之 examples 全部 `:= rfl` — 也就是说每个 OX 字面量在 elaboration 后**直接** equal 到对应的 Lean 显式构造，无需 simp / decide。

### 5.1 origin

```lean
/-- All-`o` 8-string = (qian, dao) = Cell256.origin = (Z/2)⁸ identity. -/
example : OX["oooooooo"] = (Hexagram.qian, Shi.dao) := rfl

/-- `OX["oooooooo"]` 是 Cell256.origin. -/
example : OX["oooooooo"] = (Cell256.origin : Cell256) := rfl
```

### 5.2 Shi 之四态（hex 部分 = 乾）

```lean
/-- Char 7 = `x` flips YinBit only ⇒ Shi.ji (已). -/
example : OX["ooooooxo"] = (Hexagram.qian, Shi.ji) := rfl

/-- Char 8 = `x` flips GuoBit only ⇒ Shi.wei (未). -/
example : OX["ooooooox"] = (Hexagram.qian, Shi.wei) := rfl

/-- Both Shi bits set ⇒ Shi.jin (今, PT central element). -/
example : OX["ooooooxx"] = (Hexagram.qian, Shi.jin) := rfl
```

### 5.3 hex 部分 = 坤

```lean
/-- All-`x` Hexagram part = Hexagram.kun (all yin); Shi.jin (PT). -/
example : OX["xxxxxxxx"] = (Hexagram.kun, Shi.jin) := rfl
```

### 5.4 单爻翻转

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

### 5.5 混合 (hex 内多翻 + Shi.wei)

```lean
/-- Mixed cell: hexagram-internal flip + Shi.wei. -/
example :
    OX["xoxoxoox"] =
      (Hexagram.mk Yao.yin Yao.yang Yao.yin Yao.yang Yao.yin Yao.yang,
       Shi.wei) := rfl
```

8 个 examples 一齐 ack 了 macro 的端到端 round-trip：字符 → 6 yao + (因, 果) → Shi reconstruction → Cell256 字面量。

---

## 6. 印 / 投 mask 之 OX 字面写法

按本约定：

| OX | 解读 |
|---|---|
| `OX["ooooooxo"]` | Cell256.yin_mask = (qian, ji) — 印之 mask |
| `OX["ooooooox"]` | Cell256.tou_mask = (qian, wei) — 投之 mask |
| `OX["ooooooxx"]` | yin_mask ⊕ tou_mask = (qian, jin) — V₄ 中央元 = 错综 (cuoZong) |

详 [`yin-tou-operators.md`](yin-tou-operators.md) § 3.1。

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

### 8.2 cuo 之 mask

| cuo (in [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 4.2) | OX |
|---|---|
| Hex side cuo (XOR with kun-mask) | `OX["xxxxxxoo"]` (preserves Shi) |
| Shi side cuo (Shi.cuo = 印 = toggle YinBit) | `OX["ooooooxo"]` |
| Full cuo (both axes) | `OX["xxxxxxxo"]` 或 `OX["xxxxxxox"]` 之类，依具体语义 |

---

## 9. 设计取舍 / 边界

### 9.1 为何 inner-to-outer (而不是相反)

约定 `string[0] = y₁ = 初爻` 是因为 [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) 的 `Hexagram` 结构 field 顺序就是 `y1, y2, ..., y6`，且 `Hexagram.qian = ⟨yang, yang, yang, yang, yang, yang⟩` 即 `OX["oooooooo"]`。这与古典 Yi 之"自下而上读爻"一致。

### 9.2 为何 `o` = yang, `x` = yin

`o` 是「圆 / 满 / 无形破」之直观；`x` 是「断 / 截 / 形破」。配 (Z/2)⁸ origin 设计：

- `Hexagram.qian` (全 yang) = `OX["oooooo··"]` — 即 (Z/2)⁶ zero / additive identity
- `Cell256.origin` = (qian, dao) = `OX["oooooooo"]` — (Z/2)⁸ zero
- 任何 mask 之非零位用 `x` — 与 XOR 的「翻位」语义一致

### 9.3 为何不支持空白 / 分隔

设计上 `OX["ooo|oooo|x"]` (含分隔符) 会触发 length > 8 之 error。如果未来需要可读分组（如 `OX["oooooo|xx"]`），可在宏前预过滤分隔符，但当前版本**不支持**以保 macro 之 minimal 与 unambiguous。

### 9.4 为何 case-sensitive

只接受小写 `o` / `x`；`X` / `O` 都触发 invalid-char error。这是为了**保证 grep-able**（搜索 `OX["x` 总是命中合法 set bit；`OX["X` 命中错误 input）。

---

## 10. 与其他文档之关系

| 文档 | 关系 |
|---|---|
| [`cell256-grid.md`](cell256-grid.md) | 用 OX 字面表 256 元清单 |
| [`v4-shi.md`](v4-shi.md) § 3 | 位 6/7 之 (因, 果) → Shi V₄ 重构 |
| [`yin-tou-operators.md`](yin-tou-operators.md) | 印/投 之 mask 字面 |
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 2.1 | 元 (state) — bit string 命名约定 |
| [`cell256-algebra.md`](cell256-algebra.md) | OX 字面对应的 Cell256 群操作语义 |

---

## 形式锚 (Lean modules)

- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["..."]` macro 全文（语法、validation、expansion、8 examples）
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `Cell256`, `Shi.ofYinGuo`, `Cell256.origin`
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Yao.yang / yin`, `Hexagram.mk`, `Hexagram.qian / kun`
