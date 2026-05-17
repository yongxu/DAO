# Wen by Example

**Date**: 2026-05-18 · **Status**: 草稿 (drafting; Chapter 1 verified, 9 more to come)

A worked-example walkthrough of the Wen language. Every example is **run-verified** in the `wen` REPL (`lake build wen && ./.lake/build/bin/wen`). Where an example doesn't work, that's noted explicitly — those are real gaps in the language, not in the doc.

For the language reference, see [`wen-spec.md`](wen-spec.md).

---

## 体例 (Conventions)

Each example shows:
- **文言** (the actual Wen source)
- **REPL output** (verbatim from `wen`)
- **义** (explanation: what's happening + why it matters)
- **试 (Try)** — variations to explore

REPL prompt is `≫ `. Output for Hex values is `«name» (bit-pattern) : Hex` where the bit pattern reads `y1 y2 y3 y4 y5 y6` low-to-high, with `1 = 阳 (yang)` and `0 = 阴 (yin)`.

---

# Chapter 1 — 数与象 (numbers, hexagrams, booleans)

How does Wen represent numbers? Not as Arabic digits — Wen has no integers. The kernel knows two atomic worlds:

- **Hex** (卦) — the 64 hexagrams of 易经. Each is a 6-bit pattern. They are Wen's "small numbers" (cardinality 64) and Wen's geometry (the 卦象 forms).
- **Bool** (真假) — `真` (true) and `假` (false). Used for predicates and queries.

Everything else (functions, products, lists, sets) is built from these by composition.

---

## 1.1  「一」是 姤

```
≫ 一
«姤» (011111) : Hex
```

**义**: `一` is a Hex literal — a name for a specific hexagram. It evaluates to **姤** (King-Wen #44, 天風姤), whose bit pattern is `011111`. Reading right-to-left: `阴, 阳, 阳, 阳, 阳, 阳` — five solid yang lines with one yin at the bottom.

Why is `一` paired with 姤? Because 姤 is the hex with **exactly one** 阴 — the "first one" emerging from pure 阳 (乾). In Wen, "one" means "first appearance" in the cosmological sense, not the cardinal sense.

Compare:

```
≫ 乾
«乾» (111111) : Hex
≫ 坤
«坤» (000000) : Hex
≫ 泰
«泰» (111000) : Hex
```

- `乾` (heaven) — all 阳, no 阴
- `坤` (earth) — all 阴, no 阳
- `泰` (peace) — 阳 below, 阴 above (天地交合)

**试**:
- 同人 (`«同人» (101111) : Hex`?) — "fellowship", 1 阴 in the middle?
- 复 (`«复» (100000) : Hex`?) — "return", 1 阳 at the bottom?

---

## 1.2  错 — 阴阳反转

```
≫ 错 一
«复» (100000) : Hex
≫ 错 乾
«坤» (000000) : Hex
≫ 错 坤
«乾» (111111) : Hex
```

**义**: `错` (cuò) is the **complement** operation — flip every yao (line). 一 (`011111`) becomes 复 (`100000`); 乾 becomes 坤; 坤 becomes 乾.

`错` has type `Hex → Hex`:

```
≫ :t 错
Hex → Hex
```

`错` is an **involution**: applying it twice returns the original.

```
≫ 错 错 一
«姤» (011111) : Hex
```

Yes — 一 = 姤. The double complement is identity.

**试**:
- 错 (错 (错 乾)) — three complements
- 错 同人 — what's 同人 's mirror?

---

## 1.3  综 与 互 — 重排之象

```
≫ 综 一
«夬» (111110) : Hex
≫ 互 一
«乾» (111111) : Hex
≫ 错综 一
«剥» (000001) : Hex
```

**义**: Three more Hex → Hex transforms:

- **综** (zōng) — 反转 (reverse the 6 lines top-to-bottom). 一 `011111` reversed is `111110` = 夬.
- **互** (hù) — 互卦 (interlocking: take 爻 2-3-4 as the inner trigram, 3-4-5 as the outer, recombine). 一's 互 is the 6-yang 乾.
- **错综** (cuòzōng) — both complement and reverse, in that order. 一 → 复 (100000) → 剥 (000001).

These are the four **basic transformations** in classical 易经 commentary: 错 (yin-yang inversion), 综 (top-bottom reversal), 互 (interior projection), 错综 (compound). All are Hex → Hex.

```
≫ :t 综
Hex → Hex
≫ :t 互
Hex → Hex
≫ :t 错综
Hex → Hex
```

**试**:
- 错综 乾 (= 综 (错 乾) = 综 坤 = 坤 — verify!)
- 互 互 一

---

## 1.4  同 — 等否

```
≫ 同 乾 乾
true : Bool
≫ 同 乾 坤
false : Bool
≫ 同 (错 乾) 坤
true : Bool
```

**义**: `同` (tóng) is **hex equality** — returns `Bool` true if the two Hex are the same.

```
≫ :t 同
Hex → Hex → Bool
```

`同` curries: applied to one arg, it returns a `Hex → Bool` predicate. We'll use this in §1.5 and Chapter 2.

The third example above shows the **involution** of 错 indirectly: `错 乾 = 坤`, so `同 (错 乾) 坤 = true`.

**试**:
- 同 一 (错 (错 一)) — is the double complement equal to the original? (Should be `true`.)
- 同 一 (综 (综 一)) — is double reversal equal? (Should be `true`.)

---

## 1.5  不 — 真否之反

```
≫ 不 真
false : Bool
≫ 不 假
true : Bool
≫ 不 不 真
true : Bool
≫ 不 同 乾 坤
true : Bool
```

**义**: `不` (bù) is **Boolean NOT**. Type `Bool → Bool`.

The last example shows composition: `不 (同 乾 坤)`. Since 乾 ≠ 坤, `同 乾 坤 = false`, so `不 false = true`. **Wen has no `≠` operator** — express it as `不 (同 X Y)`.

```
≫ :t 不
Bool → Bool
```

`不` is also an involution: `不 不 X = X`.

**试**:
- 不 不 假
- 不 (不 (不 真))

---

## 1.6  之又 — 迭代

```
≫ 之又 错 一
«姤» (011111) : Hex
≫ 之又 综 一
«姤» (011111) : Hex
≫ 之又 错 乾
«乾» (111111) : Hex
```

**义**: `之又` (zhī yòu) is the **iteration marker** — `之又 op arg` applies `op` twice to `arg`. Equivalent to `op (op arg)`.

Since 错 and 综 are both involutions, `之又` of them is identity. So `之又 错 一 = 一`.

This is more than a shortcut — `之又` exposes Wen's view of **operation as data**. We'll see in Chapter 9 (`执 「X」` quote-eval) that operations can be quoted and replayed, of which `之又` is the simplest case.

**试**:
- 之又 推 乾 — what does double-推 give?
- 之又 之又 错 一 — but wait, the inner `之又 错` is a `Hex → Hex`; can `之又` accept it? (Hint: try and see what error you get.)

---

## 章末 — 知 (What you can do after Chapter 1)

You can:
- Name hexagrams (`乾`, `坤`, `泰`, `一`, …)
- Transform them (`错`, `综`, `互`, `错综`)
- Compare them (`同 X Y`)
- Manipulate Booleans (`不`)
- Compose operations (`错 (综 X)`)
- Iterate (`之又 op X`)

You cannot yet:
- Define your own operations — Chapter 3 (`定`)
- Quantify (`for all X, P X`) — Chapter 5 (`凡` / `唯`)
- Pattern-match on a Hex — Chapter 6 (`析`)

**Working primitives 表** (all Hex → Hex unless noted):

| 文言 | 名 | 义 | Example |
|---|---|---|---|
| 一 | yī | hex literal (姤 011111) | `一` |
| 乾, 坤, … | 64 hex names | hex literal | `泰` → 111000 |
| 错 | cuò | complement | `错 一 → 复` |
| 综 | zōng | reverse | `综 一 → 夬` |
| 互 | hù | interlock | `互 一 → 乾` |
| 错综 | cuòzōng | complement + reverse | `错综 一 → 剥` |
| 推 | tuī | shift (Hex→Hex) | `推 一 → 同人` |
| 初爻 | flip y1 | one-yao flip | (Hex → Hex) |
| 二爻 … 上爻 | flip y2…y6 | one-yao flip | (Hex → Hex) |
| 同 | tóng | equality | Hex → Hex → Bool |
| 不 | bù | NOT | Bool → Bool |
| 真, 假 | true, false | Bool literal | |
| 之又 | zhī yòu | iterate twice | `之又 op X = op (op X)` |

**Known gaps** (验证发现):
- `加` (hex addition) — Tm.jia exists but has no surface reading. Can't use bare `加 X Y` syntax. (Reported gap; not yet fixed.)
- `並` (Bool AND) — bound to `pairH` in catalogue, not `andB`. Won't work as Boolean conjunction.
- `或` (Bool OR) — bound to modal "possibly" (M_2), not `orB`.
- `列一` / `首` (list ops) — no surface readings.

These will need surface-reading PRs before they're usable from Wen source. Until then, work around with `不` + 同 for booleans, and skip list ops entirely.

---

# Chapter 2 — λ 与 应用 (lambda and application)

*Drafting in progress.* The plan: identity `者 甲 甲`, composition `者 甲 错 之 综 之 甲`, application via grouping `(者 …) 之 X`, and the precedence story (`者` body extends to end-of-chunk).

Examples 2.1-2.5 to follow once Chapter 1 review lands.

---

# Subsequent chapters (planned)

- Chapter 3 — `定 NAME 为 BODY` (user definitions, substitution)
- Chapter 4 — `定递 NAME 为 BODY` (recursion with fuel)
- Chapter 5 — `凡 / 唯 / 三 / 過半` (quantifiers)
- Chapter 6 — `类 NAME = CTOR | …` + `析 X 为 …` (inductive + match)
- Chapter 7 — `曰 / 所…者 / 之所以` (literary surface)
- Chapter 8 — `定 LHS 等 RHS` (rewrite rules)
- Chapter 9 — `执 「X」` (quote-eval, meta-programming)
- Chapter 10 — Worked programs: 道德经-Wen 1st stanza, 易经-占卜 sim, 人类命运共同体 自指

Each chapter ~5 examples, all REPL-verified. Total target: 50 examples.

---

## Method note

The principle: **never write an example without running it**. The wen REPL is the spec's tip-of-iceberg ground truth; documents that diverge from it are bugs.

If you're following along: `lake build wen && ./.lake/build/bin/wen`. The REPL hangs around the `≫ ` prompt; type `:quit` or Ctrl-D to exit.
