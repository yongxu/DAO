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

See also [Appendix B — Gaps & limitations](#appendix-b--gaps--limitations) for the **full** validation-discovered gap list (11 issues).

---

# Chapter 2 — λ 与 应用 (lambda and application)

The binder `者` introduces a λ-abstraction: `者 NAME body`. Wen's evaluator is **call-by-value** with **explicit application markers** (`之`), which leads to a few non-obvious idioms.

## 2.1  Identity

```
≫ 者 甲 甲
<elaborated> : Hex → Hex
≫ :t 者 甲 甲
Hex → Hex
```

**义**: `者 甲 甲` is `λx. x` — the identity. Wen's HM defaults the unsolved domain mvar to `.hex`, so without an applied context it prints as `Hex → Hex`.

To apply it, wrap in parens and use `之`:

```
≫ （者 甲 甲）之 一
«姤» (011111) : Hex
≫ （者 甲 甲）之 乾
«乾» (111111) : Hex
```

The **fullwidth** parens `（）` or **ASCII** parens `()` both work as grouping.

## 2.2  Wrapping an operation

```
≫ （者 甲 错 之 甲）之 一
«复» (100000) : Hex
≫ （者 甲 错 之 综 之 甲）之 一
«剥» (000001) : Hex
≫ （者 甲 综 之 错 之 甲）之 一
«剥» (000001) : Hex
```

**义**: `者 甲 错 之 甲` = `λx. 错 x` — a function that applies 错. The last two examples show **composition commutes** for 错 and 综: `错 ∘ 综 = 综 ∘ 错` (both give 错综).

## 2.3  Curried λ — explicit parens required

Multi-binder λs are tricky:

```
≫ 者 甲 者 乙 甲
<elaborated> : Hex → Hex → Hex
≫ :t 者 甲 者 乙 甲
Hex → Hex → Hex
```

So `者 甲 者 乙 甲` typechecks as `λx. λy. x` (the K combinator). But:

```
≫ （者 甲 者 乙 甲）之 乾 之 坤
elab error: SSBX.Foundation.Wen.WenSurface.ElabErr.empty
```

**Application of a curried λ to two args fails without inner parens**. Workaround: bracket the partial application:

```
≫ （（者 甲 者 乙 甲）之 乾）之 坤
«乾» (111111) : Hex
```

This is a real parser issue (see Appendix B #7) — the application-chain elaborator can't fold `之 X 之 Y` into a single curried call. For pedagogy: **always bracket curried partials explicitly**.

## 2.4  Higher-order — predicates

A predicate is a `Hex → Bool` function. Applying a quantifier folds it into a Bool:

```
≫ :t 同 乾
Hex → Bool
≫ （同 乾）之 坤
false : Bool
≫ （同 乾）之 乾
true : Bool
```

**义**: `同 乾` curries the equality op into a unary predicate `λx. x = 乾`. Apply via `之`.

## 2.5  Identity as a Bool function

```
≫ 者 甲 不 之 不 之 甲
<elaborated> : Bool → Bool
≫ （者 甲 不 之 不 之 甲）之 真
true : Bool
≫ （者 甲 不 之 不 之 甲）之 假
false : Bool
```

**义**: HM picks `Bool → Bool` here because the body `不 之 不 之 甲` only typechecks with `甲 : Bool`. This is the **HM-driven binder-domain selection** in action — no annotation needed.

## 章末 — Patterns to remember

| 想法 | 文言 |
|---|---|
| Identity (Hex) | `者 甲 甲` |
| Identity (Bool) | `者 甲 不 之 不 之 甲` |
| Wrap an op | `者 甲 OP 之 甲` |
| Compose | `者 甲 OP₁ 之 OP₂ 之 甲` |
| Curried partial | wrap inner `(λ 之 X)` in parens before `之 Y` |
| Predicate | `同 X` or `者 甲 PRED-expr` |

---

# Chapter 5 — 量词 (quantifiers) — preview

(Chapters 3-4 on user defs / recursion need multi-statement REPL — see Appendix B #1. Skipping ahead.)

Wen has 4 quantifier-style higher-order operators, all `(Hex → Bool) → Bool`:

```
≫ :t 凡
(Hex → Bool) → Bool
≫ :t 唯
(Hex → Bool) → Bool
≫ :t 三
(Hex → Bool) → Bool
≫ :t 過半
(Hex → Bool) → Bool
```

Each runs an exhaustive check over all 64 hexagrams.

## 5.1  `凡` — for all

```
≫ 凡 之 者 甲 真
true : Bool
≫ 凡 之 者 甲 假
false : Bool
≫ 凡 之 者 甲 不 之 不 之 真
true : Bool
```

**义**: `凡 之 (λ甲. P)` ≡ `∀甲 : Hex. P 甲`. The body must return Bool.

The third example shows compositions live inside the predicate: `不 ∘ 不 ∘ 真 = 真`, so the `∀` is trivially true.

## 5.2  `唯` — exists unique

```
≫ 唯 之 者 甲 同 甲 乾
true : Bool
≫ 唯 之 者 甲 真
false : Bool
```

**义**: `唯` returns true if **exactly one** hex satisfies the predicate. `同 甲 乾` is true only for 甲 = 乾, so unique. `真` is satisfied by all 64, so not unique.

## 5.3  `三` — exactly three

```
≫ 三 之 者 甲 真
false : Bool
```

**义**: `三` checks for exactly 3 satisfying hexes. `真` has 64 satisfiers, not 3.

## 5.4  `過半` — majority (≥ 33)

```
≫ 過半 之 者 甲 真
true : Bool
```

**义**: 64 > 32 — majority.

## 5.5  Algebraic theorems — verified by exhaustive check

`凡` over a 64-element domain effectively makes Wen a **decision procedure** for closed Hex-quantified formulas. This means we can verify **algebraic identities** by writing them as `凡` propositions:

```
≫ 凡 之 者 甲 同 之 甲 之 错 之 错 之 甲
true : Bool
```

**义**: `∀x. x = 错 (错 x)` — **错 is an involution**. Verified by exhaustive check over 64 hexes.

```
≫ 凡 之 者 甲 同 之 甲 之 综 之 综 之 甲
true : Bool
```

**义**: `综` is also an involution.

```
≫ 凡 之 者 甲 同 之 错 之 综 之 甲 之 综 之 错 之 甲
true : Bool
```

**义**: **`错 ∘ 综 = 综 ∘ 错`** — complement and reverse **commute**. (Both compose to 错综.)

```
≫ 凡 之 者 甲 不 之 同 之 推 之 甲 之 甲
true : Bool
```

**义**: `推` has **no fixed point** — there's no hex x such that 推 x = x.

These four are real algebraic theorems machine-verified by Wen.

---

# Appendix A — Working primitives table (verified)

All from Chapter 1-2 + 5 + extra probes:

| 文言 | Type | Notes |
|---|---|---|
| `一` | Hex | the hex 姤 (011111) |
| 64 King-Wen names | Hex | `乾 坤 屯 蒙 需 訟 師 比 小畜 履 泰 否 …` (some 1-char ones like 及/夷 fail when bare; see B-10) |
| `真` `假` | Bool | literals |
| `错` `综` `互` `错综` | Hex → Hex | involutions (錯/錯综 verified) |
| `推` | Hex → Hex | shift; no fixed point |
| `不` | Bool → Bool | involution |
| `同` | Hex → Hex → Bool | curries: `同 乾 : Hex → Bool` |
| `凡` `唯` `三` `過半` | (Hex → Bool) → Bool | exhaustive over 64 |
| `比` | Hex → Hex → Bool (when applied; Hex alone) | R_8 infix |
| `之又` | iterate twice | `之又 op X = op (op X)` |
| `之` | app marker | left-associative |
| `「 」` `『 』` `〈 〉` | quote brackets | wraps Tm-as-`Quoted` |
| `执 「X」` | unquote + eval | `Quoted → Hex` only |
| `（ ）` `( )` | grouping | both fullwidth and ASCII |
| `也` | Hex → Hex | postfix predication (identity on Hex) |
| `乎` `矣` `哉` `兮` | Bool → Bool | postfix Bool particles |
| `者 NAME body` | λ-binder | HM-inferred domain |

---

# Appendix B — Gaps & limitations (validation-discovered)

These are real bugs/limitations found by running examples through the REPL. Each is worth a future PR.

### B-1: REPL is single-expression only

The `wen` REPL only accepts **one expression per line**. Multi-statement input fails at the lexer because `；` / `。` / `;` are not allowed inside a `wenyanCompile` (single-stmt) call.

```
≫ 定 甲 为 一；甲
lex error: SSBX.Foundation.Wen.WenSurface.LexErr.unexpected 11 '；'
```

**Impact**: cannot use 定 / 定递 / 类 / 析 / 用 / 定…等 in the REPL at all. All five Wen 2.0 declaration forms are unreachable interactively.

**Fix**: have REPL try `wenyanCompileProgramWithDefs` first (full pipeline), fall back to `wenyanCompile` only for bare expressions. Or add `:def NAME = BODY` etc. REPL commands.

### B-2: 6 yao flips have no surface readings

`初爻 / 二爻 / 三爻 / 四爻 / 五爻 / 上爻` are kernel-level Tm constructors (`flip1H` … `flip6H`) but the **multi-char surface table doesn't register them**:

```
≫ 初爻 一
resolve error: SSBX.Foundation.Wen.WenSurface.ResolveErr.noReading "初" 0
```

**Fix**: add 初爻/二爻/三爻/四爻/五爻/上爻 to `Lex.multiCharSurfaces` with appropriate catalogue mapping.

### B-3: `加` (Tm.jia) is unreachable

The Tm builtin `jia` (Hex addition, `Hex → Hex → Hex`) exists but has no surface reading. The character 加 doesn't resolve:

```
≫ 加 一 一
resolve error: noReading "加" 0
```

### B-4: `並` is `pairH`, not `andB`

The kernel has `Tm.andB : Bool → Bool → Bool` named for `並`. But the surface 並 binds to `pairH` (`Hex → Hex → (Hex × Hex)`):

```
≫ :t 並
Hex → Hex → (Hex × Hex)
```

**Impact**: there is **no surface way to AND two Bools** in Wen. Spec doc was wrong.

### B-5: `或` is modal M_2, not `orB`

Similarly, `Tm.orB` exists but the surface 或 binds to modal `M_2 可能模态`:

```
≫ :t 或
…modal…
```

**Impact**: no surface Bool OR.

### B-6: List ops 列一/列二/列三/首 unreachable

```
≫ :t 列一
resolve error: noReading "列" 0
≫ :t 首
resolve error: noReading "首" 0
```

Tm constructors `list1H`, `list2H`, `list3H`, `headH` exist but no surface readings.

### B-7: Curried λ application without inner parens fails

```
≫ （者 甲 者 乙 甲）之 乾 之 坤
elab error: empty
≫ （（者 甲 者 乙 甲）之 乾）之 坤
«乾» (111111) : Hex
```

The elaborator can't chain `之 X 之 Y` into one curried call without explicit bracketing.

**Impact**: any pedagogical example using a 2-arg λ needs ugly nested parens. Workaround: always introduce 2-arg ops as catalogue ops instead of λ.

### B-8: `执` on Bool-quoted expression fails with confusing error

```
≫ 执 「真」
denote failed: expected Hex, got Hex
≫ 执 「不 之 真」
denote failed: expected Hex, got Hex
≫ 执 「同 之 一 之 一」
denote failed: expected Hex, got Hex
```

The error message reads **"expected Hex, got Hex"** — both sides say Hex. The actual problem: `执` types its result as `.hex` per the doctrine, but the quoted expression returns Bool. The error renderer can't distinguish.

**Fix**: either allow `执` to type-dispatch on the inner expression, or improve the error message ("execution returned Bool, but `执` always returns Hex — wrap with `不 之 不 之` to coerce?").

### B-9: `typeMismatch` errors don't show expected/actual types

```
≫ 推 真
elab error: SSBX.Foundation.Wen.WenSurface.ElabErr.typeMismatch
```

The error rendering is too terse — the user can't tell *what* was expected vs *what was given* without reading source. ErrorRender was supposed to fix this in Wen 1.5; for typeMismatch specifically, it's still bare.

### B-10: Some single-glyph hex starters are unreachable when bare

```
≫ 及
resolve error: noReading "及" 0
≫ 夷
resolve error: noReading "夷" 0
```

These are the second glyph of multi-char hex names (明夷). They were intentionally excluded from the bare-glyph surface to avoid ambiguity, but the user-facing error is opaque. **Impact**: 64 hex names work; ~10 first-glyphs of compound names are reserved.

### B-11: 学派 surfaces are not parseable expressions

The `Namespace.entries` table has 42 surface aliases (墨经, 名家, 老子, 庄子, etc.) for use in `用 NS_NAME` declarations. But these surfaces are NOT registered as **expressions**:

```
≫ 墨经
resolve error: noReading "墨" 2
```

And several **学派 op aliases** mentioned in the spec doc (兼愛, 中庸, 莊周夢蝶, 仁) are not in `multiCharSurfaces` either:

```
≫ 兼愛
resolve error: noReading "愛" 1
≫ 中庸
resolve error: noReading "庸" 1
≫ 仁
resolve error: noReading "仁" 0
```

**Impact**: the 学派 layer (P/G/A/L/ZHU/SUN/CHU/LIJ/ZA/E/X/Z, 12 groups) is **mostly inaccessible from Wen source**. The spec doc oversold this.

### B-12: Cell op surface is broken

```
≫ :t 同位
elab error: typeMismatch
≫ :t 错位
elab error: typeMismatch
≫ 错位 乾
«坤» (000000) : Hex
```

`同位`/`错位` are supposed to be `Cell → Cell` and `Cell → Cell` respectively, but `:t` reports type errors yet **application returns a Hex**. Something is wrong with the cell-vs-hex dispatch in elaboration.

---

# Subsequent chapters (planned, blocked on REPL improvements)

Chapters 3 (定), 4 (定递), 6 (类 + 析), 7 (曰/所…者/之所以), 8 (定…等), 9 (执 lambdas), 10 (worked programs) all need **either** B-1 fixed (multi-statement REPL) **or** an alternate path: writing programs to file and feeding via stdin.

Reasonable first action: **fix B-1 first**. A REPL that does `wenyanCompileProgramWithDefs` per submission (with `；` separator allowed) unlocks all five 2.0 decl forms.

---

## Method note

The principle: **never write an example without running it**. The wen REPL is the spec's tip-of-iceberg ground truth; documents that diverge from it are bugs.

If you're following along: `lake build wen && ./.lake/build/bin/wen`. The REPL hangs around the `≫ ` prompt; type `:quit` or Ctrl-D to exit.

For a one-liner test from the shell:

```
echo -e "推 之 一\n:quit" | ./.lake/build/bin/wen 2>&1 | grep "^≫"
```
