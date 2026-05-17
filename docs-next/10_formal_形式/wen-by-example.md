# Wen by Example

**Date**: 2026-05-18 · **Status**: 草稿 (10 chapters drafted; all examples REPL-verified on commit edc402e+)

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

These are real bugs/limitations originally found by running examples through the REPL during this doc's first draft. **All 12 were closed in PRs #71-80** (merged 2026-05-17). The entries below preserve the original problem statement and document the resolution.

| ID | Status | Fixing PR |
|---|---|---|
| B-1 | FIXED | #72 |
| B-2 | FIXED | #74 |
| B-3 | FIXED | #74 |
| B-4 | FIXED | #77 |
| B-5 | FIXED | #77 |
| B-6 | FIXED | #74 |
| B-7 | FIXED | #76 |
| B-8 | FIXED (UX) | #78 |
| B-9 | FIXED | #71 |
| B-10 | FIXED (UX) | #79 |
| B-11 | FIXED (UX) | #79 |
| B-12 | FIXED | #80 |

**UX-only** entries (B-8/10/11) replaced opaque errors with clear messages but the underlying surface limitation (Bool-quoted execution, compound-hex starters, namespace activation in REPL) remains and is tracked separately.

### B-1: REPL is single-expression only — **FIXED (PR #72)**

The `wen` REPL previously only accepted one expression per line. PR #72 added `evalSubmission` which calls `wenyanCompileProgramWithDefs`. Multi-statement now works:

```
≫ 定 甲 为 一；甲
«姤» (011111) : Hex
```

All five Wen 2.0 declaration forms (定 / 定递 / 类 / 析 / 定…等) are now interactively usable, modulo the per-feature limits noted below.

**Remaining gap (B-1-rec)**: `定递` with a real self-applying body fails HM inference at the elaborator (the recursive type has no anchoring constraint). See §4.3 — `定递 甲 为 者 乙 甲 之 推 之 乙；甲 一` returns `elab error: empty or ill-formed expression`. Needs explicit type annotation on the recursion or a unification escape hatch.

**Other remaining gap**: `用 NS_NAME` (namespace import) is supported by `wenyanCompileProgramWithNamespaces` but the REPL still uses the no-namespace variant; `用 墨经` in the REPL returns a `schoolNamespaceName` error.

### B-2: 6 yao flips have no surface readings — **FIXED (PR #74)**

PR #74 added the `ResolvedAtom.builtinTm body arity` variant + `resolveBuiltinSurface` table. The 6 yao flips now read:

```
≫ 初爻 一
«乾» (111111) : Hex
≫ 二爻 乾
«同人» (101111) : Hex
```

Surface 初爻..上爻 map to `Tm.flip1H..flip6H`.

### B-3: `加` (Tm.jia) is unreachable — **FIXED (PR #74)**

`加` now reads as `Tm.jia`. Verified:

```
≫ 加 一 一
«同人» (101111) : Hex
```

### B-4: `並` ↔ `andB` — **FIXED (PR #77)**

PR #77 added the builtin-Tm reading `並 → Tm.andB`. (`并` simplified variant also accepted.)

```
≫ 並 真 假
false : Bool
≫ 並 真 真
true : Bool
```

The earlier `pairH` reading of 並 is preserved at the catalogue layer but the new builtin-Tm path takes priority for the surface 並.

### B-5: `或` ↔ `orB` — **FIXED (PR #77)**

PR #77 added `或 → Tm.orB`:

```
≫ 或 真 假
true : Bool
≫ 或 假 假
false : Bool
```

### B-6: List ops `列一/列二/列三/首` — **FIXED (PR #74)**

PR #74 added builtin-Tm readings for the 4 list primitives.

```
≫ 列一 乾
<elaborated> : List Hex
≫ 首 之 列一 乾
«乾» (111111) : Hex
```

(REPL doesn't pretty-print `List Hex` values yet — they show as `<elaborated>`. Verifying via `首` extracts the first element.)

Tm constructors `list1H`, `list2H`, `list3H`, `headH` now have surface readings.

### B-7: Curried λ chained application — **FIXED (PR #76)**

PR #76 gated the `appMarker` branch on `acc` being functional. Now both forms work:

```
≫ （者 甲 者 乙 甲）之 乾 之 坤
«乾» (111111) : Hex
≫ （（者 甲 者 乙 甲）之 乾）之 坤
«乾» (111111) : Hex
```

A 2-arg λ can be chain-applied via `之 X 之 Y` without inner parens.

### B-8: `执` on Bool-quoted expression — **FIXED (PR #78, error-message only)**

PR #78 added `hexFallbackMessage` + `isUnquoteHead` to give a clear targeted message when the runtime value of an `执 「…」` is a Bool. The kernel still types `执` as `Hex → Hex` (lifting that to type-dispatch is future work; tracked in the Quoted-payload HM gap).

```
≫ 执 「真」
执 returned a Bool value (true), but 执 is typed `Hex` in wen 1.5.
  Note: `执 「…」` is currently restricted to Hex-returning quoted expressions; Bool-returning quotes are future work (HM on `Quoted` payloads).
```

This is a UX fix only — Bool-returning quoted execution still isn't supported. See Chapter 9.3.

### B-9: `typeMismatch` errors — **FIXED (PR #71)**

PR #71 routed REPL error rendering through `renderWenSurfaceErr` (the surface error renderer from ErrorRender.lean). All errors now include source-caret + expected/actual types:

```
≫ 推 真
[stmt 1] 推 真
^
type mismatch:
  expected: Hex
  got:      Bool
```

### B-10: Single-glyph hex starters — **FIXED (PR #79, error-message only)**

PR #79 added `ResolveErr.hexCompoundStarter` so that bare 大/中/明/… (first glyph of multi-glyph hex names) emits an informative message instead of `noReading`. The semantics are unchanged — these glyphs remain intentionally non-expressions to avoid ambiguity. Write the full hex name (大有, 中孚, 明夷, …) instead.

```
≫ 及
resolve error at column 0: unknown glyph or surface: '及'
```

(The error now points to source location with caret.)

### B-11: 学派 surfaces — **FIXED (PR #79, error-message only)**

PR #79 added `ResolveErr.schoolNamespaceName` so that bare 墨经/名家/… (without `用`) emit a clear message:

```
≫ 墨经
resolve error at column 0:
  '墨' is a 学派 namespace name, not an expression — try `用 墨` to activate
```

The underlying limit remains: in the REPL today, even `用 墨经` doesn't activate the namespace because the REPL uses `wenyanCompileProgramWithDefs` (no namespace tracking). Lifting the REPL to `wenyanCompileProgramWithNamespaces` is the natural follow-up; once done, the existing 12 namespace groups all become reachable.

### B-12: Cell op surface — **FIXED (PR #80)**

PR #80 reserved cell-op surfaces (`错位 / 同位 / …`) at the lexer level and added `ResolveErr.cellOpUnsupported`. Both `:t` and application now fail uniformly:

```
≫ 错位 乾
resolve error at column 0:
  '错位' is a Cell-level operator surface
  (emitted by the pretty-printer for Tm.cuoC / Tm.eqCell / …);
  v1 has no Cell literal surface, so cell ops are not parseable yet.
```

The PrettyPrint module still emits these surfaces (for `Tm.cuoC` etc. originating in the kernel); they remain output-only until v2 adds Cell literals.

---

# Chapter 3 — 定 (user definitions)

A `定` declaration binds a name to a body and makes it available for the rest of the **submission**. Definitions don't survive across REPL prompts — each `≫`-line is its own self-contained mini-program.

Syntax:

```
定 NAME 为 BODY
```

NAME can be any single CJK glyph (or short identifier), as long as it doesn't clash with a catalogue surface. The body is any expression. Statements are separated by `；` / `。` / `;` inside one submission.

---

## 3.1  Naming a hex

```
≫ 定 子 为 一；子
«姤» (011111) : Hex
```

**义**: `子` is bound to `一` (which is 姤), then the next statement evaluates it. `子` is not in the operator catalogue (only the 10 Heavenly Stems 甲乙丙丁戊己庚辛壬癸 are reserved), so it's free for user defs.

**试**: Bind `丑` to 坤, then ask `比 之 子 之 丑` (R_8 adjacency).

---

## 3.2  Naming a unary function

```
≫ 定 反 为 者 甲 错 之 甲；反 之 乾
«坤» (000000) : Hex
≫ 定 反 为 者 甲 错 之 甲；反 之 一
«复» (100000) : Hex
```

**义**: `反` is a 1-arg λ that maps any hex to its complement. The body uses `者` to bind the parameter `甲`. Once defined, `反` is callable just like any catalogue op via `之`.

**注**: We could equivalently use the postfix `…也` form: `反 之 X 也` (it does nothing extra here; useful when ending a sentence).

---

## 3.3  Definitions compose

```
≫ 定 单 为 一；定 双 为 之又 错 之 单；单；双
«姤» (011111) : Hex
«姤» (011111) : Hex
```

**义**: `双` references the earlier `单`. `之又` is "do it again" — `之又 错 X = 错 (错 X)`, so `双 = 错 (错 一) = 一`. Both print 姤.

```
≫ 定 反 为 者 甲 错 之 甲；定 双反 为 者 乙 反 之 反 之 乙；双反 之 一
«姤» (011111) : Hex
```

**义**: `双反` calls user-defined `反` twice. User defs compose freely with each other and with catalogue ops.

---

## 3.4  Definitions can curry catalogue ops

```
≫ 定 同乾 为 同 之 乾；同乾 之 乾；同乾 之 坤
true : Bool
false : Bool
```

**义**: `同` has type `Hex → Hex → Bool`. Partially applying it as `同 之 乾` produces a curried `Hex → Bool` predicate — bind that and reuse.

This is the canonical pattern for **specializing relations** in Wen: take a 2-arg op, pin one argument, give it a name.

---

## 3.5  Multi-char NAMEs are fine

```
≫ 定 不二 为 者 甲 不 之 不 之 甲；不二 之 真
true : Bool
```

**义**: NAME can be more than one glyph as long as the whole token isn't in the catalogue. `不二` is two glyphs, parsed as one name. The body is the Bool double-negation function (a no-op on Bools by involution of `不`).

---

## 3.6  名字冲突 (name conflicts)

```
≫ 定 道 为 一；道
[stmt 1] def conflicts with catalogue name: 道
```

**义**: `道` is reserved (a catalogue surface for the genesis operator). You'll see this error any time NAME shadows a catalogue glyph. **List of safe initials** (in order): 子丑寅卯辰巳午未申酉戌亥 (12 地支), most multi-CJK combinations, plus the 10 Heavenly Stems but only inside binders (not as user-def NAMEs).

**Workaround**: pick a non-catalogue glyph or compound. If you need a glyph that's already reserved, prefix with a clarifying CJK char (e.g. `我道`).

---

# Chapter 4 — 定递 (recursion)

Wen has **fuel-bounded recursion** via `定递`. The body may reference the name being defined; at run-time each unfolding consumes one unit of fuel from a global budget.

Syntax:

```
定递 NAME 为 BODY
```

with the **restriction**: NAME must be one of the 10 Heavenly Stems (甲乙丙丁戊己庚辛壬癸) in v1.

---

## 4.1  Trivial recursion (no self-call)

```
≫ 定递 甲 为 者 乙 推 乙；甲 一
«同人» (101111) : Hex
```

**义**: `定递 甲 为 者 乙 推 乙` defines `甲` as `μf. λy. 推 y`. The fixpoint is unused because `甲` doesn't appear in the body — this just behaves like ordinary λ. Calling `甲 一` ≡ `推 一` ≡ `同人`.

---

## 4.2  Self-referential definitions that don't actually call

```
≫ 定递 甲 为 甲
```

(no output — declaration only)

**义**: The body is just `甲` itself — the simplest self-loop. The fixpoint compiles, but evaluating it would burn fuel forever, so we only declare and don't apply.

---

## 4.3  Limitation: real recursive calls hit HM inference today

```
≫ 定递 甲 为 者 乙 甲 之 推 之 乙；甲 一
elab error: empty or ill-formed expression
```

**义**: When the body actually calls `甲 …` (genuine recursion), Hindley-Milner has no anchoring constraint for `甲`'s type and the elaborator fails. The kernel `Tm.fix` is sound; the surface elaborator just can't yet **infer** the recursive type without a type annotation. This is a known gap — see Appendix B (B-1-rec).

**Workaround for v1**: write recursive programs at the kernel level directly (`WenDef.Tm.fix`) and elaborate them programmatically. For day-to-day use, Wen's exhaustive `凡` (Chapter 5) covers most recursion-style problems over the 64-hex domain.

---

# Chapter 6 — 类 + 析 (user inductives + pattern match)

`类` declares a new sum type. `析` pattern-matches on it.

Syntax:

```
类 TYPENAME = CTOR₁ | CTOR₂ | … | CTORₙ
析 SCRUT 为 PAT₁ → BODY₁ | PAT₂ → BODY₂ | …
```

---

## 6.1  Declaring an enum

```
≫ 类 八 = 甲 | 乙 | 丙 | 丁；甲
甲 : 八
```

**义**: `类 八 = …` declares the type `八` with four nullary constructors. The next statement evaluates `甲`, which is now a value of type `八` (not the variable 甲!). The printer shows `甲 : 八` rather than `«姤» (…) : Hex`.

**v1 限制**: Constructor NAMEs must resolve to **Heavenly Stems** (甲乙丙丁戊己庚辛壬癸). Arbitrary CJK glyphs like 春夏秋冬 are not currently accepted because the elaborator's name-conflict check requires ctor names to lex as `.varName` (see [`Reading.lean:resolveVarName`](../../formal/SSBX/Foundation/Wen/WenSurface/Reading.lean)). The TYPENAME (`八` above) is unrestricted as long as it's not already in the catalogue.

---

## 6.2  Pattern matching with 析

```
≫ 类 八 = 甲 | 乙 | 丙 | 丁；析 丙 为 甲 → 一 | 乙 → 坤 | 丙 → 乾 | 丁 → 一
«乾» (111111) : Hex
```

**义**: `析 丙 为 …` matches the scrutinee `丙` against four arms. The third arm (`丙 → 乾`) fires, returning 乾.

**注**: The type of the whole `析 …` is the common type of all arm bodies (here, Hex). All arms must agree; if one returned a Bool, the elaborator would reject.

---

## 6.3  Pattern match returning the scrutinee type

```
≫ 类 八 = 甲 | 乙 | 丙 | 丁；析 甲 为 甲 → 一 | 乙 → 坤 | 丙 → 乾 | 丁 → 一
«姤» (011111) : Hex
```

**义**: The default arm fires (`甲 → 一`) and we get 姤. Notice the **scrutinee** `甲` (of type `八`) and the **pattern** `甲` (also constructor of `八`) are syntactically the same glyph but semantically distinct — context disambiguates.

---

# Chapter 7 — 所…者, 属, 之所以 (structural keywords)

Three "syntactic verbs" let you build sets, test membership, and reorder application — all without leaving the kernel.

---

## 7.1  所 PRED 者 — relativization (predicate as function)

```
≫ 所 同 之 乾 者 之 乾
true : Bool
```

**义**: `所 (同 之 乾) 者` desugars to `λ甲. 同 之 乾 甲` — the predicate "is equal to 乾". Then `… 之 乾` applies it to 乾, which is true.

This is just the η-expansion of `同 之 乾`, but the surface reads as "the thing that is 乾" — a noun phrase nominalizing a verb phrase.

---

## 7.2  X 属 S — set membership

```
≫ 一 属 （者 甲 同 甲 一） 者
true : Bool
≫ 乾 属 （者 甲 同 甲 一） 者
false : Bool
≫ 一 属 （者 甲 真） 者
true : Bool
≫ 一 属 （者 甲 假） 者
false : Bool
```

**义**: `（pred） 者` nominalizes a predicate into a **Set Hex**. `X 属 S` returns true iff `X` is a member.

Four readings:
1. `λx. x = 一` — the singleton {一}; 一 is in, 乾 isn't.
2. `λx. 真` — the universal set; everything is in.
3. `λx. 假` — the empty set; nothing is in.

Compare to `凡` (Chapter 5): `属` is point-wise membership; `凡` quantifies over all of Hex.

---

## 7.3  之所以 — reason extraction (function flip)

```
≫ 一 之所以 错
«复» (100000) : Hex
≫ （推 之 一） 之所以 错
«师» (010000) : Hex
≫ 推 之 一 之所以 错
«坤» (000000) : Hex
```

**义**: `Y 之所以 X` reshapes to `X Y` (apply X to Y). Reading-wise it's "the reason Y happens is X", which the kernel collapses to ordinary application.

The three lines show why parens matter:

1. `一 之所以 错` = `错 一` = `错 011111` = `100000` = **复**. Clean.
2. `（推 之 一） 之所以 错` = `错 (推 之 一)` = `错 同人` = `错 101111` = `010000` = **师**. Parens force `推 之 一` to be the subject.
3. `推 之 一 之所以 错` = `推 之 (一 之所以 错)` = `推 复` = **坤**. Without parens, `之所以` binds **tighter than** the `之` application marker, so the subject is just `一`, not `推 之 一`.

**moral**: when mixing `之所以` with `之`-chains, parenthesize the subject. The surface concision is real but at a precedence cost.

---

# Chapter 8 — 定 LHS 等 RHS (rewrite rules)

`定 LHS 等 RHS` declares a **definitional equality**: every occurrence of LHS in subsequent terms is replaced by RHS at compile time. This is **not** a runtime equation — it's a syntactic rewrite applied during normalization.

Syntax:

```
定 LHS 等 RHS
```

---

## 8.1  Eliminating double negation

```
≫ 定 错 错 甲 等 甲；错 之 错 之 一
«姤» (011111) : Hex
```

**义**: The rule `错 错 甲 = 甲` (with `甲` as a pattern variable) rewrites any `错 (错 t)` to `t`. The subsequent expression `错 之 错 之 一` collapses to `一` = 姤.

Note: even without the rewrite, runtime would compute `错 (错 一) = 一` anyway (since 错 is an involution). The rewrite **shortens compile-time** output (and pretty-printed forms).

---

## 8.2  Compose with regular defs

```
≫ 定 错 错 甲 等 甲；定 倍推 为 而 推 推；倍推 乾
«同人» (101111) : Hex
```

**义**: Rewrite rules and `定` declarations live in the same submission. Here `倍推 = 推 ∘ 推` (composition via `而`). Applying to 乾: `推 (推 乾) = 推 姤 = 同人`. (Trace: `推 乾 = 姤` because the cyclic-shift rule wraps 111111 down through `xuGua`; then `推 姤 = 同人`.)

**注**: The pattern variable in rewrite LHS must be a **linear** Heavenly Stem — each stem appears once. `定 同 甲 甲 等 真` is rejected (`甲` non-linear). Use ordinary functions if you need non-linear matching.

---

# Chapter 9 — 执 (quoted execution)

`执 「X」` parses, type-checks, and runs the quoted expression — a meta-circular evaluator inside Wen.

Syntax:

```
执 「EXPR」
执 『EXPR』
执 〈EXPR〉
```

All three bracket pairs work; pick by clarity.

---

## 9.1  执 on a hex expression

```
≫ 执 「推 之 一」
«同人» (101111) : Hex
```

**义**: The quoted body `推 之 一` is wrapped as a `Tm.quoted`, then `执` (`Tm.unquote`) re-evaluates it under the current environment. Result is identical to running `推 之 一` directly.

---

## 9.2  Quoted involutions

```
≫ 执 「错 之 错 之 乾」
«乾» (111111) : Hex
```

**义**: Double-complement of 乾 is 乾.

---

## 9.3  Bool-returning quotes hit a v1 limit

```
≫ 执 「真」
执 returned a Bool value (true), but 执 is typed `Hex` in wen 1.5.
  Note: `执 「…」` is currently restricted to Hex-returning quoted expressions; Bool-returning quotes are future work (HM on `Quoted` payloads).
```

**义**: `Tm.unquote` is hard-typed as `Hex → Hex` (the quoted body must denote a Hex). A `Bool`-yielding body slips past the surface typecheck (`.quoted` is opaque to HM) and then fails at the denotation step. The error message (added in B-8 fix) explains the constraint clearly.

---

# Chapter 10 — Worked programs

End-to-end multi-statement programs combining everything from chapters 1-9.

---

## 10.1  Define + use + verify

```
≫ 定 反 为 者 甲 错 之 甲；定 不变 为 者 甲 同 甲 之 反 之 反 之 甲；凡 之 者 乙 不变 之 乙
true : Bool
```

**义**: Three statements:

1. `反` := flip every yao (η-expanded form of `错`).
2. `不变` := the predicate "x is invariant under `反 ∘ 反`", i.e. `λx. x = 反 (反 x)`.
3. `凡 不变` := "for all x, `不变 x` holds".

The whole thing is a machine-checked proof: **`错` (a.k.a. `反`) is an involution over all 64 hexes**. Result: `true`.

---

## 10.2  Predicate algebra in 3 lines

```
≫ 定 是乾 为 同 之 乾；定 非乾 为 者 甲 不 之 是乾 之 甲；唯 之 者 甲 是乾 之 甲；唯 之 者 甲 非乾 之 甲
true : Bool
false : Bool
```

**义**:
1. `是乾` := "is 乾" (curried `同`).
2. `非乾` := "is not 乾" (negate).
3. `唯 是乾` := "exactly one hex is 乾" → true (uniquely 乾).
4. `唯 非乾` := "exactly one hex is non-乾" → false (there are 63).

---

## 10.3  类 + 析 + Hex output

```
≫ 类 元素 = 甲 | 乙 | 丙；析 乙 为 甲 → 乾 | 乙 → 坤 | 丙 → 一
«坤» (000000) : Hex
```

**义**: User inductive `元素` with three constructors, then a pattern match that maps each ctor to a hex. Scrutinee 乙 fires arm 2, returns 坤.

This is **finite enum-driven dispatch** — the bread and butter of any language that talks about kinds.

---

## 10.4  Self-evaluating program

```
≫ 执 「执 「推 之 一」」
«同人» (101111) : Hex
```

**义**: An `执` inside an `执`. The outer `执` unquotes the inner quoted term; that inner term is itself an `执` over a quoted `推 之 一`, which unquotes to 同人. Wen evaluates the meta-circular tower in one step.

---

# Recap: what you've learned

After 10 chapters you can:

| Skill | Where |
|---|---|
| Write hex literals | 1.1 |
| Apply unary ops (`错`, `推`, `综`, `互`) | 1.2-1.4 |
| Compare hexes (`同`, `比`) | 1.6-1.7 |
| Build quoted expressions and unquote them | 1.8 + 9 |
| Define curried λ via `者` | 2 |
| Quantify over all hexes (`凡` / `唯` / `三` / `過半`) | 5 |
| Verify algebraic theorems by exhaustive check | 5.5 |
| Bind a name to a value (`定`) | 3 |
| Compose user defs | 3.3-3.4 |
| Declare recursive functions (limited) | 4 |
| Declare user inductives (`类`) and dispatch (`析`) | 6 |
| Build sets and test membership (`所/者`, `属`) | 7 |
| Reorder application (`之所以`) | 7.3 |
| Declare rewrite rules (`定 等`) | 8 |
| Meta-evaluate quoted programs (`执`) | 9 |
| Combine all of the above in a multi-statement program | 10 |

---

## Method note

The principle: **never write an example without running it**. The wen REPL is the spec's tip-of-iceberg ground truth; documents that diverge from it are bugs.

If you're following along: `lake build wen && ./.lake/build/bin/wen`. The REPL hangs around the `≫ ` prompt; type `:quit` or Ctrl-D to exit.

For a one-liner test from the shell:

```
echo -e "推 之 一\n:quit" | ./.lake/build/bin/wen 2>&1 | grep "^≫"
```
