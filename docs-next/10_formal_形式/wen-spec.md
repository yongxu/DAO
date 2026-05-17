# Wen Language Specification (v2.0)

**Date**: 2026-05-18 · **Status**: 0 sorry / 0 axiom · **Toolchain**: Lean 4.30.0-rc2

This is the canonical reference for the Wen language as implemented in `formal/SSBX/Foundation/Wen/`. It documents the lexical structure, kernel calculus (`Tm` + `Ty`), surface forms, declaration statements, type inference, operational semantics, and tooling.

Scope of this doc: **describe what exists**. For history (Wen 1.0 restructure / Wen 1.5 user-facing / Wen 2.0 features), see `project_wen_*` memories. For doctrine (R-tower / V₄ Shi), see `wen-substrate.md` and `wen-strata-invariants.md`.

---

## 0  Reading guide

| Audience | Start here |
|---|---|
| Want to use the REPL | §1, §5, §6.1 (`定`), §11.1 |
| Want to write programs | §5 + §6 (all forms) |
| Want to extend the kernel | §3 (Ty), §4 (Tm), §9 (eval) |
| Want to formalize proofs | §8 (HM), §10 (compilation pipeline) |
| Want to know what's out | §12 |

File map:

| File | Role |
|---|---|
| `WenDef.lean` | Kernel: `Ty`, `Tm`, `MatchPat`, `MatchArms`, `typeCheck`, `substTmFree` |
| `WenDefEval.lean` | Runtime: `Value`, `evalFuel`, `applyFuel`, fuel discipline |
| `WenSurface/Lex.lean` | Tokeniser: glyphs, multi-char surfaces, brackets |
| `WenSurface/Reading.lean` | Atom resolver: `ResolvedAtom`, `SyntaxMarker`, bracket pairs |
| `WenSurface/Syntax.lean` | `SurfaceExpr` parser (Pratt, prefix/infix/postfix/mixfix) |
| `WenSurface/Elaborate.lean` | `SurfaceExpr → Tm` with HM-driven binder type pick |
| `WenSurface/TypeInfer.lean` | Hindley-Milner: `MTy = Ty + .mvar Nat`, Robinson unify |
| `WenSurface/EndToEnd.lean` | Statement-level pipeline + cross-stmt env |
| `WenSurface/Namespace.lean` | `用 NS` 学派 activation |
| `WenSurface/RewriteRules.lean` | `定 LHS 等 RHS` normalize |
| `WenSurface/PrettyPrint.lean` | `Tm → String` (not round-trip) |
| `WenSurface/ErrorRender.lean` | Source-spanned error with caret |
| `REPL.lean` | `wen` CLI exe |

---

## 1  Lexical structure

### 1.1 Glyph classes

| Class | Codepoint range | Used in |
|---|---|---|
| CJK basic | U+4E00…U+9FFF | identifiers, operators, hexagram names |
| CJK ext-A | U+3400…U+4DBF | rare characters (some hexagrams) |
| ASCII letters | a-z, A-Z | (reserved; not used in surface programs) |
| ASCII digits | 0-9 | (reserved; no numeric literals) |
| ASCII spaces | space, tab, `\n`, `\r` | token separation |
| Ideographic space | U+3000 (`　`) | token separation |
| Brackets | `（）` `()` `「」` `『』` `〈〉` | grouping + quoting |
| Separators | `；` `。` `;` | statement-level |
| Slash | `/` `／` | declaration internal (rare) |
| Pipe | `|` `｜` | `类 NAME = CTOR | CTOR` |
| Arrow | `→` `->` | `析 X 为 PAT → EXPR` (statement-form only; parsed pre-lex) |

### 1.2 Multi-character surfaces

Several semantic atoms span multiple glyphs and are recognized by `WenSurface/Lex.lean` table-lookup:

- **64 hexagram names** (e.g. 乾, 坤, 既济, 同人, 噬嗀, …)
- **30+ catalogue compounds** (e.g. 過半, 無為, 錯綜, 兼愛, 無不為, 大同, 中庸, …)
- **3 final particles compounds**: 之又 (iteration), 之所以 (reason-extraction)

Lexing is **greedy-longest-match** within the registered surface table.

### 1.3 Atom kinds (`ResolvedAtom`)

After lexing, each token resolves to one of:

| Atom | Carries | Example surface |
|---|---|---|
| `hexConst h` | `Hexagram` | 乾 / 同人 |
| `boolConst b` | `Bool` (真/假) | 真 / 假 |
| `varName n` | `String` (heavenly stem only) | 甲 / 乙 / 丙 / 丁 / 戊 / 己 / 庚 / 辛 / 壬 / 癸 |
| `catalogueOp r` | `OperatorReading` | 推, 不, 凡, … (375 ops) |
| `appMarker` | (none) | 之 |
| `iterate` | (none) | 之又 |
| `openBracket b` / `closeBracket b` | bracket kind | `（` `「` `『` `〈` etc. |
| `syntax s` | `SyntaxMarker` | 者, 凡, 令, 曰, 执, 所, 之所以, 属 |
| `ambiguousOp` | (none) | 也, 而 (positionally disambiguated) |
| `hexOrOp h r` | Hex + Op reading | 同 (hex 13 vs equality op), 比 (hex 8 vs relation) |

**Variable name policy**: bare CJK identifiers are restricted to the **10 Heavenly Stems** (甲乙丙丁戊己庚辛壬癸) because the Lean 4 stock lexer rejects bare CJK and Mathlib-rebuild cost forbids a toolchain fork (see `feedback_lean_cjk_identifiers`). User-defined names declared via `定 NAME 为 BODY` are also restricted to single-stem names in v1.

### 1.4 Quote brackets (`「」` / `『』` / `〈〉`)

Quote brackets are **separate** from grouping brackets (`（）` and `()`):

- `「X」` (primary) — wraps `X` as deferred Tm data; elaborator emits `Tm.quote X'`
- `『X』` (nested / alternate) — same semantics; for nesting clarity
- `〈X〉` (alternate) — same semantics

The token inside a quote bracket is parsed as a normal `SurfaceExpr` first, then wrapped. The body need not typecheck strongly (its outer type is always `Ty.quoted`).

---

## 2  Statement separators and chunks

A Wen **program** is a sequence of **chunks** separated by `；`, `。`, or `;`. There is no semantic distinction between the three separators at parse time (cross-statement env updates are separator-blind), except `。` clears the `PendingBinder` for ⑨ subject ellipsis (see §10.3).

```
chunk₁；chunk₂。chunk₃；chunk₄
```

Each chunk is either:

- A **declaration** (`定`, `定递`, `用`, `类`, `析` — see §6)
- A **code expression** (anything else — produces a `TypedTm` for the program output)

Chunks have a **chunk-leading keyword** which determines dispatch. The keyword is the first non-whitespace token of the chunk.

---

## 3  Type system (`Ty`)

The kernel type universe is a 10-case inductive defined in `WenDef.lean`:

```
inductive Ty
  | hex                            -- Hexagram (64)
  | bool                           -- Bool (2)
  | cell                           -- R8 = R₄² = 256 (the squaring tower top)
  | catalogue (kind : SignatureKind)
  | prod (fst snd : Ty)
  | list (elem : Ty)
  | arr (dom cod : Ty)
  | quoted                         -- wen-2.0 ⑥: Tm-as-data
  | user (name : String)           -- wen-2.0 ④: nominal user inductive
  | set (elem : Ty)                -- wen-2.0 ⑦: predicate extension
deriving DecidableEq, Repr
```

### 3.1 Type semantics

| `Ty` | Interpretation | Cardinality |
|---|---|---|
| `hex` | Hexagram (R₈ projection at 时=道) | 64 |
| `bool` | `Bool` | 2 |
| `cell` | R8 = R₄² (full squaring-tower top) | 256 |
| `catalogue k` | placeholder for catalogue operator result; eliminated by surface | varies |
| `prod a b` | `a × b` | `|a| · |b|` |
| `list a` | `List a` | countably infinite |
| `arr a b` | `a → b` | function space |
| `quoted` | `Tm` (deferred, opaque) | countably infinite |
| `user "N"` | nominal type, ctor-table-bound | size of declared ctor list |
| `set T` | predicate `T → Bool` | finite subset family if `T` finite |

### 3.2 `cell` and the R-tower

`cell = R8 = R₄²` is derived from the squaring tower (`R₀ = 1, R_{k+1} = R_k²`). V₄ Shi is **doctrine-out** as of 2026-05-17 — Cell256 is **not** `Hex × Shi`; it is `R₄²`. See `project_v4_shi_doctrine_out_2026-05-17.md`.

### 3.3 `Ty.quoted` opacity

`Ty.quoted` is intentionally **opaque** to HM inference: unification rejects `quoted ↔ T` for any concrete `T`, so quoted subtrees cannot leak typing constraints into surrounding expressions. The `执` (unquote) operator (⑪) defaults the result to `.hex` (the "everything reduces to a Hex in the end" doctrine).

### 3.4 `Ty.user` nominal equality

Two `Ty.user "N₁"` and `Ty.user "N₂"` are equal iff `N₁ = N₂` as strings. There is no structural subtyping or row polymorphism.

### 3.5 `Ty.set` finite extension

`Ty.set T` carries a `T → Bool` predicate. Membership is decidable but enumeration is NOT (kernel cannot reify the predicate's extension). The element type `T` is typically `.hex` (which would give a 64-element family upper bound) but can be any `Ty`.

---

## 4  Term language (`Tm`)

The kernel term `Tm` is a single-sorted mutual inductive (mutual with `MatchArms` for derivable `DecidableEq`). It has 49 constructors:

### 4.1 Core syntactic forms

| Constructor | Shape | Typing rule (informal) |
|---|---|---|
| `var n` | variable reference | `(n, t) ∈ ctx ⊢ var n : t` |
| `abs n t body` | λ-abstraction | `(n, t) :: ctx ⊢ body : t' ⇒ abs n t body : t → t'` |
| `app f x` | function application | `f : t → t', x : t ⊢ app f x : t'` |

### 4.2 Literals

| Constructor | Type |
|---|---|
| `hexLit (h : Hexagram)` | `hex` |
| `boolLit (b : Bool)` | `bool` |
| `cellLit (c : R8)` | `cell` |

### 4.3 Core builtins (22 Hex/Bool + 12 cell-endo + 5 list/pair)

22 core algebra ops (returning `hex` / `bool` / `(hex → ...)`):

- **Hex algebra**: `jia 加`, `yi 一` (literal 0), `cuoH 错`, `zongH 综`, `huH 互`, `cuoZongH 错综`, `flip[1-6]H 初/二/三/四/五/上爻`
- **Bool algebra**: `notB 不`, `andB 並`, `orB 或`
- **Hex predicates / quantifiers**: `eqHex 同`, `forallH 凡`, `uniqueH 唯`, `exactly3H 三`, `majorityH 過半`
- **List/pair**: `pairH 對`, `dupH 倍`, `list1H 列一`, `list2H 列二`, `list3H 列三`, `headH 首`

12 cell-endo ops (R8 → R8): `eqCell 同位`, `cuoC 错位`, `zongC 综位`, `huC 互位`, `shiNextC 进时`, `shiPrevC 退时`, `flip[1-6]C 位初爻…位上爻`

### 4.4 Catalogue ops

`catalogue1 / catalogue2 / catalogue3 : OperatorId → Tm → … → Tm`

The 375 OperatorIds span 27 groups (R/C/T/F/B/Q/K/M/N/I/S/H + 学派层 P/G/A/D/E/L/Y/X/Z/ZHU/SUN/CHU/LIJ/ZA). Each carries a signature (1/2/3-ary) per `OperatorSignatures.lean`. See `WenSurface/Coverage.lean` for the full table.

### 4.5 Wen 2.0 constructors

| Constructor | Surface form | Notes |
|---|---|---|
| `quote (body : Tm)` | `「BODY」` | wen-2.0 ⑥/⑩, opaque (`.quoted`) |
| `unquote (q : Tm)` | `执 q` | wen-2.0 ⑪, result `.hex`, fuel-bounded |
| `fix (n t body)` | (kernel-only) | wen-2.0 ②, surface decl `定递 n 为 body` |
| `userCtor (typeName ctorName)` | bare ctor glyph in scope | wen-2.0 ④ |
| `«match» scrut arms` | (statement-form `析 …`) | wen-2.0 ⑤ |
| `setOf (pred : Tm)` | `PRED 者` (noun position) | wen-2.0 ⑦ |
| `memberOf (x s : Tm)` | `X 属 S` | wen-2.0 ⑦ |

### 4.6 `MatchPat`

```
inductive MatchPat
  | lit (h : Hexagram)
  | boolP (b : Bool)
  | userP (typeName ctorName : String)
  | wildcard
  | varP (n : String)
```

Pattern type compatibility (see `patternBindings`):

- `lit h` requires scrutinee `.hex`
- `boolP b` requires scrutinee `.bool`
- `userP T C` requires scrutinee `.user T`
- `wildcard` matches any
- `varP n` matches any, binds `n` with scrutinee's type

Patterns are **flat** (no nesting) and **non-exhaustive** in v1 (runtime returns `none` on no-match).

### 4.7 `typeCheck` (total, decidable)

`typeCheck : Ctx → Tm → Option Ty` is a total Lean function. It is the **ground truth** for typing: anything that passes `typeCheck` is well-typed. Surface elaboration may use HM inference as a planning oracle (§8), but the resulting `Tm` must satisfy `typeCheck`.

---

## 5  Surface expressions (`SurfaceExpr`)

The Pratt parser (`WenSurface/Syntax.lean`) produces a `SurfaceExpr` then elaborates to `Tm`:

```
inductive SurfaceExpr
  | atom (tok : ResolvedTok)
  | app (f x : SurfaceExpr)
  | seq (items : List SurfaceExpr)
  | marker (tok : ResolvedTok) (body : SurfaceExpr)        -- 之 / postfix
  | binder (kind : BinderKind) (name : String) (body : SurfaceExpr)
  | letBind (name : String) (value body : SurfaceExpr)
  | construction (name : String) (items : List SurfaceExpr)  -- 曰, 执, 所…者 desugar
  | grouped (openTok closeTok : ResolvedTok) (body : SurfaceExpr)
```

### 5.1 Application (juxtaposition)

Adjacent expressions associate **left-to-right** by default:

```
推 一       ⟹  app 推 一
推 推 一     ⟹  app (app 推 推) 一  ?  NO — 推 is unary, so:
推 (推 一)   ⟹  app 推 (app 推 一)
```

Wen distinguishes unary/binary/ternary operators by their **catalogue signature**. The parser consults `OperatorSignatures` for arity; surplus args become a separate application:

```
加 一 一       ⟹  app (app 加 一) 一  (加 is binary)
推 一 一       ⟹  app (app 推 一) 一  but推 is unary, so the second 一 is a syntax error
```

The explicit application marker `之` (S_1) forces application:

```
f 之 x         ⟹  app f x
```

### 5.2 Binders

Three head-position keywords introduce binders:

| Keyword | Kind | Surface | Tm |
|---|---|---|---|
| `者` | λ | `者 NAME body` | `abs NAME T body` (T inferred via HM, §8) |
| `凡` | ∀ | `凡 NAME body` | `app forallH (abs NAME hex body)` |
| `令` | let | `令 NAME 为 VALUE 用 BODY` | `app (abs NAME T BODY) VALUE` (T inferred) |

Note `者` is **context-sensitive** post wen-2.0 ⑦:

- **Head position** (`者 NAME body`) — λ-binder as above
- **Noun position** (`PRED 者` with `PRED` immediately preceding) — nominalize predicate via `Tm.setOf` (§7.5)

### 5.3 Infix

Two infix operators (with their own precedence and nonassoc rule):

| Op | Surface | Tm | Precedence |
|---|---|---|---|
| `I_1` | `同` | `app (app eqHex a) b` | 40 |
| `R_8` | `比` | `catalogue2 R_8 a b` | 40 |

Plus the wen-2.0 ⑦ infix:

| Op | Surface | Tm | Notes |
|---|---|---|---|
| (sym) | `X 属 S` | `memberOf x s` | postfix-app dispatch; consumes one trailing |

### 5.4 Postfix

Five postfix particles (precedence 10, bind tightly to the immediately preceding expression):

| Op | Surface | Tm | Notes |
|---|---|---|---|
| `S_14` | `也` | `catalogue1 S_14 e` | predication/finality |
| `S_21` | `乎` | `catalogue1 S_21 e` | interrogative final |
| `S_22` | `矣` | `catalogue1 S_22 e` | perfective final |
| `S_23` | `哉` | `catalogue1 S_23 e` | exclamatory final |
| `S_24` | `兮` | `catalogue1 S_24 e` | lyrical/aesthetic final |

### 5.5 Iteration

`之又 op arg` ⟹ `app op (app op arg)` (double-iterates the unary op).

### 5.6 Grouping vs quoting

| Bracket pair | Role | Result |
|---|---|---|
| `（X）` / `(X)` | grouping | parsed as normal subexpression |
| `「X」` / `『X』` / `〈X〉` | quoting (wen-2.0 ⑩) | parsed then wrapped in `Tm.quote` |

---

## 6  Statement-form declarations

Statement-form chunks introduce names, types, or rewrite rules into the cross-statement environment. They produce no `TypedTm` for the program output.

### 6.1 `定 NAME 为 BODY` — user definition (substitution-based)

```
定 甲 为 推 之 一
```

Semantics: **textual substitution** before elaboration. Subsequent chunks see `甲` rewritten to `(推 之 一)` (with parens for safety).

Rules:
- NAME must be a single Heavenly Stem (甲…癸) or a multi-char surface not already in the catalogue
- Body is elaborated **once** at decl time; the resulting `Tm` is captured and substituted at use sites
- Recursive self-reference is **rejected** (`定 甲 为 甲 之 一` → error). Use `定递` (§6.2) for recursion.
- Redefinition is rejected
- Clashes with catalogue operators are rejected (see `nameConflictsWithCatalogue`)

### 6.2 `定递 NAME 为 BODY` — recursive user definition (μ-fixpoint)

```
定递 甲 为 者 乙 析 乙 为 一 → 一；_ → 加 之 一 之 甲 之 乙
```

Semantics: kernel `Tm.fix NAME T BODY` where `T` is inferred via HM. Each application unfolds one level; fuel exhaustion ⇒ `none` (clean error, no crash).

- Self-reference allowed and required (otherwise the `fix` wrapper is redundant)
- NAME restriction: single Heavenly Stem in v1
- Mutual recursion not supported (would need a join across multiple fixpoints)

### 6.3 `定 LHS 等 RHS` — rewrite rule (wen-2.0 ⑫)

```
定 错 错 甲 等 甲
```

Semantics: a rewrite rule `LHS → RHS` applied during expression-statement normalization. LHS is a pattern over `Tm` with pattern variables (heavenly stems only); RHS is a template using the same vars.

Restrictions:
- Linear patterns only (each var appears once on LHS)
- All RHS vars must occur on LHS
- LHS head must be a non-variable Tm constructor (concrete shape required)
- Bare-var LHS rejected (would match anything)
- New rules must not have an LHS head colliding with existing rules' LHS heads (conservative confluence check — head-disjointness)

Disambiguation with `定 NAME 为 BODY`: a chunk containing both `等` and `为` is rejected as ambiguous; chunks with `等` (not `为`) are rewrite decls; chunks with `为` (not `等`) are user defs.

### 6.4 `用 NS_NAME` — namespace activation (wen-2.0 ③)

```
用 墨经；用 名家；……
```

Semantics: adds `NS_NAME` (a 学派 surface like 墨经, 名家, 老子, 庄子, 列子, 朱子, 孙子, 楚辞, 礼记, 杂家) to the active namespace list. Subsequent operator resolution prefers operators tagged with active namespaces (v1: state threading only — no resolver filter yet).

42 surface aliases map to 12 OperatorGroups (`P`/`G`/`L`/`Y`/`ZHU`/`SUN`/`CHU`/`LIJ`/`ZA`/`E`/`X`/`Z`). See `Namespace.entries`.

### 6.5 `类 NAME = CTOR | CTOR | …` — user inductive (wen-2.0 ④)

```
类 五行 = 木 | 火 | 土 | 金 | 水
```

Semantics: declares a nominal type `Ty.user "NAME"` with zero-arg constructors `CTOR₁, …, CTORₙ`. Constructor bare-glyph references in subsequent chunks resolve to `Tm.userCtor "NAME" "CTOR"`.

Restrictions (v1):
- TYPENAME must not be a multi-char surface in the catalogue (e.g. `类 五行 = …` is rejected because `五行 = Y_2`)
- CTOR names must be single-token `.varName` leaves (Heavenly Stems only)
- Ctor clash with `定 NAME 为 ...` or with catalogue ops rejected
- No parameterized constructors
- No recursive/inductive references (e.g. `类 Tree = leaf | node Tree Tree` — out of scope)

### 6.6 `析 SCRUT 为 PAT₁ → EXPR₁；PAT₂ → EXPR₂；…` — pattern matching (wen-2.0 ⑤)

```
析 木 为 木 → 一；火 → 加 之 一；_ → 加 之 加 之 一
```

Semantics: kernel `Tm.match SCRUT (MatchArms.ofList [(p₁, e₁), …])`. Arms tried top-down at runtime; no-match yields evaluation error.

This is a **statement-form** chunk (not embedded inside expressions). The `→` and `；` glyphs are parsed by a pre-lex string scanner because Wen's CJK lexer does not natively handle them.

---

## 7  Special expression constructs

### 7.1 `曰` — direct speech (wen-2.0 ⑥)

```
甲 曰：「学」
```

Surface: `X 曰 「Y」` (the colon is optional whitespace).
Tm: `catalogue2 E_2 X (Tm.quote Y)` (where `E_2 = 曰`).
The right-hand argument is **automatically** wrapped in `Tm.quote` — it is treated as deferred data, not evaluated.

### 7.2 `执 「X」` — quote-eval (wen-2.0 ⑪)

```
执 「推 之 一」
```

Surface: `执 q` where `q` must have type `.quoted`.
Tm: `Tm.unquote q`.
Semantics: at runtime, decompose `q` to `Value.quoteV inner`, then `evalFuel env inner` (re-evaluates the inner term under the **current** env). Each unquote consumes one fuel tick.

Type rule: result is **always** `.hex` (the doctrine-driven default; could be refined in future).

### 7.3 `所 PRED 者` — object relativization (wen-2.0 ⑧)

```
所 推 者
```

Surface: `所` followed by an expression `PRED`, followed by a literal `者`.
Desugars to: `者 甲 PRED 之 甲` (a fresh λ-binder with `甲` as the implicit object).
Effect: nominalizes `PRED` as `λx. PRED x` — useful for picking up object-relativized clauses (「所信」 = "what is believed" = `λx. trusted x`).

Note: the legacy catalogue reading `S_16` (所 as Hex→Hex identity) is **shadowed** — `所` no longer reaches as an operator surface.

### 7.4 `Y 之所以 X` — reason-as-application (wen-2.0 ⑧)

```
乾 之所以 推
```

Surface: `Y 之所以 X` (where `之所以` is one multi-char surface).
Desugars to: `app X Y` (i.e., `X(Y)`).
Semantics: the rhetorical "what causes Y to X" collapses to ordinary function application in the kernel; surface form preserved only for pretty-printing.

### 7.5 `PRED 者` (postfix nominalizer, wen-2.0 ⑦)

When `者` appears **after** a complete predicate expression (and not in head position followed by a stem name), it acts as the nominalizer:

```
贤 者
```

Surface: `PRED 者` with `PRED` a `.bool`-returning function.
Desugars to: `Tm.setOf PRED` of type `Ty.set elem` (where `elem` is the predicate's input type).

Disambiguation from λ-binder: parser checks whether the `者` is followed by a stem name (`者 甲 …` → λ-binder) vs not (`PRED 者 …` → nominalizer).

### 7.6 `X 属 S` — set membership (wen-2.0 ⑦)

```
乾 属 (贤 者)
```

Surface: `X 属 S`. Infix; right operand is a `Ty.set elem`, left is an `elem`.
Tm: `Tm.memberOf X S`.
Result: `Ty.bool`.

### 7.7 `其` — subject pronoun (wen-2.0 ⑨)

A bare `其` in a statement is **rewritten textually** to the name of the currently-pending binder before parsing. The pending binder is established by a preceding statement that ended with an identity λ (v1: only `Tm.abs n t (.var n)` shape). Cleared on `。`.

```
凡 仁 者；其 心 善
```

Semantics:
- `凡 仁 者` is parsed first; its body is `仁` (a predicate); the surrounding `凡 ... 者` does NOT (currently in v1) leave a binder open
- v1 limitation: only literal `(者 甲 甲)` shape opens a pending binder
- Use case: `(者 甲 甲)；其 推` ⟹ `(者 甲 甲)；甲 推`

This is an **experimental** v1 — broader binder shapes (`凡`, `所…者`, `定递`) do not currently open `PendingBinder`. Future work in Wen 3.0.

---

## 8  Type inference (Hindley-Milner)

Implementation: `WenSurface/TypeInfer.lean`.

### 8.1 The `MTy` universe

```
inductive MTy
  | … (one constructor per Ty case)
  | mvar (n : Nat)
```

`MTy` extends `Ty` with metavariables for unification. After inference, `zonk` substitutes solutions back; **unsolved mvars default to `.hex`** (the "everything ends up Hex" doctrine; can surprise users with intended polymorphism).

### 8.2 Unification

Standard Robinson unification:
- Same-head: unify children pointwise
- Different-head: fail
- `.mvar n ↔ T`: occurs-check, then bind
- `.quoted ↔ T` (any non-`.quoted` T): fail (opacity)
- `.user N₁ ↔ .user N₂`: succeed iff `N₁ = N₂`
- `.set T₁ ↔ .set T₂`: unify T₁ and T₂

### 8.3 Inference scope

HM is invoked for:
- **Binder domain pick**: `者 NAME body` — domain type T inferred from how NAME is used in body
- **Rec-fix type**: `定递 NAME 为 BODY` — inferred from body's self-application shape
- **Catalogue arg expectations**: per-operator signature drives domain

HM is **not** invoked for: literal types, explicit `Ty.user`, `Ty.quoted` opacity boundary.

### 8.4 Back-compat: `pickBinderDomain`

For legacy reasons, `者 NAME body` enumerates a 5-candidate domain list (Hex / Bool / Cell / quoted / user) and uses HM as the **predicate** to validate each candidate, returning the first that fits. This preserves Wen 1.5 baseline behavior where `者 甲 甲 之 真` got `(Bool → Bool) → Bool` instead of the HM-default `(Bool → Hex) → Hex`.

---

## 9  Operational semantics

Implementation: `WenDefEval.lean`.

### 9.1 `evalFuel`

```
evalFuel : Env → Nat → Tm → Option Value
```

Total Lean function (no `partial`). Decreases fuel on each recursive call. Returns `none` on:
- Fuel exhaustion
- Unbound variable
- Type-incorrect application at runtime (should not occur if `typeCheck` passed)
- No-match in `Tm.match`

### 9.2 Value space

```
inductive Value
  | hexV / boolV / cellV       -- literals
  | pairV / listV               -- product / list
  | closV env n body            -- λ-closure
  | builtinV b args             -- partial application of builtins
  | catalogueV id kind args     -- catalogue op partial app
  | quoteV body                 -- deferred Tm data (⑥/⑩/⑪)
  | fixV env n body             -- μ-fixpoint value (②)
  | userCtorV typeName ctorName  -- user inductive value (④)
  | setV pred                   -- nominalized predicate (⑦)
```

### 9.3 Reduction strategy

**Call-by-value**, left-to-right argument order. Builtins reduce as soon as all required args are present (no thunking). Curry-style partial application for multi-arg builtins.

`Tm.fix` unrolls **on demand** (when applied): each unrolling consumes one fuel tick and substitutes the self-reference into the body.

### 9.4 `applyFuel`

```
applyFuel : Nat → Value → Value → Option Value
```

Applies a Value (function-shape) to a Value argument. Fuel-bounded; same `none` semantics on exhaustion.

---

## 10  Multi-statement compilation pipeline

Implementation: `WenSurface/EndToEnd.lean`.

### 10.1 The `wenyanCompile*` family

| Function | Output | Threads |
|---|---|---|
| `wenyanCompile : String → Except WenSurfaceErr TypedTm` | single Tm + Ty | nothing |
| `wenyanInterp` / `wenyanInterpBool` | Hex / Bool | (eval after compile) |
| `wenyanCompileProgram` | `List TypedTm` | (separators only) |
| `wenyanCompileProgramWithDefs` | `List Stmt × DefEnv × RewriteEnv × List UserCtor` | defs + rewrites + ctors |
| `wenyanCompileProgramWithNamespaces` | + `activeNamespaces` | + namespaces |
| `wenyanCompileProgramWithEllipsis` | + `PendingBinder` | + ⑨ ellipsis |

### 10.2 The `Stmt` type

```
inductive Stmt
  | defStmt    (name : String) (typedTm : TypedTm) (chunk : String)
  | recDefStmt (name : String) (typedTm : TypedTm) (chunk : String)
  | rewriteStmt (rule : RewriteRule)
  | classStmt  (typeName : String) (ctorNames : List String)
  | useDecl    (group : OperatorGroup) (chunk : String)
  | exprStmt   (typedTm : TypedTm)        -- ← the only kind that produces output
```

### 10.3 Cross-statement env

State threaded across chunks:

- **`DefEnv`** — `List (String × Tm)` for `定` substitutions (and the captured rec-def types for `定递`)
- **`RewriteEnv`** — list of compiled rewrite rules, applied to subsequent expr-stmts during normalization
- **`UserCtorEnv`** — `List UserCtor` with `(typeName, ctorName)` pairs
- **`activeNamespaces`** — `List OperatorGroup` (additive set)
- **`PendingBinder`** — `Option (String × Ty)`; set when a stmt ends with an identity λ; cleared on `。`; used for ⑨ `其` resolution

### 10.4 Chunk dispatch order

```
chunk → leading keyword check:
  类 …      → classStmt
  定递 …    → recDefStmt
  定 … 等 … 为 … → ambiguous, reject
  定 … 等 …  → rewriteStmt
  定 … 为 …  → defStmt
  析 …      → exprStmt (matchT)
  用 NS    → useDecl
  default → exprStmt (code)
```

Expression chunks go through: `rec-subst → user-ctor resolve → rewrite-normalize → typecheck → ellipsis 其 rewrite → typecheck`.

---

## 11  Tooling

### 11.1 `wen` REPL

CLI entry: `lake build wen && ./.lake/build/bin/wen`.

Commands:
- `:help` / `:h` / `:?` — show help
- `:quit` / `:q` — exit (Ctrl-D / EOF also works)
- `:type <expr>` / `:t <expr>` — show elaborated type
- `<expr>` — compile + evaluate + show result

Output dispatches on result type:
- `Hex` → hexagram name + 6-bit pattern (e.g. `«乾» (111111) : Hex`)
- `Bool` → `true / false : Bool`
- other → `<elaborated> : <type>` (function / pair / list / cell / catalogue / etc.)

### 11.2 PrettyPrint

`prettyPrintTm : Tm → String` (`WenSurface/PrettyPrint.lean`).

Renders all 49 Tm constructors back to surface-like文言:
- 22 core builtins via `builtinGlyph` table
- 12 cell-endo builtins via same
- catalogue ops via `OperatorId.title` first-glyph extraction
- abs / app / var / literals as standard
- `quote body` → `「BODY」`, `unquote q` → `执 q`
- `setOf pred` → `pred 者`, `memberOf x s` → `x 属 s`
- `userCtor _ cn` → `cn`
- `match scrut arms` → multi-line `析 SCRUT 为 …`
- `fix n t body` → `定递 n 为 BODY`

**Not round-trip safe**: parser cue resolution may pick alternate glyphs (e.g. `不` for `not`); the pretty-printed string is human-readable but not guaranteed to re-parse identically.

### 11.3 ErrorRender

`renderWenSurfaceErr : String → WenSurfaceErr → String` (`WenSurface/ErrorRender.lean`).

Emits source-line + caret indication for:
- `lex` errors (column anchor from `Lex.startCol`)
- `resolve` errors
- `parse` errors
- `elab` errors (caret at col 0 for now — limitation)
- `denoteFailed` errors

---

## 12  Out of scope (explicit non-goals)

| Feature | Reason |
|---|---|
| LLVM / WASM backend | user-excluded; Lean kernel is the only backend |
| 韵律 / 对偶 / 排比 | 诗经楚辞 surface, pure aesthetic |
| GC / async / concurrency | pure typed-λ; ref/effect breaks R8 projection doctrine |
| Classifiers (三人 vs 三個人) | marginal; classical Chinese doesn't enforce |
| Full trait / typeclass system | conflicts with catalogue inductive design |
| V₄ Shi as first-class axis | doctrine-out 2026-05-17; Cell256 = R₈ = R₄² |
| Compile-time macros (full) | partially covered by ⑪ quote/unquote |
| Parameterized inductives | v1 ④ scope cut; would need ctor signatures |
| Mutual recursion | ② v1 cut; would need fixpoint join |
| Exhaustiveness check for `析` | ⑤ v1 cut; runtime no-match returns `none` |
| Higher-order user inductives | ④ v1 cut |
| Module / foreign import | beyond ③ 学派; v1 only intra-program decls |

---

## 13  Reference appendices

### A. The 27 OperatorGroups

| Group | Surface | Notes |
|---|---|---|
| R | 关系 relations | I_1 同, R_8 比 |
| C | 称谓 称 | naming / referring |
| T | 推 inference | T_10 推 |
| F | 反 negation/inversion | F_8 反 (Hex) |
| B | 倍 doubling | B_1 倍 |
| Q | 求 求 | quantification / extraction |
| K | 可 modal | K_5 可 (possible) |
| M | 必 necessary | M_1 必 |
| N | 必 necessary alt | |
| I | identity / equality | I_1 同 |
| S | 句法 syntax | 也 / 乎 / 矣 / 哉 / 兮 / 之 / 之又 / 者 / 凡 / 令 |
| H | 卦 hexagram literal-as-op | 64 entries |
| P | 墨经 (墨家) | E.g. 兼愛 |
| G | 名家 | |
| A | 道家 | |
| D | (reserved) | |
| E | 易经 / 言说 | E_2 曰 |
| L | 老子 | |
| Y | 五行 / 阴阳 | Y_2 五行, Y_n 阴阳 |
| X | 荀子 / 礼记 | |
| Z | 杂家 / 补遗 | |
| ZHU | 朱子 | |
| SUN | 孙子 | |
| CHU | 楚辞 | |
| LIJ | 礼记 | |
| ZA | 杂家 | |

Total: 375 OperatorIds across these groups. See `formal/SSBX/Text/OperatorAnchors.lean` and `WenSurface/Coverage.lean`.

### B. Multi-character surface registry

See `formal/SSBX/Foundation/Wen/WenSurface/Lex.lean` for the authoritative table. Notable entries:

- All 64 hexagram names (e.g. 乾, 坤, 同人, 噬嗀, …)
- Algebra compounds: 過半, 錯綜, 兼愛, 無為, 無不為, 大同, 中庸, 莊周夢蝶, …
- Wen 2.0 multi-char: 之又, 之所以
- Quote brackets: 「」, 『』, 〈〉 (handled in `Reading.matchingCloseBracket?`)

### C. Acceptance test suites

All under `formal/SSBX/Foundation/Wen/WenSurface/`:

| File | Coverage |
|---|---|
| `UserDefsTests.lean` | 1.5 定 + 2.0 定递 |
| `TypeInferTests.lean` | ① HM |
| `UserInductiveTests.lean` | ④ 类 |
| `MatchTests.lean` | ⑤ 析 |
| `QuoteEvalTests.lean` | ⑪ 执 |
| `RewriteRulesTests.lean` | ⑫ 定…等 |
| `NominalizerTests.lean` | ⑦ 者 / 属 |
| `RelativeClauseTests.lean` | ⑧ 所…者 / 之所以 |
| `EllipsisTests.lean` | ⑨ 其 |
| `EndToEndTests.lean` | full surface acceptance (~339 examples) |

Plus `Namespace.lean` and `RewriteRules.lean` carry their own examples.

### D. Related docs

- [`wen-substrate.md`](../wen-substrate.md) — doctrine: R-tower, 易经, 道源
- [`wen-strata-invariants.md`](wen-strata-invariants.md) — CoreForm/Tm/R8Semantics distinct strata
- [`wen-2.0-spec.md`](wen-2.0-spec.md) — Wen 2.0 planning doc (now mostly historical; see `project_wen_2_0_complete_2026-05-17`)
- [`wen-language-roadmap.md`](wen-language-roadmap.md) — Wen 1.0 decisions
- [`samples/README.md`](../../formal/SSBX/Foundation/Wen/samples/README.md) — sample programs (sparse)

---

## 14  Versioning notes

- **Wen 1.0** (PR #26-37, 2026-05-17): kernel restructure, 5-stratum doctrine, 371 → 375 ops, B' universal ISA
- **Wen 1.5** (PR #39-44, 2026-05-17): REPL + PrettyPrint + multi-statement + ErrorRender + user-defs
- **Wen 2.0** (PR #46-65, 2026-05-17 → 2026-05-18): 12 spec items — HM inference, recursion, namespace, user inductive, pattern match, 曰+「」, 执 quote-eval, rewrite rules, nominalizer, relative clauses, subject ellipsis (+ V₄ Shi doctrine-out)

The Wen 2.0 ⑬ (Cell-level surface) was **removed** per doctrine: V₄ Shi is not a first-class axis (Cell256 derives from squaring tower R₄²).

Next anticipated: **Wen 3.0** would address ⑤ exhaustiveness, mutual recursion, parameterized inductives, broader subject-ellipsis binder shapes, and possibly a pedagogical sample suite.
