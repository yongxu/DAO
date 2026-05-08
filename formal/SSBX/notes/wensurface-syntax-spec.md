# WenSurface Syntax Spec: brackets, precedence, infix, mixfix

Status: design spec and implementation tracker for the next WenSurface parser.
S0-S1 are implemented, binder domain inference has been regularized for Bool
and common function values, and S4 relation infix forms are implemented for
`同`/`比`.  S5 relation-chain diagnostics and relation infix JSON metadata are
also implemented.  S2/S3/S6/S7 remain design contracts.  This document defines the
contract that the next parser should satisfy while preserving the current
`wenyan-surface` behavior.

## 1. Goal

WenSurface should grow from the current prefix-only controlled language into a
table-driven surface syntax with:

- brackets / parenthesized grouping;
- explicit precedence and associativity;
- prefix, infix, postfix, and bounded mixfix operator forms;
- structured diagnostics for ambiguous or unsupported syntax;
- continued separation between catalogue coverage and executable semantics.

The target is not full natural-language classical Chinese.  The target is a
controlled formal surface language where every accepted syntactic form is
registered, inspectable, and typechecked before any evaluator result is
returned.

## 2. Non-goals

- Do not modify the frozen `baguaWen` 22-token parser.
- Do not make catalogue-only operators executable.
- Do not infer arbitrary natural-language grammar from prose.
- Do not add an unrestricted CFG or parser-combinator grammar that can silently
  compete with the operator registry.
- Do not change current accepted prefix programs such as `推 一`, `同 推 坤 乾`,
  `之又 不 真`, `凡 甲 同 甲 甲`.

## 3. Invariants

1. Resolver completeness and evaluator completeness remain different claims.
   All 371 `OperatorId` rows may have syntax entries, but only rows with
   theorem-backed `ExecutableSemantics` elaborate to runnable `WenDef.Tm`.
2. The parser returns an explicit `SurfaceExpr`; it does not directly emit
   `Tm`.
3. Every nontrivial parse decision is recoverable by `--ast` or `--explain`.
4. Ambiguous syntax is an error unless a registered syntax cue makes one form
   unique.
5. Brackets only affect grouping.  They do not promote unsupported operators to
   executable semantics.

## 4. Token Model

The lexer should distinguish glyph tokens from punctuation tokens.

```lean
inductive SurfaceTokKind where
  | glyph
  | openBracket
  | closeBracket
  | delimiter

structure SurfaceTok where
  surface  : String
  kind     : SurfaceTokKind
  startCol : Nat
  width    : Nat
```

Required bracket pairs for the first implementation:

| Open | Close | Status |
|---|---|---|
| `（` | `）` | required |
| `(` | `)` | dev/CLI convenience |

Deferred bracket pairs:

| Open | Close | Reason |
|---|---|---|
| `「` | `」` | useful for quoted terms, but can conflict with text quotation |
| `〔` | `〕` | useful for annotations, not needed for first parser |

Lexing rules:

- Whitespace remains insignificant.
- Existing multi-character surfaces still use longest-prefix matching.
- Brackets are single punctuation tokens even though they are not CJK glyphs.
- Unmatched closing brackets are parse errors, not lex errors.
- Unsupported ASCII letters remain lex errors.

## 5. AST

Current `SurfaceExpr` can be extended without breaking existing constructors.

```lean
inductive Fixity where
  | prefix
  | infix
  | postfix
  | mixfix

inductive SurfaceExpr where
  | atom (tok : ResolvedTok)
  | app (f x : SurfaceExpr)
  | seq (items : List SurfaceExpr)
  | marker (tok : ResolvedTok) (body : SurfaceExpr)
  | binder (kind : BinderKind) (name : String) (body : SurfaceExpr)
  | letBind (name : String) (value body : SurfaceExpr)
  | construction (name : String) (items : List SurfaceExpr)
  | grouped (openTok closeTok : SurfaceTok) (body : SurfaceExpr)
  | operatorForm (id : OperatorId) (fixity : Fixity)
      (surface : String) (args : List SurfaceExpr)
```

`operatorForm` is the preferred target for new infix/postfix/mixfix syntax.
Existing `.app` can continue to represent curried prefix application after
desugaring, but `--ast` should preserve fixity before elaboration.

## 6. Syntax Registry

Operator spelling, reading, syntactic form, and executable semantics are four
separate layers.

| Layer | Question |
|---|---|
| reading registry | What can this surface mean? |
| syntax registry | How can this operator bind in source? |
| signature registry | What type shape does the operator claim? |
| semantics registry | Can it elaborate to theorem-backed `Tm`? |

Suggested types:

```lean
inductive Assoc where
  | left
  | right
  | nonassoc

inductive PatternPart where
  | lit  (surface : String)
  | hole (name : String) (minPrec : Nat)

inductive SurfaceForm where
  | prefix  (prec : Nat)
  | infix   (prec : Nat) (assoc : Assoc)
  | postfix (prec : Nat)
  | mixfix  (pattern : List PatternPart) (prec : Nat)

structure SurfaceSyntaxEntry where
  id       : OperatorId
  surface  : String
  form     : SurfaceForm
  note     : String
```

Registry lookup must be context-sensitive:

- expression start: atom, bracket, binder, prefix, mixfix opener;
- after a left expression: infix, postfix, application marker;
- inside a mixfix pattern: expected literal delimiter or expression hole.

## 7. Precedence

Precedence values are parser-internal contracts.  They are not philosophical
claims about classical Chinese.

Higher number binds tighter.

| Prec | Class | Initial forms |
|---:|---|---|
| 100 | atom / grouped expression | literals, variables, `（ E ）`, `( E )` |
| 90 | postfix | reserved |
| 80 | prefix unary / prefix operator | `不`, `推`, `损/損`, `益`, `错/錯`, `综/綜`, `互`, `反` |
| 70 | application marker | `F 之 X`, explicit application/projection marker |
| 60 | iteration / construction | `之又 F X` |
| 50 | transform / composition infix | reserved for future transform operators |
| 40 | relation / equality infix | `E 同 E`, `E 比 E` |
| 30 | boolean connective | reserved for future `且`, `或` if promoted |
| 20 | binder body | `者`, `凡`, `令` |
| 0 | top level | full expression |

Associativity:

- prefix operators are right-binding: `不 不 真` parses as `不 (不 真)`;
- relation infix operators are `nonassoc`: `A 同 B 同 C` is a syntax error
  unless explicitly bracketed;
- application marker is left-associative for chained applications, but a
  non-function left side must fail in typecheck, not parse.

## 8. Pratt Parser Contract

The main parser should be Pratt-style:

```text
parseExpr(minBp):
  left := parseNud()
  while next token has led form with lbp >= minBp:
    left := parseLed(left)
  return left
```

`parseNud` handles:

- literals and variables;
- grouped expressions;
- prefix operators;
- binder keywords;
- mixfix openers.

`parseLed` handles:

- infix operators;
- postfix operators;
- explicit application marker `之`;
- mixfix continuations if a form requires a left argument.

Binding-power rule:

- left-assoc infix: parse right with `prec + 1`;
- right-assoc infix: parse right with `prec`;
- nonassoc infix: parse right with `prec + 1`, then reject another same-prec
  nonassoc operator without brackets.

## 9. Brackets

Accepted examples:

```text
同 （推 一） （推 一）
（推 一） 同 （推 一）
不 （同 一 乾）
推 （损 一）
```

Errors:

```text
（推 一
推 一）
（）
同 （推 一））
```

Diagnostics should include:

- unmatched opening or closing surface;
- source column;
- expected matching bracket;
- whether an expression was expected inside the bracket.

## 10. Infix Forms

The first infix promotion should be limited to executable relation operators:

| Surface | OperatorId | Prefix remains valid | Infix form |
|---|---|---|---|
| `同` | `I-1` | `同 A B` | `A 同 B` |
| `比` | `R-8` | `比 A B` | `A 比 B` |

Examples:

```text
一 同 一
推 乾 同 一
（推 乾） 同 一
乾 比 坤
```

`比` is also a hexagram name.  In expression-start position, `比` may be a
literal unless prefix arguments make the operator reading viable.  In led
position after a left expression, `比` may use its infix operator form.

Status: implemented by desugaring relation infix to existing curried
application AST: `A 同 B` becomes `同 A B`, and `A 比 B` becomes `比 A B`.
Relation chains such as `一 同 一 同 一` are rejected as non-associative syntax.
`--json --ast` and nested `--json --explain.ast` include a `syntaxForms` entry
for each detected source infix form with `fixity`, `precedence`, `assoc`, source
span, and desugaring metadata.

## 11. Prefix Forms

All currently executable prefix forms remain accepted:

```text
推 一
损 益 乾
不 真
同 一 一
凡 甲 同 甲 甲
令 甲 乾 推 甲
```

Prefix parsing should be implemented through the syntax registry, not hardcoded
recursive cases, except for binder keywords that remain language syntax.

## 12. Application Marker `之`

`之` remains explicit syntax, not a silent skip.

Accepted:

```text
推 之 一
者 甲 甲 之 乾
```

Parse-valid but type-invalid:

```text
乾 之 坤
```

Parse-invalid:

```text
推 乾 之
之
```

`之` should be represented as an application/projection marker in AST before
elaboration.  Elaboration may desugar successful application marker forms to
`SurfaceExpr.app`.

## 13. Mixfix Forms

Mixfix is bounded pattern matching, not a general grammar.

Allowed pattern parts:

- fixed literal delimiters;
- expression holes with minimum precedence;
- a fixed number of holes;
- no optional holes in the first implementation.

Example shape:

```lean
SurfaceForm.mixfix
  [ PatternPart.lit "若"
  , PatternPart.hole "cond" 0
  , PatternPart.lit "则"
  , PatternPart.hole "then" 0
  , PatternPart.lit "否则"
  , PatternPart.hole "else" 0
  ] 20
```

First implementation should add the machinery and one or two catalogue-only
examples, but should not claim executable semantics until a theorem-backed
denotation exists.

Mixfix diagnostics:

- missing delimiter;
- delimiter found at wrong precedence;
- ambiguous opener;
- unsupported operator after successful parse.

## 14. Binder Scope

Current binder forms remain prefix-only:

```text
者 甲 E
凡 甲 E
令 甲 V E
```

Scope rule:

- binder body consumes the lowest precedence expression;
- brackets can restrict body extent;
- unannotated `者` binders are inferred over a finite domain list:
  `Hex`, `Bool`, `Hex → Hex`, `Hex → Bool`, `Bool → Bool`, `Bool → Hex`;
- expected-function contexts parse `者` bodies under the expected argument
  type, so predicate/function arguments can be written directly.

Examples:

```text
凡 甲 甲 同 甲
凡 甲 （甲 同 甲）
令 甲 乾 （甲 同 乾）
者 甲 不 甲 真
者 甲 甲 推
而 者 甲 甲 者 甲 推 甲
```

The first two examples should parse to equivalent Bool expressions once infix
`同` exists.

## 15. Ambiguity Policy

The parser must not silently prefer executable readings over catalogue-only
readings when the syntax cue does not determine a unique reading.

Return `ambiguous` when:

- the same surface has multiple readings with the same viable fixity;
- two mixfix patterns share an opener and both can consume the same token span;
- a surface can be both delimiter and operator in the same context.

It may choose a reading when:

- source position determines fixity uniquely;
- bracket or delimiter context determines one pattern;
- only one candidate has a registered syntax entry for the current context.

Structured candidate output should include:

- surface;
- column span;
- `OperatorId` / code;
- fixity;
- support status: executable, with exact-vs-structural catalogue detail when available;
- expected argument types when available.

## 16. Error Taxonomy

Extend `ParseErr` rather than collapsing all failures into leftover tokens.

Suggested constructors:

```lean
inductive ParseErr where
  | empty
  | fuelExhausted
  | expectedExpression (col : Nat)
  | expectedVariable (surface : String) (col : Nat)
  | unexpectedToken (surface : String) (col : Nat)
  | unmatchedOpenBracket (surface : String) (col : Nat)
  | unmatchedCloseBracket (surface : String) (col : Nat)
  | expectedCloseBracket (openSurface expected : String) (openCol col : Nat)
  | nonassocChain (surface : String) (col : Nat)
  | ambiguousSyntax (surface : String) (col : Nat) (candidates : List SyntaxCandidate)
  | unsupportedSyntaxForm (surface : String) (col : Nat)
  | leftoverAtoms (count : Nat) (firstSurface : String) (firstCol : Nat)
```

CLI JSON should preserve the phase as `parse` for syntax failures and
`unsupported` for successful parse plus missing executable semantics.

## 17. Desugaring

Parser output should preserve source syntax.  A later normalization pass may
desugar:

- prefix operator form to curried `.app`;
- infix `A 同 B` to `operatorForm I-1 infix [A, B]`, then to `.app (.app same A) B`;
- `F 之 X` to application;
- `之又 F X` to `F (F X)`;
- grouped expressions to their body for typechecking while retaining group info
  in `--ast`.

Desugaring must occur before `WenDef.Tm` elaboration and after syntax
diagnostics.

## 18. Compatibility Tests

Existing examples that must continue to pass:

```text
一
乾
坤
推 一
推 之 一
推 推 一
同 一 一
同 推 坤 乾
比
同 比 比
比 乾 坤
不 真
之又 不 真
错 乾
凡 甲 同 甲 甲
令 甲 乾 同 甲 乾
```

New positive examples:

```text
（推 一）
同 （推 一） （推 一）
一 同 一
推 乾 同 一
（推 乾） 同 一
不 （一 同 乾）
凡 甲 甲 同 甲
令 甲 乾 甲 同 乾
```

New negative examples:

```text
（推 一
推 一）
（）
一 同 一 同 一
推 乾 之
乾 之 坤       -- parse ok, type error
五行 （乾）    -- parse/typecheck ok as structural catalogue normal form
```

## 19. CLI Contract

Inspection modes should show syntax-form data:

- `--tokens`: bracket tokens and delimiter tokens;
- `--resolve`: candidate readings and syntax entries;
- `--ast`: grouped/operatorForm/fixity nodes, or additive `syntaxForms` metadata
  when an implemented form is currently represented by desugared `.app`;
- `--typecheck`: type mismatch with grouped source spans;
- `--json`: stable fields for fixity, precedence, associativity, and support.

Example JSON fields for an infix form:

```json
{
  "node": "operatorForm",
  "operatorCode": "I-1",
  "surface": "同",
  "fixity": "infix",
  "precedence": 40,
  "assoc": "nonassoc",
  "args": [...]
}
```

## 20. Implementation Milestones

| Milestone | Status | Scope | Acceptance |
|---|---|---|---|
| S0 | done | Add this spec and preserve current parser | docs-only |
| S1 | done | Tokenize brackets and add grouped AST | current tests + bracket parse tests |
| S1b | done | Regularize Bool/function binder inference | `者 甲 不 甲 真`, `者 甲 甲 推`, predicate/function args |
| S2 | next | Add syntax registry for existing prefix forms | old parser behavior reproduced through registry |
| S3 | pending | Replace parser core with Pratt parser | all old examples pass, better parse errors |
| S4 | done | Promote `同` and `比` infix forms | prefix and infix both pass |
| S5 | done | Add nonassoc diagnostics and precedence JSON | relation chains fail structurally; relation infix JSON exposes precedence/assoc |
| S6 | pending | Add bounded mixfix parser machinery | catalogue-only mixfix can parse and diagnose unsupported |
| S7 | pending | Broaden syntax entries across 371 operators | all registered forms parse or diagnose ambiguity |

Each implementation milestone must pass:

```bash
lake build
lake build wenyan-surface
scripts/check_wenyan_surface_cli.py
python3 scripts/docs_next.py check --strict
```

## 21. Open Decisions

- Whether to keep `SurfaceExpr.app` as the normalized application node or make
  every operator application use `operatorForm`.
- Whether ASCII parentheses should remain permanently supported or only be a
  development convenience.
- Which catalogue-only mixfix forms should be used as the first parser test.
- How much source-span data should be carried in `SurfaceExpr` versus only in
  tokens.
- Whether binder inference should remain a fixed finite list or grow explicit
  type annotation syntax before infix/mixfix expands further.
