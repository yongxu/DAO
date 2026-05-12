# V4 Kernel Interpreter Architecture

> Status: draft v0.2 (2026-05-12)
> Lean anchors: `SSBX.Foundation.Wen.V4Kernel.*`
> Scope: V4-native interpreter kernel first; R0..R8 embedding second.

## Decision

The Wen interpreter kernel is a two-level system:

```text
V4 algebra
-> V4-native syntax, data, combinators, binding, quote/eval
-> representation backend contract
-> later R0..R8 embedding
```

The kernel is not built by patching R8 execution details into the syntax layer.
It starts from the mathematics of V4 as the minimum two-axis algebra.  R-space is
then a representation target with a proof obligation.

## Level 1: V4-Native Kernel

The first level is the self-contained interpreter core.

| Layer | Lean anchor | Role |
|---|---|---|
| alphabet | `Hierarchy.Operators.V4` | canonical Klein-four carrier and laws |
| syntax | `V4Kernel.Syntax` | free terms and quoted V4 trees |
| semantics | `V4Kernel.Semantics` | direct fold through `V4.compose` |
| encoding | `V4Kernel.Encode` | quote/decode terms as V4-labelled trees |
| universal evaluator | `V4Kernel.Universal` | evaluates quoted programs |
| self-host surface | `V4Kernel.SelfHost` | packages quote plus eval |
| data | `V4Kernel.Data` | V4 atoms, nil, cons, atom lists |
| combinators | `V4Kernel.Combinator` | V4 endomaps and term-level application |
| binding | `V4Kernel.Binding` | de Bruijn environment fragment |
| 64-word carrier | `V4Kernel.Word64` | `Word64 = V4 × V4 × V4`, not `Fin 64` |
| Lisp syntax | `V4Kernel.LispSyntax` | unified `Expr`, `Value`, and canonical Lisp `Env` |
| Lisp primitives | `V4Kernel.LispPrim` | exact-arity structural primitive table |
| Lisp evaluator | `V4Kernel.LispEval` | fuelled evaluator with closures, globals, quote, and `eval` |
| Lisp quote | `V4Kernel.LispQuote` | `Expr` as `V4Tree` and `Value` |
| Lisp universal | `V4Kernel.LispUniversal` | universal evaluator for encoded Lisp expressions |
| Lisp backend | `V4Kernel.LispRBackend` | backend contract for encoded expressions |
| R-space plan | `V4Kernel.LispRSpacePlan` | tree-over-cell carrier contract |
| surface elaboration | `V4Kernel.LispSurface` | 64-word names to de Bruijn locals or global refs |
| R6 word bridge | `V4Kernel.Word64Bridge` | R6 hexagram/Lexicon boundary for the 64 surface words |
| Sexp reader | `V4Kernel.LispReader` | boundary reader for the 64-word Lisp surface |
| VM compiler | `V4Kernel.LispCompile` | supported-fragment compiler boundary to `YiInstr` |
| Meta frontier | `V4Kernel.LispMetaInterp` | bridge into restored meta-interpreter obligations |

This level does not import R7, R8, Cell256, Bagua, or a concrete VM.  It may use
only the canonical V4 algebra and free syntax over V4 labels.

## Level 2: R-Space Representation

R0..R8 remains the intended audited coordinate space.  The kernel therefore
exposes a representation contract instead of choosing a backend too early:

```text
V4Tree
-> backend Code
-> Option V4Tree
-> universalEval
```

The Lean anchor is `V4Kernel.RBackend`.

A future R-space backend must prove:

```text
decodeTree (encodeTree tree) = some tree
```

Then the V4 universal theorem lifts automatically:

```text
evalEncodedTerm term = some term.eval
```

This is the correct direction: R-space implements the representation theorem;
it does not define the interpreter's syntax or semantics.

## Design Rules

- V4 is the alphabet and algebraic kernel.
- The 64 Wen words are represented internally as `Word64 = V4^3`; the R6
  King Wen lexicon is a surface bridge, not the core carrier.
- Lists, pairs, binding, and combinators are V4-native structures before they
  are R-space encodings.
- Core binding remains de Bruijn; surface `Word64` names elaborate either to
  local variables or to global references.
- `define` is immutable at the Lean level: it returns an extended `GlobalEnv`.
- R5+ word names remain deferred.  Use structural English and existing Lean
  identifiers.
- Temporal projection names stay `Temporal`, not `Shi`, in public V4 projection
  APIs.
- Backend modules may map into R0..R8 later, but they must preserve the V4
  quote/eval theorem.

## Current Completion Boundary

This architecture completes the first V4-native interpreter step:

```text
Term
-> encodeTerm : V4Tree
-> universalEval
-> term.eval
```

and extends it with data, combinators, binding, and an abstract backend
interface.  The minimal Lisp layer now additionally has:

```text
Expr / Value / Env
-> evalFuel
-> encodeExpr / decodeExpr
-> universalEvalExpr
-> LispBackend
```

The true Wen Lisp surface now adds:

```text
R6 King Wen token
-> Word64
-> SurfaceExpr
-> Expr
-> evalFuelG / evalTopFuel
```

Bare 64-word names read as references; quoted names read as symbol data.
Numbers are native `Nat` values, with the first reader covering existing
Chinese numerals 1..64 plus ASCII natural numbers.

The VM-facing layer is deliberately conditional: `LispCompile` emits `YiInstr`
for a small supported fragment and carries a Lisp-side evaluation witness, while
`LispMetaInterp` says how compiled fragments enter the restored
meta-interpreter frontier once its existing loop obligations are supplied.

It does not claim:

- recursive definitions or a full Scheme/Common Lisp standard library;
- arbitrary natural-language word coverage beyond the R6 word bridge;
- a concrete R8/Cell256 executable layout;
- full `metaInterpProg` arbitrary-program simulation.

Those are later representation and execution phases.

## Next R-Space Work

The next elegant R-space phase is a concrete backend instance:

```text
V4Tree -> R-space code stream -> Option V4Tree
```

The proof should be a representation theorem over the abstract backend
contract, not a rewrite of the V4 kernel.
