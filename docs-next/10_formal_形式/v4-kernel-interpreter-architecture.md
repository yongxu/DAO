# Native Wen Interpreter Architecture

> Status: supersedes the old V4 kernel interpreter draft (2026-05-13)
> Lean anchor: `SSBX.Foundation.Wen.Native`
> Scope: rank-polymorphic native Wen kernel over `Layered.Vn/Rn`.

## Decision

The active Wen interpreter kernel is no longer rooted in the old V4 interpreter
spine.  It is a native, arbitrary-rank kernel:

```text
Layered.Rn n / Layered.Vn n
-> Wen.Native.Expr n / Value n / Env n / GlobalEnv n / TopForm n
-> eval / quote / universal eval
-> backend contract
-> surface reader and program runner
-> Kleene target interfaces
```

The old V4 kernel modules remain available as compatibility and research
history, but they are not the active public interpreter API.

## Native Kernel Layers

| Layer | Lean anchor | Role |
|---|---|---|
| rank carrier | `Wen.Layered.VnRn` | `Rn n := BitSpace n`, `Vn n := BitSpace n` |
| syntax and values | `Wen.Native.Syntax` | `Expr n`, `Value n`, `Env n`, `GlobalEnv n`, `TopForm n` |
| evaluator | `Wen.Native.Eval` | fuelled eval with globals, closures, quote values, and `.eval` |
| code trees | `Wen.Native.Quote` | reference `CodeTree n`, encode/decode, value-level quote round trip |
| universal eval | `Wen.Native.Universal` | evaluates encoded native expressions and top forms |
| backend contract | `Wen.Native.Backend` | abstract representation contract plus `treeBackend` |
| surface | `Wen.Native.Surface` | cell-named surface forms to de Bruijn core expressions |
| reader | `Wen.Native.Reader` | S-expression boundary over native cells, with no YiInstr import |
| programs | `Wen.Native.Program` | top-form lists, surface programs, reader-backed programs |
| Kleene targets | `Wen.Native.Kleene` | `Halts`, `Computable`, universal/s-m-n/fixed-point/inverter targets |

## Design Rules

- Atomic program values are `Rn n` cells.
- Primitive layer operations are `Vn n`: `zero`, `xor`, `act`, cell `eq`, and
  slot `flip`.
- `V4`, `Word64/R6`, and `R8/Cell256` are bridges or examples over `Expr n`;
  they do not define separate interpreter roots.
- Core binding remains de Bruijn; surface names are cells that elaborate either
  to local variables or immutable global references.
- `define` is immutable at the Lean level: evaluation returns an extended
  `GlobalEnv`.
- Backend modules prove representation round trips; they do not redefine
  evaluation.

## Suspended Lines

The old `Foundation/Wen/V4Kernel` and its Lisp-named modules are compatibility
and research material.  YiInstr and restored `MetaInterp` also remain separate
backend/proof lines.  `Wen.Native` intentionally does not import those modules.

## Current Completion Boundary

This phase completes the public native spine:

```text
Expr n
-> evalFuel
-> CodeTree n
-> universalEvalExpr
-> Backend n
-> SurfaceTopForm n / Reader
```

Native Kleene currently stops at target interfaces and target assembly:

```text
FixedPointExists n
-> BoolInverterCompilerExists n
-> NativeKleeneInverter n
```

It does not yet supply hard witnesses for the universal interpreter,
s-m-n compiler, fixed-point compiler, or Boolean inverter compiler.  Those are
future proof/implementation obligations, not axioms added to this phase.
