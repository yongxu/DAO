# V4² Action-Trace Calculus

> Status: launch kernel design
> Date: 2026-05-12
> Lean modules: `Foundation/Wen/V4Kernel/Mode16`, `WenAction`, `WenTrace`,
> `WenRecursion`

## Purpose

The Lisp layer is a useful runnable surface, but it is not the ontology of
Wen.  The core structure is smaller:

```text
R8 / Cell256       = state carrier
Word64 = V4^3      = 64-word state surface
Mode16 = V4 x V4   = action/control modes above the state carrier
Trace              = computation as a mode-labelled path
Recursion          = repeated path/self-action, hence finite cycles on R8
```

`Mode16` is not another cell space.  It is an operator layer over R8.  A mode
has two V4 coordinates:

- `word`: the uniform V4 action on the three V4 coordinates of a `Word64`;
- `temporal`: the V4 action on the R8 temporal coordinate.

This gives the sixteen basic structures as:

```text
Mode16 = V4_word x V4_temporal
```

They are enough to lift the 64-word surface into R8 dynamics without making
Lisp primitive.

## Core Semantics

For `word : Word64 = V4^3` and `mode : Mode16`:

```text
actWord mode (a,b,c)
  = (mode.word * a, mode.word * b, mode.word * c)
```

For an R8 view:

```text
R8View = Word64 x V4
actView mode (word, temporal)
  = (actWord mode word, mode.temporal * temporal)
```

Existing `R8 = Hexagram x Shi` is bridged through:

```text
Word64 ≃ Hexagram
V4 ≃ TemporalCoordinate
```

Thus the action is mathematically above R8 while preserving the current R8
implementation.

## Trace

A computation is a list of mode-labelled steps:

```text
before --mode--> after
```

The trace layer is diagnostic and semantic.  It can show the path from any
64-word state under chosen modes, without invoking Lisp.

## Recursion

On this kernel, recursion first appears as repeated self-action:

```text
x, f x, f (f x), ...
```

Because every V4 element is self-inverse, every fixed `Mode16` action is also
self-inverse.  Therefore repeated application has period at most two:

```text
f (f x) = x
```

This is not full Lisp recursion.  It is the primitive finite recursion/cycle
law of the Mode16 layer.  Full named recursion, macros, and self-hosting can be
compiled down to traces later, but they should not define the core.

## Boundary

Completed now:

- Mode16 algebra;
- Mode16 action on Word64 and R8 views;
- mode-labelled traces;
- finite recursion/cycle theorem for repeated Mode16 actions;
- executable examples.

Deferred:

- macro expansion;
- named recursive bindings;
- compiler lowering from Lisp/surface syntax to Mode16 traces;
- VM/meta-interpreter self-hosting.
