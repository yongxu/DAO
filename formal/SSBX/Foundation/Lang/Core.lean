/-
# Core — layer-polymorphic glue for the R-hierarchy Lisp

Re-exports `Sexp / Pattern / Rule / Eval` and provides the `LangLayer` type
class — the abstract interface every concrete layer (L1..L7..L8) implements.

## The yao/yuan duality

A cell `c : α` at layer `α` plays two semantic roles:

- **Yao role (data)**: the cell is a value in `α`.
- **Yuan role (operator)**: the cell is the function `λ s => apply c s = c ⊕ s`.

The two roles share one definition. `apply` IS the Cayley action:

```
applyAsCayley : (c : α) → (s : α) → apply c s = c.cayley s
```

For all our layers this is XOR on `(Z/2)ⁿ` and the equation holds by `rfl`.

## Layer interface

Every layer provides:

- `parseCell : Sexp → Except String α` — Lisp surface → cell
- `printCell : α → Sexp`               — cell → Lisp surface (round-trips)
- `apply    : α → α → α`               — Cayley XOR (the only operator we need)
- `origin   : α`                       — the (Z/2)ⁿ zero / 道-anchor
- `cardinality : Nat`                  — exposed `2 ^ n` for self-test
- `atomicOps : List α`                 — the n single-bit-flip masks (yao bases)

These are the v1 contract. The 文言 phase will add more (e.g., a `name`
field per cell for printing 古文 character labels), but the v1 interface is
sufficient to express the Lisp surface and the rewrite-rule semantics.

## Programs

A "program" in v1 is `(rules, initialCell, fuel)`. Run with `runLayered`.
-/

import SSBX.Foundation.Lang.Sexp
import SSBX.Foundation.Lang.Pattern
import SSBX.Foundation.Lang.Rule
import SSBX.Foundation.Lang.Eval

namespace SSBX.Foundation.Lang

/-- The contract every R-hierarchy layer fulfills to plug into the Lisp. -/
class LangLayer (α : Type) where
  parseCell    : Sexp → Except String α
  printCell    : α → Sexp
  apply        : α → α → α
  origin       : α
  cardinality  : Nat
  atomicOps    : List α
  /-- Apply is involutive: every cell is its own XOR-inverse. -/
  apply_self   : ∀ c : α, apply c c = origin
  /-- `origin` is the left identity. -/
  origin_apply : ∀ c : α, apply origin c = c

/-- Run the rule list on a cell-as-Sexp, returning the final Sexp.
    Caller bridges back to `α` via `parseCell` if needed. -/
def runOnLayer (rules : List Rule) (initSexp : Sexp) (fuel : Nat) : Sexp :=
  Eval.runRules rules initSexp fuel

/-- Convenience: run starting from a cell of type `α`, return the final cell
    (or an error if the resulting Sexp doesn't parse back to `α`). -/
def runCell {α : Type} [LangLayer α]
    (rules : List Rule) (init : α) (fuel : Nat) : Except String α :=
  let initSexp := LangLayer.printCell init
  let finalSexp := runOnLayer rules initSexp fuel
  LangLayer.parseCell finalSexp

/-! ## Yao/Yuan duality theorem (parametric)

Given any `LangLayer α`, the cell-as-data and cell-as-fn views of `c : α`
agree on application: both compute `apply c s`. Concrete layers will have
this as `rfl`; here we just state the abstract interface.
-/

/-- The Cayley action: cell-as-yuan operating on cell-as-yao. -/
def cayley {α : Type} [LangLayer α] (c : α) (s : α) : α :=
  LangLayer.apply c s

theorem cayley_eq_apply {α : Type} [LangLayer α] (c s : α) :
    cayley c s = LangLayer.apply c s := rfl

/-- Cayley regular action is involutive (each operator is its own inverse). -/
theorem cayley_self {α : Type} [LangLayer α] (c : α) :
    cayley c c = LangLayer.origin :=
  LangLayer.apply_self c

end SSBX.Foundation.Lang
