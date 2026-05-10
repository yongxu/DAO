/-
# Eval — fuel-bounded leftmost-first rewrite engine

Given a list of rewrite rules and a starting Sexp, repeatedly fire the first
matching rule per step. Stop when no rule matches (fixed point) or when fuel
is exhausted.

## Semantics

- `runOne` tries rules in list order; returns the result of the first match,
  or `none` if no rule matches.
- `runRules` iterates `runOne` up to `fuel` times. Returns the final Sexp,
  whichever ends first (fixed point or fuel exhaustion).

This is the simplest reasonable evaluator: it makes program behavior
predictable (rule order matters), keeps the engine total (fuel-bounded), and
does not attempt sub-pattern matching (rules match the *whole* current Sexp).

## Forward-compat note

The 文言 phase will likely want a richer evaluator: sub-tree rewriting,
priority-based selection, congruence-closure-style matching. Those are easy
to add as `runRulesV2` etc. — the v1 engine deliberately keeps its scope tight
so it's verifiable and easy to reason about.
-/

import SSBX.Foundation.Lang.Rule

namespace SSBX.Foundation.Lang

namespace Eval

/-- Try each rule in order. Return the first successful rewrite, or `none`. -/
def runOne (rules : List Rule) (target : Sexp) : Option Sexp :=
  rules.findSome? (fun r => r.apply target)

/-- Run the rule list iteratively. Returns the Sexp after up to `fuel` steps
of leftmost-first rewriting. Stops early on fixed point. -/
def runRules : List Rule → Sexp → Nat → Sexp
  | _,     target, 0      => target
  | rules, target, fuel+1 =>
      match runOne rules target with
      | some target' => runRules rules target' fuel
      | none         => target

/-- Did execution stop at a fixed point (rather than fuel exhaustion)? -/
def reachedFixedPoint (rules : List Rule) (target : Sexp) : Bool :=
  (runOne rules target).isNone

/-- Number of steps actually taken (≤ fuel). -/
def stepCount : List Rule → Sexp → Nat → Nat
  | _,     _,      0      => 0
  | rules, target, fuel+1 =>
      match runOne rules target with
      | some target' => 1 + stepCount rules target' fuel
      | none         => 0

end Eval

/-! ## Smoke checks -/

private def toggleYin : Rule :=
  Rule.named "toggle-yin"
    (.list [.atom "yao", .atom "0"])
    (.list [.atom "yao", .atom "1"])

private def toggleYang : Rule :=
  Rule.named "toggle-yang"
    (.list [.atom "yao", .atom "1"])
    (.list [.atom "yao", .atom "0"])

#eval Eval.runRules [toggleYin] (.list [.atom "yao", .atom "0"]) 1
  -- expect: (yao 1) — one step
#eval Eval.runRules [toggleYin] (.list [.atom "yao", .atom "0"]) 5
  -- expect: (yao 1) — fixed point after 1 step
#eval Eval.runRules [toggleYin, toggleYang] (.list [.atom "yao", .atom "0"]) 5
  -- expect: (yao 0) or (yao 1) depending on parity (5 = odd → (yao 1) → (yao 0) → ... — actually iteration runs up to 5, ends mid-cycle)
  -- with both rules active and runs alternating, after 5 steps starting from (yao 0):
  --   step 1: toggle-yin fires → (yao 1)
  --   step 2: toggle-yang fires → (yao 0)
  --   step 3: toggle-yin fires → (yao 1)
  --   step 4: toggle-yang fires → (yao 0)
  --   step 5: toggle-yin fires → (yao 1)
  -- expect: (yao 1)
#eval Eval.reachedFixedPoint [toggleYin, toggleYang] (.list [.atom "yao", .atom "0"])
  -- expect: false (some rule always fires)
#eval Eval.reachedFixedPoint [toggleYin] (.list [.atom "yao", .atom "1"])
  -- expect: true (toggle-yin's pattern is (yao 0); doesn't match (yao 1))
#eval Eval.stepCount [toggleYin] (.list [.atom "yao", .atom "0"]) 10
  -- expect: 1 — step 1 fires, then fixed point

end SSBX.Foundation.Lang
