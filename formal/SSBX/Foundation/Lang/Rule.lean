/-
# Rule — pattern → replacement rewrite rules

A `Rule` is `pattern ⇒ replacement` plus three forward-compat metadata fields:
- `name` — optional human-readable name (for debugging / 文言 phase output)
- `priority` — integer priority for ordering (higher fires first when both
  match; v1 ignores priority since rules are tried left-to-right, but the
  field is preserved for the 文言 phase)
- `kind` — `yao` / `yuan` / `both`. Distinguishes rules that operate on
  positions (state transitions) from rules that define operators (algebraic
  combinators). v1 default is `both`.

## API

- `Rule.apply : Rule → Sexp → Option Sexp` — try to fire the rule on a target.
- `Rule.fire? : Rule → Sexp → Bool` — does the rule's pattern match?
-/

import SSBX.Foundation.Lang.Pattern

namespace SSBX.Foundation.Lang

/-- Rule classification — yao (position) / yuan (operator) / both. -/
inductive RuleKind : Type
  | yao
  | yuan
  | both
  deriving Repr, Inhabited, BEq

/-- A rewrite rule with optional name/priority/kind metadata. -/
structure Rule where
  pat       : Pattern
  repl      : Sexp
  name      : Option String := none
  priority  : Int := 0
  kind      : RuleKind := .both
  deriving Repr, Inhabited

namespace Rule

/-- Apply a rule to a target Sexp. Returns `some result` on a successful match
+ substitution; `none` if the pattern doesn't match. -/
def apply (r : Rule) (target : Sexp) : Option Sexp :=
  match Pattern.matchPattern r.pat target with
  | some bindings => some (Pattern.subst bindings r.repl)
  | none          => none

/-- Does this rule's pattern match the target? -/
def fire? (r : Rule) (target : Sexp) : Bool :=
  (Pattern.matchPattern r.pat target).isSome

/-- Sort a rule list by priority descending (higher fires first). Stable on ties. -/
def sortByPriority (rules : List Rule) : List Rule :=
  rules.mergeSort (fun a b => a.priority > b.priority)

/-- Construct a no-name no-priority rule of kind `.both`. -/
def mk' (pat : Pattern) (repl : Sexp) : Rule :=
  { pat := pat, repl := repl }

/-- Construct a named rule. -/
def named (name : String) (pat : Pattern) (repl : Sexp) : Rule :=
  { pat := pat, repl := repl, name := some name }

end Rule

/-! ## Smoke checks -/

private def toggleYin : Rule :=
  Rule.named "toggle-yin"
    (.list [.atom "yao", .atom "0"])
    (.list [.atom "yao", .atom "1"])

private def captureRule : Rule :=
  Rule.named "swap-keep"
    (.list [.atom "sixiang", .atom "?x", .atom "0"])
    (.list [.atom "sixiang", .atom "?x", .atom "1"])

#eval toggleYin.apply (.list [.atom "yao", .atom "0"])
  -- expect: some (list [atom yao, atom 1])
#eval toggleYin.apply (.list [.atom "yao", .atom "1"])
  -- expect: none (pattern is `(yao 0)`, target is `(yao 1)`)
#eval captureRule.apply (.list [.atom "sixiang", .atom "1", .atom "0"])
  -- expect: some (list [atom sixiang, atom 1, atom 1])  -- ?x captured "1"
#eval captureRule.apply (.list [.atom "sixiang", .atom "0", .atom "1"])
  -- expect: none (second arg is "1", pattern wants "0")
#eval (toggleYin.fire? (.list [.atom "yao", .atom "0"]),
       toggleYin.fire? (.list [.atom "yao", .atom "1"]))
  -- expect: (true, false)

end SSBX.Foundation.Lang
