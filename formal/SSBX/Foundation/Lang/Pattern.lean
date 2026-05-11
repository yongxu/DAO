/-
# Pattern — structural matching on Sexp with `?`-prefixed variables

A pattern is an `Sexp`. Atoms whose name begins with `?` (e.g. `?x`, `?head`)
are variables that match any sub-Sexp and capture the matched value into a
binding. Everything else is matched literally and structurally.

## Examples

```
pattern   `(yao ?x)`      target `(yao 1)`        ⇒ bindings { x ↦ 1 }
pattern   `(yao 0)`       target `(yao 1)`        ⇒ no match
pattern   `(sixiang ?x 0)`target `(sixiang 1 0)`  ⇒ bindings { x ↦ 1 }
pattern   `?whole`        target `anything`       ⇒ bindings { whole ↦ anything }
```

## API

- `Pattern.matchPattern : Sexp → Sexp → Option Bindings` — try to match.
- `Pattern.subst : Bindings → Sexp → Sexp` — substitute bindings into template.
-/

import SSBX.Foundation.Lang.Sexp

namespace SSBX.Foundation.Lang

/-- A pattern is just an Sexp whose `?`-prefixed atoms are variables. -/
abbrev Pattern : Type := Sexp

/-- Variable bindings collected during a successful match. -/
abbrev Bindings : Type := List (String × Sexp)

namespace Pattern

/-- If `s` is an atom whose name begins with `?`, return the variable name
(without the `?`). -/
def isVar (s : Sexp) : Option String :=
  match s with
  | .atom name =>
      if name.startsWith "?" then
        some (String.ofList (name.toList.drop 1))
      else none
  | _ => none

mutual
partial def matchOne (pat target : Sexp) (acc : Bindings) : Option Bindings :=
  match isVar pat with
  | some name => some ((name, target) :: acc)
  | none =>
      match pat, target with
      | .atom a, .atom b =>
          if a == b then some acc else none
      | .named la lb, .named ra rb =>
          if la == ra && lb == rb then some acc else none
      | .list ps, .list ts =>
          if ps.length != ts.length then none else matchList ps ts acc
      | _, _ => none

partial def matchList (ps ts : List Sexp) (acc : Bindings) : Option Bindings :=
  match ps, ts with
  | [], [] => some acc
  | p :: ps', t :: ts' =>
      match matchOne p t acc with
      | some acc' => matchList ps' ts' acc'
      | none      => none
  | _, _ => none
end

/-- Top-level pattern match. -/
def matchPattern (pat target : Sexp) : Option Bindings :=
  matchOne pat target []

/-- Substitute bindings into a template Sexp. Variables not in the binding
list are left as-is (treated as free). -/
partial def subst (b : Bindings) (template : Sexp) : Sexp :=
  match isVar template with
  | some name =>
      match b.find? (fun p => p.fst == name) with
      | some (_, v) => v
      | none        => template
  | none =>
      match template with
      | .list xs   => .list (xs.map (subst b))
      | other       => other

end Pattern

/-! ## Smoke checks -/

#eval (Pattern.matchPattern (.atom "?x") (.atom "yao"))
  -- expect: some [("x", atom "yao")]
#eval (Pattern.matchPattern (.atom "yao") (.atom "yao"))
  -- expect: some []
#eval (Pattern.matchPattern (.atom "yao") (.atom "earth"))
  -- expect: none
#eval (Pattern.matchPattern
        (.list [.atom "yao", .atom "?x"])
        (.list [.atom "yao", .atom "1"]))
  -- expect: some [("x", atom "1")]
#eval Pattern.subst [("x", .atom "1")]
        (.list [.atom "yao", .atom "?x"])
  -- expect: (list [atom yao, atom 1])

end SSBX.Foundation.Lang
