# Mathlib PR: `class ElementaryTopos`

## Summary

Add a `Prop`-valued mixin `CategoryTheory.ElementaryTopos C` bundling Mathlib's existing
`HasFiniteLimits`, `CartesianMonoidalCategory` + `MonoidalClosed`, and
`HasSubobjectClassifier`. Provide the standard propagation instances and the canonical
example `Type u`.

## Motivation

Mathlib already supplies each component of an elementary topos independently:

- finite-limit completeness (`HasFiniteLimits`),
- cartesian-closed structure (`CartesianMonoidalCategory` + `MonoidalClosed`, the new
  replacement for the deprecated `CartesianClosed`),
- subobject classifier (`HasSubobjectClassifier`, added in 2024 by Conneen–Donato–Gy).

There is, however, no single typeclass that lets a user say *"`C` is an elementary
topos"* and reuse the standard derived facts (terminal, finite products, pullbacks,
equalisers, power object `Ω ^^ A`) without `haveI` boilerplate. This PR adds that
bundle. It does **not** prove deep results about topoi (e.g. Heyting structure on
subobjects, internal logic); it only assembles the existing infrastructure into a
ready-to-use mixin and verifies the prototypical `Type u` instance.

## What this adds

- `class ElementaryTopos (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C] : Prop`
  extending `HasFiniteLimits C` and `HasSubobjectClassifier C`. Data-bearing components
  (`CartesianMonoidalCategory`, `MonoidalClosed`) are instance parameters rather than
  `extends`, matching the pattern of `CategoryTheory.Regular` and
  `CategoryTheory.ObjectProperty.IsMonoidalClosed`.
- Propagation instances `toHasTerminal`, `toHasFiniteProducts`, `toHasBinaryProducts`,
  `toHasPullbacks`, `toHasEqualizers` (all `priority := 100`).
- Re-exports `ElementaryTopos.Ω C : C` and
  `ElementaryTopos.truth : Ω₀ ⟶ Ω`.
- `ElementaryTopos.PowerObject A = Ω ^^ A` (internal hom into Ω; powerset in `Set`).
- `Types.truth`, `Types.χ`, with `@[simp]` lemmas `truth_apply_down` /
  `χ_apply_down`.
- `Types.subobjectClassifier : Subobject.Classifier (Type u)` — the classical Lawvere
  construction `Ω := ULift Prop`.
- `Types.hasSubobjectClassifier : HasSubobjectClassifier (Type u)`.
- `Types.instElementaryTopos : ElementaryTopos (Type u)`.
- `example`-driven sanity checks that the propagation works end-to-end via
  `inferInstance`.

## Naming and style

- Copyright header (Apache 2.0).
- Module docstring with `## Main definitions`, `## Main results`, `## Implementation
  notes`, `## References` (LT70, MM92, Joh02, nLab).
- Theorems `snake_case`, definitions `camelCase`, class `PascalCase`.
- `@[simp]` on the `apply_down` lemmas.
- Universe variables explicit (`universe v u`); the class is parameterised over
  `Category.{v} C`.

## Dependencies

Only existing Mathlib modules:

- `Mathlib.CategoryTheory.Limits.Shapes.{FiniteLimits, FiniteProducts, Pullback.HasPullback}`
- `Mathlib.CategoryTheory.Monoidal.Closed.{Cartesian, Types}`
- `Mathlib.CategoryTheory.Monoidal.Types.Basic`
- `Mathlib.CategoryTheory.Subobject.Classifier.Defs`
- `Mathlib.CategoryTheory.Limits.Types.{Limits, Pullbacks, Products}`
- `Mathlib.CategoryTheory.Types.{Basic, Monomorphisms}`

No new axioms; 0 `sorry`. Net file size ~365 LOC.

## Build verification

```
$ lake build SSBX.Foundation.CategoryTheory.ElementaryTopos
Build completed successfully (913 jobs).
```

Verified against Mathlib pin `ea11ccc0c5c7c4c562742e918fe2e0b2814a58aa`.

## Future work (not in this PR)

- Heyting-algebra structure on `Subobject A` (Mac Lane–Moerdijk IV.8).
- Internal-language interpretation.
- Topos morphism / geometric morphism classes.
- Mitchell–Bénabou language.

## Author

Yongxu Ren (renyongxu@gmail.com).
