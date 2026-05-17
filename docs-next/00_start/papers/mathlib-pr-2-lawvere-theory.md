# Mathlib PR: `class LawvereTheory` and models

## Summary

Add `CategoryTheory.LawvereTheory T` (a small category with chosen generator and
finite-power tower), the structure `CategoryTheory.Model T C` of finite-product-
preserving functors, `CategoryTheory.LawvereTheoryHom` of theory morphisms, the
category instance on `Model T C`, the pullback functor along a theory morphism, and the
free Lawvere theory `free` as a term-model `Σ`-type packaging.

## Motivation

Lawvere theories (Lawvere 1963, *Functorial semantics of algebraic theories*) are one
of the standard categorical-logic counterparts of universal algebra. They are
equivalent to finitary monads on `Set` and to finitary varieties. Mathlib currently
has finitary monads (`Mathlib.CategoryTheory.Monad`) but no `LawvereTheory` class,
which makes it awkward to state Lawvere-theory-flavoured constructions (free algebra
on a signature, model functors, pullback along a theory morphism).

This PR provides that gap. The class is data-light (a generator object, a chosen
power family, and an `obj_isPow` axiom) and uses the *pseudo* (non-strict) variant —
each `pow n` is asked to be only isomorphic to the iterated binary product, which is
equivalent to the strict variant up to biequivalence (Lack–Rosický 2011) and is the
right choice for a Lean/Mathlib setting where finite products are characterised by a
universal property.

## What this adds

- `class LawvereTheory (T : Type u) [SmallCategory T]` with fields `δ`, `pow`,
  `hasFiniteProducts` (instance), `pow_zero_isTerminal`, `pow_one_iso`,
  `pow_succ_iso`, `obj_isPow`.
- `LawvereTheory.generator T`, `LawvereTheory.powObj` re-exports.
- `LawvereTheory.exists_iso_pow`, `LawvereTheory.isTerminal_pow_zero`,
  `LawvereTheory.pow_zero_iso_terminal`.
- `structure LawvereTheoryHom T T'` (functor + generator-preserving iso +
  `PreservesFiniteProducts`), with `LawvereTheoryHom.id` annotated `@[simps]`.
- `structure Model T C` (functor + `[PreservesFiniteProducts]`), `Model.carrier`,
  `Model.Hom` with `@[ext]`, identity / composition with `@[simps]`, the `Category
  (Model T C)` instance, and `@[simp]` lemmas `id_trans` / `comp_trans`.
- `Model.forget : Model T C ⥤ (T ⥤ C)` with `@[simps]`.
- `Model.pullback` along a theory morphism, with `@[simps]`, and `Model.pullback_id`.
- `LawvereTheory.Algebra` = `Model T (Type u)`.
- `LawvereTheory.FreeLawvereTheory.Term` (inductive, parameterised by free-variable
  type `α`) with `subst`, `subst_var_id`, `subst_subst` (the standard substitution
  lemmas).
- `LawvereTheory.FreeLawvereTheory.Obj` = `ULift ℕ`, `category` (small-category
  structure: morphisms = `n`-tuples of terms, composition = simultaneous
  substitution).
- `LawvereTheory.free (Sig : ℕ → Type u) : (T : Type u) × SmallCategory T`.
- Skeleton `lawvereTheory_equiv_finitaryMonad_skeleton : True`, deliberately
  placeholder (full Eilenberg–Moore correspondence is out of scope here).
- `example`-driven sanity block.

## Naming and style

- Copyright header (Apache 2.0).
- Module docstring with `## Main definitions`, `## Main results`, `## Design choices`,
  `## Implementation notes`, `## References` (Law63, Mac98, Bor94, ARV11, HP07, nLab).
- Theorems `snake_case` (`exists_iso_pow`, `pow_zero_iso_terminal`, `subst_var_id`),
  definitions `camelCase` (`powObj`, `preservesGenerator`, `preservesFiniteProducts`),
  classes / structures `PascalCase`.
- `@[ext]`, `@[simps]`, `@[simp]` applied where they pay off.

## Dependencies

Only existing Mathlib modules (small-category infra, finite products / preservation,
functor categories, `Types.Basic`).

No new axioms; 0 `sorry`. The skeleton theorem
`lawvereTheory_equiv_finitaryMonad_skeleton` has a trivial proof (`True`) and a
docstring stating that a real version requires `Mathlib.CategoryTheory.Monad.Algebra`.
Net file size ~625 LOC.

## Build verification

```
$ lake build SSBX.Foundation.Doctrine.LawvereTheory
Build completed successfully (786 jobs).
```

Verified against Mathlib pin `ea11ccc0c5c7c4c562742e918fe2e0b2814a58aa`. Full
downstream `lake build SSBX` also succeeds (3942 jobs) with no new warnings.

## Future work (not in this PR)

- Promote `free` from `(T, SmallCategory T)` Σ-type to a full `LawvereTheory` instance
  — requires bridging `Fin n` products with `ℕ + ℕ` addition via `mkFanLimit`.
- The `Set`-pointed-models adjoint to `free`.
- The Lawvere/finitary-monad equivalence
  (`lawvereTheory_equiv_finitaryMonad_skeleton`) — requires
  `Mathlib.CategoryTheory.Monad.Algebra` and a `FinitaryMonad` class.
- Enriched (Power 1999) version, which a separate file will provide on top of this
  one.

## Author

Yongxu Ren (renyongxu@gmail.com).
