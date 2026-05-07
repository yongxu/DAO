# Shengsheng Buxi Documentation Preview

This directory is the staging area for a rebuilt documentation set. It does not yet replace the repository root documents; it is meant to become the single replacement once generated indexes and links are stable.

## Entry Points

- [Formal overview](10_formal_形式/README.md): Lean modules, build status, trust boundaries, and claim ledger.
- [Theory overview](20_theory_义理/README.md): Chinese doctrine/theory path, reorganized by theme instead of scattered files.
- [Archive pointers](archive-pointers.md): where old historical documents now point.

## Current Verification Policy

The Lean build now completes, with warnings. Trust-boundary facts are generated in [_generated/trust-boundary.md](./_generated/trust-boundary.md):

- one live axiom: `kleene_recursion_axiom`;
- one opaque sealed witness: `theOne`;
- one top-level partial executable boundary: `YiState.run`;
- no live `sorry`, `admit`, or `unsafe` declarations.

Machine-readable indexes live in [_generated](./_generated/). Authored documents should explain; generated indexes should carry counts, status, and source locations.
