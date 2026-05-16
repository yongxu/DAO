/-
# `SSBX.Foundation.Representation` — umbrella for the concept locator suite

Per `wen-substrate.md` v1.4 §Representation, the representation-closure
programme establishes that concepts and language both inhabit the R-Family
tower.  The **locator** algorithms make this map computable: given a
concept `c`, return its R-Family level `N` so that `c` lives in `R N`.

This umbrella pulls in the three independent locator strategies:

* **Strategy A** (`Representation.Concept`): compositional / denotational —
  a `Concept` inductive type mirrors the D1+P1–P7 primitives, and
  `Concept.level` computes the level by structural recursion.

* **Strategy B** (`Representation.Signature`): invariant fingerprinting —
  any concept yields a `ConceptSignature` (arity, modal flag, recursion
  depth, etc.), and the signature maps directly to the R-Family level.

* **Strategy D** (`Representation.Articulate`): self-articulation fixed
  point — `articulate` strips P7 (derivation) decorations; the fixed
  point's level matches Strategy A on every concept.

The three strategies agree on closed concepts (see `Articulate.locator_agreement`
for the A↔D equality).

Strategy C (lexical anchor table) is deferred — it slots in on top of
A by refining `Concept.cell` against the wen-substrate character tables.
-/

import SSBX.Foundation.Representation.Concept
import SSBX.Foundation.Representation.Signature
import SSBX.Foundation.Representation.Articulate
