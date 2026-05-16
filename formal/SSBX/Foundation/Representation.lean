/-
# `SSBX.Foundation.Representation` — umbrella for the concept locator suite

Per `wen-substrate.md` v1.4 §Representation, the representation-closure
programme establishes that concepts and language both inhabit the R-Family
tower.  The **locator** algorithms make this map computable: given a
concept `c`, return its R-Family level `N` so that `c` lives in `R N`.

This umbrella pulls in four independent locator strategies:

* **Strategy A** (`Representation.Concept`): compositional / denotational —
  a `Concept` inductive type mirrors the D1+P1–P7 primitives, and
  `Concept.level` computes the level by structural recursion.

* **Strategy B** (`Representation.Signature`): invariant fingerprinting —
  any concept yields a `ConceptSignature` (arity, modal flag, recursion
  depth, etc.), and the signature maps directly to the R-Family level.

* **Strategy D** (`Representation.Articulate`): self-articulation fixed
  point — `articulate` strips P7 (derivation) decorations; the fixed
  point's level matches Strategy A on every concept.

* **Strategy E** (`Representation.OXPattern`): explicit bit-pattern
  parser — `fromOX : String → Σ N, R N` directly converts any o/x
  string of arbitrary length to an R-tower coordinate, with full
  bidirectional round-trip identities against `renderOX`.

Strategies A/B/D agree on closed concepts (see `Articulate.locator_agreement`
for the A↔B↔D triple).  Strategy E is the most concrete locator and is
the basis for downstream Strategy C (lexical anchor table) once 汉字 →
o/x patterns are tabulated.
-/

import SSBX.Foundation.Representation.Concept
import SSBX.Foundation.Representation.Signature
import SSBX.Foundation.Representation.Articulate
import SSBX.Foundation.Representation.OXPattern
