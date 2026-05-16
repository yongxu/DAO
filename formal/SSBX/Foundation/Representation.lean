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

* **Strategy C** (`Representation.Lexicon`): lexical anchor table —
  `LexicalAnchor : String → Option (Σ N, R N)` parametric over school /
  era / register; a school = a `LexicalAnchor` term loaded from a
  `.lex` text file or built from `Lang.Lexicon`.  Cross-school
  agreement on R-tower coordinates is decidable via `agreesAt`.
  Demonstrations across 6 schools (wen-substrate / yijing / confucian /
  daoist / buddhist / military) in `Lexicon/Examples.lean`.

Strategies A/B/D agree on closed concepts (see `Articulate.locator_agreement`
for the A↔B↔D triple).  Strategy E is the most concrete locator.
Strategy C closes the suite: it provides the **lexical input layer**
(汉字 / 词 → o/x string → Strategy E → R-tower coordinate), making the
full pipeline 字 ↦ R-tower computable for any school's lexicon.
-/

import SSBX.Foundation.Representation.Concept
import SSBX.Foundation.Representation.Signature
import SSBX.Foundation.Representation.Articulate
import SSBX.Foundation.Representation.OXPattern
import SSBX.Foundation.Representation.Lexicon
import SSBX.Foundation.Representation.Lexicon.Examples
