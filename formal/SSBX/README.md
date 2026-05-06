# SSBX Lean Codebase

This directory contains the current clean Lean formalization of 生生不息论.

## Module Map

- `Core.lean`: terms, registries, three-valued logic, the minimal model, and the Γ/间/格/重/耦/法/生合 continuation interface.
- `Roster.lean`: formal symbol roster with Chinese quoted identifiers.
- `Text/Glyph.lean`: glyph and numbered-sense registry.
- `Text/WenyanOperators.lean`: wenyan operator catalogue from `wenyan-operators.md`.
- `Text/Completeness.lean`: text and operator coverage theorems.
- `Truth/Basic.lean`: claim, truth, semantic adequacy, and axiom-ledger core types.
- `Truth/ClaimLedger.lean`: finite claim ledger for the theory's core claims.
- `Truth/Semantics.lean`: formal semantic source assigned to each claim.
- `Truth/Adequacy.lean`: semantic adequacy and no-unregistered-claim theorems.
- `Truth/Absolute.lean`: ledger-dependent absolute-truth certificate.
- `Model/Adequacy.lean`: adequate-model principles and model-grounded truth.
- `Foundation/Monism.lean`: content-construction DAG from Γ, 三本（物/動/間）, 三显（位/場/際）, 三征（幾/勢/機）, and 開/閉 to 生生不息论.
- `Foundation/MonadRoot.lean`: single-root DAG proving all formal symbols, construction stages, and claims return to 一元 through a single glyph.
- `Foundation/JianOntology.lean`: Tier-1 間/Jian ontology: 三本, 三显, 三征, 開/閉, 網/體/流, and the self-referential witness.
- `Foundation/ShengshengBuxi.lean`: machine-checked minimal wenyan core returned to registered atoms: “诸期皆开，递递有间，境以其间而复开”.
- `Foundation/Li.lean`: code-level `理` certificate for the root-to-生生不息 expression, using numbered-sense syntax and truth adequacy.
- `Foundation/HumanAlignment.lean`: 人 as world self-focus and 做人 as intentional life-alignment.
- `Foundation/Attention.lean`: 注意 / Attention as mechanism over 聚焦 with cognitive-science mappings.
- `ConceptDAG.md`: registry/dependency DAG overview; it is complete but not intended to be single-root.
- `ConceptDAG.complete.mmd`: complete roster graph covering every registered symbol.
- `ConceptDAG.layered.mmd`: complete roster graph grouped by registry class.
- `ConstructionDAG.md`: content-construction DAG for the Γ/间 theory spine.
- `JianOntology.md`: human-readable map of the new 三本 / 三显 / 三征 / 開閉 / 網體流 architecture and its Lean anchors.
- `MonadDAG.md`: single-root generative DAG from 一元 to faces, core atoms, registered atoms, formal/construction items, and claims.
- `HumanAlignment.md`: human/alignment subtheory and rendered DAG.
- `Attention.md`: attention/focus distinction, mechanism components, and rendered DAG.

Regenerate the concept DAG after roster changes:

```bash
/Users/ren/repos/生生不息/scripts/generate_concept_dag.py
```

Render the Mermaid DAGs to SVG:

```bash
/Users/ren/repos/生生不息/scripts/render_concept_dag.sh
```

Render the construction DAG to SVG:

```bash
/Users/ren/repos/生生不息/scripts/render_construction_dag.sh
```

Generate and render the single-root Monad DAG:

```bash
/Users/ren/repos/生生不息/scripts/generate_monad_dag.py
/Users/ren/repos/生生不息/scripts/render_monad_dag.sh
```

Render the human alignment DAG to SVG:

```bash
/Users/ren/repos/生生不息/scripts/render_human_alignment.sh
```

Render the attention DAG to SVG:

```bash
/Users/ren/repos/生生不息/scripts/render_attention.sh
```

## Main Build

```bash
/Users/ren/.elan/bin/lake build
```

The top-level module is `SSBX.lean`.
