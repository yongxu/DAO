# R0..R8 Root-Interpreter Unification

> Status: draft v0.1 (2026-05-12)
> Role: this document is the executable architecture note for making the small
> interpreter grow from the R0..R8 formal theory instead of living beside it.
> Lean anchors: `RootLanguageTree.lean`, `RootRuleKernel.lean`,
> `RootOperator.lean`, `BaguaTuring.lean`, `MetaInterp/Universal.lean`.

## 0. Decision

The current system should be read as one stack, not two separate systems.

```text
R0..R8 carriers
-> root cells and root roles
-> root glyphs and root words
-> RootRule / CoreForm
-> YiInstr execution target
-> MetaInterp / universal self-interpretation
```

`BaguaTuring` already runs on `R8`, so the small interpreter is not outside the
formal theory. The remaining work is to make its instruction set, glyph layer,
and self-interpreter explicitly pass through the root-language interface.

## 1. Principle

Every extendable word should have four audit anchors:

| Anchor | Meaning |
|---|---|
| R-layer anchor | which `R0..R8` layer carries the root cell |
| role anchor | whether the root is read as cell, operator, or both |
| semantic anchor | the `RootOperator` / `CoreForm` meaning visible at `R8` |
| execution anchor | the optional `YiInstr` or meta-interpreter target |

Adding a new word should normally mean adding a new rooted entry and its semantic
bridge. It should not mean inventing a new ontology layer or a parallel
interpreter vocabulary.

## 2. Current Shape

| Layer | Current status | Next integration |
|---|---|---|
| `RootLanguageTree` | proves R0..R8 counts, root roles, and the 12 root rules | remains the ontology spine |
| `RootRuleKernel` | evaluates `CoreForm` to an R8-visible value with loss ledger | becomes the root-language semantic kernel |
| `RootOperator` | classifies masks, programs, projections, and aliases | becomes the operator boundary for words |
| `BaguaTuring` | executes `YiInstr` over `YiState.cur : R8` | becomes the VM target of rooted words |
| `MetaInterp` | builds the self-interpreter path over `YiInstr` | becomes the universal execution layer |

The clean reading is:

```text
root word
-> CoreForm meaning
-> optional YiInstr lowering
-> R8-state execution
```

## 3. What This Prevents

This structure rules out three failure modes:

| Failure mode | Replacement |
|---|---|
| treating opcode names as ontology | opcodes are execution targets for rooted words |
| treating historical catalogues as root structure | catalogues are aliases, evidence, or ledger rows |
| treating a word as just text | each accepted word has R-layer, role, semantics, and execution anchors |

It also preserves the important algebraic fact: at `R8`, a cell can be read as a
state and the same carrier can be read as an XOR mask operator. Negation,
composition, self-application, and return-to-origin are therefore not external
metaphors; they are the executable algebra of the root carrier.

## 4. Execution Phases

### Phase 1: root-word skeleton

Add a typed `RootWord` boundary:

```text
RootGlyph  = surface + RootInterfaceEntry + RootOperator
RootWord   = RootGlyph + CoreForm + optional execution target
YiInstr    -> RootRule / CoreForm classification
```

This phase should prove only structural facts:

- every glyph has an R-layer and role;
- every word has an R8-visible semantic projection;
- every word has a loss ledger;
- every `YiInstr` has a root-rule classification.

It should not claim that all natural-language readings are complete.

### Phase 2: instruction lowering ledger

For each existing `YiInstr`, record which root rule class it belongs to and
which parts remain parameter-specific:

| Instruction family | Root-rule reading |
|---|---|
| no-op / halt | return-to-Way boundary |
| set temporal component | projection plus state update |
| flip coordinate | negation / XOR mask action |
| interlace / complement / reverse | operator composition |
| branch | equality plus conditional |
| jump | lookup / control transfer |
| push / pop | quote / project through history |

This is an audit ledger first. Exact per-parameter semantics can then be proved
module by module without moving the architecture.

### Phase 3: glyph registry

Create a small registry format for accepted words:

```text
surface text
R-layer
root code
role
CoreForm meaning
optional YiInstr lowering
claim anchor
```

The registry should be append-friendly: adding words extends the system without
changing the interpreter core.

### Phase 4: self-interpreter alignment

Connect the `MetaInterp` universal path to the root-word layer:

```text
RootWord list
-> CoreForm / YiInstr lowering
-> encoded program
-> universal interpreter execution
```

The intended theorem shape is not "natural language is finished". The intended
shape is:

```text
accepted rooted words compile into the R8 interpreter target,
and the universal interpreter executes that target with an explicit ledger.
```

### Phase 5: expansion discipline

After the skeleton is stable, each new word must enter through the same gate:

1. choose the R-layer and root code;
2. choose cell/operator reading;
3. give a `CoreForm` or `RootOperator` meaning;
4. give a VM lowering only when it is executable;
5. add the theorem or ledger row that states exactly what is proved.

This keeps the framework small while allowing the vocabulary to grow.

## 5. Immediate Work Queue

1. Add `RootWord.lean` with the typed skeleton and `YiInstr` root-rule
   classification.
2. Run a direct Lean check on that file only.
3. Add the new document as the architecture anchor for later phases.
4. Continue from the roadmap by filling the lowering ledger and then the glyph
   registry.
