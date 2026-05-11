# R0..R8 Root-Interpreter Unification

> Status: draft v0.1 (2026-05-12)
> Role: this document is the executable architecture note for making the small
> interpreter grow from the R0..R8 formal theory instead of living beside it.
> Lean anchors: `RootLanguageTree.lean`, `RootRuleKernel.lean`,
> `RootOperator.lean`, `RootWord.lean`, `RootRuleInstructionBridge.lean`,
> `RootWordRegistry.lean`, `RootWordMetaInterpBridge.lean`,
> `BaguaTuring.lean`, `MetaInterp/Universal.lean`.

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
```

This phase should prove only structural facts:

- every glyph has an R-layer and role;
- every word has an R8-visible semantic projection;
- every word has a loss ledger.

It should not claim that all natural-language readings are complete.

### Phase 2: instruction lowering ledger

For each existing `YiInstr`, record which root rule class it belongs to and
which parts remain parameter-specific:

| Instruction family | Root-rule reading |
|---|---|
| no-op / halt | return-to-Way boundary |
| set temporal component | lift / projection plus state update |
| flip coordinate | negation / XOR mask action |
| interlace / reverse | projected operator composition |
| complement | XOR mask action |
| branch | equality plus conditional |
| jump | recursion / control transfer |
| push | quote through history |
| pop | lookup from history context |

This is an audit ledger first. Exact per-parameter semantics can then be proved
module by module without moving the architecture.

The bridge should stay thin and one-directional:

```text
L0 instruction class
-> primary RootRule plus support RootRules
-> CoreForm readback
-> R8-visible projection and loss ledger
```

It must not make `MetaInterp` depend on the theory layer, and it must not claim
that root-rule evaluation is identical to VM state transition. Exact execution
facts remain in the VM and are linked only where the instruction exposes a real
current-cell endomap.

### Phase 3: glyph registry

Create a small registry format for accepted words:

```text
surface text
R-layer
root code
role
CoreForm meaning
optional YiInstr lowering
English reading
review status
claim anchor
```

The registry should be append-friendly: adding words extends the system without
changing the interpreter core. The seed registry should contain only the
undivided `Way` anchor; broad 1023-row coverage belongs in a generated registry,
not in a hand-maintained Lean file.

### Phase 4: self-interpreter alignment

Connect the `MetaInterp` universal path to the root-word layer:

```text
RootWord list
-> optional YiInstr targets
-> encoded program
-> META starting state
-> universal interpreter execution obligations
```

The intended theorem shape is not "natural language is finished". The intended
shape is:

```text
accepted rooted words compile into the R8 interpreter target,
and the universal interpreter executes that target with an explicit ledger.
```

The bridge at this layer should stop at the META input boundary:

```text
RootWordRegistry
-> List YiInstr
-> ProgEnc.encProg
-> RunWith h metaInterpProg encodedInput
```

The existing universal-compose file remains responsible for semantic loop
obligations. This keeps the rooted-word layer from absorbing the meta-interpreter
proof.

### Phase 4.1: loop-frame bridge discipline

The restored META route needs a bridge, but the bridge is not an ontology layer.
It is a narrow loop-frame contract between fetch, dispatch, and execute-block
proofs.

The issue is structural: dispatch must read the opcode tag through `META.cur`,
while execute blocks need `META.cur` restored to the simulated current R8 cell.
The current `fetchProgWithPeel` reaches dispatch with the halted-flag cell in
`META.cur` and the post-peel tail in history; it cannot be read as a
saved-current fetch outcome. The restored path therefore uses this contract:

```text
fetch produces:
  META.cur     = opcode tag
  META.history = simulated current R8 cell :: encMetaHistory regHex sim
  META.pc      = restored dispatch offset

dispatch routes by opcode tag
restore prelude pops simulated current cell
execute block receives the existing BlockPre shape
```

Lean anchors:

| Contract | Anchor |
|---|---|
| saved-current fetch target | `FetchSavedCur.SavedCurFetchOutcome` |
| uniform restore prelude | `DispatchRestore.restoreSavedCur_yields_BlockPre` |
| restored layout | `AssemblyRestorePlan.restoredMetaInterpProg` |
| fetch → dispatch → restore | `FetchDispatchRestore.savedCurFetch_dispatch_restore_yields_BlockPre` |
| first exact restored opcode path | `FetchDispatchRestore.savedCurFetch_dispatch_restore_execute_nop_simulates_aligned` |
| future real fetch walker boundary | `FetchSavedCurObligations.RestoredSavedCurFetchObligations` |

This is elegant only if it stays thin: it names the missing executable handoff,
composes already-proved pieces, and has a deletion path once the concrete fetch
walker directly proves the saved-current outcome. It must not become a second
interpreter or a place to hide semantic work.

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
