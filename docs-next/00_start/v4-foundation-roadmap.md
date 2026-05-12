# V4 Foundation Roadmap

> Status: active execution roadmap  
> Source of truth: [`docs-next/v4-foundation.md`](../v4-foundation.md)  
> Date: 2026-05-12

This roadmap turns the latest V4 foundation note into implementation phases.
The foundation note remains the doctrine text; this file tracks what must be
made true in Lean and, later, in the compiler/runtime track.

## Implementation Status

| Phase | Status | Primary modules |
|-------|--------|-----------------|
| 1. Mathlib-facing V4 interfaces | Done | `V4/Instances.lean` |
| 2. Preservation proof layer | Done | `V4/PreservationLogic.lean` |
| 3. Atlas and orbit completion | Done | `V4/Atlas.lean`, `V4/OrbitBurnside.lean`, `Word64Bridge.lean` |
| 4. V8 information preservation | Done | `Operators/V8Info.lean` |
| 5. Cross-level bridge | Done | `V4/V8Bridge.lean` |
| 6. V8 naming and metadata audit | Done | `Operators/V8Audit.lean` |
| 7. Compiler/runtime track | Boundary documented | no Clojure/compiler source is present in the current repository slice |

## Current Baseline

- Canonical V4 carrier exists at `SSBX.Foundation.Hierarchy.Operators.V4`.
- V4 action on hexagrams, R7, and R8 exists.
- Interlace is outside V4, as a separate non-invertible projection.
- TM local two-flip action routes through canonical V4.
- Preservation hierarchy exists as registry-level markers.
- Dao row and basic four-reading orbit lists exist.
- `Word64 = V4 x V4 x V4` and the R6 hexagram bridge exist.
- V4-native Lisp syntax, global references, numbers, quoting, reader, and
  small text examples exist under `Foundation/Wen/V4Kernel`.

## Phase 1 — Mathlib-Facing V4 Interfaces

Status: completed in `formal/SSBX/Foundation/Hierarchy/Operators/V4/Instances.lean`.

Goal: make the canonical V4 usable as a mathematical kernel without changing
its algebra-first definition.

Implement:

- finite instances for canonical `V4`;
- `Mul`, `One`, `Inv`, and `CommGroup` instances backed by `V4.compose`;
- an equivalence with `Bool x Bool`;
- a `MulAction`-style interface for hexagram action, if it fits without
  forcing unrelated imports into the core module.

Acceptance:

- existing pure `V4/Core.lean` remains the algebra center;
- Mathlib-facing instances live in a sidecar module;
- no domain interpretation is introduced into `Core.lean`.

## Phase 2 — Preservation Proof Layer

Status: completed in `formal/SSBX/Foundation/Hierarchy/Operators/V4/PreservationLogic.lean`.

Goal: upgrade registry markers into auditable finite proofs where the current
system can support them.

Implement:

- subgroup classification surface for the three nontrivial V4 axes;
- a small Boolean/implication model for the `cuoZong` contrapositive theorem;
- proof that `preservesAt g .algebraHom` and `preservesAt g
  .implicationTruth` select exactly `{dao, cuoZong}`;
- keep category-level claims as typed classification data unless a real
  category model is introduced.

Acceptance:

- `cuoZong` is primary, not merely syntactic composition;
- no external physics/history claim is presented as a Lean proof.

## Phase 3 — Atlas and Orbit Completion

Status: completed across `V4/Atlas.lean`, `V4/OrbitBurnside.lean`, and the
`Word64Bridge.hexagramEquiv` bridge.

Goal: make the V4 atlas and 64-hexagram orbit facts match the foundation note.

Implement:

- complete typed atlas rows for Wen, logic, category, Turing, Pauli, Galois,
  and semiotics;
- preservation markers attached to atlas entries;
- exact orbit support for hexagrams under V4 action;
- Burnside-style finite count or an equivalent executable enumeration for the
  64 hexagrams;
- explicit bridge theorem for `Word64 = V4^3` and R6 hexagrams.

Acceptance:

- atlas is data, not proof of external domains;
- orbit quotienting accounts for symmetric hexagrams and duplicate readings.

## Phase 4 — V8 Information Preservation

Status: completed in `formal/SSBX/Foundation/Hierarchy/Operators/V8Info.lean`.

Goal: implement the algebra behind §8 of the foundation note.

Implement:

- `V8 := Fin 8 -> Bool`;
- XOR operation and finite subgroup records;
- linear query evaluation by F2 dot product;
- `isInvariant`, `orbit`, and the main information preservation theorem;
- V4 time subgroup and `{dao, jin}` subgroup;
- parity query `y7 xor y8`;
- theorem that `{dao, jin}` preserves parity;
- theorem/counterexample that full V4 time does not preserve that parity.

Acceptance:

- this phase proves the state-level half of the privileged `{dao, cuoZong}`
  story;
- it does not rename R8 globally or mutate existing VM semantics.

## Phase 5 — Cross-Level Bridge

Status: completed in `formal/SSBX/Foundation/Hierarchy/Operators/V4/V8Bridge.lean`.

Goal: connect the element-level preservation subgroup with the state-level
parity subgroup.

Implement:

- map canonical `V4` into the y7-y8 V8 time subgroup;
- prove `{dao, cuoZong}` maps exactly to `{dao, jin}`;
- state clearly that hexagram reversal `zong` is not an XOR mask in V8 and
  belongs to the permutation/action layer.

Acceptance:

- the two independent arguments in the foundation note point to the same
  subgroup by theorem, not prose alone.

## Phase 6 — V8 Naming and Metadata Audit

Status: completed in `formal/SSBX/Foundation/Hierarchy/Operators/V8Audit.lean`.

Goal: repair the implementation-facing audit items without disturbing proven
R0..R8 structure.

Implement:

- document `o = yang` / `x = yin` where V8/OX strings are introduced;
- reserve structural names for high-symmetry masks;
- separate hexagram atoms from time atoms in compiler-facing records or Lean
  metadata, if such records exist in the current repository;
- add explicit R6 and V4 component accessors for Cell256/R8 views.

Acceptance:

- this is naming/metadata only unless a proof already depends on the accessor;
- no archived cell-carrier or cyclic three-state temporal terminology is
  reintroduced.

## Phase 7 — Compiler/Runtime Track

Goal: mirror the Lean kernel in the compiler/runtime once the Lean surface is
stable.

Status: boundary documented. A repository scan found no Clojure/SCI compiler
source files in the current workspace slice, so the executable compiler track
is not implemented here yet. The Lean-side kernel is now stable enough for that
track to consume.

Implement when the compiler track exists in this repository:

- V4 IR primitive;
- V4 multiplication table;
- normalize pass for V4 action chains;
- derivability checker for V8 linear queries;
- consistency check between Lean atlas/invariant data and runtime tables;
- REPL examples such as `cuo zhi qian` and `derivable?`.

Acceptance:

- no compiler table may redefine V4 independently of the canonical Lean kernel;
- if no compiler/runtime source is present, this remains a documented boundary.

## Verification Policy

For each phase:

- run targeted `lake env lean` or `lake build SSBX.Foundation.Hierarchy.Operators.V4`
  only on touched modules;
- run `git diff --check`;
- guard against archived carrier terminology, cyclic three-state temporal
  claims, old R numbering, and flat exhaustive-table claims;
- do not run full `lake build` until a real integration boundary requires it.
