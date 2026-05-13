# V4 Foundation Roadmap

> Status: active execution roadmap  
> Source of truth: [`docs-next/v4-foundation.md`](../v4-foundation.md)  
> Date: 2026-05-13

This roadmap turns the latest V4 foundation note into implementation phases.
The foundation note remains the doctrine text; this file tracks what must be
made true in Lean and, later, in the compiler/runtime track.

## Implementation Status

| Phase | Status | Primary modules |
|-------|--------|-----------------|
| 1. Mathlib-facing V4 interfaces | Done | `V4/Instances.lean` |
| 2. Preservation proof layer | Done | `V4/PreservationLogic.lean` |
| 3. Atlas and orbit completion | Done | `V4/Atlas.lean`, `V4/OrbitBurnside.lean`, `Wen/Layered/Bridges/Word64.lean` |
| 4. R8 information preservation | Done | `Wen/Layered/Information.lean`, `Wen/Layered/Bridges/V4Time.lean` |
| 5. Cross-level bridge | Done | `Wen/Layered/Bridges/V4Time.lean` |
| 6. R8 naming and metadata audit | Done | `Wen/Layered/Bridges/R8.lean` |
| 7. Compiler/runtime track | Boundary documented | no Clojure/compiler source is present in the current repository slice |
| 8. Layered Wen semantic core | Implemented, targeted checks passing | `Wen/Layered/*` |
| 9. Final module re-layout | Done, hard re-layout | `Wen/Layered`, `Wen/Layered/Runtime`, Layered bridges |
| 10. Generic `Vn/Rn` final interface | Done | `Wen/Layered/VnRn.lean`, `Finite.lean`, `Derivability.lean`, `Runtime/VnRn.lean` |

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

## Phase 8 — Layered Wen Semantic Core

Status: implemented as an incremental refactor.  The new
`formal/SSBX/Foundation/Wen/Layered` core and bridges compile under targeted
checks; the older V8/V4 public modules now carry Phase 8 compatibility anchors.

Goal: add the `wen-formal` / `wen-layered` classical semantics as a clean
layer above the existing R8/V4/Word64 assets, without breaking existing theorem
names or import boundaries during the transition.

The current decision is explicit: **do not directly rewrite the existing
`V4Kernel`, `V8Info`, `V8Derivability`, or `Word64Bridge` modules first**.
Instead, introduce a new layered core, prove it can carry the existing facts,
then let old modules become compatibility facades.

Implement:

- `Wen/Layered/Slot.lean` for finite positions and even split indices;
- `Wen/Layered/BitSpace.lean` for `BitSpace n := Fin n -> Bool`;
- `Wen/Layered/Split.lean` for `outer`, `inner`, and `combine` round trips;
- `Wen/Layered/Flip.lean` for bit flips and outer/inner flips;
- `Wen/Layered/Dao.lean` for `DaoFamily`, `DaoRegion`, observable states,
  and `Boxtimes`;
- `Wen/Layered/Modal.lean` for the classical four-way judgment
  `necessary true / necessary false / contingent / boxtimes`;
- `Wen/Layered/Core.lean` and `Wen/Layered/Rescue.lean` for k-core, boundary,
  collapse irreversibility, and rescue-requires-outer;
- `Wen/Layered/Information.lean` for invariant queries, orbits,
  annihilator-style derivability, and the `{dao, jin}` parity example.

Bridge after the core exists:

- `Wen/Layered/Bridges/R8.lean`: `BitSpace 8` with the current R8/V8 reading;
- `Wen/Layered/Bridges/Word64.lean`: `BitSpace 6` with
  `Word64 = V4 x V4 x V4`;
- `Wen/Layered/Bridges/RootCell256.lean`: `BitSpace 8` with
  `Word64 x V4`;
- `Wen/Layered/Bridges/V4Time.lean`: the y7/y8 time plane, `{dao, jin}`,
  parity preservation, and the full-V4 counterexample.

Quantum backend note:

- reserve no implementation dependency for Hilbert spaces, tensor products,
  Born measurement, or partial trace in this phase;
- quantum remains a future optional backend, not part of the current
  verification target.

Acceptance:

- the layered core proves the classical `wen-formal` obligations without
  using the Klein `V4` name for `F2^4`;
- `truth` and `is_observable` are not fields of a carrier class; they belong
  to a `DaoFamily` / modal model layer;
- existing public theorem names remain available during the transition;
- old modules may import the layered core once bridges are in place, but the
  layered core must not depend on old high-level interpreter modules.

Completed in Phase 8:

- `Slot`, `BitSpace`, `Split`, `Flip`, `Dao`, `Modal`, `Core`, `Rescue`, and
  `Information` form the carrier-neutral classical bit-space core.
- `Bridges/V4`, `Bridges/R8`, `Bridges/Word64`, `Bridges/RootCell256`, and
  `Bridges/V4Time` connect the core to the current V4/R8/Word64 assets.
- `V8Info`, `V8Derivability`, and `V4/V8Bridge` retain existing public names
  and expose explicit Layered compatibility summaries.
- `RootCell256` uses the current `Mode16.viewOfR8` / `Mode16.r8OfView`
  round trip for the existing R8 carrier.

## Phase 9 — Final Module Re-Layout

Status: completed as a hard internal re-layout.

This was not treated as optional cleanup.  The repository now routes the
classical semantic core and runtime mirror through `Wen/Layered`; old V8 and
Word64 bridge entrypoints were deleted rather than kept as shims.

Completed in Phase 9:

- `Wen/Layered/Runtime` adds the BitVec-backed `Cell n` mirror for the full
  classical Layered semantics: bit operations, split/flip, Dao/modal, core,
  rescue, information, and V4 time-plane derivability.
- `Wen/Layered/Bridges/Word64.lean` owns the former Word64/R6 hexagram and
  lexicon bridge: `toHexagram`, `ofHexagram`, `hexagramEquiv`, `wordOfBits`,
  and `wordOfToken`.
- `Wen/Layered/Bridges/R8.lean` owns the R8/OX coordinate audit and R8
  component metadata.
- `Wen/Layered/Bridges/V4Time.lean` owns the former V8 derivability and
  V4-to-time-plane bridge facts.
- Deleted old entrypoints:
  `Operators/V8Info.lean`, `Operators/V8Derivability.lean`,
  `Operators/V8Audit.lean`, `Operators/V4/V8Bridge.lean`, and
  `Wen/V4Kernel/Word64Bridge.lean`.
- `Wen/V4Kernel`, `Hierarchy/RHierarchy`, `Operators/V4`, and the top-level
  `SSBX` umbrella now import the Layered paths.

Handoff audit:

- Adopted: spec/impl separation, `Fin n -> Bool` proof core, `BitVec n`
  runtime cells, first-class `boxtimes`, 4+4 representation, and 6+2 R8
  semantic projection.
- Rejected as obsolete for v3: using `V4` for `F2^4`, pre-v3 Shi/Dao
  remapping, Jian naming, external JS-engine framing, and any archived 192-cell
  or cyclic temporal carrier.

Final acceptance:

- one canonical carrier story: `BitSpace` / R8 / Cell256 as the same finite
  8-bit root, read through explicit bridges;
- one semantic judgment story: `DaoFamily`, observable/boxtimes, modal
  judgment, rescue, invariant derivability;
- no duplicate root ontology between `Wen/Layered`, `V4Kernel`, `V8Info`, and
  `Word64Bridge`;
- no future quantum module is required for the classical core to compile.

## Phase 10 — Generic Vn/Rn Final Interface

Status: completed as the public arbitrary-rank interface over Layered.

The final classical core is now phrased for any finite bit rank:

- `Rn n := BitSpace n` is the canonical proof-level state space.
- `Vn n := BitSpace n` is the canonical XOR translation group acting on
  `Rn n`.
- `Vn n` has Mathlib-facing `CommGroup` and `MulAction (Vn n) (Rn n)`
  instances.
- `Vn 2` is explicitly bridged to the existing Klein-four `V4`; the old `V4`
  name remains reserved for the Klein carrier, not for a four-bit space.
- `BitSpace.card_eq_two_pow` proves `|Rn n| = 2^n`.
- `spanList` gives finite generator closure and its universal property.
- `derivable?` is a generic finite checker for any Boolean evaluator over a
  generated subgroup; `derivableLinear?` specializes it to `linearEval q`.
- `Runtime.Vn/Rn` exposes the packed `BitVec n` mirror with `toSpec/ofSpec`
  round trips and spec-lifted runtime action laws.

## Verification Policy

For each phase:

- run targeted `lake env lean` or `lake build SSBX.Foundation.Hierarchy.Operators.V4`
  only on touched modules;
- run `git diff --check`;
- guard against archived carrier terminology, cyclic three-state temporal
  claims, old R numbering, and flat exhaustive-table claims;
- do not run full `lake build` until a real integration boundary requires it.
