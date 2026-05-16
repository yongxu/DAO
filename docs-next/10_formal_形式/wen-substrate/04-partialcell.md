# 04 — PartialCell substrate

> Wen.Core, the canonical interpreter for the 文 ISA, runs on `PartialCell 8`, not on the total bit vector `R 8`. This is the type-level realisation of chapter 03's operation monism: the carrier is the fixed-point object of the merge operation, the initial state is the maximally undetermined cell (道), and contradiction is operational (不通 = halt). This chapter is the bridge between the mathematical doctrine and the Lean code that runs.

The carrier we want is `PartialCell N := Fin N → Option Bool`. At each position the machine either *commits* (`some b`) or *abstains* (`none`). Programs progressively specify or unspecify positions. The initial state `dao` is the empty assignment — the maximally undetermined cell, the whole N-cube. Contradiction is primitive: when an operation would assert `false` at a position already pinned to `true`, the partial-cell `merge` returns `none` and the machine halts. **不通 = halt is what the substrate is**, not a check the programmer writes.

The shift from `R 8` to `PartialCell 8` is not a refactor of convenience; it is the operational presentation of chapter 03 at the type level. The carrier (`PartialCell 8`) is not chosen — it is forced by the requirement that the state be able to *grow by commitment* rather than be *given by enumeration*. The "one" of the substrate is the merge operation; the "carrier" is its fixed-point object.

---

## Algebra — PartialCell as face-lattice

[`Foundation/R/PartialCell.lean`](../../../formal/SSBX/Foundation/R/PartialCell.lean) builds the algebra in four phases. The phases compose into a partial commutative monoid with full categorical bona fides; each adds one layer of structure.

**Phase A — definition and the `dao` identity.** A `PartialCell N` is a function `Fin N → Option Bool`. The unique cell `dao : PartialCell N := fun _ => none` is the empty assignment. Its support — the set of specified positions — is empty; it selects the entire N-cube. Geometrically, `dao` is the top of the face lattice; algebraically, it is the merge identity. The doctrinal correspondence is exact:

$$\text{dao} \;\longleftrightarrow\; \text{the un-named (无名)} \;\longleftrightarrow\; \Sigma\text{-seed at iteration-level 0.}$$

The `ofFull : R N → PartialCell N` lift expresses every fully-specified bit vector as a partial cell whose support is `Finset.univ`; `toFull?` is the partial inverse that succeeds exactly when the cell is total. Together they realise the 印 / 投 (impress / project) pair at the partial-cell level: 印 takes a total state into the lattice as a 0-face; 投 collapses a 0-face back to a total state.

**Phase B — commutativity, restriction, full extraction.** Two partial cells are *compatible* iff they agree at every shared specified position:

$$\text{compatible}(a, b) \;:\equiv\; \forall i,\ a\,i = \text{none}\ \lor\ b\,i = \text{none}\ \lor\ a\,i = b\,i.$$

The pointwise merge `mergeFn a b := fun i => a i || b i` (first-specified-wins) is unconditionally pointwise-defined; the partial-monoid merge `merge a b : Option (PartialCell N)` returns `some (mergeFn a b)` exactly when `compatible a b` holds, else `none`. Phase B proves `merge_comm` *unconditionally* (the conflict case is symmetric); `mergeFn_comm` holds *conditionally* (when compatibility witnesses agree on shared positions).

`restrict s c := fun i => if i ∈ s then c i else none` is the codim-increasing projection — positions outside the mask `s` are forgotten. Its identities (`restrict_dao = dao`, `restrict_univ c = c`, `restrict_empty c = dao`) verify that `restrict` interpolates between the identity and the projection-to-dao.

**Phase C — bridge to total bit vectors.** The `ofFull / toFull?` pair satisfies a round-trip (`toFull?_ofFull v = some v`), so total programs are a *strict cross-section* of partial-cell programs. Phase C plugs the partial-cell algebra into the existing `Cell256` / `R 8` machinery so legacy programs lift into the partial substrate without losing structure.

**Phase D — the full monoid laws, list fold, and support algebra.** Phase D closes the loop:

- `merge_assoc` (under pairwise compatibility): (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c), proven via unconditional pointwise associativity of `mergeFn_assoc`.
- `mergeAll : List (PartialCell N) → Option (PartialCell N)` — the right-fold of `merge` over a list, with empty list folding to `dao`. Returns `some _` iff the chain is everywhere compatible; `none` if any pair in the cumulative chain fails. This is the **list-level realisation** of the partial commutative monoid.
- `support_mergeFn : support (mergeFn a b) = support a ∪ support b` — supports add by union under merge. This is the engine of the codim filtration that the next subsection exploits.
- `support_restrict : support (restrict s c) = s ∩ support c` — supports drop to the intersection with the mask.

After Phase D the lattice picture is complete. `(PartialCell N, dao, merge)` is a partial commutative monoid; `dao` is the top; `ofFull v` for total `v` are the atoms (codim-N vertices); `restrict s` and `merge` move us up and down the codim filtration in a controlled, decidable way. This is the substrate Wen.Core operates on. Every instruction in the ISA either consults this algebra directly or is forced to respect it.

---

## Interpreter — 5 → 11 primitives, partial-aware control

The canonical interpreter is housed in three files: the ISA in [`Foundation/Wen/Core/Instruction.lean`](../../../formal/SSBX/Foundation/Wen/Core/Instruction.lean), the state in [`Foundation/Wen/Core/State.lean`](../../../formal/SSBX/Foundation/Wen/Core/State.lean), and the small-step semantics in [`Foundation/Wen/Core/Machine.lean`](../../../formal/SSBX/Foundation/Wen/Core/Machine.lean). The ISA carries **11 constructors**, expanded from the doctrinal "five primitives" (the conceptual minimum before tactical decomposition).

Two of the 11 — `merge c` and `restrict s` — are PartialCell-native: they have no analogue in any total-state interpreter, and they are the only two instructions strictly necessary to realise the algebra above at runtime. The remaining nine are partial-aware liftings of the legacy Wen.Core ISA, kept for feature parity and ergonomics.

| # | constructor | effect on `cur : PartialCell 8` | pc update |
|---|---|---|---|
| 1 | `nop` | unchanged | pc + 1 |
| 2 | `merge c` | `cur ⊔ c` or halt if 不通 | pc + 1 |
| 3 | `restrict s` | `cur ↾ s` (forget bits ∉ s) | pc + 1 |
| 4 | `push` | `history := cur :: history` | pc + 1 |
| 5 | `pop` | `cur := head history` (no-op if empty) | pc + 1 |
| 6 | `flipBit i` | flip `cur i` if defined; no-op if `none` | pc + 1 |
| 7 | `writeBit i b` | `cur i := some b` (overwrite) | pc + 1 |
| 8 | `xorMask m` | flip each defined bit `i` where `m i = true` | pc + 1 |
| 9 | `branchBitEq i b t` | unchanged | `t` if `cur i = some b`, else pc + 1 |
| 10 | `jump t` | unchanged | `t` |
| 11 | `halt` | unchanged | unchanged + `halted := true` |

Three semantic adaptations are *forced* by the partial substrate; they have no other coherent extension from the total-state world.

**`flipBit i` is no-op on `none`.** In the legacy total-state interpreter, `flipBit` always toggled the bit at position i. In the canonical interpreter, `none` means *no commitment*; toggling no-commitment is not "commit to the negation of nothing" — there is no negation of `none` in the lattice. The doctrinally aligned choice is: if the bit is defined, flip it; if not, leave it. This preserves the invariant that partial cells encode *commitment*, and operations on uncommitted positions are transparent.

**`branchBitEq i b t` is partial-aware.** The branch fires only on `cur i = some b` — the bit is *explicitly committed* to the queried value. If `cur i = none`, the branch *does not fire* and the machine falls through to pc + 1. This is the only doctrinally coherent reading: the branch asks "is the system *known to be* in state b at bit i?", and "unknown" answers "no". A total-state interpreter never has to make this choice; a partial-state interpreter must. The lemmas `branchBitEq_pc_taken`, `branchBitEq_pc_skip`, and `branchBitEq_pc_unspec` in `Machine.lean` record the three cases.

**`merge c` may halt the machine.** This is the operational realisation of 不通. The execution rule:

```lean
| .merge c =>
    match PartialCell.merge s.cur c with
    | some c' => { s with cur := c', pc := s.pc + 1 }
    | none    => { s with halted := true }
```

If the merge succeeds, the new cell replaces `cur` and execution continues. If the merge fails — meaning `cur` and `c` disagree on a shared committed position — the machine halts. The halt is not exceptional; it is the substrate refusing to admit a contradiction. The programmer never writes a contradiction-check; **the contradiction-check is the substrate**.

The interpreter state `State` carries four fields: `pc : Nat`, `cur : PartialCell 8`, `history : List (PartialCell 8)`, `halted : Bool`. The initial state `State.initial` has `pc = 0`, `cur = PartialCell.dao`, `history = []`, `halted = false`. The doctrinal anchor for the initial state is exact: a Wen.Core program begins in the maximally undetermined state, the entire 8-cube, the 道; instructions progressively *commit* (`merge`, `writeBit`) or *uncommit* (`restrict`) positions. The lifecycle of a Wen.Core run is the lifecycle of a partial assignment through the face lattice.

The bridge `State.init : R 8 → State` lifts a total input into a fully-specified partial cell, preserving compatibility with any legacy Wen.Core program that took an `R 8` argument. Total programs run; partial programs run; mixed programs run. The substrate is uniform.

The five-to-eleven expansion. The doctrine-level five primitives — `dao`, `merge`, `restrict`, `ofFull`, `toFull?` — form the *algebraic* minimum: they generate every partial cell and the partial monoid structure. The interpreter exposes 11 because (i) three control primitives `jump`, `branchBitEq`, `halt` are needed for *programs* (not just cells); (ii) `push` and `pop` give the interpreter a finite stack for snapshot / restore, useful for backtracking-style programs; (iii) `flipBit`, `writeBit`, `xorMask` are expressible via `merge` but are exposed as single instructions because they are frequent and their decompositions are unwieldy. The ISA is conservatively extended, not minimised — feature parity with legacy Wen.Core matters more than minimality for an interpreter that must accept legacy code. The shrinkage from 13+ primitives in some legacy variants to 11 reflects the chapter-03 point: one operation (merge) replaces multiple bespoke primitives, because the partial-cell substrate is more expressive than the total-bit substrate.

---

## Codim filtration — relation to the R-tower

The face lattice of `PartialCell 8` is exactly the codim filtration of the R-tower restricted to base F₂ at N = 8.

| lattice level | `support` size | R-tower character | geometric face |
|---|---|---|---|
| `dao` | 0 | R₀ / 道 | the whole 8-cube (codim 0) |
| codim-2 face | 2 | R₂ character | a 6-face |
| codim-4 face | 4 | R₄ character | a 4-face |
| codim-8 vertex | 8 | R₈ character | a 0-face (a vertex) |

A partial cell with k specified positions selects a face of dimension 8 − k containing 2^{8−k} full R₈ vectors. The R-tower characters at the squaring-tower atoms {R₂, R₄, R₈} are exactly the partial cells whose support has size {2, 4, 8} respectively. The tower {R₀, R₂, R₄, R₈} maps bijectively to the squaring sub-tower of the face lattice.

This collapses the **heterogeneous-mixing problem** that previously required separate machinery for "R₈ + R₄ + R₂ in one string". In the canonical substrate, every character — regardless of which tower level it belongs to — is a `PartialCell 8`; the apparent heterogeneity is just *different support sizes inside one type*. The operation that combines them is the single partial-monoid operation `merge`, which yields three distinct combinator behaviours by support geometry:

- **并列 (parallel, lateral composition)** — when supports are disjoint, `merge` produces the union assignment; both commitments survive.
- **修饰 (modifier-head, vertical composition)** — when one support is contained in the other, `merge` produces the more specified cell; the modifier *refines* the head.
- **不通 (conflict, halt)** — when supports overlap with disagreeing values, `merge` returns `none`; the substrate refuses to admit the combination.

The three cases are not separate algorithms; they are the three outcomes of the *same* operation, differentiated only by mask geometry. This is what chapter 03 means by "operations *are* identifications": the partial cell `merge` is one operation, but it carries the meaning of three combinator forms depending on support overlap. The combinator forms are not primitive; they are *consequences* of the support algebra.

The support algebra is precisely:

- `support_mergeFn : support (mergeFn a b) = support a ∪ support b` — merge adds supports by union.
- `support_restrict : support (restrict s c) = s ∩ support c` — restrict intersects.

These two equations *are* the codim filtration. Together with the lattice top (`dao`, codim 0) and the lattice bottoms (`ofFull v`, codim 8), they fully axiomatise the geometric content of the substrate.

The R-tower's squaring sub-tower {T₀, T₁, T₂, T₃} at base F₂ is the diagonal slice of the codim filtration at support sizes {0, 2, 4, 8}; the partial-cell face lattice fills in the *continuous* picture by also admitting intermediate support sizes (1, 3, 5, 6, 7) that have no direct R-tower analogue but are forced by the lattice structure. The R-tower picks out a privileged sub-lattice; the partial-cell substrate generalises naturally to the full one.

Operationally, the interpreter's `restrict s` instruction *is* the codim-raising operation on the lattice; the `merge c` instruction *is* the codim-lowering operation (or codim-preserving, when `c`'s support is already a subset of `cur`'s support). The two primitive instructions of the partial-cell ISA correspond exactly to the two structural moves of the face lattice. This is the type-level realisation of "the substrate operates by lattice motion alone".

---

## Use case — constraint composition

The doctrinal claim that PartialCell makes constraint composition a *primitive*, not a *programming pattern*, is operationally demonstrated in [`Foundation/Wen/Core/ConstraintDemo.lean`](../../../formal/SSBX/Foundation/Wen/Core/ConstraintDemo.lean). The file is intentionally short (~150 lines) and the demonstrations are sanity-level (each property is checked by `rfl` from a small fuel-bound). The point is not the size of the proof; the point is that the proofs *exist at all*.

In a classical bit-machine — where `cur : R 8` is always fully specified — the question "I commit only to bits 0 and 2; bit 5 is unknown" has no representation. Every step writes a definite value to every position. Contradiction is not a concept the machine recognises; it is a property of *programs* the programmer must check for, typically via a branch-and-halt pattern with an explicitly synthesised contradiction predicate.

In Wen.Core (PartialCell-native), the same situation is direct:

```lean
def agreementProg : List Instr := mergeProg [
  Instr.pinBit ⟨0, _⟩ true,
  Instr.pinBit ⟨2, _⟩ false,
  Instr.pinBit ⟨5, _⟩ true
]
```

Each `merge` adds a partial commitment; `cur` remains partially specified through the entire run. The program halts cleanly when it reaches the trailing `.halt` (theorem `agreementProg_halts`).

The contradiction case is equally direct:

```lean
def conflictProg : List Instr := mergeProg [
  Instr.pinBit ⟨0, _⟩ true,
  Instr.pinBit ⟨3, _⟩ true,
  Instr.pinBit ⟨0, _⟩ false   -- 不通 — already committed to true
]
```

The third statement attempts to commit bit 0 to `false`, but bit 0 is already committed to `true`. The `merge` returns `none`; the machine halts mid-program (theorem `conflictProg_halts`). No branch was written. No contradiction predicate was synthesised. The substrate detected the conflict and halted.

The codim-raising case (forgetting bits):

```lean
def restrictProg : List Instr := [
  .merge (Instr.pinBit ⟨0, _⟩ true),
  .merge (Instr.pinBit ⟨1, _⟩ true),
  .merge (Instr.pinBit ⟨2, _⟩ true),
  .restrict ({⟨0, _⟩, ⟨1, _⟩} : Finset (Fin 8)),
  .halt
]
```

After running, bits 0 and 1 retain their commitments; bit 2 has been *uncommitted* — `cur ⟨2, _⟩ = none`, witnessed by theorem `restrictProg_forgets_bit_2`. The interpreter has moved up the codim filtration mid-program, forgetting a specific commitment. No total-state interpreter can do this without auxiliary tagging machinery; for the partial-state interpreter it is one instruction.

**The algebra-operational bridge.** For a pure-merge program, running the program from `initial` is exactly `PartialCell.mergeAll` of the merge cells, modulo Option-unwrapping. The helper `mergeCells : List Instr → List (PartialCell 8)` extracts the merge cells from a program in order; the interpreter's `runFuel` on a pure-merge program collapses to the algebraic fold. The full proof requires induction on the cell list and case-splitting on merge success / failure; the file marks it as a future exercise but the small-case demonstrations (`#eval`-level `rfl` checks) already confirm it on representative inputs. This correspondence is the operational realisation of Phase D's algebraic fold: the interpreter is not merely *compatible* with the algebra; on pure-merge programs it *is* the algebra. In a total-state world there is no `mergeAll` analogue and the question does not arise.

---

## What the substrate guarantees

Three properties the partial-cell substrate makes *primitive* that the total-cell substrate could only *encode*:

1. **Partial states are first-class.** The interpreter carries under-specified knowledge through computation. This is not simulation by tagging; the state's type *is* partial.
2. **Contradiction is operational.** The substrate enforces non-contradiction at the instruction level. The programmer does not write a check; the substrate is the check.
3. **Forgetting is primitive.** The interpreter can uncommit positions mid-program. Codim-raising is not deletion-then-rewrite; it is `restrict`, a single instruction with a single semantics.

The three together justify the move from `R 8` to `PartialCell 8` as canonical. The total-cell substrate could *encode* each of these, but encoding is exactly what chapter 03 said the substrate should not require: when the carrier is forced by the operation, the operations are *primitive* on the carrier; when the carrier is given and operations are layered on top, every desirable property must be re-derived per program. The partial-cell substrate moves these three properties from "programmer responsibility" to "substrate guarantee".

Wen.Core *is* the operational presentation of chapter 03's doctrine. The doctrine and the type theory agree on what the machine fundamentally does: it walks the face lattice of `PartialCell 8` under the partial-monoid operation `merge`, with `dao` as the doctrinal origin and 不通 as the doctrinal halt. Every instruction in the ISA either consults this lattice or moves through it. Nothing else.

---

## Status

- [`Foundation/R/PartialCell.lean`](../../../formal/SSBX/Foundation/R/PartialCell.lean) carries the full Phases A–D algebra: definition, `dao` / `ofFull` / `toFull?`, `compatible` and `mergeFn` / `merge`, commutativity and (compatibility-conditional) associativity, `restrict`, `mergeAll`, `support_mergeFn` and `support_restrict`.
- [`Foundation/Wen/Core/Instruction.lean`](../../../formal/SSBX/Foundation/Wen/Core/Instruction.lean) defines the 11-constructor ISA; [`State.lean`](../../../formal/SSBX/Foundation/Wen/Core/State.lean) and [`Machine.lean`](../../../formal/SSBX/Foundation/Wen/Core/Machine.lean) carry the partial-aware semantics, including the three forced adaptations (`flipBit` no-op on `none`, partial-aware `branchBitEq`, `merge` halt-on-conflict).
- [`Foundation/Wen/Core/ConstraintDemo.lean`](../../../formal/SSBX/Foundation/Wen/Core/ConstraintDemo.lean) carries the sanity-level demonstrations (`agreementProg_halts`, `conflictProg_halts`, `restrictProg_forgets_bit_2`) showing partial states, operational contradiction, and primitive forgetting at runtime.

## Open / TODO

- The full algebra-operational bridge `mergeAll ↔ runFuel-on-pure-merge` is currently `#eval`-checked on small inputs; the inductive proof over the cell list is marked as a future exercise.
- The interpreter currently lives at N = 8 only. The partial-cell algebra works for any N; lifting Wen.Core to a polymorphic `PartialCell N` interpreter is doctrinally clean but not committed in code.
- The relation between `PartialCell N` and the parametric R-Family-over-k of chapter 02 is via the codim filtration over base F₂; there is no parametric `PartialCell` over arbitrary k (and the doctrine is silent on whether such a generalisation is structurally meaningful or merely a notational variant).
- The dual lift `toFull? ∘ ofFull = id` is unconditional; the lift in the other direction (partial → total via choice of `none`-resolution) is open. There is no canonical "fill the unknowns" operation, by design — that is what makes partial-cells more expressive than tagged totals.
