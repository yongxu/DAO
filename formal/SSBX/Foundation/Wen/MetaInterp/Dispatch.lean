/-
# Dispatch — route from the opcode-tag cell to the appropriate executeBlock

This file implements the current **pre-swap dispatch tree** that fetch invokes
after it has deposited the next instruction's tag cell into `META.cur`.  The
tree covers tags 0..11.  After `YiInstr.swap` was added at tag 12, this file
remains a verified scaffold for the legacy 12-way geometry; the full 13-way
dispatch tree is intentionally deferred with the rest of Phase C.

For Option-F per-parameter blocks (`setShi sh`, `flipYao i`,
`branchYaoEq i j t`, `branchShiEq sh t`), dispatch must also consume the
next param cell(s) from `META.history` and route to the right pre-compiled
sub-block.  We give the **structural** dispatch tree here and document the
sub-dispatch protocol; the per-(op, param) sub-dispatch trees are built
parametrically by `subDispatchSetShi`, `subDispatchFlipYao`, etc.

## §0  Pre-state contract — what fetch is required to leave behind

This dispatch tree is the **callee**.  It assumes the following pre-state
when control is transferred to its entry offset:

| field         | value                                                       |
| ------------- | ----------------------------------------------------------- |
| `META.cur`    | the **tag cell** of the next instruction to execute         |
|               | i.e. `cellFromIdx ⟨k, _⟩` for some `k ∈ {0..11}`            |
|               | (`swap`, tag 12, is outside this scaffold)                  |
| `META.history`| the **param cells** of this instruction, prepended to the   |
|               | rest of the encoded META state (per `MetaInterp.lean §4`).  |
| `META.pc`     | `dispatchOffset`                                            |
| `META.prog`   | the global `metaInterpProg`                                 |
| `META.halted` | `false`                                                     |

This is the **simplest** of the three "fetch contract" candidates discussed
in `ExecuteBlock.lean §A.4`: fetch puts the tag in cur, params at the top
of history.  It minimizes dispatcher state and aligns well with the per-block
contract (which expects `META.cur = sim.cur` on block entry; the very first
instruction of each executeBlock is responsible for restoring `META.cur`
from the tag cell back to `sim.cur`).

Note that this **slightly** weakens the per-block precondition's
`META.cur = sim.cur` invariant *across the dispatch boundary* — dispatch
"borrows" `META.cur` to hold the tag cell, then the executeBlock's first
instruction restores it.  The per-block local-effect lemmas in
`Block_*.lean` already abstract over this restoration step (they take
`cur` as a free variable).

## §1  Dispatch tree shape — legacy 4-way hex × 3-way Shi

The opcode-tag cell is `cellFromIdx ⟨k, _⟩` for `k ∈ {0..11}`.  Per
`WenyanSelfInterp.cellFromIdx`:

  hex_idx = k / 3 ∈ {0, 1, 2, 3}
  shi_idx = k % 3 ∈ {0, 1, 2}     (= ji, jin, wei)

The encoding `Yao.toIdx` is `yang ↦ 0, yin ↦ 1`, so for
`Hexagram.fromIdx ⟨hex_idx, _⟩` with `hex_idx < 16`,
`y3 = y4 = y5 = y6 = Yao.yang` (all upper bits of hex_idx are 0).
Only `y1` and `y2` distinguish the 4 hex indices:

  hex_idx=0 (binary 000000): y1=yang, y2=yang   (used by tags 0, 1, 2)
  hex_idx=1 (binary 000001): y1=yin,  y2=yang   (used by tags 3, 4, 5)
  hex_idx=2 (binary 000010): y1=yang, y2=yin    (used by tags 6, 7, 8)
  hex_idx=3 (binary 000011): y1=yin,  y2=yin    (used by tags 9, 10, 11)

So we dispatch by:
  1. `branchYaoEq 1 5`: is y2 = y6 (=yang)?  if yes → hex ∈ {0, 1}
                                              if no  → hex ∈ {2, 3}
  2. within each branch, `branchYaoEq 0 5`: is y1 = y6 (=yang)?
  3. now hex_idx is known; sub-dispatch on Shi via two `branchShiEq`s.

The pseudo-code:

```
  if y2 = y6  then  /* hex ∈ {0, 1} */
    if y1 = y6  then  /* hex = 0: nop / setShi / flipYao */
      shi-dispatch → nop_offset / setShi_dispatch / flipYao_dispatch
    else              /* hex = 1: hu / cuo / zong */
      shi-dispatch → hu_offset / cuo_offset / zong_offset
  else        /* hex ∈ {2, 3} */
    if y1 = y6  then  /* hex = 2: branchYaoEq / branchShiEq / jump */
      shi-dispatch → branchYaoEq_dispatch / branchShiEq_dispatch / jump_offset
    else              /* hex = 3: push / pop / halt */
      shi-dispatch → push_offset / pop_offset / halt_offset
```

Each shi-dispatch is two `branchShiEq` followed by a fall-through `jump`.

For Option-F sub-dispatch (`setShi`, `flipYao`, `branchYaoEq`, `branchShiEq`):
the sub-dispatch is a separate program fragment that pops the next param
cell from `META.history` into `META.cur`, then 3- or 6-way branches on the
new `META.cur` to route to the right pre-compiled (op, param) block.

## §2  What is provided

  * `DispatchOffsets` — a record of all the entry-offsets, parametric so
    the dispatch tree can be re-located by adjusting offsets.
  * `dispatchHexShi (offsets, hexIdx)` — a per-hex 3-way Shi dispatch
    fragment (3 instructions: 2 `branchShiEq` + 1 `jump`).
  * `dispatchTree (offsets)` — the full top-level 4-way hex × 3-way Shi
    dispatch tree.
  * Length lemma: `dispatchTree_length`.
  * One concrete dispatch case proven end-to-end:
    `dispatchTree_routes_halt` — when `META.cur` is the halt tag cell
    (idx 11, hex_idx = 3, shi = wei), the tree halts at `halt_offset`.

## §3  What is deferred

  * **Sub-dispatch tree construction** for Option-F blocks (setShi 3-way,
    flipYao 6-way, branchYaoEq 36-way × encNat, branchShiEq 3-way × encNat).
    Stubs included; full bodies are Phase D work because the Nat-target
    branches (`branchYaoEq`, `branchShiEq`) require dynamic decode (same
    arithmetic gap as `Block_Jump.lean`).
  * **Routing proofs for the other legacy 11 cases** — same shape as the
    halt case, mostly mechanical; one case is sufficient to certify the
    scaffold architecture.
  * **Tag 12 / `swap` routing** — requires replacing this legacy 4×3
    geometry with a full 13-way tree.
  * **Composition with fetch** — the precise pre-state contract documented
    in §0 must be discharged by `fetchProg` (Phase B follow-up).
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
import SSBX.Foundation.Wen.MetaInterp.Block_HuCuoZong
import SSBX.Foundation.Wen.MetaInterp.Block_SetShi_FlipYao
import SSBX.Foundation.Wen.MetaInterp.Block_Jump
import SSBX.Foundation.Wen.MetaInterp.Block_Branches
import SSBX.Foundation.Wen.MetaInterp.Block_PushPop

namespace SSBX.Foundation.Wen.MetaInterp.Dispatch

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanSelfInterp.YiInstrEnc
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

/-! ## § 1  DispatchOffsets — entry-offset table

Every executeBlock has a unique entry offset in `metaInterpProg`.  The
dispatch tree is parametric over this record so it can be re-instantiated
when the block layout changes.  For Option-F per-(op, param) blocks we
record one offset per (op, param) pair; for `branchYaoEq` and
`branchShiEq` the sub-dispatch into the per-(i, j, t) or per-(sh, t)
blocks is deferred (see §3 above), so the offsets here name the
sub-dispatch entry points only.
-/

/-- Entry-offset table for all executeBlocks (and sub-dispatch entries
    for Option-F opcodes).

    The `_offset` fields are the absolute pc within `metaInterpProg`. -/
structure DispatchOffsets where
  -- 0-arity blocks (direct entries)
  nop_offset : Nat
  hu_offset : Nat
  cuo_offset : Nat
  zong_offset : Nat
  push_offset : Nat
  pop_offset : Nat
  halt_offset : Nat
  -- single-Nat-target block (deferred dispatch on encNat target)
  jump_offset : Nat
  -- Option-F sub-dispatch entries
  setShi_dispatch_offset : Nat       -- routes to setShi_ji / setShi_jin / setShi_wei
  flipYao_dispatch_offset : Nat      -- routes to flipYao_0 .. flipYao_5
  branchYaoEq_dispatch_offset : Nat  -- routes to branchYaoEq_(i,j,t)
  branchShiEq_dispatch_offset : Nat  -- routes to branchShiEq_(sh,t)
  deriving Repr

/-! ## § 2  Per-Shi 3-way dispatch fragment

Each fragment compares `META.cur.2` against `Shi.ji` and `Shi.jin`,
falling through to a target taken to mean `Shi.wei`.

The fragment is:

  [ branchShiEq Shi.ji  jiTarget
  , branchShiEq Shi.jin jinTarget
  , jump weiTarget
  ]

Length = 3 instructions.
-/

/-- A 3-way dispatch on `META.cur.2`. -/
def dispatchShi (jiTarget jinTarget weiTarget : Nat) : List YiInstr :=
  [ YiInstr.branchShiEq Shi.ji  jiTarget
  , YiInstr.branchShiEq Shi.jin jinTarget
  , YiInstr.jump weiTarget
  ]

theorem dispatchShi_length (a b c : Nat) :
    (dispatchShi a b c).length = 3 := rfl

/-! ## § 3  Top-level dispatch tree

Layout (offsets relative to the dispatch tree's own start):

  +0 : branchYaoEq 1 5  L_y2yang   -- if y2 = y6 (=yang) jump to L_y2yang
  +1 : jump L_y2yin                -- else (y2 = yin) fall to L_y2yin

  L_y2yin (+2):  hex ∈ {2, 3}
  +2 : branchYaoEq 0 5  L_hex2     -- if y1 = y6 (=yang) → hex=2; else → hex=3
  +3 : jump L_hex3
  L_hex2 (+4):
  +4 : dispatchShi (branchYaoEq, branchShiEq, jump)        — 3 instr
  L_hex3 (+7):
  +7 : dispatchShi (push, pop, halt)                       — 3 instr

  L_y2yang (+10):  hex ∈ {0, 1}
  +10: branchYaoEq 0 5  L_hex0
  +11: jump L_hex1
  L_hex0 (+12):
  +12: dispatchShi (nop, setShi, flipYao)                  — 3 instr
  L_hex1 (+15):
  +15: dispatchShi (hu, cuo, zong)                         — 3 instr

Total length = 18 instructions.
All `branchYaoEq i j t` and `jump t` targets are absolute pcs in
`metaInterpProg`; we compute them by adding `dispatchBase` to the local
offsets above.
-/

/-- The full top-level dispatch tree.  `dispatchBase` is the absolute pc
    where the tree begins inside `metaInterpProg`. -/
def dispatchTree (offsets : DispatchOffsets) (dispatchBase : Nat) : List YiInstr :=
  let L_y2yin  := dispatchBase + 2
  let L_y2yang := dispatchBase + 10
  let L_hex2   := dispatchBase + 4
  let L_hex3   := dispatchBase + 7
  let L_hex0   := dispatchBase + 12
  let L_hex1   := dispatchBase + 15
  -- y2-test (compare y_2 to y_6 = known yang for legacy tags 0..11)
  [ YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩ L_y2yang
  , YiInstr.jump L_y2yin ]
  ++
  -- L_y2yin (+2): y2 was yin → hex ∈ {2, 3}
  [ YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩ L_hex2
  , YiInstr.jump L_hex3 ]
  ++
  -- L_hex2 (+4): dispatch shi within hex=2 → branchYaoEq / branchShiEq / jump
  dispatchShi offsets.branchYaoEq_dispatch_offset
              offsets.branchShiEq_dispatch_offset
              offsets.jump_offset
  ++
  -- L_hex3 (+7): dispatch shi within hex=3 → push / pop / halt
  dispatchShi offsets.push_offset
              offsets.pop_offset
              offsets.halt_offset
  ++
  -- L_y2yang (+10): y2 was yang → hex ∈ {0, 1}
  [ YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩ L_hex0
  , YiInstr.jump L_hex1 ]
  ++
  -- L_hex0 (+12): dispatch shi within hex=0 → nop / setShi / flipYao
  dispatchShi offsets.nop_offset
              offsets.setShi_dispatch_offset
              offsets.flipYao_dispatch_offset
  ++
  -- L_hex1 (+15): dispatch shi within hex=1 → hu / cuo / zong
  dispatchShi offsets.hu_offset
              offsets.cuo_offset
              offsets.zong_offset

/-- The dispatch tree is exactly 18 instructions long. -/
theorem dispatchTree_length (offsets : DispatchOffsets) (dispatchBase : Nat) :
    (dispatchTree offsets dispatchBase).length = 18 := by
  unfold dispatchTree
  simp [dispatchShi]

/-! ## § 4  Sub-dispatch stubs for Option-F blocks

These are the hooks that the top-level `dispatchTree` jumps to for the
parameterized opcodes.  Each sub-dispatch is responsible for popping the
next param cell from `META.history` (which fetch left at the top, see §0)
into `META.cur`, then performing a small N-way dispatch.

We provide the `setShi` and `flipYao` sub-dispatch trees here.  The
`branchYaoEq` and `branchShiEq` sub-dispatchers additionally need to read
the encNat-encoded target, which requires the dynamic Nat-decode subroutine
that has not yet been built (same arithmetic gap as `Block_Jump.lean`).
-/

/-- The setShi sub-dispatch table.  Routes to one of three pre-compiled
    `executeBlock_setShi sh ...` blocks based on the param cell's `Shi`.

    Layout (relative to the sub-dispatch base):

      +0 : pop                          — pop param cell into META.cur
      +1 : branchShiEq Shi.ji  jiOff
      +2 : branchShiEq Shi.jin jinOff
      +3 : jump weiOff

    Length = 4 instructions. -/
def subDispatchSetShi (jiOff jinOff weiOff : Nat) : List YiInstr :=
  YiInstr.pop :: dispatchShi jiOff jinOff weiOff

theorem subDispatchSetShi_length (a b c : Nat) :
    (subDispatchSetShi a b c).length = 4 := by
  unfold subDispatchSetShi
  simp [dispatchShi]

/-- Encoding fact: the Shi-component of `encShi sh` is `sh` itself.  Used
    to discharge the routing proof for `subDispatchSetShi`. -/
private theorem encShi_shi (sh : Shi) : (encShi sh).2 = sh := by
  cases sh <;> rfl

/-- **Routing lemma for `subDispatchSetShi`**: starting from a META state
    whose `cur` is anything (typically the setShi tag cell), `pc = 0`,
    `prog = subDispatchSetShi jiOff jinOff weiOff`, and `history` begins
    with `encShi sh` followed by `rest`, after the appropriate number of
    fuel steps (2 for `ji`, 3 for `jin`, 4 for `wei`) META lands at the
    correct branch offset, with `cur = encShi sh`, `history = rest`, and
    `halted = false`.

    The fuel count varies by case because `branchShiEq` short-circuits as
    soon as it matches; `wei` falls through both `branchShiEq`s before the
    final `jump` fires. -/
theorem subDispatchSetShi_routes
    (sh : Shi) (jiOff jinOff weiOff : Nat)
    (cur : Cell192) (rest : List Cell192) :
    let μ : YiState :=
      { cur := cur
        history := encShi sh :: rest
        pc := 0
        prog := subDispatchSetShi jiOff jinOff weiOff
        halted := false }
    let fuel : Nat := match sh with | .ji => 2 | .jin => 3 | .wei => 4
    let μ' := μ.runFuel fuel
    let target : Nat := match sh with
      | .ji => jiOff | .jin => jinOff | .wei => weiOff
    μ'.pc = target
    ∧ μ'.cur = encShi sh
    ∧ μ'.history = rest
    ∧ μ'.halted = false := by
  -- Step 0 (pop): cur := encShi sh, history := rest, pc := 1.
  -- Step 1 (branchShiEq ji jiOff): test (encShi sh).2 = ji.
  -- Step 2 (branchShiEq jin jinOff): test (encShi sh).2 = jin.
  -- Step 3 (jump weiOff): unconditional.
  cases sh <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute,
            subDispatchSetShi, dispatchShi, encShi_shi]

/-! ### § 4.1  flipYao 6-way sub-dispatch -/

/-- The flipYao sub-dispatch table.  Routes to one of six pre-compiled
    `executeBlock_flipYao i ...` blocks based on the param cell's index
    `i ∈ Fin 6`.

    The param cell is `encFin6 i = cellFromIdx ⟨i.val, _⟩`, with
    `i.val ∈ {0..5}`.  Decomposing via `cellFromIdx`:

      hex_idx = i.val / 3 ∈ {0, 1}     (0 for i ∈ {0,1,2}, 1 for i ∈ {3,4,5})
      shi_idx = i.val % 3 ∈ {0, 1, 2}  (0=ji, 1=jin, 2=wei)

    `Hexagram.fromIdx ⟨0, _⟩` = all yang; `fromIdx ⟨1, _⟩` = y1=yin,
    y2..y6=yang.  So we can decide hex_idx by comparing `y1` and `y6`:
    they are equal (both yang) for hex_idx = 0, unequal for hex_idx = 1.

    Layout (offsets relative to the dispatch base):

      +0 : pop                                     — pop param cell into cur
      +1 : branchYaoEq 0 5  (base + 3)             — y1 = y6 → hex 0
      +2 : jump (base + 6)                         — else hex 1
      +3 : branchShiEq Shi.ji  off0                — hex 0 / ji
      +4 : branchShiEq Shi.jin off1                — hex 0 / jin
      +5 : jump off2                               — hex 0 / wei
      +6 : branchShiEq Shi.ji  off3                — hex 1 / ji
      +7 : branchShiEq Shi.jin off4                — hex 1 / jin
      +8 : jump off5                               — hex 1 / wei

    Length = 9 instructions.

    `dispatchBase` is the absolute pc where this sub-dispatch starts inside
    `metaInterpProg`; the two intra-fragment branch targets above
    (`base + 3`, `base + 6`) need it. -/
def subDispatchFlipYao (dispatchBase : Nat)
    (off0 off1 off2 off3 off4 off5 : Nat) : List YiInstr :=
  [ YiInstr.pop
  , YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩ (dispatchBase + 3)
  , YiInstr.jump (dispatchBase + 6)
  , YiInstr.branchShiEq Shi.ji  off0
  , YiInstr.branchShiEq Shi.jin off1
  , YiInstr.jump off2
  , YiInstr.branchShiEq Shi.ji  off3
  , YiInstr.branchShiEq Shi.jin off4
  , YiInstr.jump off5 ]

theorem subDispatchFlipYao_length (base a b c d e f : Nat) :
    (subDispatchFlipYao base a b c d e f).length = 9 := rfl

/-- **Routing lemma for `subDispatchFlipYao`**: starting from a META state
    whose `cur` is anything (typically the flipYao tag), `pc = 0`,
    `prog = subDispatchFlipYao 0 off0 off1 off2 off3 off4 off5`, and
    `history` begins with `encFin6 i` followed by `rest`, after the
    appropriate number of fuel steps META lands at the correct
    `off_{i.val}`, with `cur = encFin6 i`, `history = rest`, and
    `halted = false`.

    Fuel counts (per i):
      i=0 (hex0/ji):  3   pop, branchYao take, branchShi ji take
      i=1 (hex0/jin): 4   pop, branchYao take, branchShi ji fall, branchShi jin take
      i=2 (hex0/wei): 5   pop, branchYao take, ji fall, jin fall, jump
      i=3 (hex1/ji):  4   pop, branchYao fall, jump, branchShi ji take
      i=4 (hex1/jin): 5   pop, branchYao fall, jump, ji fall, branchShi jin take
      i=5 (hex1/wei): 6   pop, branchYao fall, jump, ji fall, jin fall, jump

    `dispatchBase` is fixed to 0 here so the intra-fragment targets
    (`base+3`, `base+6`) point to instructions 3 and 6 of the fragment
    itself when the fragment is run as a stand-alone program.

    Proof strategy: each of the six cases unfolds `encFin6` and its
    `cellFromIdx` decomposition all the way down to `Yao.fromIdx` /
    `Shi.fromIdx` literals; from there `simp` normalizes the
    `branchYaoEq` / `branchShiEq` conditions and the routing falls out
    by pure reduction. -/
theorem subDispatchFlipYao_routes
    (i : Fin 6) (off0 off1 off2 off3 off4 off5 : Nat)
    (cur : Cell192) (rest : List Cell192) :
    let μ : YiState :=
      { cur := cur
        history := encFin6 i :: rest
        pc := 0
        prog := subDispatchFlipYao 0 off0 off1 off2 off3 off4 off5
        halted := false }
    let fuel : Nat := match i.val with
      | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 4 | 4 => 5 | _ => 6
    let μ' := μ.runFuel fuel
    let target : Nat := match i.val with
      | 0 => off0 | 1 => off1 | 2 => off2 | 3 => off3 | 4 => off4 | _ => off5
    μ'.pc = target
    ∧ μ'.cur = encFin6 i
    ∧ μ'.history = rest
    ∧ μ'.halted = false := by
  match i with
  | ⟨0, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute,
            subDispatchFlipYao, Hexagram.yaoAt,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx, Shi.fromIdx]
  | ⟨1, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute,
            subDispatchFlipYao, Hexagram.yaoAt,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx, Shi.fromIdx]
  | ⟨2, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute,
            subDispatchFlipYao, Hexagram.yaoAt,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx, Shi.fromIdx]
  | ⟨3, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute,
            subDispatchFlipYao, Hexagram.yaoAt,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx, Shi.fromIdx]
  | ⟨4, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute,
            subDispatchFlipYao, Hexagram.yaoAt,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx, Shi.fromIdx]
  | ⟨5, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute,
            subDispatchFlipYao, Hexagram.yaoAt,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx, Shi.fromIdx]

/-! ## § 5  Concrete routing proof — the `halt` case

This proves that when `META.cur` is the halt tag cell
(`cellFromIdx ⟨11, _⟩`), running the dispatch tree from a fresh state
that uses `dispatchTree` as its program lands at `halt_offset` (the
absolute address of the `executeBlock_halt` entry).

The halt tag has `hex_idx = 11/3 = 3` and `shi = Shi.fromIdx (11%3) = wei`.
With `Yao.toIdx (yang) = 0, Yao.toIdx (yin) = 1`, hex_idx = 3 = 0b000011
gives y1 = yin, y2 = yin, y3..y6 = yang.  So the dispatch path is:
  +0 : branchYaoEq 1 5  L_y2yang   — y2 = yin, y6 = yang → not equal → fall through
  +1 : jump L_y2yin                — pc := dispatchBase + 2
  +2 : branchYaoEq 0 5  L_hex2     — y1 = yin, y6 = yang → not equal → fall through
  +3 : jump L_hex3                 — pc := dispatchBase + 7
  +7 : branchShiEq Shi.ji  push    — Shi = wei ≠ ji → fall through
  +8 : branchShiEq Shi.jin pop     — Shi = wei ≠ jin → fall through
  +9 : jump halt_offset            — fires; META.pc := halt_offset

Total fuel used: 7 META steps (one per pc movement above).
-/

/-- The halt tag cell. -/
def haltTag : Cell192 := cellFromIdx ⟨11, by omega⟩

/-- The hex-component of the halt tag has y1 = yin, y2 = yin (since
    hex_idx = 11/3 = 3 = 0b11), and y3..y6 = yang (upper bits of 3 are 0).
    Recall `Yao.toIdx`: `yang ↦ 0, yin ↦ 1`. -/
private theorem haltTag_yao : haltTag.1.y1 = Yao.yin
                            ∧ haltTag.1.y2 = Yao.yin
                            ∧ haltTag.1.y3 = Yao.yang
                            ∧ haltTag.1.y4 = Yao.yang
                            ∧ haltTag.1.y5 = Yao.yang
                            ∧ haltTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The shi-component of the halt tag is `Shi.wei`. -/
private theorem haltTag_shi : haltTag.2 = Shi.wei := by
  unfold haltTag cellFromIdx
  rfl

/-- **Routing lemma for `halt`**: starting from a META state whose
    `cur = haltTag`, `pc = dispatchBase`, and `prog = dispatchTree`,
    after 6 fuel steps META lands at `pc = halt_offset`, with `cur`
    still the halt tag and history untouched.

    This certifies that the top-level dispatch tree correctly routes the
    halt tag to the halt block's entry. -/
theorem dispatchTree_routes_halt
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := haltTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 7
    μ'.pc = offsets.halt_offset
    ∧ μ'.cur = haltTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  -- Drive the proof by direct reduction.  At each step:
  --   step +0: branchYaoEq 1 5 L_y2yin
  --     condition: haltTag.1.yaoAt 1 = haltTag.1.yaoAt 5
  --              = y2 = y6 = yang = yin = false
  --     so pc := 0+1 = 1
  --   step +1: jump (dispatchBase + 2 = 2)
  --   step +2: branchYaoEq 0 5 L_hex2
  --     condition: y1 = y6 = yang = yin = false
  --     so pc := 3
  --   step +3: jump (dispatchBase + 7 = 7)
  --   step +7: branchShiEq Shi.ji push_offset
  --     condition: haltTag.2 = wei ≠ ji = false
  --     so pc := 8
  --   step +8: branchShiEq Shi.jin pop_offset
  --     condition: wei ≠ jin = false
  --     so pc := 9
  --   step +9: jump halt_offset
  --     pc := halt_offset
  -- Total: 6 META steps to reach halt_offset.
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, haltTag_shi,
          Hexagram.yaoAt, haltTag_yao.1, haltTag_yao.2.1, haltTag_yao.2.2.2.2.2]

/-! ## § 5b  Routing proofs for the remaining 11 opcodes

The following 11 theorems are mechanical analogues of
`dispatchTree_routes_halt`, one per non-halt opcode tag.  Each follows the
same template:
  * a `<op>Tag` cell (= `cellFromIdx ⟨k, _⟩` for the right `k`)
  * a `<op>Tag_yao` lemma enumerating (y1..y6) for that hex_idx
  * a `<op>Tag_shi` lemma giving the Shi component
  * a `dispatchTree_routes_<op>` lemma stating `runFuel n` lands at the
    correct entry-offset, with `cur`, `history`, `halted` preserved.
The fuel `n` ranges from 3 to 6 (vs. 7 for halt) depending on path length.
-/

/-! ### nop  (k=0, hex_idx=0, shi=ji) -/

def nopTag : Cell192 := cellFromIdx ⟨0, by omega⟩

private theorem nopTag_yao : nopTag.1.y1 = Yao.yang
                           ∧ nopTag.1.y2 = Yao.yang
                           ∧ nopTag.1.y3 = Yao.yang
                           ∧ nopTag.1.y4 = Yao.yang
                           ∧ nopTag.1.y5 = Yao.yang
                           ∧ nopTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem nopTag_shi : nopTag.2 = Shi.ji := by
  unfold nopTag cellFromIdx
  rfl

theorem dispatchTree_routes_nop
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := nopTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = offsets.nop_offset
    ∧ μ'.cur = nopTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, nopTag_shi,
          Hexagram.yaoAt, nopTag_yao.1, nopTag_yao.2.1, nopTag_yao.2.2.2.2.2]

/-! ### setShi  (k=1, hex_idx=0, shi=jin) -/

def setShiTag : Cell192 := cellFromIdx ⟨1, by omega⟩

private theorem setShiTag_yao : setShiTag.1.y1 = Yao.yang
                              ∧ setShiTag.1.y2 = Yao.yang
                              ∧ setShiTag.1.y3 = Yao.yang
                              ∧ setShiTag.1.y4 = Yao.yang
                              ∧ setShiTag.1.y5 = Yao.yang
                              ∧ setShiTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem setShiTag_shi : setShiTag.2 = Shi.jin := by
  unfold setShiTag cellFromIdx
  rfl

theorem dispatchTree_routes_setShi
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := setShiTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.setShi_dispatch_offset
    ∧ μ'.cur = setShiTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, setShiTag_shi,
          Hexagram.yaoAt, setShiTag_yao.1, setShiTag_yao.2.1,
          setShiTag_yao.2.2.2.2.2]

/-! ### flipYao  (k=2, hex_idx=0, shi=wei) -/

def flipYaoTag : Cell192 := cellFromIdx ⟨2, by omega⟩

private theorem flipYaoTag_yao : flipYaoTag.1.y1 = Yao.yang
                               ∧ flipYaoTag.1.y2 = Yao.yang
                               ∧ flipYaoTag.1.y3 = Yao.yang
                               ∧ flipYaoTag.1.y4 = Yao.yang
                               ∧ flipYaoTag.1.y5 = Yao.yang
                               ∧ flipYaoTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem flipYaoTag_shi : flipYaoTag.2 = Shi.wei := by
  unfold flipYaoTag cellFromIdx
  rfl

theorem dispatchTree_routes_flipYao
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := flipYaoTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.flipYao_dispatch_offset
    ∧ μ'.cur = flipYaoTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, flipYaoTag_shi,
          Hexagram.yaoAt, flipYaoTag_yao.1, flipYaoTag_yao.2.1,
          flipYaoTag_yao.2.2.2.2.2]

/-! ### hu  (k=3, hex_idx=1, shi=ji) -/

def huTag : Cell192 := cellFromIdx ⟨3, by omega⟩

private theorem huTag_yao : huTag.1.y1 = Yao.yin
                          ∧ huTag.1.y2 = Yao.yang
                          ∧ huTag.1.y3 = Yao.yang
                          ∧ huTag.1.y4 = Yao.yang
                          ∧ huTag.1.y5 = Yao.yang
                          ∧ huTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem huTag_shi : huTag.2 = Shi.ji := by
  unfold huTag cellFromIdx
  rfl

theorem dispatchTree_routes_hu
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := huTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.hu_offset
    ∧ μ'.cur = huTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, huTag_shi,
          Hexagram.yaoAt, huTag_yao.1, huTag_yao.2.1, huTag_yao.2.2.2.2.2]

/-! ### cuo  (k=4, hex_idx=1, shi=jin) -/

def cuoTag : Cell192 := cellFromIdx ⟨4, by omega⟩

private theorem cuoTag_yao : cuoTag.1.y1 = Yao.yin
                           ∧ cuoTag.1.y2 = Yao.yang
                           ∧ cuoTag.1.y3 = Yao.yang
                           ∧ cuoTag.1.y4 = Yao.yang
                           ∧ cuoTag.1.y5 = Yao.yang
                           ∧ cuoTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem cuoTag_shi : cuoTag.2 = Shi.jin := by
  unfold cuoTag cellFromIdx
  rfl

theorem dispatchTree_routes_cuo
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := cuoTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.cuo_offset
    ∧ μ'.cur = cuoTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, cuoTag_shi,
          Hexagram.yaoAt, cuoTag_yao.1, cuoTag_yao.2.1, cuoTag_yao.2.2.2.2.2]

/-! ### zong  (k=5, hex_idx=1, shi=wei) -/

def zongTag : Cell192 := cellFromIdx ⟨5, by omega⟩

private theorem zongTag_yao : zongTag.1.y1 = Yao.yin
                            ∧ zongTag.1.y2 = Yao.yang
                            ∧ zongTag.1.y3 = Yao.yang
                            ∧ zongTag.1.y4 = Yao.yang
                            ∧ zongTag.1.y5 = Yao.yang
                            ∧ zongTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem zongTag_shi : zongTag.2 = Shi.wei := by
  unfold zongTag cellFromIdx
  rfl

theorem dispatchTree_routes_zong
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := zongTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.zong_offset
    ∧ μ'.cur = zongTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, zongTag_shi,
          Hexagram.yaoAt, zongTag_yao.1, zongTag_yao.2.1, zongTag_yao.2.2.2.2.2]

/-! ### branchYaoEq  (k=6, hex_idx=2, shi=ji) -/

def branchYaoEqTag : Cell192 := cellFromIdx ⟨6, by omega⟩

private theorem branchYaoEqTag_yao : branchYaoEqTag.1.y1 = Yao.yang
                                   ∧ branchYaoEqTag.1.y2 = Yao.yin
                                   ∧ branchYaoEqTag.1.y3 = Yao.yang
                                   ∧ branchYaoEqTag.1.y4 = Yao.yang
                                   ∧ branchYaoEqTag.1.y5 = Yao.yang
                                   ∧ branchYaoEqTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem branchYaoEqTag_shi : branchYaoEqTag.2 = Shi.ji := by
  unfold branchYaoEqTag cellFromIdx
  rfl

theorem dispatchTree_routes_branchYaoEq
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := branchYaoEqTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.branchYaoEq_dispatch_offset
    ∧ μ'.cur = branchYaoEqTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, branchYaoEqTag_shi,
          Hexagram.yaoAt, branchYaoEqTag_yao.1, branchYaoEqTag_yao.2.1,
          branchYaoEqTag_yao.2.2.2.2.2]

/-! ### branchShiEq  (k=7, hex_idx=2, shi=jin) -/

def branchShiEqTag : Cell192 := cellFromIdx ⟨7, by omega⟩

private theorem branchShiEqTag_yao : branchShiEqTag.1.y1 = Yao.yang
                                   ∧ branchShiEqTag.1.y2 = Yao.yin
                                   ∧ branchShiEqTag.1.y3 = Yao.yang
                                   ∧ branchShiEqTag.1.y4 = Yao.yang
                                   ∧ branchShiEqTag.1.y5 = Yao.yang
                                   ∧ branchShiEqTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem branchShiEqTag_shi : branchShiEqTag.2 = Shi.jin := by
  unfold branchShiEqTag cellFromIdx
  rfl

theorem dispatchTree_routes_branchShiEq
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := branchShiEqTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.branchShiEq_dispatch_offset
    ∧ μ'.cur = branchShiEqTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, branchShiEqTag_shi,
          Hexagram.yaoAt, branchShiEqTag_yao.1, branchShiEqTag_yao.2.1,
          branchShiEqTag_yao.2.2.2.2.2]

/-! ### jump  (k=8, hex_idx=2, shi=wei) -/

def jumpTag : Cell192 := cellFromIdx ⟨8, by omega⟩

private theorem jumpTag_yao : jumpTag.1.y1 = Yao.yang
                            ∧ jumpTag.1.y2 = Yao.yin
                            ∧ jumpTag.1.y3 = Yao.yang
                            ∧ jumpTag.1.y4 = Yao.yang
                            ∧ jumpTag.1.y5 = Yao.yang
                            ∧ jumpTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem jumpTag_shi : jumpTag.2 = Shi.wei := by
  unfold jumpTag cellFromIdx
  rfl

theorem dispatchTree_routes_jump
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := jumpTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.jump_offset
    ∧ μ'.cur = jumpTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, jumpTag_shi,
          Hexagram.yaoAt, jumpTag_yao.1, jumpTag_yao.2.1, jumpTag_yao.2.2.2.2.2]

/-! ### push  (k=9, hex_idx=3, shi=ji) -/

def pushTag : Cell192 := cellFromIdx ⟨9, by omega⟩

private theorem pushTag_yao : pushTag.1.y1 = Yao.yin
                            ∧ pushTag.1.y2 = Yao.yin
                            ∧ pushTag.1.y3 = Yao.yang
                            ∧ pushTag.1.y4 = Yao.yang
                            ∧ pushTag.1.y5 = Yao.yang
                            ∧ pushTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem pushTag_shi : pushTag.2 = Shi.ji := by
  unfold pushTag cellFromIdx
  rfl

theorem dispatchTree_routes_push
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := pushTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.push_offset
    ∧ μ'.cur = pushTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, pushTag_shi,
          Hexagram.yaoAt, pushTag_yao.1, pushTag_yao.2.1, pushTag_yao.2.2.2.2.2]

/-! ### pop  (k=10, hex_idx=3, shi=jin) -/

def popTag : Cell192 := cellFromIdx ⟨10, by omega⟩

private theorem popTag_yao : popTag.1.y1 = Yao.yin
                           ∧ popTag.1.y2 = Yao.yin
                           ∧ popTag.1.y3 = Yao.yang
                           ∧ popTag.1.y4 = Yao.yang
                           ∧ popTag.1.y5 = Yao.yang
                           ∧ popTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem popTag_shi : popTag.2 = Shi.jin := by
  unfold popTag cellFromIdx
  rfl

theorem dispatchTree_routes_pop
    (offsets : DispatchOffsets) (history : List Cell192) :
    let μ : YiState :=
      { cur := popTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.pop_offset
    ∧ μ'.cur = popTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          dispatchTree, dispatchShi, popTag_shi,
          Hexagram.yaoAt, popTag_yao.1, popTag_yao.2.1, popTag_yao.2.2.2.2.2]

/-! ## § 6  Routing-proof template for the other 11 cases

The other 11 routing proofs follow the same shape as
`dispatchTree_routes_halt`:

  1. State the tag cell (e.g. `nopTag : Cell192 := cellFromIdx ⟨0, _⟩`).
  2. Establish the (y1, y2, shi) facts about the tag.
  3. Compute the fuel needed (depends on tree path: 4..6 META steps).
  4. Discharge with `simp [YiState.runFuel, YiState.step, ..., tag-facts]`
     analogous to the halt proof.

For Option-F sub-dispatch (`setShi`, `flipYao`, `branchYaoEq`,
`branchShiEq`), the routing also has to walk through the sub-dispatch
fragment (4 additional META steps for `setShi`, more for the deferred
`flipYao` 6-way tree).  These are mechanical extensions deferred to the
follow-up.

The single proven case here certifies the **architecture** — top-level
4-way × 3-way dispatch correctly addresses all 12 entry points — and
provides a runnable template for the remaining 11.
-/

end SSBX.Foundation.Wen.MetaInterp.Dispatch
