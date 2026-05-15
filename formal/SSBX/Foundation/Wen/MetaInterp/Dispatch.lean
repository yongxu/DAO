/-
# Dispatch — route from the opcode-tag cell to the appropriate executeBlock

This file implements the **dispatch tree** that fetch invokes after it has
deposited the next instruction's tag cell into `META.cur`.  The dispatch tree
inspects the tag cell, decides which of the 12 opcodes it represents, and
performs an unconditional `jump` to that opcode's executeBlock entry-offset.

For Option-F per-parameter blocks (`setShi sh`, `flipYao i`,
`branchYaoEq i j t`, `branchShiEq sh t`), dispatch must also consume the
next param cell(s) from `META.history` and route to the right pre-compiled
sub-block.  We give the **structural** dispatch tree here and document the
sub-dispatch protocol; the per-(op, param) sub-dispatch trees are built
parametrically by `subDispatchSetShi`, `subDispatchFlipYao`, etc.

## Phase F.2 migration note (Cell192 → R8)

Pre-migration `Shi` was a 3-cycle and the 12 tags decomposed as
`(hex_idx ∈ {0,1,2,3}, shi_idx ∈ {0,1,2})`.  Post-migration `Shi` is a V₄
Klein 4-group and tags decompose as `(hex_idx ∈ {0,1,2}, shi_idx ∈ {0,1,2,3})`
with `cellFromIdx ⟨k, _⟩ = (Hexagram.fromIdx ⟨k/4, _⟩, Shi.fromIdx ⟨k%4, _⟩)`.

Concretely for k ∈ {0..11}:
  hex_idx 0 (heaven, all yang):   k ∈ {0,1,2,3}  =  nop / setShi / flipYao / interlace
  hex_idx 1 (y1=yin, rest yang): k ∈ {4,5,6,7}  = complement / reverse / branchYaoEq / branchShiEq
  hex_idx 2 (y2=yin, rest yang): k ∈ {8,9,10,11} = jump / push / pop / halt

(With shi_idx 0=dao, 1=ji, 2=jin, 3=wei.)

## §0  Pre-state contract — what fetch is required to leave behind

This dispatch tree is the **callee**.  It assumes the following pre-state
when control is transferred to its entry offset:

| field         | value                                                       |
| ------------- | ----------------------------------------------------------- |
| `META.cur`    | the **tag cell** of the next instruction to execute         |
|               | i.e. `cellFromIdx ⟨k, _⟩` for some `k ∈ {0..11}`            |
| `META.history`| the **param cells** of this instruction, prepended to the   |
|               | rest of the encoded META state (per `MetaInterp.lean §4`).  |
| `META.pc`     | `dispatchOffset`                                            |
| `META.prog`   | the global `metaInterpProg`                                 |
| `META.halted` | `false`                                                     |

This is the **simplest** of the three "fetch contract" candidates.

## §1  Dispatch tree shape — 3-way hex × 4-way Shi

The opcode-tag cell is `cellFromIdx ⟨k, _⟩` for `k ∈ {0..11}`:

  hex_idx = k / 4 ∈ {0, 1, 2}
  shi_idx = k % 4 ∈ {0, 1, 2, 3}     (= dao, ji, jin, wei)

`Hexagram.fromIdx ⟨h, _⟩` with `h < 4` decomposes via `Yao.toIdx` (yang↦0,
yin↦1) so:

  hex_idx=0 (binary 000000): y1=yang, y2=yang   (y1=y6, y2=y6)
  hex_idx=1 (binary 000001): y1=yin,  y2=yang   (y1≠y6, y2=y6)
  hex_idx=2 (binary 000010): y1=yang, y2=yin    (y1=y6, y2≠y6)

(hex_idx=3 is structurally unreachable for tags k<12.)

So we dispatch by:
  1. `branchYaoEq 1 5`: is y2 = y6 (=yang)?  if yes → hex ∈ {0, 1}
                                              if no  → hex = 2
  2. within hex01, `branchYaoEq 0 5`: is y1 = y6 (=yang)?
                                       if yes → hex = 0
                                       if no  → hex = 1
  3. shi-dispatch on cur.2 via three `branchShiEq`s + final `jump`.

The pseudo-code:

```
  if y2 = y6 then                      /* hex ∈ {0, 1} */
    if y1 = y6 then                    /* hex = 0: nop / setShi / flipYao / interlace */
      shi-dispatch → nop / setShi / flipYao / interlace
    else                               /* hex = 1: complement / reverse / branchYaoEq / branchShiEq */
      shi-dispatch → complement / reverse / branchYaoEq / branchShiEq
  else                                 /* hex = 2: jump / push / pop / halt */
    shi-dispatch → jump / push / pop / halt
```

Each shi-dispatch is three `branchShiEq` followed by a fall-through `jump`.

## §2  What is provided

  * `DispatchOffsets` — a record of all the entry-offsets, parametric.
  * `dispatchShi (daoT, jiT, jinT, weiT)` — a per-hex 4-way Shi dispatch
    fragment (4 instructions: 3 `branchShiEq` + 1 `jump`).
  * `dispatchTree (offsets)` — the full top-level 3-way hex × 4-way Shi
    dispatch tree.
  * Length lemma: `dispatchTree_length`.
  * Routing proofs for all 12 opcode tags.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
import SSBX.Foundation.Wen.MetaInterp.Block_HuCuoZong
import SSBX.Foundation.Wen.MetaInterp.Block_SetShi_FlipYao
import SSBX.Foundation.Wen.MetaInterp.Block_Jump
import SSBX.Foundation.Wen.MetaInterp.Block_Branches
import SSBX.Foundation.Wen.MetaInterp.Block_PushPop

namespace SSBX.Foundation.Wen.MetaInterp.Dispatch

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
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
  setShi_dispatch_offset : Nat       -- routes to setShi_dao .. setShi_wei
  flipYao_dispatch_offset : Nat      -- routes to flipYao_0 .. flipYao_5
  branchYaoEq_dispatch_offset : Nat  -- routes to branchYaoEq_(i,j,t)
  branchShiEq_dispatch_offset : Nat  -- routes to branchShiEq_(sh,t)
  deriving Repr

/-! ## § 2  Per-Shi 4-way dispatch fragment

Each fragment compares `META.cur.2` against `Shi.dao`, `Shi.ji`, `Shi.jin`,
falling through to a target taken to mean `Shi.wei`.

The fragment is:

  [ branchShiEq Shi.dao daoTarget
  , branchShiEq Shi.ji  jiTarget
  , branchShiEq Shi.jin jinTarget
  , jump weiTarget
  ]

Length = 4 instructions.
-/

/-- A 4-way dispatch on `META.cur.2`. -/
def dispatchShi (daoTarget jiTarget jinTarget weiTarget : Nat) : List YiInstr :=
  [ YiInstr.branchShiEq Shi.dao daoTarget
  , YiInstr.branchShiEq Shi.ji  jiTarget
  , YiInstr.branchShiEq Shi.jin jinTarget
  , YiInstr.jump weiTarget
  ]

theorem dispatchShi_length (a b c d : Nat) :
    (dispatchShi a b c d).length = 4 := rfl

/-! ## § 3  Top-level dispatch tree

Layout (offsets relative to the dispatch tree's own start, `dispatchBase`):

  +0  : branchYaoEq 1 5  L_hex01    -- if y2 = y6 (=yang) → hex ∈ {0,1}
  +1  : jump L_hex2                  -- else hex = 2

  L_hex01 (+2):
  +2  : branchYaoEq 0 5  L_hex0      -- if y1 = y6 (=yang) → hex = 0
  +3  : jump L_hex1                  -- else hex = 1

  L_hex0 (+4):
  +4  : dispatchShi (nop, setShi, flipYao, interlace)         — 4 instr (+4..+7)

  L_hex1 (+8):
  +8  : dispatchShi (complement, reverse, branchYaoEq, branchShiEq)  — 4 instr (+8..+11)

  L_hex2 (+12):
  +12 : dispatchShi (jump, push, pop, halt)            — 4 instr (+12..+15)

Total length = 16 instructions.
-/

/-- The full top-level dispatch tree.  `dispatchBase` is the absolute pc
    where the tree begins inside `metaInterpProg`. -/
def dispatchTree (offsets : DispatchOffsets) (dispatchBase : Nat) : List YiInstr :=
  let L_hex01 := dispatchBase + 2
  let L_hex2  := dispatchBase + 12
  let L_hex0  := dispatchBase + 4
  let L_hex1  := dispatchBase + 8
  -- y2-test (compare y_2 to y_6 = known yang for tags 0..11)
  [ YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩ L_hex01
  , YiInstr.jump L_hex2 ]
  ++
  -- L_hex01 (+2): hex ∈ {0, 1} → y1-test
  [ YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩ L_hex0
  , YiInstr.jump L_hex1 ]
  ++
  -- L_hex0 (+4): hex=0 → nop / setShi / flipYao / interlace
  dispatchShi offsets.nop_offset
              offsets.setShi_dispatch_offset
              offsets.flipYao_dispatch_offset
              offsets.hu_offset
  ++
  -- L_hex1 (+8): hex=1 → complement / reverse / branchYaoEq / branchShiEq
  dispatchShi offsets.cuo_offset
              offsets.zong_offset
              offsets.branchYaoEq_dispatch_offset
              offsets.branchShiEq_dispatch_offset
  ++
  -- L_hex2 (+12): hex=2 → jump / push / pop / halt
  dispatchShi offsets.jump_offset
              offsets.push_offset
              offsets.pop_offset
              offsets.halt_offset

/-- The dispatch tree is exactly 16 instructions long. -/
theorem dispatchTree_length (offsets : DispatchOffsets) (dispatchBase : Nat) :
    (dispatchTree offsets dispatchBase).length = 16 := by
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

/-- The setShi sub-dispatch table.  Routes to one of four pre-compiled
    `executeBlock_setShi sh ...` blocks based on the param cell's `Shi`.

    Layout (relative to the sub-dispatch base):

      +0 : pop                          — pop param cell into META.cur
      +1 : branchShiEq Shi.dao daoOff
      +2 : branchShiEq Shi.ji  jiOff
      +3 : branchShiEq Shi.jin jinOff
      +4 : jump weiOff

    Length = 5 instructions. -/
def subDispatchSetShi (daoOff jiOff jinOff weiOff : Nat) : List YiInstr :=
  YiInstr.pop :: dispatchShi daoOff jiOff jinOff weiOff

theorem subDispatchSetShi_length (a b c d : Nat) :
    (subDispatchSetShi a b c d).length = 5 := by
  unfold subDispatchSetShi
  simp [dispatchShi]

/-- Encoding fact: the Shi-component of `encShi sh` is `sh` itself.  Used
    to discharge the routing proof for `subDispatchSetShi`. -/
private theorem encShi_shi (sh : Shi) : (encShi sh).2 = sh := by
  rcases sh with ⟨y, g⟩; cases y <;> cases g <;> rfl

/-- **Routing lemma for `subDispatchSetShi`**: starting from a META state
    whose `cur` is anything, `pc = 0`,
    `prog = subDispatchSetShi daoOff jiOff jinOff weiOff`, and `history`
    begins with `encShi sh` followed by `rest`, after the appropriate
    number of fuel steps (2 for `dao`, 3 for `ji`, 4 for `jin`, 5 for
    `wei`) META lands at the correct branch offset. -/
theorem subDispatchSetShi_routes
    (sh : Shi) (daoOff jiOff jinOff weiOff : Nat)
    (cur : R8) (rest : List R8) :
    let μ : YiState :=
      { cur := cur
        history := encShi sh :: rest
        pc := 0
        prog := subDispatchSetShi daoOff jiOff jinOff weiOff
        halted := false }
    let fuel : Nat := match sh with
      | .dao => 2 | .ji => 3 | .jin => 4 | .wei => 5
    let μ' := μ.runFuel fuel
    let target : Nat := match sh with
      | .dao => daoOff | .ji => jiOff | .jin => jinOff | .wei => weiOff
    μ'.pc = target
    ∧ μ'.cur = encShi sh
    ∧ μ'.history = rest
    ∧ μ'.halted = false := by
  rcases sh with ⟨y, g⟩
  cases y <;> cases g <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
            subDispatchSetShi, dispatchShi, encShi_shi]

/-! ### § 4.1  flipYao 6-way sub-dispatch -/

/-- The flipYao sub-dispatch table.  Routes to one of six pre-compiled
    `executeBlock_flipYao i ...` blocks based on the param cell's index
    `i ∈ Fin 6`.

    The param cell is `encFin6 i = cellFromIdx ⟨i.val, _⟩`, with
    `i.val ∈ {0..5}`.  Decomposing via `cellFromIdx`:

      hex_idx = i.val / 4 ∈ {0, 1}     (0 for i ∈ {0,1,2,3}, 1 for i ∈ {4,5})
      shi_idx = i.val % 4 ∈ {0, 1, 2, 3}  (0=dao, 1=ji, 2=jin, 3=wei)

    `Hexagram.fromIdx ⟨0, _⟩` = all yang; `fromIdx ⟨1, _⟩` = y1=yin,
    y2..y6=yang.  So we can decide hex_idx by comparing `y1` and `y6`:
    they are equal (both yang) for hex_idx = 0, unequal for hex_idx = 1.

    Layout (offsets relative to the dispatch base):

      +0 : pop                                     — pop param cell into cur
      +1 : branchYaoEq 0 5  (base + 3)             — y1 = y6 → hex 0
      +2 : jump (base + 7)                         — else hex 1
      +3 : branchShiEq Shi.dao off0                — hex 0 / dao
      +4 : branchShiEq Shi.ji  off1                — hex 0 / ji
      +5 : branchShiEq Shi.jin off2                — hex 0 / jin
      +6 : jump off3                               — hex 0 / wei
      +7 : branchShiEq Shi.dao off4                — hex 1 / dao
      +8 : branchShiEq Shi.ji  off5                — hex 1 / ji
      +9 : jump off5                               — defensive (unreachable)

    Length = 10 instructions. -/
def subDispatchFlipYao (dispatchBase : Nat)
    (off0 off1 off2 off3 off4 off5 : Nat) : List YiInstr :=
  [ YiInstr.pop
  , YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩ (dispatchBase + 3)
  , YiInstr.jump (dispatchBase + 7)
  , YiInstr.branchShiEq Shi.dao off0
  , YiInstr.branchShiEq Shi.ji  off1
  , YiInstr.branchShiEq Shi.jin off2
  , YiInstr.jump off3
  , YiInstr.branchShiEq Shi.dao off4
  , YiInstr.branchShiEq Shi.ji  off5
  , YiInstr.jump off5 ]

theorem subDispatchFlipYao_length (base a b c d e f : Nat) :
    (subDispatchFlipYao base a b c d e f).length = 10 := rfl

/-- **Routing lemma for `subDispatchFlipYao`**.  Fuel counts:
      i=0 (hex0/dao): 3   pop, branchYao take, branchShi dao take
      i=1 (hex0/ji):  4   pop, branchYao take, dao fall, ji take
      i=2 (hex0/jin): 5   pop, branchYao take, dao fall, ji fall, jin take
      i=3 (hex0/wei): 6   pop, branchYao take, dao fall, ji fall, jin fall, jump
      i=4 (hex1/dao): 4   pop, branchYao fall, jump, dao take
      i=5 (hex1/ji):  5   pop, branchYao fall, jump, dao fall, ji take
-/
theorem subDispatchFlipYao_routes
    (i : Fin 6) (off0 off1 off2 off3 off4 off5 : Nat)
    (cur : R8) (rest : List R8) :
    let μ : YiState :=
      { cur := cur
        history := encFin6 i :: rest
        pc := 0
        prog := subDispatchFlipYao 0 off0 off1 off2 off3 off4 off5
        halted := false }
    let fuel : Nat := match i.val with
      | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 4 | _ => 5
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
      simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
            subDispatchFlipYao, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx,
            SSBX.Foundation.Bagua.R8.Shi.fromIdx]
  | ⟨1, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
            subDispatchFlipYao, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx,
            SSBX.Foundation.Bagua.R8.Shi.fromIdx]
  | ⟨2, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
            subDispatchFlipYao, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx,
            SSBX.Foundation.Bagua.R8.Shi.fromIdx]
  | ⟨3, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin, Shi.wei,
            subDispatchFlipYao, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx,
            SSBX.Foundation.Bagua.R8.Shi.fromIdx]
  | ⟨4, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
            subDispatchFlipYao, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx,
            SSBX.Foundation.Bagua.R8.Shi.fromIdx]
  | ⟨5, _⟩ =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
            subDispatchFlipYao, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin,
            encFin6, cellFromIdx, Hexagram.fromIdx, Yao.fromIdx,
            SSBX.Foundation.Bagua.R8.Shi.fromIdx]

/-! ## § 5  Concrete routing proofs — all 12 opcode tags

For each tag k ∈ {0..11}, the path through the dispatch tree depends on
hex_idx (= k/4) and shi_idx (= k%4):

| k  | op            | hex | shi | y2=y6  | y1=y6  | shi-fires     | fuel |
| -- | ------------- | --- | --- | ------ | ------ | ------------- | ---- |
| 0  | nop           | 0   | dao | yes    | yes    | dao (1 take)  | 3    |
| 1  | setShi        | 0   | ji  | yes    | yes    | dao→ji (2)    | 4    |
| 2  | flipYao       | 0   | jin | yes    | yes    | dao→ji→jin    | 5    |
| 3  | interlace            | 0   | wei | yes    | yes    | jump          | 6    |
| 4  | complement           | 1   | dao | yes    | no     | dao           | 4    |
| 5  | reverse          | 1   | ji  | yes    | no     | dao→ji        | 5    |
| 6  | branchYaoEq   | 1   | jin | yes    | no     | dao→ji→jin    | 6    |
| 7  | branchShiEq   | 1   | wei | yes    | no     | jump          | 7    |
| 8  | jump          | 2   | dao | no     | -      | dao           | 3    |
| 9  | push          | 2   | ji  | no     | -      | dao→ji        | 4    |
| 10 | pop           | 2   | jin | no     | -      | dao→ji→jin    | 5    |
| 11 | halt          | 2   | wei | no     | -      | jump          | 6    |
-/

/-! ### nop  (k=0, hex_idx=0, shi=dao) -/

/-! ### Segment-level route helpers

The standalone route theorems below run with `pc = 0` and
`prog = dispatchTree offsets 0`.  The universal-compose assembly needs the
same facts after the dispatch tree has been spliced into a larger program at
an absolute `dispatchBase`.  These tiny step lemmas keep that lift explicit:
callers provide the local lookup at the absolute pc, and the VM step reduces
to the corresponding branch or jump move. -/

private theorem step_branchYaoEq_not_taken
    (s : YiState) (i j : Fin 6) (target : Nat)
    (h_halted : s.halted = false)
    (h_lookup : s.prog[s.pc]? = some (YiInstr.branchYaoEq i j target))
    (h_ne : s.cur.1.yaoAt i ≠ s.cur.1.yaoAt j) :
    s.step = { s with pc := s.pc + 1, halted := false } := by
  unfold YiState.step
  rw [h_halted]
  simp [h_lookup, YiState.execute, h_ne, h_halted]

private theorem step_branchYaoEq_taken
    (s : YiState) (i j : Fin 6) (target : Nat)
    (h_halted : s.halted = false)
    (h_lookup : s.prog[s.pc]? = some (YiInstr.branchYaoEq i j target))
    (h_eq : s.cur.1.yaoAt i = s.cur.1.yaoAt j) :
    s.step = { s with pc := target, halted := false } := by
  unfold YiState.step
  rw [h_halted]
  simp [h_lookup, YiState.execute, h_eq, h_halted]

private theorem step_branchShiEq_not_taken
    (s : YiState) (sh : Shi) (target : Nat)
    (h_halted : s.halted = false)
    (h_lookup : s.prog[s.pc]? = some (YiInstr.branchShiEq sh target))
    (h_ne : s.cur.2 ≠ sh) :
    s.step = { s with pc := s.pc + 1, halted := false } := by
  unfold YiState.step
  rw [h_halted]
  simp [h_lookup, YiState.execute, h_ne, h_halted]

private theorem step_branchShiEq_taken
    (s : YiState) (sh : Shi) (target : Nat)
    (h_halted : s.halted = false)
    (h_lookup : s.prog[s.pc]? = some (YiInstr.branchShiEq sh target))
    (h_eq : s.cur.2 = sh) :
    s.step = { s with pc := target, halted := false } := by
  unfold YiState.step
  rw [h_halted]
  simp [h_lookup, YiState.execute, h_eq, h_halted]

private theorem step_jump
    (s : YiState) (target : Nat)
    (h_halted : s.halted = false)
    (h_lookup : s.prog[s.pc]? = some (YiInstr.jump target)) :
    s.step = { s with pc := target, halted := false } := by
  unfold YiState.step
  rw [h_halted]
  simp [h_lookup, YiState.execute, h_halted]

def nopTag : R8 := cellFromIdx ⟨0, by omega⟩

private theorem nopTag_yao : nopTag.1.y1 = Yao.yang
                           ∧ nopTag.1.y2 = Yao.yang
                           ∧ nopTag.1.y3 = Yao.yang
                           ∧ nopTag.1.y4 = Yao.yang
                           ∧ nopTag.1.y5 = Yao.yang
                           ∧ nopTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem nopTag_shi : nopTag.2 = Shi.dao := by
  unfold nopTag cellFromIdx
  rfl

theorem dispatchTree_routes_nop
    (offsets : DispatchOffsets) (history : List R8) :
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
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, nopTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, nopTag_yao.1, nopTag_yao.2.1, nopTag_yao.2.2.2.2.2]

/-! ### setShi  (k=1, hex_idx=0, shi=ji) -/

def setShiTag : R8 := cellFromIdx ⟨1, by omega⟩

private theorem setShiTag_yao : setShiTag.1.y1 = Yao.yang
                              ∧ setShiTag.1.y2 = Yao.yang
                              ∧ setShiTag.1.y3 = Yao.yang
                              ∧ setShiTag.1.y4 = Yao.yang
                              ∧ setShiTag.1.y5 = Yao.yang
                              ∧ setShiTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem setShiTag_shi : setShiTag.2 = Shi.ji := by
  unfold setShiTag cellFromIdx
  rfl

theorem dispatchTree_routes_setShi
    (offsets : DispatchOffsets) (history : List R8) :
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
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, setShiTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, setShiTag_yao.1, setShiTag_yao.2.1,
          setShiTag_yao.2.2.2.2.2]

/-! ### flipYao  (k=2, hex_idx=0, shi=jin) -/

def flipYaoTag : R8 := cellFromIdx ⟨2, by omega⟩

private theorem flipYaoTag_yao : flipYaoTag.1.y1 = Yao.yang
                               ∧ flipYaoTag.1.y2 = Yao.yang
                               ∧ flipYaoTag.1.y3 = Yao.yang
                               ∧ flipYaoTag.1.y4 = Yao.yang
                               ∧ flipYaoTag.1.y5 = Yao.yang
                               ∧ flipYaoTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem flipYaoTag_shi : flipYaoTag.2 = Shi.jin := by
  unfold flipYaoTag cellFromIdx
  rfl

theorem dispatchTree_routes_flipYao
    (offsets : DispatchOffsets) (history : List R8) :
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
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, flipYaoTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, flipYaoTag_yao.1, flipYaoTag_yao.2.1,
          flipYaoTag_yao.2.2.2.2.2]

/-! ### interlace  (k=3, hex_idx=0, shi=wei) -/

def huTag : R8 := cellFromIdx ⟨3, by omega⟩

private theorem huTag_yao : huTag.1.y1 = Yao.yang
                          ∧ huTag.1.y2 = Yao.yang
                          ∧ huTag.1.y3 = Yao.yang
                          ∧ huTag.1.y4 = Yao.yang
                          ∧ huTag.1.y5 = Yao.yang
                          ∧ huTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem huTag_shi : huTag.2 = Shi.wei := by
  unfold huTag cellFromIdx
  rfl

theorem dispatchTree_routes_hu
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := huTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.hu_offset
    ∧ μ'.cur = huTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin, Shi.wei,
          dispatchTree, dispatchShi, huTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, huTag_yao.1, huTag_yao.2.1, huTag_yao.2.2.2.2.2]

/-! ### complement  (k=4, hex_idx=1, shi=dao) -/

def cuoTag : R8 := cellFromIdx ⟨4, by omega⟩

private theorem cuoTag_yao : cuoTag.1.y1 = Yao.yin
                           ∧ cuoTag.1.y2 = Yao.yang
                           ∧ cuoTag.1.y3 = Yao.yang
                           ∧ cuoTag.1.y4 = Yao.yang
                           ∧ cuoTag.1.y5 = Yao.yang
                           ∧ cuoTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem cuoTag_shi : cuoTag.2 = Shi.dao := by
  unfold cuoTag cellFromIdx
  rfl

theorem dispatchTree_routes_cuo
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := cuoTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.cuo_offset
    ∧ μ'.cur = cuoTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, cuoTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, cuoTag_yao.1, cuoTag_yao.2.1, cuoTag_yao.2.2.2.2.2]

/-! ### reverse  (k=5, hex_idx=1, shi=ji) -/

def zongTag : R8 := cellFromIdx ⟨5, by omega⟩

private theorem zongTag_yao : zongTag.1.y1 = Yao.yin
                            ∧ zongTag.1.y2 = Yao.yang
                            ∧ zongTag.1.y3 = Yao.yang
                            ∧ zongTag.1.y4 = Yao.yang
                            ∧ zongTag.1.y5 = Yao.yang
                            ∧ zongTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem zongTag_shi : zongTag.2 = Shi.ji := by
  unfold zongTag cellFromIdx
  rfl

theorem dispatchTree_routes_zong
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := zongTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.zong_offset
    ∧ μ'.cur = zongTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, zongTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, zongTag_yao.1, zongTag_yao.2.1, zongTag_yao.2.2.2.2.2]

/-! ### branchYaoEq  (k=6, hex_idx=1, shi=jin) -/

def branchYaoEqTag : R8 := cellFromIdx ⟨6, by omega⟩

private theorem branchYaoEqTag_yao : branchYaoEqTag.1.y1 = Yao.yin
                                   ∧ branchYaoEqTag.1.y2 = Yao.yang
                                   ∧ branchYaoEqTag.1.y3 = Yao.yang
                                   ∧ branchYaoEqTag.1.y4 = Yao.yang
                                   ∧ branchYaoEqTag.1.y5 = Yao.yang
                                   ∧ branchYaoEqTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem branchYaoEqTag_shi : branchYaoEqTag.2 = Shi.jin := by
  unfold branchYaoEqTag cellFromIdx
  rfl

theorem dispatchTree_routes_branchYaoEq
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := branchYaoEqTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.branchYaoEq_dispatch_offset
    ∧ μ'.cur = branchYaoEqTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, branchYaoEqTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, branchYaoEqTag_yao.1, branchYaoEqTag_yao.2.1,
          branchYaoEqTag_yao.2.2.2.2.2]

/-! ### branchShiEq  (k=7, hex_idx=1, shi=wei) -/

def branchShiEqTag : R8 := cellFromIdx ⟨7, by omega⟩

private theorem branchShiEqTag_yao : branchShiEqTag.1.y1 = Yao.yin
                                   ∧ branchShiEqTag.1.y2 = Yao.yang
                                   ∧ branchShiEqTag.1.y3 = Yao.yang
                                   ∧ branchShiEqTag.1.y4 = Yao.yang
                                   ∧ branchShiEqTag.1.y5 = Yao.yang
                                   ∧ branchShiEqTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem branchShiEqTag_shi : branchShiEqTag.2 = Shi.wei := by
  unfold branchShiEqTag cellFromIdx
  rfl

theorem dispatchTree_routes_branchShiEq
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := branchShiEqTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 7
    μ'.pc = offsets.branchShiEq_dispatch_offset
    ∧ μ'.cur = branchShiEqTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin, Shi.wei,
          dispatchTree, dispatchShi, branchShiEqTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, branchShiEqTag_yao.1, branchShiEqTag_yao.2.1,
          branchShiEqTag_yao.2.2.2.2.2]

/-! ### jump  (k=8, hex_idx=2, shi=dao) -/

def jumpTag : R8 := cellFromIdx ⟨8, by omega⟩

private theorem jumpTag_yao : jumpTag.1.y1 = Yao.yang
                            ∧ jumpTag.1.y2 = Yao.yin
                            ∧ jumpTag.1.y3 = Yao.yang
                            ∧ jumpTag.1.y4 = Yao.yang
                            ∧ jumpTag.1.y5 = Yao.yang
                            ∧ jumpTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem jumpTag_shi : jumpTag.2 = Shi.dao := by
  unfold jumpTag cellFromIdx
  rfl

theorem dispatchTree_routes_jump
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := jumpTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = offsets.jump_offset
    ∧ μ'.cur = jumpTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, jumpTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, jumpTag_yao.2.1, jumpTag_yao.2.2.2.2.2]

/-! ### push  (k=9, hex_idx=2, shi=ji) -/

def pushTag : R8 := cellFromIdx ⟨9, by omega⟩

private theorem pushTag_yao : pushTag.1.y1 = Yao.yang
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
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := pushTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.push_offset
    ∧ μ'.cur = pushTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, pushTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, pushTag_yao.2.1, pushTag_yao.2.2.2.2.2]

/-! ### pop  (k=10, hex_idx=2, shi=jin) -/

def popTag : R8 := cellFromIdx ⟨10, by omega⟩

private theorem popTag_yao : popTag.1.y1 = Yao.yang
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
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := popTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.pop_offset
    ∧ μ'.cur = popTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin,
          dispatchTree, dispatchShi, popTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, popTag_yao.2.1, popTag_yao.2.2.2.2.2]

/-! ### halt  (k=11, hex_idx=2, shi=wei) -/

def haltTag : R8 := cellFromIdx ⟨11, by omega⟩

private theorem haltTag_yao : haltTag.1.y1 = Yao.yang
                            ∧ haltTag.1.y2 = Yao.yin
                            ∧ haltTag.1.y3 = Yao.yang
                            ∧ haltTag.1.y4 = Yao.yang
                            ∧ haltTag.1.y5 = Yao.yang
                            ∧ haltTag.1.y6 = Yao.yang := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem haltTag_shi : haltTag.2 = Shi.wei := by
  unfold haltTag cellFromIdx
  rfl

theorem dispatchTree_routes_halt
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := haltTag
        history := history
        pc := 0
        prog := dispatchTree offsets 0
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.halt_offset
    ∧ μ'.cur = haltTag
    ∧ μ'.history = history
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao, Shi.ji, Shi.jin, Shi.wei,
          dispatchTree, dispatchShi, haltTag_shi,
          Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, haltTag_yao.2.1, haltTag_yao.2.2.2.2.2]

/-- Segment-level nop routing. -/
theorem dispatchTree_routes_nop_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := nopTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = offsets.nop_offset
      ∧ μ'.cur = nopTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup2 : metaProg[dispatchBase + 2]? =
      some (YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 4)) := by
    have h := hseg 2 (by decide)
    simpa [dispatchTree] using h
  have h_lookup4 : metaProg[dispatchBase + 4]? =
      some (YiInstr.branchShiEq Shi.dao offsets.nop_offset) := by
    have h := hseg 4 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao,
      h_lookup0, h_lookup2, h_lookup4, nopTag_shi,
      Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, nopTag_yao.1, nopTag_yao.2.1,
      nopTag_yao.2.2.2.2.2]

/-- Segment-level setShi routing. -/
theorem dispatchTree_routes_setShi_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := setShiTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.setShi_dispatch_offset
      ∧ μ'.cur = setShiTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup2 : metaProg[dispatchBase + 2]? =
      some (YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 4)) := by
    have h := hseg 2 (by decide)
    simpa [dispatchTree] using h
  have h_lookup4 : metaProg[dispatchBase + 4]? =
      some (YiInstr.branchShiEq Shi.dao offsets.nop_offset) := by
    have h := hseg 4 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup5 : metaProg[dispatchBase + 5]? =
      some (YiInstr.branchShiEq Shi.ji offsets.setShi_dispatch_offset) := by
    have h := hseg 5 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
      Shi.dao, Shi.ji,
      h_lookup0, h_lookup2, h_lookup4, h_lookup5, setShiTag_shi,
      Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, setShiTag_yao.1, setShiTag_yao.2.1,
      setShiTag_yao.2.2.2.2.2]

/-- Segment-level flipYao routing. -/
theorem dispatchTree_routes_flipYao_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := flipYaoTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.flipYao_dispatch_offset
      ∧ μ'.cur = flipYaoTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup2 : metaProg[dispatchBase + 2]? =
      some (YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 4)) := by
    have h := hseg 2 (by decide)
    simpa [dispatchTree] using h
  have h_lookup4 : metaProg[dispatchBase + 4]? =
      some (YiInstr.branchShiEq Shi.dao offsets.nop_offset) := by
    have h := hseg 4 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup5 : metaProg[dispatchBase + 5]? =
      some (YiInstr.branchShiEq Shi.ji offsets.setShi_dispatch_offset) := by
    have h := hseg 5 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup6 : metaProg[dispatchBase + 6]? =
      some (YiInstr.branchShiEq Shi.jin offsets.flipYao_dispatch_offset) := by
    have h := hseg 6 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
      Shi.dao, Shi.ji, Shi.jin,
      h_lookup0, h_lookup2, h_lookup4, h_lookup5, h_lookup6,
      flipYaoTag_shi, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, flipYaoTag_yao.1,
      flipYaoTag_yao.2.1, flipYaoTag_yao.2.2.2.2.2]

/-- Segment-level interlace routing. -/
theorem dispatchTree_routes_hu_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := huTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.hu_offset
      ∧ μ'.cur = huTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup2 : metaProg[dispatchBase + 2]? =
      some (YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 4)) := by
    have h := hseg 2 (by decide)
    simpa [dispatchTree] using h
  have h_lookup4 : metaProg[dispatchBase + 4]? =
      some (YiInstr.branchShiEq Shi.dao offsets.nop_offset) := by
    have h := hseg 4 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup5 : metaProg[dispatchBase + 5]? =
      some (YiInstr.branchShiEq Shi.ji offsets.setShi_dispatch_offset) := by
    have h := hseg 5 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup6 : metaProg[dispatchBase + 6]? =
      some (YiInstr.branchShiEq Shi.jin offsets.flipYao_dispatch_offset) := by
    have h := hseg 6 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup7 : metaProg[dispatchBase + 7]? =
      some (YiInstr.jump offsets.hu_offset) := by
    have h := hseg 7 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
      Shi.dao, Shi.ji, Shi.jin, Shi.wei,
      h_lookup0, h_lookup2, h_lookup4, h_lookup5, h_lookup6,
      h_lookup7, huTag_shi, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, huTag_yao.1,
      huTag_yao.2.1, huTag_yao.2.2.2.2.2]

/-- Segment-level complement routing. -/
theorem dispatchTree_routes_cuo_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := cuoTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.cuo_offset
      ∧ μ'.cur = cuoTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup2 : metaProg[dispatchBase + 2]? =
      some (YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 4)) := by
    have h := hseg 2 (by decide)
    simpa [dispatchTree] using h
  have h_lookup3 : metaProg[dispatchBase + 3]? =
      some (YiInstr.jump (dispatchBase + 8)) := by
    have h := hseg 3 (by decide)
    simpa [dispatchTree] using h
  have h_lookup8 : metaProg[dispatchBase + 8]? =
      some (YiInstr.branchShiEq Shi.dao offsets.cuo_offset) := by
    have h := hseg 8 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao,
      h_lookup0, h_lookup2, h_lookup3, h_lookup8, cuoTag_shi,
      Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, cuoTag_yao.1, cuoTag_yao.2.1,
      cuoTag_yao.2.2.2.2.2]

/-- Segment-level reverse routing. -/
theorem dispatchTree_routes_zong_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := zongTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.zong_offset
      ∧ μ'.cur = zongTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup2 : metaProg[dispatchBase + 2]? =
      some (YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 4)) := by
    have h := hseg 2 (by decide)
    simpa [dispatchTree] using h
  have h_lookup3 : metaProg[dispatchBase + 3]? =
      some (YiInstr.jump (dispatchBase + 8)) := by
    have h := hseg 3 (by decide)
    simpa [dispatchTree] using h
  have h_lookup8 : metaProg[dispatchBase + 8]? =
      some (YiInstr.branchShiEq Shi.dao offsets.cuo_offset) := by
    have h := hseg 8 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup9 : metaProg[dispatchBase + 9]? =
      some (YiInstr.branchShiEq Shi.ji offsets.zong_offset) := by
    have h := hseg 9 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
      Shi.dao, Shi.ji,
      h_lookup0, h_lookup2, h_lookup3, h_lookup8, h_lookup9,
      zongTag_shi, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, zongTag_yao.1,
      zongTag_yao.2.1, zongTag_yao.2.2.2.2.2]

/-- Segment-level branchYaoEq routing. -/
theorem dispatchTree_routes_branchYaoEq_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := branchYaoEqTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.branchYaoEq_dispatch_offset
      ∧ μ'.cur = branchYaoEqTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup2 : metaProg[dispatchBase + 2]? =
      some (YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 4)) := by
    have h := hseg 2 (by decide)
    simpa [dispatchTree] using h
  have h_lookup3 : metaProg[dispatchBase + 3]? =
      some (YiInstr.jump (dispatchBase + 8)) := by
    have h := hseg 3 (by decide)
    simpa [dispatchTree] using h
  have h_lookup8 : metaProg[dispatchBase + 8]? =
      some (YiInstr.branchShiEq Shi.dao offsets.cuo_offset) := by
    have h := hseg 8 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup9 : metaProg[dispatchBase + 9]? =
      some (YiInstr.branchShiEq Shi.ji offsets.zong_offset) := by
    have h := hseg 9 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup10 : metaProg[dispatchBase + 10]? =
      some (YiInstr.branchShiEq Shi.jin
        offsets.branchYaoEq_dispatch_offset) := by
    have h := hseg 10 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
      Shi.dao, Shi.ji, Shi.jin,
      h_lookup0, h_lookup2, h_lookup3, h_lookup8, h_lookup9,
      h_lookup10, branchYaoEqTag_shi, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin,
      branchYaoEqTag_yao.1, branchYaoEqTag_yao.2.1,
      branchYaoEqTag_yao.2.2.2.2.2]

/-- Segment-level branchShiEq routing. -/
theorem dispatchTree_routes_branchShiEq_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := branchShiEqTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 7
    μ'.pc = offsets.branchShiEq_dispatch_offset
      ∧ μ'.cur = branchShiEqTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup2 : metaProg[dispatchBase + 2]? =
      some (YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 4)) := by
    have h := hseg 2 (by decide)
    simpa [dispatchTree] using h
  have h_lookup3 : metaProg[dispatchBase + 3]? =
      some (YiInstr.jump (dispatchBase + 8)) := by
    have h := hseg 3 (by decide)
    simpa [dispatchTree] using h
  have h_lookup8 : metaProg[dispatchBase + 8]? =
      some (YiInstr.branchShiEq Shi.dao offsets.cuo_offset) := by
    have h := hseg 8 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup9 : metaProg[dispatchBase + 9]? =
      some (YiInstr.branchShiEq Shi.ji offsets.zong_offset) := by
    have h := hseg 9 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup10 : metaProg[dispatchBase + 10]? =
      some (YiInstr.branchShiEq Shi.jin
        offsets.branchYaoEq_dispatch_offset) := by
    have h := hseg 10 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup11 : metaProg[dispatchBase + 11]? =
      some (YiInstr.jump offsets.branchShiEq_dispatch_offset) := by
    have h := hseg 11 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
      Shi.dao, Shi.ji, Shi.jin, Shi.wei,
      h_lookup0, h_lookup2, h_lookup3, h_lookup8, h_lookup9,
      h_lookup10, h_lookup11, branchShiEqTag_shi, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin,
      branchShiEqTag_yao.1, branchShiEqTag_yao.2.1,
      branchShiEqTag_yao.2.2.2.2.2]

/-- Segment-level jump routing. -/
theorem dispatchTree_routes_jump_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := jumpTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = offsets.jump_offset
      ∧ μ'.cur = jumpTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup1 : metaProg[dispatchBase + 1]? =
      some (YiInstr.jump (dispatchBase + 12)) := by
    have h := hseg 1 (by decide)
    simpa [dispatchTree] using h
  have h_lookup12 : metaProg[dispatchBase + 12]? =
      some (YiInstr.branchShiEq Shi.dao offsets.jump_offset) := by
    have h := hseg 12 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute, Shi.dao,
      h_lookup0, h_lookup1, h_lookup12, jumpTag_shi,
      Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, jumpTag_yao.2.1, jumpTag_yao.2.2.2.2.2]

/-- Segment-level push routing. -/
theorem dispatchTree_routes_push_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := pushTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.push_offset
      ∧ μ'.cur = pushTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup1 : metaProg[dispatchBase + 1]? =
      some (YiInstr.jump (dispatchBase + 12)) := by
    have h := hseg 1 (by decide)
    simpa [dispatchTree] using h
  have h_lookup12 : metaProg[dispatchBase + 12]? =
      some (YiInstr.branchShiEq Shi.dao offsets.jump_offset) := by
    have h := hseg 12 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup13 : metaProg[dispatchBase + 13]? =
      some (YiInstr.branchShiEq Shi.ji offsets.push_offset) := by
    have h := hseg 13 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
      Shi.dao, Shi.ji,
      h_lookup0, h_lookup1, h_lookup12, h_lookup13, pushTag_shi,
      Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, pushTag_yao.2.1, pushTag_yao.2.2.2.2.2]

/-- Segment-level pop routing. -/
theorem dispatchTree_routes_pop_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := popTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.pop_offset
      ∧ μ'.cur = popTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h_lookup1 : metaProg[dispatchBase + 1]? =
      some (YiInstr.jump (dispatchBase + 12)) := by
    have h := hseg 1 (by decide)
    simpa [dispatchTree] using h
  have h_lookup12 : metaProg[dispatchBase + 12]? =
      some (YiInstr.branchShiEq Shi.dao offsets.jump_offset) := by
    have h := hseg 12 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup13 : metaProg[dispatchBase + 13]? =
      some (YiInstr.branchShiEq Shi.ji offsets.push_offset) := by
    have h := hseg 13 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h_lookup14 : metaProg[dispatchBase + 14]? =
      some (YiInstr.branchShiEq Shi.jin offsets.pop_offset) := by
    have h := hseg 14 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
      Shi.dao, Shi.ji, Shi.jin,
      h_lookup0, h_lookup1, h_lookup12, h_lookup13, h_lookup14,
      popTag_shi, Hexagram.yaoAt, Yao.yang, Yao.yin,
            SSBX.Foundation.Atlas.Yi.Yao.yang, SSBX.Foundation.Atlas.Yi.Yao.yin, popTag_yao.2.1,
      popTag_yao.2.2.2.2.2]

/-- Segment-level halt routing: if a `dispatchTree offsets dispatchBase`
    segment is spliced into a larger `metaProg` at `dispatchBase`, then the
    halt tag follows the absolute-pc route through that segment and lands at
    `offsets.halt_offset` in six fuel ticks.

    This is the narrow F.7c lift from a standalone `pc = 0` dispatch proof to
    an assembled-program route witness. -/
theorem dispatchTree_routes_halt_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8)
    (hseg : ∀ i (_hi : i < 16),
      metaProg[dispatchBase + i]? =
        (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := haltTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.halt_offset
      ∧ μ'.cur = haltTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  let μ0 : YiState :=
      { cur := haltTag, history := history, pc := dispatchBase,
        prog := metaProg, halted := false }
  have h_lookup0 : metaProg[dispatchBase]? =
      some (YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨5, by omega⟩
        (dispatchBase + 2)) := by
    have h := hseg 0 (by decide)
    simpa [dispatchTree] using h
  have h0 : μ0.step = { μ0 with pc := dispatchBase + 1, halted := false } := by
    apply step_branchYaoEq_not_taken
    · rfl
    · exact h_lookup0
    · show haltTag.1.yaoAt ⟨1, by omega⟩ ≠ haltTag.1.yaoAt ⟨5, by omega⟩
      decide
  let μ1 : YiState := { μ0 with pc := dispatchBase + 1, halted := false }
  have hrun1 : μ0.runFuel 1 = μ1 := by
    change (if μ0.halted then μ0 else μ0.step) = μ1
    rw [show μ0.halted = false by rfl]
    simp [h0, μ1]
  have h_lookup1 : metaProg[dispatchBase + 1]? =
      some (YiInstr.jump (dispatchBase + 12)) := by
    have h := hseg 1 (by decide)
    simpa [dispatchTree] using h
  have h1 : μ1.step = { μ1 with pc := dispatchBase + 12, halted := false } := by
    apply step_jump
    · rfl
    · exact h_lookup1
  let μ2 : YiState := { μ1 with pc := dispatchBase + 12, halted := false }
  have hrun2 : μ0.runFuel 2 = μ2 := by
    rw [show (2 : Nat) = 1 + 1 from rfl,
      SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun1, h1]
  have h_lookup12 : metaProg[dispatchBase + 12]? =
      some (YiInstr.branchShiEq Shi.dao offsets.jump_offset) := by
    have h := hseg 12 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h2 : μ2.step = { μ2 with pc := dispatchBase + 13, halted := false } := by
    apply step_branchShiEq_not_taken
    · rfl
    · exact h_lookup12
    · show haltTag.2 ≠ Shi.dao
      decide
  let μ3 : YiState := { μ2 with pc := dispatchBase + 13, halted := false }
  have hrun3 : μ0.runFuel 3 = μ3 := by
    rw [show (3 : Nat) = 2 + 1 from rfl,
      SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun2, h2]
  have h_lookup13 : metaProg[dispatchBase + 13]? =
      some (YiInstr.branchShiEq Shi.ji offsets.push_offset) := by
    have h := hseg 13 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h3 : μ3.step = { μ3 with pc := dispatchBase + 14, halted := false } := by
    apply step_branchShiEq_not_taken
    · rfl
    · exact h_lookup13
    · show haltTag.2 ≠ Shi.ji
      decide
  let μ4 : YiState := { μ3 with pc := dispatchBase + 14, halted := false }
  have hrun4 : μ0.runFuel 4 = μ4 := by
    rw [show (4 : Nat) = 3 + 1 from rfl,
      SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun3, h3]
  have h_lookup14 : metaProg[dispatchBase + 14]? =
      some (YiInstr.branchShiEq Shi.jin offsets.pop_offset) := by
    have h := hseg 14 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h4 : μ4.step = { μ4 with pc := dispatchBase + 15, halted := false } := by
    apply step_branchShiEq_not_taken
    · rfl
    · exact h_lookup14
    · show haltTag.2 ≠ Shi.jin
      decide
  let μ5 : YiState := { μ4 with pc := dispatchBase + 15, halted := false }
  have hrun5 : μ0.runFuel 5 = μ5 := by
    rw [show (5 : Nat) = 4 + 1 from rfl,
      SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun4, h4]
  have h_lookup15 : metaProg[dispatchBase + 15]? =
      some (YiInstr.jump offsets.halt_offset) := by
    have h := hseg 15 (by decide)
    simpa [dispatchTree, dispatchShi] using h
  have h5 : μ5.step = { μ5 with pc := offsets.halt_offset, halted := false } := by
    apply step_jump
    · rfl
    · exact h_lookup15
  let μ6 : YiState := { μ5 with pc := offsets.halt_offset, halted := false }
  have hrun6 : μ0.runFuel 6 = μ6 := by
    rw [show (6 : Nat) = 5 + 1 from rfl,
      SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun5, h5]
  change (μ0.runFuel 6).pc = offsets.halt_offset
      ∧ (μ0.runFuel 6).cur = haltTag
      ∧ (μ0.runFuel 6).history = history
      ∧ (μ0.runFuel 6).prog = metaProg
      ∧ (μ0.runFuel 6).halted = false
  rw [hrun6]
  simp [μ6, μ5, μ4, μ3, μ2, μ1, μ0]

/-! ### Instruction-indexed dispatch route

The 12 route theorems above are the primitive facts.  The following
definitions package the same table behind `YiInstr`, so later universal
compose witnesses can case-split on the source instruction rather than
manually selecting one of 12 theorem names.  Parameterized opcodes still route
only to their Strategy-B sub-dispatch/default entry; their payload semantics
remain a later obligation. -/

def dispatchTagOfInstr : YiInstr → R8
  | .nop => nopTag
  | .setShi _ => setShiTag
  | .flipYao _ => flipYaoTag
  | .interlace => huTag
  | .complement => cuoTag
  | .reverse => zongTag
  | .branchYaoEq _ _ _ => branchYaoEqTag
  | .branchShiEq _ _ => branchShiEqTag
  | .jump _ => jumpTag
  | .push => pushTag
  | .pop => popTag
  | .halt => haltTag

def dispatchFuelOfInstr : YiInstr → Nat
  | .nop => 3
  | .setShi _ => 4
  | .flipYao _ => 5
  | .interlace => 6
  | .complement => 4
  | .reverse => 5
  | .branchYaoEq _ _ _ => 6
  | .branchShiEq _ _ => 7
  | .jump _ => 3
  | .push => 4
  | .pop => 5
  | .halt => 6

def dispatchTargetOfInstr (offsets : DispatchOffsets) : YiInstr → Nat
  | .nop => offsets.nop_offset
  | .setShi _ => offsets.setShi_dispatch_offset
  | .flipYao _ => offsets.flipYao_dispatch_offset
  | .interlace => offsets.hu_offset
  | .complement => offsets.cuo_offset
  | .reverse => offsets.zong_offset
  | .branchYaoEq _ _ _ => offsets.branchYaoEq_dispatch_offset
  | .branchShiEq _ _ => offsets.branchShiEq_dispatch_offset
  | .jump _ => offsets.jump_offset
  | .push => offsets.push_offset
  | .pop => offsets.pop_offset
  | .halt => offsets.halt_offset

theorem encInstr_head?_eq_dispatchTagOfInstr (instr : YiInstr) :
    (YiInstrEnc.encInstr instr).head? = some (dispatchTagOfInstr instr) := by
  cases instr <;> rfl

theorem dispatchTree_routes_instr_at_segment
    (offsets : DispatchOffsets) (dispatchBase : Nat)
    (metaProg : List YiInstr) (history : List R8) (instr : YiInstr)
    (hseg : ∀ i (_ : i < 16),
        metaProg[dispatchBase + i]? =
          (dispatchTree offsets dispatchBase)[i]?) :
    let μ : YiState :=
      { cur := dispatchTagOfInstr instr
        history := history
        pc := dispatchBase
        prog := metaProg
        halted := false }
    let μ' := μ.runFuel (dispatchFuelOfInstr instr)
    μ'.pc = dispatchTargetOfInstr offsets instr
      ∧ μ'.cur = dispatchTagOfInstr instr
      ∧ μ'.history = history
      ∧ μ'.prog = metaProg
      ∧ μ'.halted = false := by
  cases instr with
  | nop =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_nop_at_segment offsets dispatchBase metaProg history hseg
  | setShi sh =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_setShi_at_segment offsets dispatchBase metaProg history hseg
  | flipYao i =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_flipYao_at_segment offsets dispatchBase metaProg history hseg
  | interlace =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_hu_at_segment offsets dispatchBase metaProg history hseg
  | complement =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_cuo_at_segment offsets dispatchBase metaProg history hseg
  | reverse =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_zong_at_segment offsets dispatchBase metaProg history hseg
  | branchYaoEq i j target =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_branchYaoEq_at_segment offsets dispatchBase
          metaProg history hseg
  | branchShiEq sh target =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_branchShiEq_at_segment offsets dispatchBase
          metaProg history hseg
  | jump target =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_jump_at_segment offsets dispatchBase metaProg history hseg
  | push =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_push_at_segment offsets dispatchBase metaProg history hseg
  | pop =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_pop_at_segment offsets dispatchBase metaProg history hseg
  | halt =>
      simpa [dispatchTagOfInstr, dispatchFuelOfInstr, dispatchTargetOfInstr] using
        dispatchTree_routes_halt_at_segment offsets dispatchBase metaProg history hseg

end SSBX.Foundation.Wen.MetaInterp.Dispatch
