/-
# SubDispatch_BranchYaoEq — outer (i,j) 36-way sub-dispatch for branchYaoEq

After fetch lands branchYaoEq's TAG into META.cur and leaves
`encFin6 i :: encFin6 j :: encNat t :: tail` on META.history, this
sub-dispatcher routes through TWO levels of 6-way Fin 6 dispatch to one
of 36 per-(i, j) sub-blocks.  Each per-(i, j) sub-block (left as offset
parameter) handles encNat t consumption and the actual conditional pc-update.

This is the "outer" half of branchYaoEq dispatch; the per-t inner dispatch
is C.D-pending.

Structure:
- `subDispatchBranchYaoEqPerJ` : ONE 9-instruction j-dispatcher
  (mirrors flipYao 6-way shape: pop, branchYaoEq y1 y6, jump,
  3-way Shi for hex 0, 3-way Shi for hex 1)
- `subDispatchBranchYaoEq` : 9-instruction outer i-dispatcher routing to
  6 perJ entries.

For each Fin 6 cell `encFin6 i` we have:
  hex.y1 = yang ↔ i.val < 3,     hex.y6 = yang  (always, since i.val < 6 < 32)
  shi    = Shi.fromIdx ⟨i.val % 3, _⟩
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.SubDispatch_BranchYaoEq

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanSelfInterp.YiInstrEnc
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  Per-j 9-instr dispatcher (one instance per fixed i)

Layout (relative to `dispatchBase`):

  +0 : pop                              — encFin6 j :: tail → cur := encFin6 j
  +1 : branchYaoEq y1 y6 (db + 3)       — fires if y1 = y6 (= yang ↔ j.val < 3)
  +2 : jump (db + 6)                    — falls through here only when j.val ≥ 3
  +3 : branchShiEq Shi.ji  off0         — j.val = 0
  +4 : branchShiEq Shi.jin off1         — j.val = 1
  +5 : jump off2                        — j.val = 2
  +6 : branchShiEq Shi.ji  off3         — j.val = 3
  +7 : branchShiEq Shi.jin off4         — j.val = 4
  +8 : jump off5                        — j.val = 5
-/

/-- A single 6-way Fin 6 dispatcher.  Pops one Cell192 from history into
    cur, then routes to one of `off0..off5` based on the popped cell's
    (y1, shi) bits, identical to flipYao sub-dispatch shape. -/
def subDispatchBranchYaoEqPerJ (dispatchBase : Nat)
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

theorem subDispatchBranchYaoEqPerJ_length (db a b c d e f : Nat) :
    (subDispatchBranchYaoEqPerJ db a b c d e f).length = 9 := rfl

/-! ## § 2  Outer i-dispatcher

Same shape as PerJ; routes to 6 per-i j-dispatcher base offsets. -/

/-- The outer i-dispatcher: same structure as PerJ, but routes to 6
    per-i j-dispatcher sub-blocks. -/
def subDispatchBranchYaoEq (dispatchBase : Nat)
    (iSubBase0 iSubBase1 iSubBase2 iSubBase3 iSubBase4 iSubBase5 : Nat)
    : List YiInstr :=
  [ YiInstr.pop
  , YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩ (dispatchBase + 3)
  , YiInstr.jump (dispatchBase + 6)
  , YiInstr.branchShiEq Shi.ji  iSubBase0
  , YiInstr.branchShiEq Shi.jin iSubBase1
  , YiInstr.jump iSubBase2
  , YiInstr.branchShiEq Shi.ji  iSubBase3
  , YiInstr.branchShiEq Shi.jin iSubBase4
  , YiInstr.jump iSubBase5 ]

theorem subDispatchBranchYaoEq_length (db a b c d e f : Nat) :
    (subDispatchBranchYaoEq db a b c d e f).length = 9 := rfl

/-! ## § 3  Helpers — yao/shi components of `encFin6 i` (per-literal)

The generic `encFin6_y1`, `encFin6_y6`, `encFin6_shi` over an arbitrary
`Fin 6` collide with `decide` because the proof component of the `Fin`
constructor becomes a metavariable under pattern matching.  We work around
this by stating one ground-decidable lemma per literal value of `i`. -/

private theorem encFin6_0_y1_eq_y6 :
    (encFin6 (0 : Fin 6)).1.y1 = (encFin6 (0 : Fin 6)).1.y6 := by decide
private theorem encFin6_0_shi : (encFin6 (0 : Fin 6)).2 = Shi.ji := by decide

private theorem encFin6_1_y1_eq_y6 :
    (encFin6 (1 : Fin 6)).1.y1 = (encFin6 (1 : Fin 6)).1.y6 := by decide
private theorem encFin6_1_shi : (encFin6 (1 : Fin 6)).2 = Shi.jin := by decide
private theorem encFin6_1_shi_ne_ji : (encFin6 (1 : Fin 6)).2 ≠ Shi.ji := by decide

private theorem encFin6_2_y1_eq_y6 :
    (encFin6 (2 : Fin 6)).1.y1 = (encFin6 (2 : Fin 6)).1.y6 := by decide
private theorem encFin6_2_shi : (encFin6 (2 : Fin 6)).2 = Shi.wei := by decide
private theorem encFin6_2_shi_ne_ji : (encFin6 (2 : Fin 6)).2 ≠ Shi.ji := by decide
private theorem encFin6_2_shi_ne_jin : (encFin6 (2 : Fin 6)).2 ≠ Shi.jin := by decide

private theorem encFin6_3_y1_ne_y6 :
    ¬ ((encFin6 (3 : Fin 6)).1.y1 = (encFin6 (3 : Fin 6)).1.y6) := by decide
private theorem encFin6_3_shi : (encFin6 (3 : Fin 6)).2 = Shi.ji := by decide

private theorem encFin6_4_y1_ne_y6 :
    ¬ ((encFin6 (4 : Fin 6)).1.y1 = (encFin6 (4 : Fin 6)).1.y6) := by decide
private theorem encFin6_4_shi : (encFin6 (4 : Fin 6)).2 = Shi.jin := by decide
private theorem encFin6_4_shi_ne_ji : (encFin6 (4 : Fin 6)).2 ≠ Shi.ji := by decide

private theorem encFin6_5_y1_ne_y6 :
    ¬ ((encFin6 (5 : Fin 6)).1.y1 = (encFin6 (5 : Fin 6)).1.y6) := by decide
private theorem encFin6_5_shi : (encFin6 (5 : Fin 6)).2 = Shi.wei := by decide
private theorem encFin6_5_shi_ne_ji : (encFin6 (5 : Fin 6)).2 ≠ Shi.ji := by decide
private theorem encFin6_5_shi_ne_jin : (encFin6 (5 : Fin 6)).2 ≠ Shi.jin := by decide

/-! ## § 4  Routing correctness for the per-J dispatcher

Six per-j routing theorems — one for each value of `j.val ∈ {0..5}`.
Fuel needed:
  j=0: 3 fuel  (pop, branchYaoEq fires, branchShiEq.ji fires)
  j=1: 4 fuel  (pop, branchYaoEq fires, branchShiEq.ji falls, branchShiEq.jin fires)
  j=2: 5 fuel  (pop, branchYaoEq fires, both branchShiEq fall, jump fires)
  j=3: 4 fuel  (pop, branchYaoEq falls, jump, branchShiEq.ji fires)
  j=4: 5 fuel
  j=5: 6 fuel
-/

/-- Routing for `j.val = 0`: lands at `off0`. -/
theorem subDispatchBranchYaoEqPerJ_routes_j0
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (off0 off1 off2 off3 off4 off5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (0 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEqPerJ 0 off0 off1 off2 off3 off4 off5
        halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = off0
    ∧ μ'.cur = encFin6 (0 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEqPerJ, Hexagram.yaoAt,
          encFin6_0_y1_eq_y6, encFin6_0_shi]

/-- Routing for `j.val = 1`: lands at `off1`. -/
theorem subDispatchBranchYaoEqPerJ_routes_j1
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (off0 off1 off2 off3 off4 off5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (1 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEqPerJ 0 off0 off1 off2 off3 off4 off5
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = off1
    ∧ μ'.cur = encFin6 (1 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEqPerJ, Hexagram.yaoAt,
          encFin6_1_y1_eq_y6, encFin6_1_shi, encFin6_1_shi_ne_ji]

/-- Routing for `j.val = 2`: lands at `off2`. -/
theorem subDispatchBranchYaoEqPerJ_routes_j2
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (off0 off1 off2 off3 off4 off5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (2 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEqPerJ 0 off0 off1 off2 off3 off4 off5
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = off2
    ∧ μ'.cur = encFin6 (2 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEqPerJ, Hexagram.yaoAt,
          encFin6_2_y1_eq_y6, encFin6_2_shi,
          encFin6_2_shi_ne_ji, encFin6_2_shi_ne_jin]

/-- Routing for `j.val = 3`: lands at `off3`. -/
theorem subDispatchBranchYaoEqPerJ_routes_j3
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (off0 off1 off2 off3 off4 off5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (3 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEqPerJ 0 off0 off1 off2 off3 off4 off5
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = off3
    ∧ μ'.cur = encFin6 (3 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEqPerJ, Hexagram.yaoAt,
          encFin6_3_y1_ne_y6, encFin6_3_shi]

/-- Routing for `j.val = 4`: lands at `off4`. -/
theorem subDispatchBranchYaoEqPerJ_routes_j4
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (off0 off1 off2 off3 off4 off5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (4 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEqPerJ 0 off0 off1 off2 off3 off4 off5
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = off4
    ∧ μ'.cur = encFin6 (4 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEqPerJ, Hexagram.yaoAt,
          encFin6_4_y1_ne_y6, encFin6_4_shi, encFin6_4_shi_ne_ji]

/-- Routing for `j.val = 5`: lands at `off5`. -/
theorem subDispatchBranchYaoEqPerJ_routes_j5
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (off0 off1 off2 off3 off4 off5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (5 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEqPerJ 0 off0 off1 off2 off3 off4 off5
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = off5
    ∧ μ'.cur = encFin6 (5 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEqPerJ, Hexagram.yaoAt,
          encFin6_5_y1_ne_y6, encFin6_5_shi,
          encFin6_5_shi_ne_ji, encFin6_5_shi_ne_jin]

/-! ## § 5  Routing correctness for the outer i-dispatcher

Same six theorems, but for `subDispatchBranchYaoEq`, routing to
`iSubBase0..iSubBase5` instead of `off0..off5`.  Identical fuel counts
because the structure is identical. -/

/-- Routing for `i.val = 0`: lands at `iSubBase0`. -/
theorem subDispatchBranchYaoEq_routes_i0
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (iSubBase0 iSubBase1 iSubBase2 iSubBase3 iSubBase4 iSubBase5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (0 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEq 0 iSubBase0 iSubBase1 iSubBase2
                                         iSubBase3 iSubBase4 iSubBase5
        halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = iSubBase0
    ∧ μ'.cur = encFin6 (0 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEq, Hexagram.yaoAt,
          encFin6_0_y1_eq_y6, encFin6_0_shi]

/-- Routing for `i.val = 1`: lands at `iSubBase1`. -/
theorem subDispatchBranchYaoEq_routes_i1
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (iSubBase0 iSubBase1 iSubBase2 iSubBase3 iSubBase4 iSubBase5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (1 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEq 0 iSubBase0 iSubBase1 iSubBase2
                                         iSubBase3 iSubBase4 iSubBase5
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = iSubBase1
    ∧ μ'.cur = encFin6 (1 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEq, Hexagram.yaoAt,
          encFin6_1_y1_eq_y6, encFin6_1_shi, encFin6_1_shi_ne_ji]

/-- Routing for `i.val = 2`: lands at `iSubBase2`. -/
theorem subDispatchBranchYaoEq_routes_i2
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (iSubBase0 iSubBase1 iSubBase2 iSubBase3 iSubBase4 iSubBase5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (2 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEq 0 iSubBase0 iSubBase1 iSubBase2
                                         iSubBase3 iSubBase4 iSubBase5
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = iSubBase2
    ∧ μ'.cur = encFin6 (2 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEq, Hexagram.yaoAt,
          encFin6_2_y1_eq_y6, encFin6_2_shi,
          encFin6_2_shi_ne_ji, encFin6_2_shi_ne_jin]

/-- Routing for `i.val = 3`: lands at `iSubBase3`. -/
theorem subDispatchBranchYaoEq_routes_i3
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (iSubBase0 iSubBase1 iSubBase2 iSubBase3 iSubBase4 iSubBase5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (3 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEq 0 iSubBase0 iSubBase1 iSubBase2
                                         iSubBase3 iSubBase4 iSubBase5
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = iSubBase3
    ∧ μ'.cur = encFin6 (3 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEq, Hexagram.yaoAt,
          encFin6_3_y1_ne_y6, encFin6_3_shi]

/-- Routing for `i.val = 4`: lands at `iSubBase4`. -/
theorem subDispatchBranchYaoEq_routes_i4
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (iSubBase0 iSubBase1 iSubBase2 iSubBase3 iSubBase4 iSubBase5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (4 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEq 0 iSubBase0 iSubBase1 iSubBase2
                                         iSubBase3 iSubBase4 iSubBase5
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = iSubBase4
    ∧ μ'.cur = encFin6 (4 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEq, Hexagram.yaoAt,
          encFin6_4_y1_ne_y6, encFin6_4_shi, encFin6_4_shi_ne_ji]

/-- Routing for `i.val = 5`: lands at `iSubBase5`. -/
theorem subDispatchBranchYaoEq_routes_i5
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (iSubBase0 iSubBase1 iSubBase2 iSubBase3 iSubBase4 iSubBase5 : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encFin6 (5 : Fin 6) :: tail
        pc := 0
        prog := subDispatchBranchYaoEq 0 iSubBase0 iSubBase1 iSubBase2
                                         iSubBase3 iSubBase4 iSubBase5
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = iSubBase5
    ∧ μ'.cur = encFin6 (5 : Fin 6)
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchYaoEq, Hexagram.yaoAt,
          encFin6_5_y1_ne_y6, encFin6_5_shi,
          encFin6_5_shi_ne_ji, encFin6_5_shi_ne_jin]

end SSBX.Foundation.Wen.MetaInterp.SubDispatch_BranchYaoEq
