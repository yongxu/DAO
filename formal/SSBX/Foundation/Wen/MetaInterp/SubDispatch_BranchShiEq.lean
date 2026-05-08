/-
# SubDispatch_BranchShiEq — outer 3-way sub-dispatch for branchShiEq

After fetch lands branchShiEq's TAG into META.cur and leaves
`encShi s :: encNat t :: tail` on META.history, this sub-dispatcher:
  1. Pops encShi s into META.cur
  2. Routes to one of three per-s sub-blocks based on cur.2

Per-s sub-blocks (left as offset parameters) handle the encNat t consumption
and final pc-update.  This is the "outer" half of branchShiEq dispatch;
the per-t inner dispatch is C.D-pending.

## Layout

  +0 : pop                         — encShi s :: tail → cur := encShi s, history := tail
  +1 : branchShiEq Shi.ji  jiOff   — fires if (encShi s).2 = ji  (i.e. s = ji)
  +2 : branchShiEq Shi.jin jinOff  — fires if s = jin
  +3 : jump weiOff                 — falls through here only when s = wei

## Routing

Three per-s routing lemmas:

  * `subDispatchBranchShiEq_routes_ji`  — fuel 2: pop + branchShiEq.ji  fires.
  * `subDispatchBranchShiEq_routes_jin` — fuel 3: pop + branchShiEq.ji  falls
                                          through + branchShiEq.jin fires.
  * `subDispatchBranchShiEq_routes_wei` — fuel 4: pop + both branches fall
                                          through + jump fires.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.SubDispatch_BranchShiEq

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanSelfInterp.YiInstrEnc
open SSBX.Foundation.Wen.MetaInterp

/-- 4-instruction outer dispatch: pop encShi, then 3-way shi-branch. -/
def subDispatchBranchShiEq (jiSubOff jinSubOff weiSubOff : Nat) : List YiInstr :=
  [ YiInstr.pop
  , YiInstr.branchShiEq Shi.ji  jiSubOff
  , YiInstr.branchShiEq Shi.jin jinSubOff
  , YiInstr.jump weiSubOff ]

theorem subDispatchBranchShiEq_length (a b c : Nat) :
    (subDispatchBranchShiEq a b c).length = 4 := rfl

/-- The Shi component of `encShi s` is exactly `s`.  This is the key fact
    making the outer dispatch route correctly. -/
private theorem encShi_shi (s : Shi) : (encShi s).2 = s := by
  cases s <;> rfl

/-! ## § 1  Routing — `s = ji`

Fuel trace (from pc = 0):
  step 0 (pop): cur := encShi ji, history := tail, pc := 1
  step 1 (branchShiEq Shi.ji jiSubOff):
    cur.2 = (encShi ji).2 = ji = ji → fires → pc := jiSubOff
-/

/-- Routing for `s = Shi.ji`: after 2 fuel steps, pc lands at `jiSubOff`. -/
theorem subDispatchBranchShiEq_routes_ji
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (jiSubOff jinSubOff weiSubOff : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encShi Shi.ji :: tail
        pc := 0
        prog := subDispatchBranchShiEq jiSubOff jinSubOff weiSubOff
        halted := false }
    let μ' := μ.runFuel 2
    μ'.pc = jiSubOff
    ∧ μ'.cur = encShi Shi.ji
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchShiEq, encShi_shi]

/-! ## § 2  Routing — `s = jin`

Fuel trace (from pc = 0):
  step 0 (pop): cur := encShi jin, history := tail, pc := 1
  step 1 (branchShiEq Shi.ji jiSubOff):
    cur.2 = jin ≠ ji → falls through → pc := 2
  step 2 (branchShiEq Shi.jin jinSubOff):
    cur.2 = jin = jin → fires → pc := jinSubOff
-/

/-- Routing for `s = Shi.jin`: after 3 fuel steps, pc lands at `jinSubOff`. -/
theorem subDispatchBranchShiEq_routes_jin
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (jiSubOff jinSubOff weiSubOff : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encShi Shi.jin :: tail
        pc := 0
        prog := subDispatchBranchShiEq jiSubOff jinSubOff weiSubOff
        halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = jinSubOff
    ∧ μ'.cur = encShi Shi.jin
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchShiEq, encShi_shi]

/-! ## § 3  Routing — `s = wei`

Fuel trace (from pc = 0):
  step 0 (pop): cur := encShi wei, history := tail, pc := 1
  step 1 (branchShiEq Shi.ji jiSubOff):
    cur.2 = wei ≠ ji → falls through → pc := 2
  step 2 (branchShiEq Shi.jin jinSubOff):
    cur.2 = wei ≠ jin → falls through → pc := 3
  step 3 (jump weiSubOff):
    pc := weiSubOff
-/

/-- Routing for `s = Shi.wei`: after 4 fuel steps, pc lands at `weiSubOff`. -/
theorem subDispatchBranchShiEq_routes_wei
    (curHex : Hexagram) (curShi : Shi) (tail : List Cell192)
    (jiSubOff jinSubOff weiSubOff : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encShi Shi.wei :: tail
        pc := 0
        prog := subDispatchBranchShiEq jiSubOff jinSubOff weiSubOff
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = weiSubOff
    ∧ μ'.cur = encShi Shi.wei
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchShiEq, encShi_shi]

end SSBX.Foundation.Wen.MetaInterp.SubDispatch_BranchShiEq
