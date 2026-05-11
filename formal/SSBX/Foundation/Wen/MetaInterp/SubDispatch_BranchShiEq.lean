/-
# SubDispatch_BranchShiEq — outer 4-way sub-dispatch for branchShiEq

After fetch lands branchShiEq's TAG into META.cur and leaves
`encShi s :: encNat t :: tail` on META.history, this sub-dispatcher:
  1. Pops encShi s into META.cur
  2. Routes to one of FOUR per-s sub-blocks based on cur.2

Per-s sub-blocks (left as offset parameters) handle the encNat t consumption
and final pc-update.  This is the "outer" half of branchShiEq dispatch;
the per-t inner dispatch is C.D-pending.

## Phase F.2 migration note (Cell192 → R8)

Pre-migration `Shi` was a 3-cycle `{已, 今, 未}` and the dispatcher branched
3-ways. With R8 `Shi` is a V₄ Klein 4-group `{道, 已, 今, 未}` and the
dispatcher must route 4-ways. We add an explicit `Shi.dao` arm; the
fall-through (default) target is the wei branch, with `dao` checked first.

## Layout

  +0 : pop                         — encShi s :: tail → cur := encShi s, history := tail
  +1 : branchShiEq Shi.dao daoOff  — fires if (encShi s).2 = dao
  +2 : branchShiEq Shi.ji  jiOff   — fires if s = ji
  +3 : branchShiEq Shi.jin jinOff  — fires if s = jin
  +4 : jump weiOff                 — falls through here only when s = wei

## Routing

Four per-s routing lemmas:

  * `subDispatchBranchShiEq_routes_dao` — fuel 2: pop + branchShiEq.dao fires.
  * `subDispatchBranchShiEq_routes_ji`  — fuel 3: pop + dao falls through +
                                          branchShiEq.ji fires.
  * `subDispatchBranchShiEq_routes_jin` — fuel 4: pop + dao + ji fall through +
                                          branchShiEq.jin fires.
  * `subDispatchBranchShiEq_routes_wei` — fuel 5: pop + dao + ji + jin fall
                                          through + jump fires.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.SubDispatch_BranchShiEq

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanSelfInterp.YiInstrEnc
open SSBX.Foundation.Wen.MetaInterp

/-- 5-instruction outer dispatch: pop encShi, then 4-way shi-branch
    (dao / ji / jin / wei). -/
def subDispatchBranchShiEq (daoSubOff jiSubOff jinSubOff weiSubOff : Nat) : List YiInstr :=
  [ YiInstr.pop
  , YiInstr.branchShiEq Shi.dao daoSubOff
  , YiInstr.branchShiEq Shi.ji  jiSubOff
  , YiInstr.branchShiEq Shi.jin jinSubOff
  , YiInstr.jump weiSubOff ]

theorem subDispatchBranchShiEq_length (a b c d : Nat) :
    (subDispatchBranchShiEq a b c d).length = 5 := rfl

/-- The Shi component of `encShi s` is exactly `s`.  This is the key fact
    making the outer dispatch route correctly. -/
private theorem encShi_shi (s : Shi) : (encShi s).2 = s := by
  rcases s with ⟨y, g⟩; cases y <;> cases g <;> rfl

/-! ## § 1  Routing — `s = dao`

Fuel trace (from pc = 0):
  step 0 (pop): cur := encShi dao, history := tail, pc := 1
  step 1 (branchShiEq Shi.dao daoSubOff):
    cur.2 = (encShi dao).2 = dao = dao → fires → pc := daoSubOff
-/

/-- Routing for `s = Shi.dao`: after 2 fuel steps, pc lands at `daoSubOff`. -/
theorem subDispatchBranchShiEq_routes_dao
    (curHex : Hexagram) (curShi : Shi) (tail : List R8)
    (daoSubOff jiSubOff jinSubOff weiSubOff : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encShi Shi.dao :: tail
        pc := 0
        prog := subDispatchBranchShiEq daoSubOff jiSubOff jinSubOff weiSubOff
        halted := false }
    let μ' := μ.runFuel 2
    μ'.pc = daoSubOff
    ∧ μ'.cur = encShi Shi.dao
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchShiEq, encShi_shi, Shi.dao, Shi.ji, Shi.jin]

/-! ## § 2  Routing — `s = ji`

Fuel trace (from pc = 0):
  step 0 (pop): cur := encShi ji, history := tail, pc := 1
  step 1 (branchShiEq Shi.dao daoSubOff):
    cur.2 = ji ≠ dao → falls through → pc := 2
  step 2 (branchShiEq Shi.ji jiSubOff):
    cur.2 = ji = ji → fires → pc := jiSubOff
-/

/-- Routing for `s = Shi.ji`: after 3 fuel steps, pc lands at `jiSubOff`. -/
theorem subDispatchBranchShiEq_routes_ji
    (curHex : Hexagram) (curShi : Shi) (tail : List R8)
    (daoSubOff jiSubOff jinSubOff weiSubOff : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encShi Shi.ji :: tail
        pc := 0
        prog := subDispatchBranchShiEq daoSubOff jiSubOff jinSubOff weiSubOff
        halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = jiSubOff
    ∧ μ'.cur = encShi Shi.ji
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchShiEq, encShi_shi, Shi.dao, Shi.ji, Shi.jin]

/-! ## § 3  Routing — `s = jin`

Fuel trace (from pc = 0):
  step 0 (pop): cur := encShi jin, history := tail, pc := 1
  step 1 (branchShiEq Shi.dao daoSubOff):
    cur.2 = jin ≠ dao → falls through → pc := 2
  step 2 (branchShiEq Shi.ji jiSubOff):
    cur.2 = jin ≠ ji → falls through → pc := 3
  step 3 (branchShiEq Shi.jin jinSubOff):
    cur.2 = jin = jin → fires → pc := jinSubOff
-/

/-- Routing for `s = Shi.jin`: after 4 fuel steps, pc lands at `jinSubOff`. -/
theorem subDispatchBranchShiEq_routes_jin
    (curHex : Hexagram) (curShi : Shi) (tail : List R8)
    (daoSubOff jiSubOff jinSubOff weiSubOff : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encShi Shi.jin :: tail
        pc := 0
        prog := subDispatchBranchShiEq daoSubOff jiSubOff jinSubOff weiSubOff
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = jinSubOff
    ∧ μ'.cur = encShi Shi.jin
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchShiEq, encShi_shi, Shi.dao, Shi.ji, Shi.jin]

/-! ## § 4  Routing — `s = wei`

Fuel trace (from pc = 0):
  step 0 (pop): cur := encShi wei, history := tail, pc := 1
  step 1 (branchShiEq Shi.dao daoSubOff):
    cur.2 = wei ≠ dao → falls through → pc := 2
  step 2 (branchShiEq Shi.ji jiSubOff):
    cur.2 = wei ≠ ji → falls through → pc := 3
  step 3 (branchShiEq Shi.jin jinSubOff):
    cur.2 = wei ≠ jin → falls through → pc := 4
  step 4 (jump weiSubOff):
    pc := weiSubOff
-/

/-- Routing for `s = Shi.wei`: after 5 fuel steps, pc lands at `weiSubOff`. -/
theorem subDispatchBranchShiEq_routes_wei
    (curHex : Hexagram) (curShi : Shi) (tail : List R8)
    (daoSubOff jiSubOff jinSubOff weiSubOff : Nat) :
    let μ : YiState :=
      { cur := (curHex, curShi)
        history := encShi Shi.wei :: tail
        pc := 0
        prog := subDispatchBranchShiEq daoSubOff jiSubOff jinSubOff weiSubOff
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = weiSubOff
    ∧ μ'.cur = encShi Shi.wei
    ∧ μ'.history = tail
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          subDispatchBranchShiEq, encShi_shi, Shi.dao, Shi.ji, Shi.jin, Shi.wei]

end SSBX.Foundation.Wen.MetaInterp.SubDispatch_BranchShiEq
