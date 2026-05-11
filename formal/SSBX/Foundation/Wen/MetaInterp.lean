/-
# MetaInterp — YiInstr 通用元解释器（构造中）

最终 full target：建造 `metaInterpProg : List YiInstr` 满足
`KleeneInternal.UniversalInterpSpec metaInterpProg`，从而为
`KleeneInternal.UniversalInterpExists` 提供具体 witness。当前 Phase 1
的可执行靶由 `MetaInterp/TargetContract.lean` 固定。

## 文件位置（roadmap）

- **Phase A** (foundation): 本文件 — state layout helpers / Shi-tagged
  encoding 之 Lean 端定义 + decoding 函数 + round-trip lemmas
- **Phase A.2-A.4**: prologue / counted-loop combinator / skip-one-instr
  （拆出独立文件或下一阶段追加）
- **Phase B** (per-opcode): 12 个 executeBlock + fetch + dispatch + writeback
  （subagent 并行）
- **Phase C** (integration): metaStep_simulates_step + UniversalInterpSpec

`MetaInterp/TargetContract.lean` 固定 Phase 1 证明靶：Lean 先定义
bounded/full universal-interpreter target 与 framed-input 工程 lane；文言
程序随后只作为 Lean 检查的 witness，不作为根证明系统。

## 编码约束（complement-equivariance ceiling）

YiInstr 之 12 指令**无法构造绝对的 Hexagram 值**——只有 cur 之 transform
（interlace/complement/reverse/flipYao）+ Shi 之绝对设置（setShi）。runtime cur 之初值是
输入 h，编译期未知。故所有 register cells 之 Hex 部分必依赖于初始 cur，
仅 Shi 部分可绝对控制。

→ 所有 register 之**类型标签**用 Shi 编码：
  - `Shi.jin` = data unit（一格 = +1 计数）
  - `Shi.wei` = end-marker / running-flag
  - `Shi.ji`  = halted-flag

→ register cell 之 Hex 部分**未指定**（依输入而变）；下游 fetch logic
  通过 Shi tag + 位置（counted-pop）区分 region。这套 encoding 自然
  满足 complement-不变性（Shi 与 Hex.complement 正交）。

## META.history 布局（top → bottom，pop 取头）

```
[pc-data × pc]                       (each Shi.jin)
[pc-end-marker]                      (Shi.wei)
[halted-flag]                        (Shi.ji=halted | Shi.wei=running)
[simhist-len-data × |sim.history|]   (each Shi.jin)
[simhist-len-end-marker]             (Shi.wei)
[sim.history cells]                  (raw, Shi 任意)
[encProg sim.prog]                   (raw, read-only after prologue)
```

## Phase F.2 migration note (Cell192 → Cell256)

This file migrates from `Cell192` (3-state Z/3 Shi `{已, 今, 未}`) to `Cell256`
(V₄ Klein 4-state Shi `{道, 已, 今, 未}`). The encoding-tag conventions used
here only reference `Shi.jin / Shi.wei / Shi.ji`; the new identity element
`Shi.dao` is reserved (not consumed by counter / halted-flag encoding) but is
admissible as an "unexpected" case in `decCounter` / `decHaltedFlag`.

## META.cur 之角色

**Loop 不变**：META.cur ≡ sim.cur（直接镜像，无编码开销）。
6 个 cur-变换指令（interlace/complement/reverse/flipYao/setShi）可直接在 META.cur 上
执行——天然实现 sim 之同名指令。

仅在 fetch/dispatch/execute 临时（中间步骤）期间，META.cur 被借用作
scratch（放 tag、读取参数等）；execute 结束前必须恢复为 sim.step.cur。
-/
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Bagua.KleeneInternal

namespace SSBX.Foundation.Wen.MetaInterp

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Bagua.GodelLi
open SSBX.Foundation.Wen.WenyanSelfInterp

/-! ## § 1 Shi-tagged register cells -/

/-- Pc/simhist-len data unit cell：Shi.jin，Hex 任意. -/
def regDataCell (h : Hexagram) : Cell256 := (h, Shi.jin)

/-- End-marker cell：Shi.wei. -/
def regMarkerCell (h : Hexagram) : Cell256 := (h, Shi.wei)

/-- Halted-flag = halted: Shi.ji. -/
def haltedTrueCell (h : Hexagram) : Cell256 := (h, Shi.ji)

/-- Halted-flag = running: Shi.wei. -/
def haltedFalseCell (h : Hexagram) : Cell256 := (h, Shi.wei)

/-! ## § 2 Counter-encoding (Nat ↔ List of Shi.jin cells + Shi.wei marker) -/

/-- Encode a Nat counter as `n` data cells + 1 end-marker.  All `n+1`
    cells share the same Hex (the `h` parameter); only Shi distinguishes. -/
def encCounter (h : Hexagram) (n : Nat) : List Cell256 :=
  List.replicate n (regDataCell h) ++ [regMarkerCell h]

theorem encCounter_length (h : Hexagram) (n : Nat) :
    (encCounter h n).length = n + 1 := by
  unfold encCounter
  simp [List.length_replicate]

theorem encCounter_zero (h : Hexagram) :
    encCounter h 0 = [regMarkerCell h] := by
  unfold encCounter
  rfl

theorem encCounter_succ (h : Hexagram) (n : Nat) :
    encCounter h (n + 1) = regDataCell h :: encCounter h n := by
  unfold encCounter
  simp [List.replicate]

/-- Decode a counter prefix: count Shi.jin cells until first Shi.wei.
    Returns `(count, rest_after_marker)` or `none` if no marker found.

    Phase F.2: V₄ Shi adds `Shi.dao` (V₄ identity); like `Shi.ji`, it is not
    used in the counter encoding — appearance ⇒ `none` (decode error). -/
def decCounter : List Cell256 → Option (Nat × List Cell256)
  | [] => none
  | (_, Shi.jin) :: rest =>
      match decCounter rest with
      | some (n, tail) => some (n + 1, tail)
      | none => none
  | (_, Shi.wei) :: rest => some (0, rest)
  | (_, Shi.ji) :: _ => none  -- unexpected: ji not used in counters
  | (_, Shi.dao) :: _ => none -- unexpected: dao (V₄ identity) not used in counters

theorem decCounter_encCounter (h : Hexagram) (n : Nat) (tail : List Cell256) :
    decCounter (encCounter h n ++ tail) = some (n, tail) := by
  induction n with
  | zero =>
    rw [encCounter_zero]
    show decCounter ((h, Shi.wei) :: tail) = some (0, tail)
    rfl
  | succ k ih =>
    rw [encCounter_succ]
    show decCounter ((h, Shi.jin) :: (encCounter h k ++ tail)) = some (k + 1, tail)
    unfold decCounter
    rw [ih]

/-! ## § 3 Halted-flag encoding -/

/-- Decode the halted flag from a single cell: ji = halted (true),
    wei = running (false), jin = unexpected (return none).

    Phase F.2: V₄ Shi adds `Shi.dao` (V₄ identity); like `Shi.jin`, it is not
    a halted-flag encoding — appearance ⇒ `none` (decode error). -/
def decHaltedFlag (c : Cell256) : Option Bool :=
  match c.2 with
  | Shi.ji  => some true
  | Shi.wei => some false
  | Shi.jin => none
  | Shi.dao => none

theorem decHaltedFlag_haltedTrue (h : Hexagram) :
    decHaltedFlag (haltedTrueCell h) = some true := rfl

theorem decHaltedFlag_haltedFalse (h : Hexagram) :
    decHaltedFlag (haltedFalseCell h) = some false := rfl

/-- Encode a Bool halted-flag as a single cell. -/
def encHaltedFlag (h : Hexagram) (b : Bool) : Cell256 :=
  if b then haltedTrueCell h else haltedFalseCell h

theorem decHaltedFlag_encHaltedFlag (h : Hexagram) (b : Bool) :
    decHaltedFlag (encHaltedFlag h b) = some b := by
  cases b
  · exact decHaltedFlag_haltedFalse h
  · exact decHaltedFlag_haltedTrue h

/-! ## § 4 META.history 完整布局 -/

/-- Encode the META-history for a given simulated state.

    Layout (top → bottom of the returned list):
    ```
    pc-data × pc | pc-marker
    halted-flag
    simhist-len-data × |simhist| | simhist-len-marker
    sim.history (raw)
    encProg sim.prog (raw)
    ```

    `regHex` is the Hex value used for register cells (don't-care from
    the spec's perspective; in practice, this is the runtime `cur.1`
    threaded through the prologue, but for Lean-level reasoning we
    parameterize). -/
def encMetaHistory (regHex : Hexagram) (sim : YiState) : List Cell256 :=
  encCounter regHex sim.pc ++
  [encHaltedFlag regHex sim.halted] ++
  encCounter regHex sim.history.length ++
  sim.history ++
  ProgEnc.encProg sim.prog

theorem encMetaHistory_length (regHex : Hexagram) (sim : YiState) :
    (encMetaHistory regHex sim).length =
      sim.pc + 1 + 1 + (sim.history.length + 1) + sim.history.length +
      (ProgEnc.encProg sim.prog).length := by
  unfold encMetaHistory
  simp [List.length_append, List.length_cons,
        encCounter_length]
  omega

/-! ## § 5 META state: full layout (cur + history) -/

/-- Complete META-state corresponding to a simulated `YiState`, given a
    chosen register-Hex value `regHex` and a chosen meta-cur (which by
    convention is `sim.cur`, the direct mirror).

    META.cur = sim.cur  (direct mirror; central trick).
    META.history = encMetaHistory regHex sim. -/
def metaStateOf (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (metaPc : Nat) : YiState :=
  { cur     := sim.cur
    history := encMetaHistory regHex sim
    pc      := metaPc
    prog    := metaProg
    halted  := false }  -- META always running unless we explicitly halt it

/-! ## § 6 Prologue program

  The prologue is the first segment of `metaInterpProg`.  Starting from
  `META.cur := (h, jin)` and `META.history := encProg P` (i.e., from
  `RunWith h metaInterpProg (encProg P)`), the prologue's job is to
  prepend three end-marker cells (Shi.wei) representing:

    pc-end-marker (pc = 0, no data cells before it)
    halted-flag (running, encoded as Shi.wei)
    simhist-len-end-marker (simhist-len = 0)

  ...so that after the prologue, `META.history` matches
  `encMetaHistory h (YiState.init h P)`, ready for the fetch loop.

  The prologue trivially preserves `META.cur.1 = h` (no Hex modification);
  it temporarily sets `META.cur.2 := wei` then restores to `jin` so
  `META.cur = (h, jin) = (YiState.init h P).cur`.
-/

/-- Prologue: a 5-instruction sequence that converts an initial
    `RunWith h metaInterpProg (encProg P)` state into the META encoding
    of `YiState.init h P`. -/
def prologueProg : List YiInstr :=
  [ YiInstr.setShi Shi.wei  -- META.cur.2 := wei
  , YiInstr.push             -- pc-end-marker
  , YiInstr.push             -- halted-flag (still wei = running)
  , YiInstr.push             -- simhist-len-end-marker
  , YiInstr.setShi Shi.jin   -- restore META.cur.2 := jin (= sim.cur.2)
  ]

theorem prologueProg_length : prologueProg.length = 5 := rfl

/-! ### § 6.1 Prologue correctness

  After 5 fuel steps from the initial RunWith state, the META state
  matches `metaStateOf h (YiState.init h P) prologueProg 5`. -/

/-- The exact state after running the prologue 5 fuel steps. -/
private def afterPrologue (h : Hexagram) (P : List YiInstr) : YiState :=
  ((RunWith h prologueProg (ProgEnc.encProg P)).runFuel 5)

theorem afterPrologue_cur (h : Hexagram) (P : List YiInstr) :
    (afterPrologue h P).cur = (h, Shi.jin) := by
  unfold afterPrologue
  rfl

theorem afterPrologue_history (h : Hexagram) (P : List YiInstr) :
    (afterPrologue h P).history =
      [(h, Shi.wei), (h, Shi.wei), (h, Shi.wei)] ++ ProgEnc.encProg P := by
  unfold afterPrologue
  rfl

theorem afterPrologue_pc (h : Hexagram) (P : List YiInstr) :
    (afterPrologue h P).pc = 5 := by
  unfold afterPrologue
  rfl

theorem afterPrologue_halted (h : Hexagram) (P : List YiInstr) :
    (afterPrologue h P).halted = false := by
  unfold afterPrologue
  rfl

theorem afterPrologue_prog (h : Hexagram) (P : List YiInstr) :
    (afterPrologue h P).prog = prologueProg := by
  unfold afterPrologue
  rfl

/-- **Main correctness**: after the prologue, META.history matches
    `encMetaHistory h (YiState.init h P)`. -/
theorem afterPrologue_history_eq_encMetaHistory
    (h : Hexagram) (P : List YiInstr) :
    (afterPrologue h P).history = encMetaHistory h (YiState.init h P) := by
  rw [afterPrologue_history]
  -- encMetaHistory h (init h P) = encCounter h 0 ++ [encHaltedFlag h false]
  --                              ++ encCounter h 0 ++ [] ++ encProg P
  -- encCounter h 0 = [regMarkerCell h] = [(h, wei)]
  -- encHaltedFlag h false = haltedFalseCell h = (h, wei)
  unfold encMetaHistory
  show [(h, Shi.wei), (h, Shi.wei), (h, Shi.wei)] ++ ProgEnc.encProg P
       = encCounter h (YiState.init h P).pc
         ++ [encHaltedFlag h (YiState.init h P).halted]
         ++ encCounter h (YiState.init h P).history.length
         ++ (YiState.init h P).history
         ++ ProgEnc.encProg (YiState.init h P).prog
  -- YiState.init h P has pc = 0, halted = false, history = [], prog = P
  show [(h, Shi.wei), (h, Shi.wei), (h, Shi.wei)] ++ ProgEnc.encProg P
       = encCounter h 0
         ++ [encHaltedFlag h false]
         ++ encCounter h 0
         ++ []
         ++ ProgEnc.encProg P
  rw [encCounter_zero]
  show [(h, Shi.wei), (h, Shi.wei), (h, Shi.wei)] ++ ProgEnc.encProg P
       = [regMarkerCell h]
         ++ [encHaltedFlag h false]
         ++ [regMarkerCell h]
         ++ []
         ++ ProgEnc.encProg P
  -- regMarkerCell h = (h, wei), encHaltedFlag h false = (h, wei)
  unfold regMarkerCell encHaltedFlag haltedFalseCell
  simp

/-! ## § 7 Counted-loop combinator

  A reusable building block for fetch / writeback / skip-instr blocks.
  Wraps a `body : List YiInstr`; assumes the **counter** (n × Shi.jin
  data cells + 1 × Shi.wei marker) is at the top of META.history at
  loop-start.  Executes body exactly n times, then advances past loop_end.

  ## Layout (in YiInstr)
  ```
  offset+0:           pop                          ← consume next counter cell
  offset+1:           branchShiEq Shi.wei exitOffset  ← if marker, exit
  offset+2..body:     body                         ← user-provided
  offset+2+bodyLen:   jump offset                  ← back to top
  exitOffset = offset+2+bodyLen+1                  ← past the jump
  ```

  ## Constraints

  - `offset` must equal the `pc` at which countedLoop is placed in the
    surrounding meta-program (jumps are absolute, so the combinator must
    know its own location).
  - `body`'s effect on `META.cur` is ephemeral: each iteration, the next
    `pop` overwrites cur with the new counter cell.  Body should
    side-effect META.history (push results) for any non-cur outputs.
  - Body must NOT modify the bottom of history (the counter's tail / rest
    of META.history below the counter).
  - Body must terminate; total fuel for one loop iteration =
    `body_fuel + 3` (1 pop + 1 branch + body + 1 jump).

  ## What's NOT yet proven

  The simulation lemma `countedLoop_simulates_n_iterations` (induction on n)
  is left for Phase B — it requires per-block reasoning about body's effect
  on the encoded state.  The combinator's structural properties (length,
  PC-offset arithmetic) are established here.
-/

/-- Counted-loop combinator: pop-test-body-jump pattern.
    Counter (Shi.jin × n + Shi.wei × 1) at top of history is consumed;
    body is executed n times; on marker, falls through to past loop_end. -/
def countedLoop (offset : Nat) (body : List YiInstr) : List YiInstr :=
  let bodyLen := body.length
  let exitOffset := offset + 2 + bodyLen + 1
  [ YiInstr.pop
  , YiInstr.branchShiEq Shi.wei exitOffset ] ++
  body ++
  [ YiInstr.jump offset ]

theorem countedLoop_length (offset : Nat) (body : List YiInstr) :
    (countedLoop offset body).length = body.length + 3 := by
  unfold countedLoop
  simp [List.length_append, List.length_cons, List.length_nil]

theorem countedLoop_first_instr (offset : Nat) (body : List YiInstr) :
    (countedLoop offset body)[0]? = some YiInstr.pop := by
  unfold countedLoop
  rfl

theorem countedLoop_second_instr (offset : Nat) (body : List YiInstr) :
    (countedLoop offset body)[1]? =
      some (YiInstr.branchShiEq Shi.wei (offset + 2 + body.length + 1)) := by
  unfold countedLoop
  rfl

/-- The exit offset of the loop = past the jump-back instruction.
    Useful for proving program-composition lemmas. -/
def countedLoop_exitOffset (offset : Nat) (body : List YiInstr) : Nat :=
  offset + 2 + body.length + 1

theorem countedLoop_exitOffset_eq_length (offset : Nat) (body : List YiInstr) :
    countedLoop_exitOffset offset body = offset + (countedLoop offset body).length := by
  unfold countedLoop_exitOffset
  rw [countedLoop_length]
  omega

/-! ### § 7.1 Simulation lemma — empty-body specialization

  We prove the counted-loop simulation lemma for the SPECIALIZED case
  `body = []`.  This is the simplest interesting case — an empty body
  means the loop just consumes the counter — and it is the workhorse
  building block for the **fetch-pc-decoding** part of Phase B (where
  the body is non-trivial; this lemma deliberately leaves that outside
  its scope).

  ### Why specialize to empty body

  For non-empty body, the simulation lemma has to be parametric in
  body's effect — body is allowed to push results into history, modify
  cur, etc.  That parametrization requires either (a) a full
  per-instruction Hoare-style refinement layer, or (b) restricting body
  to a class of "non-disturbing" prefixes.  Both are Phase B engineering;
  the empty-body case is Phase A and discharges all combinator-side
  arithmetic (PC offsets, fuel formula, branch arithmetic).

  ### What's proven here

  Given the META state at the entry of `countedLoop offset []` with
  `history = encCounter regHex n ++ tail`, after exactly `3*n + 2`
  fuel steps we land at the exit:

    pc       := offset + 3                 (= countedLoop_exitOffset)
    history  := tail                       (counter fully consumed)
    cur      := (regHex, Shi.wei)          (last popped marker cell)
    halted   := false
    prog     := metaProg                   (unchanged)

  The hypothesis `MetaProgHasEmptyCountedLoopAt offset metaProg` says
  the three instruction slots `offset`, `offset+1`, `offset+2` of
  `metaProg` look exactly like `countedLoop offset []`.

  ### Roadmap for the general case

  For non-empty `body`, the lemma generalizes to:

    runFuel ((body_fuel + 3) * n + 2) inputState = exitState

  where `body_fuel` is body's per-iteration fuel, and `exitState.cur` /
  the upper portion of `exitState.history` are determined by an
  abstract `body_effect : YiState → YiState` hypothesized to obey:

    (H1) body, started from `cur := (regHex, Shi.jin)` and
         `history := encCounter regHex n ++ tail` and `pc := offset+2`,
         after `body_fuel` steps lands at `pc := offset+2+body.length`,
         with `halted = false` and the bottom portion of history
         (below the counter) untouched.

  With (H1) the proof is the obvious analogue of the empty-body case.
-/

/-- The three instruction slots of an empty-body countedLoop placed at
    `offset` inside `metaProg`.  Used as the structural hypothesis for
    `countedLoop_empty_simulates_n_iterations`. -/
def MetaProgHasEmptyCountedLoopAt (offset : Nat) (metaProg : List YiInstr) : Prop :=
  metaProg[offset]?     = some YiInstr.pop ∧
  metaProg[offset + 1]? = some (YiInstr.branchShiEq Shi.wei (offset + 3)) ∧
  metaProg[offset + 2]? = some (YiInstr.jump offset)

/-- Helper: the META state on entry to one invocation of `countedLoop`
    with empty body.  `cur` is arbitrary (left as a parameter — body's
    initial `cur` is irrelevant since the first instruction is `pop`,
    which overwrites it). -/
def countedLoopEmptyEntryState (offset : Nat) (metaProg : List YiInstr)
    (cur : Cell256) (regHex : Hexagram) (n : Nat) (tail : List Cell256) : YiState :=
  { cur     := cur
  , history := encCounter regHex n ++ tail
  , pc      := offset
  , prog    := metaProg
  , halted  := false }

/-- Helper: the expected META state after the empty-body loop completes. -/
def countedLoopEmptyExitState (offset : Nat) (metaProg : List YiInstr)
    (regHex : Hexagram) (tail : List Cell256) : YiState :=
  { cur     := (regHex, Shi.wei)
  , history := tail
  , pc      := offset + 3
  , prog    := metaProg
  , halted  := false }

/-- Auxiliary: `runFuel` is additive in the fuel argument.  Follows from
    `runFuel_succ_right` by induction on `n`. -/
private theorem runFuel_add (s : YiState) (m n : Nat) :
    s.runFuel (m + n) = (s.runFuel m).runFuel n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : s.runFuel (m + (k + 1)) = (s.runFuel (m + k)).step := by
      have : m + (k + 1) = (m + k) + 1 := by omega
      rw [this, runFuel_succ_right]
    have h2 : (s.runFuel m).runFuel (k + 1) = ((s.runFuel m).runFuel k).step :=
      runFuel_succ_right _ _
    rw [h1, h2, ih]

/-- **Counted-loop simulation, empty-body specialization**.

    Starting from a META state at `pc = offset`, with the counter
    `encCounter regHex n ++ tail` at the top of history, exactly
    `3 * n + 2` fuel steps suffice to reach the loop's exit.

    The proof is by induction on `n`.  Each iteration with `n+1` data
    cells consumes the head data cell in 3 steps (pop, branch-not-taken,
    jump-back) and reduces to the `n`-cell case.  The base case (`n=0`)
    consumes the marker cell in 2 steps (pop, branch-taken). -/
theorem countedLoop_empty_simulates_n_iterations
    (offset : Nat) (metaProg : List YiInstr)
    (h_loop : MetaProgHasEmptyCountedLoopAt offset metaProg)
    (cur : Cell256) (regHex : Hexagram) (n : Nat) (tail : List Cell256) :
    (countedLoopEmptyEntryState offset metaProg cur regHex n tail).runFuel (3 * n + 2)
      = countedLoopEmptyExitState offset metaProg regHex tail := by
  obtain ⟨h_pop, h_branch, h_jump⟩ := h_loop
  induction n generalizing cur with
  | zero =>
    -- Fuel = 2.  history starts with [(regHex, Shi.wei)] ++ tail.
    -- Step 1 (pop): cur := (regHex, wei), history := tail, pc := offset+1.
    -- Step 2 (branchShiEq wei (offset+3)): cur.2 = wei, taken → pc := offset+3.
    show (countedLoopEmptyEntryState offset metaProg cur regHex 0 tail).runFuel 2
        = countedLoopEmptyExitState offset metaProg regHex tail
    -- Unfold one step at a time using runFuel_succ_right.
    have hstep1 :
        (countedLoopEmptyEntryState offset metaProg cur regHex 0 tail).step =
          { cur := (regHex, Shi.wei)
          , history := tail
          , pc := offset + 1
          , prog := metaProg
          , halted := false } := by
      unfold countedLoopEmptyEntryState YiState.step
      simp [encCounter_zero, regMarkerCell, h_pop, YiState.execute]
    have hstep2 :
        ({ cur := (regHex, Shi.wei)
         , history := tail
         , pc := offset + 1
         , prog := metaProg
         , halted := false } : YiState).step =
          countedLoopEmptyExitState offset metaProg regHex tail := by
      unfold countedLoopEmptyExitState YiState.step
      simp [h_branch, YiState.execute]
    -- runFuel 2 s = ((runFuel 0 s).step).step = s.step.step.
    -- Use the right-expansion view: runFuel (n+1) s = (runFuel n s).step.
    have h2 :
        (countedLoopEmptyEntryState offset metaProg cur regHex 0 tail).runFuel 2 =
          ((countedLoopEmptyEntryState offset metaProg cur regHex 0 tail).step).step := by
      rw [show (2 : Nat) = 1 + 1 from rfl,
          runFuel_succ_right, runFuel_succ_right]
      rfl
    rw [h2, hstep1, hstep2]
  | succ k ih =>
    -- Fuel = 3 * (k+1) + 2 = 3*k + 5 = 3 + (3*k + 2).
    -- After 3 steps, state = entry state for k.
    show (countedLoopEmptyEntryState offset metaProg cur regHex (k + 1) tail).runFuel
            (3 * (k + 1) + 2)
        = countedLoopEmptyExitState offset metaProg regHex tail
    have hfuel : 3 * (k + 1) + 2 = 3 + (3 * k + 2) := by omega
    rw [hfuel, runFuel_add]
    -- Show: after 3 steps, we're at the entry state for k.
    have hstep1 :
        (countedLoopEmptyEntryState offset metaProg cur regHex (k + 1) tail).step =
          { cur := (regHex, Shi.jin)
          , history := encCounter regHex k ++ tail
          , pc := offset + 1
          , prog := metaProg
          , halted := false } := by
      unfold countedLoopEmptyEntryState YiState.step
      simp [encCounter_succ, regDataCell, h_pop, YiState.execute]
    have hstep2 :
        ({ cur := (regHex, Shi.jin)
         , history := encCounter regHex k ++ tail
         , pc := offset + 1
         , prog := metaProg
         , halted := false } : YiState).step =
          { cur := (regHex, Shi.jin)
          , history := encCounter regHex k ++ tail
          , pc := offset + 2
          , prog := metaProg
          , halted := false } := by
      unfold YiState.step
      simp [h_branch, YiState.execute, Shi.jin, Shi.wei]
    have hstep3 :
        ({ cur := (regHex, Shi.jin)
         , history := encCounter regHex k ++ tail
         , pc := offset + 2
         , prog := metaProg
         , halted := false } : YiState).step =
          countedLoopEmptyEntryState offset metaProg (regHex, Shi.jin) regHex k tail := by
      unfold countedLoopEmptyEntryState YiState.step
      simp [h_jump, YiState.execute]
    -- Compose the three steps to compute runFuel 3.
    have h3 :
        (countedLoopEmptyEntryState offset metaProg cur regHex (k + 1) tail).runFuel 3 =
          countedLoopEmptyEntryState offset metaProg (regHex, Shi.jin) regHex k tail := by
      rw [show (3 : Nat) = 2 + 1 from rfl, runFuel_succ_right,
          show (2 : Nat) = 1 + 1 from rfl, runFuel_succ_right, runFuel_succ_right]
      -- now goal: ((entry.runFuel 0).step.step).step = entry-for-k
      change (((countedLoopEmptyEntryState offset metaProg cur regHex (k + 1) tail).step).step).step
              = countedLoopEmptyEntryState offset metaProg (regHex, Shi.jin) regHex k tail
      rw [hstep1, hstep2, hstep3]
    rw [h3]
    exact ih (regHex, Shi.jin)

/-! ## § 8 Decode helpers — DEFERRED to Phase B

  The full `decMetaHistory : List Cell256 → Option (...)` plus its round-trip
  with `encMetaHistory` will be needed when we prove per-opcode simulation
  lemmas in Phase B (each executeBlock's behavior is stated in terms of
  decoded sim-state).

  Deferring here is intentional: the encoding side (§§ 1–4) is stable and
  enough for Phase A.2-A.4 (prologue, counted-loop combinator, skip-instr
  subroutine).  The decoding + round-trip will be added when Phase B
  actually consumes them, to avoid speculative API design.
-/

end SSBX.Foundation.Wen.MetaInterp
