/-
# MetaInterp — YiInstr 通用元解释器（构造中）

目标：建造 `metaInterpProg : List YiInstr` 满足
`KleeneInternal.UniversalInterpSpec metaInterpProg`，从而 discharge
`KleeneCarrier.universalInterpExists` 公理。

## 文件位置（roadmap）

- **Phase A** (foundation): 本文件 — state layout helpers / Shi-tagged
  encoding 之 Lean 端定义 + decoding 函数 + round-trip lemmas
- **Phase A.2-A.4**: prologue / counted-loop combinator / skip-one-instr
  （拆出独立文件或后续追加）
- **Phase B** (per-opcode): 12 个 executeBlock + fetch + dispatch + writeback
  （subagent 并行）
- **Phase C** (integration): metaStep_simulates_step + UniversalInterpSpec

## 编码约束（cuo-equivariance ceiling）

YiInstr 之 12 指令**无法构造绝对的 Hexagram 值**——只有 cur 之 transform
（hu/cuo/zong/flipYao）+ Shi 之绝对设置（setShi）。runtime cur 之初值是
输入 h，编译期未知。故所有 register cells 之 Hex 部分必依赖于初始 cur，
仅 Shi 部分可绝对控制。

→ 所有 register 之**类型标签**用 Shi 编码：
  - `Shi.jin` = data unit（一格 = +1 计数）
  - `Shi.wei` = end-marker / running-flag
  - `Shi.ji`  = halted-flag

→ register cell 之 Hex 部分**未指定**（依输入而变）；下游 fetch logic
  通过 Shi tag + 位置（counted-pop）区分 region。这套 encoding 自然
  满足 cuo-不变性（Shi 与 Hex.cuo 正交）。

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

## META.cur 之角色

**Loop 不变**：META.cur ≡ sim.cur（直接镜像，无编码开销）。
6 个 cur-变换指令（hu/cuo/zong/flipYao/setShi）可直接在 META.cur 上
执行——天然实现 sim 之同名指令。

仅在 fetch/dispatch/execute 临时（中间步骤）期间，META.cur 被借用作
scratch（放 tag、读取参数等）；execute 结束前必须恢复为 sim.step.cur。
-/
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Bagua.KleeneInternal

namespace SSBX.Foundation.Wen.MetaInterp

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.WenyanSelfInterp

/-! ## § 1 Shi-tagged register cells -/

/-- Pc/simhist-len data unit cell：Shi.jin，Hex 任意. -/
def regDataCell (h : Hexagram) : Cell192 := (h, Shi.jin)

/-- End-marker cell：Shi.wei. -/
def regMarkerCell (h : Hexagram) : Cell192 := (h, Shi.wei)

/-- Halted-flag = halted: Shi.ji. -/
def haltedTrueCell (h : Hexagram) : Cell192 := (h, Shi.ji)

/-- Halted-flag = running: Shi.wei. -/
def haltedFalseCell (h : Hexagram) : Cell192 := (h, Shi.wei)

/-! ## § 2 Counter-encoding (Nat ↔ List of Shi.jin cells + Shi.wei marker) -/

/-- Encode a Nat counter as `n` data cells + 1 end-marker.  All `n+1`
    cells share the same Hex (the `h` parameter); only Shi distinguishes. -/
def encCounter (h : Hexagram) (n : Nat) : List Cell192 :=
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
    Returns `(count, rest_after_marker)` or `none` if no marker found. -/
def decCounter : List Cell192 → Option (Nat × List Cell192)
  | [] => none
  | (_, Shi.jin) :: rest =>
      match decCounter rest with
      | some (n, tail) => some (n + 1, tail)
      | none => none
  | (_, Shi.wei) :: rest => some (0, rest)
  | (_, Shi.ji) :: _ => none  -- unexpected: ji not used in counters

theorem decCounter_encCounter (h : Hexagram) (n : Nat) (tail : List Cell192) :
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
    wei = running (false), jin = unexpected (return none). -/
def decHaltedFlag (c : Cell192) : Option Bool :=
  match c.2 with
  | Shi.ji  => some true
  | Shi.wei => some false
  | Shi.jin => none

theorem decHaltedFlag_haltedTrue (h : Hexagram) :
    decHaltedFlag (haltedTrueCell h) = some true := rfl

theorem decHaltedFlag_haltedFalse (h : Hexagram) :
    decHaltedFlag (haltedFalseCell h) = some false := rfl

/-- Encode a Bool halted-flag as a single cell. -/
def encHaltedFlag (h : Hexagram) (b : Bool) : Cell192 :=
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
def encMetaHistory (regHex : Hexagram) (sim : YiState) : List Cell192 :=
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

/-! ## § 8 Decode helpers — DEFERRED to Phase B

  The full `decMetaHistory : List Cell192 → Option (...)` plus its round-trip
  with `encMetaHistory` will be needed when we prove per-opcode simulation
  lemmas in Phase B (each executeBlock's behavior is stated in terms of
  decoded sim-state).

  Deferring here is intentional: the encoding side (§§ 1–4) is stable and
  enough for Phase A.2-A.4 (prologue, counted-loop combinator, skip-instr
  subroutine).  The decoding + round-trip will be added when Phase B
  actually consumes them, to avoid speculative API design.
-/

end SSBX.Foundation.Wen.MetaInterp
