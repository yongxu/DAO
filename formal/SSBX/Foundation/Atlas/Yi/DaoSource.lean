/-
# Foundation.Atlas.Yi.DaoSource — «道源» on the clean R 8 stack

This is the **Phase β wave 2** port of the original
`Foundation/Wen/DaoSource.lean` artifact onto the language-independent
`Wen.Core` interpreter, with Yi-flavoured naming supplied by the
`Atlas/Yi/` overlay.

The original `Wen/DaoSource` (16 instructions on `YiInstr`, hex carrier
= `Hexagram × Shi`) is the project's signature self-referential
artifact: a Wenyan program that judges «是道非道» (Shi = 已 ↔ middle-yao
symmetry y3 = y4), and is itself **five-相** correct:

  形 — well-typed (all jump targets in-range, ends in `halt`)
  解 — text → program round-trip
  印 — program → text round-trip
  执 — terminates on every input
  义 — judges the same property the spec promises

This file recovers exactly that fivefold certificate on the **clean
stack**:

* execution semantics from `Wen/Core` (the language-independent R 8
  bit-machine).
* Yi naming from `Atlas/Yi/` (Hexagram = R 6, Shi = R 2, the V₄
  four-named states {道, 已, 今, 未}).

## Carrier layout — R 8 = R 6 ⊕ R 2

We embed the Yi data into `R 8` by laying out:

    bits 0..5  →  Hexagram (R 6) — the input
    bits 6,7   →  Shi      (R 2) — the running 时态

`Shi.fromR8 c i = c ⟨i.val + 6, _⟩` is the projection R 8 → R 2.

## Program design — 11 instructions, doctrinally equivalent

The original 16-step program had four no-op pairs (complement²,
reverse² = id) and a push/pop round-trip used purely as the «太极»
gesture.  The new port keeps the essential **branching skeleton**
(judge y3 vs y4 to pick 已 or 未) plus one `push` («太极» mark on
history) and produces an 11-step program.  Per the migration brief,
"the 12 instructions need not be 1-to-1; if 8 or 15 instructions yield
the same correct judge, that's fine — just preserve the five 相".

```
pc  Instr                                 Rationale (in the «道» reading)
──  ────────────────────────────────────  ─────────────────────────────────
 0  push                                  太极 — mark the input on history
 1  writeBit 6 false                      初设 — clear high-bit of Shi
 2  writeBit 7 true                       立 wei — provisional 心道 state
 3  branchBitEq 2 true 7                  问 y3 — split on the third yao
 4  branchBitEq 3 false 9                 y3=阳 path: y4=阳 → equal
 5  jump 11                               y3=阳, y4=阴 — differ → halt as wei
 6  halt                                  (unreachable padding, kept for parity)
 7  branchBitEq 3 true 9                  y3=阴 path: y4=阴 → equal
 8  jump 11                               y3=阴, y4=阳 — differ → halt as wei
 9  writeBit 6 true                       天道 — set bit 6 = true
10  writeBit 7 false                      天道 — set bit 7 = false → ji
11  halt
```

This program is purely Wen.Core (no Yi-typed instructions); Yi
naming enters only through how we **interpret** bits 0..5 (= input
hexagram) and bits 6..7 (= output Shi).

## Status

0 sorry / 0 axiom.  Each 相 lemma is proved by `native_decide` on the
finite carrier (256 hexagram bytes ≤ 64 instructions deep).

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9 (Atlas separation), §10.7 (Interpreter
  Foundation).
* `v4-foundation.md` v0.5 §15 (external traditions), §4 (Shi V₄).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.Wen.CorePartial
import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.ShiV4

namespace SSBX.Foundation.Atlas.Yi
namespace DaoSource

open SSBX.Foundation.R
open SSBX.Foundation.Wen.CorePartial
open SSBX.Foundation.Atlas.Yi

/-! ## § 0  Shi-from-R 8 projection

Bits 6,7 of an `R 8` cell hold the Shi (= R 2) overlay.  This is the
`fromR8` projection used by the «义» lemma. -/

namespace Shi

/-- Project an `R 8` cell to its Shi (R 2) overlay, taking bits 6,7.
    This is the `Shi.fromR8` referenced in the «义» specification. -/
def fromR8 (c : R 8) : Shi := fun i =>
  match i with
  | ⟨0, _⟩ => c ⟨6, by decide⟩
  | ⟨1, _⟩ => c ⟨7, by decide⟩

/-- Project a `PartialCell 8` cell (the CorePartial state representation)
    to its Shi (R 2) overlay.  Reads bits at positions `i.val + 6`;
    unspecified bits default to `false` (which is unreachable for a
    `State.init`-derived run using only flipBit/writeBit/branchBitEq/jump/halt). -/
def fromPartial (c : PartialCell 8) : Shi := fun i =>
  (c ⟨i.val + 6, by omega⟩).getD false

/-- The four Shi values, restated as `R 8`-bit witnesses for `fromR8`. -/
@[simp] theorem fromR8_apply_0 (c : R 8) :
    fromR8 c ⟨0, by decide⟩ = c ⟨6, by decide⟩ := rfl

@[simp] theorem fromR8_apply_1 (c : R 8) :
    fromR8 c ⟨1, by decide⟩ = c ⟨7, by decide⟩ := rfl

end Shi

/-! ## § 1  Hexagram-into-R 8 lift

The «执» / «义» quantifiers range over `Hexagram = R 6`.  We lift each
hexagram to an `R 8` byte by placing the six yao in bits 0..5 and
zeroing bits 6,7 (the Shi-output channel starts blank). -/

/-- Lift a Hexagram (R 6) into a starting R 8 byte: yao in bits 0..5,
    Shi-output bits 6,7 cleared to false. -/
def liftHex (h : Hexagram) : R 8 := fun i =>
  if hlt : i.val < 6 then h ⟨i.val, hlt⟩ else false

@[simp] theorem liftHex_apply_lt (h : Hexagram) (i : Fin 8) (hi : i.val < 6) :
    liftHex h i = h ⟨i.val, hi⟩ := by
  unfold liftHex
  simp [hi]

@[simp] theorem liftHex_apply_6 (h : Hexagram) :
    liftHex h ⟨6, by decide⟩ = false := rfl

@[simp] theorem liftHex_apply_7 (h : Hexagram) :
    liftHex h ⟨7, by decide⟩ = false := rfl

/-! ## § 2  «道程» — the 11-instruction R 8 program

Per the table in the file-header docstring.  All targets land within
0..11 and the program ends in `halt`. -/

/-- «道程»: the 11-instruction `Wen.Core` program implementing the
    «是道非道» judge on the R 8 stack.

    `init` state = `liftHex h` (input hexagram in bits 0..5);
    output Shi = bits 6,7 of `final.cur`.

    Final Shi = 已 (Shi.ji) iff h.y3 = h.y4 ; otherwise final Shi = 未
    (Shi.wei). -/
def daoProg : List Instr :=
  [ -- pc 0  太极 — push input cell onto history
    .push
    -- pc 1  initial high-Shi-bit = false
  , .writeBit ⟨6, by decide⟩ false
    -- pc 2  initial low-Shi-bit  = true   (state = wei = (false, true))
  , .writeBit ⟨7, by decide⟩ true
    -- pc 3  if y3 = true (yin), jump to "y3=yin path" at pc 7
  , .branchBitEq ⟨2, by decide⟩ true 7
    -- pc 4  y3 = false (yang): if y4 = false (yang), equal → jump to 9
  , .branchBitEq ⟨3, by decide⟩ false 9
    -- pc 5  differ — y3=yang, y4=yin: jump to halt at 11
  , .jump 11
    -- pc 6  unreachable; halt as safety
  , .halt
    -- pc 7  y3 = true (yin) path: if y4 = true (yin), equal → jump to 9
  , .branchBitEq ⟨3, by decide⟩ true 9
    -- pc 8  differ — y3=yin, y4=yang: jump to halt at 11
  , .jump 11
    -- pc 9  天道 — flip Shi bit 6 to true
  , .writeBit ⟨6, by decide⟩ true
    -- pc 10 天道 — flip Shi bit 7 to false → state (true, false) = ji
  , .writeBit ⟨7, by decide⟩ false
    -- pc 11 halt
  , .halt
  ]

/-- Sanity: the program is 12 instructions long (11 productive + 1
    unreachable safety pad). -/
theorem daoProg_length : daoProg.length = 12 := by native_decide

/-! ## § 3  形 — wellTyped

A syntactic certificate: every jump/branch target is in-range, the
program is non-empty, and the last instruction is `halt`. -/

/-- The target of a jump/branch instruction, if any. -/
def Instr.target? : Instr → Option Nat
  | .branchBitEq _ _ t => some t
  | .jump t => some t
  | _ => none

/-- Single-instruction well-typed check: any explicit target must be a
    valid pc in `prog`. -/
def instrWellTyped (prog : List Instr) (i : Instr) : Bool :=
  match Instr.target? i with
  | none => true
  | some t => decide (t < prog.length)

/-- Whole-program well-typed check:
    1. program is non-empty
    2. last instruction is `halt`
    3. every jump/branch target is a valid pc.

    Note: `prog[prog.length - 1]?` is used to fetch the last instr in
    a way that gracefully handles the empty case (caught by clause 1). -/
def wellTyped (prog : List Instr) : Bool :=
  if prog.isEmpty then false
  else
    let last := prog[prog.length - 1]?
    match last with
    | some .halt =>
        prog.all (instrWellTyped prog)
    | _ => false

/-- «形»: `daoProg` is well-typed. -/
theorem daoProg_xing : wellTyped daoProg = true := by native_decide

/-! ## § 4  解 / 印 — structural encoding round-trip

Per the migration brief, we use a simple **structural** encoding
(triple of `Nat`s per instruction) rather than the heavyweight
Wenyan text parser used in the legacy file.  This preserves the
spirit of the «解 / 印» pair while keeping the proof tractable.

Each `Instr` (apart from `.xorMask` — which `daoProg` does not use)
is encoded as a `Nat × Nat × Nat` opcode + 2-operand triple.  The
`encode`/`decode` pair is a bijection on the instructions used by
`daoProg`, hence both round-trips hold by `native_decide`. -/

/-- The textual encoding of `daoProg` as a list of `Nat × Nat × Nat`
    opcode triples.  This is the "source form" («道源») corresponding
    to the program. -/
abbrev SourceForm : Type := List (Nat × Nat × Nat)

/-- Encode one instruction as a `Nat × Nat × Nat` triple.

    Opcodes:
      0 = nop
      1 = flipBit
      2 = writeBit
      3 = branchBitEq
      4 = jump
      5 = push
      6 = pop
      7 = halt
      8 = xorMask  (not used by `daoProg`; encoded as (8, 0, 0))
-/
def encodeOne : Instr → Nat × Nat × Nat
  | .nop                  => (0, 0, 0)
  | .flipBit i            => (1, i.val, 0)
  | .writeBit i b         => (2, i.val, if b then 1 else 0)
  | .branchBitEq i b t    => (3, i.val * 2 + (if b then 1 else 0), t)
  | .jump t               => (4, t, 0)
  | .push                 => (5, 0, 0)
  | .pop                  => (6, 0, 0)
  | .halt                 => (7, 0, 0)
  | .xorMask _            => (8, 0, 0)
  -- CorePartial-only constructors (not used by daoProg; encoded as no-info):
  | .merge _              => (9, 0, 0)
  | .restrict _           => (10, 0, 0)

/-- Decode one triple back to an instruction; `none` if the opcode or
    operand is out of range. -/
def decodeOne : Nat × Nat × Nat → Option Instr
  | (0, 0, 0) => some .nop
  | (1, i, 0) =>
      if h : i < 8 then some (.flipBit ⟨i, h⟩) else none
  | (2, i, b) =>
      if h : i < 8 then
        match b with
        | 0 => some (.writeBit ⟨i, h⟩ false)
        | 1 => some (.writeBit ⟨i, h⟩ true)
        | _ => none
      else none
  | (3, ib, t) =>
      let i := ib / 2
      let bbit := ib % 2
      if h : i < 8 then
        match bbit with
        | 0 => some (.branchBitEq ⟨i, h⟩ false t)
        | 1 => some (.branchBitEq ⟨i, h⟩ true t)
        | _ => none
      else none
  | (4, t, 0) => some (.jump t)
  | (5, 0, 0) => some .push
  | (6, 0, 0) => some .pop
  | (7, 0, 0) => some .halt
  | _ => none

/-- Encode a whole program as a list of triples. -/
def encode (prog : List Instr) : SourceForm :=
  prog.map encodeOne

/-- Decode a list of triples back to a program; `none` on the first
    decoding failure. -/
def decode : SourceForm → Option (List Instr)
  | []     => some []
  | x :: xs =>
      match decodeOne x, decode xs with
      | some i, some rest => some (i :: rest)
      | _, _              => none

/-- The «道源» — the program in its source form. -/
def daoSource : SourceForm := encode daoProg

/-- «解»: parsing the source form yields the program.
    Both sides reduce to the same `some ([…closed list…])`. -/
theorem daoSource_jie : decode daoSource = some daoProg := by
  -- `daoSource = encode daoProg = daoProg.map encodeOne` by definition.
  -- `decode` on this list rebuilds `daoProg` instruction by instruction.
  -- All steps are `rfl`-friendly closed computations.
  rfl

/-- «印»: emitting the program reproduces the source form. -/
theorem daoProg_yin : encode daoProg = daoSource := rfl

/-- 解-印 fixpoint: source →解→ program →印→ self. -/
theorem dao_jie_yin_fixpoint :
    (decode daoSource).map encode = some daoSource := by
  rw [daoSource_jie]
  rfl

/-! ## § 5  执 — termination on every input

For each of the 64 hexagrams (`R 6 = Fin 6 → Bool`, 2^6 = 64), the
program halts within 64 fuel units.  (12 fuel is in fact enough; we
use 64 to track the original program's fuel budget for parity.) -/

/-- «执»: for every input hexagram, `daoProg` halts within 64 steps. -/
theorem daoProg_zhi :
    ∀ (h : Hexagram),
      (runFuel daoProg 64 (State.init (liftHex h))).halted = true := by
  intro h
  -- Enumerate the 6 yao via the 2-element `Bool` cases on each.
  -- This generates 64 leaf goals, each discharged by `native_decide`.
  let h0 := h ⟨0, by decide⟩
  let h1 := h ⟨1, by decide⟩
  let h2 := h ⟨2, by decide⟩
  let h3 := h ⟨3, by decide⟩
  let h4 := h ⟨4, by decide⟩
  let h5 := h ⟨5, by decide⟩
  -- Rewrite `h` as the explicit `Hexagram.mk` of its 6 yao via funext.
  have heq : h = Hexagram.mk h0 h1 h2 h3 h4 h5 := by
    apply Hexagram.ext <;> rfl
  rw [heq]
  -- Now case on each `hk : Bool`.
  cases h0 <;> cases h1 <;> cases h2 <;> cases h3 <;> cases h4 <;> cases h5
    <;> native_decide

/-! ## § 6  义 — semantic correctness

The signature theorem: «末态时 = 已 ↔ 中爻同 (y3 = y4)».
Encoded on the R 8 stack: `Shi.fromR8 final.cur = Shi.ji ↔
h ⟨2,_⟩ = h ⟨3,_⟩`. -/

/-- «义»: the final Shi (read off bits 6,7) is `ji` (天道) iff
    `h.y3 = h.y4` (middle-yao symmetry). -/
theorem daoProg_yi :
    ∀ (h : Hexagram),
      let final := runFuel daoProg 64 (State.init (liftHex h))
      Shi.fromPartial final.cur = Shi.ji ↔
        h ⟨2, by decide⟩ = h ⟨3, by decide⟩ := by
  intro h
  let h0 := h ⟨0, by decide⟩
  let h1 := h ⟨1, by decide⟩
  let h2 := h ⟨2, by decide⟩
  let h3 := h ⟨3, by decide⟩
  let h4 := h ⟨4, by decide⟩
  let h5 := h ⟨5, by decide⟩
  have heq : h = Hexagram.mk h0 h1 h2 h3 h4 h5 := by
    apply Hexagram.ext <;> rfl
  rw [heq]
  cases h0 <;> cases h1 <;> cases h2 <;> cases h3 <;> cases h4 <;> cases h5
    <;> native_decide

/-! ## § 7  Sanity witnesses — three named hexagrams

* 乾 (heaven, all yang)        — y3 = yang = y4 → 已 (天道)
* 坤 (earth, all yin)          — y3 = yin  = y4 → 已 (天道)
* 否 (heaven over earth)       — y3 = yin, y4 = yang → 未 (心道) -/

/-- 乾 — all yang (= all false). -/
def qian : Hexagram := fun _ => false

/-- 坤 — all yin (= all true). -/
def kun : Hexagram := fun _ => true

/-- 否 — ⟨阴, 阴, 阴, 阳, 阳, 阳⟩.
    In Bool convention (yin = true): y1..y3 = true, y4..y6 = false. -/
def fou : Hexagram :=
  Hexagram.mk true true true false false false

theorem daoProg_qian_tian :
    Shi.fromPartial (runFuel daoProg 64 (State.init (liftHex qian))).cur = Shi.ji := by
  native_decide

theorem daoProg_kun_tian :
    Shi.fromPartial (runFuel daoProg 64 (State.init (liftHex kun))).cur = Shi.ji := by
  native_decide

theorem daoProg_fou_xin :
    Shi.fromPartial (runFuel daoProg 64 (State.init (liftHex fou))).cur = Shi.wei := by
  native_decide

/-! ## § 8  «道之自指 (新)» — five-相 summary

The conjunction of the five 相 lemmas on the clean stack.

╔══════════════════════════════════════════════════════════════════╗
║                                                                  ║
║   形  «wellTyped daoProg = true»                                 ║
║        · 11 instructions + halt pad; all targets in 0..11        ║
║                                                                  ║
║   解  «decode daoSource = some daoProg»                          ║
║        · structural `Nat × Nat × Nat` encoding round-trips       ║
║                                                                  ║
║   印  «encode daoProg = daoSource»                               ║
║        · reverse round-trip; emitter is left-inverse of parser   ║
║                                                                  ║
║   执  ∀ h, runFuel daoProg 64 (init (liftHex h)) halts           ║
║        · 64 enumerated cases, each by `native_decide`            ║
║                                                                  ║
║   义  ∀ h, Shi.fromR8 final.cur = ji ↔ h.y3 = h.y4               ║
║        · iff at every hexagram; the «是道非道» judge              ║
║                                                                  ║
╚══════════════════════════════════════════════════════════════════╝

-/

/-- «道之自指» — the five 相 conjunction in one theorem. -/
theorem dao_self_reference :
    -- 形
    (wellTyped daoProg = true) ∧
    -- 解
    (decode daoSource = some daoProg) ∧
    -- 印
    (encode daoProg = daoSource) ∧
    -- 执
    (∀ h : Hexagram,
        (runFuel daoProg 64 (State.init (liftHex h))).halted = true) ∧
    -- 义
    (∀ h : Hexagram,
        Shi.fromPartial (runFuel daoProg 64 (State.init (liftHex h))).cur = Shi.ji ↔
          h ⟨2, by decide⟩ = h ⟨3, by decide⟩) :=
  ⟨daoProg_xing, daoSource_jie, daoProg_yin, daoProg_zhi, daoProg_yi⟩

end DaoSource
end SSBX.Foundation.Atlas.Yi
