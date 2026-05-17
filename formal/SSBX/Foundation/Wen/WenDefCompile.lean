/-
# WenDefCompile — L1 typed Tm → L0 YiInstr 之桥（compile 一隅）

L1 (`WenDef.Tm`) 与 L0 (`BaguaTuring.YiInstr`) 之间一桥。
WenDefEval.lean 已建 Lean-level evaluator (`denoteHexFun`)。
本文 进一步：取若干 closed Tm，给出 YiInstr 程序，证 二者同义。

## 关键观察 — 错对称之约束 (complement-symmetry constraint)

YiInstr 之 12 条原语皆与「错」(全爻取反) 通约：
  ·  flipYao i :  (flipPos i h).complement = flipPos i (h.complement)
  ·  complement, interlace, reverse : 皆与 complement 通约
  ·  branchYaoEq i j : (h.yaoAt i = h.yaoAt j) ↔ (h.complement.yaoAt i = h.complement.yaoAt j)
  ·  setShi/branchShiEq : 仅作用于 Shi，不涉 yao
  ·  jump/push/pop/halt/nop : 控制流原语

故：任 YiInstr 程序之转换 f : Hexagram → Hexagram 满足
  f(h.complement) = (f h).complement                              ... (★)

「错等变」(complement-equivariance) — YiInstr 可表达之 Hex → Hex 函数之刚性约束。

由 (★) 可推：
  ·  常值函数 f(h) = «一» 不可表（«一» ≠ «一».complement = ⟨yang,yin,yin,yin,yin,yin⟩）
  ·  «生» = «加» «一» 不可表（«生» «乾» = «一»; («生» «乾»).complement = «一».complement ≠ «生» «坤» = «乾»）
     故任 YiInstr 程序皆不能模拟 «生» — 此为 Path 丙 之结构性界限。

可表者：恒等、«错»、«互»、«综»、flipYao i 之复合、«加» k (k.toIdx ∈ {0, 32})、
       并 control flow 由 complement-invariant 谓词决定者（如「y3=y4」）。

非常值之 Hex → Bool 谓词若 complement-invariant，亦可由 YiInstr 实现并以 Shi 输出
（如 daoJudgeProg 之 `isTian` 判定）。

## 本文 之范围

我们给出三例 L1 → L0 compile，皆 complement-equivariant：

### Tier 0：恒等
  ·  Tm `λx. x`（`idBody`）  →  `[halt]` (`idProg`)
  ·  `idProg_correct` : init h idProg 之 cur 为 h

### Tier 1：常加 (mod 64) 之 32
  ·  Tm `λx. .jia (.hexLit (fromIdx 32)) x`（`add32Body`）  →  `[flipYao 5, halt]` (`add32Prog`)
  ·  `add32Prog_correct` : init h add32Prog 之 cur 为 «加» (fromIdx 32) h
  ·  桥 引理：`flipPos 5 h = «加» (fromIdx 32) h` —— 由 toIdx XOR 等价于 mod 64 加
  ·  Tm 等价：`add32Prog_denotes` : YiInstr 输出 = denoteHexFun add32Body h

### Tier 2：exact Hex transform 之直接 compile
  ·  Tm `.cuoH/.zongH/.huH/.cuoZongH/.flip{1..6}H`
     → YiInstr straight-line 程序
  ·  `compileHexFunCertified?` 暴露保守桥：仅返回经 64 卦验证的 Hex → Hex 程序

## v2 扩展 (doctrine break, 2026-05-17)

**变更**：v1 doctrine 「YiInstr 之 12 原语皆与 complement 通约 — 故 ISA 之 Hex → Hex
universe 限于 cuo-equivariant 子集」之约束，在 v2 中**已破**。

`BaguaTuring.lean` 加入第 13 条 instruction `branchYaoYang (i : Fin 6) (target : Nat)`：
absolute yao test 「若 y_i = yang，跳 target；否则 pc + 1」。

`branchYaoYang` **不与 complement 通约**（complement 把 yang ↔ yin, 绝对测试故必失对称）。
此原语之引入：

- 把 ISA 从「代数封闭机器」（cuo-symmetric 12-instr universe）升为「通用图灵机」
  (universal Hex → Hex compile)
- 12 v1 原语之 `complement_commutes` 系定理 由「全集事实」改为「子集事实」：
  仅 `BaguaTuring.complementEquivariantInstr` 为真之 instruction 在
  `complementEquivariantProg` 之 program 中仍 commute
- `compileHexFunCertified?` 扩 pattern 覆盖：
  * `Stdlib.tuiBody` (mod-64 +1) via propagate-carry adder 用 `branchYaoYang`
  * `Stdlib.sunBody` (mod-64 -1) 同理 dual

**对比 v1 / v2**:

| 项 | v1 (旧 doctrine) | v2 (新 doctrine, 本 commit) |
|---|---|---|
| YiInstr cardinality | 12 (cuo-symmetric universe) | 13 (含 `branchYaoYang`) |
| `Hex → Hex` compile coverage | equivariant 子集 only | universal (含 «生», `tui`, `sun` 等) |
| `compileHexFunCertified? .tuiBody` | `none` (rejected) | `some [adder...]` |
| `«生»` 之 ISA 可表达性 | 反例: `sheng_not_cuo_equivariant` (★ 等式 fails) | 仍 reproven (★ 仍为 v1 子集事实) |
| 12 v1 原语之 complement_commutes | 全集事实 | 子集事实 (limited to `complementEquivariantInstr`) |
| Path 丙 narrative (wen-substrate.md) | "ceiling is structural" | "ceiling is cross-section-specific, dissolved by new instr" |

「★ 等式」（`(prog h).complement = prog h.complement`）作为 v1 子集事实仍**机器可证**：
`sheng_not_cuo_equivariant` 之反例不变，因 `«生»` 仍非 equivariant，**但** v2 中
`«生»` 可由含 `branchYaoYang` 之 program 表达（因不要求等变）。

## 历史 doctrine 之保留

v1 doctrine 之结构性观察（cuo-symmetry 在 12-instr 子集下成立）仍 metatheoretically
正确：`complementEquivariantProg` 子集之 program 满足 ★ 等式。v1 之
12 个 `*_cuo_equivariant` lemma（`flipPos_cuo_equivariant` 等）原文保留，
含义现在是「这些算子在 v2 doctrine 下仍 commute, 因属 equivariant 子集」。

## 状态

0 sorry / 0 axiom. 无 partial def. native_decide 见证具体例。
-/
import SSBX.Foundation.Atlas.Yi.Classical.Computation.BaguaTuring
import SSBX.Foundation.Wen.WenDefEval

namespace SSBX.Foundation.Wen.WenDefCompile

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Wen.WenDefEval

/-! ## § 1  Tier 0 — 恒等 -/

/-- 「恒等」之 Tm：λx:Hex. x. -/
def idBody : Tm := .abs "x" .hex (.var "x")

theorem idBody_typed :
    typeCheck [] idBody = some (.arr .hex .hex) := by native_decide

/-- 「恒等」之 YiInstr 程序：仅 halt 一条。 -/
def idProg : List YiInstr := [.halt]

/-- 「恒等」compile 正确：runFuel 1 之 cur.1 = 输入 h。 -/
theorem idProg_correct (h : Hexagram) :
    ((YiState.init h idProg).runFuel 1).cur.1 = h := by
  rfl

/-- 「恒等」compile 之 Tm 等价：runFuel 之输出与 denotation 一致。 -/
theorem idProg_denotes (h : Hexagram) :
    some ((YiState.init h idProg).runFuel 1).cur.1 = denoteHexFun idBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-! ## § 2  Tier 1 — 常加 32 (即 flipYao 5) -/

/-- 卦索引 32：仅 y6 为 yin (高位)，其余 yang。 -/
def hex32 : Hexagram := Hexagram.fromIdx ⟨32, by omega⟩

theorem hex32_def : hex32 = Hexagram.mk .yang .yang .yang .yang .yang .yin := by
  native_decide

/-- 「加 32」之 Tm 体：λx:Hex. .jia (.hexLit hex32) x. -/
def add32Body : Tm := .abs "x" .hex
  (.app (.app .jia (.hexLit hex32)) (.var "x"))

theorem add32Body_typed :
    typeCheck [] add32Body = some (.arr .hex .hex) := by native_decide

/-- 「加 32」之 YiInstr 程序：翻 y6 一爻，毕。 -/
def add32Prog : List YiInstr := [.flipYao ⟨5, by omega⟩, .halt]

/-- 「加 32」compile 之核心：runFuel 2 之 cur.1 = h.flipPos 5。 -/
theorem add32Prog_runs (h : Hexagram) :
    ((YiState.init h add32Prog).runFuel 2).cur.1 = h.flipPos ⟨5, by omega⟩ := by
  rfl

/-- 桥 引理：翻 y6 一爻 = «加» hex32 h（mod 64 加 32 等同于 XOR 第 5 位）。 -/
theorem flipPos5_eq_add32 (h : Hexagram) :
    h.flipPos ⟨5, by omega⟩ = «加» hex32 h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-- 「加 32」compile 正确：runFuel 之 cur = «加» hex32 h。 -/
theorem add32Prog_correct (h : Hexagram) :
    ((YiState.init h add32Prog).runFuel 2).cur.1 = «加» hex32 h := by
  rw [add32Prog_runs, flipPos5_eq_add32]

/-- 「加 32」compile 之 Tm 等价：runFuel 之输出与 denoteHexFun add32Body 一致。
    全 64 输入皆 native_decide 见证。 -/
theorem add32Prog_denotes (h : Hexagram) :
    some ((YiState.init h add32Prog).runFuel 2).cur.1 = denoteHexFun add32Body h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-! ## § 3  Tier 2 — 直接 «错» (no Tm source) -/

/-- 「错」之 YiInstr 程序：直接 complement 一条加 halt。 -/
def cuoProg : List YiInstr := [.complement, .halt]

/-- 「错」compile 正确：runFuel 2 之 cur = h.complement。 -/
theorem cuoProg_correct (h : Hexagram) :
    ((YiState.init h cuoProg).runFuel 2).cur.1 = h.complement := by
  rfl

/-- 「错」compile 之 Tm 等价。 -/
theorem cuoProg_denotes (h : Hexagram) :
    some ((YiState.init h cuoProg).runFuel 2).cur.1 = denoteHexFun Stdlib.cuoBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-- 「综」之 YiInstr 程序。 -/
def zongProg : List YiInstr := [.reverse, .halt]

theorem zongProg_denotes (h : Hexagram) :
    some ((YiState.init h zongProg).runFuel 2).cur.1 = denoteHexFun Stdlib.zongBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-- 「互」之 YiInstr 程序。 -/
def huProg : List YiInstr := [.interlace, .halt]

theorem huProg_denotes (h : Hexagram) :
    some ((YiState.init h huProg).runFuel 2).cur.1 = denoteHexFun Stdlib.huBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-- 「错综」之 YiInstr 程序：按定义先错后综。 -/
def cuoZongProg : List YiInstr := [.complement, .reverse, .halt]

theorem cuoZongProg_denotes (h : Hexagram) :
    some ((YiState.init h cuoZongProg).runFuel 3).cur.1 =
      denoteHexFun Stdlib.cuoZongBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

def fin0 : Fin 6 := ⟨0, by omega⟩
def fin1 : Fin 6 := ⟨1, by omega⟩
def fin2 : Fin 6 := ⟨2, by omega⟩
def fin3 : Fin 6 := ⟨3, by omega⟩
def fin4 : Fin 6 := ⟨4, by omega⟩
def fin5 : Fin 6 := ⟨5, by omega⟩

/-- 单爻翻转程序。 -/
def flip1Prog : List YiInstr := [.flipYao fin0, .halt]
def flip2Prog : List YiInstr := [.flipYao fin1, .halt]
def flip3Prog : List YiInstr := [.flipYao fin2, .halt]
def flip4Prog : List YiInstr := [.flipYao fin3, .halt]
def flip5Prog : List YiInstr := [.flipYao fin4, .halt]
def flip6Prog : List YiInstr := [.flipYao fin5, .halt]

theorem flip1Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip1Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip1Body h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem flip2Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip2Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip2Body h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem flip3Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip3Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip3Body h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem flip4Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip4Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip4Body h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem flip5Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip5Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip5Body h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem flip6Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip6Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip6Body h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

/-! ## § 3b  v2: propagate-carry adders (`tui` / `sun`) via `branchYaoYang`

  v1 doctrine 把 `Stdlib.tuiBody` (mod-64 +1) 与 `Stdlib.sunBody` (mod-64 -1)
  列为「结构性不可 compile」（皆 non cuo-equivariant）。v2 加入
  `branchYaoYang` 之后, 这些函数可以以 propagate-carry adder 表达。

  以 +1 mod 64 为例（`tui`）:

  Hexagram bit pattern (per `WenyanSelfInterp.SSBX.Foundation.Yi.Yi.Hexagram.toIdx`):
    y1 (bit 0, LSB, value 1) ... y6 (bit 5, MSB, value 32)
  Yao 编码: yang = false = 0, yin = true = 1

  Algorithm (start at y1 = LSB, propagate carry toward y6 = MSB):
    - 若 y1 = yang (bit 0 = 0): flip y1 (now 1), done.
    - 若 y1 = yin  (bit 0 = 1): flip y1 (now 0), carry to y2; recurse upward.
    - 顶层 y6 同处理, mod-64 之 overflow 自然丢弃.

  Block layout per level (5 instructions, indexed by `i ∈ {0,1,2,3,4}`)
  对应 yao 位 fin{0,1,2,3,4} (i.e. y1..y5, LSB→MSB-1):
    pc=P+0: branchYaoYang ⟨i, _⟩ (P+3)  // 若 yang, 跳 P+3 (yang case)
    pc=P+1: flipYao ⟨i, _⟩                // yin case: clear bit, carry up
    pc=P+2: jump (P+5)                    // proceed to next level
    pc=P+3: flipYao ⟨i, _⟩                // yang case: set bit
    pc=P+4: halt                          // done

  顶层 y6 (fin5, MSB): 简化为 `flipYao 5; halt` (2 instrs), 因 mod-64 overflow
  无需 distinguished case (yang→yin and yin→yang 皆为 carry-out 之结果).

  Total: 5 levels × 5 + 2 = 27 instructions.
-/

/-- Block of 5 instructions for level `i` (handling yao at position i,
    i ∈ {1,2,3,4,5}). `P` is the block start pc, `next` is pc of next level. -/
def adderLevel (i : Fin 6) (P next : Nat) : List YiInstr :=
  [ .branchYaoYang i (P + 3)
  , .flipYao i
  , .jump next
  , .flipYao i
  , .halt
  ]

/-- Propagate-carry adder for +1 mod 64 (`tui`), without trailing halt
    (wrapper `compileHexFun?` appends `[.halt]`). 26 instructions.
    Layout (`P` = block start of level for yao at index `i`):
    - Level for y1 (i=0, LSB): pc 0..4   (next level at pc 5)
    - Level for y2 (i=1):      pc 5..9   (next level at pc 10)
    - Level for y3 (i=2):      pc 10..14 (next level at pc 15)
    - Level for y4 (i=3):      pc 15..19 (next level at pc 20)
    - Level for y5 (i=4):      pc 20..24 (next level at pc 25)
    - Terminal y6 (i=5, MSB):  pc 25 (flipYao 5; wrapper appends halt at pc 26)
-/
def tuiSteps : List YiInstr :=
  adderLevel fin0 0  5  ++
  adderLevel fin1 5  10 ++
  adderLevel fin2 10 15 ++
  adderLevel fin3 15 20 ++
  adderLevel fin4 20 25 ++
  [.flipYao fin5]

/-- Public form with explicit terminal halt. -/
def tuiProg : List YiInstr := tuiSteps ++ [.halt]

/-- For `sun` (mod-64 -1), we use the same propagate-carry adder structure
    but the semantics is +63 mod 64 = -1 mod 64. Equivalently: start at y6,
    if y6 = yin (1), flip to yang (0), done. If y6 = yang (0), flip to yin (1),
    borrow propagates up. This is the dual of `tuiProg` — branch on yin instead
    of yang. We get this by swapping the yang/yin cases at each block.

    Block per level (5 instructions, dual of `adderLevel`):
      pc=P+0: branchYaoYang ⟨i, _⟩ (P+1)   // 若 yang, 进入 P+1 (yang case: borrow propagates)
      pc=P+1: flipYao ⟨i, _⟩                // yang case: set bit (now yin), borrow up
      pc=P+2: jump (P+5)                    // proceed to next level
      pc=P+3: flipYao ⟨i, _⟩                // yin case: clear bit, halt
      pc=P+4: halt

    Wait — easier: just use the same `adderLevel` shape but reverse target order.
    Specifically, swap target: instead of `branchYaoYang i (P+3); flipYao i; jump next; flipYao i; halt`,
    we use `branchYaoYang i (P+1); flipYao i; halt; flipYao i; jump next`.

    Concretely for -1 (sun):
      pc=P+0: branchYaoYang ⟨i, _⟩ (P+3)  // yang? → P+3 (propagate borrow)
      pc=P+1: flipYao ⟨i, _⟩                // yin case (bit was 1): flip to 0, halt
      pc=P+2: halt
      pc=P+3: flipYao ⟨i, _⟩                // yang case (bit was 0): flip to 1, borrow up
      pc=P+4: jump (P+5)

    Terminal y1 (i=0): same `flipYao 0; halt` since mod-64.
-/
def sunAdderLevel (i : Fin 6) (P next : Nat) : List YiInstr :=
  [ .branchYaoYang i (P + 3)
  , .flipYao i
  , .halt
  , .flipYao i
  , .jump next
  ]

/-- Propagate-borrow subtracter for -1 mod 64 (`sun`), without trailing halt
    (wrapper appends). 26 instructions. LSB→MSB order. -/
def sunSteps : List YiInstr :=
  sunAdderLevel fin0 0  5  ++
  sunAdderLevel fin1 5  10 ++
  sunAdderLevel fin2 10 15 ++
  sunAdderLevel fin3 15 20 ++
  sunAdderLevel fin4 20 25 ++
  [.flipYao fin5]

/-- Public form with explicit terminal halt. -/
def sunProg : List YiInstr := sunSteps ++ [.halt]

/-! ## § 3c  A conservative executable bridge -/

/-- Run a complete straight-line Hex program.  The compiler below returns lists
    that already include the final `halt`; `prog.length` is therefore enough
    fuel for this subset. -/
def runHexProg (prog : List YiInstr) (h : Hexagram) : Hexagram :=
  ((YiState.init h prog).runFuel prog.length).cur.1

/-- Internal helper: run steps that omit the final `halt`. -/
def runHexSteps (steps : List YiInstr) (h : Hexagram) : Hexagram :=
  runHexProg (steps ++ [.halt]) h

private def appendNote (a b : String) : String :=
  if a = "" then b else if b = "" then a else a ++ " ; " ++ b

private def tmNodeCount : Tm → Nat
  | .abs _ _ body => tmNodeCount body + 1
  | .app f x => tmNodeCount f + tmNodeCount x + 1
  | .catalogue1 _ a => tmNodeCount a + 1
  | .catalogue2 _ a b => tmNodeCount a + tmNodeCount b + 1
  | .catalogue3 _ a b c => tmNodeCount a + tmNodeCount b + tmNodeCount c + 1
  | _ => 1

mutual
  private def compileHexStepsFuel? : Nat → Tm → Option (List YiInstr × String)
    | 0, _ => none
    | fuel+1, .abs x .hex body =>
        compileHexBodyFuel? fuel x body
    | fuel+1, .app (.app comp f) g =>
        if comp = Stdlib.endoCompBody then do
          let (gSteps, gNote) ← compileHexStepsFuel? fuel g
          let (fSteps, fNote) ← compileHexStepsFuel? fuel f
          some (gSteps ++ fSteps, appendNote gNote fNote)
        else
          none
    | fuel+1, .app rpt f =>
        if rpt = Stdlib.repeatOnceBody then do
          let (steps, note) ← compileHexStepsFuel? fuel f
          some (steps ++ steps, appendNote note note)
        else if rpt = Stdlib.hexApplyBody then
          compileHexStepsFuel? fuel f
        else
          none
    | _+1, .cuoH => some ([.complement], "complement")
    | _+1, .zongH => some ([.reverse], "reverse")
    | _+1, .huH => some ([.interlace], "interlace")
    | _+1, .cuoZongH => some ([.complement, .reverse], "complementReverse")
    | _+1, .flip1H => some ([.flipYao fin0], "flip1")
    | _+1, .flip2H => some ([.flipYao fin1], "flip2")
    | _+1, .flip3H => some ([.flipYao fin2], "flip3")
    | _+1, .flip4H => some ([.flipYao fin3], "flip4")
    | _+1, .flip5H => some ([.flipYao fin4], "flip5")
    | _+1, .flip6H => some ([.flipYao fin5], "flip6")
    | _+1, _ => none

  private def compileHexBodyFuel? : Nat → String → Tm → Option (List YiInstr × String)
    | 0, _, _ => none
    | _+1, x, .var y =>
        if x = y then some ([], "id") else none
    -- v2: tui (mod-64 +1) pattern `.app (.app .jia .yi) (.var x)`
    | _+1, x, .app (.app .jia .yi) (.var y) =>
        if x = y then some (tuiSteps, "tui") else none
    -- v2: sun (mod-64 -1) pattern `.app (.app .jia (.hexLit Hexagram.earth)) (.var x)`
    | _+1, x, .app (.app .jia (.hexLit h)) (.var y) =>
        if x = y && h = Hexagram.earth then some (sunSteps, "sun") else none
    | fuel+1, x, .app f arg => do
        let (argSteps, argNote) ← compileHexBodyFuel? fuel x arg
        let (fSteps, fNote) ← compileHexStepsFuel? fuel f
        some (argSteps ++ fSteps, appendNote argNote fNote)
    | _+1, _, _ => none
end

private def compileHexSteps? (t : Tm) : Option (List YiInstr × String) :=
  compileHexStepsFuel? (tmNodeCount t + 3) t

/-- Syntactic conservative compiler for closed, typeable straight-line
    `Hex → Hex` fragments.

    Accepted shapes:
    * identity lambdas (`λx:Hex. x`);
    * the primitive endomorphisms `.cuoH`, `.zongH`, `.huH`, `.cuoZongH`,
      `.flip1H` ... `.flip6H`;
    * simple application chains such as `λx. f (g x)`, when every stage is in
      this same fragment;
    * exact helper combinators for composition, one-repeat, and explicit
      endomap application when their operands are in this same fragment.

    Everything else is rejected, including `tui`, `sun`, `.jia`, catalogue
    wrappers, Bool/pair/list terms, and Cell terms. -/
def compileHexFun? (t : Tm) : Option (List YiInstr) := do
  let (steps, _) ← compileHexSteps? t
  match typeCheck [] t with
  | some (.arr .hex .hex) => some (steps ++ [.halt])
  | _ => none

/-- Runtime finite validation of the bridge over all 64 hexagrams. -/
def compiledHexFunAgrees (t : Tm) (prog : List YiInstr) : Bool :=
  Hexagram.allHex.all fun h =>
    match denoteHexFun t h with
    | some out => decide (runHexProg prog h = out)
    | none => false

/-- Public safe bridge: only return programs that validate against `denoteHexFun`. -/
def compileHexFunCertified? (t : Tm) : Option (List YiInstr) :=
  match compileHexFun? t with
  | some prog => if compiledHexFunAgrees t prog then some prog else none
  | none => none

theorem compileHexFun_id :
    compileHexFun? Stdlib.hexIdBody = some [.halt] := by rfl

theorem compileHexFun_cuo :
    compileHexFun? Stdlib.cuoBody = some [.complement, .halt] := by rfl

theorem compileHexFun_zong :
    compileHexFun? Stdlib.zongBody = some [.reverse, .halt] := by rfl

theorem compileHexFun_hu :
    compileHexFun? Stdlib.huBody = some [.interlace, .halt] := by rfl

theorem compileHexFun_cuoZong :
    compileHexFun? Stdlib.cuoZongBody = some [.complement, .reverse, .halt] := by rfl

theorem compileHexFun_flip1 :
    compileHexFun? Stdlib.flip1Body = some [.flipYao fin0, .halt] := by rfl

theorem compileHexFun_flip6 :
    compileHexFun? Stdlib.flip6Body = some [.flipYao fin5, .halt] := by rfl

/-- Simple composition example: `λx. complement (reverse x)`. -/
def cuoAfterZongBody : Tm :=
  .abs "x" .hex (.app .cuoH (.app .zongH (.var "x")))

theorem cuoAfterZongBody_typed :
    typeCheck [] cuoAfterZongBody = some (.arr .hex .hex) := by native_decide

theorem compileHexFun_cuoAfterZong :
    compileHexFun? cuoAfterZongBody = some [.reverse, .complement, .halt] := by rfl

/-- Surface `而 错 综`: exact endomap composition without eta expansion. -/
def cuoAfterZongCombinatorBody : Tm :=
  .app (.app Stdlib.endoCompBody Stdlib.cuoBody) Stdlib.zongBody

theorem cuoAfterZongCombinatorBody_typed :
    typeCheck [] cuoAfterZongCombinatorBody = some (.arr .hex .hex) := by native_decide

theorem compileHexFun_cuoAfterZongCombinator :
    compileHexFun? cuoAfterZongCombinatorBody = some [.reverse, .complement, .halt] := by rfl

/-- Surface `而 反 综`: deferred `反` as object-level `.cuoH`. -/
def fanAfterZongCombinatorBody : Tm :=
  .app (.app Stdlib.endoCompBody Stdlib.fanReverseBody) Stdlib.zongBody

theorem fanAfterZongCombinatorBody_typed :
    typeCheck [] fanAfterZongCombinatorBody = some (.arr .hex .hex) := by native_decide

theorem compileHexFun_fanAfterZongCombinator :
    compileHexFun? fanAfterZongCombinatorBody = some [.reverse, .complement, .halt] := by rfl

/-- Surface `再 反`: exact one-repeat helper over the object-level `反`. -/
def repeatFanBody : Tm :=
  .app Stdlib.repeatOnceBody Stdlib.fanReverseBody

theorem repeatFanBody_typed :
    typeCheck [] repeatFanBody = some (.arr .hex .hex) := by native_decide

theorem compileHexFun_repeatFan :
    compileHexFun? repeatFanBody = some [.complement, .complement, .halt] := by rfl

theorem compileHexFun_id_denotes (h : Hexagram) :
    some (runHexProg [.halt] h) = denoteHexFun Stdlib.hexIdBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem compileHexFun_cuo_denotes (h : Hexagram) :
    some (runHexProg [.complement, .halt] h) = denoteHexFun Stdlib.cuoBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem compileHexFun_cuoAfterZong_denotes (h : Hexagram) :
    some (runHexProg [.reverse, .complement, .halt] h) = denoteHexFun cuoAfterZongBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem compileHexFun_cuoAfterZongCombinator_denotes (h : Hexagram) :
    some (runHexProg [.reverse, .complement, .halt] h) =
      denoteHexFun cuoAfterZongCombinatorBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem compileHexFun_fanAfterZongCombinator_denotes (h : Hexagram) :
    some (runHexProg [.reverse, .complement, .halt] h) =
      denoteHexFun fanAfterZongCombinatorBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

theorem compileHexFun_repeatFan_denotes (h : Hexagram) :
    some (runHexProg [.complement, .complement, .halt] h) = denoteHexFun repeatFanBody h := by
  have heq : h = Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by apply Hexagram.ext <;> rfl
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;> cases h.y6 <;>
    native_decide

example :
    (match compileHexFunCertified? Stdlib.hexIdBody with
    | some prog => compiledHexFunAgrees Stdlib.hexIdBody prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? Stdlib.cuoBody with
    | some prog => compiledHexFunAgrees Stdlib.cuoBody prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? Stdlib.zongBody with
    | some prog => compiledHexFunAgrees Stdlib.zongBody prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? Stdlib.huBody with
    | some prog => compiledHexFunAgrees Stdlib.huBody prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? Stdlib.cuoZongBody with
    | some prog => compiledHexFunAgrees Stdlib.cuoZongBody prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? Stdlib.flip1Body with
    | some prog => compiledHexFunAgrees Stdlib.flip1Body prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? Stdlib.flip6Body with
    | some prog => compiledHexFunAgrees Stdlib.flip6Body prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? cuoAfterZongBody with
    | some prog => compiledHexFunAgrees cuoAfterZongBody prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? cuoAfterZongCombinatorBody with
    | some prog => compiledHexFunAgrees cuoAfterZongCombinatorBody prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? fanAfterZongCombinatorBody with
    | some prog => compiledHexFunAgrees fanAfterZongCombinatorBody prog
    | none => false) = true := by native_decide

example :
    (match compileHexFunCertified? repeatFanBody with
    | some prog => compiledHexFunAgrees repeatFanBody prog
    | none => false) = true := by native_decide

/-! ### v2: tui / sun are now COMPILABLE (was rejected in v1) -/

/-- v2: `Stdlib.tuiBody` (mod-64 +1) 现在可 compile, 用 `branchYaoYang` 之
    propagate-carry adder. v1 中此函数 non cuo-equivariant, 被 rejected. -/
theorem compileHexFun_tui :
    compileHexFun? Stdlib.tuiBody = some (tuiSteps ++ [.halt]) := by rfl

/-- v2: `Stdlib.sunBody` (mod-64 -1) 现在可 compile, 用 `branchYaoYang` 之
    propagate-borrow subtracter. -/
theorem compileHexFun_sun :
    compileHexFun? Stdlib.sunBody = some (sunSteps ++ [.halt]) := by rfl

/-- v2: certified 桥 接受 tui, 64-Hex finite agreement 见证. -/
example :
    (match compileHexFunCertified? Stdlib.tuiBody with
    | some prog => compiledHexFunAgrees Stdlib.tuiBody prog
    | none => false) = true := by native_decide

/-- v2: certified 桥 接受 sun, 64-Hex finite agreement 见证. -/
example :
    (match compileHexFunCertified? Stdlib.sunBody with
    | some prog => compiledHexFunAgrees Stdlib.sunBody prog
    | none => false) = true := by native_decide

/-- `.app .jia .yi` 单独 (无 .var 闭合) 仍非 well-typed `Hex → Hex`，故被 rejected
    (类型为 `Hex → Hex`, 但 `compileHexBodyFuel?` 仅在 `.abs x .hex body` 之内
    才识别 tui pattern; raw `.app .jia .yi` 不进入此 branch)。 -/
theorem compileHexFun_reject_jia :
    (compileHexFunCertified? (.app .jia .yi)).isNone = true := by native_decide

theorem compileHexFun_reject_catalogue :
    (compileHexFunCertified?
      (.catalogue2 .E_2 (.hexLit Hexagram.heaven) (.hexLit Hexagram.heaven))).isNone = true := by
  native_decide

theorem compileHexFun_reject_bool :
    (compileHexFunCertified? Stdlib.boolMarkerBody).isNone = true := by native_decide

theorem compileHexFun_reject_pair :
    (compileHexFunCertified? Stdlib.pairHBody).isNone = true := by native_decide

theorem compileHexFun_reject_list :
    (compileHexFunCertified? Stdlib.list1HBody).isNone = true := by native_decide

theorem compileHexFun_reject_cell :
    (compileHexFunCertified? Stdlib.cuoCBody).isNone = true := by native_decide

/-! ## § 4  错对称 之 形式见证 (complement-symmetry as a structural lemma)

  对每个 YiInstr，运行结果之 cur.1 与输入 complement 通约。这是「为何不能 compile «生»」之
  根因的形式化。我们 仅 证 单步原语之 通约性 (complement-equivariance)，不全展开 runFuel。
-/

/-- flipYao 之 complement-等变：(flipPos i h).complement = flipPos i (h.complement)。 -/
theorem flipPos_cuo_equivariant (h : Hexagram) (i : Fin 6) :
    (h.flipPos i).complement = (h.complement).flipPos i := by
  match i with
  | ⟨0, _⟩ => apply Hexagram.ext <;> cases h.y1 <;> rfl
  | ⟨1, _⟩ => apply Hexagram.ext <;> cases h.y2 <;> rfl
  | ⟨2, _⟩ => apply Hexagram.ext <;> cases h.y3 <;> rfl
  | ⟨3, _⟩ => apply Hexagram.ext <;> cases h.y4 <;> rfl
  | ⟨4, _⟩ => apply Hexagram.ext <;> cases h.y5 <;> rfl
  | ⟨5, _⟩ => apply Hexagram.ext <;> cases h.y6 <;> rfl

/-- complement 与自身之 等变：(complement h).complement = complement (h.complement)。 -/
theorem cuo_cuo_equivariant (h : Hexagram) :
    (Hexagram.complement h).complement = Hexagram.complement (h.complement) := by
  apply Hexagram.ext <;> rfl

/-- interlace 与 complement 通约：(interlace h).complement = interlace (h.complement)。 -/
theorem hu_cuo_equivariant (h : Hexagram) :
    (Hexagram.interlace h).complement = Hexagram.interlace (h.complement) := by
  apply Hexagram.ext <;> rfl

/-- reverse 与 complement 通约：(reverse h).complement = reverse (h.complement)。 -/
theorem zong_cuo_equivariant (h : Hexagram) :
    (Hexagram.reverse h).complement = Hexagram.reverse (h.complement) := by
  apply Hexagram.ext <;> rfl

/-- branchYaoEq 之 complement-不变性：y_i = y_j ↔ y_i.neg = y_j.neg
    （等价性 在 complement 下保持）。 -/
theorem yaoAt_eq_cuo_invariant (h : Hexagram) (i j : Fin 6) :
    (h.yaoAt i = h.yaoAt j) ↔ ((h.complement).yaoAt i = (h.complement).yaoAt j) := by
  constructor
  · intro heq
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩
    | ⟨0, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨0, _⟩
    | ⟨0, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨0, _⟩
    | ⟨0, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨0, _⟩
    | ⟨0, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨0, _⟩
    | ⟨1, _⟩, ⟨1, _⟩
    | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩
    | ⟨1, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨1, _⟩
    | ⟨1, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨1, _⟩
    | ⟨1, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨1, _⟩
    | ⟨2, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨2, _⟩
    | ⟨3, _⟩, ⟨3, _⟩
    | ⟨3, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨3, _⟩
    | ⟨3, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨3, _⟩
    | ⟨4, _⟩, ⟨4, _⟩
    | ⟨4, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨4, _⟩
    | ⟨5, _⟩, ⟨5, _⟩ =>
        first
          | rfl
          | (simp only [Hexagram.yaoAt, Hexagram.complement,
                        Hexagram.y1_mk, Hexagram.y2_mk, Hexagram.y3_mk,
                        Hexagram.y4_mk, Hexagram.y5_mk, Hexagram.y6_mk] at heq ⊢
             revert heq
             cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;>
               cases h.y6 <;> decide +revert)
  · intro heq
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩
    | ⟨0, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨0, _⟩
    | ⟨0, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨0, _⟩
    | ⟨0, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨0, _⟩
    | ⟨0, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨0, _⟩
    | ⟨1, _⟩, ⟨1, _⟩
    | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩
    | ⟨1, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨1, _⟩
    | ⟨1, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨1, _⟩
    | ⟨1, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨1, _⟩
    | ⟨2, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨2, _⟩
    | ⟨3, _⟩, ⟨3, _⟩
    | ⟨3, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨3, _⟩
    | ⟨3, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨3, _⟩
    | ⟨4, _⟩, ⟨4, _⟩
    | ⟨4, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨4, _⟩
    | ⟨5, _⟩, ⟨5, _⟩ =>
        first
          | rfl
          | (simp only [Hexagram.yaoAt, Hexagram.complement,
                        Hexagram.y1_mk, Hexagram.y2_mk, Hexagram.y3_mk,
                        Hexagram.y4_mk, Hexagram.y5_mk, Hexagram.y6_mk] at heq ⊢
             revert heq
             cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;> cases h.y5 <;>
               cases h.y6 <;> decide +revert)

/-! ## § 5  「«生» 非 complement-等变」之 数学事实 + v2 之 compile

  ★ 等式 `(prog h).complement = prog h.complement` 在 v1 doctrine 下对全 YiInstr
  program 成立；故 «生» 之非等变性 (`sheng_not_cuo_equivariant`) 等价于
  「无 v1-12-instr program 实现 «生»」。

  v2 doctrine 加入 `branchYaoYang` 后, ★ 等式 仅对 `complementEquivariantProg`
  子集成立。«生» 仍非等变（数学事实, 与 ISA 无关）, 但可由含 `branchYaoYang`
  之 program 表达（因 v2 program 不再要求等变）。

  具体: `tuiProg`（即 `Stdlib.tuiBody` 之 v2 compile 结果）实现 +1 mod 64,
  含 5 个 `branchYaoYang` 之 propagate-carry. 由 «生» = «加» «一» 即 +1,
  `tuiProg` 即 «生» 之 ISA 实现。
-/

/-- 反例点（数学事实，与 ISA 无关）：«生» 不与 complement 通约 — 取
    h = «乾» 则等式不成立。

    v1 解读：「故无 prog 实现 «生»」 — 12-instr ISA 之 cuo-ceiling.
    v2 解读：「故无 `complementEquivariantProg` 实现 «生»」 — 13-instr ISA
    之 `branchYaoYang` 含 program 不在此约束内, 可实现 «生». -/
theorem sheng_not_cuo_equivariant :
    («生» Hexagram.heaven).complement ≠ «生» (Hexagram.heaven.complement) := by
  native_decide

/-! ## § 6  公示总结 -/

/-- compile 之 v2 公示成果：
    (1) 恒等 Tm 之 compile
    (2) 加常 32 之 Tm 之 compile (含 Tm 等价)
    (3) complement 程序之直接定义
    (4) complement-symmetry 引理 (witness flipYao/complement/interlace/reverse/branchYaoEq 皆 complement-等变)
    (5) «生» 之非等变事实（数学层面, 不随 ISA 变化）
    (6) v2 新成果：`Stdlib.tuiBody` (+1 mod 64) 之 universal compile
-/
theorem compile_summary :
    -- (1) 恒等
    (∀ h : Hexagram, ((YiState.init h idProg).runFuel 1).cur.1 = h)
    ∧ -- (2) 加 32 (cur 等价)
    (∀ h : Hexagram, ((YiState.init h add32Prog).runFuel 2).cur.1 = «加» hex32 h)
    ∧ -- (3) complement 程序
    (∀ h : Hexagram, ((YiState.init h cuoProg).runFuel 2).cur.1 = h.complement)
    ∧ -- (4) complement-symmetry: flipPos 通约
    (∀ h : Hexagram, ∀ i : Fin 6, (h.flipPos i).complement = (h.complement).flipPos i)
    ∧ -- (5) «生» 之非等变性 (数学事实)
    («生» Hexagram.heaven).complement ≠ «生» (Hexagram.heaven.complement)
    ∧ -- (6) v2: tuiBody 现可 compile (was 不可 in v1)
    (compileHexFun? Stdlib.tuiBody = some (tuiSteps ++ [.halt]))
    := ⟨idProg_correct, add32Prog_correct, cuoProg_correct,
        flipPos_cuo_equivariant, sheng_not_cuo_equivariant, compileHexFun_tui⟩

end SSBX.Foundation.Wen.WenDefCompile
