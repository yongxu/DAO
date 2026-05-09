/-
# WenDefCompile — L1 typed Tm → L0 YiInstr 之桥（compile 一隅）

L1 (`WenDef.Tm`) 与 L0 (`BaguaTuring.YiInstr`) 之间一桥。
WenDefEval.lean 已建 Lean-level evaluator (`denoteHexFun`)。
本文 进一步：取若干 closed Tm，给出 YiInstr 程序，证 二者同义。

## 关键观察 — 错对称之约束 (cuo-symmetry constraint)

YiInstr 之 12 条原语皆与「错」(全爻取反) 通约：
  ·  flipYao i :  (flipPos i h).cuo = flipPos i (h.cuo)
  ·  cuo, hu, zong : 皆与 cuo 通约
  ·  branchYaoEq i j : (h.yaoAt i = h.yaoAt j) ↔ (h.cuo.yaoAt i = h.cuo.yaoAt j)
  ·  setShi/branchShiEq : 仅作用于 Shi，不涉 yao
  ·  jump/push/pop/halt/nop : 控制流原语

故：任 YiInstr 程序之转换 f : Hexagram → Hexagram 满足
  f(h.cuo) = (f h).cuo                              ... (★)

「错等变」(cuo-equivariance) — YiInstr 可表达之 Hex → Hex 函数之刚性约束。

由 (★) 可推：
  ·  常值函数 f(h) = «一» 不可表（«一» ≠ «一».cuo = ⟨yang,yin,yin,yin,yin,yin⟩）
  ·  «生» = «加» «一» 不可表（«生» «乾» = «一»; («生» «乾»).cuo = «一».cuo ≠ «生» «坤» = «乾»）
     故任 YiInstr 程序皆不能模拟 «生» — 此为 Path 丙 之结构性界限。

可表者：恒等、«错»、«互»、«综»、flipYao i 之复合、«加» k (k.toIdx ∈ {0, 32})、
       并 control flow 由 cuo-invariant 谓词决定者（如「y3=y4」）。

非常值之 Hex → Bool 谓词若 cuo-invariant，亦可由 YiInstr 实现并以 Shi 输出
（如 daoJudgeProg 之 `isTian` 判定）。

## 本文 之范围

我们给出三例 L1 → L0 compile，皆 cuo-equivariant：

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

## 未尽之业 (future work)

由 cuo-symmetry，Tier B (生 = 加 «一») 与 Tier A (常 «一») 皆不可表。
完整 `compileHexFun : Tm → Option (List YiInstr)` 须严格限制于可由 L0 原语表达的
cuo-equivariant 子集。本文之 `compileHexFunCertified?` 先覆盖 straight-line exact
Hex transform chain，并以 64 卦 finite validation 作执行边界。

替代方案：扩展 YiInstr 加 absolute yao test (`branchYaoYang i t`) 或加 hexLit-style 常量
载入 — 此皆破 cuo-symmetry，得任意 Hex → Hex compile 能力。本文不行此路，留作 future work。

## 状态

0 sorry / 0 axiom. 无 partial def. native_decide 见证具体例。
-/
import SSBX.Foundation.Bagua.BaguaTuring
import SSBX.Foundation.Wen.WenDefEval

namespace SSBX.Foundation.Wen.WenDefCompile

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Bagua.Cell192
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
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-! ## § 2  Tier 1 — 常加 32 (即 flipYao 5) -/

/-- 卦索引 32：仅 y6 为 yin (高位)，其余 yang。 -/
def hex32 : Hexagram := Hexagram.fromIdx ⟨32, by omega⟩

theorem hex32_def : hex32 = ⟨.yang, .yang, .yang, .yang, .yang, .yin⟩ := by
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
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-- 「加 32」compile 正确：runFuel 之 cur = «加» hex32 h。 -/
theorem add32Prog_correct (h : Hexagram) :
    ((YiState.init h add32Prog).runFuel 2).cur.1 = «加» hex32 h := by
  rw [add32Prog_runs, flipPos5_eq_add32]

/-- 「加 32」compile 之 Tm 等价：runFuel 之输出与 denoteHexFun add32Body 一致。
    全 64 输入皆 native_decide 见证。 -/
theorem add32Prog_denotes (h : Hexagram) :
    some ((YiState.init h add32Prog).runFuel 2).cur.1 = denoteHexFun add32Body h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-! ## § 3  Tier 2 — 直接 «错» (no Tm source) -/

/-- 「错」之 YiInstr 程序：直接 cuo 一条加 halt。 -/
def cuoProg : List YiInstr := [.cuo, .halt]

/-- 「错」compile 正确：runFuel 2 之 cur = h.cuo。 -/
theorem cuoProg_correct (h : Hexagram) :
    ((YiState.init h cuoProg).runFuel 2).cur.1 = h.cuo := by
  rfl

/-- 「错」compile 之 Tm 等价。 -/
theorem cuoProg_denotes (h : Hexagram) :
    some ((YiState.init h cuoProg).runFuel 2).cur.1 = denoteHexFun Stdlib.cuoBody h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-- 「综」之 YiInstr 程序。 -/
def zongProg : List YiInstr := [.zong, .halt]

theorem zongProg_denotes (h : Hexagram) :
    some ((YiState.init h zongProg).runFuel 2).cur.1 = denoteHexFun Stdlib.zongBody h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-- 「互」之 YiInstr 程序。 -/
def huProg : List YiInstr := [.hu, .halt]

theorem huProg_denotes (h : Hexagram) :
    some ((YiState.init h huProg).runFuel 2).cur.1 = denoteHexFun Stdlib.huBody h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-- 「错综」之 YiInstr 程序：按定义先错后综。 -/
def cuoZongProg : List YiInstr := [.cuo, .zong, .halt]

theorem cuoZongProg_denotes (h : Hexagram) :
    some ((YiState.init h cuoZongProg).runFuel 3).cur.1 =
      denoteHexFun Stdlib.cuoZongBody h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

private def fin0 : Fin 6 := ⟨0, by omega⟩
private def fin1 : Fin 6 := ⟨1, by omega⟩
private def fin2 : Fin 6 := ⟨2, by omega⟩
private def fin3 : Fin 6 := ⟨3, by omega⟩
private def fin4 : Fin 6 := ⟨4, by omega⟩
private def fin5 : Fin 6 := ⟨5, by omega⟩

/-- 单爻翻转程序。 -/
def flip1Prog : List YiInstr := [.flipYao fin0, .halt]
def flip2Prog : List YiInstr := [.flipYao fin1, .halt]
def flip3Prog : List YiInstr := [.flipYao fin2, .halt]
def flip4Prog : List YiInstr := [.flipYao fin3, .halt]
def flip5Prog : List YiInstr := [.flipYao fin4, .halt]
def flip6Prog : List YiInstr := [.flipYao fin5, .halt]

theorem flip1Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip1Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip1Body h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

theorem flip2Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip2Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip2Body h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

theorem flip3Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip3Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip3Body h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

theorem flip4Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip4Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip4Body h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

theorem flip5Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip5Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip5Body h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

theorem flip6Prog_denotes (h : Hexagram) :
    some ((YiState.init h flip6Prog).runFuel 2).cur.1 = denoteHexFun Stdlib.flip6Body h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-! ## § 3b  A conservative executable bridge -/

/-- A straight-line L0 program for a closed L1 `Hex → Hex` term.
    `steps` omits the final `halt`; `program` appends it uniformly. -/
structure CompiledHexFun where
  source : Tm
  steps : List YiInstr
  note : String
deriving Repr

namespace CompiledHexFun

def program (c : CompiledHexFun) : List YiInstr :=
  c.steps ++ [.halt]

def fuel (c : CompiledHexFun) : Nat :=
  c.steps.length + 1

end CompiledHexFun

def runHexSteps (steps : List YiInstr) (h : Hexagram) : Hexagram :=
  ((YiState.init h (steps ++ [.halt])).runFuel (steps.length + 1)).cur.1

def runCompiledHexFun (c : CompiledHexFun) (h : Hexagram) : Hexagram :=
  runHexSteps c.steps h

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
          match rpt, f with
          | .jia, .hexLit h =>
              if h = hex32 then
                some ([.flipYao fin5], "add32")
              else if h = Hexagram.qian then
                some ([], "add0")
              else
                none
          | _, _ => none
    | _+1, .cuoH => some ([.cuo], "cuo")
    | _+1, .zongH => some ([.zong], "zong")
    | _+1, .huH => some ([.hu], "hu")
    | _+1, .cuoZongH => some ([.cuo, .zong], "cuoZong")
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
    | fuel+1, x, .app f (.var y) =>
        if x = y then
          compileHexStepsFuel? fuel f
        else
          none
    | fuel+1, x, .app f arg => do
        let (argSteps, argNote) ← compileHexBodyFuel? fuel x arg
        let (fSteps, fNote) ← compileHexStepsFuel? fuel f
        some (argSteps ++ fSteps, appendNote argNote fNote)
    | _+1, _, _ => none
end

private def compileHexSteps? (t : Tm) : Option (List YiInstr × String) :=
  compileHexStepsFuel? (tmNodeCount t + 3) t

/-- Syntactic conservative compiler for exact `Hex → Hex` fragments. -/
def compileHexFun? (t : Tm) : Option CompiledHexFun := do
  let (steps, note) ← compileHexSteps? t
  match typeCheck [] t with
  | some (.arr .hex .hex) => some { source := t, steps := steps, note := note }
  | _ => none

/-- Runtime finite validation of the bridge over all 64 hexagrams. -/
def compiledHexFunAgrees (c : CompiledHexFun) : Bool :=
  Hexagram.allHex.all fun h =>
    match denoteHexFun c.source h with
    | some out => decide (runCompiledHexFun c h = out)
    | none => false

/-- Public safe bridge: only return programs that validate against `denoteHexFun`. -/
def compileHexFunCertified? (t : Tm) : Option CompiledHexFun :=
  match compileHexFun? t with
  | some c => if compiledHexFunAgrees c then some c else none
  | none => none

example : (match compileHexFunCertified? Stdlib.hexIdBody with
    | some c => compiledHexFunAgrees c
    | none => false) = true := by native_decide

example : (match compileHexFunCertified? Stdlib.cuoBody with
    | some c => compiledHexFunAgrees c
    | none => false) = true := by native_decide

example : (match compileHexFunCertified? Stdlib.zongBody with
    | some c => compiledHexFunAgrees c
    | none => false) = true := by native_decide

example : (match compileHexFunCertified? Stdlib.huBody with
    | some c => compiledHexFunAgrees c
    | none => false) = true := by native_decide

example : (match compileHexFunCertified? Stdlib.cuoZongBody with
    | some c => compiledHexFunAgrees c
    | none => false) = true := by native_decide

example : (match compileHexFunCertified? Stdlib.flip1Body with
    | some c => compiledHexFunAgrees c
    | none => false) = true := by native_decide

example : (match compileHexFunCertified? Stdlib.flip6Body with
    | some c => compiledHexFunAgrees c
    | none => false) = true := by native_decide

example : (compileHexFunCertified? Stdlib.tuiBody).isNone = true := by native_decide

example : (compileHexFunCertified? Stdlib.sunBody).isNone = true := by native_decide

example : (compileHexFunCertified? (.boolLit true)).isNone = true := by native_decide

/-! ## § 4  错对称 之 形式见证 (cuo-symmetry as a structural lemma)

  对每个 YiInstr，运行结果之 cur.1 与输入 cuo 通约。这是「为何不能 compile «生»」之
  根因的形式化。我们 仅 证 单步原语之 通约性 (cuo-equivariance)，不全展开 runFuel。
-/

/-- flipYao 之 cuo-等变：(flipPos i h).cuo = flipPos i (h.cuo)。 -/
theorem flipPos_cuo_equivariant (h : Hexagram) (i : Fin 6) :
    (h.flipPos i).cuo = (h.cuo).flipPos i := by
  match i with
  | ⟨0, _⟩ => rcases h with ⟨y1, _, _, _, _, _⟩; cases y1 <;> rfl
  | ⟨1, _⟩ => rcases h with ⟨_, y2, _, _, _, _⟩; cases y2 <;> rfl
  | ⟨2, _⟩ => rcases h with ⟨_, _, y3, _, _, _⟩; cases y3 <;> rfl
  | ⟨3, _⟩ => rcases h with ⟨_, _, _, y4, _, _⟩; cases y4 <;> rfl
  | ⟨4, _⟩ => rcases h with ⟨_, _, _, _, y5, _⟩; cases y5 <;> rfl
  | ⟨5, _⟩ => rcases h with ⟨_, _, _, _, _, y6⟩; cases y6 <;> rfl

/-- cuo 与自身之 等变：(cuo h).cuo = cuo (h.cuo)。 -/
theorem cuo_cuo_equivariant (h : Hexagram) :
    (Hexagram.cuo h).cuo = Hexagram.cuo (h.cuo) := by
  rfl

/-- hu 与 cuo 通约：(hu h).cuo = hu (h.cuo)。 -/
theorem hu_cuo_equivariant (h : Hexagram) :
    (Hexagram.hu h).cuo = Hexagram.hu (h.cuo) := by
  rfl

/-- zong 与 cuo 通约：(zong h).cuo = zong (h.cuo)。 -/
theorem zong_cuo_equivariant (h : Hexagram) :
    (Hexagram.zong h).cuo = Hexagram.zong (h.cuo) := by
  rfl

/-- branchYaoEq 之 cuo-不变性：y_i = y_j ↔ y_i.neg = y_j.neg
    （等价性 在 cuo 下保持）。 -/
theorem yaoAt_eq_cuo_invariant (h : Hexagram) (i j : Fin 6) :
    (h.yaoAt i = h.yaoAt j) ↔ ((h.cuo).yaoAt i = (h.cuo).yaoAt j) := by
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
        rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
        cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
          simp_all [Hexagram.yaoAt, Hexagram.cuo, Yao.neg]
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
        rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
        cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
          simp_all [Hexagram.yaoAt, Hexagram.cuo, Yao.neg]

/-! ## § 5  「«生» 不可 compile」之 见证

  由 cuo-symmetry，任 YiInstr 程序 prog 满足
    ((init h prog).runFuel n).cur.1.cuo = ((init h.cuo prog).runFuel n).cur.1   (∀ n h)

  若 prog 实现 «生»，则 («生» h).cuo = «生» (h.cuo) 须成立。但：
    («生» «乾»).cuo = «一».cuo = ⟨yang,yin,yin,yin,yin,yin⟩ (toIdx 62)
    «生» («乾».cuo) = «生» «坤» = ⟨yang,yang,yang,yang,yang,yang⟩ (toIdx 0) = «乾»
  二者相异，故无 prog 实现 «生»。

  此为 Path 丙之 structural limit。下证之。
-/

/-- 反例点：«生» 不与 cuo 通约 — 取 h = «乾» 则等式不成立。 -/
theorem sheng_not_cuo_equivariant :
    («生» Hexagram.qian).cuo ≠ «生» (Hexagram.qian.cuo) := by
  native_decide

/-! ## § 6  公示总结 -/

/-- compile 之 三层成果：
    (1) 恒等 Tm 之 compile
    (2) 加常 32 之 Tm 之 compile (含 Tm 等价)
    (3) cuo 程序之直接定义
    (4) cuo-symmetry 引理 (witness flipYao/cuo/hu/zong/branchYaoEq 皆 cuo-等变)
    (5) «生» 不可 compile 之反例（Tier B 之 不可性）
-/
theorem compile_summary :
    -- (1) 恒等
    (∀ h : Hexagram, ((YiState.init h idProg).runFuel 1).cur.1 = h)
    ∧ -- (2) 加 32 (cur 等价)
    (∀ h : Hexagram, ((YiState.init h add32Prog).runFuel 2).cur.1 = «加» hex32 h)
    ∧ -- (3) cuo 程序
    (∀ h : Hexagram, ((YiState.init h cuoProg).runFuel 2).cur.1 = h.cuo)
    ∧ -- (4) cuo-symmetry: flipPos 通约
    (∀ h : Hexagram, ∀ i : Fin 6, (h.flipPos i).cuo = (h.cuo).flipPos i)
    ∧ -- (5) «生» 之结构性不可 compile 见证
    («生» Hexagram.qian).cuo ≠ «生» (Hexagram.qian.cuo)
    := ⟨idProg_correct, add32Prog_correct, cuoProg_correct,
        flipPos_cuo_equivariant, sheng_not_cuo_equivariant⟩

end SSBX.Foundation.Wen.WenDefCompile
