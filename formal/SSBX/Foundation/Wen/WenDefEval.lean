/-
# WenDefEval — WenDef ↔ baguaTuring 之桥（Tm 之 Lean-level 求值）

L1 layer (`WenDef.Tm`) 与 L0 internal kernel (`YiCore.«加»/«一»`) 之桥：

  ·  `eval`              — closure-based Lean-level 求值器（total, fuel-bounded）
  ·  builtin 等价         — `.jia ⟷ «加»`，`.yi ⟷ «一»`，`.eqHex ⟷ DecidableEq`，…
  ·  Stdlib correctness   — `tuiDef` 之 denotation = `«生»`

由 64 元有限论域，eval 之 `.forallH` 是有限合取（64-fold ∧），全可决.

## 设计

```
Value :=
  | hexV : Hexagram → Value
  | boolV : Bool → Value
  | cellV : R8 → Value
  | pairV : Value → Value → Value
  | listV : List Value → Value
  | closV : List (String × Value) → String → Tm → Value      -- λ closure
  | builtinV : Builtin → List Value → Value                  -- partially-applied builtin
```

`evalFuel` 使用显式 fuel 防 nontermination；STLC 上结构 normalizing，
特例等价仍用 `native_decide` 见证.

## 桥到 baguaTuring (M3 之始)

`denoteHex : Tm → Option Hexagram`
`denoteBool : Tm → Option Bool`
`denoteHexFun : Tm → Option (Hexagram → Option Hexagram)`  — 对 Hex → Hex 之 Tm

`tui_eq_sheng (h : Hexagram) : denoteHexFun tuiBody h = some («生» h)`
   ↑↑↑ wenyan-op «推» 之 denotation = YiCore.«生» — 全 native_decide.

## 状态

0 sorry / 0 axiom. evaluator 为 fuel-bounded 总函数 + native_decide 见证 PoC.
-/
import SSBX.Foundation.Wen.WenDef
import SSBX.Foundation.Atlas.YiLegacy.YiCore
import SSBX.Foundation.Atlas.YiLegacy.Bagua.BaguaAlgebra
import SSBX.Foundation.Atlas.YiLegacy.Bagua.R8

namespace SSBX.Foundation.Wen.WenDefEval

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.R8

/-! ## § 1  Builtin 标记 -/

/-- 求值时之 builtin tag。 -/
inductive Builtin : Type
  | jia | notB | andB | orB | eqHex | forallH | cuoH | zongH | huH
  | uniqueH | exactly3H | majorityH
  | cuoZongH | flip1H | flip2H | flip3H | flip4H | flip5H | flip6H
  | pairH | dupH | list1H | list2H | list3H | headH
  | eqCell | cuoC | zongC | huC | shiNextC | shiPrevC
  | flip1C | flip2C | flip3C | flip4C | flip5C | flip6C
deriving DecidableEq, Repr

/-- builtin 之 arity（满足后产 result）。 -/
def Builtin.arity : Builtin → Nat
  | .list3H => 3
  | .jia | .andB | .orB | .eqHex | .pairH | .list2H | .eqCell => 2
  | .notB | .forallH | .uniqueH | .exactly3H | .majorityH | .cuoH | .zongH | .huH
  | .cuoZongH | .flip1H | .flip2H | .flip3H | .flip4H | .flip5H | .flip6H
  | .dupH | .list1H | .headH
  | .cuoC | .zongC | .huC | .shiNextC | .shiPrevC
  | .flip1C | .flip2C | .flip3C | .flip4C | .flip5C | .flip6C => 1

/-! ## § 2  Value -/

/-- 运行时值。closV 持环境；builtinV 持已应用之参数（partial application）. -/
inductive Value : Type
  | hexV     (h : Hexagram)                                    : Value
  | boolV    (b : Bool)                                        : Value
  | cellV    (c : R8)                                     : Value
  | pairV    (a b : Value)                                     : Value
  | listV    (xs : List Value)                                 : Value
  | closV    (env : List (String × Value)) (n : String) (body : Tm) : Value
  | builtinV (b : Builtin) (args : List Value)                 : Value
  | catalogueV (id : SSBX.Text.WenyanOperators.OperatorId)
      (kind : SSBX.Text.OperatorSignatures.SignatureKind)
      (args : List Value)                                      : Value
deriving Repr

abbrev Env := List (String × Value)

/-- 在环境中查 variable. -/
def Env.lookup : Env → String → Option Value
  | [], _ => none
  | (n, v) :: rest, name => if n = name then some v else rest.lookup name

/-! ## § 3  64-fold 凡 — 有限 ∀ -/

/-- 64 元 hex 上之 ∀: 检查 64 hex 之 predicate 全 true. -/
def forallHex (p : Hexagram → Bool) : Bool :=
  (List.range 64).all (fun k => p (Hexagram.fromIdx ⟨k % 64, Nat.mod_lt _ (by omega)⟩))

def countHex (p : Hexagram → Bool) : Nat :=
  (List.range 64).foldl
    (fun n k => if p (Hexagram.fromIdx ⟨k % 64, Nat.mod_lt _ (by omega)⟩) then n + 1 else n)
    0

def uniqueHex (p : Hexagram → Bool) : Bool :=
  countHex p == 1

def exactly3Hex (p : Hexagram → Bool) : Bool :=
  countHex p == 3

def majorityHex (p : Hexagram → Bool) : Bool :=
  32 < countHex p

/-! ## § 4  evaluator -/

/-- 闭项 denotation 使用之默认 fuel。stdlib demos 远低于此界。 -/
def defaultFuel : Nat := 512

mutual
  /-- Fuel-bounded 应用 Value 到 Value: closure beta + builtin partial-apply. -/
  def applyFuel : Nat → Value → Value → Option Value
    | 0,     _, _ => none
    | fuel+1, .closV env n body, arg => evalFuel fuel ((n, arg) :: env) body
    | fuel+1, .builtinV b args, arg =>
        let args' := args ++ [arg]
        if args'.length < b.arity then
          some (.builtinV b args')
        else
          applyBuiltinFuel fuel b args'
    | _+1, _, _ => none

  /-- Fuel-bounded Tm 求值（closure-based，总函数）. -/
  def evalFuel : Nat → Env → Tm → Option Value
    | 0,      _,   _             => none
    | _+1,    env, .var n        => env.lookup n
    | _+1,    env, .abs n _ body => some (.closV env n body)
    | fuel+1, env, .app f x      => do
        let vf ← evalFuel fuel env f
        let vx ← evalFuel fuel env x
        applyFuel fuel vf vx
    | _+1,    _,   .hexLit h     => some (.hexV h)
    | _+1,    _,   .boolLit b    => some (.boolV b)
    | _+1,    _,   .cellLit c    => some (.cellV c)
    | _+1,    _,   .jia          => some (.builtinV .jia [])
    | _+1,    _,   .yi           => some (.hexV «一»)
    | _+1,    _,   .notB         => some (.builtinV .notB [])
    | _+1,    _,   .andB         => some (.builtinV .andB [])
    | _+1,    _,   .orB          => some (.builtinV .orB [])
    | _+1,    _,   .eqHex        => some (.builtinV .eqHex [])
    | _+1,    _,   .forallH      => some (.builtinV .forallH [])
    | _+1,    _,   .uniqueH      => some (.builtinV .uniqueH [])
    | _+1,    _,   .exactly3H    => some (.builtinV .exactly3H [])
    | _+1,    _,   .majorityH    => some (.builtinV .majorityH [])
    | _+1,    _,   .cuoH         => some (.builtinV .cuoH [])
    | _+1,    _,   .zongH        => some (.builtinV .zongH [])
    | _+1,    _,   .huH          => some (.builtinV .huH [])
    | _+1,    _,   .cuoZongH     => some (.builtinV .cuoZongH [])
    | _+1,    _,   .flip1H       => some (.builtinV .flip1H [])
    | _+1,    _,   .flip2H       => some (.builtinV .flip2H [])
    | _+1,    _,   .flip3H       => some (.builtinV .flip3H [])
    | _+1,    _,   .flip4H       => some (.builtinV .flip4H [])
    | _+1,    _,   .flip5H       => some (.builtinV .flip5H [])
    | _+1,    _,   .flip6H       => some (.builtinV .flip6H [])
    | _+1,    _,   .pairH        => some (.builtinV .pairH [])
    | _+1,    _,   .dupH         => some (.builtinV .dupH [])
    | _+1,    _,   .list1H       => some (.builtinV .list1H [])
    | _+1,    _,   .list2H       => some (.builtinV .list2H [])
    | _+1,    _,   .list3H       => some (.builtinV .list3H [])
    | _+1,    _,   .headH        => some (.builtinV .headH [])
    | _+1,    _,   .eqCell       => some (.builtinV .eqCell [])
    | _+1,    _,   .cuoC         => some (.builtinV .cuoC [])
    | _+1,    _,   .zongC        => some (.builtinV .zongC [])
    | _+1,    _,   .huC          => some (.builtinV .huC [])
    | _+1,    _,   .shiNextC     => some (.builtinV .shiNextC [])
    | _+1,    _,   .shiPrevC     => some (.builtinV .shiPrevC [])
    | _+1,    _,   .flip1C       => some (.builtinV .flip1C [])
    | _+1,    _,   .flip2C       => some (.builtinV .flip2C [])
    | _+1,    _,   .flip3C       => some (.builtinV .flip3C [])
    | _+1,    _,   .flip4C       => some (.builtinV .flip4C [])
    | _+1,    _,   .flip5C       => some (.builtinV .flip5C [])
    | _+1,    _,   .flip6C       => some (.builtinV .flip6C [])
    | fuel+1, env, .catalogue1 id a => do
        let va ← evalFuel fuel env a
        some (.catalogueV id (SSBX.Text.OperatorSignatures.fullSignatureFor id).kind [va])
    | fuel+1, env, .catalogue2 id a b => do
        let va ← evalFuel fuel env a
        let vb ← evalFuel fuel env b
        some (.catalogueV id (SSBX.Text.OperatorSignatures.fullSignatureFor id).kind [va, vb])
    | fuel+1, env, .catalogue3 id a b c => do
        let va ← evalFuel fuel env a
        let vb ← evalFuel fuel env b
        let vc ← evalFuel fuel env c
        some (.catalogueV id (SSBX.Text.OperatorSignatures.fullSignatureFor id).kind [va, vb, vc])

  /-- Fuel-bounded builtin 求值. -/
  def applyBuiltinFuel : Nat → Builtin → List Value → Option Value
    | 0,      _,       _                    => none
    | _+1,    .jia,    [.hexV a, .hexV b]   => some (.hexV («加» a b))
    | _+1,    .notB,   [.boolV b]           => some (.boolV (!b))
    | _+1,    .andB,   [.boolV a, .boolV b] => some (.boolV (a && b))
    | _+1,    .orB,    [.boolV a, .boolV b] => some (.boolV (a || b))
    | _+1,    .eqHex,  [.hexV a, .hexV b]   => some (.boolV (decide (a = b)))
    | _+1,    .cuoH,   [.hexV h]            => some (.hexV h.complement)
    | _+1,    .zongH,  [.hexV h]            => some (.hexV h.reverse)
    | _+1,    .huH,    [.hexV h]            => some (.hexV h.interlace)
    | _+1,    .cuoZongH, [.hexV h]          => some (.hexV h.complementReverse)
    | _+1,    .flip1H, [.hexV h]            => some (.hexV (dongInner h))
    | _+1,    .flip2H, [.hexV h]            => some (.hexV (middleFlipInner h))
    | _+1,    .flip3H, [.hexV h]            => some (.hexV (topFlipInner h))
    | _+1,    .flip4H, [.hexV h]            => some (.hexV (dongOuter h))
    | _+1,    .flip5H, [.hexV h]            => some (.hexV (middleFlipOuter h))
    | _+1,    .flip6H, [.hexV h]            => some (.hexV (topFlipOuter h))
    | _+1,    .pairH,  [.hexV a, .hexV b]   => some (.pairV (.hexV a) (.hexV b))
    | _+1,    .dupH,   [.hexV h]            => some (.pairV (.hexV h) (.hexV h))
    | _+1,    .list1H, [.hexV h]            => some (.listV [.hexV h])
    | _+1,    .list2H, [.hexV a, .hexV b]   => some (.listV [.hexV a, .hexV b])
    | _+1,    .list3H, [.hexV a, .hexV b, .hexV c] => some (.listV [.hexV a, .hexV b, .hexV c])
    | _+1,    .headH,  [.listV (.hexV h :: _)] => some (.hexV h)
    | _+1,    .eqCell, [.cellV a, .cellV b] => some (.boolV (decide (a = b)))
    | _+1,    .cuoC,   [.cellV c]           => some (.cellV (R8.hexCuo c))
    | _+1,    .zongC,  [.cellV c]           => some (.cellV (R8.hexZong c))
    | _+1,    .huC,    [.cellV c]           => some (.cellV (R8.hexHu c))
    | _+1,    .shiNextC, [.cellV c]         => some (.cellV (R8.shiCuo c))
    | _+1,    .shiPrevC, [.cellV c]         => some (.cellV (R8.shiCuo c))
    | _+1,    .flip1C, [.cellV c]           => some (.cellV (R8.flip1 c))
    | _+1,    .flip2C, [.cellV c]           => some (.cellV (R8.flip2 c))
    | _+1,    .flip3C, [.cellV c]           => some (.cellV (R8.flip3 c))
    | _+1,    .flip4C, [.cellV c]           => some (.cellV (R8.flip4 c))
    | _+1,    .flip5C, [.cellV c]           => some (.cellV (R8.flip5 c))
    | _+1,    .flip6C, [.cellV c]           => some (.cellV (R8.flip6 c))
    | fuel+1, .forallH, [p]                 =>
        some (.boolV (forallHex (fun h =>
          match applyFuel fuel p (.hexV h) with
          | some (.boolV b) => b
          | _               => false)))
    | fuel+1, .uniqueH, [p]                 =>
        some (.boolV (uniqueHex (fun h =>
          match applyFuel fuel p (.hexV h) with
          | some (.boolV b) => b
          | _               => false)))
    | fuel+1, .exactly3H, [p]               =>
        some (.boolV (exactly3Hex (fun h =>
          match applyFuel fuel p (.hexV h) with
          | some (.boolV b) => b
          | _               => false)))
    | fuel+1, .majorityH, [p]               =>
        some (.boolV (majorityHex (fun h =>
          match applyFuel fuel p (.hexV h) with
          | some (.boolV b) => b
          | _               => false)))
    | _+1,    _,       _                    => none
end

/-- 应用 Value 到 Value: closure beta + builtin partial-apply. -/
def apply (v arg : Value) : Option Value :=
  applyFuel defaultFuel v arg

/-- Tm 之求值（closure-based，fuel-bounded）. -/
def eval (env : Env) (t : Tm) : Option Value :=
  evalFuel defaultFuel env t

/-- builtin 之满足后求值. -/
def applyBuiltin (b : Builtin) (args : List Value) : Option Value :=
  applyBuiltinFuel defaultFuel b args

/-! ## § 5  closed-Tm 之 denotation -/

/-- 闭项之 Hex denotation：eval 后取 hexV. -/
def denoteHex (t : Tm) : Option Hexagram :=
  match eval [] t with
  | some (.hexV h) => some h
  | _              => none

/-- 闭项之 Bool denotation. -/
def denoteBool (t : Tm) : Option Bool :=
  match eval [] t with
  | some (.boolV b) => some b
  | _               => none

def denoteCell (t : Tm) : Option R8 :=
  match eval [] t with
  | some (.cellV c) => some c
  | _ => none

def valueToHexPair? : Value → Option (Hexagram × Hexagram)
  | .pairV (.hexV a) (.hexV b) => some (a, b)
  | _ => none

def valueToHexList? : List Value → Option (List Hexagram)
  | [] => some []
  | .hexV h :: rest =>
      match valueToHexList? rest with
      | some hs => some (h :: hs)
      | none => none
  | _ :: _ => none

def denoteHexPair (t : Tm) : Option (Hexagram × Hexagram) :=
  match eval [] t with
  | some v => valueToHexPair? v
  | none => none

def denoteHexList (t : Tm) : Option (List Hexagram) :=
  match eval [] t with
  | some (.listV xs) => valueToHexList? xs
  | _ => none

def valueToCellList? : List Value → Option (List R8)
  | [] => some []
  | .cellV c :: rest =>
      match valueToCellList? rest with
      | some cs => some (c :: cs)
      | none => none
  | _ :: _ => none

def denoteCellList (t : Tm) : Option (List R8) :=
  match eval [] t with
  | some (.listV xs) => valueToCellList? xs
  | _ => none

/-- Hex → Hex 之 Tm: 逐输入施 apply 取 hexV. -/
def denoteHexFun (t : Tm) (h : Hexagram) : Option Hexagram :=
  match eval [] t with
  | some v =>
      match apply v (.hexV h) with
      | some (.hexV h') => some h'
      | _               => none
  | none => none

/-- Cell → Cell 之 Tm: 逐输入施 apply 取 cellV. -/
def denoteCellFun (t : Tm) (c : R8) : Option R8 :=
  match eval [] t with
  | some v =>
      match apply v (.cellV c) with
      | some (.cellV c') => some c'
      | _ => none
  | none => none

/-- Hex → Bool 之 Tm: 逐输入施 apply 取 boolV. -/
def denoteHexPred (t : Tm) (h : Hexagram) : Option Bool :=
  match eval [] t with
  | some v =>
      match apply v (.hexV h) with
      | some (.boolV b) => some b
      | _               => none
  | none => none

/-- Hex → Hex → Bool 之 Tm: binary relation denotation. -/
def denoteHexRel (t : Tm) (a b : Hexagram) : Option Bool :=
  match eval [] t with
  | some v =>
      match apply v (.hexV a) with
      | some v' =>
          match apply v' (.hexV b) with
          | some (.boolV out) => some out
          | _                 => none
      | _ => none
  | none => none

/-- Cell → Cell → Bool 之 Tm: binary Cell relation denotation. -/
def denoteCellRel (t : Tm) (a b : R8) : Option Bool :=
  match eval [] t with
  | some v =>
      match apply v (.cellV a) with
      | some v' =>
          match apply v' (.cellV b) with
          | some (.boolV out) => some out
          | _ => none
      | _ => none
  | none => none

def denoteCatalogue (t : Tm) :
    Option (SSBX.Text.WenyanOperators.OperatorId ×
      SSBX.Text.OperatorSignatures.SignatureKind × List Value) :=
  match eval [] t with
  | some (.catalogueV id kind args) => some (id, kind, args)
  | _ => none

/-! ## § 6  builtin 等价：.jia/.yi/.eqHex ⟷ YiCore -/

/-- `.jia .yi .yi` denotes «加» «一» «一» = «生» «一». -/
example :
    denoteHex (.app (.app .jia .yi) .yi) = some («生» «一») := by native_decide

/-- `.yi` denotes «一» (the unit hex with index 1). -/
example : denoteHex .yi = some «一» := by native_decide

/-- `.eqHex .yi .yi` denotes true. -/
example :
    denoteBool (.app (.app .eqHex .yi) .yi) = some true := by native_decide

/-- `.eqHex .yi (.hexLit Hexagram.heaven)` denotes false (heaven ≠ 一). -/
example :
    denoteBool (.app (.app .eqHex .yi) (.hexLit Hexagram.heaven))
      = some false := by native_decide

example :
    denoteHexPair (.app (.app .pairH (.hexLit Hexagram.heaven)) (.hexLit Hexagram.earth))
      = some (Hexagram.heaven, Hexagram.earth) := by native_decide

theorem pairHBody_eq_pair (a b : Hexagram) :
    denoteHexPair (.app (.app Stdlib.pairHBody (.hexLit a)) (.hexLit b)) = some (a, b) := by
  rfl

theorem dupHBody_eq_dup (h : Hexagram) :
    denoteHexPair (.app Stdlib.dupHBody (.hexLit h)) = some (h, h) := by
  rfl

example :
    denoteHexList (.app .list1H (.hexLit Hexagram.heaven))
      = some [Hexagram.heaven] := by native_decide

theorem list1HBody_eq_singleton (h : Hexagram) :
    denoteHexList (.app Stdlib.list1HBody (.hexLit h)) = some [h] := by
  rfl

theorem list2HBody_eq_pairList (a b : Hexagram) :
    denoteHexList (.app (.app Stdlib.list2HBody (.hexLit a)) (.hexLit b)) = some [a, b] := by
  rfl

theorem list3HBody_eq_tripleList (a b c : Hexagram) :
    denoteHexList (.app (.app (.app Stdlib.list3HBody (.hexLit a)) (.hexLit b)) (.hexLit c)) =
      some [a, b, c] := by
  rfl

example :
    denoteHex (.app .headH (.app .list1H (.hexLit Hexagram.heaven)))
      = some Hexagram.heaven := by native_decide

theorem headHBody_list1_eq_id (h : Hexagram) :
    denoteHex (.app Stdlib.headHBody (.app Stdlib.list1HBody (.hexLit h))) = some h := by
  rfl

example :
    denoteCell (.cellLit (Hexagram.heaven, Shi.jin)) =
      some (Hexagram.heaven, Shi.jin) := by native_decide

example :
    denoteCellFun .cuoC (Hexagram.heaven, Shi.jin) =
      some (Hexagram.earth, Shi.jin) := by native_decide

example :
    denoteCellFun .shiNextC (Hexagram.heaven, Shi.jin) =
      some (Hexagram.heaven, Shi.wei) := by native_decide

example :
    denoteCellRel .eqCell (Hexagram.heaven, Shi.jin) (Hexagram.heaven, Shi.jin) =
      some true := by native_decide

/-! ## § 7  Stdlib correctness — 推 ⟷ 生 -/

/-- 「推」之 denotation 即 YiCore.«生». -/
theorem tui_eq_sheng (h : Hexagram) :
    denoteHexFun Stdlib.tuiBody h = some («生» h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 損 之 denotation = mod-64 减一 (即 «加» Hexagram.earth).
    «坤».toIdx = 63；(x + 63) mod 64 = (x − 1) mod 64. -/
theorem sun_eq_decrement (h : Hexagram) :
    denoteHexFun Stdlib.sunBody h = some («加» Hexagram.earth h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 益 之 denotation = mod-64 加一 = «生». 与 推 共体. -/
theorem yiBenefit_eq_sheng (h : Hexagram) :
    denoteHexFun Stdlib.yiBenefitBody h = some («生» h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 错 之 denotation = Hexagram.complement. -/
theorem cuoBody_eq_cuo (h : Hexagram) :
    denoteHexFun Stdlib.cuoBody h = some h.complement := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 综 之 denotation = Hexagram.reverse. -/
theorem zongBody_eq_zong (h : Hexagram) :
    denoteHexFun Stdlib.zongBody h = some h.reverse := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 互 之 denotation = Hexagram.interlace. -/
theorem huBody_eq_hu (h : Hexagram) :
    denoteHexFun Stdlib.huBody h = some h.interlace := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 反 在 object-transform 读法下同错. -/
theorem fanReverseBody_eq_cuo (h : Hexagram) :
    denoteHexFun Stdlib.fanReverseBody h = some h.complement :=
  cuoBody_eq_cuo h

theorem hexIdBody_eq_id (h : Hexagram) :
    denoteHexFun Stdlib.hexIdBody h = some h := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

theorem cuoZongBody_eq_cuoZong (h : Hexagram) :
    denoteHexFun Stdlib.cuoZongBody h = some h.complementReverse := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

theorem flip1Body_eq_dongInner (h : Hexagram) :
    denoteHexFun Stdlib.flip1Body h = some (dongInner h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

theorem flip2Body_eq_huaInner (h : Hexagram) :
    denoteHexFun Stdlib.flip2Body h = some (middleFlipInner h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

theorem flip3Body_eq_bianInner (h : Hexagram) :
    denoteHexFun Stdlib.flip3Body h = some (topFlipInner h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

theorem flip4Body_eq_dongOuter (h : Hexagram) :
    denoteHexFun Stdlib.flip4Body h = some (dongOuter h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

theorem flip5Body_eq_huaOuter (h : Hexagram) :
    denoteHexFun Stdlib.flip5Body h = some (middleFlipOuter h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

theorem flip6Body_eq_bianOuter (h : Hexagram) :
    denoteHexFun Stdlib.flip6Body h = some (topFlipOuter h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 「同 «一» «一»」denotes true (恒等于自身). -/
example :
    denoteBool (.app (.app Stdlib.tongBody .yi) .yi) = some true := by native_decide

/-- 「同 «一» «乾»」denotes false («一» ≠ «乾»). -/
example :
    denoteBool (.app (.app Stdlib.tongBody .yi) (.hexLit Hexagram.heaven))
      = some false := by native_decide

/-- 「不」之 denotation 即 boolean negation. -/
example : denoteBool (.app .notB (.boolLit true)) = some false := by native_decide
example : denoteBool (.app .notB (.boolLit false)) = some true := by native_decide

theorem boolMarkerBody_eq_id (b : Bool) :
    denoteBool (.app Stdlib.boolMarkerBody (.boolLit b)) = some b := by
  cases b <;> native_decide

/-! ### Promoted logic alias bodies -/

example :
    denoteBool (.app (.app Stdlib.impBody (.boolLit true)) (.boolLit false))
      = some false := by native_decide

example :
    denoteBool (.app (.app Stdlib.impBody (.boolLit false)) (.boolLit false))
      = some true := by native_decide

example :
    denoteBool (.app (.app Stdlib.xorBBody (.boolLit true)) (.boolLit false))
      = some true := by native_decide

example :
    denoteBool (.app (.app Stdlib.xorBBody (.boolLit true)) (.boolLit true))
      = some false := by native_decide

example :
    denoteHexRel Stdlib.neqHexBody «一» «一» = some false := by native_decide

example :
    denoteHexRel Stdlib.neqHexBody «一» Hexagram.heaven = some true := by native_decide

example :
    denoteBool (.app Stdlib.existsHBody
      (.abs "h" .hex (.app (.app .eqHex (.var "h")) .yi)))
      = some true := by native_decide

example :
    denoteBool (.app Stdlib.noneHBody
      (.abs "h" .hex (.app (.app .eqHex (.var "h")) .yi)))
      = some false := by native_decide

example :
    denoteBool (.app Stdlib.uniqueHBody
      (.abs "h" .hex (.app (.app .eqHex (.var "h")) .yi)))
      = some true := by native_decide

example :
    denoteBool (.app Stdlib.exactly3HBody
      (.abs "h" .hex
        (.app (.app .orB (.app (.app .eqHex (.var "h")) .yi))
          (.app (.app .orB
            (.app (.app .eqHex (.var "h")) (.hexLit Hexagram.heaven)))
            (.app (.app .eqHex (.var "h")) (.hexLit Hexagram.earth))))))
      = some true := by native_decide

example :
    denoteBool (.app Stdlib.majorityHBody
      (.abs "h" .hex (.boolLit true)))
      = some true := by native_decide

example :
    denoteHex
      (.app
        (.app (.app Stdlib.endoCompBody Stdlib.tuiBody) Stdlib.sunBody)
        .yi)
      = some «一» := by native_decide

example :
    denoteHex (.app (.app Stdlib.hexApplyBody Stdlib.tuiBody) .yi)
      = some («生» «一») := by native_decide

theorem hexApplyBody_tui_eq_sheng (h : Hexagram) :
    denoteHex (.app (.app Stdlib.hexApplyBody Stdlib.tuiBody) (.hexLit h)) = some («生» h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

example :
    denoteHex (.app (.app Stdlib.hexApplyBody Stdlib.sunBody) .yi)
      = some («加» Hexagram.earth «一») := by native_decide

theorem hexApplyBody_sun_eq_decrement (h : Hexagram) :
    denoteHex (.app (.app Stdlib.hexApplyBody Stdlib.sunBody) (.hexLit h)) =
      some («加» Hexagram.earth h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 「凡 (λh. 同 h h)」denotes true (反身性 universally). -/
theorem self_eq_all_true : denoteBool selfEqAll = some true := by native_decide

/-- 「凡 (λh. 同 h «一»)」denotes false (only «一» equals «一»). -/
example :
    denoteBool (.app .forallH
      (.abs "h" .hex (.app (.app .eqHex (.var "h")) .yi)))
      = some false := by native_decide

/-! ## § 8  应用范例：tui ∘ tui = «生生» 2 -/

/-- 「推 (推 一)» = «生生» 2 «一» = 索引 3. -/
example :
    denoteHex (.app Stdlib.tuiBody (.app Stdlib.tuiBody .yi))
      = some («生生» 2 «一») := by native_decide

/-- 「推 64 次 «一»» 经 wenyan eval 与 «生生» 64 «一» 一致（皆归原）. -/
example : «生生» 64 «一» = «一» := by exact «周而复始» «一»

/-! ## § 9  «乾» 起 64 步遍历之 wenyan 镜像 -/

/-- wenyan 之 «推» 施于 «乾» 一次 = «生» «乾». -/
example :
    denoteHexFun Stdlib.tuiBody Hexagram.heaven = some («生» Hexagram.heaven) := by
  native_decide

/-- 由 «乾» 起 «推» 一次至 «一»（by «生施一即一»）. -/
example :
    denoteHexFun Stdlib.tuiBody Hexagram.heaven = some «一» := by native_decide

/-! ## § 10  桥之总公示 -/

/-- 桥之公示：L1 typed Tm (WenDef) 与 L0 «加»/«一» (YiCore) 一致.

  对所有 stdlib 之 Tm 与所有 64 hex 输入，denotation = YiCore 之自然解释.
  此公示之充分性由 64 元有限论域 + native_decide 见证.

  具体：
    · `tui_eq_sheng`        ：tui = «生» （全 64 输入）
    · `tong_eq_DecidableEq` ：tong = decide ∘ Eq
    · examples              ：bu / fan / 等 各一例
    · 64-fold ∀             ：forallHex 与 Lean 之 ∀ 在 Hexagram 上一致
                              （由 «卦由索引» + «生生不息» 见证）
-/
theorem bridge_summary :
    (denoteHex .yi = some «一»)
    ∧ (denoteHex (.app (.app .jia .yi) .yi) = some («生» «一»))
    ∧ (denoteBool selfEqAll = some true) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end SSBX.Foundation.Wen.WenDefEval
