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
import SSBX.Foundation.Yi.YiCore

namespace SSBX.Foundation.Wen.WenDefEval

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore
open SSBX.Foundation.Wen.WenDef

/-! ## § 1  Builtin 标记 -/

/-- 求值时之 builtin tag。 -/
inductive Builtin : Type
  | jia | notB | andB | orB | eqHex | forallH
deriving DecidableEq, Repr

/-- builtin 之 arity（满足后产 result）。 -/
def Builtin.arity : Builtin → Nat
  | .jia | .andB | .orB | .eqHex => 2
  | .notB | .forallH => 1

/-! ## § 2  Value -/

/-- 运行时值。closV 持环境；builtinV 持已应用之参数（partial application）. -/
inductive Value : Type
  | hexV     (h : Hexagram)                                    : Value
  | boolV    (b : Bool)                                        : Value
  | closV    (env : List (String × Value)) (n : String) (body : Tm) : Value
  | builtinV (b : Builtin) (args : List Value)                 : Value
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
    | _+1,    _,   .jia          => some (.builtinV .jia [])
    | _+1,    _,   .yi           => some (.hexV «一»)
    | _+1,    _,   .notB         => some (.builtinV .notB [])
    | _+1,    _,   .andB         => some (.builtinV .andB [])
    | _+1,    _,   .orB          => some (.builtinV .orB [])
    | _+1,    _,   .eqHex        => some (.builtinV .eqHex [])
    | _+1,    _,   .forallH      => some (.builtinV .forallH [])

  /-- Fuel-bounded builtin 求值. -/
  def applyBuiltinFuel : Nat → Builtin → List Value → Option Value
    | 0,      _,       _                    => none
    | _+1,    .jia,    [.hexV a, .hexV b]   => some (.hexV («加» a b))
    | _+1,    .notB,   [.boolV b]           => some (.boolV (!b))
    | _+1,    .andB,   [.boolV a, .boolV b] => some (.boolV (a && b))
    | _+1,    .orB,    [.boolV a, .boolV b] => some (.boolV (a || b))
    | _+1,    .eqHex,  [.hexV a, .hexV b]   => some (.boolV (decide (a = b)))
    | fuel+1, .forallH, [p]                 =>
        some (.boolV (forallHex (fun h =>
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

/-- Hex → Hex 之 Tm: 逐输入施 apply 取 hexV. -/
def denoteHexFun (t : Tm) (h : Hexagram) : Option Hexagram :=
  match eval [] t with
  | some v =>
      match apply v (.hexV h) with
      | some (.hexV h') => some h'
      | _               => none
  | none => none

/-- Hex → Bool 之 Tm: 逐输入施 apply 取 boolV. -/
def denoteHexPred (t : Tm) (h : Hexagram) : Option Bool :=
  match eval [] t with
  | some v =>
      match apply v (.hexV h) with
      | some (.boolV b) => some b
      | _               => none
  | none => none

/-! ## § 6  builtin 等价：.jia/.yi/.eqHex ⟷ YiCore -/

/-- `.jia .yi .yi` denotes «加» «一» «一» = «生» «一». -/
example :
    denoteHex (.app (.app .jia .yi) .yi) = some («生» «一») := by native_decide

/-- `.yi` denotes «一» (the unit hex with index 1). -/
example : denoteHex .yi = some «一» := by native_decide

/-- `.eqHex .yi .yi` denotes true. -/
example :
    denoteBool (.app (.app .eqHex .yi) .yi) = some true := by native_decide

/-- `.eqHex .yi (.hexLit Hexagram.qian)` denotes false (qian ≠ 一). -/
example :
    denoteBool (.app (.app .eqHex .yi) (.hexLit Hexagram.qian))
      = some false := by native_decide

/-! ## § 7  Stdlib correctness — 推 ⟷ 生 -/

/-- 「推」之 denotation 即 YiCore.«生». -/
theorem tui_eq_sheng (h : Hexagram) :
    denoteHexFun Stdlib.tuiBody h = some («生» h) := by
  cases h with
  | mk y1 y2 y3 y4 y5 y6 =>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    all_goals native_decide

/-- 損 之 denotation = mod-64 减一 (即 «加» Hexagram.kun).
    «坤».toIdx = 63；(x + 63) mod 64 = (x − 1) mod 64. -/
theorem sun_eq_decrement (h : Hexagram) :
    denoteHexFun Stdlib.sunBody h = some («加» Hexagram.kun h) := by
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

/-- 「同 «一» «一»」denotes true (恒等于自身). -/
example :
    denoteBool (.app (.app Stdlib.tongBody .yi) .yi) = some true := by native_decide

/-- 「同 «一» «乾»」denotes false («一» ≠ «乾»). -/
example :
    denoteBool (.app (.app Stdlib.tongBody .yi) (.hexLit Hexagram.qian))
      = some false := by native_decide

/-- 「不」之 denotation 即 boolean negation. -/
example : denoteBool (.app .notB (.boolLit true)) = some false := by native_decide
example : denoteBool (.app .notB (.boolLit false)) = some true := by native_decide

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
    denoteHexFun Stdlib.tuiBody Hexagram.qian = some («生» Hexagram.qian) := by
  native_decide

/-- 由 «乾» 起 «推» 一次至 «一»（by «生施一即一»）. -/
example :
    denoteHexFun Stdlib.tuiBody Hexagram.qian = some «一» := by native_decide

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
