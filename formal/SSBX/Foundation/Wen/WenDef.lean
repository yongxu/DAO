/-
# WenDef — 文之定义机制（typed lambda over 64-hexagram universe）

Path 丙 § 风险 3 之完全缓解：
  baguaWen 22 内核 + WenDef 扩展 = wenyan-operators 281 字之全体表达力。

## 论证

由 64 元有限论域 + Church-Turing 之退化形式：
  ∀ wenyan-op : Hexagram^k → (Hexagram | Bool)^m,
    ∃ baguaWen 程序 + 用户 def, 其 denotation = 该 op

故 wenyan-ops 之全体可由 baguaWen 22 + 算子组合 + 用户 def 表达。
不可计算的「∀」「□」在 64 论域上退化为有限合取，全 `Decidable`，全可 `native_decide`。

## 设计

类型 (Ty):   Hex | Bool | Arr a b

项 (Tm):     var | abs | app | hexLit | boolLit
            + 10 内核 primitives:
              jia (加) :  Hex → Hex → Hex
              yi  (一) :  Hex
              notB (不):  Bool → Bool
              andB (並):  Bool → Bool → Bool
              orB  (或):  Bool → Bool → Bool
              eqHex (同): Hex → Hex → Bool
              forallH (凡): (Hex → Bool) → Bool      -- 64-fold ∀，有限可决
              uniqueH / exactly3H / majorityH: finite Hex counters
              cuoH (错): Hex → Hex
              zongH (综): Hex → Hex
              huH (互): Hex → Hex
              cuoZongH: Hex → Hex
              flip1H/flip2H/flip3H: Hex → Hex

命名约定:
  · 天干 10 字（甲乙丙丁戊己庚辛壬癸）— 中性变量名
  · ASCII 标识符（[a-zA-Z][a-zA-Z0-9_]*）
  · 不在 `Bagua.BaguaWenSpec.reservedTokens` 内（即 baguaWen 22 之外）

## 复用

`Jian.JianSTLC` 之 untyped Lam β-reduction 已 0 sorry 完毕（subst_preserves_enc + simulation）.
`Tm` 之 operational semantics 经类型擦除可映入 `Lam`，由 `JianSTLC.simulation` 见证.
该映射定于 M2 之 `WenEval.lean`，本文件仅给类型层 + WenDef 结构.

## 状态

0 sorry / 0 axiom. 仅类型层；operational semantics 见 M2.
-/
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.Cell192
import SSBX.Foundation.Bagua.BaguaWenSpec
import SSBX.Text.OperatorSignatures

namespace SSBX.Foundation.Wen.WenDef

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaWenSpec
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorSignatures

/-! ## § 1  简单类型 -/

/-- 简单类型：Hex（卦，64 元）、Bool、函数。 -/
inductive Ty : Type
  | hex
  | bool
  | cell
  | catalogue (kind : SignatureKind)
  | prod (fst snd : Ty)
  | list (elem : Ty)
  | arr (dom cod : Ty)
deriving DecidableEq, Repr

/-! ## § 2  项 -/

/-- 文之项：λ + app + var + 字面值 + 10 个内核 primitives。 -/
inductive Tm : Type
  | var     (n : String)               : Tm
  | abs     (n : String) (t : Ty) (body : Tm) : Tm
  | app     (f x : Tm)                 : Tm
  | hexLit  (h : Hexagram)             : Tm
  | boolLit (b : Bool)                 : Tm
  | cellLit (c : Cell192)              : Tm
  | jia                                : Tm  -- 加 :  Hex → Hex → Hex
  | yi                                 : Tm  -- 一 :  Hex
  | notB                               : Tm  -- 不 :  Bool → Bool
  | andB                               : Tm  -- 並 :  Bool → Bool → Bool
  | orB                                : Tm  -- 或 :  Bool → Bool → Bool
  | eqHex                              : Tm  -- 同 :  Hex → Hex → Bool
  | forallH                            : Tm  -- 凡 :  (Hex → Bool) → Bool
  | uniqueH                            : Tm  -- 唯 :  (Hex → Bool) → Bool
  | exactly3H                          : Tm  -- 三 :  (Hex → Bool) → Bool
  | majorityH                          : Tm  -- 過半 : (Hex → Bool) → Bool
  | cuoH                               : Tm  -- 错 :  Hex → Hex
  | zongH                              : Tm  -- 综 :  Hex → Hex
  | huH                                : Tm  -- 互 :  Hex → Hex
  | cuoZongH                           : Tm  -- 错综 : Hex → Hex
  | flip1H                             : Tm  -- 初爻 flip : Hex → Hex
  | flip2H                             : Tm  -- 二爻 flip : Hex → Hex
  | flip3H                             : Tm  -- 三爻 flip : Hex → Hex
  | pairH                              : Tm  -- pair : Hex → Hex → Hex×Hex
  | dupH                               : Tm  -- dup : Hex → Hex×Hex
  | list1H                             : Tm  -- singleton : Hex → List Hex
  | list2H                             : Tm  -- pair-list : Hex → Hex → List Hex
  | headH                              : Tm  -- head : List Hex → Hex
  | eqCell                             : Tm  -- Cell → Cell → Bool
  | cuoC                               : Tm  -- Cell → Cell, preserve 时
  | zongC                              : Tm  -- Cell → Cell, preserve 时
  | huC                                : Tm  -- Cell → Cell, preserve 时
  | shiNextC                           : Tm  -- Cell → Cell, 时态前进
  | shiPrevC                           : Tm  -- Cell → Cell, 时态后退
  | flip1C                             : Tm  -- Cell → Cell, y1 flip
  | flip2C                             : Tm  -- Cell → Cell, y2 flip
  | flip3C                             : Tm  -- Cell → Cell, y3 flip
  | flip4C                             : Tm  -- Cell → Cell, y4 flip
  | flip5C                             : Tm  -- Cell → Cell, y5 flip
  | flip6C                             : Tm  -- Cell → Cell, y6 flip
  | catalogue1 (id : OperatorId) (a : Tm) : Tm
  | catalogue2 (id : OperatorId) (a b : Tm) : Tm
  | catalogue3 (id : OperatorId) (a b c : Tm) : Tm
deriving DecidableEq, Repr

/-! ## § 3  类型检查 -/

/-- 上下文：变量名 → 类型。 -/
abbrev Ctx := List (String × Ty)

/-- 在上下文中查找变量类型。 -/
def Ctx.lookup : Ctx → String → Option Ty
  | [], _ => none
  | (n, t) :: rest, name => if n = name then some t else rest.lookup name

/-- 类型检查：返回项的类型 (well-typed) 或 none (ill-typed)。
    总函数（结构递归 on Tm）。 -/
def typeCheck : Ctx → Tm → Option Ty
  | ctx, .var n => ctx.lookup n
  | ctx, .abs n t body =>
      match typeCheck ((n, t) :: ctx) body with
      | some t' => some (.arr t t')
      | none    => none
  | ctx, .app f x =>
      match typeCheck ctx f, typeCheck ctx x with
      | some (.arr a b), some a' => if a = a' then some b else none
      | _, _ => none
  | _, .hexLit _  => some .hex
  | _, .boolLit _ => some .bool
  | _, .cellLit _ => some .cell
  | _, .jia       => some (.arr .hex (.arr .hex .hex))
  | _, .yi        => some .hex
  | _, .notB      => some (.arr .bool .bool)
  | _, .andB      => some (.arr .bool (.arr .bool .bool))
  | _, .orB       => some (.arr .bool (.arr .bool .bool))
  | _, .eqHex     => some (.arr .hex (.arr .hex .bool))
  | _, .forallH   => some (.arr (.arr .hex .bool) .bool)
  | _, .uniqueH   => some (.arr (.arr .hex .bool) .bool)
  | _, .exactly3H => some (.arr (.arr .hex .bool) .bool)
  | _, .majorityH => some (.arr (.arr .hex .bool) .bool)
  | _, .cuoH      => some (.arr .hex .hex)
  | _, .zongH     => some (.arr .hex .hex)
  | _, .huH       => some (.arr .hex .hex)
  | _, .cuoZongH  => some (.arr .hex .hex)
  | _, .flip1H    => some (.arr .hex .hex)
  | _, .flip2H    => some (.arr .hex .hex)
  | _, .flip3H    => some (.arr .hex .hex)
  | _, .pairH     => some (.arr .hex (.arr .hex (.prod .hex .hex)))
  | _, .dupH      => some (.arr .hex (.prod .hex .hex))
  | _, .list1H    => some (.arr .hex (.list .hex))
  | _, .list2H    => some (.arr .hex (.arr .hex (.list .hex)))
  | _, .headH     => some (.arr (.list .hex) .hex)
  | _, .eqCell    => some (.arr .cell (.arr .cell .bool))
  | _, .cuoC      => some (.arr .cell .cell)
  | _, .zongC     => some (.arr .cell .cell)
  | _, .huC       => some (.arr .cell .cell)
  | _, .shiNextC  => some (.arr .cell .cell)
  | _, .shiPrevC  => some (.arr .cell .cell)
  | _, .flip1C    => some (.arr .cell .cell)
  | _, .flip2C    => some (.arr .cell .cell)
  | _, .flip3C    => some (.arr .cell .cell)
  | _, .flip4C    => some (.arr .cell .cell)
  | _, .flip5C    => some (.arr .cell .cell)
  | _, .flip6C    => some (.arr .cell .cell)
  | ctx, .catalogue1 id a =>
      let sig := fullSignatureFor id
      if sig.arity = 1 && (typeCheck ctx a).isSome then
        some (.catalogue sig.kind)
      else
        none
  | ctx, .catalogue2 id a b =>
      let sig := fullSignatureFor id
      if sig.arity = 2 && (typeCheck ctx a).isSome && (typeCheck ctx b).isSome then
        some (.catalogue sig.kind)
      else
        none
  | ctx, .catalogue3 id a b c =>
      let sig := fullSignatureFor id
      if sig.arity = 3 && (typeCheck ctx a).isSome && (typeCheck ctx b).isSome
          && (typeCheck ctx c).isSome then
        some (.catalogue sig.kind)
      else
        none

/-! ## § 4  命名空间 -/

/-- 天干 10 字：中性变量名空间。 -/
def heavenlyStems : List String :=
  ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"]

/-- ASCII 标识符判定：开头字母，余下字母/数字/下划线。 -/
def isAsciiIdent (s : String) : Bool :=
  match s.toList with
  | []        => false
  | c :: rest => c.isAlpha && rest.all (fun c => c.isAlpha || c.isDigit || c = '_')

/-- 合法 def 名：天干 ∪ ASCII，不在 baguaWen 22 reservedTokens 内。 -/
def isValidName (s : String) : Bool :=
  (heavenlyStems.contains s || isAsciiIdent s) &&
  !reservedTokens.contains s

/-! ## § 5  WenDef 结构 -/

/-- 一个 wenyan 定义：name + body + 类型签名 + 名合度凭据 + 类型一致凭据。 -/
structure WenDef where
  name           : String
  body           : Tm
  bodyType       : Ty
  validName      : isValidName name = true
  bodyTypechecks : typeCheck [] body = some bodyType

/-! ## § 6  命名空间 sanity -/

theorem heavenlyStems_length : heavenlyStems.length = 10 := by native_decide

theorem heavenlyStems_all_valid :
    heavenlyStems.all isValidName = true := by native_decide

theorem heavenlyStems_disjoint_reserved :
    heavenlyStems.all (fun s => !reservedTokens.contains s) = true := by native_decide

/-- ASCII 标识符之范例皆为合度名。 -/
example : isValidName "tui"     = true := by native_decide
example : isValidName "bi"      = true := by native_decide
example : isValidName "biModal" = true := by native_decide

/-- 与 baguaWen 22 重之 CJK token 不合度（保命名空间分离）。 -/
example : isValidName "推"  = false := by native_decide
example : isValidName "终"  = false := by native_decide
example : isValidName "比爻" = false := by native_decide

/-- 数字开头之 ASCII 不合度。 -/
example : isValidName "1tui"   = false := by native_decide

/-- 空串不合度。 -/
example : isValidName ""       = false := by native_decide

/-! ## § 7  Stdlib 示例：wenyan-operators 之 def

  每条用拼音 / ASCII 作 WenDef.name（避免与 baguaWen 22 之 CJK 冲突）；
  CJK 名仅作 Lean-level navigation 与文档参考。
-/

namespace Stdlib

/-! ### T-10 推（推动 — 沿轴推进；孟子「推恩足以保四海」）

  实现：λx:Hex. 加 一 x  （即 YiCore.«生»，64-cyclic group action）.
  类型：Hex → Hex.
-/

def tuiBody : Tm :=
  .abs "x" .hex (.app (.app .jia .yi) (.var "x"))

theorem tuiBody_typed :
    typeCheck [] tuiBody = some (.arr .hex .hex) := by native_decide

def tuiDef : WenDef where
  name           := "tui"
  body           := tuiBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### R-8 比（邻接 — 易·彖「比，辅也」）

  第一近似实现：λa b:Hex. 同 a b （恒等谓词）.
  Refined 版（限于「相邻爻位」）留待 stdlib v2.
  类型：Hex → Hex → Bool.
-/

def biBody : Tm :=
  .abs "a" .hex (.abs "b" .hex (.app (.app .eqHex (.var "a")) (.var "b")))

theorem biBody_typed :
    typeCheck [] biBody = some (.arr .hex (.arr .hex .bool)) := by native_decide

def biDef : WenDef where
  name           := "bi"
  body           := biBody
  bodyType       := .arr .hex (.arr .hex .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### N-1 不（否定）

  实现：直接是 .notB primitive.
  类型：Bool → Bool.
-/

def buBody : Tm := .notB

theorem buBody_typed :
    typeCheck [] buBody = some (.arr .bool .bool) := by native_decide

def buDef : WenDef where
  name           := "bu"
  body           := buBody
  bodyType       := .arr .bool .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### M-1 必（必然 — modal □）

  在 64 元有限论域上，∀h ≡ □（固定可达关系）.
  实现：直接是 .forallH primitive.
  类型：(Hex → Bool) → Bool.
-/

def biModalBody : Tm := .forallH

theorem biModalBody_typed :
    typeCheck [] biModalBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def biModalDef : WenDef where
  name           := "biModal"
  body           := biModalBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### I-1 同（恒等关系）

  实现：直接是 .eqHex primitive.
  类型：Hex → Hex → Bool.
-/

def tongBody : Tm := .eqHex

theorem tongBody_typed :
    typeCheck [] tongBody = some (.arr .hex (.arr .hex .bool)) := by native_decide

def tongDef : WenDef where
  name           := "tong"
  body           := tongBody
  bodyType       := .arr .hex (.arr .hex .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Q-1 凡（universal 量化）

  实现：直接是 .forallH primitive (有限 ∀ over 64).
  类型：(Hex → Bool) → Bool.
-/

def fanBody : Tm := .forallH

theorem fanBody_typed :
    typeCheck [] fanBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def fanDef : WenDef where
  name           := "fan"
  body           := fanBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### T-12 損（减一 / 反生）

  实现：λx:Hex. 加 «坤» x.
  «坤» 之索引为 63，故 (x + 63) mod 64 = (x − 1) mod 64，即 mod-64 减一.
  与 T-13 益 互逆；与 T-10 推 一加一减.
  类型：Hex → Hex.
-/

def sunBody : Tm :=
  .abs "x" .hex (.app (.app .jia (.hexLit Hexagram.kun)) (.var "x"))

theorem sunBody_typed :
    typeCheck [] sunBody = some (.arr .hex .hex) := by native_decide

def sunDef : WenDef where
  name           := "sun"
  body           := sunBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### T-13 益（加一 / 同推）

  实现：λx:Hex. 加 一 x  （即 YiCore.«生»，与 T-10 推 共体）.
  以独立 WenDef 收录，明示 catalogue 中「益 = 推」之同义.
  类型：Hex → Hex.
-/

def yiBenefitBody : Tm :=
  .abs "x" .hex (.app (.app .jia .yi) (.var "x"))

theorem yiBenefitBody_typed :
    typeCheck [] yiBenefitBody = some (.arr .hex .hex) := by native_decide

def yiBenefitDef : WenDef where
  name           := "yiBenefit"
  body           := yiBenefitBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Z-5 / Z-6 / Z-3 / T-6 exact Hex transforms

  这些对应 `Yi.Hexagram` 已证明的结构算子，不从 catalogue 文义临时解释。
-/

def cuoBody : Tm := .cuoH

theorem cuoBody_typed :
    typeCheck [] cuoBody = some (.arr .hex .hex) := by native_decide

def cuoDef : WenDef where
  name           := "cuo"
  body           := cuoBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def zongBody : Tm := .zongH

theorem zongBody_typed :
    typeCheck [] zongBody = some (.arr .hex .hex) := by native_decide

def zongDef : WenDef where
  name           := "zong"
  body           := zongBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def huBody : Tm := .huH

theorem huBody_typed :
    typeCheck [] huBody = some (.arr .hex .hex) := by native_decide

def huDef : WenDef where
  name           := "hu"
  body           := huBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def fanReverseBody : Tm := .cuoH

theorem fanReverseBody_typed :
    typeCheck [] fanReverseBody = some (.arr .hex .hex) := by native_decide

def fanReverseDef : WenDef where
  name           := "fanReverse"
  body           := fanReverseBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def hexIdBody : Tm :=
  .abs "x" .hex (.var "x")

theorem hexIdBody_typed :
    typeCheck [] hexIdBody = some (.arr .hex .hex) := by native_decide

def hexIdDef : WenDef where
  name           := "hexId"
  body           := hexIdBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def cuoZongBody : Tm := .cuoZongH

theorem cuoZongBody_typed :
    typeCheck [] cuoZongBody = some (.arr .hex .hex) := by native_decide

def cuoZongDef : WenDef where
  name           := "cuoZong"
  body           := cuoZongBody
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip1Body : Tm := .flip1H

theorem flip1Body_typed :
    typeCheck [] flip1Body = some (.arr .hex .hex) := by native_decide

def flip1Def : WenDef where
  name           := "flip1"
  body           := flip1Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip2Body : Tm := .flip2H

theorem flip2Body_typed :
    typeCheck [] flip2Body = some (.arr .hex .hex) := by native_decide

def flip2Def : WenDef where
  name           := "flip2"
  body           := flip2Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

def flip3Body : Tm := .flip3H

theorem flip3Body_typed :
    typeCheck [] flip3Body = some (.arr .hex .hex) := by native_decide

def flip3Def : WenDef where
  name           := "flip3"
  body           := flip3Body
  bodyType       := .arr .hex .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Logic and identity aliases promoted from catalogue-only rows

  These bodies reuse the existing `Bool`, `Hex`, and finite `forallH` core.
  They deliberately avoid catalogue rows that require new carriers such as
  `Cell192`, paths, text acts, modal frames, or domain-specific state.
-/

def impBody : Tm :=
  .abs "p" .bool
    (.abs "q" .bool
      (.app (.app .orB (.app .notB (.var "p"))) (.var "q")))

theorem impBody_typed :
    typeCheck [] impBody = some (.arr .bool (.arr .bool .bool)) := by native_decide

def impDef : WenDef where
  name           := "imp"
  body           := impBody
  bodyType       := .arr .bool (.arr .bool .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def neqHexBody : Tm :=
  .abs "a" .hex
    (.abs "b" .hex
      (.app .notB (.app (.app .eqHex (.var "a")) (.var "b"))))

theorem neqHexBody_typed :
    typeCheck [] neqHexBody = some (.arr .hex (.arr .hex .bool)) := by native_decide

def neqHexDef : WenDef where
  name           := "neqHex"
  body           := neqHexBody
  bodyType       := .arr .hex (.arr .hex .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def existsHBody : Tm :=
  .abs "p" (.arr .hex .bool)
    (.app .notB
      (.app .forallH
        (.abs "x" .hex
          (.app .notB (.app (.var "p") (.var "x"))))))

theorem existsHBody_typed :
    typeCheck [] existsHBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def existsHDef : WenDef where
  name           := "existsH"
  body           := existsHBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def noneHBody : Tm :=
  .abs "p" (.arr .hex .bool)
    (.app .forallH
      (.abs "x" .hex
        (.app .notB (.app (.var "p") (.var "x")))))

theorem noneHBody_typed :
    typeCheck [] noneHBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def noneHDef : WenDef where
  name           := "noneH"
  body           := noneHBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def uniqueHBody : Tm := .uniqueH

theorem uniqueHBody_typed :
    typeCheck [] uniqueHBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def uniqueHDef : WenDef where
  name           := "uniqueH"
  body           := uniqueHBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def exactly3HBody : Tm := .exactly3H

theorem exactly3HBody_typed :
    typeCheck [] exactly3HBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def exactly3HDef : WenDef where
  name           := "exactly3H"
  body           := exactly3HBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def majorityHBody : Tm := .majorityH

theorem majorityHBody_typed :
    typeCheck [] majorityHBody = some (.arr (.arr .hex .bool) .bool) := by native_decide

def majorityHDef : WenDef where
  name           := "majorityH"
  body           := majorityHBody
  bodyType       := .arr (.arr .hex .bool) .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def endoCompBody : Tm :=
  .abs "f" (.arr .hex .hex)
    (.abs "g" (.arr .hex .hex)
      (.abs "x" .hex
        (.app (.var "f") (.app (.var "g") (.var "x")))))

theorem endoCompBody_typed :
    typeCheck [] endoCompBody =
      some (.arr (.arr .hex .hex) (.arr (.arr .hex .hex) (.arr .hex .hex))) := by
  native_decide

def endoCompDef : WenDef where
  name           := "endoComp"
  body           := endoCompBody
  bodyType       := .arr (.arr .hex .hex) (.arr (.arr .hex .hex) (.arr .hex .hex))
  validName      := by native_decide
  bodyTypechecks := by native_decide

def hexApplyBody : Tm :=
  .abs "f" (.arr .hex .hex)
    (.abs "x" .hex
      (.app (.var "f") (.var "x")))

theorem hexApplyBody_typed :
    typeCheck [] hexApplyBody =
      some (.arr (.arr .hex .hex) (.arr .hex .hex)) := by
  native_decide

def hexApplyDef : WenDef where
  name           := "hexApply"
  body           := hexApplyBody
  bodyType       := .arr (.arr .hex .hex) (.arr .hex .hex)
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Structural truth/motion helpers -/

def boolMarkerBody : Tm :=
  .abs "p" .bool (.var "p")

theorem boolMarkerBody_typed :
    typeCheck [] boolMarkerBody = some (.arr .bool .bool) := by native_decide

def boolMarkerDef : WenDef where
  name           := "boolMarker"
  body           := boolMarkerBody
  bodyType       := .arr .bool .bool
  validName      := by native_decide
  bodyTypechecks := by native_decide

def repeatOnceBody : Tm :=
  .abs "f" (.arr .hex .hex)
    (.abs "x" .hex (.app (.var "f") (.app (.var "f") (.var "x"))))

theorem repeatOnceBody_typed :
    typeCheck [] repeatOnceBody =
      some (.arr (.arr .hex .hex) (.arr .hex .hex)) := by native_decide

def repeatOnceDef : WenDef where
  name           := "repeatOnce"
  body           := repeatOnceBody
  bodyType       := .arr (.arr .hex .hex) (.arr .hex .hex)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def eachHBody : Tm :=
  .abs "dom" (.arr .hex .bool)
    (.abs "p" (.arr .hex .bool)
      (.app .forallH
        (.abs "x" .hex
          (.app
            (.app impBody (.app (.var "dom") (.var "x")))
            (.app (.var "p") (.var "x"))))))

theorem eachHBody_typed :
    typeCheck [] eachHBody =
      some (.arr (.arr .hex .bool) (.arr (.arr .hex .bool) .bool)) := by
  native_decide

def eachHDef : WenDef where
  name           := "eachH"
  body           := eachHBody
  bodyType       := .arr (.arr .hex .bool) (.arr (.arr .hex .bool) .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Hex pair/list carrier helpers -/

def pairHBody : Tm := .pairH

theorem pairHBody_typed :
    typeCheck [] pairHBody = some (.arr .hex (.arr .hex (.prod .hex .hex))) := by
  native_decide

def pairHDef : WenDef where
  name           := "pairH"
  body           := pairHBody
  bodyType       := .arr .hex (.arr .hex (.prod .hex .hex))
  validName      := by native_decide
  bodyTypechecks := by native_decide

def dupHBody : Tm := .dupH

theorem dupHBody_typed :
    typeCheck [] dupHBody = some (.arr .hex (.prod .hex .hex)) := by native_decide

def dupHDef : WenDef where
  name           := "dupH"
  body           := dupHBody
  bodyType       := .arr .hex (.prod .hex .hex)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def list1HBody : Tm := .list1H

theorem list1HBody_typed :
    typeCheck [] list1HBody = some (.arr .hex (.list .hex)) := by native_decide

def list1HDef : WenDef where
  name           := "list1H"
  body           := list1HBody
  bodyType       := .arr .hex (.list .hex)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def list2HBody : Tm := .list2H

theorem list2HBody_typed :
    typeCheck [] list2HBody = some (.arr .hex (.arr .hex (.list .hex))) := by
  native_decide

def list2HDef : WenDef where
  name           := "list2H"
  body           := list2HBody
  bodyType       := .arr .hex (.arr .hex (.list .hex))
  validName      := by native_decide
  bodyTypechecks := by native_decide

def headHBody : Tm := .headH

theorem headHBody_typed :
    typeCheck [] headHBody = some (.arr (.list .hex) .hex) := by native_decide

def headHDef : WenDef where
  name           := "headH"
  body           := headHBody
  bodyType       := .arr (.list .hex) .hex
  validName      := by native_decide
  bodyTypechecks := by native_decide

/-! ### Cell192 carrier helpers -/

def eqCellBody : Tm := .eqCell

theorem eqCellBody_typed :
    typeCheck [] eqCellBody = some (.arr .cell (.arr .cell .bool)) := by
  native_decide

def eqCellDef : WenDef where
  name           := "eqCell"
  body           := eqCellBody
  bodyType       := .arr .cell (.arr .cell .bool)
  validName      := by native_decide
  bodyTypechecks := by native_decide

def cuoCBody : Tm := .cuoC
def zongCBody : Tm := .zongC
def huCBody : Tm := .huC
def shiNextCBody : Tm := .shiNextC
def shiPrevCBody : Tm := .shiPrevC
def flip1CBody : Tm := .flip1C
def flip2CBody : Tm := .flip2C
def flip3CBody : Tm := .flip3C
def flip4CBody : Tm := .flip4C
def flip5CBody : Tm := .flip5C
def flip6CBody : Tm := .flip6C

theorem cuoCBody_typed : typeCheck [] cuoCBody = some (.arr .cell .cell) := by native_decide
theorem zongCBody_typed : typeCheck [] zongCBody = some (.arr .cell .cell) := by native_decide
theorem huCBody_typed : typeCheck [] huCBody = some (.arr .cell .cell) := by native_decide
theorem shiNextCBody_typed : typeCheck [] shiNextCBody = some (.arr .cell .cell) := by native_decide
theorem shiPrevCBody_typed : typeCheck [] shiPrevCBody = some (.arr .cell .cell) := by native_decide
theorem flip1CBody_typed : typeCheck [] flip1CBody = some (.arr .cell .cell) := by native_decide
theorem flip2CBody_typed : typeCheck [] flip2CBody = some (.arr .cell .cell) := by native_decide
theorem flip3CBody_typed : typeCheck [] flip3CBody = some (.arr .cell .cell) := by native_decide
theorem flip4CBody_typed : typeCheck [] flip4CBody = some (.arr .cell .cell) := by native_decide
theorem flip5CBody_typed : typeCheck [] flip5CBody = some (.arr .cell .cell) := by native_decide
theorem flip6CBody_typed : typeCheck [] flip6CBody = some (.arr .cell .cell) := by native_decide

def cellEndoDef (name : String) (body : Tm)
    (validName : isValidName name = true)
    (bodyTypechecks : typeCheck [] body = some (.arr .cell .cell)) : WenDef where
  name := name
  body := body
  bodyType := .arr .cell .cell
  validName := validName
  bodyTypechecks := by simpa using bodyTypechecks

def cuoCDef : WenDef := cellEndoDef "cuoC" cuoCBody (by native_decide) cuoCBody_typed
def zongCDef : WenDef := cellEndoDef "zongC" zongCBody (by native_decide) zongCBody_typed
def huCDef : WenDef := cellEndoDef "huC" huCBody (by native_decide) huCBody_typed
def shiNextCDef : WenDef := cellEndoDef "shiNextC" shiNextCBody (by native_decide) shiNextCBody_typed
def shiPrevCDef : WenDef := cellEndoDef "shiPrevC" shiPrevCBody (by native_decide) shiPrevCBody_typed
def flip1CDef : WenDef := cellEndoDef "flip1C" flip1CBody (by native_decide) flip1CBody_typed
def flip2CDef : WenDef := cellEndoDef "flip2C" flip2CBody (by native_decide) flip2CBody_typed
def flip3CDef : WenDef := cellEndoDef "flip3C" flip3CBody (by native_decide) flip3CBody_typed
def flip4CDef : WenDef := cellEndoDef "flip4C" flip4CBody (by native_decide) flip4CBody_typed
def flip5CDef : WenDef := cellEndoDef "flip5C" flip5CBody (by native_decide) flip5CBody_typed
def flip6CDef : WenDef := cellEndoDef "flip6C" flip6CBody (by native_decide) flip6CBody_typed

/-! ### Stdlib 总表 -/

/-- 当前 stdlib 中已合度且类型化之 wenyan-ops 定义。 -/
def all : List WenDef :=
  [ tuiDef, biDef, buDef, biModalDef, tongDef, fanDef, sunDef, yiBenefitDef
  , cuoDef, zongDef, huDef, fanReverseDef
  , hexIdDef, cuoZongDef, flip1Def, flip2Def, flip3Def
  , impDef, neqHexDef, existsHDef, noneHDef
  , uniqueHDef, exactly3HDef, majorityHDef, endoCompDef, hexApplyDef
  , boolMarkerDef, repeatOnceDef, eachHDef
  , pairHDef, dupHDef, list1HDef, list2HDef, headHDef
  , eqCellDef, cuoCDef, zongCDef, huCDef, shiNextCDef, shiPrevCDef
  , flip1CDef, flip2CDef, flip3CDef, flip4CDef, flip5CDef, flip6CDef ]

theorem all_length : all.length = 46 := by native_decide

theorem all_names :
    all.map WenDef.name =
      [ "tui", "bi", "bu", "biModal", "tong", "fan", "sun", "yiBenefit"
      , "cuo", "zong", "hu", "fanReverse"
      , "hexId", "cuoZong", "flip1", "flip2", "flip3"
      , "imp", "neqHex", "existsH", "noneH"
      , "uniqueH", "exactly3H", "majorityH", "endoComp", "hexApply"
      , "boolMarker", "repeatOnce", "eachH"
      , "pairH", "dupH", "list1H", "list2H", "headH"
      , "eqCell", "cuoC", "zongC", "huC", "shiNextC", "shiPrevC"
      , "flip1C", "flip2C", "flip3C", "flip4C", "flip5C", "flip6C" ] := by
  native_decide

theorem all_distinct_names : (all.map WenDef.name).Nodup := by native_decide

end Stdlib

/-! ## § 8  组合范例：wenyan-ops 之 64-fold 合取

  展示「凡 (λh. 同 h h)」 — i.e. ∀h:H, h = h — 是一个 well-typed Tm.
  其类型为 Bool. 此例展示 forallH 之高阶用法.
-/

/-- 凡 (λh. 同 h h)：恒等之 universal 闭合，类型 Bool。 -/
def selfEqAll : Tm :=
  .app .forallH (.abs "h" .hex (.app (.app .eqHex (.var "h")) (.var "h")))

theorem selfEqAll_typed : typeCheck [] selfEqAll = some .bool := by native_decide

/-- 反例：«凡 不» 类型不通（不 之类型 Bool→Bool ≠ Hex→Bool）。 -/
example : typeCheck [] (.app .forallH .notB) = none := by native_decide

end SSBX.Foundation.Wen.WenDef
