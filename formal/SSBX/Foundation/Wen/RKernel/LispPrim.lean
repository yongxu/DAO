/-
# Wen.RKernel.LispPrim -- structural primitive table

Primitive names are fixed Lean constructors.  There are no surface strings and
no R-space imports in this table.
-/

import SSBX.Foundation.Wen.RKernel.LispSyntax

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

namespace Prim

def arity : Prim → Nat
  | .v4Compose => 2
  | .v4Eq => 2
  | .wordCompose => 2
  | .wordEq => 2
  | .numEq => 2
  | .succ => 1
  | .pred => 1
  | .add => 2
  | .cons => 2
  | .car => 1
  | .cdr => 1
  | .null => 1
  | .atom => 1
  | .isSymbol => 1
  | .isNumber => 1
  | .eval => 1
  | .r5Is => 1
  | .r5ToR4 => 1
  | .r5Compose => 2
  | .r5Coords => 1

end Prim

def truthValue : Bool → Value
  | true => .atom .dao
  | false => .nil

def valueAtom? : Value → Bool
  | .atom _ => true
  | .symbol _ => true
  | .num _ => true
  | .nil => true
  | .prim _ => true
  | _ => false

def isR5Symbol (word : Word64) : Bool :=
  word.third.frameBit = false

def r4ValueOfWord (word : Word64) : Value :=
  Value.list [.atom word.first, .atom word.second]

def r5CoordsValue (word : Word64) : Value :=
  Value.list [.atom word.first, .atom word.second, .atom word.third]

/-- Apply a primitive to an exact argument list. -/
def applyPrim : Prim → List Value → Option Value
  | .v4Compose, [.atom a, .atom b] => some (.atom (V4.compose a b))
  | .v4Compose, _ => none
  | .v4Eq, [.atom a, .atom b] => some (truthValue (a = b))
  | .v4Eq, _ => none
  | .wordCompose, [.symbol a, .symbol b] => some (.symbol (Word64.compose a b))
  | .wordCompose, _ => none
  | .wordEq, [.symbol a, .symbol b] => some (truthValue (a = b))
  | .wordEq, _ => none
  | .numEq, [.num a, .num b] => some (truthValue (a = b))
  | .numEq, _ => none
  | .succ, [.num n] => some (.num (n + 1))
  | .succ, _ => none
  | .pred, [.num 0] => some (.num 0)
  | .pred, [.num (n + 1)] => some (.num n)
  | .pred, _ => none
  | .add, [.num a, .num b] => some (.num (a + b))
  | .add, _ => none
  | .cons, [head, tail] => some (.cons head tail)
  | .cons, _ => none
  | .car, [.cons head _] => some head
  | .car, _ => none
  | .cdr, [.cons _ tail] => some tail
  | .cdr, _ => none
  | .null, [v] => some (truthValue (v.isNil = true))
  | .null, _ => none
  | .atom, [v] => some (truthValue (valueAtom? v = true))
  | .atom, _ => none
  | .isSymbol, [.symbol _] => some (.atom .dao)
  | .isSymbol, [_] => some .nil
  | .isSymbol, _ => none
  | .isNumber, [.num _] => some (.atom .dao)
  | .isNumber, [_] => some .nil
  | .isNumber, _ => none
  | .eval, _ => none
  | .r5Is, [.symbol word] => some (truthValue (isR5Symbol word))
  | .r5Is, [_] => some .nil
  | .r5Is, _ => none
  | .r5ToR4, [.symbol word] =>
      if isR5Symbol word then some (r4ValueOfWord word) else none
  | .r5ToR4, _ => none
  | .r5Compose, [.symbol a, .symbol b] =>
      if isR5Symbol a && isR5Symbol b then
        let c := Word64.compose a b
        if isR5Symbol c then some (.symbol c) else none
      else
        none
  | .r5Compose, _ => none
  | .r5Coords, [.symbol word] =>
      if isR5Symbol word then some (r5CoordsValue word) else none
  | .r5Coords, _ => none

@[simp] theorem applyPrim_v4Compose_atoms (a b : V4) :
    applyPrim .v4Compose [.atom a, .atom b] = some (.atom (V4.compose a b)) :=
  rfl

@[simp] theorem applyPrim_cons (head tail : Value) :
    applyPrim .cons [head, tail] = some (.cons head tail) := rfl

@[simp] theorem applyPrim_wordCompose_symbols (a b : Word64) :
    applyPrim .wordCompose [.symbol a, .symbol b] =
      some (.symbol (Word64.compose a b)) :=
  rfl

@[simp] theorem applyPrim_add_nums (a b : Nat) :
    applyPrim .add [.num a, .num b] = some (.num (a + b)) :=
  rfl

@[simp] theorem applyPrim_pred_zero :
    applyPrim .pred [.num 0] = some (.num 0) := rfl

@[simp] theorem applyPrim_car_cons (head tail : Value) :
    applyPrim .car [.cons head tail] = some head := rfl

@[simp] theorem applyPrim_cdr_cons (head tail : Value) :
    applyPrim .cdr [.cons head tail] = some tail := rfl

@[simp] theorem applyPrim_null_nil :
    applyPrim .null [.nil] = some (.atom .dao) := rfl

@[simp] theorem applyPrim_atom_v4 (g : V4) :
    applyPrim .atom [.atom g] = some (.atom .dao) := rfl

@[simp] theorem applyPrim_r5Is_qian :
    applyPrim .r5Is [.symbol .qian] = some (.atom .dao) := rfl

@[simp] theorem applyPrim_r5Is_kun :
    applyPrim .r5Is [.symbol .kun] = some .nil := rfl

theorem applyPrim_wrong_v4Compose_arity :
    applyPrim .v4Compose [.atom .dao] = none := rfl

theorem lisp_prim_summary :
    Prim.arity .v4Compose = 2
    ∧ applyPrim .v4Compose [.atom .cuo, .atom .zong] = some (.atom .cuoZong)
    ∧ applyPrim .wordCompose [.symbol .qian, .symbol .kun] = some (.symbol .kun)
    ∧ applyPrim .add [.num 2, .num 3] = some (.num 5)
    ∧ applyPrim .pred [.num 0] = some (.num 0)
    ∧ applyPrim .cons [.atom .cuo, .nil] = some (.cons (.atom .cuo) .nil)
    ∧ applyPrim .car [.cons (.atom .cuo) .nil] = some (.atom .cuo)
    ∧ applyPrim .v4Compose [.atom .dao] = none
    ∧ applyPrim .r5Is [.symbol .qian] = some (.atom .dao)
    ∧ applyPrim .r5Is [.symbol .kun] = some .nil :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SSBX.Foundation.Wen.RKernel
