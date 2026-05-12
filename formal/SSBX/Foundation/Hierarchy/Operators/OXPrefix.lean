/-
# Operators · OXPrefix -- variable-length `o/x` prefixes

`OX["..."]` is the full 8-coordinate Cell256 surface.  This module handles
front prefixes such as `x`, `ox`, and `oxo` without expanding V4 itself:

* prefix length 1 reads as R1/Yao;
* prefix length 2 may read as the canonical V4 kernel or as R2/SiXiang;
* prefix length 3 reads as R3/Trigram;
* prefix length 4 reads as R4/Mian through the existing R2 × R2 structure.

The layer is intentionally a surface-coordinate layer.  V4 remains exactly the
two-axis kernel.
-/

import SSBX.Foundation.Bagua.R8
import SSBX.Foundation.Bagua.BenZheng
import SSBX.Foundation.Hierarchy.Operators.V4

namespace SSBX.Foundation.Hierarchy.Operators

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.BenZheng
open SSBX.Foundation.Bagua.R8

/-- A front `o/x` prefix of length `n`, represented as Boolean coordinates.

`false` is `o`; `true` is `x`. -/
abbrev OXPrefix (n : Nat) : Type := Fin n → Bool

namespace OXPrefix

/-! ## Basic coordinate operations -/

def ofList (bits : List Bool) : OXPrefix bits.length :=
  fun i => bits.get i

def bit? (p : OXPrefix n) (i : Nat) : Bool :=
  if h : i < n then p ⟨i, h⟩ else false

def charToBit? : Char → Option Bool
  | 'o' => some false
  | 'x' => some true
  | _ => none

def bitsOfChars? : List Char → Option (List Bool)
  | [] => some []
  | c :: cs =>
      match charToBit? c, bitsOfChars? cs with
      | some b, some bs => some (b :: bs)
      | _, _ => none

/-- Runtime parser for variable-length `o/x` prefixes. -/
def ofString? (s : String) : Option (Sigma OXPrefix) :=
  match bitsOfChars? s.toList with
  | some bits => some ⟨bits.length, ofList bits⟩
  | none => none

def yaoOfBool : Bool → Yao
  | false => Yao.yang
  | true => Yao.yin

def boolOfYao : Yao → Bool
  | Yao.yang => false
  | Yao.yin => true

@[simp] theorem yaoOfBool_boolOfYao (y : Yao) :
    yaoOfBool (boolOfYao y) = y := by
  cases y <;> rfl

@[simp] theorem boolOfYao_yaoOfBool (b : Bool) :
    boolOfYao (yaoOfBool b) = b := by
  cases b <;> rfl

/-! ## R8 padding and prefix extraction -/

/-- Read a prefix as a full R8 cell by padding missing right-side coordinates
with `o`.  Prefixes longer than eight are projected to their first eight
coordinates. -/
def toR8Padded (p : OXPrefix n) : R8 :=
  (⟨yaoOfBool (bit? p 0), yaoOfBool (bit? p 1), yaoOfBool (bit? p 2),
    yaoOfBool (bit? p 3), yaoOfBool (bit? p 4), yaoOfBool (bit? p 5)⟩,
   Shi.ofYinGuo (bit? p 6, bit? p 7))

/-- Take the first `n` OX coordinates of an R8 cell.  For `n > 8`, coordinates
past the R8 surface are filled with `o`. -/
def ofR8Prefix (n : Nat) (c : R8) : OXPrefix n :=
  fun i =>
    match i.val with
    | 0 => boolOfYao c.1.y1
    | 1 => boolOfYao c.1.y2
    | 2 => boolOfYao c.1.y3
    | 3 => boolOfYao c.1.y4
    | 4 => boolOfYao c.1.y5
    | 5 => boolOfYao c.1.y6
    | 6 => c.2.1
    | 7 => c.2.2
    | _ => false

/-! ## R-axis and V4 readings -/

def toR1 (p : OXPrefix 1) : Yao :=
  yaoOfBool (bit? p 0)

def ofR1 (y : Yao) : OXPrefix 1 :=
  ofList [boolOfYao y]

def toR2 (p : OXPrefix 2) : SiXiang :=
  ⟨yaoOfBool (bit? p 0), yaoOfBool (bit? p 1)⟩

def ofR2 (s : SiXiang) : OXPrefix 2 :=
  ofList [boolOfYao s.y1, boolOfYao s.y2]

/-- The length-2 prefix as the canonical two-axis V4 kernel. -/
def toV4 (p : OXPrefix 2) : V4 :=
  V4.ofBits (bit? p 0) (bit? p 1)

def ofV4 (g : V4) : OXPrefix 2 :=
  ofList [V4.contentBit g, V4.frameBit g]

def toR3 (p : OXPrefix 3) : Trigram :=
  ⟨yaoOfBool (bit? p 0), yaoOfBool (bit? p 1), yaoOfBool (bit? p 2)⟩

def ofR3 (t : Trigram) : OXPrefix 3 :=
  ofList [boolOfYao t.y1, boolOfYao t.y2, boolOfYao t.y3]

def r2ToBen : SiXiang → Ben
  | ⟨.yang, .yang⟩ => .thing
  | ⟨.yang, .yin⟩ => .motion
  | ⟨.yin, .yang⟩ => .interval
  | ⟨.yin, .yin⟩ => .event

def benToR2 : Ben → SiXiang
  | .thing => ⟨.yang, .yang⟩
  | .motion => ⟨.yang, .yin⟩
  | .interval => ⟨.yin, .yang⟩
  | .event => ⟨.yin, .yin⟩

def r2ToZheng : SiXiang → Zheng
  | ⟨.yang, .yang⟩ => .trace
  | ⟨.yang, .yin⟩ => .momentum
  | ⟨.yin, .yang⟩ => .pivot
  | ⟨.yin, .yin⟩ => .occasion

def zhengToR2 : Zheng → SiXiang
  | .trace => ⟨.yang, .yang⟩
  | .momentum => ⟨.yang, .yin⟩
  | .pivot => ⟨.yin, .yang⟩
  | .occasion => ⟨.yin, .yin⟩

/-- The length-4 prefix as R4/Mian, read as `(first two bits) × (next two bits)`.
-/
def toR4 (p : OXPrefix 4) : Mian :=
  (r2ToBen ⟨yaoOfBool (bit? p 0), yaoOfBool (bit? p 1)⟩,
   r2ToZheng ⟨yaoOfBool (bit? p 2), yaoOfBool (bit? p 3)⟩)

def ofR4 (m : Mian) : OXPrefix 4 :=
  let b := benToR2 m.1
  let z := zhengToR2 m.2
  ofList [boolOfYao b.y1, boolOfYao b.y2, boolOfYao z.y1, boolOfYao z.y2]

/-! ## Roundtrips -/

theorem toR1_ofR1 (y : Yao) : toR1 (ofR1 y) = y := by
  cases y <;> rfl

theorem toR2_ofR2 (s : SiXiang) : toR2 (ofR2 s) = s := by
  rcases s with ⟨y1, y2⟩
  cases y1 <;> cases y2 <;> rfl

theorem toV4_ofV4 (g : V4) : toV4 (ofV4 g) = g := by
  cases g <;> rfl

theorem toR3_ofR3 (t : Trigram) : toR3 (ofR3 t) = t := by
  rcases t with ⟨y1, y2, y3⟩
  cases y1 <;> cases y2 <;> cases y3 <;> rfl

theorem toR4_ofR4 (m : Mian) : toR4 (ofR4 m) = m := by
  rcases m with ⟨b, z⟩
  cases b <;> cases z <;> rfl

/-! ## Canonical small prefix examples -/

def prefixX : OXPrefix 1 := ofList [true]
def prefixOX : OXPrefix 2 := ofList [false, true]
def prefixOXO : OXPrefix 3 := ofList [false, true, false]
def prefixOXOO : OXPrefix 4 := ofList [false, true, false, false]

theorem prefixX_reads_R1 :
    toR1 prefixX = Yao.yin := rfl

theorem prefixOX_reads_V4 :
    toV4 prefixOX = V4.zong := rfl

theorem prefixOX_reads_R2 :
    toR2 prefixOX = SiXiang.lesserYin := rfl

theorem prefixOXO_reads_R3 :
    toR3 prefixOXO = Trigram.fire := rfl

theorem prefixOXOO_reads_R4 :
    toR4 prefixOXOO = (Ben.motion, Zheng.trace) := rfl

theorem ox_prefix_summary :
    toR1 prefixX = Yao.yin
    ∧ toV4 prefixOX = V4.zong
    ∧ toR2 prefixOX = SiXiang.lesserYin
    ∧ toR3 prefixOXO = Trigram.fire
    ∧ toR4 prefixOXOO = (Ben.motion, Zheng.trace)
    ∧ (∀ g : V4, toV4 (ofV4 g) = g)
    ∧ (∀ m : Mian, toR4 (ofR4 m) = m) :=
  ⟨prefixX_reads_R1, prefixOX_reads_V4, prefixOX_reads_R2,
   prefixOXO_reads_R3, prefixOXOO_reads_R4, toV4_ofV4, toR4_ofR4⟩

end OXPrefix

end SSBX.Foundation.Hierarchy.Operators
