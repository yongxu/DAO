/-
# Wen.Layered.Bridges.Word64 -- Word64 as a six-bit space

`Word64 = V4 x V4 x V4`; each V4 coordinate contributes its two
content/frame bits.
-/

import SSBX.Foundation.Wen.Layered.Bridges.V4
import SSBX.Foundation.Lang.Lexicon
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Wen.V4Kernel.Word64

namespace SSBX.Foundation.Wen.Layered.Bridges

namespace Word64

open SSBX.Foundation.Hierarchy.Operators
open SSBX.Foundation.Yi.Yi

abbrev Carrier : Type := SSBX.Foundation.Wen.V4Kernel.Word64

def yaoOfBit : Bool → Yao
  | false => .yang
  | true => .yin

def bitOfYao : Yao → Bool
  | .yang => false
  | .yin => true

def v4OfYaoPair (first second : Yao) : V4 :=
  V4.ofBits (bitOfYao first) (bitOfYao second)

def yaoPairOfV4 (g : V4) : Yao × Yao :=
  (yaoOfBit g.contentBit, yaoOfBit g.frameBit)

def toHexagram (word : Carrier) : Hexagram :=
  let p1 := yaoPairOfV4 word.first
  let p2 := yaoPairOfV4 word.second
  let p3 := yaoPairOfV4 word.third
  ⟨p1.1, p1.2, p2.1, p2.2, p3.1, p3.2⟩

def ofHexagram (h : Hexagram) : Carrier :=
  ⟨v4OfYaoPair h.y1 h.y2, v4OfYaoPair h.y3 h.y4,
    v4OfYaoPair h.y5 h.y6⟩

@[simp] theorem ofHexagram_toHexagram (word : Carrier) :
    ofHexagram (toHexagram word) = word := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem toHexagram_ofHexagram (h : Hexagram) :
    toHexagram (ofHexagram h) = h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;>
    cases y6 <;> rfl

/-- The exact carrier bridge: the V4-native 64-word space is the R6
hexagram space, read as three two-bit V4 coordinates. -/
def hexagramEquiv : Carrier ≃ Hexagram where
  toFun := toHexagram
  invFun := ofHexagram
  left_inv := ofHexagram_toHexagram
  right_inv := toHexagram_ofHexagram

theorem word64_is_r6_hexagram :
    (∀ word : Carrier, hexagramEquiv.symm (hexagramEquiv word) = word)
    ∧ (∀ h : Hexagram, hexagramEquiv (hexagramEquiv.symm h) = h) :=
  ⟨ofHexagram_toHexagram, toHexagram_ofHexagram⟩

theorem word64_hexagram_checklist_summary :
    SSBX.Foundation.Wen.V4Kernel.Word64.all.length = 64
    ∧ SSBX.Foundation.Wen.V4Kernel.Word64.all.length = 4 ^ 3
    ∧ Nonempty (Carrier ≃ Hexagram)
    ∧ (∀ word : Carrier, hexagramEquiv.symm (hexagramEquiv word) = word)
    ∧ (∀ h : Hexagram, hexagramEquiv (hexagramEquiv.symm h) = h)
    ∧ (∀ word : Carrier, ofHexagram (toHexagram word) = word)
    ∧ (∀ h : Hexagram, toHexagram (ofHexagram h) = h) :=
  ⟨SSBX.Foundation.Wen.V4Kernel.Word64.all_length,
   by native_decide,
   ⟨hexagramEquiv⟩,
   word64_is_r6_hexagram.1,
   word64_is_r6_hexagram.2,
   ofHexagram_toHexagram,
   toHexagram_ofHexagram⟩

def bitOfChar : Char → Option Bool
  | 'o' => some false
  | 'x' => some true
  | _ => none

def wordOfBits (bits : String) : Option Carrier :=
  match bits.toList with
  | [a, b, c, d, e, f] => do
      let y1 ← bitOfChar a
      let y2 ← bitOfChar b
      let y3 ← bitOfChar c
      let y4 ← bitOfChar d
      let y5 ← bitOfChar e
      let y6 ← bitOfChar f
      some
        ⟨V4.ofBits y1 y2, V4.ofBits y3 y4, V4.ofBits y5 y6⟩
  | _ => none

def matchesHexEntry (token : String)
    (entry : SSBX.Foundation.Lang.Lexicon.Entry) : Bool :=
  entry.chinese == token || entry.english == token || entry.aka.contains token ||
    entry.bits == token

/-- Resolve a token through the R6 King Wen hexagram table only. -/
def wordOfToken (token : String) : Option Carrier :=
  match SSBX.Foundation.Lang.Lexicon.hexagram.find? (matchesHexEntry token) with
  | some entry => wordOfBits entry.bits
  | none => wordOfBits token

theorem qian_token :
    wordOfToken "乾" = some SSBX.Foundation.Wen.V4Kernel.Word64.qian := by
  native_decide

theorem kun_token :
    wordOfToken "坤" = some SSBX.Foundation.Wen.V4Kernel.Word64.kun := by
  native_decide

theorem complete_token :
    wordOfToken "既济" = some SSBX.Foundation.Wen.V4Kernel.Word64.complete := by
  native_decide

theorem incomplete_token :
    wordOfToken "未济" = some SSBX.Foundation.Wen.V4Kernel.Word64.incomplete := by
  native_decide

theorem english_qian_token :
    wordOfToken "heaven" = some SSBX.Foundation.Wen.V4Kernel.Word64.qian := by
  native_decide

theorem bridge_summary :
    SSBX.Foundation.Lang.Lexicon.hexagram.length = 64
    ∧ wordOfToken "乾" = some SSBX.Foundation.Wen.V4Kernel.Word64.qian
    ∧ wordOfToken "坤" = some SSBX.Foundation.Wen.V4Kernel.Word64.kun
    ∧ wordOfToken "既济" = some SSBX.Foundation.Wen.V4Kernel.Word64.complete
    ∧ wordOfToken "未济" = some SSBX.Foundation.Wen.V4Kernel.Word64.incomplete
    ∧ (∀ word : Carrier, hexagramEquiv.symm (hexagramEquiv word) = word)
    ∧ (∀ h : Hexagram, hexagramEquiv (hexagramEquiv.symm h) = h)
    ∧ (∀ word : Carrier, ofHexagram (toHexagram word) = word)
    ∧ (∀ h : Hexagram, toHexagram (ofHexagram h) = h) :=
  ⟨SSBX.Foundation.Lang.Lexicon.hexagram_count, qian_token, kun_token,
    complete_token, incomplete_token, word64_is_r6_hexagram.1,
    word64_is_r6_hexagram.2, ofHexagram_toHexagram, toHexagram_ofHexagram⟩

def toBitSpace (word : Carrier) : BitSpace 6 :=
  fun i =>
    match i.val with
    | 0 => SSBX.Foundation.Hierarchy.Operators.V4.contentBit word.first
    | 1 => SSBX.Foundation.Hierarchy.Operators.V4.frameBit word.first
    | 2 => SSBX.Foundation.Hierarchy.Operators.V4.contentBit word.second
    | 3 => SSBX.Foundation.Hierarchy.Operators.V4.frameBit word.second
    | 4 => SSBX.Foundation.Hierarchy.Operators.V4.contentBit word.third
    | 5 => SSBX.Foundation.Hierarchy.Operators.V4.frameBit word.third
    | _ => false

def fromBitSpace (v : BitSpace 6) : Carrier :=
  ⟨SSBX.Foundation.Hierarchy.Operators.V4.ofBits
      (v ⟨0, by decide⟩) (v ⟨1, by decide⟩),
    SSBX.Foundation.Hierarchy.Operators.V4.ofBits
      (v ⟨2, by decide⟩) (v ⟨3, by decide⟩),
    SSBX.Foundation.Hierarchy.Operators.V4.ofBits
      (v ⟨4, by decide⟩) (v ⟨5, by decide⟩)⟩

@[simp] theorem fromBitSpace_toBitSpace (word : Carrier) :
    fromBitSpace (toBitSpace word) = word := by
  cases word with
  | mk first second third =>
      cases first <;> cases second <;> cases third <;> rfl

@[simp] theorem toBitSpace_fromBitSpace (v : BitSpace 6) :
    toBitSpace (fromBitSpace v) = v := by
  funext i
  fin_cases i <;>
    simp [toBitSpace, fromBitSpace,
      SSBX.Foundation.Hierarchy.Operators.V4.contentBit_ofBits,
      SSBX.Foundation.Hierarchy.Operators.V4.frameBit_ofBits]

@[simp] theorem fromBitSpace_zero :
    fromBitSpace (BitSpace.zero : BitSpace 6) =
      SSBX.Foundation.Wen.V4Kernel.Word64.origin := rfl

@[simp] theorem toBitSpace_zero :
    toBitSpace SSBX.Foundation.Wen.V4Kernel.Word64.origin =
      (BitSpace.zero : BitSpace 6) := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem toBitSpace_xor (a b : Carrier) :
    toBitSpace (SSBX.Foundation.Wen.V4Kernel.Word64.compose a b) =
      BitSpace.xor (toBitSpace a) (toBitSpace b) := by
  funext i
  fin_cases i <;>
    simp [toBitSpace, BitSpace.xor,
      SSBX.Foundation.Wen.V4Kernel.Word64.compose,
      SSBX.Foundation.Hierarchy.Operators.V4.compose,
      SSBX.Foundation.Hierarchy.Operators.V4.contentBit_ofBits,
      SSBX.Foundation.Hierarchy.Operators.V4.frameBit_ofBits]

theorem word64_bridge_summary :
    fromBitSpace (BitSpace.zero : BitSpace 6) =
      SSBX.Foundation.Wen.V4Kernel.Word64.origin
    ∧ toBitSpace SSBX.Foundation.Wen.V4Kernel.Word64.origin =
      (BitSpace.zero : BitSpace 6)
    ∧ (∀ word : Carrier, fromBitSpace (toBitSpace word) = word)
    ∧ (∀ v : BitSpace 6, toBitSpace (fromBitSpace v) = v)
    ∧ (∀ a b : Carrier,
        toBitSpace (SSBX.Foundation.Wen.V4Kernel.Word64.compose a b) =
          BitSpace.xor (toBitSpace a) (toBitSpace b)) :=
  ⟨fromBitSpace_zero, toBitSpace_zero, fromBitSpace_toBitSpace,
   toBitSpace_fromBitSpace, toBitSpace_xor⟩

end Word64

end SSBX.Foundation.Wen.Layered.Bridges
