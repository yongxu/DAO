/-
# Wen.V4Kernel.Word64Bridge -- R6/Lexicon bridge for 64 Wen words

The Lisp core stays V4-native.  This bridge connects `Word64 = V4^3` to the
existing R6 hexagram carrier and King Wen lexicon.
-/

import SSBX.Foundation.Lang.Lexicon
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Wen.V4Kernel.Word64

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators
open SSBX.Foundation.Yi.Yi

namespace Word64Bridge

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

def toHexagram (word : Word64) : Hexagram :=
  let p1 := yaoPairOfV4 word.first
  let p2 := yaoPairOfV4 word.second
  let p3 := yaoPairOfV4 word.third
  ⟨p1.1, p1.2, p2.1, p2.2, p3.1, p3.2⟩

def ofHexagram (h : Hexagram) : Word64 :=
  ⟨v4OfYaoPair h.y1 h.y2, v4OfYaoPair h.y3 h.y4, v4OfYaoPair h.y5 h.y6⟩

@[simp] theorem ofHexagram_toHexagram (word : Word64) :
    ofHexagram (toHexagram word) = word := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem toHexagram_ofHexagram (h : Hexagram) :
    toHexagram (ofHexagram h) = h := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;> rfl

/-- The exact carrier bridge: the V4-native 64-word space is the R6
hexagram space, read as three two-bit V4 coordinates. -/
def hexagramEquiv : Word64 ≃ Hexagram where
  toFun := toHexagram
  invFun := ofHexagram
  left_inv := ofHexagram_toHexagram
  right_inv := toHexagram_ofHexagram

theorem word64_is_r6_hexagram :
    (∀ word : Word64, hexagramEquiv.symm (hexagramEquiv word) = word)
    ∧ (∀ h : Hexagram, hexagramEquiv (hexagramEquiv.symm h) = h) :=
  ⟨ofHexagram_toHexagram, toHexagram_ofHexagram⟩

theorem word64_hexagram_checklist_summary :
    Word64.all.length = 64
    ∧ Word64.all.length = 4 ^ 3
    ∧ Nonempty (Word64 ≃ Hexagram)
    ∧ (∀ word : Word64, hexagramEquiv.symm (hexagramEquiv word) = word)
    ∧ (∀ h : Hexagram, hexagramEquiv (hexagramEquiv.symm h) = h)
    ∧ (∀ word : Word64, ofHexagram (toHexagram word) = word)
    ∧ (∀ h : Hexagram, toHexagram (ofHexagram h) = h) :=
  ⟨Word64.all_length,
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

def wordOfBits (bits : String) : Option Word64 :=
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

def matchesHexEntry (token : String) (entry : SSBX.Foundation.Lang.Lexicon.Entry) : Bool :=
  entry.chinese == token || entry.english == token || entry.aka.contains token || entry.bits == token

/-- Resolve a token through the R6 King Wen hexagram table only. -/
def wordOfToken (token : String) : Option Word64 :=
  match SSBX.Foundation.Lang.Lexicon.hexagram.find? (matchesHexEntry token) with
  | some entry => wordOfBits entry.bits
  | none => wordOfBits token

theorem qian_token :
    wordOfToken "乾" = some Word64.qian := by native_decide

theorem kun_token :
    wordOfToken "坤" = some Word64.kun := by native_decide

theorem complete_token :
    wordOfToken "既济" = some Word64.complete := by native_decide

theorem incomplete_token :
    wordOfToken "未济" = some Word64.incomplete := by native_decide

theorem english_qian_token :
    wordOfToken "heaven" = some Word64.qian := by native_decide

theorem bridge_summary :
    SSBX.Foundation.Lang.Lexicon.hexagram.length = 64
    ∧ wordOfToken "乾" = some Word64.qian
    ∧ wordOfToken "坤" = some Word64.kun
    ∧ wordOfToken "既济" = some Word64.complete
    ∧ wordOfToken "未济" = some Word64.incomplete
    ∧ (∀ word : Word64, hexagramEquiv.symm (hexagramEquiv word) = word)
    ∧ (∀ h : Hexagram, hexagramEquiv (hexagramEquiv.symm h) = h)
    ∧ (∀ word : Word64, ofHexagram (toHexagram word) = word)
    ∧ (∀ h : Hexagram, toHexagram (ofHexagram h) = h) :=
  ⟨SSBX.Foundation.Lang.Lexicon.hexagram_count, qian_token, kun_token,
    complete_token, incomplete_token, word64_is_r6_hexagram.1,
    word64_is_r6_hexagram.2, ofHexagram_toHexagram, toHexagram_ofHexagram⟩

end Word64Bridge

end SSBX.Foundation.Wen.V4Kernel
