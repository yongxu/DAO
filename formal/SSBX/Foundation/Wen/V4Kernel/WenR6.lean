/-
# Wen.V4Kernel.WenR6 -- R6 as the full Word64 lift

R5 is a 32-cell slice of `Word64 = V4 x V4 x V4`.  R6 is the full
64-word carrier.  This module makes the lift explicit and defines the
canonical R6 dual operators on the V4-native carrier.

The R6 dual operators here are the hexagram-level operators:

* content dual: yao-wise complement (`错`);
* frame dual: order reversal (`综`);
* compound dual: content dual after frame dual (`错综`).

They are not the same thing as the coordinate-only `Mode16.actWord` action.
The bridge theorem below states that these operators are exactly the existing
`V4.actHex` action after translating `Word64` to the canonical R6 hexagram.
-/

import SSBX.Foundation.Wen.V4Kernel.WenR5
import SSBX.Foundation.Wen.Layered.Bridges.Word64

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators
open SSBX.Foundation.Yi.Yi

/-- R6 as seen from the V4-native Wen kernel: all 64 words. -/
abbrev R6View : Type := Word64

namespace R6View

def origin : R6View := Word64.qian

def all : List R6View := Word64.all

theorem all_length : all.length = 64 := Word64.all_length

/-! ## Lift from R5 -/

def ofR5 (r : R5View) : R6View :=
  R5View.toWord64 r

def toR5? (word : R6View) : Option R5View :=
  R5View.ofWord64? word

@[simp] theorem toR5_ofR5 (r : R5View) :
    toR5? (ofR5 r) = some r :=
  R5View.ofWord64_toWord64 r

/-! ## R6 dual operators -/

/-- Swap the two bits inside one V4 coordinate.  This is the local bit-pair
operation needed by full hexagram reversal. -/
def swapPair (g : V4) : V4 :=
  V4.ofBits g.frameBit g.contentBit

@[simp] theorem swapPair_swapPair (g : V4) :
    swapPair (swapPair g) = g := by
  cases g <;> rfl

@[simp] theorem swapPair_dao :
    swapPair .dao = .dao := rfl

@[simp] theorem swapPair_cuo :
    swapPair .cuo = .zong := rfl

@[simp] theorem swapPair_zong :
    swapPair .zong = .cuo := rfl

@[simp] theorem swapPair_cuoZong :
    swapPair .cuoZong = .cuoZong := rfl

/-- R6 content dual (`错`): complement all six yao.

Because each `Word64` coordinate stores two yao bits, full yao-wise complement
is coordinate-wise composition by `.cuoZong`, not by `.cuo`. -/
def contentDual (word : R6View) : R6View :=
  ⟨V4.compose .cuoZong word.first,
    V4.compose .cuoZong word.second,
    V4.compose .cuoZong word.third⟩

/-- R6 frame dual (`综`): reverse all six yao. -/
def frameDual (word : R6View) : R6View :=
  ⟨swapPair word.third, swapPair word.second, swapPair word.first⟩

/-- R6 compound dual (`错综`): content dual after frame dual. -/
def compoundDual (word : R6View) : R6View :=
  contentDual (frameDual word)

/-- The canonical V4 dual action on R6. -/
def dual : V4 → R6View → R6View
  | .dao, word => word
  | .cuo, word => contentDual word
  | .zong, word => frameDual word
  | .cuoZong, word => compoundDual word

@[simp] theorem dual_dao (word : R6View) :
    dual .dao word = word := rfl

@[simp] theorem dual_cuo (word : R6View) :
    dual .cuo word = contentDual word := rfl

@[simp] theorem dual_zong (word : R6View) :
    dual .zong word = frameDual word := rfl

@[simp] theorem dual_cuoZong (word : R6View) :
    dual .cuoZong word = compoundDual word := rfl

@[simp] theorem contentDual_self_inverse (word : R6View) :
    contentDual (contentDual word) = word := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem frameDual_self_inverse (word : R6View) :
    frameDual (frameDual word) = word := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

theorem content_frame_comm (word : R6View) :
    contentDual (frameDual word) = frameDual (contentDual word) := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem compoundDual_self_inverse (word : R6View) :
    compoundDual (compoundDual word) = word := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

theorem dual_compose (a b : V4) (word : R6View) :
    dual (V4.compose a b) word = dual a (dual b word) := by
  cases a <;> cases b <;>
    cases word with
    | mk x y z =>
        cases x <;> cases y <;> cases z <;> rfl

@[simp] theorem dual_self_inverse (g : V4) (word : R6View) :
    dual g (dual g word) = word := by
  rw [← dual_compose, V4.compose_self, dual_dao]

/-! ## Bridge to canonical R6 Hexagram operators -/

def toHexagram : R6View → Hexagram :=
  SSBX.Foundation.Wen.Layered.Bridges.Word64.toHexagram

def ofHexagram : Hexagram → R6View :=
  SSBX.Foundation.Wen.Layered.Bridges.Word64.ofHexagram

@[simp] theorem ofHexagram_toHexagram (word : R6View) :
    ofHexagram (toHexagram word) = word :=
  SSBX.Foundation.Wen.Layered.Bridges.Word64.ofHexagram_toHexagram word

@[simp] theorem toHexagram_ofHexagram (h : Hexagram) :
    toHexagram (ofHexagram h) = h :=
  SSBX.Foundation.Wen.Layered.Bridges.Word64.toHexagram_ofHexagram h

def hexagramEquiv : R6View ≃ Hexagram :=
  SSBX.Foundation.Wen.Layered.Bridges.Word64.hexagramEquiv

theorem toHexagram_contentDual (word : R6View) :
    toHexagram (contentDual word) = Hexagram.complement (toHexagram word) := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

theorem toHexagram_frameDual (word : R6View) :
    toHexagram (frameDual word) = Hexagram.reverse (toHexagram word) := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

theorem toHexagram_compoundDual (word : R6View) :
    toHexagram (compoundDual word) = Hexagram.complementReverse (toHexagram word) := by
  cases word with
  | mk a b c =>
      cases a <;> cases b <;> cases c <;> rfl

theorem toHexagram_dual (g : V4) (word : R6View) :
    toHexagram (dual g word) = V4.actHex g (toHexagram word) := by
  cases g <;>
    cases word with
    | mk a b c =>
        cases a <;> cases b <;> cases c <;> rfl

/-! ## R5 boundary examples -/

theorem contentDual_origin_is_kun :
    contentDual origin = Word64.kun := rfl

theorem contentDual_lifts_R5_origin_out_of_R5 :
    toR5? (contentDual (ofR5 R5View.origin)) = none := rfl

def frameEscapeWitness : R5View :=
  ⟨.cuo, .dao, false⟩

theorem frameDual_escapeWitness_out_of_R5 :
    toR5? (frameDual (ofR5 frameEscapeWitness)) = none := rfl

theorem r6view_summary :
    all.length = 64
    ∧ (∀ r : R5View, toR5? (ofR5 r) = some r)
    ∧ (∀ word : R6View, dual .dao word = word)
    ∧ (∀ word : R6View, contentDual (contentDual word) = word)
    ∧ (∀ word : R6View, frameDual (frameDual word) = word)
    ∧ (∀ word : R6View, compoundDual (compoundDual word) = word)
    ∧ (∀ g word, dual g (dual g word) = word)
    ∧ (∀ a b word, dual (V4.compose a b) word = dual a (dual b word))
    ∧ (∀ g word, toHexagram (dual g word) = V4.actHex g (toHexagram word))
    ∧ contentDual origin = Word64.kun
    ∧ toR5? (contentDual (ofR5 R5View.origin)) = none
    ∧ toR5? (frameDual (ofR5 frameEscapeWitness)) = none :=
  ⟨all_length, toR5_ofR5, dual_dao, contentDual_self_inverse,
   frameDual_self_inverse, compoundDual_self_inverse, dual_self_inverse,
   dual_compose, toHexagram_dual, contentDual_origin_is_kun,
   contentDual_lifts_R5_origin_out_of_R5, frameDual_escapeWitness_out_of_R5⟩

end R6View

end SSBX.Foundation.Wen.V4Kernel
