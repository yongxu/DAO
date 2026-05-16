/-
# Wen.RKernel.WenR5 -- R5 as a Mode16-visible Word64 slice

R5 is already canonically defined as `Wuyao = Mian x Bool`.  This module does
not replace that carrier.  It gives the action-trace kernel's reading:

  R5 = V4 x V4 x Bool

inside `Word64 = V4 x V4 x V4`, where the third V4 coordinate is restricted
to the content bit and has `frameBit = false`.
-/

import SSBX.Foundation.Hierarchy.R5_Wuyao
import SSBX.Foundation.Wen.RKernel.WenAction

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators
open SSBX.Foundation.Bagua.BenZheng
open SSBX.Foundation.Hierarchy.R5_Wuyao

/-- R5 as seen from the V4² action-trace kernel:
two complete V4 coordinates plus one extension bit. -/
structure R5View where
  first : V4
  second : V4
  extension : Bool
  deriving DecidableEq, BEq, Repr

namespace R5View

def origin : R5View := ⟨.dao, .dao, false⟩

def all : List R5View :=
  V4.all.flatMap fun first =>
    V4.all.flatMap fun second =>
      [⟨first, second, false⟩, ⟨first, second, true⟩]

theorem all_length : all.length = 32 := by
  native_decide

/-! ## R5 as a Word64 slice -/

def extensionV4 (bit : Bool) : V4 :=
  V4.ofBits bit false

def toWord64 (r : R5View) : Word64 :=
  ⟨r.first, r.second, extensionV4 r.extension⟩

def ofWord64? (word : Word64) : Option R5View :=
  if word.third.frameBit = false then
    some ⟨word.first, word.second, word.third.contentBit⟩
  else
    none

@[simp] theorem ofWord64_toWord64 (r : R5View) :
    ofWord64? (toWord64 r) = some r := by
  cases r
  simp [ofWord64?, toWord64, extensionV4, V4.frameBit_ofBits, V4.contentBit_ofBits]

theorem toWord64_origin :
    toWord64 origin = Word64.qian := rfl

theorem ofWord64_kun_none :
    ofWord64? Word64.kun = none := rfl

/-! ## Bridge to canonical R5_Wuyao -/

def benOfV4 (g : V4) : Ben :=
  V4.elim g .thing .interval .motion .event

def v4OfBen : Ben → V4
  | .thing => .dao
  | .motion => .zong
  | .interval => .cuo
  | .event => .cuoZong

def zhengOfV4 (g : V4) : Zheng :=
  V4.elim g .trace .pivot .momentum .occasion

def v4OfZheng : Zheng → V4
  | .trace => .dao
  | .momentum => .zong
  | .pivot => .cuo
  | .occasion => .cuoZong

@[simp] theorem v4OfBen_benOfV4 (g : V4) :
    v4OfBen (benOfV4 g) = g := by
  cases g <;> rfl

@[simp] theorem benOfV4_v4OfBen (b : Ben) :
    benOfV4 (v4OfBen b) = b := by
  cases b <;> rfl

@[simp] theorem v4OfZheng_zhengOfV4 (g : V4) :
    v4OfZheng (zhengOfV4 g) = g := by
  cases g <;> rfl

@[simp] theorem zhengOfV4_v4OfZheng (z : Zheng) :
    zhengOfV4 (v4OfZheng z) = z := by
  cases z <;> rfl

def toWuyao (r : R5View) : Wuyao :=
  ((benOfV4 r.first, zhengOfV4 r.second), r.extension)

def ofWuyao (w : Wuyao) : R5View :=
  ⟨v4OfBen w.1.1, v4OfZheng w.1.2, w.2⟩

@[simp] theorem ofWuyao_toWuyao (r : R5View) :
    ofWuyao (toWuyao r) = r := by
  cases r
  simp [ofWuyao, toWuyao]

@[simp] theorem toWuyao_ofWuyao (w : Wuyao) :
    toWuyao (ofWuyao w) = w := by
  rcases w with ⟨⟨ben, zheng⟩, extension⟩
  simp [ofWuyao, toWuyao]

def wuyaoEquiv : R5View ≃ Wuyao where
  toFun := toWuyao
  invFun := ofWuyao
  left_inv := ofWuyao_toWuyao
  right_inv := toWuyao_ofWuyao

/-! ## Mode16 action boundary -/

/-- A Mode16 preserves the R5 slice exactly when its word-action has no
frame-axis flip.  The temporal/control V4 coordinate remains above the slice
and does not affect this closure condition. -/
def modePreservesR5 (mode : Mode16) : Prop :=
  mode.word.frameBit = false

def act? (mode : Mode16) (r : R5View) : Option R5View :=
  ofWord64? (Mode16.actWord mode (toWord64 r))

theorem pureContentMode_preservesR5 :
    modePreservesR5 (Mode16.pureWord .cuo) := rfl

theorem pureFrameMode_not_preservesR5 :
    ¬ modePreservesR5 (Mode16.pureWord .zong) := by
  intro h
  contradiction

theorem act?_origin_content :
    act? (Mode16.pureWord .cuo) origin =
      some ⟨.cuo, .cuo, true⟩ := rfl

theorem act?_origin_frame_escapes :
    act? (Mode16.pureWord .zong) origin = none := rfl

theorem r5view_summary :
    all.length = 32
    ∧ (∀ r : R5View, ofWord64? (toWord64 r) = some r)
    ∧ (∀ r : R5View, ofWuyao (toWuyao r) = r)
    ∧ (∀ w : Wuyao, toWuyao (ofWuyao w) = w)
    ∧ modePreservesR5 (Mode16.pureWord .cuo)
    ∧ ¬ modePreservesR5 (Mode16.pureWord .zong)
    ∧ act? (Mode16.pureWord .cuo) origin = some ⟨.cuo, .cuo, true⟩
    ∧ act? (Mode16.pureWord .zong) origin = none :=
  ⟨all_length, ofWord64_toWord64, ofWuyao_toWuyao, toWuyao_ofWuyao,
   pureContentMode_preservesR5, pureFrameMode_not_preservesR5,
   act?_origin_content, act?_origin_frame_escapes⟩

end R5View

end SSBX.Foundation.Wen.RKernel
