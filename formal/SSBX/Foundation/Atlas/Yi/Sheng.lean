/-
# Foundation.Atlas.Yi.Sheng — 生生 / SiXiang / single-yao flip algebra on R 3

Port of `Atlas/Yi/Classical/Algebra/BaguaAlgebra.lean` onto the
R-Family Trigram type (= `R 3 = Fin 3 → Bool`).

This file contributes the **(Z/2)³ flip algebra** on `Trigram = R 3`:

* `motion`     (动): flip `y1` (bottom yao).
* `middleFlip` (化): flip `y2` (center yao).
* `topFlip`   (变): flip `y3` (top yao).
* `bottomFlip`     : alias for `motion` (flip y1).

Together with the identity, these three involutive, pairwise-commuting
flips generate the abelian group `(Z/2)³` acting simply transitively
on the 8 trigrams.

The file also exposes:

* `SiXiang := Shi` (= `R 2 = 4 elements`), with the four classical names
  `taiyang`, `shaoyin`, `shaoyang`, `taiyin`.
* `hammingDist` on trigrams (number of differing yao positions).
* `transform` taking a → b independently per yao position.

## Doctrinal anchor

* `wen-algebra.md` v0.6 §1.4 (R 3 algebra).
* `v4-foundation.md` v0.5 §15.3 (Bagua binding).
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Bagua

namespace SSBX.Foundation.Atlas.Yi.Sheng

open SSBX.Foundation.R
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 SiXiang (四象, T_2) -/

/-- 四象 (Sì Xiàng): the 4 elemental images = `R 2 = Shi`.  The four
    classical names live here; in the temporal-modality Atlas the same type is named
    `{道, 已, 今, 未}` (see `Atlas/Yi/Shi.lean`). -/
abbrev SiXiang : Type := Shi

namespace SiXiang

/-- 太阳 (Tài Yáng, ⚌) — `(yang, yang)`. -/
@[match_pattern] def taiyang : SiXiang := fun _ => Yao.yang

/-- 少阴 (Shào Yīn, ⚍) — `(yang, yin)`. -/
@[match_pattern] def shaoyin : SiXiang := fun i =>
  match i with
  | ⟨0, _⟩ => Yao.yang
  | ⟨1, _⟩ => Yao.yin

/-- 少阳 (Shào Yáng, ⚎) — `(yin, yang)`. -/
@[match_pattern] def shaoyang : SiXiang := fun i =>
  match i with
  | ⟨0, _⟩ => Yao.yin
  | ⟨1, _⟩ => Yao.yang

/-- 太阴 (Tài Yīn, ⚏) — `(yin, yin)`. -/
@[match_pattern] def taiyin : SiXiang := fun _ => Yao.yin

/-- The 4 si-xiang in canonical order. -/
def all : List SiXiang := [taiyang, shaoyin, shaoyang, taiyin]

theorem all_length : all.length = 4 := rfl

end SiXiang

/-! ## § 2 Three single-yao flips on Trigram -/

/-- 动 (motion): flip the 1st (bottom) yao `y1`. -/
def motion (t : Trigram) : Trigram :=
  Trigram.mk (Yao.neg t.y1) t.y2 t.y3

/-- 化 (middleFlip): flip the 2nd (center) yao `y2`. -/
def middleFlip (t : Trigram) : Trigram :=
  Trigram.mk t.y1 (Yao.neg t.y2) t.y3

/-- 变 (topFlip): flip the 3rd (top) yao `y3`. -/
def topFlip (t : Trigram) : Trigram :=
  Trigram.mk t.y1 t.y2 (Yao.neg t.y3)

/-- Alias: `bottomFlip = motion` (flip y1). -/
abbrev bottomFlip : Trigram → Trigram := motion

/-! ### Computed accessor lemmas -/

@[simp] theorem motion_y1 (t : Trigram) : (motion t).y1 = Yao.neg t.y1 := rfl
@[simp] theorem motion_y2 (t : Trigram) : (motion t).y2 = t.y2 := rfl
@[simp] theorem motion_y3 (t : Trigram) : (motion t).y3 = t.y3 := rfl

@[simp] theorem middleFlip_y1 (t : Trigram) : (middleFlip t).y1 = t.y1 := rfl
@[simp] theorem middleFlip_y2 (t : Trigram) : (middleFlip t).y2 = Yao.neg t.y2 := rfl
@[simp] theorem middleFlip_y3 (t : Trigram) : (middleFlip t).y3 = t.y3 := rfl

@[simp] theorem topFlip_y1 (t : Trigram) : (topFlip t).y1 = t.y1 := rfl
@[simp] theorem topFlip_y2 (t : Trigram) : (topFlip t).y2 = t.y2 := rfl
@[simp] theorem topFlip_y3 (t : Trigram) : (topFlip t).y3 = Yao.neg t.y3 := rfl

/-! ## § 3 Involutivity (each flip has order 2) -/

theorem motion_motion (t : Trigram) : motion (motion t) = t := by
  apply Trigram.ext
  · simp [Yao.neg_neg]
  · rfl
  · rfl

theorem middleFlip_middleFlip (t : Trigram) : middleFlip (middleFlip t) = t := by
  apply Trigram.ext
  · rfl
  · simp [Yao.neg_neg]
  · rfl

theorem topFlip_topFlip (t : Trigram) : topFlip (topFlip t) = t := by
  apply Trigram.ext
  · rfl
  · rfl
  · simp [Yao.neg_neg]

/-! ## § 4 Pairwise commutativity ((Z/2)³ is abelian) -/

theorem motion_middleFlip_comm (t : Trigram) :
    middleFlip (motion t) = motion (middleFlip t) := by
  apply Trigram.ext <;> rfl

theorem middleFlip_topFlip_comm (t : Trigram) :
    topFlip (middleFlip t) = middleFlip (topFlip t) := by
  apply Trigram.ext <;> rfl

theorem motion_topFlip_comm (t : Trigram) :
    topFlip (motion t) = motion (topFlip t) := by
  apply Trigram.ext <;> rfl

/-! ## § 5 Concrete orbit of 乾 under (Z/2)³ -/

theorem motion_qian : motion Trigram.qian = Trigram.xun := by
  apply Trigram.ext <;>
    simp [motion, Trigram.qian, Trigram.xun, Trigram.mk, Yao.neg, Yao.yang, Yao.yin,
      Trigram.y1, Trigram.y2, Trigram.y3]

theorem middleFlip_qian : middleFlip Trigram.qian = Trigram.li := by
  apply Trigram.ext <;>
    simp [middleFlip, Trigram.qian, Trigram.li, Trigram.mk, Yao.neg, Yao.yang, Yao.yin,
      Trigram.y1, Trigram.y2, Trigram.y3]

theorem topFlip_qian : topFlip Trigram.qian = Trigram.dui := by
  apply Trigram.ext <;>
    simp [topFlip, Trigram.qian, Trigram.dui, Trigram.mk, Yao.neg, Yao.yang, Yao.yin,
      Trigram.y1, Trigram.y2, Trigram.y3]

theorem motion_middleFlip_qian :
    motion (middleFlip Trigram.qian) = Trigram.gen := by
  apply Trigram.ext <;>
    simp [motion, middleFlip, Trigram.qian, Trigram.gen, Trigram.mk, Yao.neg,
      Yao.yang, Yao.yin, Trigram.y1, Trigram.y2, Trigram.y3]

theorem middleFlip_topFlip_qian :
    middleFlip (topFlip Trigram.qian) = Trigram.zhen := by
  apply Trigram.ext <;>
    simp [middleFlip, topFlip, Trigram.qian, Trigram.zhen, Trigram.mk, Yao.neg,
      Yao.yang, Yao.yin, Trigram.y1, Trigram.y2, Trigram.y3]

theorem motion_topFlip_qian :
    motion (topFlip Trigram.qian) = Trigram.kan := by
  apply Trigram.ext <;>
    simp [motion, topFlip, Trigram.qian, Trigram.kan, Trigram.mk, Yao.neg,
      Yao.yang, Yao.yin, Trigram.y1, Trigram.y2, Trigram.y3]

theorem motion_middleFlip_topFlip_qian :
    motion (middleFlip (topFlip Trigram.qian)) = Trigram.kun := by
  apply Trigram.ext <;>
    simp [motion, middleFlip, topFlip, Trigram.qian, Trigram.kun, Trigram.mk,
      Yao.neg, Yao.yang, Yao.yin, Trigram.y1, Trigram.y2, Trigram.y3]

/-! ## § 6 Hamming distance -/

/-- Hamming distance on trigrams: number of yao positions where `a` and `b` differ. -/
def hammingDist (a b : Trigram) : Nat :=
  (if a.y1 = b.y1 then 0 else 1) +
  (if a.y2 = b.y2 then 0 else 1) +
  (if a.y3 = b.y3 then 0 else 1)

theorem hammingDist_le_3 (a b : Trigram) : hammingDist a b ≤ 3 := by
  unfold hammingDist
  split <;> split <;> split <;> omega

theorem hammingDist_self (t : Trigram) : hammingDist t t = 0 := by
  unfold hammingDist
  simp

/-! ## § 7 Independent per-yao transform -/

/-- `transform a b t`: apply per-yao flips chosen by the
    `a-vs-b` difference pattern.  Concretely, position-`i` of `t` is
    flipped iff `a.yi ≠ b.yi`. -/
def transform (a b t : Trigram) : Trigram :=
  Trigram.mk
    (if a.y1 = b.y1 then t.y1 else Yao.neg t.y1)
    (if a.y2 = b.y2 then t.y2 else Yao.neg t.y2)
    (if a.y3 = b.y3 then t.y3 else Yao.neg t.y3)

/-- `transform a b` takes `a` to `b` (the canonical Hamming witness). -/
theorem transform_correct (a b : Trigram) : transform a b a = b := by
  apply Trigram.ext
  · simp [transform]
    by_cases h : a.y1 = b.y1
    · simp [h]
    · simp [h]
      cases hya : a.y1 <;> cases hyb : b.y1 <;>
        first | rfl | (exfalso; apply h; rw [hya, hyb])
  · simp [transform]
    by_cases h : a.y2 = b.y2
    · simp [h]
    · simp [h]
      cases hya : a.y2 <;> cases hyb : b.y2 <;>
        first | rfl | (exfalso; apply h; rw [hya, hyb])
  · simp [transform]
    by_cases h : a.y3 = b.y3
    · simp [h]
    · simp [h]
      cases hya : a.y3 <;> cases hyb : b.y3 <;>
        first | rfl | (exfalso; apply h; rw [hya, hyb])

/-- 八卦 互通: any two trigrams are connected by some transformation. -/
theorem bagua_intercommunication (a b : Trigram) :
    ∃ f : Trigram → Trigram, f a = b :=
  ⟨transform a b, transform_correct a b⟩

/-- Bounded: at most Hamming-many single-flip steps connect any two trigrams. -/
theorem bagua_intercommunication_bounded (a b : Trigram) :
    ∃ f : Trigram → Trigram, f a = b ∧ hammingDist a b ≤ 3 :=
  ⟨transform a b, transform_correct a b, hammingDist_le_3 a b⟩

/-! ## § 8 Hamming distance characterizes equality -/

/-- `hammingDist a b = 0 ↔ a = b`. -/
theorem hammingDist_eq_zero_iff (a b : Trigram) :
    hammingDist a b = 0 ↔ a = b := by
  constructor
  · intro hd
    unfold hammingDist at hd
    apply Trigram.ext
    · by_contra hne
      have h1 : (if a.y1 = b.y1 then (0 : Nat) else 1) = 1 := by simp [hne]
      rw [h1] at hd
      omega
    · by_contra hne
      have h2 : (if a.y2 = b.y2 then (0 : Nat) else 1) = 1 := by simp [hne]
      rw [h2] at hd
      omega
    · by_contra hne
      have h3 : (if a.y3 = b.y3 then (0 : Nat) else 1) = 1 := by simp [hne]
      rw [h3] at hd
      omega
  · rintro rfl
    exact hammingDist_self a

end SSBX.Foundation.Atlas.Yi.Sheng
