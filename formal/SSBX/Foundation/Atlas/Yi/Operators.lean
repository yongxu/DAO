/-
# Foundation.Atlas.Yi.Operators — V₄ operators on Hexagram (= R 6)

Per `wen-algebra` v0.6 §9.3 and `v4-foundation` v0.5 §15.6:

The three classical Yi-tradition operators on a hexagram:

* `cuo`     (錯, "complement"): negate every yao.
* `zong`    (綜, "reverse"):    reverse the yao order (y1 ↔ y6, etc.).
* `cuoZong` (錯綜):              `cuo ∘ zong` (= `zong ∘ cuo`, they commute).

Together `{id, cuo, zong, cuoZong}` form the Klein four-group V₄ acting
on `Hexagram = R 6`.

The 4th classical operator is `hu` (互, "mutual"), formed by
extracting yao 2-3-4 (inner trigram of 互) and 3-4-5 (outer trigram of
互).  It is NOT a V₄ element — its only fixed points are `qianqian`
(乾為天) and `kunkun` (坤為地), and it has the 2-cycle
`jiji ↔ weiji` (既濟 ↔ 未濟).

## Doctrinal anchor

* `wen-algebra.md` v0.6 §9.3 (Atlas operators).
* `v4-foundation.md` v0.5 §15.6 (Hexagram V₄ on R 6).
-/

import SSBX.Foundation.Atlas.Yi.Names
import SSBX.Foundation.Atlas.Yi.Hexagrams

namespace SSBX.Foundation.Atlas.Yi

open SSBX.Foundation.R
open Yao (yang yin)

namespace Hexagram

/-! ## § 1 cuo (錯) — coordinate-wise negation -/

/-- 錯 (cuò, "complement"): flip every yao.  Equivalent to XOR with
    the all-ones vector of `R 6`. -/
def cuo (h : Hexagram) : Hexagram := fun i => !(h i)

@[simp] theorem cuo_apply (h : Hexagram) (i : Fin 6) :
    cuo h i = !(h i) := rfl

/-- cuo is involutive. -/
theorem cuo_involutive (h : Hexagram) : cuo (cuo h) = h := by
  funext i
  unfold cuo
  cases h i <;> rfl

@[simp] theorem cuo_qianqian : cuo qianqian = kunkun := by
  apply ext <;> rfl

@[simp] theorem cuo_kunkun : cuo kunkun = qianqian := by
  apply ext <;> rfl

@[simp] theorem cuo_jiji : cuo jiji = weiji := by
  apply ext <;> rfl

@[simp] theorem cuo_weiji : cuo weiji = jiji := by
  apply ext <;> rfl

/-! ## § 2 zong (綜) — yao-order reversal -/

/-- The reverse of a `Fin 6` index `i` is `5 - i`. -/
private def revIdx (i : Fin 6) : Fin 6 := ⟨5 - i.val, by omega⟩

/-- 綜 (zōng, "reverse"): reverse the yao order — y1 ↔ y6, y2 ↔ y5, y3 ↔ y4. -/
def zong (h : Hexagram) : Hexagram := fun i => h (revIdx i)

@[simp] theorem zong_y1 (h : Hexagram) : (zong h).y1 = h.y6 := rfl
@[simp] theorem zong_y2 (h : Hexagram) : (zong h).y2 = h.y5 := rfl
@[simp] theorem zong_y3 (h : Hexagram) : (zong h).y3 = h.y4 := rfl
@[simp] theorem zong_y4 (h : Hexagram) : (zong h).y4 = h.y3 := rfl
@[simp] theorem zong_y5 (h : Hexagram) : (zong h).y5 = h.y2 := rfl
@[simp] theorem zong_y6 (h : Hexagram) : (zong h).y6 = h.y1 := rfl

/-- zong is involutive. -/
theorem zong_involutive (h : Hexagram) : zong (zong h) = h := by
  apply ext <;> rfl

@[simp] theorem zong_qianqian : zong qianqian = qianqian := by
  apply ext <;> rfl

@[simp] theorem zong_kunkun : zong kunkun = kunkun := by
  apply ext <;> rfl

@[simp] theorem zong_jiji : zong jiji = weiji := by
  apply ext <;> rfl

@[simp] theorem zong_weiji : zong weiji = jiji := by
  apply ext <;> rfl

/-! ## § 3 cuoZong (錯綜) — composite -/

/-- 錯綜 (cuòzōng): cuo composed with zong.  V₄ central element. -/
def cuoZong (h : Hexagram) : Hexagram := cuo (zong h)

/-- cuo and zong commute. -/
theorem cuo_zong_comm (h : Hexagram) : cuo (zong h) = zong (cuo h) := by
  apply ext <;> rfl

/-- cuoZong = zong ∘ cuo too. -/
theorem cuoZong_eq_zong_cuo (h : Hexagram) : cuoZong h = zong (cuo h) := by
  unfold cuoZong; exact cuo_zong_comm h

/-- cuoZong is involutive. -/
theorem cuoZong_involutive (h : Hexagram) : cuoZong (cuoZong h) = h := by
  unfold cuoZong
  rw [← cuo_zong_comm, cuo_involutive, zong_involutive]

@[simp] theorem cuoZong_qianqian : cuoZong qianqian = kunkun := by
  unfold cuoZong; rw [zong_qianqian, cuo_qianqian]

@[simp] theorem cuoZong_kunkun : cuoZong kunkun = qianqian := by
  unfold cuoZong; rw [zong_kunkun, cuo_kunkun]

@[simp] theorem cuoZong_jiji : cuoZong jiji = jiji := by
  unfold cuoZong; rw [zong_jiji, cuo_weiji]

@[simp] theorem cuoZong_weiji : cuoZong weiji = weiji := by
  unfold cuoZong; rw [zong_weiji, cuo_jiji]

/-! ## § 4 The V₄ group laws on Hexagram -/

/-- Identity, cuo, zong, cuoZong all have order ≤ 2.  Together with
    `id`, the four constitute the Klein four-group V₄ acting on
    Hexagram. -/
theorem v4_orders (h : Hexagram) :
    h = h
  ∧ cuo (cuo h) = h
  ∧ zong (zong h) = h
  ∧ cuoZong (cuoZong h) = h :=
  ⟨rfl, cuo_involutive h, zong_involutive h, cuoZong_involutive h⟩

/-! ## § 5 hu (互) — the mutual operator (NOT a V₄ element) -/

/-- 互 (hù, "mutual"): take yao 2-3-4 as new inner trigram and yao
    3-4-5 as new outer trigram.  Concretely:

        hu h = h.y2 h.y3 h.y4 h.y3 h.y4 h.y5

    NB: This is NOT a V₄ element.  It has exactly two fixed points
    (`qianqian`, `kunkun`) and the 2-cycle `jiji ↔ weiji`. -/
def hu (h : Hexagram) : Hexagram :=
  mk h.y2 h.y3 h.y4 h.y3 h.y4 h.y5

@[simp] theorem hu_qianqian : hu qianqian = qianqian := by
  apply ext <;> rfl

@[simp] theorem hu_kunkun : hu kunkun = kunkun := by
  apply ext <;> rfl

@[simp] theorem hu_jiji : hu jiji = weiji := by
  apply ext <;> rfl

@[simp] theorem hu_weiji : hu weiji = jiji := by
  apply ext <;> rfl

/-- 互 has exactly two fixed points: `qianqian` and `kunkun`. -/
theorem hu_fixed_point (h : Hexagram) :
    hu h = h ↔ h = qianqian ∨ h = kunkun := by
  constructor
  · intro heq
    -- hu h = h: read the 6 component constraints in terms of y₁..y₆.
    have c1 : h.y2 = h.y1 := by
      have := congrFun heq ⟨0, by decide⟩
      simp only [hu, mk, y2] at this; exact this
    have c2 : h.y3 = h.y2 := by
      have := congrFun heq ⟨1, by decide⟩
      simp only [hu, mk, y3] at this; exact this
    have c3 : h.y4 = h.y3 := by
      have := congrFun heq ⟨2, by decide⟩
      simp only [hu, mk, y4] at this; exact this
    have c5 : h.y4 = h.y5 := by
      have := congrFun heq ⟨4, by decide⟩
      simp only [hu, mk, y4] at this; exact this
    have c6 : h.y5 = h.y6 := by
      have := congrFun heq ⟨5, by decide⟩
      simp only [hu, mk, y5] at this; exact this
    -- All six yao agree.
    have h12 : h.y1 = h.y2 := c1.symm
    have h13 : h.y1 = h.y3 := h12.trans c2.symm
    have h14 : h.y1 = h.y4 := h13.trans c3.symm
    have h15 : h.y1 = h.y5 := h14.trans c5
    have h16 : h.y1 = h.y6 := h15.trans c6
    -- Either all are yang or all are yin.
    rcases hy1 : h.y1 with _ | _
    · -- yang case: h.y1 = false = yang ⇒ h = qianqian
      left
      have h2_yang : h.y2 = yang := h12.symm.trans hy1
      have h3_yang : h.y3 = yang := h13.symm.trans hy1
      have h4_yang : h.y4 = yang := h14.symm.trans hy1
      have h5_yang : h.y5 = yang := h15.symm.trans hy1
      have h6_yang : h.y6 = yang := h16.symm.trans hy1
      apply ext
      · rw [hy1]; rfl
      · rw [h2_yang]; rfl
      · rw [h3_yang]; rfl
      · rw [h4_yang]; rfl
      · rw [h5_yang]; rfl
      · rw [h6_yang]; rfl
    · -- yin case: h.y1 = true = yin ⇒ h = kunkun
      right
      have h2_yin : h.y2 = yin := h12.symm.trans hy1
      have h3_yin : h.y3 = yin := h13.symm.trans hy1
      have h4_yin : h.y4 = yin := h14.symm.trans hy1
      have h5_yin : h.y5 = yin := h15.symm.trans hy1
      have h6_yin : h.y6 = yin := h16.symm.trans hy1
      apply ext
      · rw [hy1]; rfl
      · rw [h2_yin]; rfl
      · rw [h3_yin]; rfl
      · rw [h4_yin]; rfl
      · rw [h5_yin]; rfl
      · rw [h6_yin]; rfl
  · rintro (h_eq | h_eq) <;> rw [h_eq] <;> simp

/-- 互 is NOT involutive on all hexagrams.  Concretely `jiji ↔ weiji`
    is a 2-cycle, so `hu (hu jiji) = jiji` but `hu jiji ≠ jiji`. -/
theorem hu_jiji_2cycle : hu (hu jiji) = jiji := by
  rw [hu_jiji, hu_weiji]

theorem hu_weiji_2cycle : hu (hu weiji) = weiji := by
  rw [hu_weiji, hu_jiji]

end Hexagram

end SSBX.Foundation.Atlas.Yi
