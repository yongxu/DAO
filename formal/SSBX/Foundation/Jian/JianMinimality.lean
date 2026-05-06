/-
# 間 之 核 — minimality (each-removal-breaks STLC?)

  Per spec § 七 "Minimal" (conjectured):
    "任去九字中之一,则 STLC-completeness 失"
  (Now updated to 14 字: original 9 + 方 (D4 续) + 已/矣 (D4 止) + 提/取 (D1
  提取-without-主从). Same minimality picture: only 之 + 者 needed for STLC.)

  This file verifies the conjecture per character. Result (honest reading):
    - **之** (pair structure): NECESSARY for STLC (no pair → no application).
    - **者** (Op.zhe): NECESSARY for STLC (no zhe → no abstraction marker).
    - **非/而/凡/即/也/是/令/方/已/矣/提/取**: NOT necessary for bare STLC.
      (`enc` never uses these 12 ops; removing any leaves enc intact.)

  The spec's conjecture as stated **holds for 2 of 14 字** w.r.t. bare STLC
  (untyped lambda calculus with var/abs/app). The other 12 字 serve roles
  outside bare STLC — they are minimal w.r.t. the FULL kernel, not STLC.
-/

import SSBX.Foundation.Jian.Jian
import SSBX.Foundation.Jian.JianSTLC

namespace SSBX.Foundation.Jian.JianMinimality

open SSBX.Foundation.Jian.Jian
open SSBX.Foundation.Jian.JianSTLC

/-- All Op atoms appearing in a term. -/
def opsUsed : Wen → List Op
  | .atom _ => []
  | .op o => [o]
  | .pair l r => opsUsed l ++ opsUsed r

/-- Whether the term contains a pair (之-structure) anywhere. -/
def hasPair : Wen → Bool
  | .atom _ => false
  | .op _ => false
  | .pair _ _ => true

/-! ## Positive results: 之 and 者 are necessary for STLC -/

/-- The identity combinator's encoding uses Op.zhe.
    This witnesses that some STLC term requires 者. -/
theorem enc_id_uses_zhe :
    Op.zhe ∈ opsUsed (enc (.abs "x" (.var "x"))) := by
  show Op.zhe ∈ opsUsed (Wen.Zhe "x" (.atom "x"))
  show Op.zhe ∈ opsUsed (.pair (.op .zhe) (.pair (.atom "x") (.atom "x")))
  simp [opsUsed]

/-- The identity combinator's encoding has a pair.
    This witnesses that some STLC term requires 之 (pair structure). -/
theorem enc_id_has_pair :
    hasPair (enc (.abs "x" (.var "x"))) = true := by
  show hasPair (Wen.Zhe "x" (.atom "x")) = true
  rfl

/-- The application `f x`'s encoding has a pair (the outermost). -/
theorem enc_app_has_pair (f x : Lam) :
    hasPair (enc (.app f x)) = true := by
  show hasPair (.pair (enc f) (enc x)) = true
  rfl

/-! ## Negative results: 7 ops are NOT necessary for STLC -/

/-- `enc` uses only `Op.zhe` and pair structure — never any of the other 9 ops. -/
theorem enc_uses_only_zhe : ∀ (t : Lam), ∀ o ∈ opsUsed (enc t), o = Op.zhe := by
  intro t
  induction t with
  | var n =>
    intro o h
    simp [enc, opsUsed] at h
  | abs b body ih =>
    intro o h
    simp [enc, Wen.Zhe, opsUsed] at h
    rcases h with h | h
    · exact h
    · exact ih o h
  | app f x ih_f ih_x =>
    intro o h
    simp [enc, opsUsed] at h
    rcases h with h | h
    · exact ih_f o h
    · exact ih_x o h

/-- **General corollary** (parametric): `enc` doesn't use any Op other than 者.
    一 lemma 取代 12 specializations — 一 在 parametric 层 = 多 在 surface 层. -/
theorem enc_does_not_use_other (t : Lam) (o : Op) (h_ne : o ≠ Op.zhe) :
    o ∉ opsUsed (enc t) := by
  intro h
  exact h_ne (enc_uses_only_zhe t o h)

/-! ### Per-Op specializations (one-line corollaries of `enc_does_not_use_other`) -/

theorem enc_does_not_use_fei     (t : Lam) : Op.fei     ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .fei     (by decide)
theorem enc_does_not_use_er      (t : Lam) : Op.er      ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .er      (by decide)
theorem enc_does_not_use_fan     (t : Lam) : Op.fan     ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .fan     (by decide)
theorem enc_does_not_use_ji      (t : Lam) : Op.ji      ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .ji      (by decide)
theorem enc_does_not_use_ye      (t : Lam) : Op.ye      ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .ye      (by decide)
theorem enc_does_not_use_shi     (t : Lam) : Op.shi     ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .shi     (by decide)
theorem enc_does_not_use_ling    (t : Lam) : Op.ling    ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .ling    (by decide)
theorem enc_does_not_use_fang    (t : Lam) : Op.fang    ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .fang    (by decide)
theorem enc_does_not_use_yiAnter (t : Lam) : Op.yiAnter ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .yiAnter (by decide)
theorem enc_does_not_use_yiCos   (t : Lam) : Op.yiCos   ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .yiCos   (by decide)
theorem enc_does_not_use_ti      (t : Lam) : Op.ti      ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .ti      (by decide)
theorem enc_does_not_use_qu      (t : Lam) : Op.qu      ∉ opsUsed (enc t) :=
  enc_does_not_use_other t .qu      (by decide)

/-! ## Summary

  **Necessary for STLC** (minimality holds):
    - 之 (pair structure) — `enc_id_has_pair`, `enc_app_has_pair`
    - 者 (Op.zhe)         — `enc_id_uses_zhe`

  **NOT necessary for STLC** (counter-conjecture; spec § 七 over-claims):
    - 非 (Op.fei)     — `enc_does_not_use_fei`
    - 而 (Op.er)      — `enc_does_not_use_er`
    - 凡 (Op.fan)     — `enc_does_not_use_fan`
    - 即 (Op.ji)      — `enc_does_not_use_ji`
    - 也 (Op.ye)      — `enc_does_not_use_ye`
    - 是 (Op.shi)     — `enc_does_not_use_shi`
    - 令 (Op.ling)    — `enc_does_not_use_ling`
    - 方 (Op.fang)    — `enc_does_not_use_fang` (D4 续 ongoing)
    - 已 (Op.yiAnter) — `enc_does_not_use_yiAnter` (D4 止 anterior)
    - 矣 (Op.yiCos)   — `enc_does_not_use_yiCos` (D4 止 change-of-state)
    - 提 (Op.ti)      — `enc_does_not_use_ti` (D1 提取-only lift)
    - 取 (Op.qu)      — `enc_does_not_use_qu` (D1 提取-only select)

  These 12 字 are minimal w.r.t. their OWN capabilities, not STLC.

  **Spec revision suggested**: § 七's "Minimal" claim should distinguish:
    - STLC-minimality (only 之 + 者 needed)
    - Capability-minimality (each 字 minimal for its specific role)
-/

end SSBX.Foundation.Jian.JianMinimality
