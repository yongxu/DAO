/-
# Uniform Lift / Project API across the R-hierarchy

The R-hierarchy is strict (Z/2)ⁿ uniform:

  R₀ = Unit                                (1)
  R₁ = Yao                                 (2)
  R₂ = SiXiang        = Yao²               (4)
  R₃ = Trigram        = Yao³               (8)
  R₄ = Mian           = Ben × Zheng        (16)
  R₅ = Wuyao          = Mian × Bool        (32)
  R₆ = Hexagram       = Yao⁶               (64)
  R₇ = Cell128        = Hexagram × YinBit  (128)
  R₈ = Cell256        = Hexagram × Shi     (256)

For each consecutive pair (Rₙ, R_{n+1}), this module provides a uniform
**Lift / Project** pair plus a `proj_lift_id_R{n}` retract lemma (faithful
Rₙ ↪ R_{n+1}).

## R₃ ↔ R₄ design choice

|R₃| = 8 = 2³ but |R₄| = 16 = 2⁴, so the R₃ → R₄ lift takes one extra Yao
(the 4th bit). Mian = Ben × Zheng has the canonical decomposition

  Ben   ≅ Yao²   (4 inhabitants)
  Zheng ≅ Yao²   (4 inhabitants)

We choose: split Trigram's 3 yaos as `(y1, y2)` → Ben and `(y3, extra)` →
Zheng. The projection drops the `extra` bit and recovers the trigram from
the Ben-pair plus the first Zheng-bit. This is canonical up to the
choice of which 4 enum tags map to which Yao² pair (decisions made via
`benFromYao` / `zhengFromYao` below; see comments).

## R₇ ↔ R₈ design

R₇ = Hexagram × YinBit, R₈ = Hexagram × Shi where Shi ≅ YinBit × GuoBit.
The R₇ → R₈ lift attaches a GuoBit; project drops it via `Shi.toYinGuo`.
-/
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Bagua.BenZheng
import SSBX.Foundation.Bagua.Cell128
import SSBX.Foundation.Bagua.Cell256
import SSBX.Foundation.Hierarchy.R5_Wuyao

namespace SSBX.Foundation.Hierarchy.LiftProject

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.BaguaAlgebra
open SSBX.Foundation.Bagua.BenZheng
open SSBX.Foundation.Bagua.Cell128
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Hierarchy.R5_Wuyao

/-! ## § 0 R-layer abbreviations -/

/-- R₀ = 太极 = Unit. -/
abbrev R0 : Type := Unit
/-- R₁ = 两仪 = Yao. -/
abbrev R1 : Type := Yao
/-- R₂ = 四象 = SiXiang. -/
abbrev R2 : Type := SiXiang
/-- R₃ = 八卦 = Trigram. -/
abbrev R3 : Type := Trigram
/-- R₄ = 16-命 = Mian = Ben × Zheng. -/
abbrev R4 : Type := Mian
/-- R₅ = 32-五爻 = Wuyao = Mian × Bool. -/
abbrev R5 : Type := Wuyao
/-- R₆ = 六十四卦 = Hexagram. -/
abbrev R6 : Type := Hexagram
/-- R₇ = 128-格 = Cell128 = Hexagram × YinBit. -/
abbrev R7 : Type := Cell128
/-- R₈ = 256-格 = Cell256 = Hexagram × Shi. -/
abbrev R8 : Type := Cell256

/-! ## § 1 R₀ ↔ R₁ -/

/-- 太极 ↪ 两仪: lift the Unit root by attaching a Yao. -/
def liftR0toR1 (_ : R0) (y : Yao) : R1 := y

/-- 两仪 ↠ 太极: forget the Yao. -/
def projR1toR0 (_ : R1) : R0 := ()

theorem proj_lift_id_R0 (r0 : R0) (y : Yao) :
    projR1toR0 (liftR0toR1 r0 y) = r0 := rfl

/-! ## § 2 R₁ ↔ R₂ -/

/-- 两仪 ↪ 四象: extend a Yao by a 2nd Yao. -/
def liftR1toR2 (y1 : R1) (y2 : Yao) : R2 := ⟨y1, y2⟩

/-- 四象 ↠ 两仪: forget the 2nd Yao (keep y1). -/
def projR2toR1 (s : R2) : R1 := s.y1

theorem proj_lift_id_R1 (y1 : R1) (y2 : Yao) :
    projR2toR1 (liftR1toR2 y1 y2) = y1 := rfl

/-! ## § 3 R₂ ↔ R₃ -/

/-- 四象 ↪ 八卦: extend a SiXiang by a 3rd Yao. -/
def liftR2toR3 (s : R2) (y3 : Yao) : R3 := ⟨s.y1, s.y2, y3⟩

/-- 八卦 ↠ 四象: forget the 3rd Yao (keep y1, y2). -/
def projR3toR2 (t : R3) : R2 := ⟨t.y1, t.y2⟩

theorem proj_lift_id_R2 (s : R2) (y3 : Yao) :
    projR3toR2 (liftR2toR3 s y3) = s := by
  cases s; rfl

/-! ## § 4 R₃ ↔ R₄ — Trigram ↔ Mian (= Ben × Zheng)

  Strategy: encode Yao²-pairs as Ben/Zheng via canonical 2-bit bijections.
  - (y1, y2) → Ben      (4 inhabitants)
  - (y3, extra) → Zheng (4 inhabitants)
  - Project drops `extra` (the 4th yao) and recovers a trigram. -/

/-- Yao² → Ben canonical bijection.
    (yang, yang) → thing   / (yang, yin) → motion
    (yin,  yang) → interval / (yin,  yin) → shi -/
def benFromYao (y1 y2 : Yao) : Ben :=
  match y1, y2 with
  | .yang, .yang => .thing
  | .yang, .yin  => .motion
  | .yin,  .yang => .interval
  | .yin,  .yin  => .shi

/-- Ben → Yao² inverse: extract the first bit. -/
def benToYao1 : Ben → Yao
  | .thing | .motion => .yang
  | .interval | .shi => .yin

/-- Ben → Yao² inverse: extract the second bit. -/
def benToYao2 : Ben → Yao
  | .thing | .interval => .yang
  | .motion | .shi => .yin

theorem benFromYao_yao1 (y1 y2 : Yao) : benToYao1 (benFromYao y1 y2) = y1 := by
  cases y1 <;> cases y2 <;> rfl

theorem benFromYao_yao2 (y1 y2 : Yao) : benToYao2 (benFromYao y1 y2) = y2 := by
  cases y1 <;> cases y2 <;> rfl

/-- Yao² → Zheng canonical bijection.
    (yang, yang) → jiFaint    / (yang, yin) → shiForce
    (yin,  yang) → jiOccasion / (yin,  yin) → shiTime -/
def zhengFromYao (y3 y4 : Yao) : Zheng :=
  match y3, y4 with
  | .yang, .yang => .jiFaint
  | .yang, .yin  => .shiForce
  | .yin,  .yang => .jiOccasion
  | .yin,  .yin  => .shiTime

/-- Zheng → Yao² inverse: extract the first bit (the trigram's y3). -/
def zhengToYao1 : Zheng → Yao
  | .jiFaint | .shiForce => .yang
  | .jiOccasion | .shiTime => .yin

/-- Zheng → Yao² inverse: extract the second bit (the lifted "extra" bit). -/
def zhengToYao2 : Zheng → Yao
  | .jiFaint | .jiOccasion => .yang
  | .shiForce | .shiTime => .yin

theorem zhengFromYao_yao1 (y3 y4 : Yao) :
    zhengToYao1 (zhengFromYao y3 y4) = y3 := by
  cases y3 <;> cases y4 <;> rfl

theorem zhengFromYao_yao2 (y3 y4 : Yao) :
    zhengToYao2 (zhengFromYao y3 y4) = y4 := by
  cases y3 <;> cases y4 <;> rfl

/-- 八卦 ↪ 命: combine Trigram + extra Yao into Mian = Ben × Zheng.
    (y1, y2) → Ben, (y3, extra) → Zheng. -/
def liftR3toR4 (t : R3) (y4 : Yao) : R4 :=
  (benFromYao t.y1 t.y2, zhengFromYao t.y3 y4)

/-- 命 ↠ 八卦: extract trigram y1, y2 from Ben, y3 from Zheng (drop y4). -/
def projR4toR3 (m : R4) : R3 :=
  ⟨benToYao1 m.1, benToYao2 m.1, zhengToYao1 m.2⟩

theorem proj_lift_id_R3 (t : R3) (y4 : Yao) :
    projR4toR3 (liftR3toR4 t y4) = t := by
  cases t with
  | mk y1 y2 y3 =>
    simp [projR4toR3, liftR3toR4,
          benFromYao_yao1, benFromYao_yao2, zhengFromYao_yao1]

/-! ## § 5 R₄ ↔ R₅ — Mian ↔ Wuyao (= Mian × Bool)

  Re-exported from `SSBX.Foundation.Hierarchy.R5_Wuyao`. -/

/-- 命 ↪ 五爻: attach the 5th-yao Bool bit.
    (Re-export of `R5_Wuyao.liftR4toR5`.) -/
def liftR4toR5 (m : R4) (b : Bool) : R5 := R5_Wuyao.liftR4toR5 m b

/-- 五爻 ↠ 命: forget the 5th-yao Bool bit.
    (Re-export of `R5_Wuyao.projR5toR4`.) -/
def projR5toR4 (w : R5) : R4 := R5_Wuyao.projR5toR4 w

theorem proj_lift_id_R4 (m : R4) (b : Bool) :
    projR5toR4 (liftR4toR5 m b) = m :=
  R5_Wuyao.proj_lift_id_R4 m b

/-! ## § 6 R₅ ↔ R₆ — Wuyao ↔ Hexagram

  Wuyao = Mian × Bool ≅ (Z/2)⁵ = 32; Hexagram = (Z/2)⁶ = 64. The lift
  attaches one more Yao: project Wuyao → Trigram via R5→R4 + R4→R3, then
  combine with a 2nd trigram derived from (the Bool bit + extra Yao + a
  default yang yao) to form a Hexagram. We choose: the 5 bits of Wuyao
  give yaos y1..y5 (via the underlying 4 Mian-bits + Bool); the lift's
  extra Yao becomes y6.

  Decoding strategy (canonical):
    let t = projR4toR3 (projR5toR4 w);
    bool-bit = w.2;
    inner trigram = t (3 yaos);
    outer trigram = ⟨w.2 (as Yao), y6, y6⟩  -- pad outer y2 from y3 to fit 6 yaos
  But that loses info. Instead: encode (Mian × Bool) bits straight into 5
  hexagram positions (y1..y5) and let y6 = lift's extra Yao.

  Concrete: y1 = ben.bit1, y2 = ben.bit2, y3 = zheng.bit1, y4 = zheng.bit2,
  y5 = Bool→Yao (false→yang, true→yin), y6 = extra. -/

/-- Bool → Yao canonical: false = yang (default), true = yin. -/
def boolToYao (b : Bool) : Yao := if b then .yin else .yang

/-- Yao → Bool inverse. -/
def yaoToBool (y : Yao) : Bool := match y with | .yang => false | .yin => true

theorem yaoToBool_boolToYao (b : Bool) : yaoToBool (boolToYao b) = b := by
  cases b <;> rfl

/-- 五爻 ↪ 六爻: combine Wuyao (32 cells = 5 bits) with a 6th Yao to form
    a Hexagram (64 cells = 6 bits).

    Layout: y1, y2 ← ben (Mian.1) bit-pair; y3, y4 ← zheng (Mian.2) bit-pair;
    y5 ← Bool bit; y6 ← extra Yao. -/
def liftR5toR6 (w : R5) (y6 : Yao) : R6 :=
  let m := w.1
  let b := w.2
  ⟨benToYao1 m.1, benToYao2 m.1, zhengToYao1 m.2, zhengToYao2 m.2,
   boolToYao b, y6⟩

/-- 六爻 ↠ 五爻: drop y6, decode (y1, y2) → Ben, (y3, y4) → Zheng,
    y5 → Bool. -/
def projR6toR5 (h : R6) : R5 :=
  ((benFromYao h.y1 h.y2, zhengFromYao h.y3 h.y4), yaoToBool h.y5)

theorem benFromYao_benToYao (b : Ben) :
    benFromYao (benToYao1 b) (benToYao2 b) = b := by
  cases b <;> rfl

theorem zhengFromYao_zhengToYao (z : Zheng) :
    zhengFromYao (zhengToYao1 z) (zhengToYao2 z) = z := by
  cases z <;> rfl

theorem proj_lift_id_R5 (w : R5) (y6 : Yao) :
    projR6toR5 (liftR5toR6 w y6) = w := by
  rcases w with ⟨⟨b, z⟩, bit⟩
  simp [projR6toR5, liftR5toR6,
        benFromYao_benToYao, zhengFromYao_zhengToYao,
        yaoToBool_boolToYao]

/-! ## § 7 R₆ ↔ R₇ — Hexagram ↔ Cell128 (= Hexagram × YinBit) -/

/-- 六爻 ↪ 128-格: attach YinBit (R5/R7 atom 因 bit). -/
def liftR6toR7 (h : R6) (y : SSBX.Foundation.Bagua.Cell128.YinBit) : R7 := (h, y)

/-- 128-格 ↠ 六爻: drop YinBit. -/
def projR7toR6 (c : R7) : R6 := c.1

theorem proj_lift_id_R6 (h : R6) (y : SSBX.Foundation.Bagua.Cell128.YinBit) :
    projR7toR6 (liftR6toR7 h y) = h := rfl

/-! ## § 8 R₇ ↔ R₈ — Cell128 ↔ Cell256 (= Hexagram × Shi)

  Shi ≅ YinBit × GuoBit. R₈ adds a GuoBit (R6/R8 atom 果 bit) to R₇. -/

/-- 128-格 ↪ 256-格: attach GuoBit to YinBit, package as Shi. -/
def liftR7toR8 (c : R7) (g : SSBX.Foundation.Bagua.Cell256.GuoBit) : R8 :=
  (c.1, Shi.ofYinGuo (c.2, g))

/-- 256-格 ↠ 128-格: extract YinBit from Shi (drop GuoBit). -/
def projR8toR7 (c : R8) : R7 :=
  (c.1, (Shi.toYinGuo c.2).1)

theorem proj_lift_id_R7 (c : R7) (g : SSBX.Foundation.Bagua.Cell256.GuoBit) :
    projR8toR7 (liftR7toR8 c g) = c := by
  rcases c with ⟨h, y⟩
  simp [projR8toR7, liftR7toR8, Shi.toYinGuo_ofYinGuo]

/-! ## § 9 Public summary -/

/-- 8-pair lift/project retract summary: every consecutive R-layer pair
    has `proj ∘ lift = id` (faithful Rₙ ↪ R_{n+1}). -/
theorem liftProject_summary :
    (∀ r0 y, projR1toR0 (liftR0toR1 r0 y) = r0)
    ∧ (∀ y1 y2, projR2toR1 (liftR1toR2 y1 y2) = y1)
    ∧ (∀ s y3, projR3toR2 (liftR2toR3 s y3) = s)
    ∧ (∀ t y4, projR4toR3 (liftR3toR4 t y4) = t)
    ∧ (∀ m b, projR5toR4 (liftR4toR5 m b) = m)
    ∧ (∀ w y6, projR6toR5 (liftR5toR6 w y6) = w)
    ∧ (∀ h y, projR7toR6 (liftR6toR7 h y) = h)
    ∧ (∀ c g, projR8toR7 (liftR7toR8 c g) = c) :=
  ⟨proj_lift_id_R0,
   proj_lift_id_R1,
   proj_lift_id_R2,
   proj_lift_id_R3,
   proj_lift_id_R4,
   proj_lift_id_R5,
   proj_lift_id_R6,
   proj_lift_id_R7⟩

end SSBX.Foundation.Hierarchy.LiftProject
