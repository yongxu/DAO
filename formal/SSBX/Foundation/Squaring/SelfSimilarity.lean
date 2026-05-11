/-
# Self-similarity — squaring tower {R₀, R₁, R₂, R₄, R₈} explicit isomorphisms

Doctrine: T_{k+1} = T_k × T_k for k ≥ 1, with T₀ = R₀ = Unit and
T₁ = R₁ obtained from the foundational coproduct step (R₀ + R₀).
The squaring tower indices are 2^k:

  T_k:   R₀     R₁     R₂     R₄     R₈
         (k=0)  (k=1)  (k=2)  (k=3)  (k=4)
         1      2      4      16     256

This file proves the squaring isomorphisms as type equivalences:

  R₂ ≃ R₁ × R₁     (SiXiang = Yao × Yao)
  R₄ ≃ R₂ × R₂     (Mian = SiXiang × SiXiang structurally)
  R₈ ≃ R₄ × R₄     (R8 = Mian × Mian — the universe is once-squared 16-cells)

Plus the off-tower multi-route junction at R₆:

  R₆ ≃ R₃ × R₃     (Hexagram = Trigram × Trigram structurally)

Per doctrine §7.3, R₆ is the "三 routes 合一" point — it equals
R₃² = R₂ × R₄ = R₁ × R₅, three squaring paths through the tower
that converge at the same off-tower layer. Only the R₃² route is
proved here; the other two follow by composition with the tower
isomorphisms above.
-/
import SSBX.Foundation.Squaring.V4Tensor
import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Squaring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Hierarchy.LiftProject

namespace SelfSimilarity

/-! ## § 1 Squaring-tower layer isomorphisms (T_{k+1} ≃ T_k × T_k) -/

/-- T₂ = R₂ ≃ R₁ × R₁ (SiXiang = Yao²). -/
def r2_eq_r1_squared : R2 ≃ R1 × R1 where
  toFun s := (s.y1, s.y2)
  invFun p := ⟨p.1, p.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by cases p; rfl

/-- T₃ = R₄ ≃ R₂ × R₂ (Mian = Ben × Zheng ≃ SiXiang × SiXiang structurally).

    Ben ≃ SiXiang via the 4-element bijection (thing/motion/interval/event
    ↔ greaterYang/lesserYin/lesserYang/greaterYin); same for Zheng. -/
def benToSiXiang : SSBX.Foundation.Bagua.BenZheng.Ben → R2
  | .thing    => ⟨.yang, .yang⟩
  | .motion   => ⟨.yang, .yin⟩
  | .interval => ⟨.yin,  .yang⟩
  | .event    => ⟨.yin,  .yin⟩

def siXiangToBen : R2 → SSBX.Foundation.Bagua.BenZheng.Ben
  | ⟨.yang, .yang⟩ => .thing
  | ⟨.yang, .yin⟩  => .motion
  | ⟨.yin,  .yang⟩ => .interval
  | ⟨.yin,  .yin⟩  => .event

def zhengToSiXiang : SSBX.Foundation.Bagua.BenZheng.Zheng → R2
  | .trace    => ⟨.yang, .yang⟩
  | .momentum => ⟨.yang, .yin⟩
  | .pivot    => ⟨.yin,  .yang⟩
  | .occasion => ⟨.yin,  .yin⟩

def siXiangToZheng : R2 → SSBX.Foundation.Bagua.BenZheng.Zheng
  | ⟨.yang, .yang⟩ => .trace
  | ⟨.yang, .yin⟩  => .momentum
  | ⟨.yin,  .yang⟩ => .pivot
  | ⟨.yin,  .yin⟩  => .occasion

/-- R₄ = Mian = Ben × Zheng ≃ R₂ × R₂. -/
def r4_eq_r2_squared : R4 ≃ R2 × R2 where
  toFun m := (benToSiXiang m.1, zhengToSiXiang m.2)
  invFun p := (siXiangToBen p.1, siXiangToZheng p.2)
  left_inv := by
    rintro ⟨b, z⟩; cases b <;> cases z <;> rfl
  right_inv := by
    rintro ⟨⟨y1, y2⟩, ⟨y3, y4⟩⟩; cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> rfl

/-! ## § 2 The universe step: R₈ ≃ R₄ × R₄

  This is the doctrinal claim "宇宙 = 一次 R₄ 自相似". R₈ has 256 elements;
  R₄ × R₄ has 16 × 16 = 256. As (Z/2)⁸ groups they're isomorphic; here
  we exhibit a concrete bijection by splitting an 8-yao block into two
  4-yao halves and treating each as a Mian via benToSiXiang/zhengToSiXiang.

  The canonical decomposition: R₈ = (Hexagram × Shi) where
  Hexagram = R₆ = R₃ × R₃ (via inner/outer Trigram) and
  Shi = R₂. So R₈ = R₃ × R₃ × R₂.

  Reshuffling to R₄ × R₄: pack {y1, y2, y3, y4} as inner Mian (R₄) and
  {y5, y6, factor of Shi} as outer Mian (R₄). The bit count matches
  (4 + 4 = 8) and the group structure is preserved by XOR.

  This is the SQUARING view of R₈ — the one the doctrine privileges
  over the (Hexagram × Shi) incrementing view. -/

/-- An R₈ cell as 8 yao bits: 6 from Hexagram + 2 from Shi (V₄). -/
def r8_to_8yao (c : R8) : Yao × Yao × Yao × Yao × Yao × Yao × Yao × Yao :=
  let ⟨h, s⟩ := c
  let y7 : Yao := if s.1 then .yin else .yang
  let y8 : Yao := if s.2 then .yin else .yang
  (h.y1, h.y2, h.y3, h.y4, h.y5, h.y6, y7, y8)

/-- The inverse: 8 yao back to R₈. -/
def yao8_to_r8 : Yao × Yao × Yao × Yao × Yao × Yao × Yao × Yao → R8 :=
  fun ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ =>
    let h : Hexagram := ⟨y1, y2, y3, y4, y5, y6⟩
    let b1 : Bool := match y7 with | .yang => false | .yin => true
    let b2 : Bool := match y8 with | .yang => false | .yin => true
    (h, (b1, b2))

theorem r8_8yao_round_trip (c : R8) : yao8_to_r8 (r8_to_8yao c) = c := by
  rcases c with ⟨h, s⟩
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  rcases s with ⟨b1, b2⟩
  cases b1 <;> cases b2 <;> rfl

/-- The 8-yao tuple is in bijection with R₂⁴ = (Yao²)⁴ = (R₂)⁴.
    Combined with R₄ ≃ R₂ × R₂, this gives R₈ ≃ R₄ × R₄ via four-fold
    grouping. -/
def r8_to_r4_squared (c : R8) : R4 × R4 :=
  let ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := r8_to_8yao c
  -- inner Mian = (Ben from y1,y2) × (Zheng from y3,y4)
  let inner : R4 := (siXiangToBen ⟨y1, y2⟩, siXiangToZheng ⟨y3, y4⟩)
  -- outer Mian = (Ben from y5,y6) × (Zheng from y7,y8)
  let outer : R4 := (siXiangToBen ⟨y5, y6⟩, siXiangToZheng ⟨y7, y8⟩)
  (inner, outer)

def r4_squared_to_r8 : R4 × R4 → R8 :=
  fun ⟨inner, outer⟩ =>
    let ⟨bi, zi⟩ := inner
    let ⟨bo, zo⟩ := outer
    let ⟨y1, y2⟩ := benToSiXiang bi
    let ⟨y3, y4⟩ := zhengToSiXiang zi
    let ⟨y5, y6⟩ := benToSiXiang bo
    let ⟨y7, y8⟩ := zhengToSiXiang zo
    yao8_to_r8 ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩

/-- THE SQUARING-TOWER UNIVERSE THEOREM: R₈ ≃ R₄ × R₄.

    This is the precise statement of "宇宙 = R₄ once-squared". The
    cardinality 256 = 16² is realized by an explicit bijection between
    R₈ cells and (Mian, Mian) pairs. -/
def r8_eq_r4_squared : R8 ≃ R4 × R4 where
  toFun := r8_to_r4_squared
  invFun := r4_squared_to_r8
  left_inv := by
    rintro ⟨⟨y1, y2, y3, y4, y5, y6⟩, ⟨b1, b2⟩⟩
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;>
    cases y5 <;> cases y6 <;> cases b1 <;> cases b2 <;> rfl
  right_inv := by
    rintro ⟨⟨bi, zi⟩, ⟨bo, zo⟩⟩
    cases bi <;> cases zi <;> cases bo <;> cases zo <;> rfl

/-! ## § 3 Off-tower junction at R₆ — three squaring routes converge

  R₆ has special doctrinal status: it equals (modulo iso)
    R₃ × R₃       (Hexagram = Trigram squared)
    R₂ × R₄       (SiXiang × Mian)
    R₁ × R₅       (Yao × Wuyao)
  — three different squaring paths through the tower converge at R₆.

  Here we prove the canonical R₃² route. The other two follow by
  composition with the tower isos r4_eq_r2_squared and r2_eq_r1_squared. -/

/-- R₆ = Hexagram ≃ R₃ × R₃ (Hexagram = Trigram × Trigram structurally). -/
def r6_eq_r3_squared : R6 ≃ R3 × R3 where
  toFun h := (⟨h.y1, h.y2, h.y3⟩, ⟨h.y4, h.y5, h.y6⟩)
  invFun p := ⟨p.1.y1, p.1.y2, p.1.y3, p.2.y1, p.2.y2, p.2.y3⟩
  left_inv h := by cases h; rfl
  right_inv p := by cases p with | _ p1 p2 => cases p1; cases p2; rfl

/-! ## § 4 Squaring-tower summary -/

theorem squaring_tower_summary :
    Nonempty (R2 ≃ R1 × R1) ∧
    Nonempty (R4 ≃ R2 × R2) ∧
    Nonempty (R8 ≃ R4 × R4) ∧
    Nonempty (R6 ≃ R3 × R3) :=
  ⟨⟨r2_eq_r1_squared⟩, ⟨r4_eq_r2_squared⟩, ⟨r8_eq_r4_squared⟩, ⟨r6_eq_r3_squared⟩⟩

end SelfSimilarity

end SSBX.Foundation.Squaring
