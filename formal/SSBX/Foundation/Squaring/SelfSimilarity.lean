/-
# Self-similarity — squaring tower {R₀, R₁, R₂, R₄, R₈} explicit isomorphisms

Doctrine: T_{k+1} = T_k × T_k for k ≥ 1, with T₀ = R₀ = Unit and
T₁ = R₁ obtained from the foundational coproduct step (R₀ + R₀).
The squaring tower indices are 2^k:

  T_k:   R₀     R₁     R₂     R₄     R₈
         (k=0)  (k=1)  (k=2)  (k=3)  (k=4)
         1      2      4      16     256

This file proves the squaring isomorphisms as type equivalences:

  R₁ ≃ R₀ ⊕ R₀     (foundational distinction from the Unit root)
  R₂ ≃ R₁ × R₁     (R₂ = line × line)
  R₄ ≃ R₂ × R₂     (R₄ = R₂ × R₂ structurally)
  R₈ ≃ R₄ × R₄     (R₈ = R₄ × R₄, the 256-state universe)

Plus the off-tower multi-route junction at R₆:

  R₆ ≃ R₃ × R₃     (Hexagram = Trigram × Trigram structurally)
  R₆ ≃ R₂ × R₄     (R₆ = R₂ × R₄ structurally)
  R₆ ≃ R₁ × R₅     (R₆ = line × R₅ structurally)

Per doctrine §7.3, R₆ is the "三 routes 合一" point — it equals
R₃² = R₂ × R₄ = R₁ × R₅, three squaring paths through the tower
that converge at the same off-tower layer.
-/
import SSBX.Foundation.Squaring.V4Tensor
import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Squaring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Hierarchy.LiftProject

namespace SelfSimilarity

/-! ## § 0 Foundational split: R₁ ≃ R₀ ⊕ R₀ -/

/-- R₁ = line ≃ Bool. This exposes the first binary distinction. -/
def r1_eq_bool : R1 ≃ Bool where
  toFun
    | .yang => false
    | .yin => true
  invFun
    | false => .yang
    | true => .yin
  left_inv y := by cases y <;> rfl
  right_inv b := by cases b <;> rfl

/-- R₁ = line ≃ R₀ ⊕ R₀. The Unit root splits into the first two-valued layer. -/
def r1_eq_r0_plus_r0 : R1 ≃ R0 ⊕ R0 where
  toFun
    | .yang => Sum.inl ()
    | .yin => Sum.inr ()
  invFun
    | Sum.inl _ => .yang
    | Sum.inr _ => .yin
  left_inv y := by cases y <;> rfl
  right_inv s := by
    cases s with
    | inl u => cases u; rfl
    | inr u => cases u; rfl

/-! ## § 1 Squaring-tower layer isomorphisms (T_{k+1} ≃ T_k × T_k) -/

/-- T₂ = R₂ ≃ R₁ × R₁ (two independent line bits). -/
def r2_eq_r1_squared : R2 ≃ R1 × R1 where
  toFun s := (s.y1, s.y2)
  invFun p := ⟨p.1, p.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by cases p; rfl

/-- T₃ = R₄ ≃ R₂ × R₂ (surface = base × upright ≃ R₂ × R₂ structurally).

    The base side is equivalent to R₂ via the 4-element bijection
    (thing/motion/interval/event ↔ greaterYang/lesserYin/lesserYang/greaterYin);
    same for the upright side. -/
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

/-- R₄ surface = base × upright ≃ R₂ × R₂. -/
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
  we exhibit a concrete bijection by splitting an 8-line block into two
  4-line halves and treating each as an R₄ surface via benToSiXiang/zhengToSiXiang.

  The canonical decomposition: R₈ = R₆ × temporal state, where
  R₆ = R₃ × R₃ and the temporal state has type R₂.
  So R₈ = R₃ × R₃ × R₂.

  Reshuffling to R₄ × R₄: pack {y1, y2, y3, y4} as inner R₄ surface and
  {y5, y6, factor of the temporal state} as outer R₄ surface. The bit count matches
  (4 + 4 = 8) and the group structure is preserved by XOR.

  This is the SQUARING view of R₈ — the one the doctrine privileges
  over the (R₆ × temporal-state) incrementing view. -/

/-- An R₈ cell as 8 line bits: 6 from R₆ + 2 from the temporal-state V₄. -/
def r8_to_8yao (c : R8) : Yao × Yao × Yao × Yao × Yao × Yao × Yao × Yao :=
  let ⟨h, s⟩ := c
  let y7 : Yao := if s.1 then .yin else .yang
  let y8 : Yao := if s.2 then .yin else .yang
  (h.y1, h.y2, h.y3, h.y4, h.y5, h.y6, y7, y8)

/-- The inverse: 8 line bits back to R₈. -/
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

/-- The 8-line tuple is in bijection with R₂⁴.
    Combined with R₄ ≃ R₂ × R₂, this gives R₈ ≃ R₄ × R₄ via four-fold
    grouping. -/
def r8_to_r4_squared (c : R8) : R4 × R4 :=
  let ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := r8_to_8yao c
  -- inner R₄ surface = (base from y1,y2) × (upright from y3,y4)
  let inner : R4 := (siXiangToBen ⟨y1, y2⟩, siXiangToZheng ⟨y3, y4⟩)
  -- outer R₄ surface = (base from y5,y6) × (upright from y7,y8)
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
    R₈ cells and (R₄ surface, R₄ surface) pairs. -/
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
    R₂ × R₄
    R₁ × R₅
  — three different squaring paths through the tower converge at R₆.

  Here we prove all three routes as explicit bit rearrangements. -/

/-- R₆ = Hexagram ≃ R₃ × R₃ (Hexagram = Trigram × Trigram structurally). -/
def r6_eq_r3_squared : R6 ≃ R3 × R3 where
  toFun h := (⟨h.y1, h.y2, h.y3⟩, ⟨h.y4, h.y5, h.y6⟩)
  invFun p := ⟨p.1.y1, p.1.y2, p.1.y3, p.2.y1, p.2.y2, p.2.y3⟩
  left_inv h := by cases h; rfl
  right_inv p := by cases p with | _ p1 p2 => cases p1; cases p2; rfl

/-- R₆ ≃ R₂ × R₄ by an explicit bit rearrangement. -/
def r6_eq_r2_times_r4 : R6 ≃ R2 × R4 where
  toFun h :=
    (⟨h.y1, h.y2⟩,
     (siXiangToBen ⟨h.y3, h.y4⟩, siXiangToZheng ⟨h.y5, h.y6⟩))
  invFun p :=
    let s := p.1
    let m := p.2
    let ⟨y3, y4⟩ := benToSiXiang m.1
    let ⟨y5, y6⟩ := zhengToSiXiang m.2
    ⟨s.y1, s.y2, y3, y4, y5, y6⟩
  left_inv h := by
    cases h with
    | mk y1 y2 y3 y4 y5 y6 =>
      cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;>
      cases y5 <;> cases y6 <;> rfl
  right_inv p := by
    rcases p with ⟨⟨y1, y2⟩, ⟨b, z⟩⟩
    cases y1 <;> cases y2 <;> cases b <;> cases z <;> rfl

/-- R₆ ≃ R₁ × R₅ by an explicit bit rearrangement. -/
def r6_eq_r1_times_r5 : R6 ≃ R1 × R5 where
  toFun h :=
    (h.y1,
     ((siXiangToBen ⟨h.y2, h.y3⟩, siXiangToZheng ⟨h.y4, h.y5⟩),
      yaoToBool h.y6))
  invFun p :=
    let y1 := p.1
    let w := p.2
    let m := w.1
    let bit := w.2
    let ⟨y2, y3⟩ := benToSiXiang m.1
    let ⟨y4, y5⟩ := zhengToSiXiang m.2
    ⟨y1, y2, y3, y4, y5, boolToYao bit⟩
  left_inv h := by
    cases h with
    | mk y1 y2 y3 y4 y5 y6 =>
      cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;>
      cases y5 <;> cases y6 <;> rfl
  right_inv p := by
    rcases p with ⟨y1, ⟨⟨b, z⟩, bit⟩⟩
    cases y1 <;> cases b <;> cases z <;> cases bit <;> rfl

/-! ## § 4 R₈/R₇ split -/

/-- R₈ = R₇ × Bool by splitting temporal state into trace bit and projection bit. -/
def r8_eq_r7_times_bool : R8 ≃ R7 × Bool where
  toFun c := ((c.1, c.2.1), c.2.2)
  invFun p := (p.1.1, (p.1.2, p.2))
  left_inv c := by
    rcases c with ⟨h, ⟨yin, guo⟩⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨h, yin⟩, guo⟩
    rfl

/-! ## § 5 Squaring-tower summary -/

theorem squaring_tower_summary :
    Nonempty (R2 ≃ R1 × R1) ∧
    Nonempty (R4 ≃ R2 × R2) ∧
    Nonempty (R8 ≃ R4 × R4) ∧
    Nonempty (R6 ≃ R3 × R3) :=
  ⟨⟨r2_eq_r1_squared⟩, ⟨r4_eq_r2_squared⟩, ⟨r8_eq_r4_squared⟩, ⟨r6_eq_r3_squared⟩⟩

/-- Summary of the roadmap §2 partial gaps now captured in this file. -/
theorem self_similarity_gap_summary :
    Nonempty (R1 ≃ R0 ⊕ R0) ∧
    Nonempty (R1 ≃ Bool) ∧
    Nonempty (R6 ≃ R2 × R4) ∧
    Nonempty (R6 ≃ R1 × R5) ∧
    Nonempty (R8 ≃ R7 × Bool) :=
  ⟨⟨r1_eq_r0_plus_r0⟩,
   ⟨r1_eq_bool⟩,
   ⟨r6_eq_r2_times_r4⟩,
   ⟨r6_eq_r1_times_r5⟩,
   ⟨r8_eq_r7_times_bool⟩⟩

end SelfSimilarity

end SSBX.Foundation.Squaring
