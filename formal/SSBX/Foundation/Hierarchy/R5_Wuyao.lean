/-
# R₅ Wuyao — strict (Z/2)⁵ = 32 carrier (Mian × Bool)

(strict-uniform R₀..R₈ enumeration; this is the "missing" R₅ layer that
sits between R₄ Mian (= Ben × Zheng = 16) and R₆ Hexagram (= Trigram² = 64).)

R₅ = R₄ × Bool = Mian × Bool. The added Bool is the "5th yao" extension
bit — Mian carries 4 bits (2 for Ben + 2 for Zheng = 4); a single Bool
makes it (Z/2)⁵ = 32.

|Wuyao| = 16 × 2 = 32 = (Z/2)⁵.

Atomic operator: **flip5** = toggle the 5th-yao Bool bit (Z/2 involution).

Mian-extending lift / project pair:
- liftR4toR5 : Mian → Bool → Wuyao
- projR5toR4 : Wuyao → Mian
with proj ∘ lift = id (faithful R₄ ↪ R₅).

Mirrors `SSBX.Foundation.Bagua.Cell128` structure.
-/
import SSBX.Foundation.Bagua.BenZheng

namespace SSBX.Foundation.Hierarchy.R5_Wuyao

open SSBX.Foundation.Bagua.BenZheng

/-! ## § 1 R₅ carrier: Wuyao = Mian × Bool -/

/-- R₅ (32-cell Wuyao) = Mian × Bool. -/
abbrev Wuyao : Type := Mian × Bool

namespace Wuyao

/-- All 32 wuyao: 16 mian × 2 bit-state. -/
def all : List Wuyao :=
  Mian.all.flatMap fun m => [(m, false), (m, true)]

theorem all_length : all.length = 32 := by native_decide

theorem all_nodup : all.Nodup := by native_decide

theorem mem_all (w : Wuyao) : w ∈ all := by
  rcases w with ⟨m, b⟩
  unfold all
  refine List.mem_flatMap.mpr ⟨m, ?_, ?_⟩
  · -- m ∈ Mian.all
    -- Mian = Ben × Zheng; Mian.all enumerates all 16 by Ben.all.flatMap (Zheng.all.map ...)
    rcases m with ⟨bn, zh⟩
    show (bn, zh) ∈ Mian.all
    unfold Mian.all
    refine List.mem_flatMap.mpr ⟨bn, ?_, ?_⟩
    · cases bn <;> simp [Ben.all]
    · refine List.mem_map.mpr ⟨zh, ?_, rfl⟩
      cases zh <;> simp [Zheng.all]
  · cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

end Wuyao

/-! ## § 2 R₅ atomic operator: flip5 (toggle the 5th-yao Bool bit) -/

/-- flip5: toggle the Bool component (the "5th yao"). Z/2 involution. -/
def flip5 (w : Wuyao) : Wuyao := (w.1, !w.2)

/-- flip5 is involutive: flip5² = id. -/
theorem flip5_flip5 (w : Wuyao) : flip5 (flip5 w) = w := by
  rcases w with ⟨m, b⟩
  cases b <;> rfl

/-- flip5 preserves the Mian component. -/
theorem flip5_preserves_mian (w : Wuyao) : (flip5 w).1 = w.1 := by
  rcases w with ⟨m, b⟩; rfl

/-! ## § 3 Mian-extending lift / project pair (R₄ ↔ R₅) -/

/-- Lift R₄ Mian into R₅ Wuyao by attaching a 5th-yao bit. -/
def liftR4toR5 (m : Mian) (b : Bool) : Wuyao := (m, b)

/-- Project R₅ Wuyao back to R₄ Mian (forget the 5th-yao bit). -/
def projR5toR4 (w : Wuyao) : Mian := w.1

/-- proj ∘ lift = id on R₄: faithful R₄ ↪ R₅. -/
theorem proj_lift_id_R4 (m : Mian) (b : Bool) :
    projR5toR4 (liftR4toR5 m b) = m := rfl

/-! ## § 4 Public summary -/

/-- R₅ Wuyao 收口摘要: 基数 32 + 全覆盖 + flip5 involution. -/
theorem wuyao_summary :
    Wuyao.all.length = 32
    ∧ (∀ w : Wuyao, w ∈ Wuyao.all)
    ∧ (∀ w : Wuyao, flip5 (flip5 w) = w) :=
  ⟨Wuyao.all_length, Wuyao.mem_all, flip5_flip5⟩

end SSBX.Foundation.Hierarchy.R5_Wuyao
