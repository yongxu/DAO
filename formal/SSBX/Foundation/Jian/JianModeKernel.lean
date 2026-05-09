/-
# Virtue ↔ Kernel — ontological-mode mapping to dynamical kernel

  The 8 Virtue atoms (sheng/shou/yuan/shen/sai/xian/ju/kai) live in the
  ontological/phenomenological layer. The Kernel (Foundation/Kernel.lean) lives
  in the dynamical layer: 動 / 中 / 极 / 几 / orbits.

  This file maps each Virtue to its Kernel role, with the central asymmetry:

    塞 (sai) — ALONE among the 8 — is the ONLY mode that lands in 极 (extreme).
    All 7 others are 中-modes: they exhibit `dong s ≠ s`, the rhythm continues.

  This recovers the 心-tier vs. 道-tier distinction at the phenomenological layer:
    - 心-modes (yuan/shen/sai/ju): 心道 — subjective phases of motion
    - 道-modes (sheng/shou/xian/kai): 道-tier — structural / continuous / aesthetic

  Each mode also has a more refined "phase" reading: where in 動's rhythm it sits.
-/

import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Wen.Kernel

namespace SSBX.Foundation.Jian.JianModeKernel

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Wen.Kernel

/-! ## § 1 KernelRole — the 8 dynamical roles -/

/-- The 8 dynamical-layer roles, one per Virtue. -/
inductive KernelRole : Type
  | continuation   -- sheng (乾): 動 continues into next 中-state
  | reception      -- shou (坤): the receiving form; "next state from 動"
  | origin         -- yuan (震): the 元 / 几-trace initial motion
  | penetration    -- shen (巽): cause / 渗入 — depth into the orbit
  | extremity      -- sai (坎): 极 — fixed-point trap
  | manifestation  -- xian (离): 显/心 — heart's display
  | gathering      -- ju (艮): 聚/形 — form-completion
  | aesthetic      -- kai (兑): 开/美 — aesthetic opening
  deriving Repr, DecidableEq, BEq

/-! ## § 2 Virtue ↔ KernelRole bijection

  `kernelRole` defined inside `SSBX.Foundation.Yi.Yi.Virtue` for dot notation. -/

end SSBX.Foundation.Jian.JianModeKernel

namespace SSBX.Foundation.Yi.Yi.Virtue

open SSBX.Foundation.Jian.JianModeKernel (KernelRole)

/-- Each ontological mode's dynamical role. -/
def kernelRole : SSBX.Foundation.Yi.Yi.Virtue → KernelRole
  | .sheng => .continuation
  | .shou  => .reception
  | .yuan  => .origin
  | .shen  => .penetration
  | .sai   => .extremity
  | .xian  => .manifestation
  | .ju    => .gathering
  | .kai   => .aesthetic

end SSBX.Foundation.Yi.Yi.Virtue

namespace SSBX.Foundation.Jian.JianModeKernel

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Wen.Kernel

namespace KernelRole

/-- Inverse: each role's mode. -/
def virtue : KernelRole → Virtue
  | .continuation  => .sheng
  | .reception     => .shou
  | .origin        => .yuan
  | .penetration   => .shen
  | .extremity     => .sai
  | .manifestation => .xian
  | .gathering     => .ju
  | .aesthetic     => .kai

end KernelRole

/-- Bijection: Virtue ↔ KernelRole. -/
theorem mode_role_left_inverse (m : Virtue) :
    m.kernelRole.virtue = m := by cases m <;> rfl

theorem mode_role_right_inverse (r : KernelRole) :
    r.virtue.kernelRole = r := by cases r <;> rfl

/-! ## § 3 The asymmetry: 塞 IS 极, all else is 中

  This is the central content of the bridge: among 8 modes, exactly one
  (sai/塞) is the extremity-trap; the rest exhibit live motion. -/

/-- Predicate: this mode characterizes 极 (extremity) states. -/
def KernelRole.isExtreme : KernelRole → Bool
  | .extremity => true
  | _          => false

/-- Predicate: this mode characterizes 中 (middle) states. -/
def KernelRole.isMiddle : KernelRole → Bool
  | .extremity => false
  | _          => true

/-- 极 / 中 partition: every role is exactly one. -/
theorem role_partition (r : KernelRole) :
    r.isExtreme = !r.isMiddle := by cases r <;> rfl

/-- Only sai/塞 is extreme. -/
theorem only_sai_extreme (m : Virtue) :
    m.kernelRole.isExtreme = true ↔ m = .sai := by
  cases m <;> simp [Virtue.kernelRole, KernelRole.isExtreme]

/-- All non-sai modes are middle. -/
theorem non_sai_is_middle (m : Virtue) (h : m ≠ .sai) :
    m.kernelRole.isMiddle = true := by
  cases m <;> first | rfl | (exfalso; exact h rfl)

/-! ## § 4 Mode-characterizing predicates on Field

  Each mode characterizes a property on Kernel `Field` states. -/

/-- A state `s` is in the 塞-mode (sai) iff dong fails to escape it.
    塞 ≡ 极 (extremity = fixed-point). -/
def saiState (s : Field) : Prop := extreme s

/-- A state `s` is in the 续-mode (sheng) iff dong takes it elsewhere AND
    the destination is itself middle (so motion keeps unfolding). -/
def shengState (s : Field) : Prop := middle s ∧ middle (dong s)

/-- A state is in 元-mode (yuan) iff it equals `origin` (the 元 之 起点). -/
def yuanState (s : Field) : Prop := s = origin

/-- A state is in 受-mode (shou) iff it is a `dong`-image — received from prior. -/
def shouState (s : Field) : Prop := ∃ s', dong s' = s

/-- A state is in 显-mode (xian) iff there is a 心 (Xin) whose orbit passes through.
    Manifestation requires a heart-substrate to register. -/
def xianState (s : Field) : Prop := ∃ x : Xin, ∃ n : Nat, x.process.states n = s

/-- A state is in 渗-mode (shen) iff it lies along an orbit at any depth. -/
def shenState (s : Field) : Prop := ∃ (o : ZhongOrbit) (n : Nat), o.states n = s

/-- A state is in 聚-mode (ju) iff a 心-orbit gathers at it (occurs at some step). -/
def juState (s : Field) : Prop := ∃ x : Xin, ∃ n : Nat,
    x.process.states n = s ∧ middle s

/-- A state is in 开-mode (kai) iff it carries an aesthetic encounter for some 心. -/
def kaiState (s : Field) : Prop := ∃ (heart : ZhongOrbit) (n : Nat),
    aestheticEncounter heart s n

/-! ## § 5 Per-mode characterizing theorems

  Cross-link the Virtue atom to its Field predicate. -/

/-- 塞 (sai) characterizes extremity. -/
theorem sai_iff_extreme (s : Field) : saiState s ↔ extreme s := Iff.rfl

/-- 续 (sheng) implies 中. -/
theorem sheng_implies_middle (s : Field) (h : shengState s) : middle s := h.left

/-- 元 (yuan) at origin holds (origin IS the 元 之 起点). -/
theorem yuan_origin : yuanState origin := rfl

/-- 元 (yuan) state is 中 (origin is alive). -/
theorem yuan_implies_middle (s : Field) (h : yuanState s) : middle s := by
  rw [h]
  exact origin_is_middle

/-- Every state on a ZhongOrbit is in 渗-mode. -/
theorem orbit_state_is_shen (o : ZhongOrbit) (n : Nat) : shenState (o.states n) :=
  ⟨o, n, rfl⟩

/-- 渗 implies 中: every shen state is middle (orbit-states are middle). -/
theorem shen_implies_middle (s : Field) (h : shenState s) : middle s := by
  obtain ⟨o, n, hs⟩ := h
  rw [← hs]
  exact o.inMiddle n

/-- 聚 implies 中. -/
theorem ju_implies_middle (s : Field) (h : juState s) : middle s := by
  obtain ⟨_, _, _, hm⟩ := h
  exact hm

/-- 显 implies 中 (Xin-orbits are 中-orbits). -/
theorem xian_implies_middle (s : Field) (h : xianState s) : middle s := by
  obtain ⟨x, n, hs⟩ := h
  rw [← hs]
  exact x.process.inMiddle n

/-! ## § 6 The crucial disjointness — 塞 is incompatible with all 7 others

  Where 塞 holds, motion has ceased — none of the live modes can hold. -/

/-- 塞 and 续 are incompatible. -/
theorem sai_excludes_sheng (s : Field) : ¬ (saiState s ∧ shengState s) := by
  intro ⟨h_sai, h_sheng⟩
  exact h_sheng.left h_sai

/-- 塞 and 元 are incompatible (origin is alive). -/
theorem sai_excludes_yuan (s : Field) : ¬ (saiState s ∧ yuanState s) := by
  intro ⟨h_sai, h_yuan⟩
  rw [h_yuan] at h_sai
  exact origin_is_middle h_sai

/-- 塞 excludes 渗 (shen states are middle). -/
theorem sai_excludes_shen (s : Field) : ¬ (saiState s ∧ shenState s) := by
  intro ⟨h_sai, h_shen⟩
  exact (shen_implies_middle s h_shen) h_sai

/-- 塞 excludes 聚. -/
theorem sai_excludes_ju (s : Field) : ¬ (saiState s ∧ juState s) := by
  intro ⟨h_sai, h_ju⟩
  exact (ju_implies_middle s h_ju) h_sai

/-- 塞 excludes 显. -/
theorem sai_excludes_xian (s : Field) : ¬ (saiState s ∧ xianState s) := by
  intro ⟨h_sai, h_xian⟩
  exact (xian_implies_middle s h_xian) h_sai

/-! ## § 7 Trigram-level reading: V_4 group action on Virtue lifts to roles

  V_4 (cuo/zong/cuoZong/id) acts on Virtue (defined in Yi.lean §11).
  The action descends to KernelRole via the bijection. -/

namespace KernelRole

/-- 错 (cuo) on KernelRole — derived from Virtue.cuo via the bijection. -/
def cuo (r : KernelRole) : KernelRole := r.virtue.cuo.kernelRole

/-- 综 (zong) on KernelRole. -/
def zong (r : KernelRole) : KernelRole := r.virtue.zong.kernelRole

/-- 错 is involutive. -/
theorem cuo_cuo (r : KernelRole) : r.cuo.cuo = r := by
  cases r <;> rfl

/-- 综 is involutive. -/
theorem zong_zong (r : KernelRole) : r.zong.zong = r := by
  cases r <;> rfl

/-- 错 swaps extremity ↔ manifestation (sai ↔ xian; 塞 ↔ 显). -/
theorem cuo_extremity : (extremity).cuo = manifestation := rfl
theorem cuo_manifestation : (manifestation).cuo = extremity := rfl

end KernelRole

/-! ## § 8 Summary -/

/-- The bridge:
    8 Virtue atoms ↔ 8 KernelRole atoms (bijection)
    Among 8 modes, EXACTLY ONE (sai = 塞) characterizes 极
    The other 7 characterize various 中-properties (origin/orbit/heart/aesthetic)
    V_4 group action on Virtue descends to KernelRole. -/
theorem bridge_summary :
    -- Bijection
    (∀ m : Virtue, m.kernelRole.virtue = m) ∧
    (∀ r : KernelRole, r.virtue.kernelRole = r) ∧
    -- Exactly one extreme mode
    (∀ m : Virtue, m.kernelRole.isExtreme = true ↔ m = .sai) ∧
    -- 错 is involutive on KernelRole
    (∀ r : KernelRole, r.cuo.cuo = r) :=
  ⟨mode_role_left_inverse,
   mode_role_right_inverse,
   only_sai_extreme,
   KernelRole.cuo_cuo⟩

end SSBX.Foundation.Jian.JianModeKernel
