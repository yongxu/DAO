/-
# JianMode ↔ Kernel — ontological-mode mapping to dynamical kernel

  The 8 JianMode atoms (sheng/shou/yuan/shen/sai/xian/ju/kai) live in the
  ontological/phenomenological layer. The Kernel (Foundation/Kernel.lean) lives
  in the dynamical layer: 動 / 中 / 极 / 几 / orbits.

  This file maps each JianMode to its Kernel role, with the central asymmetry:

    塞 (sai) — ALONE among the 8 — is the ONLY mode that lands in 极 (terminus).
    All 7 others are 中-modes: they exhibit `motion s ≠ s`, the rhythm continues.

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

/-- The 8 dynamical-layer roles, one per JianMode. -/
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

/-! ## § 2 JianMode ↔ KernelRole bijection

  `kernelRole` defined inside `SSBX.Foundation.Yi.Yi.JianMode` for dot notation. -/

end SSBX.Foundation.Jian.JianModeKernel

namespace SSBX.Foundation.Yi.Yi.JianMode

open SSBX.Foundation.Jian.JianModeKernel (KernelRole)

/-- Each ontological mode's dynamical role. -/
def kernelRole : SSBX.Foundation.Yi.Yi.JianMode → KernelRole
  | .sheng => .continuation
  | .shou  => .reception
  | .yuan  => .origin
  | .shen  => .penetration
  | .sai   => .extremity
  | .xian  => .manifestation
  | .ju    => .gathering
  | .kai   => .aesthetic

end SSBX.Foundation.Yi.Yi.JianMode

namespace SSBX.Foundation.Jian.JianModeKernel

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Wen.Kernel

namespace KernelRole

/-- Inverse: each role's mode. -/
def jianMode : KernelRole → JianMode
  | .continuation  => .sheng
  | .reception     => .shou
  | .origin        => .yuan
  | .penetration   => .shen
  | .extremity     => .sai
  | .manifestation => .xian
  | .gathering     => .ju
  | .aesthetic     => .kai

end KernelRole

/-- Bijection: JianMode ↔ KernelRole. -/
theorem mode_role_left_inverse (m : JianMode) :
    m.kernelRole.jianMode = m := by cases m <;> rfl

theorem mode_role_right_inverse (r : KernelRole) :
    r.jianMode.kernelRole = r := by cases r <;> rfl

/-! ## § 3 The asymmetry: 塞 IS 极, all else is 中

  This is the central content of the bridge: among 8 modes, exactly one
  (sai/塞) is the extremity-trap; the rest exhibit live motion. -/

/-- Predicate: this mode characterizes 极 (extremity) states. -/
def KernelRole.isExtreme : KernelRole → Bool
  | .extremity => true
  | _          => false

/-- Predicate: this mode characterizes 中 (center) states. -/
def KernelRole.isMiddle : KernelRole → Bool
  | .extremity => false
  | _          => true

/-- 极 / 中 partition: every role is exactly one. -/
theorem role_partition (r : KernelRole) :
    r.isExtreme = !r.isMiddle := by cases r <;> rfl

/-- Only sai/塞 is terminus. -/
theorem only_sai_extreme (m : JianMode) :
    m.kernelRole.isExtreme = true ↔ m = .sai := by
  cases m <;> simp [JianMode.kernelRole, KernelRole.isExtreme]

/-- All non-sai modes are center. -/
theorem non_sai_is_middle (m : JianMode) (h : m ≠ .sai) :
    m.kernelRole.isMiddle = true := by
  cases m <;> first | rfl | (exfalso; exact h rfl)

/-! ## § 4 Mode-characterizing predicates on Field

  Each mode characterizes a property on Kernel `Field` states. -/

/-- A state `s` is in the 塞-mode (sai) iff motion fails to escape it.
    塞 ≡ 极 (extremity = fixed-point). -/
def saiState (s : Field) : Prop := terminus s

/-- A state `s` is in the 续-mode (sheng) iff motion takes it elsewhere AND
    the destination is itself center (so motion keeps unfolding). -/
def shengState (s : Field) : Prop := center s ∧ center (motion s)

/-- A state is in 元-mode (yuan) iff it equals `origin` (the 元 之 起点). -/
def yuanState (s : Field) : Prop := s = origin

/-- A state is in 受-mode (shou) iff it is a `motion`-image — received from prior. -/
def shouState (s : Field) : Prop := ∃ s', motion s' = s

/-- A state is in 显-mode (xian) iff there is a 心 (Xin) whose orbit passes through.
    Manifestation requires a heart-substrate to register. -/
def xianState (s : Field) : Prop := ∃ x : Xin, ∃ n : Nat, x.process.states n = s

/-- A state is in 渗-mode (shen) iff it lies along an orbit at any depth. -/
def shenState (s : Field) : Prop := ∃ (o : ZhongOrbit) (n : Nat), o.states n = s

/-- A state is in 聚-mode (ju) iff a 心-orbit gathers at it (occurs at some step). -/
def juState (s : Field) : Prop := ∃ x : Xin, ∃ n : Nat,
    x.process.states n = s ∧ center s

/-- A state is in 开-mode (kai) iff it carries an aesthetic encounter for some 心. -/
def kaiState (s : Field) : Prop := ∃ (heart : ZhongOrbit) (n : Nat),
    aestheticEncounter heart s n

/-! ## § 5 Per-mode characterizing theorems

  Cross-link the JianMode atom to its Field predicate. -/

/-- 塞 (sai) characterizes extremity. -/
theorem sai_iff_extreme (s : Field) : saiState s ↔ terminus s := Iff.rfl

/-- 续 (sheng) implies 中. -/
theorem sheng_implies_middle (s : Field) (h : shengState s) : center s := h.left

/-- 元 (yuan) at origin holds (origin IS the 元 之 起点). -/
theorem yuan_origin : yuanState origin := rfl

/-- 元 (yuan) state is 中 (origin is alive). -/
theorem yuan_implies_middle (s : Field) (h : yuanState s) : center s := by
  rw [h]
  exact origin_is_middle

/-- Every state on a ZhongOrbit is in 渗-mode. -/
theorem orbit_state_is_shen (o : ZhongOrbit) (n : Nat) : shenState (o.states n) :=
  ⟨o, n, rfl⟩

/-- 渗 implies 中: every shen state is center (orbit-states are center). -/
theorem shen_implies_middle (s : Field) (h : shenState s) : center s := by
  obtain ⟨o, n, hs⟩ := h
  rw [← hs]
  exact o.inMiddle n

/-- 聚 implies 中. -/
theorem ju_implies_middle (s : Field) (h : juState s) : center s := by
  obtain ⟨_, _, _, hm⟩ := h
  exact hm

/-- 显 implies 中 (Xin-orbits are 中-orbits). -/
theorem xian_implies_middle (s : Field) (h : xianState s) : center s := by
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

/-- 塞 excludes 渗 (shen states are center). -/
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

/-! ## § 7 Trigram-level reading: V_4 group action on JianMode lifts to roles

  V_4 (complement/reverse/complementReverse/id) acts on JianMode (defined in Yi.lean §11).
  The action descends to KernelRole via the bijection. -/

namespace KernelRole

/-- 错 (complement) on KernelRole — derived from JianMode.complement via the bijection. -/
def complement (r : KernelRole) : KernelRole := r.jianMode.complement.kernelRole

/-- 综 (reverse) on KernelRole. -/
def reverse (r : KernelRole) : KernelRole := r.jianMode.reverse.kernelRole

/-- 错 is involutive. -/
theorem complement_involutive (r : KernelRole) : r.complement.complement = r := by
  cases r <;> rfl

/-- 综 is involutive. -/
theorem reverse_involutive (r : KernelRole) : r.reverse.reverse = r := by
  cases r <;> rfl

/-- 错 swaps extremity ↔ manifestation (sai ↔ xian; 塞 ↔ 显). -/
theorem cuo_extremity : (extremity).complement = manifestation := rfl
theorem cuo_manifestation : (manifestation).complement = extremity := rfl

end KernelRole

/-! ## § 8 Summary -/

/-- The bridge:
    8 JianMode atoms ↔ 8 KernelRole atoms (bijection)
    Among 8 modes, EXACTLY ONE (sai = 塞) characterizes 极
    The other 7 characterize various 中-properties (origin/orbit/heart/aesthetic)
    V_4 group action on JianMode descends to KernelRole. -/
theorem bridge_summary :
    -- Bijection
    (∀ m : JianMode, m.kernelRole.jianMode = m) ∧
    (∀ r : KernelRole, r.jianMode.kernelRole = r) ∧
    -- Exactly one terminus mode
    (∀ m : JianMode, m.kernelRole.isExtreme = true ↔ m = .sai) ∧
    -- 错 is involutive on KernelRole
    (∀ r : KernelRole, r.complement.complement = r) :=
  ⟨mode_role_left_inverse,
   mode_role_right_inverse,
   only_sai_extreme,
   KernelRole.complement_involutive⟩

end SSBX.Foundation.Jian.JianModeKernel
