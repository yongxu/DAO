/-
信/诚 = alignment(化(T), 化(E)) + 反诛心五律
(Sincerity as T-E modal alignment, with five anti-conjecture invariants)

主旨形式化:

  T1 · 派生性:信/诚 不立新原语,由 (Trajectory + Bool 等 + 计数) 派生.
  T2 · graded(I-信-2):输出为 Alignment(matched/total),非 Bool 二判.
  T3 · 反诛心(I-信-1, I-信-4):metric 之类型签名仅取 PermittedModality(T, E),
       结构上排 B/R/M 之入参.
  T4 · 观察主权(I-信-3):由 ConsentedSincerity 之 consent_witness 担保.
  T5 · 高 alignment ≠ 真(I-信-5):存在反例(consistent liar 满 alignment 而持伪).
  T6 · 修之渐进:存在 alignment 单调 trajectory 渐近而不达 perfect.
  T7 · 失齐 ≠ 失败:Response 类型只有 `inquiry` 构造子,**无 `judgment`** —
       系统类型上不可输出 「P 不诚」 之判.
  T8 · 言行一致 ↔ 跨步 pointwise 相等:matchCount = n ↔ ∀ k < n, T k = E k.

合主定理 `sincerity_main_theorem` 一并陈之.

无 sorry · 无 axiom.

义理参考:
  JIAN Foundation Note v1.0 §IV.5 (信/诚)
    `/Users/ren/repos/interval/JIAN_FOUNDATION_NOTE_v1.0.md`
  生生不息论 · 补篇一·卷十·收(alignment 与礼)
  生生不息论 · 补篇二·十三(行仁要善)
配套形式化:
  Alignment.lean(本体层 alignment, ProcessAligned vs ContentAligned)
  EvolutionDao.lean(派生性同形:σ_F 派生于续能)
-/
import SSBX.Core
import SSBX.Foundation.Core.Alignment

namespace SSBX.Foundation.Core.Sincerity

open SSBX.Core.GammaProcess

/-! ## 1 · 模态 (Modalities) -/

/-- 五模态:言、行、体、处、向(《JIAN v1.0 §IV.5.4》). -/
inductive Modality where
  | T  -- 所言 (utterance)
  | E  -- 所行 (event)
  | B  -- 所体 (body)
  | R  -- 所处 (relational position)
  | M  -- 所向 (manifest tendency)
  deriving DecidableEq, Repr

/--
反诛心 type-level enforcement(I-信-1, I-信-4):
**许 metric 之模态——仅 T 与 E**.
B / R / M 不能构造此类型.
-/
inductive PermittedModality where
  | T
  | E
  deriving DecidableEq, Repr

namespace PermittedModality

/-- 嵌入到全模态. -/
def toModality : PermittedModality → Modality
  | .T => .T
  | .E => .E

/-- B、R、M 不在 PermittedModality 之像中. -/
theorem toModality_excludes_BRM (p : PermittedModality) :
    p.toModality ≠ .B ∧ p.toModality ≠ .R ∧ p.toModality ≠ .M := by
  cases p <;> exact ⟨by decide, by decide, by decide⟩

end PermittedModality

/-- 二值轨迹:Nat-索引时序之 Bool 观察. -/
abbrev Trajectory := Nat → Bool

/-! ## 2 · alignment 度量 -/

/-- alignment 量:matched/total ∈ [0, 1] 之有理表征. -/
structure Alignment where
  matched : Nat
  total : Nat
  bound : matched ≤ total
  deriving Repr

namespace Alignment

def perfect (n : Nat) : Alignment := ⟨n, n, Nat.le_refl n⟩

def empty (total : Nat) : Alignment := ⟨0, total, Nat.zero_le total⟩

end Alignment

/-! ## 3 · 信/诚 metric -/

/-- 累积匹配计数:于 [0, n) 步内 T、E 之逐点相等数. -/
def matchCount (T E : Trajectory) : Nat → Nat
  | 0 => 0
  | n + 1 => matchCount T E n + (if T n = E n then 1 else 0)

theorem matchCount_le (T E : Trajectory) (n : Nat) :
    matchCount T E n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    show matchCount T E k + (if T k = E k then 1 else 0) ≤ k + 1
    split <;> omega

theorem matchCount_eq_self (T : Trajectory) (n : Nat) :
    matchCount T T n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show matchCount T T k + (if T k = T k then 1 else 0) = k + 1
    rw [if_pos rfl, ih]

/--
信/诚 metric:**仅取 T、E 两 trajectory 与步数 n**.

**反诛心 type-level**:此函数签名只接 `Trajectory × Trajectory × Nat`,
无构造子使 B/R/M 入此函数.

**派生性 (T1)**:此 def 由 `matchCount`(由 Bool 等之计数)派生,
不立新原语.

**graded (T2)**:输出为 `Alignment`(matched/total),非 `Bool` 二判.
-/
def sincerity (T E : Trajectory) (n : Nat) : Alignment :=
  ⟨matchCount T E n, n, matchCount_le T E n⟩

/-! ## 4 · 反诛心五律 (Anti-conjecture-of-inner-state) -/

/--
**I-信-1 + I-信-4 (反诛心)**:

`sincerity` 之类型签名 `Trajectory → Trajectory → Nat → Alignment`
不接 B / R / M 模态.若有人欲将 B/R/M 经 `PermittedModality` 嵌入 metric,
其嵌入函数 `toModality` 之像不含 B/R/M(由 `toModality_excludes_BRM`).
-/
theorem sincerity_excludes_BRM (m : Modality) (hm : m = .B ∨ m = .R ∨ m = .M) :
    ¬ ∃ (p : PermittedModality), p.toModality = m := by
  rintro ⟨p, hp⟩
  rcases hm with rfl | rfl | rfl <;>
  cases p <;> simp [PermittedModality.toModality] at hp

/-- **I-信-2 (graded)**:输出之类型即 `Alignment`,非 `Bool`. -/
theorem sincerity_is_graded :
    ∀ T E n, (sincerity T E n).matched ≤ (sincerity T E n).total :=
  fun T E n => (sincerity T E n).bound

/-- 完全一致(T = E)蕴 perfect alignment. -/
theorem sincerity_perfect_when_eq (T : Trajectory) (n : Nat) :
    (sincerity T T n).matched = (sincerity T T n).total := by
  show matchCount T T n = n
  exact matchCount_eq_self T n

/--
**I-信-3 (观察主权)**:

`ConsentedSincerity` 之构造须提供 `consent_witness : agentConsented = true`,
即:无 P 之 consent,无可入此 metric 之合法构造.
-/
structure ConsentedSincerity where
  T : Trajectory
  E : Trajectory
  span : Nat
  agentConsented : Bool
  consent_witness : agentConsented = true

def consentedSincerity (cs : ConsentedSincerity) : Alignment :=
  sincerity cs.T cs.E cs.span

theorem consented_requires_witness (cs : ConsentedSincerity) :
    cs.agentConsented = true := cs.consent_witness

/--
**I-信-5 (高 alignment ≠ 真)**:

存在 `Trajectory` 对 (T, E) 与 `truth : Bool`,使 `sincerity T E n` 完美
而 T 持续与 truth 不合.即:T-E 之同步 (信/诚) 不蕴 T 之内容为真.

具体反例:**consistent liar** —— T = E = const false,
其 alignment 完美,然 T 之内容皆 false (与 truth = true 不合).
-/
theorem high_alignment_not_truth (n : Nat) :
    ∃ (T E : Trajectory) (truth : Bool),
      matchCount T E n = n ∧ ∀ t, T t ≠ truth := by
  refine ⟨fun _ => false, fun _ => false, true, ?_, ?_⟩
  · exact matchCount_eq_self _ n
  · intro _ h
    exact Bool.noConfusion h

/-! ## 5 · 失齐 ≠ 失败 -/

/--
系统响应类型:**只有 `inquiry` 构造子**,**无 `judgment`**.

此乃《JIAN v1.0 §IV.5.9》之核心:**低 alignment 之合法响应是询问而非判定**.

「我注意到你之前承诺与现在的行动之间有距离,是否需要重新约定?」
而非:「你失信了。」

类型层即排 「P 不诚」 之系统判.
-/
inductive SincerityResponse where
  | inquiry : Alignment → SincerityResponse

def respondToSincerity (a : Alignment) : SincerityResponse :=
  SincerityResponse.inquiry a

theorem response_is_only_inquiry :
    ∀ r : SincerityResponse, ∃ a, r = SincerityResponse.inquiry a := by
  intro r
  cases r with
  | inquiry a => exact ⟨a, rfl⟩

/-! ## 6 · 修之渐进 -/

/-- 修:alignment 之时间序列(《JIAN v1.0 §IV.5.6》). -/
abbrev CultivationTrajectory := Nat → Alignment

/--
修之渐进性:matched 单调非降,且每步皆**未达 perfect**.

形式上(《中庸》「自明诚」之 trajectory 解):
信/诚 是渐近极限,不必到——「完全验证 永不到达」.
-/
def IsAsymptotic (traj : CultivationTrajectory) : Prop :=
  (∀ n, (traj n).matched ≤ (traj (n+1)).matched) ∧
  (∀ n, (traj n).matched < (traj n).total)

/--
**T6 · 修可渐进**:存在修之轨迹,渐进而不达.

具体:traj n = ⟨n, n+1, _⟩.matched 升至 ∞ 而总未达 total.
-/
theorem cultivation_can_be_asymptotic :
    ∃ traj : CultivationTrajectory, IsAsymptotic traj := by
  refine ⟨fun n => ⟨n, n + 1, Nat.le_succ n⟩, ?_, ?_⟩
  · intro n
    show n ≤ n + 1
    exact Nat.le_succ n
  · intro n
    show n < n + 1
    exact Nat.lt_succ_self n

/-! ## 7 · 言行一致 ↔ pointwise 相等 -/

/--
**T8 · alignment 完美 ↔ 跨步 pointwise 相等**:

`matchCount T E n = n ↔ ∀ k < n, T k = E k`.

释:信/诚 完美乃 T-E 跨步 pointwise 一致——此即 「言行一致」 之精确陈述.
-/
theorem matchCount_eq_iff_pointwise (T E : Trajectory) (n : Nat) :
    matchCount T E n = n ↔ ∀ k, k < n → T k = E k := by
  induction n with
  | zero =>
    refine ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ k ih =>
    constructor
    · intro h j hj
      change matchCount T E k + (if T k = E k then 1 else 0) = k + 1 at h
      by_cases htk : T k = E k
      · rw [if_pos htk] at h
        have hk_eq : matchCount T E k = k := by omega
        by_cases h_eq : j = k
        · rw [h_eq]; exact htk
        · have hjk : j < k := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) h_eq
          exact (ih.mp hk_eq) j hjk
      · rw [if_neg htk] at h
        have := matchCount_le T E k
        omega
    · intro h
      change matchCount T E k + (if T k = E k then 1 else 0) = k + 1
      have hk : T k = E k := h k (Nat.lt_succ_self k)
      rw [if_pos hk]
      have hkeq : matchCount T E k = k :=
        ih.mpr (fun j hj => h j (Nat.lt_succ_of_lt hj))
      omega

/-- 言行一致 (Wen-Xing-Yi-Zhi) 之结构. -/
structure WenXingYiZhi where
  declaredActions : Trajectory  -- 化(T) — 言之时序
  actualActions : Trajectory    -- 化(E) — 行之时序
  consistent : ∀ t, declaredActions t = actualActions t

/-- 言行一致蕴任何步数下 sincerity perfect. -/
theorem wen_xing_yi_zhi_implies_perfect_sincerity (w : WenXingYiZhi) (n : Nat) :
    matchCount w.declaredActions w.actualActions n = n :=
  (matchCount_eq_iff_pointwise _ _ _).mpr (fun k _ => w.consistent k)

/-! ## 8 · 主定理 -/

/--
**主定理 · 信/诚 之形式**:

  (T1) 派生性:`sincerity` 是 def 不是公理(无新原语);
  (T2) graded:输出为 Alignment ≤ 关系,非 Bool 二判;
  (T3) 反诛心:B/R/M 类型上排;
  (T5) 高 alignment ≠ 真:反例存在;
  (T6) 修可渐进:存在不达 perfect 之 trajectory;
  (T7) 失齐 ≠ 失败:系统响应类型上只有询问.
-/
theorem sincerity_main_theorem :
    -- T2: graded
    (∀ T E n, (sincerity T E n).matched ≤ (sincerity T E n).total) ∧
    -- T3: 反诛心(B/R/M 排)
    (∀ (m : Modality), m = .B ∨ m = .R ∨ m = .M →
        ¬ ∃ (p : PermittedModality), p.toModality = m) ∧
    -- T5: 高 alignment ≠ 真
    (∀ n, ∃ (T E : Trajectory) (truth : Bool),
        matchCount T E n = n ∧ ∀ t, T t ≠ truth) ∧
    -- T6: 修可渐进
    (∃ traj : CultivationTrajectory, IsAsymptotic traj) ∧
    -- T7: 系统响应只有询问
    (∀ r : SincerityResponse, ∃ a, r = SincerityResponse.inquiry a) :=
  ⟨sincerity_is_graded,
    sincerity_excludes_BRM,
    high_alignment_not_truth,
    cultivation_can_be_asymptotic,
    response_is_only_inquiry⟩

end SSBX.Foundation.Core.Sincerity
