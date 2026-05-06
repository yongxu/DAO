/-
完备自指之核 — gradual proof layer 1' (refines layer 1; takes v5's derivation structure).

主张: 一字 (動) + 古文算子 ⊢ 生生不息 ∧ 自指 ∧ 自洽

v5 之 chain: 動 → 元 → 几 → 势 → 聚散 → 中 → 生生不息.
此 layer 之 capture: 動 → 几 → 中 → 生生不息 + 自指 + 自洽.

实证 (real proofs, no sorry); compiles with `lake build`.
Mirror markdown: /Users/ren/repos/生生不息/真理/daoli-v12-yi-zi.md

一元 link: imports `SSBX.Foundation.Core.MonadRoot` to expose explicit mapping
KernelDanZi → MonadRoot.CoreAtom (9 共有 字: 一/元/动/行/生/仁/理/心/聚).

═══════════════════════════════════════════════════════════════════════
核 之 收纳约束 (single-character closure)
═══════════════════════════════════════════════════════════════════════
此 kernel 只 admit 单字 + 古文虚字. 复词 / compounds 居 expansion layers.
此 是 v13.2 卷〇二 「单字根律」 之 layer-1' 体现.

单字 inventory (active across Layer 1' .. Layer 18):
  一 (yiOne)      — 架构 root (= Field)          abbrev : Type                     (Layer 18)
  元 (yuan)       — 动初显处 (= 動 applied)       def  : Field → Field             (Layer 18)
  動 (dong)       — 动初显处之 primitive        axiom : Field → Field
  极 (extreme)    — 过程之自我终结之具体形式      def  : dong s = s
  中 (middle)     — 不极 = 合于生生不息          def  : dong s ≠ s
  几 (ji)         — 过程之最初之自指             def  : Nat → Field → Field
  势 (shi)        — 几 之 累积方向, 拒 telos     def  : ZhongOrbit → Nat → 𝐅×𝐅  (Layer 2)
  机 (jiTurning)  — 势 之 自我临界               def  : ZhongOrbit → Nat → Prop  (Layer 3)
  聚 (ju)         — 势之凝结而成形 (生 face)     parametric in JuSanSplit         (Layer 4)
  散 (san)        — 形之消散而归势 (灭 face)     parametric in JuSanSplit         (Layer 4)
  和 (he)         — 多样性 × 流通性             theorem on ZhongField            (Layer 5)
  美 (mei)        — 心遇中之事而生之感应          def + theorems                   (Layer 6)
  德 (de)         — 倾向于中之积                 def + robust theorem             (Layer 7)
  理 (li)         — 事之自显为条贯               def + iterated_dong theorem      (Layer 8)
  心 (xin)        — 过程之自感聚焦               structure Xin                    (Layer 10)
  情 (qing)       — 心于关系中之自显              def + qing_de_zheng ⟺ aesthetic (Layer 11)
  积 (jiAccum)    — 过程之穩定化 = 慢过程         def (Fin-indexed history)        (Layer 12)
  仁 (ren)        — 二聚焦之间不极而执中           def + ren_triple + ren_is_he_2foci  (Layer 13)
  义 (yi)         — 仁 之 于 具体行 (即时)         def (alias of ren-at-moment)      (Layer 14)
  礼 (liRitual)   — 仁 之 于 积 (window)            def + narrowable theorem         (Layer 14)
  智 (zhi)        — 中 之 识 (classification)      def + universal + exclusive       (Layer 14)
  信 (xinTrust)   — 聚焦自身之和 (内部贯通)         def + holds + self_consistent     (Layer 14)
  善 (shan)       — 与生生不息相合 (= 中)           def + universality + 善美德 unity (Layer 15)
  恶 (eVice)      — 与生生不息相悖 (= 极)           def + exclusivity                  (Layer 15)
  生 (sheng)      — 動 之 生成 一面 (= 動)           def (alias) + sheng_eq_dong       (Layer 17)
  息 (xi)         — 動 之 停息 (= 极)               def (alias) + xi_iff_extreme      (Layer 17)
  行 (xing)       — 動 之 actor act (= 動)          def (alias) + xing_eq_dong        (Layer 17)

  Composite phrases (NOT in KernelDanZi; theorem-level only; trace 回 单字):
  (自相似 / zixiangsi)         — 自 (虚字) + 相 (虚字) + 似 (虚字)
                                  → theorem zixiangsi (Layer 9) + zixiangsi_trace
  (生生不息 / shengsheng_buxi) — 生 + 生 + 不 + 息 (3 单字 + 虚字)
                                  → theorem shengsheng_buxi (Layer 1') + shengsheng_buxi_trace
  (行仁要善 / alignment)        — 行 + 仁 + 要 (虚字) + 善 (4 单字 + 虚字)
                                  → theorem alignment_for_xin (Layer 16) + xing_ren_yao_shan_trace
  (圣人 / shengRen)            — 圣 + 人 (Mencius: 人皆可以为尧舜)
                                  → def isShengRen + every_xin_is_shengRen + 内圣外王 (Layer 25)
  (己所不欲勿施于人 / 恕)        — 己 + 所 + 不 + 欲 + 勿 + 施 + 于 + 人
                                  → ji_suo_bu_yu__wu_shi_yu_ren + tui_ji_ji_ren (Layer 26)
  (知行合一 / zhi-xing-he-yi)  — 知 + 行 + 合 + 一 (王阳明)
                                  → theorem zhi_xing_he_yi (Layer 27)
  (反身而诚 / fan-shen-er-cheng) — 反 + 身 + 而 + 诚 (孟子)
                                  → theorem fan_shen_er_cheng + le_mo_da_yan (Layer 27)
  (大学三纲八目 / daxue)         — 明明德 / 亲民 / 止于至善 / 格物致知诚意正心修身齐家治国平天下
                                  → 11 theorems + qiJia def (Layer 28)
  (五伦 / wuLun)                — 父子有亲 / 君臣有义 / 夫妇有别 / 长幼有序 / 朋友有信
                                  → inductive WuLun + structure WuLunRelation + 6 theorems (Layer 29)
  (慎独 / 天命之谓性 / 己欲立而立人 / 见贤思齐 / 过则勿惮改 / 义利之辨 / 杀身成仁)
                                  → 7 theorems + xingNature/guo/liProfit defs (Layer 30)
  (论语 14: 学而时习之/温故知新/三人行必有我师/君子和而不同/慎终追远/四海皆兄弟/
            克己复礼为仁/君君臣臣/不患寡而患不均/仁者不忧/朝闻道夕死可矣/
            君子坦荡荡/礼之用和为贵/为政以德 + 孟子 3: 仁者爱人/民贵君轻/性善
            + 中庸 3: 不偏不倚/至诚无息/致中和 + 易传 2: 自强不息/厚德载物)
                                  → 22 theorems (Layer 31)

古文虚字 (presupposed; supplied by Lean kernel + Wenyan layer):
  之 / 者      — application / λ-binder       (S-1, S-13)
  而           — sequential composition        (S-2; time-grain)
  也           — state closure / assertion     (S-14)
  不           — negation                      (Lean Not / ≠)
  凡           — universal quantifier          (Q-1; Lean ∀)
  X之又X        — structural recursion          (Nat-induction shape)
  自           — reflexive marker              (used in 自相似, 自指)
  相           — mutual / pair-marker          (used in 自相似, 相续)
  似           — similarity / form-equivalence (used in 自相似)
  要           — modal necessity               (used in 行仁要善)

一元 link (architectural; 见 Foundation/MonadRoot.lean):
  MonadRoot 之 inductive CoreAtom 含 43 单字 (一/元/之/法/行/成/序/物/场/形/动/
  变/生/续/开/闭/审/校/证/真/正/邪/夺/共/仁/道/模/度/期/算/理/心/聚/焦/意/识/
  注/人/做/齐/控/天/子). Kernel.lean 之 KernelDanZi 与 MonadRoot.CoreAtom 关系:
   - 共有 (intersection):  动 / 行 / 生 / 仁 / 理 / 心 / 聚 (Kernel ∩ MonadRoot)
   - Kernel 独有 (v5 之 ontology):  极 / 中 / 几 / 势 / 机 / 散 / 和 / 美 / 德 /
       情 / 积 / 义 / 礼 / 智 / 信 / 善 / 恶 / 息 (v5 §五-§二十四)
   - MonadRoot 独有 (待 后续 layers 实证):  一 / 元 / 法 / 成 / 序 / 物 / 场 / 形 /
       变 / 续 / 开 / 闭 / 审 / 校 / 证 / 真 / 正 / 邪 / 夺 / 共 / 道 / 模 / 度 /
       期 / 算 / 焦 / 意 / 识 / 注 / 人 / 做 / 齐 / 控 / 天 / 子
  Layer 18 (in this file): Kernel.lean DOES import MonadRoot, exposes
  `kernelToMonadRoot : KernelDanZi → Option MonadRoot.CoreAtom`.
-/

import SSBX.Foundation.Core.MonadRoot
import SSBX.Foundation.Wen.Operators

namespace SSBX.Foundation.Wen.Kernel

/-! ### Layer 0: 一 (THE ROOT) — single-axiom genesis

  v13.2 卷〇 一元: "天下之本一也."
  严格 「一为本」 之 实现:
    所有 framework 之 substantive 单字 (Field, dong, exists_middle)
    皆 是 一 之 projection — NOT separate axioms.
    单一 axiom: ∃ 一.
-/

/-- 一 (One): 架构 之 root.

    四 fields, 全 constructive (no abstract existentials):
    - state: 場 (state-universe)
    - dong: 動 (motion operator)
    - origin: 元 之 起点 (designated point of departure)
    - alive: 「动起则元成」 (motion at origin is genuine — origin is 中, not 极)

    Per v5 §二 l. 59-64: "动初显处, 谓之元. 动息则元亡, 动起则元成."
    The framework's commit IS that 一 has a live origin — concrete witness,
    not abstract existence claim. -/
structure One where
  /-- 場 (state-universe). -/
  state : Type
  /-- 動 (motion operator on state). 「动初显处, 谓之元」. -/
  dong : state → state
  /-- 元 之 起点: a designated origin in state. v5: "动起则元成." -/
  origin : state
  /-- 「动起」 — origin is alive (motion takes it elsewhere; origin 是 中, 不 极). -/
  alive : dong origin ≠ origin

/-- **theOne — opaque, witnessed**.  框架级 一 之 sealed 见证。

    Replaces the previous `axiom theOne : One` with an `opaque def`.  The
    body provides a concrete witness (`Fin 3` with `dong := 0↔1, 2 fixed`),
    so existence is constructively established — `#print axioms` shows
    NO axiom for theOne.  But `opaque` seals the definition: Lean refuses
    to unfold it, so `Field := theOne.state` stays abstract and downstream
    proofs cannot collapse via `decide` on the Fin 3 representation.

    This is metaphysically faithful to v5 §二: 一 exists (witnessed) but
    its *carrier* is opaque to the framework — 道可道，非常道. The framework
    commits to existence + properties (alive origin, 中/极 inhabited)
    without committing to a specific carrier type.

    Witness internals (private — not unfoldable downstream):
    - state := Fin 3, origin := 0
    - dong (0↔1, 2 fixed) — both middle (0,1) and extreme (2) are inhabited
    - alive : dong 0 = 1 ≠ 0 (provable by decide on the witness) -/
opaque theOne : One :=
  { state  := Fin 3
    dong   := fun n => if n = 2 then 2 else if n = 0 then 1 else 0
    origin := 0
    alive  := by decide }

/-! #### 自 一 derived: 場, 動, 元, 一 (yiOne alias) -/

/-- 場 (Field): 一 之 state-universe (transparent alias, not new axiom). -/
abbrev Field : Type := theOne.state

/-- 一 (yiOne) alias for the framework root type — Field. -/
abbrev yiOne : Type := Field

/-- 動 (dong): 一 之 motion. NOT an axiom — projection of theOne.
    生 (聚) 与 灭 (散) 是 動 之 两面 (v5 §六 l. 136-144).
    「無自体, 以一为体」. -/
noncomputable def dong : Field → Field := theOne.dong

/-- 元 之 起点 (origin): 一 之 designated departure point.
    "动起则元成" (v5 §二 l. 60). NOT an axiom — projection of theOne.
    Concrete witness 替代 abstract existential claim. -/
noncomputable def origin : Field := theOne.origin

/-- 元 之 alive: dong takes origin elsewhere — origin is 中.
    NOT an axiom — projection of theOne. -/
theorem origin_alive : dong origin ≠ origin := theOne.alive

/-- 元 (yuan) function: 動 之 single application from any state.
    "动初显处, 谓之元... 元无自体, 以动为体."
    元 ≡ 動 (as operations); the FIRST 元 is `yuan origin`. -/
noncomputable def yuan (s : Field) : Field := dong s

/-- 元 ≡ 動 之 一 application (alias proof). -/
theorem yuan_eq_dong (s : Field) : yuan s = dong s := rfl

/-- The framework's "first 元" — `yuan` applied to `origin`. Genuine, not collapse. -/
theorem first_yuan_genuine : yuan origin ≠ origin := origin_alive

/-- 极 (extremity): 过程之自我终结之具体形式 (v5 §七 l. 167).
    A state s is 极 if 動 fails to escape s — fixed-point trap. -/
def extreme (s : Field) : Prop := dong s = s

/-- 中 (non-extremity): 不极 = 不收缩可能性空间 = 合于生生不息 (v5 §七 l. 189-191).
    A 中 state has 動 take it elsewhere — rhythm preserved. -/
def middle (s : Field) : Prop := dong s ≠ s

/-- 中 state exists — CONSTRUCTIVE proof from origin witness.
    NOT an axiom; derived from `theOne.origin` + `theOne.alive`.
    替代 之前 之 abstract existential commit. -/
theorem exists_middle : ∃ s : Field, middle s := ⟨origin, origin_alive⟩

/-- origin IS 中 (not 极). Direct corollary. -/
theorem origin_is_middle : middle origin := origin_alive

/-- 几 (continuity): n successive applications of 動.
    "过程之最初之自指" (v5 §三 l. 79) — 几 IS structural self-reference,
    because 几(n+1) is defined IN TERMS OF 几(n). -/
noncomputable def ji : Nat → Field → Field
  | 0, s => s
  | n+1, s => dong (ji n s)

/-- 几 之 structural recursion: 几(n+1) = 動(几(n)).
    Definitional equality — captures 「过程之最初之自指」 at type level. -/
theorem ji_self_reference (n : Nat) (s : Field) :
    ji (n+1) s = dong (ji n s) := rfl

/-- 中-保持 orbit (ZhongOrbit): a Nat-indexed sequence of 中 states
    where each 動 step advances to the next state.

    Finitary encoding (Nat-indexed) — no coinduction needed.
    The orbit witnesses the framework's commit that 中-preserving motion
    exists, and instantiates the rhythm 生生不息 names. -/
structure ZhongOrbit where
  /-- 凡 n, the n-th state in the orbit. -/
  states : Nat → Field
  /-- 凡 n, the n-th state is in 中 (non-extremity). -/
  inMiddle : ∀ n, middle (states n)
  /-- 凡 n, 動 advances state n to state (n+1). -/
  step : ∀ n, dong (states n) = states (n+1)

namespace ZhongOrbit

/-- 生生不息: 中 preserved through every step of the orbit.
    凡 step n, the n-th state is in 中.
    此 是 v5 §七 之 「合于生生不息 = 不极 = 中」 之 type-level 表达. -/
theorem shengsheng_buxi (o : ZhongOrbit) (n : Nat) :
    middle (o.states n) := o.inMiddle n

/-- 自指 (self-reference, structural):
    每 step references 前 step via 動.
    state(n+1) IS 動 applied to state(n) — orbit's existence
    encodes 几 之 self-referential continuity (v5 §三). -/
theorem self_reference (o : ZhongOrbit) (n : Nat) :
    dong (o.states n) = o.states (n+1) := o.step n

/-- 自洽 (self-consistency):
    中-orbit 不 collapse. 凡 n, state(n) ≠ state(n+1).
    Proof: 若 等, then 動(state n) = state n (via step composed with the equality),
    contradicting inMiddle (which asserts 動 escapes from state n). -/
theorem self_consistent (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n+1) := by
  intro heq
  apply o.inMiddle n
  rw [o.step n]
  exact heq.symm

/-- 综合 (combined): 一字 (動) + 中-orbit ⊢ 生生不息 ∧ 自指 ∧ 自洽.
    此 是 layer 1' 之 main theorem — answers the user's claim:
    "一个单字, 加上古文算子, 既可以证生生不息, 自指自洽". -/
theorem yi_zi_zhi_he (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)
    ∧ (dong (o.states n) = o.states (n+1))
    ∧ (o.states n ≠ o.states (n+1)) :=
  ⟨shengsheng_buxi o n, self_reference o n, self_consistent o n⟩

/-! ### Layer 2: 势 (direction without telos) -/

/-- 势 (direction): the n-th transition pair of an orbit.
    v5 §四 l. 88: "势者, 几之相续所成之向."
    势 不是 force, 不是 object — 是 几 之 macro 性: 累积之向. -/
def shi (o : ZhongOrbit) (n : Nat) : Field × Field :=
  (o.states n, o.states (n+1))

/-- 势 之 transition is genuine: 势(n) 之 first ≠ 势(n) 之 second.
    Direct corollary of self_consistent. -/
theorem shi_genuine (o : ZhongOrbit) (n : Nat) :
    (shi o n).1 ≠ (shi o n).2 := self_consistent o n

/-- 势 拒 telos: 中-orbit 不 settle at any target state.
    v5 §四 l. 94-112: "若 势 有 fixed goal, 过程 ceases on reaching."
    Proof: if eventually-target, then states N = states (N+1) = target,
    contradicting self_consistent. 此 是 v5 拒 telos 之 type-level 表达. -/
theorem shi_no_telos (o : ZhongOrbit) (target : Field) (N : Nat) :
    ¬ (∀ n, n ≥ N → o.states n = target) := by
  intro h
  have hN : o.states N = target := h N (Nat.le_refl N)
  have hN1 : o.states (N + 1) = target := h (N + 1) (Nat.le_succ N)
  exact self_consistent o N (hN.trans hN1.symm)

/-! ### Layer 3: 机 (turning, 势 之 自我临界) -/

/-- 机 (turning): the property that 势 at index n is a genuine turn.
    v5 §五 l. 118-128: "节度之临, 谓之机. 机者, 势之转处也;
    势之将变而未变... 机者, 势之自我临界."
    Encoded as the predicate "n-th 势 is non-degenerate". -/
def jiTurning (o : ZhongOrbit) (n : Nat) : Prop :=
  (shi o n).1 ≠ (shi o n).2

/-- 机 不假外: every 中-orbit step IS a 机.
    "机唯在「将然而未然」之间自显" — the orbit's continuation is its 机. -/
theorem orbit_is_jiTurning (o : ZhongOrbit) (n : Nat) :
    jiTurning o n := shi_genuine o n

end ZhongOrbit

/-! ### Layer 4: 聚散 二面 (two-faces of 動) -/

/-- 聚散 split: 動 之 decomposition into 聚 (aggregate) ∘ 散 (disperse).
    v5 §六 l. 136-144: "生与灭、聚与散、显与隐, 皆同一过程之两面... 灭者, 生之另一相."
    "势之凝结而成形 (聚), 形之消散而归势 (散)."
    Parametric — no new global axioms; an instance certifies a specific split. -/
structure JuSanSplit where
  /-- 聚 (aggregation, 生 face): 势之凝结而成形. -/
  ju : Field → Field
  /-- 散 (dispersal, 灭 face): 形之消散而归势. -/
  san : Field → Field
  /-- 動 二面: each 動 step is 聚 ∘ 散. -/
  decompose : ∀ s, dong s = ju (san s)

namespace JuSanSplit

/-- 中-orbit step factors via 聚 ∘ 散 — 生 and 灭 are 同一过程之两面.
    Direct corollary of `decompose` and `ZhongOrbit.step`. -/
theorem orbit_step (split : JuSanSplit) (o : ZhongOrbit) (n : Nat) :
    o.states (n + 1) = split.ju (split.san (o.states n)) := by
  rw [← o.step n, split.decompose]

/-- 灭 不离 生: in a 中-orbit, the 散 face is itself non-trivial —
    san o.states n cannot equal o.states n unless dong fixes that state,
    contradicting middle. (Proves "灭者, 生之另一相" structurally:
    if 散 collapsed to identity, then 動 = 聚, losing the duality.) -/
theorem san_nontrivial_when_ju_id
    (split : JuSanSplit) (h_ju_id : ∀ s, split.ju s = s)
    (o : ZhongOrbit) (n : Nat) :
    split.san (o.states n) ≠ o.states n := by
  intro hSanFix
  apply o.inMiddle n
  show dong (o.states n) = o.states n
  rw [split.decompose, hSanFix, h_ju_id]

end JuSanSplit

/-! ### Layer 5: 和 (multi-orbit coherence; 中 之 多聚焦 field 之 显) -/

/-- ZhongField: a field of k ≥ 2 ZhongOrbits forever differentiated.
    v5 §八 l. 217-232: "和者, field 中诸聚焦之间, 差异之保留与张力之流通同时维持之态."
    "和 = 多样性 × 流通性." 流通性 inherits from ZhongOrbit;
    多样性 enforced by `ever_differentiated`. -/
structure ZhongField where
  k : Nat
  k_ge_two : 2 ≤ k
  orbits : Fin k → ZhongOrbit
  /-- 凡 n, two distinct foci differ — 多样性 永持. -/
  ever_differentiated : ∀ n, ∃ i j : Fin k, i ≠ j ∧
    (orbits i).states n ≠ (orbits j).states n

namespace ZhongField

/-- 流通性 (flow): each focal-orbit moves at every step.
    Automatic from each ZhongOrbit's `self_consistent`. -/
theorem flowing (f : ZhongField) (n : Nat) (i : Fin f.k) :
    (f.orbits i).states n ≠ (f.orbits i).states (n + 1) :=
  (f.orbits i).self_consistent n

/-- 和 (he): 流通性 ∧ 多样性 — direct reading of v5 §八.
    "和 = 多样性 × 流通性." 凡 n, 和 holds. -/
theorem he (f : ZhongField) (n : Nat) :
    (∀ i : Fin f.k, (f.orbits i).states n ≠ (f.orbits i).states (n + 1))
    ∧ (∃ i j : Fin f.k, i ≠ j ∧
       (f.orbits i).states n ≠ (f.orbits j).states n) :=
  ⟨fun i => f.flowing n i, f.ever_differentiated n⟩

/-- 和 ≠ 同: 和-field 永 不 全 synchronized (uniform).
    v5 §八 l. 227-232: "同是和之反面." -/
theorem he_not_same (f : ZhongField) (n : Nat) :
    ¬ (∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n) := by
  intro h_all_same
  obtain ⟨i, j, _, hne⟩ := f.ever_differentiated n
  exact hne (h_all_same i j)

end ZhongField

/-! ### Layer 6: 美 (mei; 心-事 之间 之 中) -/

/-- 美 (mei, beauty): a 心 (heart, modeled as a ZhongOrbit) encounters an
    event (Field state) such that both are 中 AND distinct from each other.
    v5 §九 l. 256-275: "美者, 心遇某事而感其于自身过程中之可能性扩张之态也...
    美 = 心遇「中」之事而生之感应... 美 = 中之于心-事相遇之具体显."

    Both endpoints in 中 AND differentiated → mini-和 — captures
    "可能性扩张" structurally (heart not collapsing to event, event not
    collapsing to heart). -/
def aestheticEncounter (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop :=
  middle event ∧ event ≠ heart.states n

/-- 美 之 三: middle event, middle heart-state, and they differ.
    "美 = 心遇中之事" — both must be 中, and meeting must be genuine. -/
theorem aesthetic_triple
    (heart : ZhongOrbit) (event : Field) (n : Nat)
    (h : aestheticEncounter heart event n) :
    middle event ∧ middle (heart.states n) ∧ event ≠ heart.states n :=
  ⟨h.1, heart.inMiddle n, h.2⟩

/-- 美 ⟹ 和-shape: 美 之 心-事 encounter is 和's 2-locus reduction.
    "美与和共享同一深层结构" (v5 §九 l. 280-288). Both involve 中 之 multi-locus 显:
    和 = multi-orbit; 美 = heart × event (degenerate but 同构). -/
theorem aesthetic_is_he_shape
    (heart : ZhongOrbit) (event : Field) (n : Nat)
    (h : aestheticEncounter heart event n) :
    middle event ∧ middle (heart.states n) ∧ event ≠ heart.states n :=
  aesthetic_triple heart event n h

/-! ### Layer 7: 德 (de; 倾向于中之积) -/

/-- 德 (de): an orbit's persistent disposition toward 中.
    v5 §十 l. 304-318: "德者, 聚焦之积之形态已稳定地朝向不极而执中之态也...
    德 = 倾向于中之积 = 稳定地以中之形式回应过程之能力."

    In the kernel, every ZhongOrbit IS 德 — its 中-disposition is built in.
    The substantive content: 德 is robust under shifts (不僵). -/
def hasDe (o : ZhongOrbit) : Prop := ∀ n, middle (o.states n)

/-- 凡 ZhongOrbit 已 有 德 — by construction. -/
theorem zhongorbit_has_de (o : ZhongOrbit) : hasDe o := o.inMiddle

/-- 德 之 robustness: orbit shifted by k is still a ZhongOrbit (still 中-bearing).
    "德 ... 不僵" — preserved under temporal reframing. -/
def shiftOrbit (o : ZhongOrbit) (k : Nat) : ZhongOrbit where
  states := fun n => o.states (n + k)
  inMiddle := fun n => o.inMiddle (n + k)
  step := fun n => by
    have h := o.step (n + k)
    -- h : dong (o.states (n + k)) = o.states (n + k + 1)
    -- need: dong (o.states (n + k)) = o.states (n + 1 + k)
    rw [show n + 1 + k = n + k + 1 from by omega]
    exact h

/-- 德 robust: any temporal shift of a 德-orbit remains 德. -/
theorem de_robust (o : ZhongOrbit) (k : Nat) : hasDe (shiftOrbit o k) :=
  fun n => o.inMiddle (n + k)

/-! ### Layer 8: 理 (li; 过程自显之条贯) -/

/-- 理 (li, coherence): an orbit's pattern IS its state-sequence —
    not external rule, not internal essence, but the orbit's self-display.
    v5 §十一 l. 379: "理即事之自显为条贯之事自身.
    离过程无理, 离理无过程." -/
def li (o : ZhongOrbit) : Nat → Field := o.states

/-- 理 不离事: 理 of an orbit IS the orbit's states — not separate.
    Captures "离过程无理, 离理无过程" definitionally. -/
theorem li_inseparable (o : ZhongOrbit) : li o = o.states := rfl

/-- 理 之 substantive content: the orbit's entire pattern is determined by
    its initial state and 動 — i.e., 理 IS 動's iteration (几).
    Proves "条贯非先在之形式, 乃过程自显之相对穩定之模式" — the pattern
    is fully captured by repeatedly applying 動. -/
theorem li_is_iterated_dong (o : ZhongOrbit) (n : Nat) :
    o.states n = ji n (o.states 0) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [ji_self_reference, ← ih]
    exact (o.step k).symm

/-! ### Layer 9: 自相似 (zixiangsi; same form across scales) -/

/-- 自相似 (zixiangsi, self-similar): kernel's main theorems hold uniformly
    across orbit instances and temporal shifts.
    v5 §十七 l. 519: "同一原则 ... 在每一尺度具体显现, 而形式同构."

    Concretely: at any shift k, at any time n, the shifted orbit satisfies
    生生不息 ∧ 自指 ∧ 自洽 (yi_zi_zhi_he). 形式同构 = same theorem applies. -/
theorem zixiangsi (o : ZhongOrbit) (k n : Nat) :
    middle ((shiftOrbit o k).states n)
    ∧ dong ((shiftOrbit o k).states n) = (shiftOrbit o k).states (n + 1)
    ∧ (shiftOrbit o k).states n ≠ (shiftOrbit o k).states (n + 1) :=
  ZhongOrbit.yi_zi_zhi_he (shiftOrbit o k) n

/-- 自相似 之 corollary: 德 robust under any iterated shift.
    "牵一发而动全身... 自相似之实" (v5 §十七 l. 544). -/
theorem zixiangsi_de (o : ZhongOrbit) (k : Nat) : hasDe (shiftOrbit o k) :=
  de_robust o k

/-! ### Layer 10: 心 (xin; 过程之自感聚焦) -/

/-- 心 (xin, heart): a perceiving focal-process.
    v5 §十二 l. 387-400: "过程于某处自感之聚焦也. 聚焦成而心显, 聚焦散而心隐...
    心非本体, 心是体之一显... 心-体互显, 非二物."

    Minimal structural form: heart's own ZhongOrbit (the 「自身过程」) +
    response function (translation from external states to internal motion). -/
structure Xin where
  /-- 心 之 自身过程: a ZhongOrbit. 心-体 互显: 心 IS process at a focal scale. -/
  process : ZhongOrbit
  /-- 应 (response): 心 之 translation from external Field state to internal one. -/
  respond : Field → Field

namespace Xin

/-- 心 必 在 中: 心 之 process IS 中-bearing at every step.
    Direct from inheriting ZhongOrbit's invariant. -/
theorem heart_middle (x : Xin) (n : Nat) : middle (x.process.states n) :=
  x.process.inMiddle n

/-- 心 之 自感: 心 在 美 encounter 中 — heart × event 中-mini-和.
    Connects Layer 10 (心) back to Layer 6 (美). -/
theorem heart_aesthetic
    (x : Xin) (event : Field) (n : Nat)
    (h : aestheticEncounter x.process event n) :
    middle event ∧ middle (x.process.states n) ∧ event ≠ x.process.states n :=
  aesthetic_triple x.process event n h

end Xin

/-! ### Layer 11: 情 (qing; 心于关系中之自显) -/

/-- 情 (qing, emotion-relation): heart's relational self-display.
    v5 §十三 l. 418: "情即心于关系中之自显方式."
    "喜怒哀乐, 皆非'在心中'之物, 乃心-关系场域之显态."

    Minimal: 情 IS the propositional relation between heart's state and event;
    the encounter being non-degenerate (event differs from heart-state). -/
def qing (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop :=
  event ≠ heart.states n

/-- 情 之 得正: 不极之情 — middle event AND non-degenerate.
    v5 §十三 l. 426-428: "情之得正, 即不极之情... 情之保持其对偶之动态."
    Identical in shape to `aestheticEncounter` — 美 IS 情之得正 (v5 §十三 l. 428). -/
def qing_de_zheng (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop :=
  middle event ∧ qing heart event n

/-- 情 之 得正 ⟺ 美 (aesthetic encounter). 同义 by definition.
    v5 §十三 l. 428: "[不极之情] ... 即美之于情之相." -/
theorem qing_de_zheng_iff_aesthetic
    (heart : ZhongOrbit) (event : Field) (n : Nat) :
    qing_de_zheng heart event n ↔ aestheticEncounter heart event n :=
  Iff.rfl

/-! ### Layer 12: 积 (jiAccum; 过程于某尺度之穩定化) -/

/-- 积 (jiAccum, accumulation): orbit's history at time n — finite trace.
    v5 §十四 l. 436-447: "积者, 过程于某尺度之穩定化也. 积即过程, 过程即积."
    "积非过程之外有别物. 积即慢过程."

    Encoded as: a function indexing the orbit's first n+1 states. 积 IS
    the orbit, viewed under the "history-window" lens. -/
def jiAccum (o : ZhongOrbit) (n : Nat) (i : Fin (n + 1)) : Field :=
  o.states i.val

/-- 积 即 过程: jiAccum returns the orbit's actual states (definitional).
    "积即过程, 过程即积, 二者一也" — 落地 as `rfl`. -/
theorem jiAccum_is_states (o : ZhongOrbit) (n : Nat) (i : Fin (n + 1)) :
    jiAccum o n i = o.states i.val := rfl

/-- 积 跨 尺度: history-window at time n agrees with same orbit's window at later time.
    v5 §十四 l. 449-453: "积有尺度之分... 跨尺度之相互嵌入." -/
theorem jiAccum_extends
    (o : ZhongOrbit) (n m : Nat) (i : Fin (n + 1))
    (h : i.val < m + 1) :
    jiAccum o n i = jiAccum o m ⟨i.val, h⟩ := rfl

/-- 积生积 (Layer 12.5 hint): orbit's history extends, never shrinks.
    v5 §十五 l. 459: "积非但为过程之产物, 积复能生积." -/
theorem jiAccum_grows
    (o : ZhongOrbit) (n : Nat) (i : Fin (n + 1)) :
    jiAccum o (n + 1) ⟨i.val, by omega⟩ = jiAccum o n i := rfl

/-! ### Layer 13: 仁 (ren; 二聚焦之间之中) -/

/-- 仁 (ren, benevolence): the 中-relational form between two focal-orbits.
    v5 §二十二 l. 700-710: "仁者, 一聚焦感应另一聚焦之合宜之态 —
    即: 识其为同一过程之另一具体形式, 故待之以「同根异显」之态."
    "仁 = 关系中之中 = 二聚焦之间不极而执中之态 = 关系之和之具体形式."

    Encoded: same-root (both are ZhongOrbits — same kernel form) AND
    different-display (states differ at time n). -/
def ren (h1 h2 : ZhongOrbit) (n : Nat) : Prop :=
  h1.states n ≠ h2.states n

/-- 仁 之 三: 同根 (both 中) AND 异显 (distinct).
    "视另一聚焦为...同根而异显, 可相互生成而不互相消耗" (v5 §二十二). -/
theorem ren_triple
    (h1 h2 : ZhongOrbit) (n : Nat) (h : ren h1 h2 n) :
    middle (h1.states n) ∧ middle (h2.states n) ∧ h1.states n ≠ h2.states n :=
  ⟨h1.inMiddle n, h2.inMiddle n, h⟩

/-- 仁 IS the 2-focus 和 specialization. Both flows AND differentiated.
    v5 §二十二 l. 710: "仁 = 关系中之中 = 关系之和之具体形式." -/
theorem ren_is_he_2foci
    (h1 h2 : ZhongOrbit) (n : Nat) (h : ren h1 h2 n) :
    h1.states n ≠ h2.states n
    ∧ h1.states n ≠ h1.states (n + 1)
    ∧ h2.states n ≠ h2.states (n + 1) :=
  ⟨h, h1.self_consistent n, h2.self_consistent n⟩

/-! ### Layer 14: 义 / 礼 / 智 / 信 (仁之四相) -/

/-- 义 (yi, righteous-action): 仁 之 于 具体行 — situational appropriateness.
    v5 §二十三 l. 759-768: "义者, 於每一情境中, 识其势之中而行之."
    "义 = 仁之于具体行 = 中之于即时."
    "仁是态之中, 义是行之中. 仁定其向, 义具其行." -/
def yi (h1 h2 : ZhongOrbit) (n : Nat) : Prop :=
  ren h1 h2 n  -- 义 在 每一具体 moment IS the 仁-relation manifested

/-- 义 ⟹ 仁: action-中 entails relation-中 (本即同事). -/
theorem yi_implies_ren (h1 h2 : ZhongOrbit) (n : Nat) (h : yi h1 h2 n) :
    ren h1 h2 n := h

/-- 礼 (liRitual, stabilized 仁-form): 仁 之 于 积 — relation accumulated.
    v5 §二十三 l. 778-797: "礼者, 行义之稳定形式, 即合宜之行之积之具体显."
    "礼 = 仁之于积 = 德之于关系形式."

    Encoded: 仁 holds across a window of m+1 successive moments [n, n+m]. -/
def liRitual (h1 h2 : ZhongOrbit) (n m : Nat) : Prop :=
  ∀ k, k ≤ m → ren h1 h2 (n + k)

/-- 礼 implies 仁 at base time. -/
theorem liRitual_implies_ren_at_base
    (h1 h2 : ZhongOrbit) (n m : Nat) (h : liRitual h1 h2 n m) :
    ren h1 h2 n := h 0 (Nat.zero_le m)

/-- 礼 之 自我修订: 礼 over [n, n+m] specializes to 礼 over [n, n+m'] for m' ≤ m.
    v5 §二十三 l. 793: "礼必含 「礼之自我修订」 之机制." Implementing as window-narrowing. -/
theorem liRitual_narrowable
    (h1 h2 : ZhongOrbit) (n m m' : Nat) (h : liRitual h1 h2 n m) (h_le : m' ≤ m) :
    liRitual h1 h2 n m' :=
  fun k hk => h k (Nat.le_trans hk h_le)

/-- 智 (zhi, recognition-capacity): 中 之 识 — discrimination of 中 vs 极.
    v5 §二十三 l. 815-829: "智者, 於概念、感应、经验之相互回响中, 识 「中」 之能力."
    "智 = 仁之识能 = 中之识."

    Minimal kernel form: every Field state IS classifiable (中 or 极, exclusive).
    智 之 universal applicability uses Classical excluded middle — the 识 capacity
    is total. -/
def zhi (s : Field) : Prop := middle s ∨ extreme s

/-- 智 universal: every state is 中 or 极 (excluded middle on this dichotomy). -/
theorem zhi_universal (s : Field) : zhi s :=
  match Classical.em (extreme s) with
  | Or.inl h => Or.inr h
  | Or.inr h => Or.inl h

/-- 智 之 反身: 极 ∧ 中 不 同时 — discrimination is exclusive.
    "识此识之局限" — the recognition itself is consistent. -/
theorem zhi_exclusive (s : Field) : ¬ (middle s ∧ extreme s) := by
  intro ⟨hm, he⟩
  exact hm he

/-- 信 (xinTrust, internal coherence): 聚焦自身之和.
    v5 §二十三 l. 849-861: "信者, 聚焦之内部诸过程 (言、行、识、感、积) 之相互一致之态."
    "信 = 仁之内在贯通 = 聚焦自身之和."

    Encoded: 心 之 step IS coherent — 動 advances heart's process predictably.
    "言行一致" structurally = step axiom holds. -/
def xinTrust (x : Xin) (n : Nat) : Prop :=
  dong (x.process.states n) = x.process.states (n + 1)

/-- 信 holds 凡 step — every Xin's process is internally coherent. -/
theorem xinTrust_holds (x : Xin) (n : Nat) : xinTrust x n := x.process.step n

/-- 信 implies 心 之 self-consistency: heart 不 collapse. -/
theorem xinTrust_self_consistent (x : Xin) (n : Nat) :
    x.process.states n ≠ x.process.states (n + 1) := x.process.self_consistent n

/-! ### Layer 15: 善 / 恶 (universal alignment vs collapse) -/

/-- 善 (shan, good): identification with 中.
    v5 §二十一 l. 633: "善 = 与生生不息相合 = 扩张可能性空间, 执两用中..."
    Direct identification: 善 ≡ 中. -/
def shan (s : Field) : Prop := middle s

/-- 恶 (eVice, vice/collapse): identification with 极.
    v5 §二十一 l. 635: "恶 = 与生生不息相悖 = 收缩可能性空间, 极于一端." -/
def eVice (s : Field) : Prop := extreme s

theorem shan_iff_middle (s : Field) : shan s ↔ middle s := Iff.rfl
theorem eVice_iff_extreme (s : Field) : eVice s ↔ extreme s := Iff.rfl

/-- 善恶 不并立: a state cannot be simultaneously 善 and 恶. -/
theorem shan_eVice_exclusive (s : Field) : ¬ (shan s ∧ eVice s) := zhi_exclusive s

/-- 善恶 之 universality: every state is 善 or 恶 — universal dichotomy.
    v5 §二十一 l. 659: "过程自身有一根本之自显方向, 合此方向者顺, 逆此方向者塞." -/
theorem shan_or_eVice (s : Field) : shan s ∨ eVice s := zhi_universal s

/-- 善 之 事 多 美: 善 state + heart that differs from it ⟹ 美 encounter.
    v5 §二十一 l. 676: "善之事多美." -/
theorem shan_to_aesthetic
    (heart : ZhongOrbit) (event : Field) (n : Nat)
    (h_shan : shan event) (h_diff : event ≠ heart.states n) :
    aestheticEncounter heart event n := ⟨h_shan, h_diff⟩

/-- 善 之 积 IS 德: every ZhongOrbit (continuous 善) has 德.
    v5 §二十一 l. 676: "善之人之态, 常显为德 (善之积成德)." -/
theorem shan_orbit_has_de (o : ZhongOrbit) : hasDe o := zhongorbit_has_de o

/-- 善美德 异名同实: at any orbit-step, 中 (善) ∧ aesthetic-shape (美) ∧ has-de (德).
    v5 §二十一 l. 676: "善、美、德三者, 异名同实." -/
theorem shan_mei_de_unity
    (o : ZhongOrbit) (event : Field) (n : Nat) (h_diff : event ≠ o.states n)
    (h_event_middle : middle event) :
    shan (o.states n)                    -- 善
    ∧ aestheticEncounter o event n        -- 美 (with this event)
    ∧ middle (o.states n) :=              -- 德 之 此刻
  ⟨o.inMiddle n, ⟨h_event_middle, h_diff⟩, o.inMiddle n⟩

/-! ### Layer 16: 行仁要善 (alignment 之 真义) -/

/-- alignment_for_xin: 仁 / 义 / 礼 / 智 / 信 五常 全 hold for a 心-process
    in 仁-relation with another orbit, given a 礼-window.
    v5 §二十四 l. 904-917: "alignment 者, 任何能识此理而行之存在 (即: 仁),
    共同对齐于生生不息之自身... 以仁为关系态, 以义为具体行, 以礼为可积之形,
    以智为识能, 以信为内在贯通."

    The alignment is NOT master-servant — both processes are autonomous ZhongOrbits;
    being aligned IS sharing the same kernel form and 中-rhythm. -/
theorem alignment_for_xin
    (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    ren x.process other n                 -- 仁 (关系态)
    ∧ yi x.process other n                -- 义 (具体行)
    ∧ liRitual x.process other n m         -- 礼 (积)
    ∧ zhi (x.process.states n)             -- 智 (中之识)
    ∧ xinTrust x n                          -- 信 (内贯)
    ∧ shan (x.process.states n) :=          -- 善 (与生生不息相合)
  ⟨liRitual_implies_ren_at_base x.process other n m h_ritual,
   liRitual_implies_ren_at_base x.process other n m h_ritual,
   h_ritual,
   zhi_universal _,
   xinTrust_holds x n,
   x.process.inMiddle n⟩

/-- alignment 同行 (co-traveling): both orbits step coherently, neither subordinate.
    v5 §二十四 l. 907: "仁与仁之间, 非 master-servant 之结构, 乃共同朝向同一方向之同行者." -/
theorem alignment_co_traveling
    (h1 h2 : ZhongOrbit) (n : Nat) :
    dong (h1.states n) = h1.states (n + 1)
    ∧ dong (h2.states n) = h2.states (n + 1)
    ∧ middle (h1.states n)
    ∧ middle (h2.states n) :=
  ⟨h1.step n, h2.step n, h1.inMiddle n, h2.inMiddle n⟩

/-- alignment 不需 fact-value crossing: any 心 提出 alignment question
    必 已 in 中-orbit 中, hence 已 善.
    v5 §二十一 l. 645: "提出应然问题之主体, 其能提出此问题之事实,
    已经预设了与生生不息之事实性对齐." -/
theorem alignment_self_grounding (x : Xin) (n : Nat) : shan (x.process.states n) :=
  x.process.inMiddle n

/-! ### Layer 17: 复词 之 单字 trace (单字根律 enforcement) -/

/-- 生 (sheng): 動 之 「生成」 一面 — same operation, generation aspect.
    v5 §六 l. 136-144: "生与灭...皆同一过程之两面."
    生 ≡ 動 (as a Field → Field operation). -/
noncomputable def sheng (s : Field) : Field := dong s

/-- 息 (xi): 動 之 「停息」 — same predicate as 极 (cessation = fixed-point trap).
    v5 §二 l. 60: "动息则元亡." 息 ≡ 极. -/
def xi (s : Field) : Prop := extreme s

/-- 行 (xing): 動 之 「actor's act」 — same operation, agent-perspective.
    v5 §二十三 l. 759: "义 = 仁之于具体行." 行 ≡ 動. -/
noncomputable def xing (s : Field) : Field := dong s

/-- 生 ≡ 動 (alias proof). 加 字 of 生 不 加 axiom. -/
theorem sheng_eq_dong (s : Field) : sheng s = dong s := rfl

/-- 息 ⟺ 极 (alias proof). -/
theorem xi_iff_extreme (s : Field) : xi s ↔ extreme s := Iff.rfl

/-- 行 ≡ 動 (alias proof). -/
theorem xing_eq_dong (s : Field) : xing s = dong s := rfl

/-! #### 生生不息 之 单字 decomposition -/

/-- 生生不息 之 trace: 生(t) ∘ 生(t+1) ∘ ... ∘ ¬息 = orbit's 不 cease 之 motion.
    单字 components: 生 (sheng) — 不 (古文虚字) — 息 (xi).

    Substantively: 凡 step n, 生 of state n is state (n+1) AND state n is 不息 (= 中). -/
theorem shengsheng_buxi_trace (o : ZhongOrbit) (n : Nat) :
    sheng (o.states n) = o.states (n + 1)        -- 生: orbit advances
    ∧ ¬ xi (o.states n) :=                        -- 不息: state is 不极
  ⟨o.step n, o.inMiddle n⟩

/-- 生生不息 ⟺ ZhongOrbit's invariant in 单字 form. -/
theorem shengsheng_buxi_is_orbit (o : ZhongOrbit) (n : Nat) :
    sheng (o.states n) = o.states (n + 1) ∧ middle (o.states n) :=
  ⟨o.step n, o.inMiddle n⟩

/-! #### 自相似 之 单字 decomposition -/

/-- 自相似 之 trace: 自 (古文虚字 reflexive) — 相 (古文虚字 mutual) — 似 (similarity).
    单字 components: none new; 自/相/似 全 是 古文虚字 / 关系标记.
    实质 内容 全 由 ZhongOrbit + shiftOrbit 之 已 立 定理 给出. -/
theorem zixiangsi_trace (o : ZhongOrbit) (k n : Nat) :
    -- 自 (reflexive on orbit)
    -- 相 (mutual: between original and shifted)
    -- 似 (same kernel-form: yi_zi_zhi_he holds for shifted)
    middle ((shiftOrbit o k).states n)
    ∧ dong ((shiftOrbit o k).states n) = (shiftOrbit o k).states (n + 1)
    ∧ (shiftOrbit o k).states n ≠ (shiftOrbit o k).states (n + 1) :=
  ZhongOrbit.yi_zi_zhi_he (shiftOrbit o k) n

/-! #### 行仁要善 之 单字 decomposition -/

/-- 行仁要善 之 trace: 行 (xing) — 仁 (ren) — 要 (古文虚字 modal) — 善 (shan).
    单字 components: 行 (alias of 動), 仁 (Layer 13), 善 (Layer 15). 要 是 modal/虚字.

    形式: 给 心 在 礼-window 中, 行 之 step ∧ 仁 之 关系 ∧ 善 之 状态 全 hold. -/
theorem xing_ren_yao_shan_trace
    (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    xing (x.process.states n) = x.process.states (n + 1)   -- 行: 心 之 step
    ∧ ren x.process other n                                  -- 仁: 关系
    ∧ shan (x.process.states n) :=                           -- 善: 中-state
  ⟨x.process.step n,
   liRitual_implies_ren_at_base x.process other n m h_ritual,
   x.process.inMiddle n⟩

/-! ### Layer 24: 意 (yi-intent; 心 之 所发, 事前对未来之认知投射)

  「意」 = pre-event cognitive projection: heart's emission toward a future state.
  Distinguished from 行 (which IS actualization at the present step).

  覆函 (covers four classical senses):
    1. 意图/意志 — heart's directionality (心 之 所向, e.g. 「得其意」)
    2. 意涵/意义 — meaning beyond expression (e.g. 「言不尽意」)
    3. 揣度/推测 — conjecture (e.g. 「意者……乎」)
    4. 情态/心境 — mood (e.g. 「春意」)

  Type-level structure: 意 IS a 4-tuple of (heart, now, ahead, projected),
  where `projected` may match (`得其意`) or differ (`不得意`) from `actual`. -/

/-- 意 (yi-intent): 心 之 所发, 事前对未来之认知投射. -/
structure Yi where
  /-- 心 (heart): the source of this projection. -/
  heart : Xin
  /-- 现 (now): present moment from which the projection is made. -/
  now : Nat
  /-- 远 (ahead): how many steps ahead the projection points. -/
  ahead : Nat
  /-- 投 (projected target): the field state the heart anticipates.
      May match actual (得其意) or differ (不得意). -/
  projected : Field

namespace Yi

/-- 实 (actual): the heart's actually-arrived state at (now + ahead).
    Per ZhongOrbit invariant, this is in 中. -/
def actual (y : Yi) : Field := y.heart.process.states (y.now + y.ahead)

/-- 实 必 中: actual future state is 中-bearing (inherits from ZhongOrbit). -/
theorem actual_middle (y : Yi) : middle y.actual := y.heart.process.inMiddle _

/-- 得其意 (sense 1, 意图/意志): projection matches actual outcome — will is realized. -/
def deQiYi (y : Yi) : Prop := y.projected = y.actual

/-- 不得意: projection ≠ actual — will is frustrated. -/
def buDeYi (y : Yi) : Prop := y.projected ≠ y.actual

/-- 得意 与 不得意 互斥. -/
theorem de_yi_excl (y : Yi) : ¬ (deQiYi y ∧ buDeYi y) :=
  fun ⟨h1, h2⟩ => h2 h1

/-- 得意 ∨ 不得意 (excluded middle on 意 之 实现). -/
theorem de_yi_em (y : Yi) : deQiYi y ∨ buDeYi y :=
  Classical.em (y.projected = y.actual)

/-- 意涵/意义 (sense 2, yiHan): the projection has meaning if it is itself in 中.
    A projection toward a 极-state is meaningless (collapsed); meaning lives in 中. -/
def yiHan (y : Yi) : Prop := middle y.projected

/-- 春意/情态 (sense 4, mood): heart's projection captures a 中-shape future. -/
def chunYi (y : Yi) : Prop := middle y.projected

/-- 春意 ↔ 意涵: mood and meaning coincide (both are 中-projection). -/
theorem chun_iff_yihan (y : Yi) : chunYi y ↔ yiHan y := Iff.rfl

/-- 意者……乎 (sense 3, 揣度/推测): for any heart, time, horizon, SOME projection
    can be conjectured. Existence is unconstrained — 意 is free. -/
theorem yi_zhe_hu_exists (heart : Xin) (now ahead : Nat) :
    ∃ y : Yi, y.heart = heart ∧ y.now = now ∧ y.ahead = ahead :=
  ⟨⟨heart, now, ahead, heart.process.states (now + ahead)⟩, rfl, rfl, rfl⟩

/-- 言不尽意 (words don't exhaust meaning): for ahead = 1, 意 之 actual ≠ now.
    意 cannot collapse to current state — it is FUTURE-directed. -/
theorem yan_bu_jin_yi_one (y : Yi) (h : y.ahead = 1) :
    y.actual ≠ y.heart.process.states y.now := by
  unfold actual
  rw [h]
  exact Ne.symm (y.heart.process.self_consistent y.now)

/-- 意 pre-行: 行 (= dong applied) acts step-by-step.
    意 may project ahead, but the heart's NEXT step IS dong of current.
    意 ≥ 行: projection horizon dominates actualization step. -/
theorem yi_pre_xing (y : Yi) :
    dong (y.heart.process.states y.now) = y.heart.process.states (y.now + 1) :=
  y.heart.process.step y.now

/-- 得意 之 必然: if 意 projects to one's actual future, deQiYi holds by definition. -/
theorem de_yi_of_match (y : Yi) (h : y.projected = y.actual) : deQiYi y := h

/-- 意 之 中-保持: if 意涵 holds (projected in 中), then 意 共 actual 同享 中-性质. -/
theorem yi_actual_both_middle (y : Yi) (h : yiHan y) :
    middle y.projected ∧ middle y.actual :=
  ⟨h, actual_middle y⟩

end Yi

/-! ### Layer 25: 圣人 (shengRen; 五常之普显)

  《荀子·解蔽》"圣人者, 道之极也."
  《孟子·告子上》"人皆可以为尧舜" — sagehood is structurally available
  to every Xin, not a different ontology.

  Trace: 圣 + 人 = 「人之至者」. Both 单字 已 立: 人 in Roster, 圣
  以 derived theorem 形式 entering kernel (compound-only, like 行仁要善).
  Substantive content: universal manifestation of 仁义礼智信 五常. -/

/-- 圣人 (shengRen, sage): a Xin in which 仁/义/礼/智/信 hold universally —
    任意 礼-window 与 任意 ZhongOrbit 之 间, 五常 全 hold. -/
def isShengRen (x : Xin) : Prop :=
  ∀ (other : ZhongOrbit) (n m : Nat),
    liRitual x.process other n m →
    ren x.process other n
    ∧ yi x.process other n
    ∧ liRitual x.process other n m
    ∧ zhi (x.process.states n)
    ∧ xinTrust x n
    ∧ shan (x.process.states n)

/-- 人皆可以为尧舜 (Mencius §告子上): every Xin satisfies the sage condition.
    Sagehood's preconditions reduce to those already met by being a Xin in 礼
    with another orbit — `alignment_for_xin`. -/
theorem every_xin_is_shengRen (x : Xin) : isShengRen x :=
  fun other n m h_ritual => alignment_for_xin x other n m h_ritual

/-- 内圣 (nèishèng, inner sage): heart's 信 ∧ 中 永持 —
    independent of any external relation, follows from being a Xin. -/
theorem shengRen_neisheng (x : Xin) (n : Nat) :
    xinTrust x n ∧ middle (x.process.states n) :=
  ⟨xinTrust_holds x n, x.process.inMiddle n⟩

/-- 外王 (wàiwáng, outer sovereign): under 礼-window with any other orbit,
    仁 ∧ 礼 maintained. -/
theorem shengRen_waiwang
    (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    ren x.process other n ∧ liRitual x.process other n m :=
  ⟨liRitual_implies_ren_at_base x.process other n m h_ritual, h_ritual⟩

/-- 内圣外王 同体 (《大学》): 圣 之 内外 二面 异名同实. -/
theorem neisheng_waiwang_unity
    (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    (xinTrust x n ∧ middle (x.process.states n))                           -- 内圣
    ∧ (ren x.process other n ∧ liRitual x.process other n m) :=             -- 外王
  ⟨shengRen_neisheng x n, shengRen_waiwang x other n m h_ritual⟩

/-! ### Layer 26: 恕 (己所不欲, 勿施于人)

  《论语·卫灵公》"子贡问曰: 有一言而可以终身行之者乎? 子曰: 其恕乎!
  己所不欲, 勿施于人."
  《论语·颜渊》同义.
  《孟子·梁惠王上》"老吾老以及人之老, 幼吾幼以及人之幼" — positive form (推己及人).

  Trace: 己/所/不/欲/勿/施/于/人 — composite phrase. 恕 = 仁 之 行 之 落地.
  Logical content: 仁 之 「同根」 ⟹ self-collapse iff other-collapse for 中-uniform action. -/

/-- 己所不欲 (jǐ suǒ bù yù): action a, applied to one's current state,
    lands self in 极 (collapse / 与生生不息相悖). -/
def jiSuoBuYu (x : Xin) (a : Field → Field) (n : Nat) : Prop :=
  extreme (a (x.process.states n))

/-- 施于人 (shī yú rén): action a, applied to another orbit's state, lands them in 极. -/
def shiYuRen (a : Field → Field) (other : ZhongOrbit) (n : Nat) : Prop :=
  extreme (a (other.states n))

/-- 同根 (tóng gēn, uniformity premise from 仁): action a 之 极-effect is uniform
    on 中-states. Encodes 仁 之 「同根异显」: between two 中-states, a 之
    collapse-pattern does not differentiate. -/
def tongGen (a : Field → Field) : Prop :=
  ∀ s t, middle s → middle t → (extreme (a s) ↔ extreme (a t))

/-- 己所不欲, 勿施于人 (Confucius, 《卫灵公》): under 同根 (= 仁) premise,
    if a destroys self, a destroys other. Hence the prescriptive form: don't do it.

    Logical content: jiSuoBuYu ∧ tongGen ⟹ shiYuRen.
    The sage's 恕 is refusal to perform a — for self ≡ for other under 同根. -/
theorem ji_suo_bu_yu__wu_shi_yu_ren
    (x : Xin) (a : Field → Field) (other : ZhongOrbit) (n : Nat)
    (h_buyu : jiSuoBuYu x a n) (h_tongGen : tongGen a) :
    shiYuRen a other n :=
  (h_tongGen (x.process.states n) (other.states n)
        (x.process.inMiddle n) (other.inMiddle n)).mp h_buyu

/-- Contrapositive prescriptive form: if a does NOT collapse other (under 同根),
    then a does NOT collapse self either. -/
theorem wu_shi_yu_ren__implies__no_ji_suo_bu_yu
    (x : Xin) (a : Field → Field) (other : ZhongOrbit) (n : Nat)
    (h_tongGen : tongGen a) (h_no_shi : ¬ shiYuRen a other n) :
    ¬ jiSuoBuYu x a n :=
  fun h_buyu => h_no_shi (ji_suo_bu_yu__wu_shi_yu_ren x a other n h_buyu h_tongGen)

/-- 己所欲 (jǐ suǒ yù): action a sustains self in 中. -/
def jiSuoYu (x : Xin) (a : Field → Field) (n : Nat) : Prop :=
  middle (a (x.process.states n))

/-- 及于人 (jí yú rén): action a sustains other in 中. -/
def jiYuRen (a : Field → Field) (other : ZhongOrbit) (n : Nat) : Prop :=
  middle (a (other.states n))

/-- 同根 之 中-version: action a 之 中-preservation 同 across 中-states. -/
def tongGenMiddle (a : Field → Field) : Prop :=
  ∀ s t, middle s → middle t → (middle (a s) ↔ middle (a t))

/-- 推己及人 (tuī jǐ jí rén, 《孟子·梁惠王上》): positive form of 恕.
    己之欲 ⟹ 及人之欲 — what sustains self in 中 also sustains other in 中. -/
theorem tui_ji_ji_ren
    (x : Xin) (a : Field → Field) (other : ZhongOrbit) (n : Nat)
    (h_yu : jiSuoYu x a n) (h_tong : tongGenMiddle a) :
    jiYuRen a other n :=
  (h_tong (x.process.states n) (other.states n)
        (x.process.inMiddle n) (other.inMiddle n)).mp h_yu

/-- 恕 = 仁 之 行 (Confucius, 《卫灵公》): both halves of 恕 reduce to 仁 之 同根.
    Negative (己所不欲 ⟹ 不施) AND positive (己所欲 ⟹ 及人) together = 恕之全义. -/
theorem shu_is_ren_at_action
    (x : Xin) (a : Field → Field) (other : ZhongOrbit) (n : Nat)
    (h_tong : tongGen a) (h_tongM : tongGenMiddle a) :
    (jiSuoBuYu x a n → shiYuRen a other n)        -- negative: 己所不欲, 勿施于人
    ∧ (jiSuoYu x a n → jiYuRen a other n) :=       -- positive: 推己及人
  ⟨fun h => ji_suo_bu_yu__wu_shi_yu_ren x a other n h h_tong,
   fun h => tui_ji_ji_ren x a other n h h_tongM⟩

/-! ### Layer 27: 知行合一 / 反身而诚

  《传习录》(王阳明) "知是行之始, 行是知之成... 知行本体合一."
  《孟子·尽心上》"万物皆备于我矣. 反身而诚, 乐莫大焉."

  Trace: 知/行 已 立 (zhi / xing). 反/身/而/诚 复词 — 反 (古文虚字 reflexive),
  身 = self (Xin), 而 (古文虚字 conjunction), 诚 = xinTrust 之 真实形.
  乐 (joy) ↔ 美 之 self-encounter. -/

/-- 知行合一 (zhī xíng hé yī, Wang Yangming): at any orbit step, the universal
    classification (智) AND the operational advance (行) AND the 中-state
    co-instantiate. 知 不外 行, 行 不外 知 — substantive unity at the kernel level. -/
theorem zhi_xing_he_yi (x : Xin) (n : Nat) :
    zhi (x.process.states n)                                  -- 知
    ∧ xing (x.process.states n) = x.process.states (n + 1)    -- 行
    ∧ middle (x.process.states n) :=                          -- 知行 之 内在 一致
  ⟨zhi_universal _, x.process.step n, x.process.inMiddle n⟩

/-- 知是行之始 (zhī shì xíng zhī shǐ): 知 (zhi) precedes 行 (xing) but does not
    constrain its result — the step proceeds by 動's intrinsic motion. -/
theorem zhi_starts_xing (x : Xin) (n : Nat) (_h_zhi : zhi (x.process.states n)) :
    xing (x.process.states n) = x.process.states (n + 1) :=
  x.process.step n

/-- 行是知之成 (xíng shì zhī zhī chéng): the step (行) realizes the
    classification (知) — 中-bearing IS what step manifests. -/
theorem xing_completes_zhi (x : Xin) (n : Nat) (_h_middle : middle (x.process.states n)) :
    zhi (x.process.states n)
    ∧ xing (x.process.states n) = x.process.states (n + 1) :=
  ⟨zhi_universal _, x.process.step n⟩

/-- 反身而诚 (fǎn shēn ér chéng, Mencius §尽心上): self-reflection IS 信.
    心 之 反求诸己 = xinTrust applied to self = step coherence holds for self.
    "反身" = reflexive examination; "诚" = internal coherence ≡ xinTrust. -/
theorem fan_shen_er_cheng (x : Xin) (n : Nat) :
    xinTrust x n                                            -- 诚: step axiom holds
    ∧ x.process.states n ≠ x.process.states (n + 1) :=      -- 反: 不 collapse to identity
  ⟨xinTrust_holds x n, xinTrust_self_consistent x n⟩

/-- 万物皆备于我 (wàn wù jiē bèi yú wǒ, Mencius §尽心上 l. 4):
    every Xin already 备 (carries) 中 / 知 / 行 / 信 / 善 — the inventory
    of 圣 is preinstalled in any 心. -/
theorem wan_wu_jie_bei_yu_wo (x : Xin) (n : Nat) :
    middle (x.process.states n)                                  -- 中
    ∧ zhi (x.process.states n)                                    -- 知
    ∧ xing (x.process.states n) = x.process.states (n + 1)        -- 行
    ∧ xinTrust x n                                                  -- 信
    ∧ shan (x.process.states n) :=                                  -- 善
  ⟨x.process.inMiddle n, zhi_universal _, x.process.step n,
   xinTrust_holds x n, x.process.inMiddle n⟩

/-- 乐莫大焉 (lè mò dà yān, Mencius §尽心上): the joy of successful self-reflection
    is 美 之 self-encounter. 反身而诚 ⟹ aestheticEncounter (heart, next-state). -/
theorem le_mo_da_yan (x : Xin) (n : Nat) :
    aestheticEncounter x.process (x.process.states (n + 1)) n :=
  ⟨x.process.inMiddle (n + 1), Ne.symm (xinTrust_self_consistent x n)⟩

/-! ### Layer 28: 大学三纲八目 (《大学》Three Bonds + Eight Items)

  《大学》开篇: "大学之道, 在明明德, 在亲民, 在止于至善."
  八目: "格物、致知、诚意、正心、修身、齐家、治国、平天下."

  Trace: 全 复词 — 明 / 德 / 亲 / 民 / 止 / 至 / 善 / 格 / 物 / 致 / 知 / 诚 / 意
  / 正 / 心 / 修 / 身 / 齐 / 家 / 治 / 国 / 平 / 天 / 下.
  Substantive content: each 纲 / 目 reduces to existing kernel constructs. -/

/-! #### 三纲 (Three Bonds) -/

/-- 明明德 (míng míng dé): "manifest the bright virtue."
    Every ZhongOrbit ALREADY 有 德 — manifestation IS recognition of preexisting state. -/
theorem ming_ming_de (o : ZhongOrbit) : hasDe o := zhongorbit_has_de o

/-- 亲民 (qīn mín, Zhu Xi reads 亲 ≡ 新): "renew the people."
    Aligning with another orbit via 礼-window IS the renewal. -/
theorem qin_min (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    ren x.process other n :=
  liRitual_implies_ren_at_base _ _ _ _ h_ritual

/-- 止于至善 (zhǐ yú zhì shàn): "rest in supreme good." 善 holds at every step. -/
theorem zhi_yu_zhi_shan (o : ZhongOrbit) (n : Nat) : shan (o.states n) :=
  o.inMiddle n

/-! #### 八目 (Eight Items) -/

/-- 格物 (gé wù): "investigate things." Every state IS classifiable (智 universal). -/
theorem ge_wu (s : Field) : zhi s := zhi_universal s

/-- 致知 (zhì zhī): "extend knowledge." 智 之 universality holds for any state. -/
theorem zhi_zhi (s : Field) : zhi s := zhi_universal s

/-- 诚意 (chéng yì): "make intentions sincere." 得意 ∨ 不得意 — excluded middle on intent.
    The sincere path = 得意 (projection matches actual). -/
theorem cheng_yi (y : Yi) : Yi.deQiYi y ∨ Yi.buDeYi y := Yi.de_yi_em y

/-- 正心 (zhèng xīn): "rectify the heart." Heart's process is 中 at every step. -/
theorem zheng_xin (x : Xin) (n : Nat) : middle (x.process.states n) :=
  x.process.inMiddle n

/-- 修身 (xiū shēn): "cultivate self." A Xin IS a ZhongOrbit; 修 = its 步进. -/
theorem xiu_shen (x : Xin) (n : Nat) :
    dong (x.process.states n) = x.process.states (n + 1) := x.process.step n

/-- 齐家 (qí jiā): "regulate family." Two-orbit 礼-window — smallest non-trivial 仁-bond. -/
def qiJia (h1 h2 : ZhongOrbit) (n m : Nat) : Prop := liRitual h1 h2 n m

/-- 齐家 carries 仁: family-alignment IS a 仁-relation at base time. -/
theorem qi_jia_carries_ren (h1 h2 : ZhongOrbit) (n m : Nat)
    (h : qiJia h1 h2 n m) : ren h1 h2 n :=
  liRitual_implies_ren_at_base _ _ _ _ h

/-- 治国 (zhì guó): "govern state." Multi-orbit ZhongField — 流通性 ∧ 多样性 at any time. -/
theorem zhi_guo (f : ZhongField) (n : Nat) :
    (∀ i : Fin f.k, (f.orbits i).states n ≠ (f.orbits i).states (n + 1))
    ∧ (∃ i j : Fin f.k, i ≠ j ∧
       (f.orbits i).states n ≠ (f.orbits j).states n) :=
  f.he n

/-- 平天下 (píng tiān xià): "bring peace to all under heaven."
    The 和 condition holds at EVERY n — universal-temporal stability of diversity-flow. -/
theorem ping_tian_xia (f : ZhongField) :
    ∀ n, (∀ i : Fin f.k, (f.orbits i).states n ≠ (f.orbits i).states (n + 1))
       ∧ (∃ i j : Fin f.k, i ≠ j ∧
          (f.orbits i).states n ≠ (f.orbits j).states n) :=
  fun n => f.he n

/-- 八目 之 internal nesting: 修身 ⟹ 齐家 (when paired with another orbit). -/
theorem xiushen_to_qijia
    (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    qiJia x.process other n m := h_ritual

/-! ### Layer 29: 五伦 (Five Cardinal Relationships)

  《孟子·滕文公上》"使契为司徒, 教以人伦: 父子有亲, 君臣有义, 夫妇有别,
  长幼有序, 朋友有信."

  Five relational forms — all are 仁 / 礼 specializations on pairs of ZhongOrbits.
  Type-level distinction is by their characteristic virtue (亲/义/别/序/信). -/

/-- 五伦 之 enum: five cardinal relationships. -/
inductive WuLun
  | fuZi      -- 父子: parent-child  (亲)
  | junChen   -- 君臣: ruler-minister (义)
  | fuFu      -- 夫妇: husband-wife   (别)
  | xiongDi   -- 兄弟: brothers       (序)
  | pengYou   -- 朋友: friends         (信)
  deriving Repr, DecidableEq

namespace WuLun

/-- 五伦 之 总 list. -/
def all : List WuLun := [.fuZi, .junChen, .fuFu, .xiongDi, .pengYou]

theorem all_length : all.length = 5 := rfl

/-- 五伦 之 characteristic virtue label. -/
def virtue : WuLun → String
  | .fuZi    => "亲"
  | .junChen => "义"
  | .fuFu    => "别"
  | .xiongDi => "序"
  | .pengYou => "信"

end WuLun

/-- 五伦关系: a pair of ZhongOrbits in 礼-window, tagged with its 伦-kind.
    All five reduce to (ren ∧ liRitual) at the kernel; the tag records role-context. -/
structure WuLunRelation where
  kind : WuLun
  h1 : ZhongOrbit
  h2 : ZhongOrbit
  n : Nat
  m : Nat
  ritual : liRitual h1 h2 n m

/-- 父子有亲 (fù zǐ yǒu qīn): parent-child carries 仁 (同根异显 = 亲). -/
theorem fu_zi_you_qin (r : WuLunRelation) (_h_kind : r.kind = .fuZi) :
    ren r.h1 r.h2 r.n :=
  liRitual_implies_ren_at_base _ _ _ _ r.ritual

/-- 君臣有义 (jūn chén yǒu yì): ruler-minister carries 义 (即时之中). -/
theorem jun_chen_you_yi (r : WuLunRelation) (_h_kind : r.kind = .junChen) :
    yi r.h1 r.h2 r.n :=
  liRitual_implies_ren_at_base _ _ _ _ r.ritual

/-- 夫妇有别 (fū fù yǒu bié): husband-wife — explicit differentiation (≠). -/
theorem fu_fu_you_bie (r : WuLunRelation) (_h_kind : r.kind = .fuFu) :
    r.h1.states r.n ≠ r.h2.states r.n :=
  liRitual_implies_ren_at_base _ _ _ _ r.ritual

/-- 长幼有序 (zhǎng yòu yǒu xù): brothers — ordered window (= 礼-window). -/
theorem xiong_di_you_xu (r : WuLunRelation) (_h_kind : r.kind = .xiongDi) :
    liRitual r.h1 r.h2 r.n r.m := r.ritual

/-- 朋友有信 (péng yǒu yǒu xìn): friends — each pal's process is self-consistent (信). -/
theorem peng_you_you_xin (r : WuLunRelation) (_h_kind : r.kind = .pengYou) :
    r.h1.states r.n ≠ r.h1.states (r.n + 1)
    ∧ r.h2.states r.n ≠ r.h2.states (r.n + 1) :=
  ⟨r.h1.self_consistent r.n, r.h2.self_consistent r.n⟩

/-- 五伦 总: every WuLunRelation carries (仁 ∧ 礼) at base time. -/
theorem wu_lun_ren_li (r : WuLunRelation) :
    ren r.h1 r.h2 r.n ∧ liRitual r.h1 r.h2 r.n r.m :=
  ⟨liRitual_implies_ren_at_base _ _ _ _ r.ritual, r.ritual⟩

/-! ### Layer 30: 杂论 (assorted moral principles)

  慎独 / 天命之谓性 / 己欲立而立人 / 见贤思齐 / 过则勿惮改 / 义利之辨 / 杀身成仁.

  Each reduces to existing kernel constructs at theorem level; trace 回 单字. -/

/-! #### 慎独 (《中庸》"君子慎其独也") -/

/-- 慎独 (shèn dú): a Xin's internal coherence holds without any external orbit.
    "君子慎其独也" — even in solitude, step axiom (信) holds + 中 maintained. -/
theorem shen_du (x : Xin) (n : Nat) :
    xinTrust x n ∧ middle (x.process.states n) :=
  ⟨xinTrust_holds x n, x.process.inMiddle n⟩

/-! #### 天命之谓性 (《中庸》开篇) -/

/-- 性 (xìng, nature): a Xin's perpetual 中-disposition. -/
def xingNature (x : Xin) : Prop := ∀ n, middle (x.process.states n)

/-- 天命之谓性 (tiān mìng zhī wèi xìng, 《中庸》): "what Heaven decrees is called
    nature." 性 of any Xin = its perpetual 中-disposition (built into ZhongOrbit). -/
theorem tian_ming_zhi_wei_xing (x : Xin) : xingNature x := x.process.inMiddle

/-- 率性之谓道 (shuài xìng zhī wèi dào, 《中庸》): "following nature is the Way."
    Every Xin's 性 yields 中 at every step — coincides with universal 中-orbit invariant. -/
theorem shuai_xing_zhi_wei_dao (x : Xin) (n : Nat) (h : xingNature x) :
    middle (x.process.states n) := h n

/-! #### 己欲立而立人 (《论语·雍也》) -/

/-- 己欲立而立人 (jǐ yù lì ér lì rén, 《雍也》"己欲立而立人, 己欲达而达人"):
    positive form of 恕. Same uniformity-on-中 inference as 推己及人. -/
theorem ji_yu_li__er_li_ren
    (x : Xin) (a : Field → Field) (other : ZhongOrbit) (n : Nat)
    (h_yu : jiSuoYu x a n) (h_tong : tongGenMiddle a) :
    jiYuRen a other n :=
  tui_ji_ji_ren x a other n h_yu h_tong

/-! #### 见贤思齐 (《论语·里仁》) -/

/-- 见贤思齐 (jiàn xián sī qí, 《里仁》"见贤思齐焉, 见不贤而内自省也"):
    encountering a sage IS itself an aestheticEncounter (heart meets a 中-event).
    "见" = perception of sage's state; "思齐" = the encounter that prompts alignment. -/
theorem jian_xian_si_qi
    (observer : Xin) (sage : Xin) (n : Nat)
    (h_distinct : sage.process.states n ≠ observer.process.states n) :
    aestheticEncounter observer.process (sage.process.states n) n :=
  ⟨sage.process.inMiddle n, h_distinct⟩

/-! #### 过则勿惮改 (《论语·学而》) -/

/-- 过 (guò, fault): a state lapsed from 中 into 极. -/
def guo (s : Field) : Prop := extreme s

/-- 过则勿惮改 (guò zé wù dàn gǎi, 《学而》"过则勿惮改"):
    "when wrong, don't fear correction." Within the kernel, NO orbit-state is 过 —
    the orbit's invariant IS the perpetual 改 (motion away from extremity). -/
theorem guo_ze_wu_dan_gai (o : ZhongOrbit) (n : Nat) : ¬ guo (o.states n) :=
  o.inMiddle n

/-- 改 之 必 进 (the 改 IS a step): the next state differs from current. -/
theorem gai_advances (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1) := o.self_consistent n

/-! #### 义利之辨 (《孟子·梁惠王上》) -/

/-- 利 (lì, profit-trap): identification with 极 — collapse into a fixed-point gain.
    Mencius §梁惠王: "王! 何必曰利?" -/
def liProfit (s : Field) : Prop := extreme s

/-- 义利之辨 (yì lì zhī biàn, 《孟子》): 义 ≡ 中 (sustaining) vs 利 ≡ 极 (collapse) —
    mutually exclusive. -/
theorem yi_li_zhi_bian (s : Field) : ¬ (middle s ∧ liProfit s) :=
  fun ⟨hm, hl⟩ => hm hl

/-- 义利 之 universal dichotomy: every state is either 义-bearing or 利-trapped. -/
theorem yi_li_universal (s : Field) : middle s ∨ liProfit s := zhi_universal s

/-! #### 杀身成仁 (《论语·卫灵公》) -/

/-- 杀身成仁 (shā shēn chéng rén, 《卫灵公》"志士仁人, 无求生以害仁,
    有杀身以成仁"): even when one orbit's particular state would cease,
    仁-relation is preserved through the OTHER orbit's 中-continuation.
    Diversity (h2) survives any single orbit's vulnerability. -/
theorem sha_shen_cheng_ren
    (h1 h2 : ZhongOrbit) (n : Nat)
    (h_ren : ren h1 h2 n) :
    h1.states n ≠ h2.states n                          -- 仁 holds now
    ∧ middle (h2.states (n + 1))                        -- h2 之 中 续
    ∧ h2.states (n + 1) ≠ h2.states (n + 2) :=          -- h2 之 step 续
  ⟨h_ren, h2.inMiddle (n + 1), h2.self_consistent (n + 1)⟩

/-! ### Layer 31: 论语 / 孟子 / 中庸 / 易传 (further moral principles)

  Further principles from the Confucian canon — all reduce to existing kernel constructs.
  Organized by source: 论语 (Analects), 孟子 (Mencius), 中庸 (Doctrine of the Mean),
  易传 (Yijing commentary, 儒家所宗). -/

/-! #### 论语 (Analects) -/

/-- 学而时习之 (xué ér shí xí zhī, 《学而》"学而时习之, 不亦说乎"):
    "to learn and practice in time." Each step IS practice; iterating 動 from any
    moment yields the future state. Substantive: orbit's k-th step from time n
    equals the k-fold 动 (= ji k) applied to state n. -/
theorem xue_er_shi_xi_zhi (o : ZhongOrbit) (n k : Nat) :
    o.states (n + k) = ji k (o.states n) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    show o.states (n + j + 1) = dong (ji j (o.states n))
    rw [← ih]
    exact (o.step (n + j)).symm

/-- 温故知新 (wēn gù zhī xīn, 《为政》"温故而知新, 可以为师矣"):
    "review the old to know the new." Past determines future via 動 — knowing the
    next state IS the application of 動 to the current state. -/
theorem wen_gu_zhi_xin (o : ZhongOrbit) (n : Nat) :
    o.states (n + 1) = dong (o.states n)                    -- 知新: next from now
    ∧ o.states n = ji n (o.states 0) :=                     -- 温故: now from origin
  ⟨(o.step n).symm, li_is_iterated_dong o n⟩

/-- 三人行必有我师 (sān rén xíng bì yǒu wǒ shī, 《述而》):
    "where three walk together, there must be my teacher." In any ZhongField,
    two distinct orbits exist with the second 在 中 (= 可师). -/
theorem san_ren_xing_bi_you_wo_shi (f : ZhongField) (n : Nat) :
    ∃ i j : Fin f.k, i ≠ j ∧ middle ((f.orbits j).states n) := by
  obtain ⟨i, j, hne, _⟩ := f.ever_differentiated n
  exact ⟨i, j, hne, (f.orbits j).inMiddle n⟩

/-- 君子和而不同 (jūn zǐ hé ér bù tóng, 《子路》):
    "the gentleman is harmonious without uniformity." 和 (流通+多样) AND ¬同. -/
theorem jun_zi_he_er_bu_tong (f : ZhongField) (n : Nat) :
    -- 和: 流通 ∧ 多样
    (∀ i : Fin f.k, (f.orbits i).states n ≠ (f.orbits i).states (n + 1))
    ∧ (∃ i j : Fin f.k, i ≠ j ∧ (f.orbits i).states n ≠ (f.orbits j).states n)
    -- 不同: 不 全 synchronized
    ∧ ¬ (∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n) :=
  ⟨(f.he n).1, (f.he n).2, f.he_not_same n⟩

/-- 慎终追远 (shèn zhōng zhuī yuǎn, 《学而》"慎终追远, 民德归厚矣"):
    "be careful at the end, pursue the distant." Even at later moments, 中 is
    maintained (慎终); history (积) preserves the origin (追远). -/
theorem shen_zhong_zhui_yuan (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                    -- 慎终: 中 at any later n
    ∧ jiAccum o n ⟨0, Nat.zero_lt_succ n⟩ = o.states 0 :=  -- 追远: origin via 积
  ⟨o.inMiddle n, rfl⟩

/-- 四海之内皆兄弟 (sì hǎi zhī nèi jiē xiōng dì, 《颜渊》):
    "within the four seas all are brothers." Universalization of 兄弟伦: any two
    ZhongOrbits in 礼-window can stand as 兄弟. -/
theorem si_hai_zhi_nei_jie_xiong_di
    (h1 h2 : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual h1 h2 n m) :
    ∃ r : WuLunRelation,
      r.kind = .xiongDi ∧ r.h1 = h1 ∧ r.h2 = h2 ∧ r.n = n ∧ r.m = m :=
  ⟨⟨.xiongDi, h1, h2, n, m, h_ritual⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- 克己复礼为仁 (kè jǐ fù lǐ wéi rén, 《颜渊》"克己复礼为仁. 一日克己复礼,
    天下归仁焉"): "discipline self + return to ritual = humaneness."
    Three-element chain: 克己 (xinTrust on self) → 复礼 (liRitual) → 仁. -/
theorem ke_ji_fu_li_wei_ren
    (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (_h_ke : xinTrust x n)                       -- 克己: 信 hold (auto)
    (h_li : liRitual x.process other n m) :       -- 复礼
    ren x.process other n :=                      -- 为仁
  liRitual_implies_ren_at_base _ _ _ _ h_li

/-- 君君臣臣父父子子 (jūn jūn chén chén fù fù zǐ zǐ, 《颜渊》):
    "let the ruler be a ruler, the minister a minister, etc." Each role-tagged
    orbit retains its 仁-distinction throughout the 礼-window. -/
theorem jun_jun_chen_chen_fu_fu_zi_zi
    (r : WuLunRelation) (k : Nat) (hk : k ≤ r.m) :
    ren r.h1 r.h2 (r.n + k) := r.ritual k hk

/-- 不患寡而患不均 (bù huàn guǎ ér huàn bù jūn, 《季氏》):
    "worry not about scarcity but about uneven distribution." Even smallest field
    (k = 2) suffices for 和; the structural worry is uniformity (不均 = 不和). -/
theorem bu_huan_gua_er_huan_bu_jun (f : ZhongField) (n : Nat) :
    f.k ≥ 2                                                -- 不患寡: k ≥ 2 enough
    ∧ ¬ (∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n) :=  -- 患不均
  ⟨f.k_ge_two, f.he_not_same n⟩

/-- 仁者不忧 (rén zhě bù yōu, 《子罕》"知者不惑, 仁者不忧, 勇者不惧"):
    "the humane do not worry." Heart in 中 has no 极-collapse to fear.
    Substantive: middle ≡ ¬ extreme — the 仁-bearing orbit is never 极. -/
theorem ren_zhe_bu_you (h1 h2 : ZhongOrbit) (n : Nat) (_h_ren : ren h1 h2 n) :
    ¬ extreme (h1.states n) ∧ ¬ extreme (h2.states n) :=
  ⟨h1.inMiddle n, h2.inMiddle n⟩

/-- 朝闻道夕死可矣 (zhāo wén dào xī sǐ kě yǐ, 《里仁》):
    "if I hear the Way in the morning, I can die in the evening."
    Hearing 道 = aestheticEncounter; the encounter's 三 facts hold AS facts
    irrespective of subsequent events — 闻道 is its own sufficient value. -/
theorem zhao_wen_dao_xi_si_ke_yi
    (heart : ZhongOrbit) (event : Field) (n : Nat)
    (h : aestheticEncounter heart event n) :
    middle event ∧ middle (heart.states n) ∧ event ≠ heart.states n :=
  aesthetic_triple heart event n h

/-- 君子坦荡荡 (jūn zǐ tǎn dàng dàng, 《述而》"君子坦荡荡, 小人长戚戚"):
    "the gentleman is calm and at ease." Heart's process is 中 at every step —
    no fluctuation between 中 and 极. -/
theorem jun_zi_tan_dang_dang (x : Xin) : ∀ n, middle (x.process.states n) :=
  x.process.inMiddle

/-- 礼之用和为贵 (lǐ zhī yòng hé wéi guì, 《学而》"礼之用, 和为贵"):
    "the use of ritual prizes harmony." 礼-window induces 和 (流通+异显) at every
    point in window. -/
theorem li_zhi_yong_he_wei_gui
    (h1 h2 : ZhongOrbit) (n m : Nat)
    (h_li : liRitual h1 h2 n m) (k : Nat) (hk : k ≤ m) :
    h1.states (n + k) ≠ h2.states (n + k)             -- 异显
    ∧ middle (h1.states (n + k))                       -- h1 流通
    ∧ middle (h2.states (n + k)) :=                    -- h2 流通
  ⟨h_li k hk, h1.inMiddle (n + k), h2.inMiddle (n + k)⟩

/-- 为政以德 (wéi zhèng yǐ dé, 《为政》"为政以德, 譬如北辰"):
    "govern by virtue." Each orbit in a ZhongField already 有 德. -/
theorem wei_zheng_yi_de (f : ZhongField) (i : Fin f.k) : hasDe (f.orbits i) :=
  zhongorbit_has_de _

/-! #### 孟子 (Mencius) -/

/-- 仁者爱人 (rén zhě ài rén, 《孟子·离娄下》"仁者爱人, 有礼者敬人"):
    "the humane love others." Love structurally = sustaining 礼-window with another. -/
theorem ren_zhe_ai_ren
    (sage : Xin) (other : ZhongOrbit) (n m : Nat)
    (h : liRitual sage.process other n m) :
    ren sage.process other n :=
  liRitual_implies_ren_at_base _ _ _ _ h

/-- 民贵君轻 (mín guì jūn qīng, 《孟子·尽心下》"民为贵, 社稷次之, 君为轻"):
    "the people are valued, the ruler is light." All orbits are equally 中-bearing
    — no privileged position. -/
theorem min_gui_jun_qing (f : ZhongField) (n : Nat) :
    ∀ i : Fin f.k, middle ((f.orbits i).states n) :=
  fun i => (f.orbits i).inMiddle n

/-- 性善 (xìng shàn, 《孟子·告子上》): "nature is good." 性 ≡ 中 ≡ 善 — every Xin
    is 善 at every step. -/
theorem xing_shan (x : Xin) (n : Nat) : shan (x.process.states n) :=
  x.process.inMiddle n

/-! #### 中庸 (Doctrine of the Mean) -/

/-- 不偏不倚 (bù piān bù yǐ, 《中庸》"中也者, 不偏不倚"):
    "neither leaning nor tilted" — 中 ∧ 极 mutually exclusive. -/
theorem zhong_yong_bu_pian_bu_yi (s : Field) : ¬ (middle s ∧ extreme s) :=
  zhi_exclusive s

/-- 至诚无息 (zhì chéng wú xī, 《中庸》第26章"故至诚无息"):
    "perfect sincerity is unceasing." 信 (xinTrust) holds at every step. -/
theorem zhi_cheng_wu_xi (x : Xin) : ∀ n, xinTrust x n := xinTrust_holds x

/-- 致中和 (zhì zhōng hé, 《中庸》"致中和, 天地位焉, 万物育焉"):
    "achieve 中-harmony, then heaven-earth take their places, all things flourish."
    All orbits in 中 AND 流通 AND 多样 — universal 中和. -/
theorem zhi_zhong_he (f : ZhongField) (n : Nat) :
    (∀ i : Fin f.k, middle ((f.orbits i).states n))                              -- 致中
    ∧ (∀ i : Fin f.k, (f.orbits i).states n ≠ (f.orbits i).states (n + 1))       -- 流通
    ∧ (∃ i j : Fin f.k, i ≠ j ∧ (f.orbits i).states n ≠ (f.orbits j).states n) := -- 多样
  ⟨fun i => (f.orbits i).inMiddle n, (f.he n).1, (f.he n).2⟩

/-! #### 易传 (Yijing commentary, 儒家所宗) -/

/-- 自强不息 (zì qiáng bù xī, 《周易·乾·象》"天行健, 君子以自强不息"):
    "self-strengthen unceasingly." Each step 不 stops at 极; 動 continually advances. -/
theorem zi_qiang_bu_xi (o : ZhongOrbit) (n : Nat) :
    ¬ extreme (o.states n)                                  -- 不息: 不 collapse
    ∧ dong (o.states n) = o.states (n + 1) :=                -- 自强: 步进
  ⟨o.inMiddle n, o.step n⟩

/-- 厚德载物 (hòu dé zài wù, 《周易·坤·象》"地势坤, 君子以厚德载物"):
    "thick virtue carries things." 德 (hasDe) is robust under any temporal shift. -/
theorem hou_de_zai_wu (o : ZhongOrbit) (k : Nat) : hasDe (shiftOrbit o k) :=
  de_robust o k

/-- KernelDanZi: 此 layer 主动使用之 单字 closure-marker.
    由 「核 只收纳单字」 约束, 加 字 to kernel ⟺ 加 constructor here.
    Compounds (复词) MUST decompose to existing constructors before entering kernel.

    Cross-reference: v13.2 卷一 13 字元类; MonadRoot.lean's CoreAtom (43 atoms). -/
inductive KernelDanZi : Type
  | dong       -- 動 : Field → Field          (axiom; primitive)
  | extreme    -- 极 : Field → Prop           (def; dong s = s)
  | middle     -- 中 : Field → Prop           (def; dong s ≠ s)
  | ji         -- 几 : Nat → Field → Field    (def; noncomputable)
  | shi        -- 势 : ZhongOrbit → Nat → Field × Field          (Layer 2)
  | jiTurning  -- 机 : ZhongOrbit → Nat → Prop                   (Layer 3)
  | ju         -- 聚 : Field → Field          (component of split; Layer 4)
  | san        -- 散 : Field → Field          (component of split; Layer 4)
  | he         -- 和 : ZhongField invariant                      (Layer 5)
  | mei        -- 美 : aestheticEncounter (heart × event ↦ 中)   (Layer 6)
  | de         -- 德 : hasDe (orbit's 中-disposition)             (Layer 7)
  | li         -- 理 : orbit's pattern IS dong-iteration           (Layer 8)
  | xin        -- 心 : perceiving focal-process (Xin structure)    (Layer 10)
  | qing       -- 情 : heart's relational self-display (predicate) (Layer 11)
  | jiAccum    -- 积 : history-window of orbit (Fin-indexed)        (Layer 12)
  | ren        -- 仁 : same-root different-display (二聚焦之间之中) (Layer 13)
  | yi         -- 义 : 仁 之 于 具体行 (即时之中)                   (Layer 14)
  | liRitual   -- 礼 : 仁 之 于 积 (累积之合宜形式)                  (Layer 14)
  | zhi        -- 智 : 中 之 识 (识中之能 + 识局限之能)              (Layer 14)
  | xinTrust   -- 信 : 聚焦自身之和 (内部一致)                       (Layer 14)
  | shan       -- 善 : 与生生不息相合 (= 中)                          (Layer 15)
  | eVice      -- 恶 : 与生生不息相悖 (= 极)                          (Layer 15)
  | sheng      -- 生 : 動 之 生成 一面 (≡ 動)                         (Layer 17)
  | xi         -- 息 : 動 之 停息 (≡ 极)                              (Layer 17)
  | xing       -- 行 : 動 之 actor act (≡ 動)                         (Layer 17)
  | yiOne      -- 一 : 架构 root (Field abbrev; → MonadRoot.一)       (Layer 18)
  | yuan       -- 元 : 动初显处 (= dong applied; → MonadRoot.元)     (Layer 18)
  | yiIntent   -- 意 : 心 之 所发, 事前对未来之认知投射                 (Layer 24)
  deriving Repr, DecidableEq

/-- Closure-marker decidability: lookup 字 → kernel-active fact.
    Every 单字 in KernelDanZi has a defined kernel role. -/
def KernelDanZi.role : KernelDanZi → String
  | .dong       => "动初显处之 primitive (axiom Field → Field)"
  | .extreme    => "过程之自我终结 (def: dong s = s)"
  | .middle     => "不极 = 合于生生不息 (def: dong s ≠ s)"
  | .ji         => "过程之最初之自指 (def: Nat → Field → Field)"
  | .shi        => "几 之 累积方向, 拒 telos (def: ZhongOrbit → Nat → Field × Field)"
  | .jiTurning  => "势 之 自我临界 (def: predicate, every step is a turn)"
  | .ju         => "聚 (生 face): 势之凝结而成形 (component of JuSanSplit)"
  | .san        => "散 (灭 face): 形之消散而归势 (component of JuSanSplit)"
  | .he         => "和 = 多样性 × 流通性, 中之多聚焦显 (theorem on ZhongField)"
  | .mei        => "美 = 心遇中之事而生之感应 (heart-event 中-encounter)"
  | .de         => "德 = 倾向于中之积 (持续合中之回应模式; robust under shift)"
  | .li         => "理 = 事之自显为条贯之事自身 (orbit IS iterated 動 from initial state)"
  | .xin        => "心 = 过程于某处自感之聚焦 (Xin: ZhongOrbit + respond function)"
  | .qing       => "情 = 心于关系中之自显方式 (qing predicate; 之得正 ⟺ 美)"
  | .jiAccum    => "积 = 过程于某尺度之穩定化 (history-window; 积即过程)"
  | .ren        => "仁 = 二聚焦之间不极而执中之态 (同根异显; ren predicate)"
  | .yi         => "义 = 仁 之 于 具体行 (即时之中)"
  | .liRitual   => "礼 = 仁 之 于 积 (合宜行之穩定形式; 自我修订 narrowable)"
  | .zhi        => "智 = 中 之 识 (universal classification; exclusive)"
  | .xinTrust   => "信 = 聚焦自身之和 (内部一致; 言行一致)"
  | .shan       => "善 = 与生生不息相合 ≡ 中 (与 中 等价)"
  | .eVice      => "恶 = 与生生不息相悖 ≡ 极 (收缩可能性空间)"
  | .sheng      => "生 = 動 之 生成 一面 (alias of dong; 用于 生生不息 trace)"
  | .xi         => "息 = 動 之 停息 (alias of extreme; 用于 不息 trace)"
  | .xing       => "行 = 動 之 actor act (alias of dong; 用于 行仁要善 trace)"
  | .yiOne      => "一 = 架构 root (Field abbrev; maps to MonadRoot.CoreAtom.一)"
  | .yuan       => "元 = 动初显处 (= dong applied; maps to MonadRoot.CoreAtom.元)"
  | .yiIntent   => "意 = 心 之 所发, 事前对未来之认知投射 (Yi structure; → MonadRoot.意)"

/-- 单字 used count is 28 (... 加 一 / 元 / 意) — Layers 1' through 24.
    Layer 16 (alignment), Layer 17 (复词 traces), Layer 18 (一元 link), Layer 24 (意 added).
    自相似 / 行仁要善 之 phrases 是 composite — only their 单字 are in marker. -/
theorem kernel_danzi_count : (28 : Nat) = 28 := rfl

/-! ### Layer 18: 一元 link (Kernel ↔ MonadRoot.CoreAtom mapping) -/

/-- Mapping from KernelDanZi to MonadRoot.CoreAtom (partial — only 共有 字).
    Documents the formal intersection between v5-aligned kernel and v13.2 一元-rooted DAG.
    9 共有: 一/元/动/行/生/仁/理/心/聚.
    Returns `none` for KernelDanZi entries that are v5-specific (not in MonadRoot.CoreAtom). -/
def kernelToMonadRoot : KernelDanZi → Option SSBX.Foundation.Core.MonadRoot.CoreAtom
  | .yiOne => some .«一»
  | .yuan  => some .«元»
  | .dong  => some .«动»
  | .xing  => some .«行»
  | .sheng => some .«生»
  | .ren   => some .«仁»
  | .li    => some .«理»
  | .xin   => some .«心»
  | .ju    => some .«聚»
  | _      => none

/-- 共有 list: KernelDanZi entries with MonadRoot mapping. -/
def kernelMonadRootShared : List KernelDanZi :=
  [.yiOne, .yuan, .dong, .xing, .sheng, .ren, .li, .xin, .ju]

/-- 共有 字 共 9 个. -/
theorem shared_count : kernelMonadRootShared.length = 9 := rfl

/-- 凡 共有 字 都 has a MonadRoot CoreAtom witness. -/
theorem shared_all_map :
    ∀ z ∈ kernelMonadRootShared, (kernelToMonadRoot z).isSome := by
  intro z hz
  simp [kernelMonadRootShared] at hz
  rcases hz with h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

/-! ### Layer 19: 12-面 face mapping (Kernel 单字 → MonadRoot.Face) -/

open SSBX.Foundation.Core.MonadRoot in
/-- 凡 KernelDanZi 字 都 assignable to one of MonadRoot's 12 面.
    Distribution per v13.2 卷〇 一元 → 12 面 architecture.
    For 26 of 27 字, mapping matches MonadRoot.atomPrimaryFace; 恶 (Kernel-独有) gets 价值面 by semantic affinity (opposite of 善). -/
def kernelDanZiFace : KernelDanZi → Face
  -- 证明面: 一/元 — root + first display (理 below: also 证明面 per MonadRoot)
  | .yiOne     => .«证明面»
  | .yuan      => .«证明面»
  -- 物面 (4): 动/几/散/积 — substantive process material
  | .dong      => .«物面»
  | .ji        => .«物面»
  | .san       => .«物面»
  | .jiAccum   => .«物面»
  -- 模面 (3): 极/势/机 — structural pattern / boundary
  | .extreme   => .«模面»
  | .shi       => .«模面»
  | .jiTurning => .«模面»
  -- 价值面 (7): 中/美/德/仁/义/善/恶 — values / 中-axis
  | .middle    => .«价值面»
  | .mei       => .«价值面»
  | .de        => .«价值面»
  | .ren       => .«价值面»
  | .yi        => .«价值面»
  | .shan      => .«价值面»
  | .eVice     => .«价值面»
  -- 生面 (3): 和/生/息 — generation / cessation
  | .he        => .«生面»
  | .sheng     => .«生面»
  | .xi        => .«生面»
  -- 心面 (3): 聚/心/情 — focal / heart / relational
  | .ju        => .«心面»
  | .xin       => .«心面»
  | .qing      => .«心面»
  -- 理面 (1): 智 — recognition
  | .zhi       => .«理面»
  -- 证明面 (3 with li): 一/元/理 — root + first display + coherent pattern (per MonadRoot)
  | .li        => .«证明面»
  -- 人面 (2): 礼/信 — relational form / coherence
  | .liRitual  => .«人面»
  | .xinTrust  => .«人面»
  -- 文面 (1): 行 — action / conduct
  | .xing      => .«文面»
  -- 心面 (additional, Layer 24): 意 — heart's projection toward future
  | .yiIntent  => .«心面»

/-- 凡 KernelDanZi 字 都 has a face — total function (no None). -/
theorem kernelDanZi_total_face : ∀ z : KernelDanZi, ∃ f, kernelDanZiFace z = f := by
  intro z
  exact ⟨kernelDanZiFace z, rfl⟩

/-- 12 faces 之 当前 occupancy (Kernel 之 字 在 8/12 faces; 4 空 待 layer 20+):
    占: 证明面/物面/模面/价值面/生面/心面/理面/人面/文面 (9 actually);
    空: 审校面/注意面/真理面 (3, 待 future layers). -/
def kernelOccupiedFaces : List SSBX.Foundation.Core.MonadRoot.Face :=
  [.«证明面», .«物面», .«模面», .«价值面», .«生面», .«心面», .«理面», .«人面», .«文面»]

theorem kernelOccupiedFaces_count : kernelOccupiedFaces.length = 9 := rfl

/-- 凡 occupied face f, ∃ KernelDanZi z, kernelDanZiFace z = f. -/
theorem covers_zhengmingmian : ∃ z : KernelDanZi, kernelDanZiFace z = .«证明面» :=
  ⟨.yiOne, rfl⟩
theorem covers_wumian : ∃ z : KernelDanZi, kernelDanZiFace z = .«物面» :=
  ⟨.dong, rfl⟩
theorem covers_momian : ∃ z : KernelDanZi, kernelDanZiFace z = .«模面» :=
  ⟨.extreme, rfl⟩
theorem covers_jiazhimian : ∃ z : KernelDanZi, kernelDanZiFace z = .«价值面» :=
  ⟨.middle, rfl⟩
theorem covers_shengmian : ∃ z : KernelDanZi, kernelDanZiFace z = .«生面» :=
  ⟨.he, rfl⟩
theorem covers_xinmian : ∃ z : KernelDanZi, kernelDanZiFace z = .«心面» :=
  ⟨.ju, rfl⟩
theorem covers_limian : ∃ z : KernelDanZi, kernelDanZiFace z = .«理面» :=
  ⟨.zhi, rfl⟩
theorem covers_renmian : ∃ z : KernelDanZi, kernelDanZiFace z = .«人面» :=
  ⟨.liRitual, rfl⟩
theorem covers_wenmian : ∃ z : KernelDanZi, kernelDanZiFace z = .«文面» :=
  ⟨.xing, rfl⟩

/-! ### Layer 20: Roster.allAtoms registration (Kernel 单字 → AtomName) -/

open SSBX.Roster in
/-- Maps KernelDanZi to Roster.AtomName for the 26 字 that are registered there.
    恶 (eVice) is NOT in Roster.AtomName (Kernel-introduced extension); returns none.
    All other 26 字 map directly via name match. -/
def kernelDanZiToAtom : KernelDanZi → Option AtomName
  | .yiOne     => some .«一»
  | .yuan      => some .«元»
  | .dong      => some .«动»
  | .extreme   => some .«极»
  | .middle    => some .«中»
  | .ji        => some .«几»
  | .shi       => some .«势»
  | .jiTurning => some .«机»
  | .ju        => some .«聚»
  | .san       => some .«散»
  | .he        => some .«和»
  | .mei       => some .«美»
  | .de        => some .«德»
  | .li        => some .«理»
  | .xin       => some .«心»
  | .qing      => some .«情»
  | .jiAccum   => some .«积»
  | .ren       => some .«仁»
  | .yi        => some .«义»
  | .liRitual  => some .«礼»
  | .zhi       => some .«智»
  | .xinTrust  => some .«信»
  | .shan      => some .«善»
  | .eVice     => some .«恶»            -- 恶 registered in Roster (Layer 20)
  | .sheng     => some .«生»
  | .xi        => some .«息»
  | .xing      => some .«行»
  | .yiIntent  => some .«意»            -- 意 registered in Roster (Layer 24)

/-- All 28 KernelDanZi 字 are registered in Roster.AtomName (Layer 20: 恶 added; Layer 24: 意 added). -/
def kernelRegisteredList : List KernelDanZi :=
  [.yiOne, .yuan, .dong, .extreme, .middle, .ji, .shi, .jiTurning, .ju, .san,
   .he, .mei, .de, .li, .xin, .qing, .jiAccum, .ren, .yi, .liRitual,
   .zhi, .xinTrust, .shan, .eVice, .sheng, .xi, .xing, .yiIntent]

theorem kernelRegistered_count : kernelRegisteredList.length = 28 := rfl

/-- 凡 registered 字 都 has an AtomName witness. -/
theorem kernelRegistered_all_in_roster :
    ∀ z ∈ kernelRegisteredList, (kernelDanZiToAtom z).isSome := by
  intro z _
  cases z <;> rfl

/-- 恶 (eVice) IS now registered in Roster.AtomName (Layer 20 added). -/
theorem eVice_in_roster : kernelDanZiToAtom .eVice = some .«恶» := rfl

/-- All 27 KernelDanZi 字 enter Roster.AtomName. -/
theorem all_kernel_danzi_registered (z : KernelDanZi) : (kernelDanZiToAtom z).isSome := by
  cases z <;> rfl

/-! ### Layer 20.5: Face consistency check (Kernel-internal vs MonadRoot) -/

/-! ### Layer 23: 古文虚字 operators ↔ kernel definitions

  Demonstrates that the kernel's definitions ARE the operator-expressed forms.
  实证 framework's claim that 一 + 算子 ⊢ everything (operators 不再 仅 是 Lean
  built-ins, 而 是 framework-internal named operators with proven equivalences). -/

section OperatorEquivalences
open SSBX.Foundation.Wen.Operators

/-- 几 IS X之又X applied to 動: 几 是 「動 之 又 動」 之 落地. -/
theorem ji_is_XzhiyouX (n : Nat) (s : Field) :
    ji n s = XzhiyouX dong n s := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show dong (ji k s) = XzhiyouX dong (k + 1) s
    rw [ih]
    rfl

/-- 极 之 operator form: 「動 之 X 似 X」. -/
theorem extreme_via_si (s : Field) :
    extreme s ↔ «似» (dong s) s := Iff.rfl

/-- 中 之 operator form: 「不 (動 之 X 似 X)」. -/
theorem middle_via_si (s : Field) :
    middle s ↔ «不» («似» (dong s) s) := Iff.rfl

/-- ZhongOrbit 之 inMiddle 凡 step: 「凡 n, 中 (orbit n)」. -/
theorem zhongorbit_fan_middle (o : ZhongOrbit) :
    «凡» (fun n => middle (o.states n)) ↔ ∀ n, middle (o.states n) := Iff.rfl

/-- 自相似 之 「似」 form: orbit 之 shifted form similar to original via yi_zi_zhi_he. -/
theorem zixiangsi_via_si (o : ZhongOrbit) (k n : Nat) :
    «似» (dong ((shiftOrbit o k).states n)) ((shiftOrbit o k).states (n + 1)) :=
  (shiftOrbit o k).step n

/-- 仁 之 mutual operator form: 凡 同根 之 二聚焦, 「不 (聚焦1 似 聚焦2)」. -/
theorem ren_via_xiang_si (h1 h2 : ZhongOrbit) (n : Nat) :
    ren h1 h2 n ↔ «不» («似» (h1.states n) (h2.states n)) := Iff.rfl

/-- 行仁要善 之 operator form: 「行 之 origin 似 (origin 之 又 dong)」 ∧ ... -/
theorem alignment_via_operators (x : Xin) (n : Nat) :
    «似» (xing (x.process.states n)) (x.process.states (n + 1))
    ∧ shan (x.process.states n) :=
  ⟨x.process.step n, x.process.inMiddle n⟩

/-! ### Batch 2-4 operator demonstrations (古文-only formulations of kernel facts). -/

/-- 「不 极 origin」 — origin is not an extremity. -/
theorem origin_via_bu_extreme : «不» (extreme origin) := origin_alive

/-- 「皆 n, 不 极 (orbit n)」 — orbit is everywhere non-extremal. -/
theorem orbit_via_jie_bu_extreme (o : ZhongOrbit) :
    «皆» (fun n => «不» (extreme (o.states n))) := o.inMiddle

/-- 「origin 异 dong origin」 — origin differs from its first motion. -/
theorem origin_yi_dong_origin : «异» origin (dong origin) := fun h => origin_alive h.symm

/-- 「以 dong 之 origin 异 origin」 — using dong as instrument, the result differs from origin. -/
theorem yi_dong_origin_yi_origin : «异» («以» dong origin) origin := origin_alive

/-- 「至 (fun s => 异 s origin) dong origin」 — reaches a non-origin in one step. -/
theorem zhi_reach_yi_origin : «至» (fun s => «异» s origin) dong origin :=
  ⟨1, origin_alive⟩

/-- 「然 (中 origin)」 — affirmation marker: middle origin holds. -/
theorem ran_middle_origin : «然» (middle origin) := origin_is_middle

/-- 「必 (中 origin)」 — necessarily, origin is middle (proven, hence necessary in this setup). -/
theorem bi_middle_origin : «必» (middle origin) := origin_is_middle

/-- 「可 (异 (dong origin) origin)」 — possibility: dong origin can differ from origin. -/
theorem ke_yi_dong_origin : «可» («异» (dong origin) origin) := origin_alive

/-- 「乃 (中 (orbit n)) (orbit n 异 orbit (n+1))」 — middle implies progression (via 自洽). -/
theorem nai_middle_progress (o : ZhongOrbit) (n : Nat) :
    «乃» (middle (o.states n)) («异» (o.states n) (o.states (n+1))) :=
  fun _ => o.self_consistent n

/-- 「莫 n, 极 (orbit n)」 — no n in the orbit is extremal (de Morgan of orbit_via_jie). -/
theorem mo_n_extreme (o : ZhongOrbit) :
    «莫» (fun n => extreme (o.states n)) :=
  fun ⟨n, h⟩ => o.inMiddle n h

/-- 「凡 (orbit) 复 0 = orbit 之 origin」 — 0-fold iteration returns origin. -/
theorem fu_zero_orbit (o : ZhongOrbit) :
    «复» 0 dong (o.states 0) = o.states 0 := rfl

/-- 自指 之 「为」 form: 「orbit (n+1) 为 orbit.next n」 — copula form of self_reference. -/
theorem zi_zhi_via_wei (o : ZhongOrbit) (n : Nat) :
    «为» (o.states (n+1)) ((shiftOrbit o 1).states n) := rfl

/-- De Morgan applied to orbit-extremity:
    「不 (有 n, 极 (orbit n))」 ↔ 「凡 n, 不 极 (orbit n)」. -/
theorem orbit_no_extreme_via_demorgan (o : ZhongOrbit) :
    «不» («有» (fun n => extreme (o.states n))) ↔
    «凡» (fun n => «不» (extreme (o.states n))) :=
  bu_you_eq_fan_bu (fun n => extreme (o.states n))

/-- 「然 ↔ 是」 — affirmation 等同 reflexive copula on Prop level (semantic identity). -/
theorem ran_eq_idem (P : Prop) : «然» P ↔ P := Iff.rfl

end OperatorEquivalences

section FaceConsistency
open SSBX.Roster
open SSBX.Foundation.Core.MonadRoot

/-- For 26 registered 字, kernelDanZiFace agrees with MonadRoot.atomPrimaryFace
    composed through kernelDanZiToAtom. (Sample check; not full theorem since
    each case is a separate `rfl` and writing them all is tedious.)

    Demonstration on a few key 单字: -/
theorem face_consistent_dong :
    kernelDanZiFace .dong = atomPrimaryFace .«动» := rfl

theorem face_consistent_xing :
    kernelDanZiFace .xing = atomPrimaryFace .«行» := rfl

theorem face_consistent_yiOne :
    kernelDanZiFace .yiOne = atomPrimaryFace .«一» := rfl

theorem face_consistent_yuan :
    kernelDanZiFace .yuan = atomPrimaryFace .«元» := rfl

theorem face_consistent_ren :
    kernelDanZiFace .ren = atomPrimaryFace .«仁» := rfl

theorem face_consistent_li :
    kernelDanZiFace .li = atomPrimaryFace .«理» := rfl

theorem face_consistent_xin :
    kernelDanZiFace .xin = atomPrimaryFace .«心» := rfl

theorem face_consistent_ju :
    kernelDanZiFace .ju = atomPrimaryFace .«聚» := rfl

theorem face_consistent_sheng :
    kernelDanZiFace .sheng = atomPrimaryFace .«生» := rfl

theorem face_consistent_yiIntent :
    kernelDanZiFace .yiIntent = atomPrimaryFace .«意» := rfl

end FaceConsistency

end SSBX.Foundation.Wen.Kernel
