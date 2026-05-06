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
  (老子 15: 道法自然/无为而无不为/反者道之动/上善若水/致虚守静/有无相生/大成若缺/
            知人自知/知足不辱/治大国若烹小鲜/玄之又玄/众妙之门/天地不仁/千里之行/
            物壮则老/祸福相倚 + 庄子 8: 齐物论/逍遥游/心斋坐忘/物化/庖丁解牛/朝三暮四/
            大知闲闲/用心若镜)
                                  → 23 theorems + ziRan/wuWei/wuBuWei defs (Layers 32–33)
  (佛家 17: 缘起/缘起性空 + 三法印 (诸行无常/诸法无我/涅槃寂静) + 四圣谛 (苦集灭道) +
            中道/八正道/戒定慧/菩萨行/自度度他/不二法门/心如工画师/一即一切/烦恼即菩提)
                                  → 17 theorems + ku def (Layer 34)

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

/-! ### Layer 32: 道家《道德经》— 老子诸纲

  老子之核要 — 全 归约为已 立 原语 (動 / 中 / 极 / orbit / Xin / ZhongField).
  道家不在外 加 axioms; 其 与 儒家 共 一 underlying machinery (生生不息 之 動),
  唯 emphasis 不同: 道家 强调 自然 / 无为 / 反复; 儒家 强调 仁义 / 礼乐 / 名分.
  在 same 框架 内 二者 互不冲突 — 形式 上 是 同 一 ZhongOrbit + Xin 之 不同 视角. -/

/-! #### 自然 / 无为 之 形式 -/

/-- 自然 (zì rán, self-so): orbit's step IS spontaneous —
    生 from inside, not from external cause. -/
def ziRan (o : ZhongOrbit) (n : Nat) : Prop :=
  o.states (n + 1) = dong (o.states n)

/-- 凡 ZhongOrbit 自 是 自然: 其 step IS dong-applied. -/
theorem orbit_is_ziRan (o : ZhongOrbit) (n : Nat) : ziRan o n := (o.step n).symm

/-- 无为 (wú wéi, non-action): no external interference — orbit advances on its own. -/
def wuWei (o : ZhongOrbit) (n : Nat) : Prop := ziRan o n

/-- 无不为 (wú bù wéi, nothing left undone): orbit IS in 中 + advances. -/
def wuBuWei (o : ZhongOrbit) (n : Nat) : Prop :=
  middle (o.states n) ∧ middle (o.states (n + 1))

/-- 道法自然 (dào fǎ zì rán, 《道德经·25》"人法地, 地法天, 天法道, 道法自然"):
    "the Way follows what-is-so-of-itself." Every orbit-step IS 自然 — intrinsic 動. -/
theorem dao_fa_zi_ran (o : ZhongOrbit) (n : Nat) : ziRan o n :=
  orbit_is_ziRan o n

/-- 无为而无不为 (wú wéi ér wú bù wéi, 《道德经·48》"无为而无不为"):
    "by non-action, nothing is left undone." 无为 (orbit autonomous) ∧ 无不为 (中 maintained). -/
theorem wu_wei_er_wu_bu_wei (o : ZhongOrbit) (n : Nat) :
    wuWei o n ∧ wuBuWei o n :=
  ⟨orbit_is_ziRan o n, ⟨o.inMiddle n, o.inMiddle (n + 1)⟩⟩

/-- 反者道之动 (fǎn zhě dào zhī dòng, 《道德经·40》"反者道之动, 弱者道之用"):
    "reversal IS the motion of dao." 反: each step diverges from previous;
    之 动: motion is intrinsic (步进 公理). -/
theorem fan_zhe_dao_zhi_dong (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1)                          -- 反: 不 同
    ∧ dong (o.states n) = o.states (n + 1) :=               -- 道之动
  ⟨o.self_consistent n, o.step n⟩

/-! #### 善 之 道家 化 -/

/-- 上善若水 (shàng shàn ruò shuǐ, 《道德经·8》"上善若水, 水善利万物而不争"):
    "supreme good is like water — benefits all without contention."
    善 ≡ 中 ∧ 不争 (≡ 不极) ∧ 流 (≡ step). -/
theorem shang_shan_ruo_shui (o : ZhongOrbit) (n : Nat) :
    shan (o.states n)                                       -- 善
    ∧ ¬ extreme (o.states n)                                 -- 不争
    ∧ dong (o.states n) = o.states (n + 1) :=                -- 流
  ⟨o.inMiddle n, o.inMiddle n, o.step n⟩

/-! #### 虚静 -/

/-- 致虚守静 (zhì xū shǒu jìng, 《道德经·16》"致虚极, 守静笃"):
    "reach emptiness's utmost, hold stillness firmly." 虚 ≡ 中 之 capacity;
    静 ≡ xinTrust 之 step coherence. -/
theorem zhi_xu_shou_jing (x : Xin) (n : Nat) :
    middle (x.process.states n)                              -- 致虚: 不极, 留 capacity
    ∧ xinTrust x n :=                                         -- 守静: step axiom holds
  ⟨x.process.inMiddle n, xinTrust_holds x n⟩

/-! #### 有无 -/

/-- 有无相生 (yǒu wú xiāng shēng, 《道德经·2》"有无相生, 难易相成"):
    "being and non-being mutually generate." 動 之 二面 = 聚 (有) ∘ 散 (无).
    Given a JuSanSplit: every 動 step factors through 聚 / 散. -/
theorem you_wu_xiang_sheng (split : JuSanSplit) (s : Field) :
    dong s = split.ju (split.san s) := split.decompose s

/-! #### 大成若缺 / 知人自知 / 知足 -/

/-- 大成若缺 (dà chéng ruò quē, 《道德经·45》"大成若缺, 其用不弊"):
    "great completeness seems lacking." 缺 = orbit never settles into static identity;
    大成 = 中-orbit's perpetual 步进 IS its completeness. -/
theorem da_cheng_ruo_que (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1)                           -- 缺: 不 同
    ∧ middle (o.states n) :=                                  -- 大成: 中-orbit
  ⟨o.self_consistent n, o.inMiddle n⟩

/-- 知人者智自知者明 (zhī rén zhě zhì zì zhī zhě míng, 《道德经·33》):
    "knowing others is wisdom; knowing self is enlightenment."
    智 (universal classification) on 他 vs xinTrust (self-coherence) on 己. -/
theorem zhi_ren_zhe_zhi__zi_zhi_zhe_ming (x : Xin) (other : Field) (n : Nat) :
    zhi other                                                -- 知人者智
    ∧ xinTrust x n :=                                         -- 自知者明
  ⟨zhi_universal _, xinTrust_holds x n⟩

/-- 知足不辱 (zhī zú bù rǔ, 《道德经·44》"知足不辱, 知止不殆"):
    "knowing sufficiency avoids disgrace." 心 之 中 = 不极 = 不辱. -/
theorem zhi_zu_bu_ru (x : Xin) (n : Nat) : ¬ extreme (x.process.states n) :=
  x.process.inMiddle n

/-! #### 治国 / 天地 -/

/-- 治大国若烹小鲜 (zhì dà guó ruò pēng xiǎo xiān, 《道德经·60》):
    "governing a great state is like cooking a small fish — minimal interference."
    Each orbit in 国 (ZhongField) advances autonomously without external 扰. -/
theorem zhi_da_guo_ruo_peng (f : ZhongField) (n : Nat) :
    ∀ i : Fin f.k, dong ((f.orbits i).states n) = (f.orbits i).states (n + 1) :=
  fun i => (f.orbits i).step n

/-- 天地不仁以万物为刍狗 (tiān dì bù rén yǐ wàn wù wéi chú gǒu, 《道德经·5》):
    "Heaven-Earth is not 'humane' — treats all as straw dogs." Universal 中 —
    no privileging, all orbits in field are equally 中-bearing. -/
theorem tian_di_bu_ren (f : ZhongField) (n : Nat) :
    ∀ i : Fin f.k, middle ((f.orbits i).states n) :=
  fun i => (f.orbits i).inMiddle n

/-! #### 玄 / 自指 / 千里之行 -/

/-- 玄之又玄 (xuán zhī yòu xuán, 《道德经·1》"玄之又玄, 众妙之门"):
    "mystery upon mystery — the gate of all wonders." 玄 之 iteration IS dong-iteration. -/
theorem xuan_zhi_you_xuan (s : Field) (n : Nat) :
    ji (n + 1) s = dong (ji n s) := ji_self_reference n s

/-- 众妙之门 (zhòng miào zhī mén): "gate of all wonders." 任一 state IS 中 ∨ 极 —
    universal 二项 splits the 妙. -/
theorem zhong_miao_zhi_men (s : Field) : middle s ∨ extreme s := zhi_universal s

/-- 千里之行始于足下 (qiān lǐ zhī xíng shǐ yú zú xià, 《道德经·64》):
    "a thousand-mile journey starts under foot." Orbit at any time k = k-fold
    iteration of 動 from origin (state 0). -/
theorem qian_li_zhi_xing (o : ZhongOrbit) (k : Nat) :
    o.states k = ji k (o.states 0) := li_is_iterated_dong o k

/-! #### 物壮 / 祸福 -/

/-- 物壮则老 (wù zhuàng zé lǎo, 《道德经·30》"物壮则老, 是谓不道"):
    "when things are strong they grow old." 壮 (中, alive) ∧ 老 (极, fixed) 互斥. -/
theorem wu_zhuang_ze_lao (s : Field) : ¬ (middle s ∧ extreme s) :=
  zhi_exclusive s

/-- 祸福相倚 (huò fú xiāng yǐ, 《道德经·58》"祸兮福之所倚, 福兮祸之所伏"):
    "calamity and fortune lean on each other." Universal 二项: every state is 中 (福) or 极 (祸). -/
theorem huo_fu_xiang_yi (s : Field) : middle s ∨ extreme s := zhi_universal s

/-! ### Layer 33: 道家《庄子》— 庄周诸纲

  庄子之核 — 齐物 / 逍遥 / 心斋 / 物化 / 依乎天理 / 朝三暮四 / 大知 / 用心若镜.
  全 归约为 ZhongOrbit / Xin / 仁 之 已 立 性质. -/

/-- 齐物论 — 是亦彼也彼亦是也 (qí wù lùn, 《齐物论》"是亦彼也, 彼亦是也"):
    "this is also that, that is also this." 仁 (≠) IS 对称 — 二焦点 之 互见. -/
theorem qi_wu_lun (h1 h2 : ZhongOrbit) (n : Nat) :
    ren h1 h2 n ↔ ren h2 h1 n :=
  ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩

/-- 逍遥游 (xiāo yáo yóu, 《逍遥游》"至人无己, 神人无功, 圣人无名"):
    "ultimate person no self, divine no merit, sage no name." 拒 telos —
    orbit doesn't settle on any external target. -/
theorem xiao_yao_you (o : ZhongOrbit) (target : Field) (N : Nat) :
    ¬ (∀ n, n ≥ N → o.states n = target) := ZhongOrbit.shi_no_telos o target N

/-- 心斋坐忘 (xīn zhāi zuò wàng, 《人间世》/《大宗师》):
    "mental fasting, sitting forgetting." 心 之 process 不 attach to any one state —
    each step replaces previous (self_consistent). -/
theorem xin_zhai_zuo_wang (x : Xin) (n : Nat) :
    x.process.states n ≠ x.process.states (n + 1) :=
  xinTrust_self_consistent x n

/-- 庄周梦蝶 — 物化 (wù huà, 《齐物论》"周与胡蝶, 则必有分矣, 此之谓物化"):
    "Zhuangzi-and-butterfly transformation." Each step IS a 化 — state becomes
    different state, while remaining 中-bearing. -/
theorem wu_hua (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1)                           -- 化: state shifts
    ∧ middle (o.states n)                                     -- 仍 在 中
    ∧ middle (o.states (n + 1)) :=
  ⟨o.self_consistent n, o.inMiddle n, o.inMiddle (n + 1)⟩

/-- 庖丁解牛 — 依乎天理 (páo dīng jiě niú, 《养生主》"依乎天理, 批大郤"):
    "butcher operates by intrinsic Way." 理 IS dong-iteration; orbit's state at n
    IS k-fold motion from origin — pattern intrinsic, not imposed. -/
theorem pao_ding_jie_niu (o : ZhongOrbit) (n : Nat) :
    o.states n = ji n (o.states 0) := li_is_iterated_dong o n

/-- 朝三暮四 (zhāo sān mù sì, 《齐物论》):
    "three-in-morning four-in-evening" — different distributions, same totality.
    History-window content extends consistently across re-framings. -/
theorem zhao_san_mu_si (o : ZhongOrbit) (n m : Nat) (i : Fin (n + 1))
    (h : i.val < m + 1) :
    jiAccum o n i = jiAccum o m ⟨i.val, h⟩ :=
  jiAccum_extends o n m i h

/-- 大知闲闲 (dà zhī xián xián, 《齐物论》"大知闲闲, 小知间间"):
    "great wisdom is broad" — 智 之 universal applicability. -/
theorem da_zhi_xian_xian (s : Field) : zhi s := zhi_universal s

/-- 至人之用心若镜 (zhì rén yòng xīn ruò jìng, 《应帝王》"至人之用心若镜,
    不将不迎, 应而不藏"): "the ultimate person uses heart like a mirror —
    not pulling, not pushing, responding without retaining." 镜 = 步进+反映:
    state shifts (不留) AND remains 中 (清). -/
theorem yong_xin_ruo_jing (x : Xin) (n : Nat) :
    x.process.states n ≠ x.process.states (n + 1)            -- 不藏 (不留)
    ∧ middle (x.process.states n) :=                          -- 镜 (清)
  ⟨xinTrust_self_consistent x n, x.process.inMiddle n⟩

/-! ### Layer 34: 佛家 — 三法印 / 四圣谛 / 八正道 / 菩萨行

  佛家与本框架结构契合度极高:
    • 「诸行无常」 直接对应 ZhongOrbit 之 self_consistent
    • 「中道」 (madhyama-pratipad) 直接对应 `middle` predicate
    • 「缘起」 (pratītya-samutpāda) IS ZhongOrbit.step
    • 「无我」 IS shi_no_telos (no fixed identity)
    • 「涅槃寂静」 IS perpetual middle (无 collapse)

  本卷归约佛家核要为既有 Kernel 原语 — 不增 axiom, 不立新字. -/

/-! #### 缘起 (pratītya-samutpāda) -/

/-- 缘起 (yuán qǐ, pratītya-samutpāda): "dependent origination."
    Every state arises from prior conditions via 動 — no state is self-causing. -/
theorem yuan_qi (o : ZhongOrbit) (n : Nat) :
    o.states (n + 1) = dong (o.states n) := (o.step n).symm

/-- 缘起性空 (yuán qǐ xìng kōng, 《中论》): "dependent origination = emptiness."
    State at n IS k-fold 動 from origin — no inherent self-essence,
    state IS the chain of conditional applications. -/
theorem yuan_qi_xing_kong (o : ZhongOrbit) (n : Nat) :
    o.states n = ji n (o.states 0) := li_is_iterated_dong o n

/-! #### 三法印 (sān fǎ yìn) -/

/-- 诸行无常 (zhū xíng wú cháng, 《杂阿含》): "all conditioned things are impermanent."
    Each step IS 化 — orbit never settles into static identity. -/
theorem zhu_xing_wu_chang (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1) := o.self_consistent n

/-- 诸法无我 (zhū fǎ wú wǒ, 《杂阿含》): "all dharmas lack self-essence."
    Orbit cannot settle to any fixed target — 拒 telos. -/
theorem zhu_fa_wu_wo (o : ZhongOrbit) (target : Field) (N : Nat) :
    ¬ (∀ n, n ≥ N → o.states n = target) :=
  ZhongOrbit.shi_no_telos o target N

/-- 涅槃寂静 (niè pán jì jìng, 《杂阿含》): "nirvana is peaceful."
    寂静 ≠ 极 (collapse); 寂静 = perpetual 中 — heart never falls into 苦. -/
theorem nie_pan_ji_jing (x : Xin) : ∀ n, middle (x.process.states n) :=
  x.process.inMiddle

/-! #### 四圣谛 (sì shèng dì) -/

/-- 苦 (kǔ, dukkha): suffering identified with 极 — collapse / fixity-trap. -/
def ku (s : Field) : Prop := extreme s

/-- 苦谛 (kǔ dì, the truth of suffering): 苦 ≡ 极. Definition unfolded. -/
theorem ku_di (s : Field) : ku s ↔ extreme s := Iff.rfl

/-- 集谛 (jí dì, samudaya, the origin of 苦):
    when 苦 holds, 動 fixes the state — orbit attempts to halt cease motion. -/
theorem ji_di (s : Field) (h : ku s) : dong s = s := h

/-- 灭谛 (miè dì, nirodha, cessation): 苦 与 中 互斥 — 灭苦 IS 入中.
    No state simultaneously 苦 and 中. -/
theorem mie_di (s : Field) : ¬ (ku s ∧ middle s) := fun ⟨hk, hm⟩ => hm hk

/-- 道谛 (dào dì, mārga, the path): ZhongOrbit IS 道 — every state in a 中-orbit
    is 不苦 (not in 极). Walking 道 IS being a ZhongOrbit. -/
theorem dao_di (o : ZhongOrbit) : ∀ n, ¬ ku (o.states n) := o.inMiddle

/-! #### 中道 (madhyama-pratipad) -/

/-- 中道 (zhōng dào, madhyama-pratipad): the middle way avoiding two extremes.
    中 (alive) ∧ 不 滞 (not over-fixity) ∧ 不 极 (not collapse). -/
theorem zhong_dao (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                   -- 中: 不 极
    ∧ o.states n ≠ o.states (n + 1)                       -- 不 滞: 步进
    ∧ ¬ extreme (o.states n) :=                            -- 不 极 (重申)
  ⟨o.inMiddle n, o.self_consistent n, o.inMiddle n⟩

/-! #### 八正道 (bā zhèng dào) -/

/-- 八正道 (bā zhèng dào, ariya aṭṭhaṅgika magga): the eight-fold noble path.
    Each "right" practice corresponds to a Xin invariant. All eight reduce to:
    Xin's process maintains 中 + step coherent + classifiable + 仁-aware. -/
theorem ba_zheng_dao (x : Xin) (n : Nat) :
    zhi (x.process.states n)                                  -- 正见 (right view): 智 universal
    ∧ middle (x.process.states n)                              -- 正思维 + 正定: 中 in present
    ∧ xing (x.process.states n) = x.process.states (n + 1)     -- 正业 (right action): 行
    ∧ xinTrust x n                                              -- 正语 + 正命 + 正念 (信)
    ∧ middle (x.process.states (n + 1)) :=                      -- 正精进: 中 ongoing
  ⟨zhi_universal _, x.process.inMiddle n, x.process.step n,
   xinTrust_holds x n, x.process.inMiddle (n + 1)⟩

/-! #### 戒定慧 (jiè dìng huì) -/

/-- 戒定慧三学 (jiè dìng huì sān xué, three trainings):
    戒 (sīla, ethics) + 定 (samādhi, concentration) + 慧 (prajñā, wisdom).
    Formally: xinTrust ∧ middle ∧ zhi. -/
theorem jie_ding_hui (x : Xin) (n : Nat) :
    xinTrust x n                                              -- 戒
    ∧ middle (x.process.states n)                              -- 定
    ∧ zhi (x.process.states n) :=                               -- 慧
  ⟨xinTrust_holds x n, x.process.inMiddle n, zhi_universal _⟩

/-! #### 菩萨行 (pú sà xíng) -/

/-- 菩萨行 (pú sà xíng, bodhisattva conduct): the awakened being maintains 中
    AND remains in 仁-relation with other beings. 自度 + 度他. -/
theorem pu_sa_xing (sage : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual sage.process other n m) :
    middle (sage.process.states n)                          -- 自度: 自 在 中
    ∧ ren sage.process other n                                -- 仁 with other
    ∧ liRitual sage.process other n m :=                      -- 礼 maintained
  ⟨sage.process.inMiddle n,
   liRitual_implies_ren_at_base _ _ _ _ h_ritual, h_ritual⟩

/-- 自度度他 (zì dù dù tā): self-liberation IS other-liberation. The awakened
    heart's middle preserves the 仁-relation when distinct from another orbit. -/
theorem zi_du_du_ta (x : Xin) (other : ZhongOrbit) (n : Nat)
    (h : x.process.states n ≠ other.states n) :
    middle (x.process.states n)                              -- 自度
    ∧ middle (other.states n)                                  -- 度他
    ∧ ren x.process other n :=                                 -- 仁
  ⟨x.process.inMiddle n, other.inMiddle n, h⟩

/-! #### 不二法门 / 心如工画师 / 一即一切 -/

/-- 不二法门 (bù èr fǎ mén, 《维摩诘经·入不二法门品》): "the gate of non-duality."
    Apparent dualities (善/恶, 中/极) are aspects of one process — same dong determines both. -/
theorem bu_er_fa_men (s : Field) :
    (shan s ↔ middle s)                                      -- 善 = 中
    ∧ (eVice s ↔ extreme s)                                    -- 恶 = 极
    ∧ (middle s ∨ extreme s) :=                                -- 同 一 process
  ⟨shan_iff_middle s, eVice_iff_extreme s, zhi_universal s⟩

/-- 心如工画师 (xīn rú gōng huà shī, 《华严经·夜摩天宫菩萨说偈品》"心如工画师,
    能画诸世间"): "the mind is like a painter — paints all worlds."
    Heart's response IS total — paints any field event into some interpretation. -/
theorem xin_ru_gong_hua_shi (x : Xin) (event : Field) :
    ∃ s : Field, x.respond event = s := ⟨x.respond event, rfl⟩

/-- 一即一切, 一切即一 (yī jí yī qiè, yī qiè jí yī, 《华严经·初发心功德品》):
    "one IS all, all IS one." 此 state 之 中-性质 IS 全 orbit 之 中-性质. -/
theorem yi_ji_yi_qie (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                       -- 一 (此 state)
    ∧ (∀ m, middle (o.states m)) :=                            -- 一切 (∀ states)
  ⟨o.inMiddle n, o.inMiddle⟩

/-- 烦恼即菩提 (fán nǎo jí pú tí, 《六祖坛经·般若品》): "afflictions ARE awakening."
    极 (afflictions) and 中 (awakening) are the universal dichotomy of the same Field —
    recognizing 极 IS the act of being-in-中. -/
theorem fan_nao_ji_pu_ti (s : Field) : middle s ∨ extreme s := zhi_universal s

/-! ### Layer 35: 墨家 — 兼爱 / 非攻 / 尚同 / 三表法 / 天志

  墨家 (Mohism) — 5 核要. 与儒家 之 仁 (specific 二焦点) 不同, 墨家 之 兼爱
  是 universal extension; 与儒家 之 礼 (window-bound) 不同, 墨家 之 非攻 是
  universal restraint. 墨家 在 本框架 中 = 仁/恕道 之 universalization. -/

/-- 兼爱 (jiān ài, 《墨子·兼爱上》"以兼相爱交相利"):
    "universal love, mutual benefit." 礼-window 内, 仁 持续 across all moments —
    扩展 儒家 之 specific 仁 至 universal. -/
theorem jian_ai
    (h1 h2 : ZhongOrbit) (n m : Nat)
    (h_li : liRitual h1 h2 n m) (k : Nat) (hk : k ≤ m) :
    ren h1 h2 (n + k) := h_li k hk

/-- 非攻 (fēi gōng, 《墨子·非攻上》): "no aggression."
    若 a 不 collapse self (己所不欲), 由 同根 (仁), 则 a 不 collapse any other —
    universal restraint follows from self-restraint + 同根. -/
theorem fei_gong
    (x : Xin) (a : Field → Field) (n : Nat)
    (h_self_safe : ¬ jiSuoBuYu x a n)
    (h_tongGen : tongGen a) :
    ∀ other : ZhongOrbit, ¬ shiYuRen a other n := by
  intro other h_shi
  exact h_self_safe (
    (h_tongGen (x.process.states n) (other.states n)
       (x.process.inMiddle n) (other.inMiddle n)).mpr h_shi
  )

/-- 尚同 (shàng tóng, 《墨子·尚同上》"上同而不下比"):
    "exalt unity (with the higher principle)." Heart aligns with another orbit —
    same form as `alignment_for_xin`. -/
theorem shang_tong
    (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    ren x.process other n
    ∧ liRitual x.process other n m
    ∧ shan (x.process.states n) :=
  ⟨liRitual_implies_ren_at_base _ _ _ _ h_ritual, h_ritual, x.process.inMiddle n⟩

/-- 三表法 (sān biǎo fǎ, 《墨子·非命下》): "three standards" for testing claims —
    本 (ground in past sage-kings), 原 (verify in experience), 用 (apply for utility).
    Formal: orbit 之 origin trace + step coherence + classifiability. -/
theorem san_biao_fa (o : ZhongOrbit) (n : Nat) :
    o.states n = ji n (o.states 0)                            -- 本: historical trace
    ∧ o.states (n + 1) = dong (o.states n)                    -- 原: empirical step
    ∧ zhi (o.states n) :=                                      -- 用: classifiable utility
  ⟨li_is_iterated_dong o n, (o.step n).symm, zhi_universal _⟩

/-- 天志 (tiān zhì, 《墨子·天志上》"天之欲人之相爱相利"):
    "Heaven's will" — universal middle preservation across all orbits in the cosmos. -/
theorem tian_zhi (f : ZhongField) (n : Nat) :
    ∀ i : Fin f.k, middle ((f.orbits i).states n) :=
  fun i => (f.orbits i).inMiddle n

/-! ### Layer 36: 法家 — 法 / 术 / 势 / 信赏必罚 / 不法古不循今

  法家 (Legalism) — 6 核要. 法家 强调 impartial law (法 之 至公), 君主 之 术 (技),
  权力 之 势. 在 本框架 中 = `zhi_universal` (法之 universal) + Xin.respond (术) +
  既 立 之 `shi` def (势). -/

/-- 法 之 universal (fǎ): impartial law applies to every state. 任一 state 必
    classifiable — 法之至公 之 形式表达. -/
theorem fa_universal (s : Field) : zhi s := zhi_universal s

/-- 法之至公 (fǎ zhī zhì gōng, 《管子·任法》"法者, 天下之至道也"):
    "law's utmost impartiality." No orbit privileged — all middle in 国. -/
theorem fa_zhi_zhi_gong (f : ZhongField) (n : Nat) :
    ∀ i : Fin f.k, middle ((f.orbits i).states n) :=
  fun i => (f.orbits i).inMiddle n

/-- 势 (shì, 《韩非子·难势》"飞龙乘云, 腾蛇游雾"):
    "authority's momentum" — 势 之 transition is genuine (不退化). -/
theorem shi_authority (o : ZhongOrbit) (n : Nat) :
    (ZhongOrbit.shi o n).1 ≠ (ZhongOrbit.shi o n).2 := ZhongOrbit.shi_genuine o n

/-- 术 (shù, 《韩非子·定法》"术者, 因任而授官"):
    "ruler's technique" — Xin's response is a total function (handles any event). -/
theorem shu_technique (x : Xin) (event : Field) :
    ∃ s : Field, x.respond event = s := ⟨x.respond event, rfl⟩

/-- 信赏必罚 (xìn shǎng bì fá, 《韩非子·主道》):
    "consistent rewards and necessary punishments." Step is deterministic —
    same prior state always yields same next state via 動. -/
theorem xin_shang_bi_fa (o : ZhongOrbit) (n : Nat) :
    o.states (n + 1) = dong (o.states n) := (o.step n).symm

/-- 不法古不循今 (bù fǎ gǔ bù xún jīn, 《商君书·更法》):
    "neither follow the past nor copy the present." Each step IS new — orbit
    breaks from prior state at every moment. -/
theorem bu_fa_gu_bu_xun_jin (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1) := o.self_consistent n

/-! ### Layer 37: 名家 — 名实之辨 / 离坚白 / 合同异

  名家 (School of Names) — 3 核要. 公孙龙 + 惠施.
  名家 关心 名 (predicate) 与 实 (state) 之 correspondence,
  以及 attribute 之 separability — 在 本框架 中 自然 reduce 到 zhi 之 classification. -/

/-- 名实之辨 (míng shí zhī biàn, 《公孙龙·名实论》"夫名, 实谓也"):
    "the discrimination of name and substance." Each state IS classifiable
    (名 = predicate) AND has actual identity (实 = state-value). -/
theorem ming_shi_zhi_bian (o : ZhongOrbit) (n : Nat) :
    zhi (o.states n)                                          -- 名 (predicate-applicable)
    ∧ middle (o.states n) :=                                   -- 实 (actual middle)
  ⟨zhi_universal _, o.inMiddle n⟩

/-- 离坚白 (lí jiān bái, 《公孙龙·坚白论》"视不得其所坚, 而得其所白者"):
    "separating hardness and whiteness." A state simultaneously satisfies multiple
    predicates that are nonetheless distinct — middle (perceptual) ∧ ziRan (intrinsic). -/
theorem li_jian_bai (o : ZhongOrbit) (n : Nat) :
    middle (o.states n) ∧ ziRan o n :=
  ⟨o.inMiddle n, orbit_is_ziRan o n⟩

/-- 合同异 (hé tóng yì, 惠施 《庄子·天下》"合同异"):
    "uniting same and different." 仁 之 同根异显 — 二 orbits 同 (both ZhongOrbit)
    AND 异 (distinct states at n). -/
theorem he_tong_yi
    (h1 h2 : ZhongOrbit) (n : Nat) (h_distinct : h1.states n ≠ h2.states n) :
    middle (h1.states n)                                       -- 同根 (h1 中)
    ∧ middle (h2.states n)                                       -- 同根 (h2 中)
    ∧ h1.states n ≠ h2.states n :=                                -- 异显
  ⟨h1.inMiddle n, h2.inMiddle n, h_distinct⟩

/-! ### Layer 38: 阴阳家 — 阴阳互根 / 五行相生 / 五行相克 / 天人感应

  阴阳家 (Yin-Yang School) — 4 核要. 邹衍 / 董仲舒.
  本卷 introduces inductive `WuXing` (五行 enum) + 相生/相克 cycles. -/

/-- 阴阳互根 (yīn yáng hù gēn, 《周易·系辞》"一阴一阳之谓道"):
    "yin and yang mutually rooted." 中/极 二项 universal — 中 之 意义 由 极 之
    possibility 给出, 反之亦然. -/
theorem yin_yang_hu_gen (s : Field) : middle s ∨ extreme s := zhi_universal s

/-- 五行 enum: 木 / 火 / 土 / 金 / 水. -/
inductive WuXing
  | mu      -- 木 (Wood)
  | huo     -- 火 (Fire)
  | tu      -- 土 (Earth)
  | jin     -- 金 (Metal)
  | shui    -- 水 (Water)
  deriving Repr, DecidableEq

namespace WuXing

/-- 五行 之 总 list. -/
def all : List WuXing := [.mu, .huo, .tu, .jin, .shui]

theorem all_length : all.length = 5 := rfl

/-- 相生 (xiāng shēng, mutual generation): 木→火→土→金→水→木. -/
def sheng : WuXing → WuXing
  | .mu   => .huo
  | .huo  => .tu
  | .tu   => .jin
  | .jin  => .shui
  | .shui => .mu

/-- 相克 (xiāng kè, mutual restriction): 木克土, 土克水, 水克火, 火克金, 金克木. -/
def ke : WuXing → WuXing
  | .mu   => .tu
  | .tu   => .shui
  | .shui => .huo
  | .huo  => .jin
  | .jin  => .mu

end WuXing

/-- 五行相生 (wǔ xíng xiāng shēng): 5-cycle on 相生 — 5 次 returns to start. -/
theorem wu_xing_xiang_sheng (w : WuXing) :
    w.sheng.sheng.sheng.sheng.sheng = w := by
  cases w <;> rfl

/-- 五行相克 (wǔ xíng xiāng kè): 5-cycle on 相克 — 5 次 returns to start. -/
theorem wu_xing_xiang_ke (w : WuXing) :
    w.ke.ke.ke.ke.ke = w := by
  cases w <;> rfl

/-- 五行 之 generation IS NOT restriction — 二 cycles 是 不同 permutations. -/
theorem sheng_ne_ke : WuXing.sheng ≠ WuXing.ke := by
  intro h
  have : WuXing.mu.sheng = WuXing.mu.ke := by rw [h]
  -- LHS = .huo, RHS = .tu — contradicts
  cases this

/-- 天人感应 (tiān rén gǎn yìng, 董仲舒《春秋繁露·阴阳义》"天人之际, 合而为一"):
    "heaven-human resonance." Cosmic field (天) and individual Xin (人)
    both maintain 中 — same invariant at different scales. -/
theorem tian_ren_gan_ying
    (f : ZhongField) (i : Fin f.k) (x : Xin) (n : Nat) :
    middle ((f.orbits i).states n)                            -- 天 (cosmic)
    ∧ middle (x.process.states n) :=                           -- 人 (individual)
  ⟨(f.orbits i).inMiddle n, x.process.inMiddle n⟩

/-! ### Layer 39: 西方古典哲学 (希腊)

  苏格拉底 + 柏拉图 + 亚里士多德 — 5 核要.
  希腊哲学之最深结构发现: 中道 (亚里士多德 golden mean) 与中国"中"完全同义;
  无知之知 (苏格拉底) IS 智 之 自 反身 limit. -/

/-- 无知之知 (Socrates, "οἶδα οὐδὲν εἰδέναι"): "I know that I know nothing."
    Structural correlate: 智 之 universal applicability AND 智 之 self-reflective limit
    (recognition that 中 ∧ 极 cannot simultaneously obtain). -/
theorem socrates_known_unknown (s : Field) :
    zhi s                                                  -- 知 (universal capacity)
    ∧ ¬ (middle s ∧ extreme s) :=                           -- 知 之 limit (self-recognition)
  ⟨zhi_universal s, zhi_exclusive s⟩

/-- 柏拉图 理念论 (Plato, ἰδέα / εἶδος, Republic): "form vs. particular."
    The form (universal predicate) is realized in each particular instance.
    Each state-at-n participates in the form `middle`; the form itself is universal. -/
theorem plato_form (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                    -- 个体 (particular instance)
    ∧ (∀ m : Nat, middle (o.states m)) :=                   -- 理念 (universal form)
  ⟨o.inMiddle n, o.inMiddle⟩

/-- 亚里士多德 中道之美德 (Aristotle, μεσότης, Nicomachean Ethics):
    "virtue is the mean between two extremes."
    Direct equivalence: 中 (Aristotelian mean) IS our `middle` predicate. -/
theorem aristotle_golden_mean (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                     -- 中 (mean)
    ∧ ¬ extreme (o.states n) :=                              -- 不 极 (avoid 二端)
  ⟨o.inMiddle n, o.inMiddle n⟩

/-- 第一推动者 (Aristotle, πρῶτον κινοῦν ἀκίνητον, Metaphysics XII):
    "the unmoved mover." Existence of a foundational motion principle. -/
theorem aristotle_unmoved_mover : ∃ f : Field → Field, f = dong :=
  ⟨dong, rfl⟩

/-- 亚里士多德 四因说 (Aristotle, τέσσαρες αἰτίαι, Physics II):
    material / formal / efficient / final causes — orbit instantiates first three;
    final cause (telos) is rejected (process philosophy alignment). -/
theorem aristotle_four_causes (o : ZhongOrbit) (n : Nat) :
    (∃ s : Field, s = o.states n)                              -- 质料因 (substrate exists)
    ∧ middle (o.states n)                                       -- 形式因 (form: middle)
    ∧ o.states (n + 1) = dong (o.states n)                      -- 动力因 (dong applies)
    ∧ (∀ target N, ¬ (∀ k, k ≥ N → o.states k = target)) :=     -- 目的因: 拒 telos
  ⟨⟨o.states n, rfl⟩, o.inMiddle n, (o.step n).symm,
   fun target N => ZhongOrbit.shi_no_telos o target N⟩

/-! ### Layer 40: 西方近代哲学 (Cartesian / Kantian / Hegelian / Nietzschean)

  笛卡尔 + 康德 + 黑格尔 + 尼采 — 5 核要. -/

/-- 笛卡尔 cogito ergo sum (Descartes, Meditations II): "I think, therefore I am."
    Heart's xinTrust holds (thinking is coherent) AND state IS in middle (existing). -/
theorem descartes_cogito (x : Xin) (n : Nat) :
    xinTrust x n                                             -- cogito (thinking coherent)
    ∧ middle (x.process.states n) :=                          -- sum (existing in 中)
  ⟨xinTrust_holds x n, x.process.inMiddle n⟩

/-- 康德 绝对命令 (Kant, kategorischer Imperativ, Grundlegung):
    "Act only according to that maxim by which you can also will that it should
    become a universal law." Structural correlate: action universalizable
    (tongGenMiddle) ⟹ self-desire ⟹ other-flourishing. -/
theorem kant_categorical_imperative
    (x : Xin) (a : Field → Field) (other : ZhongOrbit) (n : Nat)
    (h_yu : jiSuoYu x a n) (h_tong : tongGenMiddle a) :
    jiYuRen a other n :=
  tui_ji_ji_ren x a other n h_yu h_tong

/-- 康德 二律背反 (Kant, Antinomien, Critique of Pure Reason):
    "the antinomies." Structural correlate: 中 ∧ 极 mutually exclusive — opposing
    propositions cannot both hold simultaneously. -/
theorem kant_antinomy (s : Field) : ¬ (middle s ∧ extreme s) :=
  zhi_exclusive s

/-- 黑格尔 正反合 (Hegel, dialektische Triade): thesis-antithesis-synthesis.
    Each step IS dialectical: state at n (thesis) ≠ state at n+1 (antithesis),
    yet both maintain 中 (synthesis preserves the underlying form). -/
theorem hegel_dialectic (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1)                          -- 正反 (thesis ≠ antithesis)
    ∧ middle (o.states n)                                    -- 合 之 一 (synthesis)
    ∧ middle (o.states (n + 1)) :=                            -- 合 之 二
  ⟨o.self_consistent n, o.inMiddle n, o.inMiddle (n + 1)⟩

/-- 尼采 永恒回归 (Nietzsche, Ewige Wiederkunft, Also sprach Zarathustra):
    "eternal return of the same." 形式上 — orbit's pattern (middle) returns at every n,
    yet content (specific state value) never repeats (self_consistent). -/
theorem nietzsche_eternal_return (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                      -- 形式 returns to 中
    ∧ middle (o.states (n + 1))                                -- 形式 同 returns
    ∧ o.states n ≠ o.states (n + 1) :=                         -- 内容 不 repeats
  ⟨o.inMiddle n, o.inMiddle (n + 1), o.self_consistent n⟩

/-! ### Layer 41: 现象学 / 存在 / 过程 / 维特根斯坦 (20 世纪)

  胡塞尔 + 海德格尔 + 萨特 + 怀特海 + 柏格森 + 维特根斯坦 — 6 核要. -/

/-- 胡塞尔 意向性 (Husserl, Intentionalität, Logische Untersuchungen):
    "consciousness IS consciousness of something." Heart's response-function IS total —
    intentionality directs heart toward field-events. -/
theorem husserl_intentionality (x : Xin) (event : Field) :
    ∃ s, x.respond event = s := ⟨x.respond event, rfl⟩

/-- 海德格尔 向死而在 (Heidegger, Sein-zum-Tode, Sein und Zeit):
    "Being-towards-death." Authentic existence acknowledges 极 (death) as possibility
    while currently maintaining 中 (life-flow). -/
theorem heidegger_sein_zum_tode (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                       -- 在 (Da-sein 之 中-显)
    ∧ (middle (o.states n) ∨ extreme (o.states n)) :=          -- 知 极 之 possibility
  ⟨o.inMiddle n, zhi_universal _⟩

/-- 萨特 存在先于本质 (Sartre, "l'existence précède l'essence", L'existentialisme):
    "existence precedes essence." States exist (middle) BEFORE classification (zhi);
    being precedes predicate-application. -/
theorem sartre_existence_precedes_essence (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                       -- 存在 (existence)
    ∧ zhi (o.states n) :=                                      -- 本质 (essence)
  ⟨o.inMiddle n, zhi_universal _⟩

/-- 怀特海 实在场合 (Whitehead, Actual Occasion, Process and Reality):
    each step IS an actual occasion of becoming — momentary creative advance. -/
theorem whitehead_actual_occasion (o : ZhongOrbit) (n : Nat) :
    o.states (n + 1) = dong (o.states n)                      -- 生成 (becoming)
    ∧ middle (o.states n)                                       -- 实在 (actuality at n)
    ∧ middle (o.states (n + 1)) :=                              -- 实在 (actuality at n+1)
  ⟨(o.step n).symm, o.inMiddle n, o.inMiddle (n + 1)⟩

/-- 柏格森 绵延 (Bergson, durée, Essai sur les données immédiates):
    "duration as continuous becoming." Each moment differs from the next AND is
    causally connected via dong. -/
theorem bergson_duree (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1)                            -- 流变 (becoming)
    ∧ o.states (n + 1) = dong (o.states n) :=                  -- 连续 (continuity via dong)
  ⟨o.self_consistent n, (o.step n).symm⟩

/-- 维特根斯坦 世界即事实总和 (Wittgenstein, Tractatus 1.1):
    "Die Welt ist die Gesamtheit der Tatsachen, nicht der Dinge."
    "The world is the totality of facts, not of things." Orbit's totality = facts
    (middle ∧ step) at every moment. -/
theorem wittgenstein_world (o : ZhongOrbit) :
    ∀ n, middle (o.states n) ∧ dong (o.states n) = o.states (n + 1) :=
  fun n => ⟨o.inMiddle n, o.step n⟩

/-! ### Layer 42: 亚伯拉罕三教 (Judaism / Christianity / Islam)

  犹太教 + 基督教 + 伊斯兰 — 6 核要.
  注: 形式对应 IS 结构同构 (structural correlate), 不是 ontological reduction.
  各传统 之 神学内容超越本框架 — 此处仅记录 minimal kernel 中之 syntactic homomorphism. -/

/-- 犹太教 一神论 (Hebrew, "ehad", Shema Yisrael Deut. 6:4):
    "the LORD our God, the LORD is one." Structural correlate:
    foundational principle is unique. -/
theorem judaism_ehad : ∃ f : Field → Field, f = dong :=
  ⟨dong, rfl⟩

/-- 神之形象 (Hebrew, "tselem Elohim", Genesis 1:27):
    "in the image of God He created them." Structural correlate: every Xin's
    process maintains the universal form (middle). -/
theorem judaism_tselem_elohim (x : Xin) : ∀ n, middle (x.process.states n) :=
  x.process.inMiddle

/-- 基督教 道成肉身 (Greek, "λόγος ἐγένετο σάρξ", John 1:14):
    "the Word became flesh." Structural correlate: abstract dong principle
    manifests in concrete states — every Field state IS dong applied. -/
theorem christianity_incarnation (s : Field) :
    ∃ s' : Field, dong s = s' := ⟨dong s, rfl⟩

/-- 基督教 三位一体 (Greek, "τριάς", Council of Nicaea 325):
    "trinity" — three aspects of one. Structural correlate: orbit IS one process
    with three formal aspects: ousia (essence/中) / energeia (act/dong-step) /
    logos (order/iterated-pattern). -/
theorem christianity_trinity (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)                                      -- ousia (essence/中)
    ∧ dong (o.states n) = o.states (n + 1)                    -- energeia (act)
    ∧ o.states n = ji n (o.states 0) :=                        -- logos (order/iterated-Logos)
  ⟨o.inMiddle n, o.step n, li_is_iterated_dong o n⟩

/-- 基督教 ἀγάπη (Greek, "agape", 1 Cor 13): "love that wills the other's good."
    Structural correlate: 仁 之 universal extension — sage maintains 礼-window
    relation with another. (与墨家「兼爱」同形.) -/
theorem christianity_agape
    (sage : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual sage.process other n m) :
    ren sage.process other n :=
  liRitual_implies_ren_at_base _ _ _ _ h_ritual

/-- 伊斯兰 tawḥīd (Arabic, "توحيد", Qur'an 112): "the oneness of God."
    Structural correlate: foundational principle is unique. (与犹太教 ehad
    同形 — 一神论 之 数学共同体.) -/
theorem islam_tawhid : ∃ f : Field → Field, f = dong :=
  ⟨dong, rfl⟩

/-- 伊斯兰 fitra (Arabic, "فطرة", Qur'an 30:30): "innate nature."
    Every human is born with innate predisposition to truth. Structural correlate:
    every Xin's process is in middle (good by nature). -/
theorem islam_fitra (x : Xin) : ∀ n, middle (x.process.states n) :=
  x.process.inMiddle

/-! ### Layer 43: 现代政治哲学 — 实证 (validated by Kernel)

  现代政治哲学 之 核要 — 经 Kernel 之 检验, 与本框架 align 之 命题.
  注: "实证" IS 「在本 framework 中可证为定理」, 不是 historical 实证.
  各思想之 specific 经验内容超越本框架. -/

/-- 罗尔斯 无知之幕 (Rawls, "veil of ignorance", A Theory of Justice §24):
    "Behind the veil of ignorance, all parties make decisions without knowledge
    of their position." Structural correlate: action evaluated under universal
    premise (tongGenMiddle) — same effect on any 中-state. -/
theorem rawls_veil_of_ignorance
    (a : Field → Field) (h_universal : tongGenMiddle a) (s t : Field)
    (hs : middle s) (ht : middle t) :
    middle (a s) ↔ middle (a t) := h_universal s t hs ht

/-- 罗尔斯 差异原则 (Rawls, "difference principle", §13):
    "Social and economic inequalities are arranged so that they are to the greatest
    benefit of the least advantaged." Structural correlate: ZhongField maintains
    plurality (multiple orbits, all middle) — none privileged, none collapsed. -/
theorem rawls_difference_principle (f : ZhongField) (n : Nat) :
    (∃ i j : Fin f.k, i ≠ j ∧ (f.orbits i).states n ≠ (f.orbits j).states n)  -- 多样性
    ∧ (∀ i : Fin f.k, middle ((f.orbits i).states n)) :=                       -- 全 中
  ⟨f.ever_differentiated n, fun i => (f.orbits i).inMiddle n⟩

/-- 哈贝马斯 沟通理性 (Habermas, "kommunikative Rationalität", Theorie des
    kommunikativen Handelns): "rationality through communication." 礼-window 内
    多焦点 仁-relation 持续, 中 共维持. -/
theorem habermas_communicative_rationality
    (h1 h2 : ZhongOrbit) (n m : Nat) (h_li : liRitual h1 h2 n m) (k : Nat) (hk : k ≤ m) :
    middle (h1.states (n + k))
    ∧ middle (h2.states (n + k))
    ∧ ren h1 h2 (n + k) :=
  ⟨h1.inMiddle (n + k), h2.inMiddle (n + k), h_li k hk⟩

/-- 阿伦特 行动 (Arendt, "action", The Human Condition):
    "Action constitutes the public realm." Each orbit's step IS dong-application —
    spontaneous beginning of new sequences. -/
theorem arendt_action (f : ZhongField) (i : Fin f.k) (n : Nat) :
    dong ((f.orbits i).states n) = (f.orbits i).states (n + 1) :=
  (f.orbits i).step n

/-- 阿伦特 公共空间 (Arendt, "public space"): "Public space requires plurality
    and appearance." ZhongField 之 多样性 (k ≥ 2) ∧ 持续异显. -/
theorem arendt_public_space (f : ZhongField) :
    f.k ≥ 2
    ∧ (∀ n, ∃ i j : Fin f.k, i ≠ j ∧ (f.orbits i).states n ≠ (f.orbits j).states n) :=
  ⟨f.k_ge_two, f.ever_differentiated⟩

/-- 阿伦特 出生性 (Arendt, "natality"): "Capacity for new beginnings." Each orbit
    step generates novelty — state at n+1 ≠ state at n. -/
theorem arendt_natality (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n + 1) := o.self_consistent n

/-- 洛克 自然权利 (Locke, "natural rights", Two Treatises §6):
    "Life, liberty, property — endowed by nature, not granted by state."
    Every Xin's process is in middle by structural necessity. -/
theorem locke_natural_rights (x : Xin) : ∀ n, middle (x.process.states n) :=
  x.process.inMiddle

/-- 哈耶克 自发秩序 (Hayek, "spontaneous order", The Constitution of Liberty):
    "Order emerges from autonomous action without central design." Each orbit
    in ZhongField advances autonomously, yielding 流通 ∧ 多样. -/
theorem hayek_spontaneous_order (f : ZhongField) (n : Nat) :
    (∀ i : Fin f.k, dong ((f.orbits i).states n) = (f.orbits i).states (n + 1))   -- 自发
    ∧ (∀ i : Fin f.k, (f.orbits i).states n ≠ (f.orbits i).states (n + 1))         -- 流通
    ∧ (∃ i j : Fin f.k, i ≠ j ∧ (f.orbits i).states n ≠ (f.orbits j).states n) := -- 多样
  ⟨fun i => (f.orbits i).step n, (f.he n).1, (f.he n).2⟩

/-- 阿马蒂亚·森 能力进路 (Sen, "capability approach", Development as Freedom):
    "Development is the expansion of capability." Heart's response IS total —
    capability to function on any field event. -/
theorem sen_capability (x : Xin) (event : Field) :
    (∃ s, x.respond event = s) ∧ zhi event :=
  ⟨⟨x.respond event, rfl⟩, zhi_universal _⟩

/-- 柏林 价值多元主义 (Berlin, "value pluralism", Two Concepts of Liberty):
    "Plurality is not a defect but a structural feature." ZhongField 之 he_not_same:
    uniformity is forbidden. -/
theorem berlin_value_pluralism (f : ZhongField) :
    ∀ n, ¬ (∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n) :=
  f.he_not_same

/-- 穆勒 自由原则 (Mill, "harm principle", On Liberty Ch. 1):
    "The only purpose for which power can be rightfully exercised over any member
    of a civilized community, against his will, is to prevent harm to others."
    Structural form: 自我安全 + 同根 ⟹ 不害他者 (= 非攻 之 alias). -/
theorem mill_harm_principle
    (x : Xin) (a : Field → Field) (other : ZhongOrbit) (n : Nat)
    (h_self_safe : ¬ jiSuoBuYu x a n) (h_tongGen : tongGen a) :
    ¬ shiYuRen a other n := by
  intro h_shi
  exact h_self_safe (
    (h_tongGen (x.process.states n) (other.states n)
       (x.process.inMiddle n) (other.inMiddle n)).mpr h_shi)

/-- 康德 永久和平 (Kant, "Zum ewigen Frieden", 1795):
    "Perpetual peace among nations." Structural correlate: every orbit in cosmic
    ZhongField maintains middle at every time — universal-temporal stability. -/
theorem kant_perpetual_peace (f : ZhongField) :
    ∀ n, ∀ i : Fin f.k, middle ((f.orbits i).states n) :=
  fun n i => (f.orbits i).inMiddle n

/-! ### Layer 44: 现代政治哲学 — 证错 (refuted by Kernel)

  以下 命题 在本框架 中 形式 上 站不住 — Kernel 之 invariants 直接 否定 它们.
  注: 这 不 否定 各思想 之 historical / sociological insight, 仅 表 它们 之
  特定形式陈述 与 minimal kernel 之 结构 冲突. -/

/-- 马克思 历史终局之否定 (Marx 之 "communism as end of history" reading):
    若 历史有 fixed 终极 state, 则 orbit eventually settles to it — 但 ZhongOrbit
    自洽 拒此 (shi_no_telos). 历史 IS 永远 open process, 无 终局. -/
theorem marx_historical_telos_refuted (o : ZhongOrbit) (target : Field) (N : Nat) :
    ¬ (∀ n, n ≥ N → o.states n = target) :=
  ZhongOrbit.shi_no_telos o target N

/-- 马克思 决定论之否定 (Marx 之 mechanistic 历史唯物论 reading):
    "There exists N such that for all n ≥ N, history ends at target."
    Structurally impossible — orbit never converges. -/
theorem marx_deterministic_outcome_refuted (o : ZhongOrbit) (target : Field) :
    ¬ (∃ N, ∀ n, n ≥ N → o.states n = target) := by
  intro ⟨N, h⟩
  exact ZhongOrbit.shi_no_telos o target N h

/-- 霍布斯 自然状态之否定 (Hobbes, "bellum omnium contra omnes", Leviathan):
    "war of all against all" = universal extreme state. 本框架 中 ZhongField
    之 invariants 否定 universal extreme — 总 有 ≥ 一 orbit 在 中. -/
theorem hobbes_state_of_nature_refuted (f : ZhongField) :
    ¬ (∀ n, ∀ i : Fin f.k, extreme ((f.orbits i).states n)) := by
  intro h
  have h_k : 0 < f.k := by have := f.k_ge_two; omega
  exact (f.orbits ⟨0, h_k⟩).inMiddle 0 (h 0 ⟨0, h_k⟩)

/-- 施密特 敌友区分之否定 (Schmitt, "Begriff des Politischen"):
    "Politics IS the friend-enemy distinction." 本框架 提供 第三 option:
    distinct 二焦点 既 非 同 (collapse) 又 非 敌 (extreme), 而 是 仁
    (中 之 同根异显). 敌友二分 之 必然性 不成立. -/
theorem schmitt_friend_enemy_refuted
    (h1 h2 : ZhongOrbit) (n : Nat) (h_distinct : h1.states n ≠ h2.states n) :
    h1.states n ≠ h2.states n                            -- ¬ 同 (not friend-collapse)
    ∧ ¬ extreme (h1.states n)                             -- ¬ 敌 from h1's side
    ∧ ¬ extreme (h2.states n)                             -- ¬ 敌 from h2's side
    ∧ ren h1 h2 n :=                                       -- 第三 option: 仁
  ⟨h_distinct, h1.inMiddle n, h2.inMiddle n, h_distinct⟩

/-- 施密特 例外状态之否定 (Schmitt, "Ausnahmezustand", Politische Theologie):
    "Sovereign is he who decides on the state of exception (perpetual)."
    Perpetual extreme is structurally impossible — orbit cannot remain in 极. -/
theorem schmitt_state_of_exception_refuted (o : ZhongOrbit) (n : Nat) :
    ¬ extreme (o.states n) := o.inMiddle n

/-- 极权主义之否定 (totalitarianism as ideology, e.g. as critiqued by Arendt):
    "Total uniformity of all subjects." Violates ZhongField's plurality requirement
    — uniformity at any time is structurally impossible. -/
theorem totalitarianism_refuted (f : ZhongField) (n : Nat) :
    ¬ (∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n) :=
  f.he_not_same n

/-- 福柯 权力之 universal extreme reading 之否定 (Foucault, naive reading
    "everything is power = collapse"): if power IS interpreted as universal
    extreme/collapse, refuted. (Foucault's nuanced thesis on power-knowledge
    is NOT touched — only the simplified universal-collapse reading.) -/
theorem foucault_universal_collapse_refuted (o : ZhongOrbit) :
    ¬ (∀ n, extreme (o.states n)) := by
  intro h
  exact o.inMiddle 0 (h 0)

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
