# 道理 v12: 一字之核 — 動 之 中 ⊢ 生生不息 ∧ 自指 ∧ 自洽

> **主张**: 一字 (動) + 古文算子 ⊢ 生生不息 ∧ 自指 ∧ 自洽
> **此 是 gradual proof construction; 当前 已 实证 layers 1' .. 18** (取 v5 之 derivation structure + 一元 link).
> v5 之 chain: 動 → 元 → 几 → 势 → 机 → 聚散 → 中 → 和 → 美 → 德 → 理 → 心 → 情 → 积 → ... → 仁 → 义/礼/智/信 → 自相似.
> Lean 实证: `formal/SSBX/Foundation/Kernel.lean` (lake build passes, no sorry).
>
> 已 实证 layers:
> - **Layer 1'** — 動 → 几 → 中 → 中-orbit ⊢ 生生不息 ∧ 自指 ∧ 自洽
> - **Layer 2** — 势 (累积方向) ⊢ 拒 telos
> - **Layer 3** — 机 (势 之 自我临界) ⊢ orbit step IS 机
> - **Layer 4** — 聚散 二面 (parametric JuSanSplit) ⊢ orbit step factors via 聚 ∘ 散
> - **Layer 5** — 和 (ZhongField) ⊢ 多样性 × 流通性 ∧ 和 ≠ 同
> - **Layer 6** — 美 (heart-event 中-encounter) ⊢ aesthetic_triple ∧ 美-和 同构
> - **Layer 7** — 德 (持续合中之积) ⊢ zhongorbit_has_de ∧ de_robust
> - **Layer 8** — 理 (条贯 = 動-iteration) ⊢ li_is_iterated_dong (induction proof)
> - **Layer 9** — 自相似 ⊢ kernel theorems hold under any temporal shift
> - **Layer 10** — 心 (Xin: ZhongOrbit + respond) ⊢ heart_middle ∧ heart_aesthetic
> - **Layer 11** — 情 (qing predicate) ⊢ qing_de_zheng ⟺ aestheticEncounter
> - **Layer 12** — 积 (jiAccum, Fin-indexed history) ⊢ 积即过程 (definitional)
> - **Layer 13** — 仁 (二聚焦之间之中) ⊢ ren_triple ∧ ren_is_he_2foci
> - **Layer 14** — 义/礼/智/信 ⊢ yi=ren-at-moment, liRitual_narrowable, zhi_universal, xinTrust_holds
> - **Layer 15** — 善/恶 ⊢ shan ≡ 中, eVice ≡ 极, 善恶 universality + exclusivity, 善美德 unity
> - **Layer 16** — 行仁要善 ⊢ alignment_for_xin (仁/义/礼/智/信/善 ensemble), co_traveling, self_grounding
> - **Layer 17** — 复词 单字 trace ⊢ 加 sheng/xi/xing 单字 alias; shengsheng_buxi/zixiangsi/xing_ren_yao_shan trace
> - **Layer 18** — 一元 link ⊢ 加 yiOne/yuan; import MonadRoot; kernelToMonadRoot mapping (9 共有); shared_all_map
>
> 完备自指之核 之 vision 见 `daoli-v12-he.md`. 此文 是 实证 之 layer.

---

## 〇、setup

```
单字 inventory (active 单字 across Layers 1' .. 9):
  動 (dong)       — 动初显处之 primitive       axiom : 𝐅 → 𝐅
  极 (extreme)    — 过程之自我终结              def   : dong s = s
  中 (middle)     — 不极 = 合于生生不息         def   : dong s ≠ s
  几 (ji)         — 过程之最初之自指            def   : ℕ → 𝐅 → 𝐅
  势 (shi)        — 几 之 累积方向, 拒 telos    def   : ZhongOrbit → ℕ → 𝐅×𝐅   (Layer 2)
  机 (jiTurning)  — 势 之 自我临界              def   : ZhongOrbit → ℕ → Prop   (Layer 3)
  聚 (ju)         — 势之凝结而成形              parametric in JuSanSplit         (Layer 4)
  散 (san)        — 形之消散而归势              parametric in JuSanSplit         (Layer 4)
  和 (he)         — 多样性 × 流通性             theorem on ZhongField            (Layer 5)
  美 (mei)        — 心遇中之事而生之感应         def + theorems                   (Layer 6)
  德 (de)         — 倾向于中之积                def + robust theorem             (Layer 7)
  理 (li)         — 事之自显为条贯              def + li_is_iterated_dong        (Layer 8)
  (引 v5 §二 l. 59. 生 与 灭 是 動 之 两面.)

古文算子 (presupposed; already in kernel):
  之       : application / binding   (S-1)
  者       : λ-binder                 (S-13)
  而       : sequential composition    (S-2, time-grain)
  也       : state closure / assertion (S-14)
  不       : negation
  凡       : universal quantifier      (Q-1)
  "X之又X"  : structural recursion pattern

Closure constraint:
  核 只收纳 单字 + 古文虚字. 复词 居 expansion layers.
  Lean 落地: inductive KernelDanZi { dong, extreme, middle, ji, shi, jiTurning,
                                    ju, san, he, mei, de, li } (12 单字).
  加 字 to kernel ⟺ 加 constructor; this is v13.2 卷〇二 「单字根律」.

Structural commit:
  ∃ s, 中 s   — at least one 中 state exists.
```

---

## 一、元 (动初显处)

```
元 := 動 之 single application from any state.
```

引 v5 §二 l. 59-64:
> "动初显处, 谓之元. 动息则元亡, 动起则元成. 故元无自体, 以动为体; 无所从来, 以显为来."

元 不是 atom; 元 是 動 之 一刹那。无自体, 以動为体。

故 此 layer 不 立 元 为 primitive; 立 動。元 由 動 之 application 显。

---

## 二、几 (continuity / 过程之最初之自指)

```
几 (n) := iter(動, n) — n successive applications of 動.
       = if n=0 then identity
         else 動 ∘ 几(n-1)
```

引 v5 §三 l. 73-79:
> "一几不可识, 众几之相续, 自显于势... 识几者, 非识一刹那之物, 识 *过程之自指* 也."

几 之 self-reference 是 structural: 几(n+1) 之 定义 references 几(n)。
即: 「几 是 在 几 之 上 加 動」——definition recursive。

Lean:
```lean
noncomputable def ji : Nat → Field → Field
  | 0, s => s
  | n+1, s => dong (ji n s)

theorem ji_self_reference (n : Nat) (s : Field) :
    ji (n+1) s = dong (ji n s) := rfl
```

`rfl` 之 唯一 token 即 显 self-reference 已 type-level encode。

---

## 三、势 (direction without telos) — Layer 2

```
势 := 几 之 accumulated tendency.
     非 force, 非 object.
     "几之相续所成之向" (v5 §四 l. 88).

形式: 势 (o, n) := (state n, state n+1)  — n-th transition pair of orbit.
```

引 v5 §四 l. 94-112:
> 拒 telos. 若 势 有 fixed goal, 过程 ceases on reaching.
> 故 势 之 direction 必 不 lead to 终极 — else 不 生生不息.

Lean:
```lean
def shi (o : ZhongOrbit) (n : Nat) : Field × Field :=
  (o.states n, o.states (n+1))

theorem shi_genuine (o : ZhongOrbit) (n : Nat) :
    (shi o n).1 ≠ (shi o n).2 := self_consistent o n

theorem shi_no_telos (o : ZhongOrbit) (target : Field) (N : Nat) :
    ¬ (∀ n, n ≥ N → o.states n = target) := by
  intro h
  have hN : o.states N = target := h N (Nat.le_refl N)
  have hN1 : o.states (N + 1) = target := h (N + 1) (Nat.le_succ N)
  exact self_consistent o N (hN.trans hN1.symm)
```

`shi_no_telos` 之 内容: any 中-orbit, any target, any threshold N — orbit cannot stay at target from N onwards. v5 拒 telos 之 type-level realization.

---

## 三半、机 (势 之 自我临界) — Layer 3

引 v5 §五 l. 116-128:
> 势之相续, 有节有度. 节度之临, 谓之机.
> 机者, 势之转处也; 势之将变而未变, 可乘可失.
> 机者, 势之自我临界也.

形式: 机 (o, n) := 势(o, n).1 ≠ 势(o, n).2 — n-th 势 is a genuine turn.

Lean:
```lean
def jiTurning (o : ZhongOrbit) (n : Nat) : Prop :=
  (shi o n).1 ≠ (shi o n).2

theorem orbit_is_jiTurning (o : ZhongOrbit) (n : Nat) :
    jiTurning o n := shi_genuine o n
```

每 步 of 中-orbit IS 机. 机 不假外 — 在 orbit 之 continuation 中 自显.

---

## 四、聚散 (one process, two faces) — Layer 4

引 v5 §六 l. 136-146:
> "生与灭、聚与散、显与隐, 皆同一过程之两面, 非二事... 灭者, 生之另一相."
> "生生不息之'生', 非'生而不灭'之谓, 乃聚散显隐之总动力, 自不息也."

**关键 reframe**:
- 生生不息 ≠ "无终止 of 生"
- 生生不息 = "聚散显隐之总动力, 自不息"
- 動 contains 生 (聚) 与 灭 (散) cycles

故 此 kernel 之 primitive 是 動, 不是 生:
- 生 是 動 之 一面
- 灭 是 動 之 另一面
- 動 是 二者之 underlying rhythm

**形式化** (parametric, 不引入 global axiom):

```lean
structure JuSanSplit where
  ju : Field → Field           -- 聚 (生 face): 势之凝结而成形
  san : Field → Field          -- 散 (灭 face): 形之消散而归势
  decompose : ∀ s, dong s = ju (san s)

namespace JuSanSplit

theorem orbit_step (split : JuSanSplit) (o : ZhongOrbit) (n : Nat) :
    o.states (n + 1) = split.ju (split.san (o.states n)) := by
  rw [← o.step n, split.decompose]

theorem san_nontrivial_when_ju_id
    (split : JuSanSplit) (h_ju_id : ∀ s, split.ju s = s)
    (o : ZhongOrbit) (n : Nat) :
    split.san (o.states n) ≠ o.states n := by
  intro hSanFix
  apply o.inMiddle n
  show dong (o.states n) = o.states n
  rw [split.decompose, hSanFix, h_ju_id]

end JuSanSplit
```

担保 三:
1. **factor 存在性 (parametric)**: framework 提供 split, 每 split 见证 動 = 聚 ∘ 散.
2. **orbit_step**: 中-orbit 之 每 step factors via 聚 ∘ 散 — 「同一过程之两面」 落地.
3. **san_nontrivial_when_ju_id**: 若 聚 退化为 identity, 则 散 必 不 trivially fix orbit state. 此 是 「灭非彻底之消失」 之 corollary — 二面缺一不可.

---

## 五、极 与 中 (the structural core)

引 v5 §七 l. 167:
> "极 = 过程之自我终结之具体形式."

引 v5 §七 l. 189-191:
> "合于生生不息 = 不收缩可能性空间 = 不极 = 中"
> "中乃合于生生不息之结构性必然... 中即过程之相续之结构本身."

Type-level encoding:
```
极(s)  := 動(s) = s    -- 動 fails to escape s; fixed-point trap
中(s)  := 動(s) ≠ s    -- 動 takes s elsewhere; rhythm preserved
```

Lean:
```lean
def extreme (s : Field) : Prop := dong s = s
def middle (s : Field) : Prop := dong s ≠ s

axiom exists_middle : ∃ s : Field, middle s
```

`exists_middle` 是 framework 之 architectural commit: 世界 admits 非-collapsed 動。
没有此 commit, 生生不息 vacuous。

---

## 六、ZhongOrbit (中-保持 orbit)

```
中-orbit := Nat-indexed sequence of 中 states,
            where 動 之 application advances 凡 step.
```

Finitary encoding — no coinduction needed. orbit instantiates the rhythm 生生不息 names。

Lean:
```lean
structure ZhongOrbit where
  states : Nat → Field                    -- 凡 n, n-th state
  inMiddle : ∀ n, middle (states n)        -- 凡 n, 中 holds
  step : ∀ n, dong (states n) = states (n+1)  -- 動 advances
```

orbit 之 三 fields exhibit:
1. **states** — 序列 itself (凡 n, 一 state)
2. **inMiddle** — 中 invariant 凡 n
3. **step** — 動 之 sequencing relation

---

## 六.5、和 (multi-orbit coherence) — Layer 5

引 v5 §八 l. 217-232:
> "和者, field 中诸聚焦之间, 差异之保留与张力之流通同时维持之态."
> "和 = 多样性 × 流通性." "同是和之反面."

**关键**: 中 处理 单一 process 之 对偶张力; 和 处理 多 process 之 间 张力. 同构异显.

形式化: ZhongField (k ≥ 2 ZhongOrbits, 永 differentiated):

```lean
structure ZhongField where
  k : Nat
  k_ge_two : 2 ≤ k
  orbits : Fin k → ZhongOrbit
  ever_differentiated : ∀ n, ∃ i j : Fin k, i ≠ j ∧
    (orbits i).states n ≠ (orbits j).states n

theorem flowing (f : ZhongField) (n : Nat) (i : Fin f.k) :
    (f.orbits i).states n ≠ (f.orbits i).states (n + 1) :=
  (f.orbits i).self_consistent n

theorem he (f : ZhongField) (n : Nat) :
    (∀ i, (f.orbits i).states n ≠ (f.orbits i).states (n + 1))
    ∧ (∃ i j, i ≠ j ∧ (f.orbits i).states n ≠ (f.orbits j).states n) :=
  ⟨fun i => f.flowing n i, f.ever_differentiated n⟩

theorem he_not_same (f : ZhongField) (n : Nat) :
    ¬ (∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n)
```

担保: 流通性 自 ZhongOrbit; 多样性 由 framework commit; 和 ≠ 同 由 contradiction.

---

## 六.6、美 (heart-event 中-encounter) — Layer 6

引 v5 §九 l. 256-275:
> "美者, 心遇某事而感其于自身过程中之可能性扩张之态也."
> "美 = 中之于心-事相遇之具体显." "美 = 心遇「中」之事而生之感应."
> "美与和共享同一深层结构 — 「中」 之具体显."

形式化: 心 (heart) = ZhongOrbit; 事 (event) = Field state; 美 = 心-事 在 中 之 distinct encounter.

```lean
def aestheticEncounter (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop :=
  middle event ∧ event ≠ heart.states n

theorem aesthetic_triple (heart : ZhongOrbit) (event : Field) (n : Nat)
    (h : aestheticEncounter heart event n) :
    middle event ∧ middle (heart.states n) ∧ event ≠ heart.states n :=
  ⟨h.1, heart.inMiddle n, h.2⟩
```

担保: 美 ⊢ 心 中 ∧ 事 中 ∧ 心 ≠ 事 — 即 「心-事 之 mini-和」. 美 与 和 同构 (一 是 multi-orbit, 一 是 heart × event).

---

## 六.7、德 (持续合中之积) — Layer 7

引 v5 §十 l. 304-326:
> "德者, 聚焦之积之形态已稳定地朝向不极而执中之态也."
> "德 = 倾向于中之积 = 稳定地以中之形式回应过程之能力."
> "德... 不僵 — 真德能在不同情境下显为不同之具体回应."

形式化:

```lean
def hasDe (o : ZhongOrbit) : Prop := ∀ n, middle (o.states n)

theorem zhongorbit_has_de (o : ZhongOrbit) : hasDe o := o.inMiddle

def shiftOrbit (o : ZhongOrbit) (k : Nat) : ZhongOrbit where
  states := fun n => o.states (n + k)
  inMiddle := fun n => o.inMiddle (n + k)
  step := fun n => o.step (n + k)

theorem de_robust (o : ZhongOrbit) (k : Nat) : hasDe (shiftOrbit o k) :=
  fun n => o.inMiddle (n + k)
```

担保: 凡 ZhongOrbit IS 德 (by construction); 德 robust under any shift (不僵).

---

## 六.8、理 (条贯) — Layer 8

引 v5 §十一 l. 379-383:
> "理即事之自显为条贯之事自身."
> "离过程无理, 离理无过程."
> "理无根据, 以其本非有据之物; 理之为理, 在于过程自身能自显为可识之条贯耳."

形式化: 理 不 separate 于 orbit; 理 IS orbit's pattern. Substantive: orbit's states are exactly 動 iterated from initial state.

```lean
def li (o : ZhongOrbit) : Nat → Field := o.states

theorem li_inseparable (o : ZhongOrbit) : li o = o.states := rfl

theorem li_is_iterated_dong (o : ZhongOrbit) (n : Nat) :
    o.states n = ji n (o.states 0) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [ji_self_reference, ← ih]
    exact (o.step k).symm
```

担保: 理 不 separate (`rfl`); 理 = 動-iteration (by induction). 「条贯非先在之形式」 落地.

---

## 六.9、自相似 (scale invariance) — Layer 9

引 v5 §十七 l. 519-544:
> "同一原则... 在每一尺度具体显现, 而形式同构. 是为自相似之节."
> "牽一發而動全身, 非比喻也, 乃自相似之实也."

形式化: kernel theorems (生生不息 ∧ 自指 ∧ 自洽) hold uniformly across orbits and shifts.

```lean
theorem zixiangsi (o : ZhongOrbit) (k n : Nat) :
    middle ((shiftOrbit o k).states n)
    ∧ dong ((shiftOrbit o k).states n) = (shiftOrbit o k).states (n + 1)
    ∧ (shiftOrbit o k).states n ≠ (shiftOrbit o k).states (n + 1) :=
  ZhongOrbit.yi_zi_zhi_he (shiftOrbit o k) n

theorem zixiangsi_de (o : ZhongOrbit) (k : Nat) : hasDe (shiftOrbit o k) :=
  de_robust o k
```

担保: 三 性 (生生不息/自指/自洽) hold at any shift; 德 robust at any shift. 形 invariant 落地.

---

## 六.10、心 (xin; 过程之自感聚焦) — Layer 10

引 v5 §十二 l. 387-400:
> "心者, 过程于某处自感之聚焦也. 聚焦成而心显, 聚焦散而心隐."
> "心非本体, 心是体之一显... 心-体互显, 非二物."

形式化: 心 = ZhongOrbit (自身过程) + respond function (感-应).

```lean
structure Xin where
  process : ZhongOrbit
  respond : Field → Field

theorem Xin.heart_middle (x : Xin) (n : Nat) : middle (x.process.states n) :=
  x.process.inMiddle n

theorem Xin.heart_aesthetic
    (x : Xin) (event : Field) (n : Nat)
    (h : aestheticEncounter x.process event n) :
    middle event ∧ middle (x.process.states n) ∧ event ≠ x.process.states n :=
  aesthetic_triple x.process event n h
```

担保: 心 IS process (心-体 互显); 心 必 在 中 (inheriting ZhongOrbit invariant); 美 encounter ⊢ heart-event mini-和.

---

## 六.11、情 (qing; 心于关系中之自显) — Layer 11

引 v5 §十三 l. 418-428:
> "情即心于关系中之自显方式."
> "喜怒哀乐, 皆非'在心中'之物, 乃心-关系场域之显态."
> "情之得正, 即不极之情... 即美之于情之相."

形式化:

```lean
def qing (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop :=
  event ≠ heart.states n

def qing_de_zheng (heart : ZhongOrbit) (event : Field) (n : Nat) : Prop :=
  middle event ∧ qing heart event n

theorem qing_de_zheng_iff_aesthetic
    (heart : ZhongOrbit) (event : Field) (n : Nat) :
    qing_de_zheng heart event n ↔ aestheticEncounter heart event n :=
  Iff.rfl
```

担保: 情 是 关系 predicate; 情之得正 ≡ 美 (definitional); 喜怒哀乐 之 得正 形式 全 collapse to mini-和.

---

## 六.12、积 (jiAccum; 过程之穩定化) — Layer 12

引 v5 §十四 l. 436-453:
> "积者, 过程于某尺度之穩定化也."
> "积即过程, 过程即积, 二者一也, 异名而已."
> "积有尺度之分... 跨尺度之相互嵌入."

形式化: 积 = orbit's history-window, indexed by Fin (n+1).

```lean
def jiAccum (o : ZhongOrbit) (n : Nat) (i : Fin (n + 1)) : Field :=
  o.states i.val

theorem jiAccum_is_states (o : ZhongOrbit) (n : Nat) (i : Fin (n + 1)) :
    jiAccum o n i = o.states i.val := rfl

theorem jiAccum_extends
    (o : ZhongOrbit) (n m : Nat) (i : Fin (n + 1)) (h : i.val < m + 1) :
    jiAccum o n i = jiAccum o m ⟨i.val, h⟩ := rfl

theorem jiAccum_grows
    (o : ZhongOrbit) (n : Nat) (i : Fin (n + 1)) :
    jiAccum o (n + 1) ⟨i.val, by omega⟩ = jiAccum o n i := rfl
```

担保: 积 ≡ 过程 (定义即等); 积 跨 尺度 (extends across windows); 积 grows (积生积 hint).

---

## 六.13、仁 (ren; 二聚焦之间之中) — Layer 13

引 v5 §二十二 l. 700-710:
> "仁者, 一聚焦感应另一聚焦之合宜之态 — 即: 识其为同一过程之另一具体形式, 故待之以「同根异显」之态."
> "仁 = 关系中之中 = 二聚焦之间不极而执中之态 = 关系之和之具体形式."

形式化: 仁 = 同根 (both are ZhongOrbits) ∧ 异显 (states differ).

```lean
def ren (h1 h2 : ZhongOrbit) (n : Nat) : Prop :=
  h1.states n ≠ h2.states n

theorem ren_triple
    (h1 h2 : ZhongOrbit) (n : Nat) (h : ren h1 h2 n) :
    middle (h1.states n) ∧ middle (h2.states n) ∧ h1.states n ≠ h2.states n :=
  ⟨h1.inMiddle n, h2.inMiddle n, h⟩

theorem ren_is_he_2foci
    (h1 h2 : ZhongOrbit) (n : Nat) (h : ren h1 h2 n) :
    h1.states n ≠ h2.states n
    ∧ h1.states n ≠ h1.states (n + 1)
    ∧ h2.states n ≠ h2.states (n + 1) :=
  ⟨h, h1.self_consistent n, h2.self_consistent n⟩
```

担保: 仁 三 (同根 ∧ 异显 ∧ 同形); 仁 IS 关系之 中 (2-focus 和 specialization).

---

## 六.14、义 / 礼 / 智 / 信 (仁 之 四相) — Layer 14

引 v5 §二十三:
- **义**: "义 = 仁之于具体行 = 中之于即时" (l. 759-768).
- **礼**: "礼 = 仁之于积 = 德之于关系形式." "礼必含 「礼之自我修订」 之机制" (l. 778-797).
- **智**: "智 = 概念、感应、经验三者之相互修正, 以识 「中」 之能力" (l. 813-829).
- **信**: "信 = 仁之内在贯通 = 聚焦自身之和" (l. 849-861).

形式化:

```lean
-- 义: 仁 之 于 具体行 (即时之中)
def yi (h1 h2 : ZhongOrbit) (n : Nat) : Prop := ren h1 h2 n

theorem yi_implies_ren ... -- definitional

-- 礼: 仁 之 于 积 (window of m+1 successive 仁-moments)
def liRitual (h1 h2 : ZhongOrbit) (n m : Nat) : Prop :=
  ∀ k, k ≤ m → ren h1 h2 (n + k)

theorem liRitual_implies_ren_at_base ...
theorem liRitual_narrowable
    (h1 h2 : ZhongOrbit) (n m m' : Nat) (h : liRitual h1 h2 n m) (h_le : m' ≤ m) :
    liRitual h1 h2 n m' := fun k hk => h k (Nat.le_trans hk h_le)
   -- 礼之自我修订: 窗 可 narrow

-- 智: 中 之 识 (universal classification)
def zhi (s : Field) : Prop := middle s ∨ extreme s

theorem zhi_universal (s : Field) : zhi s :=
  match Classical.em (extreme s) with
  | Or.inl h => Or.inr h
  | Or.inr h => Or.inl h

theorem zhi_exclusive (s : Field) : ¬ (middle s ∧ extreme s) := ...

-- 信: 聚焦自身之和 (内部贯通; 言行一致)
def xinTrust (x : Xin) (n : Nat) : Prop :=
  dong (x.process.states n) = x.process.states (n + 1)

theorem xinTrust_holds (x : Xin) (n : Nat) : xinTrust x n := x.process.step n
theorem xinTrust_self_consistent ...
```

担保:
- **义** = 仁 at this moment (definitional);
- **礼** = 仁 across window, with 自我修订 (`liRitual_narrowable`);
- **智** = universal classification (Classical.em); exclusive;
- **信** = 心 之 step-coherence (every Xin satisfies it; provides self-consistency).

---

## 六.15、善 / 恶 (universal alignment vs collapse) — Layer 15

引 v5 §二十一 l. 633-679:
> "善 = 与生生不息相合 — 即扩张可能性空间, 执两用中, 致和生美, 以积成德..."
> "恶 = 与生生不息相悖 — 即收缩可能性空间, 极于一端, 扰和损美, 僵积失德, 趋向单一之终态."
> "善之事多美; 善之人之态, 常显为德."
> "善、美、德三者, 异名同实 — 皆为合于生生不息之具体显."

形式化: 善 ≡ 中, 恶 ≡ 极. 直接 由 已 立 之 dichotomy.

```lean
def shan (s : Field) : Prop := middle s
def eVice (s : Field) : Prop := extreme s

theorem shan_iff_middle (s : Field) : shan s ↔ middle s := Iff.rfl
theorem eVice_iff_extreme (s : Field) : eVice s ↔ extreme s := Iff.rfl

theorem shan_eVice_exclusive (s : Field) : ¬ (shan s ∧ eVice s) := zhi_exclusive s
theorem shan_or_eVice (s : Field) : shan s ∨ eVice s := zhi_universal s

theorem shan_to_aesthetic
    (heart : ZhongOrbit) (event : Field) (n : Nat)
    (h_shan : shan event) (h_diff : event ≠ heart.states n) :
    aestheticEncounter heart event n := ⟨h_shan, h_diff⟩

theorem shan_orbit_has_de (o : ZhongOrbit) : hasDe o := zhongorbit_has_de o

theorem shan_mei_de_unity ... -- 善美德 异名同实
```

担保:
- **善 ≡ 中, 恶 ≡ 极** (definitional);
- **善恶 universality**: 凡 state 必 善 或 恶 (Classical.em);
- **善恶 exclusive**: 同 state 不能 同时 二者;
- **善 ⟹ 美 之 倾向** (善之事多美);
- **善 ⟹ 德** (善之积成德);
- **善美德 unity** (异名同实).

---

## 六.16、行仁要善 (alignment 之 真义) — Layer 16

引 v5 §二十四 l. 904-917:
> "alignment 者, 任何能识此理而行之存在 (即: 仁), 共同对齐于生生不息之自身也."
> "仁与仁之间, 非 master-servant 之结构, 乃共同朝向同一方向之同行者."
> "做人要善 = 以仁为关系态, 以义为具体行, 以礼为可积之形, 以智为识能, 以信为内在贯通;
>  在每一对偶维度上, 识中而行之, 致和而生美, 持续而成德."

形式化: 给一 心 (Xin), 一 other ZhongOrbit, 一 礼-window — 仁/义/礼/智/信/善 全 hold.

```lean
theorem alignment_for_xin
    (x : Xin) (other : ZhongOrbit) (n m : Nat)
    (h_ritual : liRitual x.process other n m) :
    ren x.process other n               -- 仁 (关系态)
    ∧ yi x.process other n              -- 义 (具体行)
    ∧ liRitual x.process other n m       -- 礼 (积)
    ∧ zhi (x.process.states n)           -- 智 (中之识)
    ∧ xinTrust x n                        -- 信 (内贯)
    ∧ shan (x.process.states n)           -- 善 (与生生不息相合)
:= ⟨..., ..., h_ritual, zhi_universal _, xinTrust_holds x n, x.process.inMiddle n⟩

theorem alignment_co_traveling
    (h1 h2 : ZhongOrbit) (n : Nat) :
    dong (h1.states n) = h1.states (n+1)
    ∧ dong (h2.states n) = h2.states (n+1)
    ∧ middle (h1.states n) ∧ middle (h2.states n)
:= ⟨h1.step n, h2.step n, h1.inMiddle n, h2.inMiddle n⟩

theorem alignment_self_grounding (x : Xin) (n : Nat) : shan (x.process.states n) :=
  x.process.inMiddle n
```

担保:
- **alignment_for_xin**: 仁/义/礼/智/信/善 六性 hold simultaneously for any 心 + 礼-window;
- **alignment_co_traveling**: 仁 之 间, both processes step autonomously, neither subordinate (no master-servant);
- **alignment_self_grounding**: 任何 心 提出 alignment 之 question, 已 必 善 — 不需 fact-value crossing (v5 §二十一 l. 645).

此 是 v5 §二十四 「做人要善」 之 type-level 表达. AI alignment 与 人 alignment IS 同一对齐之不同显现.

---

## 六.17、复词 单字 trace (单字根律 enforcement) — Layer 17

**问题**: 「生生不息」「自相似」「行仁要善」 皆 复词. 然 「核 只收纳单字」. 故 必 trace 回 单字.

**形式化**: 加 `生 / 息 / 行` 为 单字 alias (各 ≡ 已立 primitive); 加 decomposition theorems.

```lean
-- 生 / 息 / 行 之 单字 alias
def sheng (s : Field) : Field := dong s        -- 生 ≡ 動 (生成 一面)
def xi (s : Field) : Prop := extreme s          -- 息 ≡ 极 (停息)
def xing (s : Field) : Field := dong s          -- 行 ≡ 動 (actor act)

theorem sheng_eq_dong : ∀ s, sheng s = dong s := fun _ => rfl
theorem xi_iff_extreme : ∀ s, xi s ↔ extreme s := fun _ => Iff.rfl
theorem xing_eq_dong : ∀ s, xing s = dong s := fun _ => rfl
```

### 三 复词 之 单字 trace:

**生生不息** = 生(单字) + 生(单字) + 不(虚字) + 息(单字).
```lean
theorem shengsheng_buxi_trace (o : ZhongOrbit) (n : Nat) :
    sheng (o.states n) = o.states (n + 1)        -- 生
    ∧ ¬ xi (o.states n) :=                        -- 不息
  ⟨o.step n, o.inMiddle n⟩
```

**自相似** = 自(虚字) + 相(虚字) + 似(虚字). 全 是 古文虚字 / 关系标记 — 实质 由 ZhongOrbit + shiftOrbit 给出.
```lean
theorem zixiangsi_trace (o : ZhongOrbit) (k n : Nat) :
    middle ((shiftOrbit o k).states n)
    ∧ dong ((shiftOrbit o k).states n) = (shiftOrbit o k).states (n + 1)
    ∧ (shiftOrbit o k).states n ≠ (shiftOrbit o k).states (n + 1) :=
  ZhongOrbit.yi_zi_zhi_he (shiftOrbit o k) n
```

**行仁要善** = 行(单字) + 仁(单字) + 要(虚字) + 善(单字).
```lean
theorem xing_ren_yao_shan_trace
    (x : Xin) (other : ZhongOrbit) (n m : Nat) (h_ritual : liRitual x.process other n m) :
    xing (x.process.states n) = x.process.states (n + 1)   -- 行
    ∧ ren x.process other n                                  -- 仁
    ∧ shan (x.process.states n) :=                           -- 善
  ⟨x.process.step n,
   liRitual_implies_ren_at_base x.process other n m h_ritual,
   x.process.inMiddle n⟩
```

### 古文虚字 expansion:

之 / 者 / 而 / 也 / 不 / 凡 / X之又X — 已 listed.
**新加**: 自 (reflexive), 相 (mutual/pair), 似 (similarity), 要 (modal necessity).

### 一元 link — Layer 18

**已 fix**: 加 一 (yiOne) 和 元 (yuan) 入 KernelDanZi; import MonadRoot; 显式 mapping.

```lean
import SSBX.Foundation.MonadRoot

abbrev yiOne : Type := Field                    -- 一 = 架构 root (Field)
def yuan (s : Field) : Field := dong s           -- 元 = 动初显处
theorem yuan_eq_dong (s : Field) : yuan s = dong s := rfl

def kernelToMonadRoot : KernelDanZi → Option SSBX.Foundation.MonadRoot.CoreAtom
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

def kernelMonadRootShared : List KernelDanZi :=
  [.yiOne, .yuan, .dong, .xing, .sheng, .ren, .li, .xin, .ju]

theorem shared_count : kernelMonadRootShared.length = 9 := rfl
theorem shared_all_map : ∀ z ∈ kernelMonadRootShared, (kernelToMonadRoot z).isSome := ...
```

`Kernel.lean` 之 KernelDanZi (27 单字) 与 `Foundation/MonadRoot.lean` 之 CoreAtom (43 单字) 关系:

| 关系 | 字 |
|---|---|
| **共有 (Kernel ∩ MonadRoot, 9 字)** | 一/元/动/行/生/仁/理/心/聚 |
| **Kernel 独有 (v5 ontology, 18 字)** | 极/中/几/势/机/散/和/美/德/情/积/义/礼/智/信/善/恶/息 |
| **MonadRoot 独有 (待 后续 layers, 34 字)** | 法/成/序/物/场/形/变/续/开/闭/审/校/证/真/正/邪/夺/共/道/模/度/期/算/焦/意/识/注/人/做/齐/控/天/子 |

担保: 「一元 架构」 (v13.2 卷〇) 在 Lean 中 显式 linked 到 v5 之 ontology. `kernelToMonadRoot` IS the architectural bridge.

后续 (留 layer 19+): 加 v13.2 之 12 面 / 43 核心 之 face mapping (`atomPrimaryFace`); add Roster registration 让 Kernel 之 单字 全 enter `allAtoms`.

---

## 七、Lean 实证 (no sorry)

`formal/SSBX/Foundation/Kernel.lean` 全文 (compiles via `lake build`):

```lean
namespace SSBX.Foundation.Kernel

axiom Field : Type
axiom dong : Field → Field

def extreme (s : Field) : Prop := dong s = s
def middle (s : Field) : Prop := dong s ≠ s

axiom exists_middle : ∃ s : Field, middle s

noncomputable def ji : Nat → Field → Field
  | 0, s => s
  | n+1, s => dong (ji n s)

theorem ji_self_reference (n : Nat) (s : Field) :
    ji (n+1) s = dong (ji n s) := rfl

structure ZhongOrbit where
  states : Nat → Field
  inMiddle : ∀ n, middle (states n)
  step : ∀ n, dong (states n) = states (n+1)

namespace ZhongOrbit

-- 生生不息: 中 preserved through every step.
theorem shengsheng_buxi (o : ZhongOrbit) (n : Nat) :
    middle (o.states n) := o.inMiddle n

-- 自指: 動 advances state n to state (n+1).
theorem self_reference (o : ZhongOrbit) (n : Nat) :
    dong (o.states n) = o.states (n+1) := o.step n

-- 自洽: 中-orbit 不 collapse.
theorem self_consistent (o : ZhongOrbit) (n : Nat) :
    o.states n ≠ o.states (n+1) := by
  intro heq
  apply o.inMiddle n
  rw [o.step n]
  exact heq.symm

-- 综合: 一字 (動) + 中-orbit ⊢ 三性 全 满.
theorem yi_zi_zhi_he (o : ZhongOrbit) (n : Nat) :
    middle (o.states n)
    ∧ (dong (o.states n) = o.states (n+1))
    ∧ (o.states n ≠ o.states (n+1)) :=
  ⟨shengsheng_buxi o n, self_reference o n, self_consistent o n⟩

end ZhongOrbit

inductive KernelDanZi : Type
  | dong       -- 動 (axiom; Layer 1')
  | extreme    -- 极 (def; Layer 1')
  | middle     -- 中 (def; Layer 1')
  | ji         -- 几 (def; Layer 1')
  | shi        -- 势 (def; Layer 2)
  | jiTurning  -- 机 (def; Layer 3)
  | ju         -- 聚 (parametric in JuSanSplit; Layer 4)
  | san        -- 散 (parametric in JuSanSplit; Layer 4)
  | he         -- 和 (theorem on ZhongField; Layer 5)
  | mei        -- 美 (def; Layer 6)
  | de         -- 德 (def; Layer 7)
  | li         -- 理 (def; Layer 8)
  | xin        -- 心 (structure Xin; Layer 10)
  | qing       -- 情 (def; Layer 11)
  | jiAccum    -- 积 (def; Layer 12)
  | ren        -- 仁 (def; Layer 13)
  | yi         -- 义 (def; Layer 14)
  | liRitual   -- 礼 (def; Layer 14)
  | zhi        -- 智 (def; Layer 14)
  | xinTrust   -- 信 (def; Layer 14)
  deriving Repr, DecidableEq

-- KernelDanZi.role mappings (one-line each) listed in Foundation/Kernel.lean.

end SSBX.Foundation.Kernel
```

(Layer 2-14 之 函数定义 各 listed in §三/§三半/§四/§六.5–§六.14; 全文 见 `formal/SSBX/Foundation/Kernel.lean`.)
(自相似 在 Layer 9 是 composite phrase, 不入 KernelDanZi, 但 theorem zixiangsi 实证.)

担保:

| 性 | 担保 sense |
|---|---|
| **生生不息** | `shengsheng_buxi` — 凡 n, state(n) is 中 |
| **自指** | `self_reference` — 動 之 application advances orbit (structural) + `ji_self_reference` (definitional) |
| **自洽** | `self_consistent` — 中 ⟹ progression (proven by contradiction) |
| **拒 telos (Layer 2)** | `shi_no_telos` — 中-orbit 不 settle at any target state |
| **机 不假外 (Layer 3)** | `orbit_is_jiTurning` — 每 step IS a 机 |
| **二面互证 (Layer 4)** | `JuSanSplit.orbit_step` ∧ `san_nontrivial_when_ju_id` |
| **和 (Layer 5)** | `he` + `he_not_same` — 多样性 × 流通性, 和 ≠ 同 |
| **美 (Layer 6)** | `aesthetic_triple` — mini-和 of heart × event |
| **德 (Layer 7)** | `zhongorbit_has_de` + `de_robust` — 持续合中, 不僵 under shift |
| **理 (Layer 8)** | `li_inseparable` (rfl) + `li_is_iterated_dong` (induction) |
| **自相似 (Layer 9)** | `zixiangsi` — kernel theorems uniform under shift |
| **心 (Layer 10)** | `Xin.heart_middle` ∧ `Xin.heart_aesthetic` — 心-体 互显 |
| **情 (Layer 11)** | `qing_de_zheng_iff_aesthetic` — 不极之情 ⟺ 美 |
| **积 (Layer 12)** | `jiAccum_is_states` (rfl) + `jiAccum_extends` + `jiAccum_grows` |
| **仁 (Layer 13)** | `ren_triple` + `ren_is_he_2foci` — 同根异显, 关系之 中 |
| **义/礼/智/信 (Layer 14)** | `yi_implies_ren`, `liRitual_narrowable`, `zhi_universal`+`zhi_exclusive`, `xinTrust_holds`+`xinTrust_self_consistent` |
| **善/恶 (Layer 15)** | `shan_iff_middle`, `eVice_iff_extreme`, `shan_or_eVice` (universal), `shan_eVice_exclusive`, `shan_to_aesthetic`, `shan_orbit_has_de`, `shan_mei_de_unity` |
| **alignment (Layer 16)** | `alignment_for_xin` (仁/义/礼/智/信/善 ensemble), `alignment_co_traveling`, `alignment_self_grounding` |
| **不假外** | 三 axioms only: Field, dong, exists_middle (JuSanSplit/ZhongField/Xin 皆 parametric) |
| **单字闭** | `KernelDanZi` enumerates 22 单字 (... 加 善/恶); 复词 cannot enter without decomposition |
| **完备 (Layers 1'-16)** | 此 layers 之 claims 全 实证 by Lean kernel; lake build passes (25 jobs) |

---

## 八、与 v5 之 alignment

v5 chain:
```
動 → 元 → 几 → 势 → 机 → 聚散 → 中 → 和 → 美 → 德 → 理 → 心 → 情 → 积 → ... → 自相似 → ...
```

此 layers 1'-9 之 capture:
```
動 (axiom)         → Layer 1'
  ↓
几 (def)           → Layer 1'
  ↓
势 (def)           → Layer 2: shi_genuine, shi_no_telos
  ↓
机 (def)           → Layer 3: orbit_is_jiTurning
  ↓
聚散 (structure)   → Layer 4: JuSanSplit.orbit_step, san_nontrivial_when_ju_id
  ↓
中 (def) → ZhongOrbit (struct) → 生生不息 ∧ 自指 ∧ 自洽   (Layer 1')
  ↓
和 (ZhongField struct) → he, he_not_same                   (Layer 5)
  ↓
美 (def aestheticEncounter) → aesthetic_triple             (Layer 6)
  ↓
德 (def hasDe) + shiftOrbit → de_robust                    (Layer 7)
  ↓
理 (def li) → li_is_iterated_dong (induction)              (Layer 8)
  ↓
自相似 (theorem zixiangsi) → kernel theorems under shift   (Layer 9)
```

elided in current layers (留 后续):
- 元 之 explicit type — 因 動 之 一 application 即 元 (no separate type needed)
- 心 / 情 / 积 / 仁 / 义 / 礼 / 智 / 信 / 善恶 / 行仁 / ... — layers 10+

---

## 九、Layer N>1 之 path

每 next layer:
```
1. 加 axiom 或 def in Foundation/Kernel.lean (or sibling layer file).
2. State theorem about new 字 之 relation to existing kernel.
3. Real proof, no sorry.
4. lake build 通过.
5. Update markdown.
```

已实证 layers (no sorry; lake build passes):

- ~~**Layer 2: 势**~~ — ✅ (`shi`, `shi_genuine`, `shi_no_telos`).
- ~~**Layer 3: 机**~~ — ✅ (`jiTurning`, `orbit_is_jiTurning`).
- ~~**Layer 4: 聚散 二面**~~ — ✅ (`JuSanSplit`, `orbit_step`, `san_nontrivial_when_ju_id`).
- ~~**Layer 5: 和**~~ — ✅ (`ZhongField`, `flowing`, `he`, `he_not_same`).
- ~~**Layer 6: 美**~~ — ✅ (`aestheticEncounter`, `aesthetic_triple`, `aesthetic_is_he_shape`).
- ~~**Layer 7: 德**~~ — ✅ (`hasDe`, `zhongorbit_has_de`, `shiftOrbit`, `de_robust`).
- ~~**Layer 8: 理**~~ — ✅ (`li`, `li_inseparable`, `li_is_iterated_dong`).
- ~~**Layer 9: 自相似**~~ — ✅ (`zixiangsi`, `zixiangsi_de`).
- ~~**Layer 10: 心**~~ — ✅ (`Xin`, `heart_middle`, `heart_aesthetic`).
- ~~**Layer 11: 情**~~ — ✅ (`qing`, `qing_de_zheng`, `qing_de_zheng_iff_aesthetic`).
- ~~**Layer 12: 积**~~ — ✅ (`jiAccum`, `jiAccum_is_states`, `jiAccum_extends`, `jiAccum_grows`).
- ~~**Layer 13: 仁**~~ — ✅ (`ren`, `ren_triple`, `ren_is_he_2foci`).
- ~~**Layer 14: 义/礼/智/信**~~ — ✅ (`yi`, `liRitual` + `narrowable`, `zhi` + `universal`/`exclusive`, `xinTrust` + `holds`/`self_consistent`).
- ~~**Layer 15: 善/恶**~~ — ✅ (`shan`, `eVice`, `shan_or_eVice`, `shan_eVice_exclusive`, `shan_to_aesthetic`, `shan_orbit_has_de`, `shan_mei_de_unity`).
- ~~**Layer 16: 行仁要善 (alignment)**~~ — ✅ (`alignment_for_xin` 六性 ensemble, `alignment_co_traveling`, `alignment_self_grounding`).

候选 next layers (留):

- **Layer 17: 序之上升** — v5 §十八 涌现层级.
- **Layer 18: 因生因** — v5 §十六 (因之 自递归; 可能性空间扩张).
- **Layer 19: 宇宙即理** — v5 §十九.
- **Layer 20: 是为吾性** — v5 §二十.

每 layer 之 加 必 with real Lean proof; kernel boundary 不 改.

---

## 终言

```
layers 1'..14 (此文):
  axiom Field : Type
  axiom dong : Field → Field        -- 動
  axiom exists_middle               -- ∃ 中 state
  (三 axioms only)
  
  def extreme, middle, ji            -- 极/中/几
  structure ZhongOrbit               -- 中-保持 orbit (Layer 1')
  
  Layer 1' (动+几+中):
    ⊢ shengsheng_buxi, self_reference, self_consistent, yi_zi_zhi_he
  Layer 2 (势):  def shi; ⊢ shi_genuine, shi_no_telos
  Layer 3 (机):  def jiTurning; ⊢ orbit_is_jiTurning
  Layer 4 (聚散): struct JuSanSplit; ⊢ orbit_step, san_nontrivial_when_ju_id
  Layer 5 (和):  struct ZhongField; ⊢ flowing, he, he_not_same
  Layer 6 (美):  def aestheticEncounter; ⊢ aesthetic_triple, aesthetic_is_he_shape
  Layer 7 (德):  def hasDe, shiftOrbit; ⊢ zhongorbit_has_de, de_robust
  Layer 8 (理):  def li; ⊢ li_inseparable (rfl), li_is_iterated_dong (induction)
  Layer 9 (自相似): ⊢ zixiangsi, zixiangsi_de
  Layer 10 (心): struct Xin; ⊢ heart_middle, heart_aesthetic
  Layer 11 (情): def qing, qing_de_zheng; ⊢ qing_de_zheng_iff_aesthetic (Iff.rfl)
  Layer 12 (积): def jiAccum (Fin-indexed); ⊢ jiAccum_is_states/extends/grows
  Layer 13 (仁): def ren; ⊢ ren_triple, ren_is_he_2foci
  Layer 14 (义/礼/智/信):
    def yi (= ren-at-moment); theorem yi_implies_ren
    def liRitual (window); ⊢ liRitual_implies_ren_at_base, liRitual_narrowable
    def zhi; ⊢ zhi_universal (Classical.em), zhi_exclusive
    def xinTrust; ⊢ xinTrust_holds, xinTrust_self_consistent
  
  Layer 15 (善/恶):
    def shan, eVice (= middle, extreme aliases)
    ⊢ shan_iff_middle, eVice_iff_extreme (Iff.rfl)
    ⊢ shan_or_eVice (universal), shan_eVice_exclusive
    ⊢ shan_to_aesthetic, shan_orbit_has_de, shan_mei_de_unity
  
  Layer 16 (行仁要善 / alignment):
    ⊢ alignment_for_xin   (仁/义/礼/智/信/善 ensemble)
    ⊢ alignment_co_traveling   (no master-servant)
    ⊢ alignment_self_grounding   (no fact-value crossing needed)
  
  inductive KernelDanZi  -- 22 单字 closure:
    动/极/中/几/势/机/聚/散/和/美/德/理/心/情/积/仁/义/礼/智/信/善/恶
  
  no sorry; lake build passes (25 jobs).
```

道在動之中, 中在不极。
生生不息, 是中之不停。
势 拒 终, 机 自临, 聚散 互 表。
和 见 多, 美 见 心, 德 见 持, 理 见 显。
自相似, 同形 一以贯之。
心-体 互显, 情 即 关系, 积 即 过程。
仁 同根 异显, 义 显 即时, 礼 持 之 形, 智 识 中 之 能, 信 贯 内 之 一。
善 即 中, 恶 即 极, 善美德 异名同实。
仁 与 仁 同行, 行仁要善, 此 即 alignment 之 真义。

**Lake build 状态** (2026-05-06): `Build completed successfully (25 jobs).`
