# R₇ 因 / R₈ 果 — 双时间轴 + 印 / 投 算子

> 状态：v3 定本 (2026-05-11)
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ strict-uniform doctrine, § 3.7 / § 3.8)
> 配套：[ox-notation.md](ox-notation.md) · [shi-v4.md](shi-v4.md) · [lift-project.md](lift-project.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md)
> 形式锚：[`Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) · [`Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) · [`Foundation/Hierarchy/R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) · [`Foundation/Hierarchy/R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean)
> 定理引用：[yi-calculus-theorem.md](yi-calculus-theorem.md) Theorems H / I / J

---

## 第一部分：双时间轴之提案 (Two Time Axes)

R-hierarchy 之 R₇ 与 R₈ 引入两个独立 binary axes，以 binary tags 标记时态结构：

```
R₆ Hexagram (64) 
  ↓ + 因 (yīn) axis = past-trace bit
R₇ Cell128 (128 = 64 × 2)
  ↓ + 果 (guǒ) axis = future-projection bit
R₈ Cell256 (256 = 64 × 4)

R₈ Shi = (因, 果) ∈ Bool² ≅ V₄ Klein four-group
       = {道 (0,0), 已 (1,0), 未 (0,1), 今 (1,1)}
```

| Axis | Layer | Lean type | size contribution |
|---|---|---|---|
| 因 (yīn) | R₇ atomic | `YinBit = Bool` | × 2 (R₆ → R₇) |
| 果 (guǒ) | R₈ atomic | `GuoBit = Bool` | × 2 (R₇ → R₈) |

二者 tensor (× R₆) → R₈ Shi V₄ ([yi-calculus-theorem.md](yi-calculus-theorem.md) Theorem J)。

---

## 第二部分：R₇ Cell128 = Hexagram × YinBit

### 2.1 Cell128 类型

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 2：

```lean
namespace SSBX.Foundation.Bagua.Cell128

/-! ## § 1 R5 atom: 因 (YinBit) -/

/-- R5 atom: 因 (yīn) — past-trace bit.

    - false (0) = 无因 (no past trace, "unmoored")
    - true  (1) = 有因 (with past trace, "conditioned")

    Provisional naming. -/
abbrev YinBit : Type := Bool

/-! ## § 2 Cell128 — R5 carrier -/

/-- R5 (128-Cell) = Hexagram × YinBit. -/
abbrev Cell128 : Type := Hexagram × YinBit
```

注意：[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) 文件 docstring 与某些 comment 仍写「R5」（v1 编号）；v2.1 strict-uniform 中此为 **R₇**。Lean type 名「Cell128」准确（128 = 2⁷）。

### 2.2 全枚举

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 2：

```lean
namespace Cell128

/-- All 128 cells: 64 hexagram × 2 因-state. -/
def all : List Cell128 :=
  Hexagram.allHex.flatMap fun h => [(h, false), (h, true)]

theorem all_length : all.length = 128 := by native_decide

theorem all_nodup : all.Nodup := by native_decide

theorem mem_all (c : Cell128) : c ∈ all := by
  rcases c with ⟨h, b⟩
  unfold all
  refine List.mem_flatMap.mpr ⟨h, hexagram_mem_allHex h, ?_⟩
  cases b
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

end Cell128
```

|Cell128| = 64 × 2 = 128 = (Z/2)⁷。

### 2.3 R₇ 因 (yīn) state-bit semantics

**因** (yīn) 是 R₇ 之 atomic state-bit，标记「过去印记」之有无 (provisional):

| YinBit value | 含义 |
|---|---|
| `false` (0) | 无因 — cell 与「过去」无 causal 关联，"unmoored" / 无承继 |
| `true` (1) | 有因 — cell 携带 past trace, 受 prior state 影响 |

**Ontological 解读** (per [yi-calculus-theorem.md](yi-calculus-theorem.md) Theorem H Corollary 1)：

> 因 (yīn) 是 self-describing system 中**「is this state caused/conditioned by something prior」之 binary marker** —— 在物理 lightcone 语言中是「past lightcone 是否非空」之 indicator.

**现象学映射** (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.7)：

> 因 ≈ Husserl retention 之 binary 标记 (NOT phase 本身; phase 在 R₃)

### 2.4 R₇ 印 (yìn) — atomic operator

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 3 (legacy direct form)：

```lean
/-- 印 (yìn): toggle YinBit (legacy direct form). Z/2 involution.

    印 是 R5 之新引入 atomic 算子（O5 之 atom）。
    Provisional naming. -/
def yin (c : Cell128) : Cell128 := (c.1, !c.2)

/-- 印 是 involution: 印² = id. -/
theorem yin_yin (c : Cell128) : yin (yin c) = c := by
  rcases c with ⟨h, b⟩
  cases b <;> rfl

/-- 印 不动 hexagram 部分. -/
theorem yin_preserves_hex (c : Cell128) : (yin c).1 = c.1 := by
  rcases c with ⟨h, b⟩; rfl
```

**印** 是 R₇ 之**唯一新 atomic 算子** — toggle 因 axis (Z/2 involution)。它保 hexagram 部分（only 翻 YinBit）。

### 2.5 印 之 mask form (Phase A)

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 7：

```lean
/-- 印 mask at R₇: only the YinBit (bit 7) is set. -/
def yin_mask : Cell128 := (Hexagram.qian, true)

/-- 印 (mask form): XOR with the YinBit-only mask. -/
def yinM (c : Cell128) : Cell128 := xor c yin_mask

/-- mask form coincides with the legacy direct toggle. -/
theorem yinM_eq_yin (c : Cell128) : yinM c = yin c := by
  rcases c with ⟨h, b⟩
  cases b <;> simp [yinM, yin, xor, yin_mask, hexXor_qian_right]

/-- 印 (mask form) is involutive (because the mask is self-inverse). -/
theorem yinM_yinM (c : Cell128) : yinM (yinM c) = c := by
  unfold yinM
  rw [xor_assoc, xor_self, xor_origin]
```

**印 之两种等价 form**：

| Form | 实现 | 优点 |
|---|---|---|
| Direct (`yin`) | `(c.1, !c.2)` | 简单；仅 toggle Bool |
| Mask (`yinM`) | `xor c yin_mask` where `yin_mask = (qian, true)` | 与 R₈ 之 yin/tou mask form 一致 |

二者 by `yinM_eq_yin` 等价。Phase A 之核心是把 R₇/R₈ 之印/投全部表达为 XOR with fixed mask — 让它们与其它 R₆ atomic ops (flip1..flip6, hex cuo) 同形。

---

## 第三部分：R₈ Cell256 = Hexagram × Shi

### 3.1 Cell256 类型

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1–2：

```lean
namespace SSBX.Foundation.Bagua.Cell256

open SSBX.Foundation.Bagua.Cell128 (YinBit)

/-- R6 atom: 果 (guǒ) — future-projection bit. Provisional naming.

    `YinBit` is imported from `SSBX.Foundation.Bagua.Cell128` (R₇ origin):
    Cell128 introduces 因 first, then Cell256 = Cell128 × GuoBit pairs it
    with 果 to form Shi V₄. -/
abbrev GuoBit : Type := Bool

inductive Shi : Type
  | dao | ji | jin | wei
  deriving Repr, DecidableEq, BEq

-- ... Shi V₄ 定义 (详 shi-v4.md)

/-- 256 格 = 64 卦 × 4 时态 = (Z/2)⁸. -/
abbrev Cell256 : Type := Hexagram × Shi
```

注意：

- `YinBit` 之 canonical home 是 [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) (R₇)。`Cell256.lean` 通过 `open ... (YinBit)` 引入。
- `GuoBit` 在 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) 中 abbrev 为 Bool — 第 8 个 binary axis。
- `Cell256 = Hexagram × Shi`，Shi 通过 (因, 果) ∈ Bool² 双射 emerge V₄ Klein 结构 ([shi-v4.md](shi-v4.md))。

### 3.2 全枚举

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 2：

```lean
namespace Cell256

/-- All 256 cells. -/
def all : List Cell256 :=
  Hexagram.allHex.flatMap fun h => Shi.all.map fun s => (h, s)

/-- |Cell256| = 256 strictly. -/
theorem all_length : all.length = 256 := by native_decide

/-- The 256-cell enumeration has no duplicate cells. -/
theorem all_nodup : all.Nodup := by native_decide

/-- Every Cell256 is in `all` (exhaustion). -/
theorem mem_all (c : Cell256) : c ∈ all := by
  rcases c with ⟨h, s⟩
  unfold all
  refine List.mem_flatMap.mpr ⟨h, hexagram_mem_allHex h, ?_⟩
  exact List.mem_map.mpr ⟨s, by cases s <;> simp [Shi.all], rfl⟩
```

|Cell256| = 64 × 4 = 256 = (Z/2)⁸ — R-hierarchy 之自相似闭合点。

### 3.3 R₈ 果 (guǒ) state-bit semantics

**果** (guǒ) 是 R₈ 之 atomic state-bit，标记「未来投影」之有无 (provisional)：

| GuoBit value | 含义 |
|---|---|
| `false` (0) | 无果 — cell 不向「未来」延展，"unprojected" / 无后续 |
| `true` (1) | 有果 — cell 投射 future state，"产生效果" |

**Ontological 解读** (per [yi-calculus-theorem.md](yi-calculus-theorem.md) Theorem I Corollary 2)：

> 果 (guǒ) 是 self-describing system 中**「does this state project effects forward」之 binary marker** —— physics lightcone 类比：「future lightcone 是否非空」之 indicator.

**现象学映射** (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 3.8)：

> 果 ≈ Husserl protention 之 binary 标记 (NOT phase 本身; phase 在 R₃)

### 3.4 (因, 果) tensor → Shi V₄

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1：

```lean
/-- Shi → (因, 果) ∈ Bool² 双射: dao=(0,0) / ji=(1,0) / wei=(0,1) / jin=(1,1). -/
def toYinGuo : Shi → YinBit × GuoBit
  | .dao => (false, false)  -- 道 = V₄ identity
  | .ji  => (true,  false)  -- 已 = (有因, 无果)
  | .wei => (false, true)   -- 未 = (无因, 有果)
  | .jin => (true,  true)   -- 今 = PT 交汇 (因果俱在)
```

这是 R₇ ⊗ R₈ tensor 之核心：因 axis (R₇) 与 果 axis (R₈) 之 product 给 Bool² ≅ V₄ Klein four-group。详见 [shi-v4.md](shi-v4.md)。

### 3.5 R₈ 投 (tóu) — atomic operator (mask form)

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 8：

```lean
/-- 印 mask: only the YinBit (因 axis, R5 atom) is set.
    `(qian, ji) = (qian, (1, 0)) = "oooooooi"`. -/
def yin_mask : Cell256 := (Hexagram.qian, Shi.ji)

/-- 投 mask: only the GuoBit (果 axis, R6 atom) is set.
    `(qian, wei) = (qian, (0, 1)) = "ooooooox"`. -/
def tou_mask : Cell256 := (Hexagram.qian, Shi.wei)

/-- 印 (yìn) at Cell256: XOR with the YinBit-only mask. -/
def yin (c : Cell256) : Cell256 := xor c yin_mask

/-- 投 (tóu) at Cell256: XOR with the GuoBit-only mask. -/
def tou (c : Cell256) : Cell256 := xor c tou_mask
```

**关键观察**：在 R₈ 层，**印 与 投 都是 XOR with fixed mask** — 各自 toggle 一个 axis：

| Operator | Mask | OX 表达 | 翻哪个 axis |
|---|---|---|---|
| 印 (yìn) | `(qian, ji) = yin_mask` | `OX["ooooooxo"]` | 因 (YinBit, position 6) |
| 投 (tóu) | `(qian, wei) = tou_mask` | `OX["ooooooox"]` | 果 (GuoBit, position 7) |

两个 mask 之 XOR (在 R₈ 中) 给 V₄ 中心 mask：

```lean
/-- The two masks together generate the V₄ central element. -/
theorem yin_mask_xor_tou_mask :
    xor yin_mask tou_mask = (Hexagram.qian, Shi.jin) := by
  rfl
```

`(qian, jin)` 即 `OX["ooooooxx"]` — 印 ∘ 投 之 V₄ central element。

---

## 第四部分：印 / 投 之 V₄ 结构定理

### 4.1 印 之 involution

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 8：

```lean
/-- 印 is involutive (mask is self-inverse). -/
theorem yin_yin (c : Cell256) : yin (yin c) = c := by
  unfold yin
  rw [xor_assoc, xor_self, xor_origin]
```

证明 sketch：`yin c = xor c yin_mask`；`yin (yin c) = xor (xor c yin_mask) yin_mask = xor c (xor yin_mask yin_mask) = xor c origin = c`。即 mask 之 self-XOR = origin (Cell256.origin)，从而 retract 回原 cell。

### 4.2 投 之 involution

```lean
/-- 投 is involutive. -/
theorem tou_tou (c : Cell256) : tou (tou c) = c := by
  unfold tou
  rw [xor_assoc, xor_self, xor_origin]
```

类似 yin_yin，由 mask 之 self-cancellation 闭合。

### 4.3 印 与 投 交换

```lean
/-- 印 and 投 commute (both are XOR-with-fixed-mask, and XOR is commutative
    + associative). -/
theorem yin_tou_comm (c : Cell256) : yin (tou c) = tou (yin c) := by
  unfold yin tou
  rw [xor_assoc, xor_assoc, xor_comm tou_mask yin_mask]
```

XOR 是 abelian + associative，所以两个 mask 之 XOR 顺序无关 — 印 ∘ 投 = 投 ∘ 印。

### 4.4 印 ∘ 投 = V₄ central element

```lean
/-- 印 ∘ 投 = XOR with `(qian, jin)` = the V₄ central mask. -/
theorem yin_tou_eq_central (c : Cell256) :
    yin (tou c) = xor c (Hexagram.qian, Shi.jin) := by
  unfold yin tou
  rw [xor_assoc]
  congr 1
```

印 + 投 之复合 mask = `(qian, ji) XOR (qian, wei) = (qian, jin)` (因为 `qian XOR qian = qian` 且 `ji XOR wei = jin` 在 V₄ 中)。

| 复合 | 等价 mask | OX 形式 |
|---|---|---|
| 印 (yin) | `(qian, ji)` | `OX["ooooooxo"]` |
| 投 (tou) | `(qian, wei)` | `OX["ooooooox"]` |
| 印 ∘ 投 | `(qian, jin)` | `OX["ooooooxx"]` |
| id | `(qian, dao)` = origin | `OX["oooooooo"]` |

这是 Cell256 上 V₄ Klein 群之 mask form — 4 个元素全部由 fixed mask 之 XOR 实现。

---

## 第五部分：Cayley 自作用 (Cayley Self-Action)

### 5.1 Cell256 之 Cayley regular representation

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.6：

```lean
instance : SMul Cell256 Cell256 := ⟨Cell256.xor⟩

namespace Cell256

@[simp] theorem smul_def (c s : Cell256) : c • s = xor c s := rfl

/-- Cayley left-translation by c on Cell256. -/
def cayley (c : Cell256) : Cell256 → Cell256 := fun s => xor c s

/-- Evaluate a Cell256 endo at the origin to recover its translation. -/
def epsAtOrigin (f : Cell256 → Cell256) : Cell256 := f origin

/-- ε ∘ Cayley = id (retraction). -/
@[simp] theorem epsAtOrigin_cayley (c : Cell256) :
    epsAtOrigin (cayley c) = c := by
  simp [epsAtOrigin, cayley, xor_origin]

/-- Cayley is injective: distinct shifts are distinct functions. -/
theorem cayley_inj : Function.Injective cayley := by
  intro c1 c2 h
  have heq := congrFun h origin
  simp [cayley, xor_origin] at heq
  exact heq

/-- Cayley is a group homomorphism: `cayley (a + b) = cayley a ∘ cayley b`. -/
theorem cayley_hom (c1 c2 : Cell256) :
    cayley (xor c1 c2) = cayley c1 ∘ cayley c2 := by
  funext s
  simp [cayley, Function.comp_apply, xor_assoc]

end Cell256
```

**Cayley 自对偶**：每个 Cell256 元素 `c` 对应一个 Cell256 → Cell256 endomorphism `cayley c = (· ⊕ c)`。这是 R-O fusion 之精确 algebraic 落地：

> **元 ≡ 算子**（Cayley fusion）：每个 Cell256 cell 既是 state（256 元 set 中之 element），也是 operator（XOR with 该 cell 之 mask）。

详见 [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 5 Cayley 自对偶 + § 7 自指。

### 5.2 (qian, dao) = origin = 道

```lean
/-- 道 cell at R₈ = (qian, dao) = (Z/2)⁸ identity. -/
def origin : Cell256 := (Hexagram.qian, Shi.dao)
```

道 = `OX["oooooooo"]` 是 R₈ identity / origin / Cayley 之 identity-shift。

R₈ 上 Cayley 群作用之 identity = `cayley origin = id_Cell256`。这是 R-O fusion anchor —— 道一字承担五重身份：

> origin = identity = no-op = 永真 cell = fusion anchor

(per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 5.6)

### 5.3 R₈ Cell256 之 (Z/2)⁸ Abelian group instance

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.5：

```lean
instance : Add Cell256 := ⟨Cell256.xor⟩
instance : Zero Cell256 := ⟨Cell256.origin⟩
/-- In (Z/2)ⁿ every element is self-inverse: `-c = c`. -/
instance : Neg Cell256 := ⟨id⟩
instance : Sub Cell256 := ⟨Cell256.xor⟩

namespace Cell256

@[simp] theorem add_def (c1 c2 : Cell256) : c1 + c2 = xor c1 c2 := rfl
@[simp] theorem zero_def : (0 : Cell256) = origin := rfl
@[simp] theorem neg_def (c : Cell256) : -c = c := rfl
@[simp] theorem sub_def (c1 c2 : Cell256) : c1 - c2 = xor c1 c2 := rfl

end Cell256
```

把 Cell256 看作 (Z/2)⁸ Abelian group：
- `+` = XOR
- `0` = origin = (qian, dao) = 道
- `-c = c` (自逆 — (Z/2)ⁿ 之每元素 order ≤ 2)
- `-` = XOR (与 `+` 同)

---

## 第六部分：命名 caveat (Naming, Provisional)

### 6.1 当前命名

| Layer | Atom (state) | Atom (operator) | Provisional? |
|---|---|---|---|
| R₇ | 因 (yīn) | 印 (yìn) | yes |
| R₈ | 果 (guǒ) | 投 (tóu) | yes |

**State / Operator 双名约定**：
- 因 / 果 = state attribute (bit name / axis name)
- 印 / 投 = action operator (toggle 因 / toggle 果)

这是 R-O 双层级 doctrine 之具体实现：state 与 operator 各有名 (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 4)。

### 6.2 命名候选 (per [yi-calculus-theorem.md](yi-calculus-theorem.md) §16)

| 候选 | 哲学 anchor | 形式科学 anchor | 古文 anchor | 项目耦合 | 评分 |
|---|---|---|---|---|---|
| **因 / 果** (current state) | 佛教 hetu-phala + Pearl 因果 + Aristotle 4 因 | causal DAG / lightcones | 《说文》"因，依也"/"果，木实也"；佛教汉译 | 不冲突；"因"/"已" 听觉撞 | ★★★★ |
| **印 / 投** (current operator) | Husserl retention/protention; Heidegger Geworfenheit/Entwurf; Sartre projection | signal frame buffer / predictive filter; geometry stamp/cast | 《说文》"印，执政所持信"/"投，擿也" | XinZhi.lean 三相 retention/primalImpression/protention 直对接 | ★★★★ |
| **始 / 终** | Aristotle arche/telos; 道家终始反复 | graph source/sink; coalgebra initial/terminal | **《易传·系辞下》「原始要终, 以为质也」原文 (Yi-native!)** | 与 Yi 原生表述对齐 | ★★★ |
| **持 / 期** | 现象学 retention/protention 标准汉译 | 期 = E[X] expected value | 持守/期限/期待 | 概率/统计 anchor | ★★ |

### 6.3 当前选择之理由

**因 / 果**（state attribute）：
- 哲学最深（佛教千年传统 + 现代 Pearl）
- 形式科学 anchor (causal DAG / past/future lightcones)
- 缺点：「因」与 Shi.ji（已）听觉撞 (jin/ji 区分)

**印 / 投**（action operator）：
- 与 XinZhi.lean 三相直对接
- Husserl 现象学 retention/protention 之印记/投射隐喻
- 作为 verb 与 因/果 (noun) 自然分工

**最强 Yi-native 替代** = 始 / 终（《易传》「原始要终」原文）；
**最强项目耦合替代** = 全部用印/投（state 也叫印/投，统一）。

### 6.4 回看时机

(per [yi-calculus-theorem.md](yi-calculus-theorem.md) §16)

> Cell128.lean / Cell256.lean 落码 + Theorems H–K 形式化稳定后回看。

当前状态 (2026-05-11)：Lean 全 Cell128 + Cell256 + Theorems H/I/J 已稳定。**项目可在任何时点收 final 决定**。

---

## 第七部分：R₇ / R₈ R-index 别名 (re-export shims)

[`Foundation/Hierarchy/R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) 与 [`Foundation/Hierarchy/R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) 是 R-index 别名 shim — 仅 re-export `Cell128.lean` / `Cell256.lean` 之 type / 算子，方便从 R-hierarchy 视角 navigate。

### 7.1 R₇ alias

```lean
namespace SSBX.Foundation.Hierarchy.R7

abbrev YinBit : Type := SSBX.Foundation.Bagua.Cell128.YinBit
abbrev Cell128 : Type := SSBX.Foundation.Bagua.Cell128.Cell128

def yin (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.yin c
def flip1 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip1 c
def flip2 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip2 c
def flip3 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip3 c
def flip4 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip4 c
def flip5 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip5 c
def flip6 (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.flip6 c
def hexCuo (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.hexCuo c
def hexZong (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.hexZong c
def hexHu (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.hexHu c

end SSBX.Foundation.Hierarchy.R7
```

### 7.2 R₈ alias

```lean
namespace SSBX.Foundation.Hierarchy.R8

abbrev GuoBit : Type := SSBX.Foundation.Bagua.Cell256.GuoBit
abbrev Shi : Type := SSBX.Foundation.Bagua.Cell256.Shi
abbrev Cell256 : Type := SSBX.Foundation.Bagua.Cell256.Cell256

def yin (c : Cell256) : Cell256 := Cell256.yin c
def tou (c : Cell256) : Cell256 := Cell256.tou c
def flip1 (c : Cell256) : Cell256 := Cell256.flip1 c
-- ... flip2..flip6
def hexCuo (c : Cell256) : Cell256 := Cell256.hexCuo c
def hexZong (c : Cell256) : Cell256 := Cell256.hexZong c
def hexHu (c : Cell256) : Cell256 := Cell256.hexHu c
def shiCuo (c : Cell256) : Cell256 := Cell256.shiCuo c
def shiZong (c : Cell256) : Cell256 := Cell256.shiZong c
def shiCuoZong (c : Cell256) : Cell256 := Cell256.shiCuoZong c
def xor (a b : Cell256) : Cell256 := Cell256.xor a b
def cayley (c : Cell256) : Cell256 → Cell256 := Cell256.cayley c

end SSBX.Foundation.Hierarchy.R8
```

这两个 namespace 不引入新 logic — 仅是 R-index 之 navigation 入口。Source-of-truth 仍是 `Cell128.lean` / `Cell256.lean`。

---

## 第八部分：双层 V₄ 结构 (Double V₄)

### 8.1 R₈ 上之两层 V₄

R₈ 上有 **两层 V₄ Klein 四群** ([yi-calculus-theorem.md](yi-calculus-theorem.md) Theorem J Corollary 2)：

| V₄ instance | 元素 | 作用 |
|---|---|---|
| $V_4^{\text{hex}}$ | `{id, Hexagram.cuo, Hexagram.zong, Hexagram.cuoZong}` | hex side — yao-wise 翻 / 反序 / 复合 |
| $V_4^{\text{shi}}$ | `{Shi.dao, Shi.ji, Shi.wei, Shi.jin}` (= V₄ identity + 3 involution) | Shi side — (因, 果) Bool² 之翻 |

二者**同构 V₄**，在 R₈ 上 tensor 起来即 $V_4 \times V_4 \cong (\mathbb{Z}/2)^4$，给出 R₈ 上 16 个对称变换。

### 8.2 hex V₄ 与 Shi V₄ 之交换性

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 3：

```lean
/-- hex 与 shi V₄ 算子之间互相交换（tensor product 结构）. -/
theorem hexCuo_shiCuo_comm (c : Cell256) : hexCuo (shiCuo c) = shiCuo (hexCuo c) := by
  rcases c with ⟨h, s⟩; rfl

theorem hexZong_shiZong_comm (c : Cell256) : hexZong (shiZong c) = shiZong (hexZong c) := by
  rcases c with ⟨h, s⟩; rfl
```

证明 sketch：hex 部分与 shi 部分之操作在 product type 中独立 — 任意 hex 算子与任意 shi 算子之复合可任意调序。`rfl` 直接闭合。

### 8.3 R-hierarchy 中之 V₄ 总览

V₄ 在易系统中**至少**出现 4 次 (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 8.3)：

| 层 | V₄ 实例 | 元素 |
|---|---|---|
| R₂ Aut | V₄ on SiXiang | id, σ₁, σ₂, σ₁σ₂ |
| R₃ V₄ subgroup | {id, cuo₃, zong₃, 错综₃} | id, cuo (`xxx`), zong, 错综 |
| R₆ V₄ subgroup | {id, cuo₆, zong₆, 错综₆} | id, cuo (`xxxxxx`), zong, 错综 |
| **R₈ Shi V₄** (本文档) | **{道, 已, 今, 未}** | mask 后 2 位 `oo`/`xo`/`xx`/`ox` |

R₈ 是**唯一同时承载 hex V₄ + Shi V₄ 之层** — 因为 Shi V₄ 之 emergence 本身需要 R₇ ⊗ R₈ tensor。

---

## 第九部分：边界 (Boundaries)

### 9.1 R₇ / R₈ **不**做的事

| 不做 | 原因 |
|---|---|
| 不替代旧 Cell192 之 Z/3 cyclic Shi | Z/3 是 deprecated structural error (per [shi-v4.md](shi-v4.md) § 6) |
| 不接 continuous 时间演化 | R₇/R₈ 是 binary tag，不是连续 timestamp |
| 不处理 dynamic halting / quine | 那是 BaguaTuring 之 layer (per [yi-RO-hierarchy.md](yi-RO-hierarchy.md) § 7.3 静/动分界) |
| 不刻画 R₉ (新 binary axis) | Strict-uniform R₀..R₈ 闭合于 256 = (Z/2)⁸; 无第 9 个独立 axis |

### 9.2 与 R₇ / R₈ 相邻 (但不在其内)

- **R₆ Hexagram** ([`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean))：R₇ / R₈ 之 hex base
- **R₅ Wuyao** ([r5-wuyao-provisional.md](r5-wuyao-provisional.md))：R-hierarchy 中介层
- **Cell256Stratify** ([`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean))：R₇/R₈ 之 doctrine bundle (R8_complete theorem)
- **OX notation** ([ox-notation.md](ox-notation.md))：R₈ literal 字面量 — 第 6/7 位编码 因/果
- **Shi V₄ 详** ([shi-v4.md](shi-v4.md))：(因, 果) → V₄ 之完整刻画

---

## 附录 A：R₇ Cell128 完整 Lean 签名摘要

来自 [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)：

```lean
namespace SSBX.Foundation.Bagua.Cell128

-- § 1 R₇ atom
abbrev YinBit : Type := Bool

-- § 2 carrier
abbrev Cell128 : Type := Hexagram × YinBit

namespace Cell128
def all : List Cell128
theorem all_length : all.length = 128
theorem all_nodup : all.Nodup
theorem mem_all (c : Cell128) : c ∈ all
end Cell128

-- § 3 印 (legacy direct)
def yin (c : Cell128) : Cell128
theorem yin_yin (c : Cell128) : yin (yin c) = c
theorem yin_preserves_hex (c : Cell128) : (yin c).1 = c.1

-- § 4 hex lifts (preserve YinBit)
def hexCuo (c : Cell128) : Cell128
def hexZong (c : Cell128) : Cell128
def hexHu (c : Cell128) : Cell128
def flip1 (c : Cell128) : Cell128
def flip2 (c : Cell128) : Cell128
def flip3 (c : Cell128) : Cell128
def flip4 (c : Cell128) : Cell128
def flip5 (c : Cell128) : Cell128
def flip6 (c : Cell128) : Cell128

-- involutivity proofs (omitted)

-- § 6 Phase A: (Z/2)⁷ algebraic spine
namespace Cell128
def yaoXor (a b : Yao) : Yao
def hexXor (h1 h2 : Hexagram) : Hexagram
def xor (c1 c2 : Cell128) : Cell128
def origin : Cell128 := (Hexagram.qian, false)
-- group laws (origin_xor, xor_self, xor_comm, xor_assoc)
end Cell128

-- AddCommGroup-flavour instances
instance : Add Cell128
instance : Zero Cell128
instance : Neg Cell128
instance : Sub Cell128
instance : SMul Cell128 Cell128

-- Cayley fusion
namespace Cell128
def cayley (c : Cell128) : Cell128 → Cell128
def epsAtOrigin (f : Cell128 → Cell128) : Cell128
@[simp] theorem epsAtOrigin_cayley (c : Cell128) : epsAtOrigin (cayley c) = c
theorem cayley_inj : Function.Injective cayley
theorem cayley_hom : ∀ c1 c2, cayley (xor c1 c2) = cayley c1 ∘ cayley c2
end Cell128

-- § 7 印 mask form
namespace Cell128
def yin_mask : Cell128 := (Hexagram.qian, true)
def yinM (c : Cell128) : Cell128 := xor c yin_mask
theorem yinM_eq_yin (c : Cell128) : yinM c = yin c
theorem yinM_yinM (c : Cell128) : yinM (yinM c) = c
end Cell128

-- § 8 Phase A summary
theorem cell128_phaseA_summary : ...

end SSBX.Foundation.Bagua.Cell128
```

## 附录 B：R₈ Cell256 完整 Lean 签名摘要

来自 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)：

```lean
namespace SSBX.Foundation.Bagua.Cell256

-- § 1 Shi V₄ + (因, 果) tensor (详见 shi-v4.md)
abbrev GuoBit : Type := Bool
inductive Shi : Type | dao | ji | jin | wei
-- ... cuo / zong / cuoZong / toYinGuo / ofYinGuo / yin / tou
-- (see shi-v4.md for full details)

-- § 2 Cell256 carrier
abbrev Cell256 : Type := Hexagram × Shi

namespace Cell256
def all : List Cell256
theorem all_length : all.length = 256
theorem all_nodup : all.Nodup
theorem mem_all (c : Cell256) : c ∈ all
def rootTo256TreeLevelCounts : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256]
end Cell256

-- § 3 lateral operators
namespace Cell256
def shiCuo (c : Cell256) : Cell256
def shiZong (c : Cell256) : Cell256
def shiCuoZong (c : Cell256) : Cell256
def hexCuo (c : Cell256) : Cell256
def hexZong (c : Cell256) : Cell256
def hexHu (c : Cell256) : Cell256
def flip1 (c : Cell256) : Cell256
-- flip2..flip6 (each preserve Shi, toggle one yao)
-- involutivity proofs (shiCuo_shiCuo, shiZong_shiZong, ...)
-- hex/shi commutativity (hexCuo_shiCuo_comm, ...)
end Cell256

-- § 4-6 序卦 + xuGua

-- § 7 Phase A: (Z/2)⁸ algebraic spine
namespace Cell256
def yaoXor (a b : Yao) : Yao
def hexXor (h1 h2 : Hexagram) : Hexagram
def shiXor (s1 s2 : Shi) : Shi
def xor (c1 c2 : Cell256) : Cell256
def origin : Cell256 := (Hexagram.qian, Shi.dao)
-- group laws (origin_xor, xor_self, xor_comm, xor_assoc)
end Cell256

instance : Add Cell256
instance : Zero Cell256
instance : Neg Cell256
instance : Sub Cell256
instance : SMul Cell256 Cell256

namespace Cell256
def cayley (c : Cell256) : Cell256 → Cell256
def epsAtOrigin (f : Cell256 → Cell256) : Cell256
@[simp] theorem epsAtOrigin_cayley (c : Cell256) : epsAtOrigin (cayley c) = c
theorem cayley_inj : Function.Injective cayley
theorem cayley_hom : ∀ c1 c2, cayley (xor c1 c2) = cayley c1 ∘ cayley c2
end Cell256

-- § 8 印/投 mask form
namespace Cell256
def yin_mask : Cell256 := (Hexagram.qian, Shi.ji)
def tou_mask : Cell256 := (Hexagram.qian, Shi.wei)
def yin (c : Cell256) : Cell256
def tou (c : Cell256) : Cell256
theorem yin_yin (c : Cell256) : yin (yin c) = c
theorem tou_tou (c : Cell256) : tou (tou c) = c
theorem yin_tou_comm (c : Cell256) : yin (tou c) = tou (yin c)
theorem yin_tou_eq_central (c : Cell256) : yin (tou c) = xor c (Hexagram.qian, Shi.jin)
theorem yin_mask_xor_tou_mask : xor yin_mask tou_mask = (Hexagram.qian, Shi.jin)
end Cell256

-- § 9 Phase A summary
theorem cell256_phaseA_summary : ...

end SSBX.Foundation.Bagua.Cell256
```

## 附录 C：术语对照

| 术语 | 在 R₇/R₈ | 在抽象代数 | 在物理 / 现象学 |
|---|---|---|---|
| 因 (yīn) | YinBit = R₇ axis | Z/2 generator | past lightcone marker / Husserl retention |
| 果 (guǒ) | GuoBit = R₈ axis | Z/2 generator | future lightcone marker / Husserl protention |
| 印 (yìn) | toggle 因 = XOR with `(qian, ji)` | XOR with YinBit-only mask | retain / record / stamp |
| 投 (tóu) | toggle 果 = XOR with `(qian, wei)` | XOR with GuoBit-only mask | project / cast / launch |
| 印 ∘ 投 | XOR with `(qian, jin)` | V₄ central element | PT compound (combined retention + protention) |
| 道 (dao) | (qian, dao) = origin | (Z/2)⁸ identity | reference vacuum / eternal anchor |
| 已 (ji) | (qian, ji) = yin_mask | (Z/2)⁸ generator | parity-like (P) / past-fixed |
| 未 (wei) | (qian, wei) = tou_mask | (Z/2)⁸ generator | time-reversal-like (T) / future-open |
| 今 (jin) | (qian, jin) = central mask | (Z/2)⁸ central element | PT now / present moment |

## 附录 D：与其它文档之关系

| 文档 | 与本文关系 |
|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | parent doctrine — § 3.7 R₇ / § 3.8 R₈ + § 4 算子代数 |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorems H/I/J 之严格陈述 + §16 命名候选 |
| [ox-notation.md](ox-notation.md) | OX 第 6 位 (因) / 第 7 位 (果) 之精确编码 |
| [shi-v4.md](shi-v4.md) | Shi V₄ = (因, 果) tensor 之完整 V₄ Klein 结构 |
| [lift-project.md](lift-project.md) | R₆ → R₇ lift 加 因; R₇ → R₈ lift 加 果 |
| [r5-wuyao-provisional.md](r5-wuyao-provisional.md) | R₅ 五爻 (provisional) — R₇/R₈ 之 unrelated descendant |
| [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | **R₇ ground truth** — YinBit + Cell128 + 印 + Cayley |
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | **R₈ ground truth** — Shi + Cell256 + 印/投 mask + Cayley |
| [`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) | R₇ R-index alias (re-export shim) |
| [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) | R₈ R-index alias (re-export shim) |
| [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | R₇/R₈ doctrine bundle (R8_complete theorem) |
