> **[v3 archive · superseded 2026-05-15 by wen-substrate v1.0.2]** — This doc is rooted in the F_2-only / Cell256-centric framing. See [`wen-substrate.md`](wen-substrate.md) §3.6 for the v1.0.2 parametric R-Family framework (R-Family-over-{F_2, ℝ, ℂ, ℂ_p, ...}) which subsumes and reframes the content here, and §4.1.5b for the carrier-vs-structure distinction. Kept for archival reference.

---

# Cell256 代数 spine — (Z/2)⁸ AddCommGroup + Cayley 自对偶

> 状态：v3 canonical (2026-05-11) — Cell128 / Cell256 之 algebraic spine：componentwise XOR 给出 (Z/2)⁷ 与 (Z/2)⁸ Abelian 群结构；Cayley regular representation `ι : Cell256 → (Cell256 → Cell256)` 把元变成自身上的左平移；ε(f) = f(origin) 是逆向 retraction；origin = (qian, dao) = V₄ identity = (Z/2)⁸ zero。
> 角色：本文是 Cell256 之"群论身份"专文。256 元清单与 quadrant 分布见 [`cell256-grid.md`](cell256-grid.md)；Shi 之 V₄ 群论见 [`v4-shi.md`](v4-shi.md)；Atomic / V4Outer 算子族划分见 [`operator-split.md`](operator-split.md)。
> 形式锚：[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7（Phase A — Algebraic Spine）+ [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 6（Phase A — (Z/2)⁷ spine）。

---

## 0. 一句话总纲

> **Cell256 = (Z/2)⁸ Abelian 群**，加法 = componentwise XOR，零元 = origin = (qian, dao)，每元素自逆 (`-c = c`)；自身上的左平移 `c ↦ (· ⊕ c)` 是 Cayley regular representation 之 group homomorphism `ι`；`ε(f) = f origin` 是其 retraction，`ε ∘ ι = id`；|Cell256| = |XOR(Cell256)| = 256，**self-action closure**。

---

## 1. Yao XOR — bit-level baseline

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.1（同样在 [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 6.1）：

```lean
def yaoXor (a b : Yao) : Yao :=
  match a, b with
  | .yang, .yang => .yang
  | .yang, .yin  => .yin
  | .yin,  .yang => .yin
  | .yin,  .yin  => .yang
```

`Yao.yang` 当 0（identity），`Yao.yin` 当 1。证：

| Lean 名 | 内容 |
|---|---|
| `yaoXor_yang_left b : yaoXor .yang b = b` | 左单位元 |
| `yaoXor_yang_right a : yaoXor a .yang = a` | 右单位元 |
| `yaoXor_self a : yaoXor a a = .yang` | 自逆 |
| `yaoXor_comm a b : yaoXor a b = yaoXor b a` | 交换 |
| `yaoXor_assoc a b c : yaoXor (yaoXor a b) c = yaoXor a (yaoXor b c)` | 结合 |

每证一行 `cases <;> rfl`：(Yao 是 2 元 inductive，4-case 完全 exhaust)。

---

## 2. Hexagram XOR — (Z/2)⁶ 层

```lean
def hexXor (h1 h2 : Hexagram) : Hexagram :=
  ⟨yaoXor h1.y1 h2.y1, yaoXor h1.y2 h2.y2, yaoXor h1.y3 h2.y3,
   yaoXor h1.y4 h2.y4, yaoXor h1.y5 h2.y5, yaoXor h1.y6 h2.y6⟩
```

逐爻 XOR。证：

| Lean 名 | 内容 |
|---|---|
| `hexXor_qian_left h : hexXor Hexagram.qian h = h` | 左单位 (qian = 全 yang) |
| `hexXor_qian_right h : hexXor h Hexagram.qian = h` | 右单位 |
| `hexXor_self h : hexXor h h = Hexagram.qian` | 自逆 |
| `hexXor_comm h1 h2 : hexXor h1 h2 = hexXor h2 h1` | 交换 |
| `hexXor_assoc` | 结合 |

R₆ Hexagram 由此成为 (Z/2)⁶ Abelian 群，单位元 = `Hexagram.qian`。

---

## 3. Shi XOR — V₄ Klein 层

V₄ 的 XOR 通过 (因, 果) ∈ Bool² 双射拉回到双 Bool componentwise XOR：

```lean
def shiXor (s1 s2 : Shi) : Shi :=
  let (y1, g1) := Shi.toYinGuo s1
  let (y2, g2) := Shi.toYinGuo s2
  Shi.ofYinGuo (Bool.xor y1 y2, Bool.xor g1 g2)
```

证：

| Lean 名 | 内容 |
|---|---|
| `shiXor_dao_left s : shiXor Shi.dao s = s` | 道 = V₄ identity |
| `shiXor_dao_right s : shiXor s Shi.dao = s` | 同上 |
| `shiXor_self s : shiXor s s = Shi.dao` | 自逆 (V₄ 性质) |
| `shiXor_comm s1 s2 : shiXor s1 s2 = shiXor s2 s1` | 交换 |
| `shiXor_assoc` | 结合 |

Shi V₄ 之群结构与 cuo / zong / cuoZong involutions 之关系详见 [`v4-shi.md`](v4-shi.md)。

---

## 4. Cell256 XOR — (Z/2)⁸ 全闭合

```lean
def Cell256.xor (c1 c2 : Cell256) : Cell256 :=
  (hexXor c1.1 c2.1, shiXor c1.2 c2.2)

def Cell256.origin : Cell256 := (Hexagram.qian, Shi.dao)
```

`origin` = (qian, dao) = V₄ identity 在 Hexagram × Shi 上的 first-light。

完整群律证（[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.4）：

| Lean 名 | 内容 |
|---|---|
| `origin_xor c : xor origin c = c` | 左单位 |
| `xor_origin c : xor c origin = c` | 右单位 |
| `xor_self c : xor c c = origin` | 自逆 (无需 `Neg`，每元素阶 ≤ 2) |
| `xor_comm c1 c2 : xor c1 c2 = xor c2 c1` | 交换 |
| `xor_assoc c1 c2 c3 : xor (xor c1 c2) c3 = xor c1 (xor c2 c3)` | 结合 |

|Cell256| = 256 = (Z/2)⁸。

---

## 5. AddCommGroup 实例

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.5 绑定 Lean 标准 `Add / Zero / Neg / Sub` typeclass：

```lean
instance : Add Cell256 := ⟨Cell256.xor⟩
instance : Zero Cell256 := ⟨Cell256.origin⟩
/-- In (Z/2)ⁿ every element is self-inverse: `-c = c`. -/
instance : Neg Cell256 := ⟨id⟩
instance : Sub Cell256 := ⟨Cell256.xor⟩
```

简化等式：

```lean
@[simp] theorem Cell256.add_def (c1 c2 : Cell256) : c1 + c2 = xor c1 c2 := rfl
@[simp] theorem Cell256.zero_def : (0 : Cell256) = origin := rfl
@[simp] theorem Cell256.neg_def (c : Cell256) : -c = c := rfl
@[simp] theorem Cell256.sub_def (c1 c2 : Cell256) : c1 - c2 = xor c1 c2 := rfl
```

注意：本 Foundation 文件**不 import Mathlib**，因此没有显式 `AddCommGroup Cell256` instance。但所有 `AddCommGroup` 之 underlying laws (`add_zero / zero_add / add_assoc / add_comm / sub_self / neg_self`) 都已逐条证明（见 § 4 之 `origin_xor / xor_origin / xor_assoc / xor_comm / xor_self / neg_def`）。任何下游模块如需要 typed `AddCommGroup`，只需 `import Mathlib` 后给出一行 `instance : AddCommGroup Cell256 := { ... }` 把这些 lemmas 串起来即可。Cell128 同此。

---

## 6. SMul self-action — Cayley regular representation

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.6：

```lean
instance : SMul Cell256 Cell256 := ⟨Cell256.xor⟩
@[simp] theorem Cell256.smul_def (c s : Cell256) : c • s = xor c s := rfl
```

Cell256 自身 act 自身 — 这是 finite-group 的 **Cayley 自对偶 / regular representation**。

### 6.1 Cayley 同态 ι

```lean
def Cell256.cayley (c : Cell256) : Cell256 → Cell256 := fun s => xor c s
```

`cayley c` = "用 c 左平移"。

### 6.2 ε retraction (evaluate at origin)

```lean
def Cell256.epsAtOrigin (f : Cell256 → Cell256) : Cell256 := f origin
```

ε 把 Cell256 endomorphism 求值在 origin (= 道) — 「道是 fusion anchor」之精确数学含义。

### 6.3 ι 的核心三性质

| Lean 名 | 形式 | 解读 |
|---|---|---|
| `Cell256.epsAtOrigin_cayley c : epsAtOrigin (cayley c) = c` | $\varepsilon \circ \iota = \mathrm{id}_{\text{Cell256}}$ | retraction |
| `Cell256.cayley_inj : Function.Injective cayley` | $\iota$ injective | 唯一性 |
| `Cell256.cayley_hom c1 c2 : cayley (xor c1 c2) = cayley c1 ∘ cayley c2` | $\iota$ group hom | 结构保持 |

证明思路：

- `epsAtOrigin_cayley`: $\varepsilon(\iota(c)) = (\iota(c))(origin) = c \oplus origin = c$，由 `xor_origin`。
- `cayley_inj`: $\iota(c_1) = \iota(c_2) \Rightarrow \iota(c_1)(origin) = \iota(c_2)(origin) \Rightarrow c_1 = c_2$。
- `cayley_hom`: `funext s; simp [cayley, xor_assoc]` — 即 $((c_1 \oplus c_2) \oplus s) = (c_1 \oplus (c_2 \oplus s))$。

整合：**Cell256 ≅ Im(ι) ⊆ Aut(Cell256)** — 这是 finite group 之 Cayley 嵌入定理的具体落地。

---

## 7. (Z/2)⁸ self-duality — |Cell256| = |XOR(Cell256)|

由 ι injective + ε retraction：

$$|\mathrm{Cell256}| = |\mathrm{Im}(\iota)| = |\mathrm{XOR}(\mathrm{Cell256})| = 256$$

即 **元-集 与 自身-XOR-action-集 同基数**。这是 R-O fusion 之精确数学条件（详 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 5.1）：

> 「自描述」之精确数学条件 = abelian self-action with chosen origin.
> 道 = origin = identity = no-op = 永真 cell = fusion anchor — 一个 8-bit 字符串承担五重身份。

---

## 8. Pontryagin 自对偶 (备注)

R-O hierarchy 视角下另一个 self-duality 是 Pontryagin：

$$\widehat{R_8} := \mathrm{Hom}(R_8, U(1)) \cong (\mathbb{Z}/2)^8 \cong R_8$$

任意 finite abelian group `G` 之 character group $\hat{G}$ 同构于 `G`；对 (Z/2)⁸ 而言，character 取值可落在 {±1} = ℤ/2。当前 Lean 完成的是 finite Boolean character skeleton，而不是 analytic `U(1)` character theory：

| Lean anchor | 含义 |
|---|---|
| `V4Tensor.maskCharacter` | R₈ mask 表示一个 `R8 → Bool` character |
| `V4Tensor.maskCharacter_xor` | character 对 XOR 保结构 |
| `V4Tensor.maskCharacter_injective` | 不同 mask 给出不同 character |
| `V4Tensor.r8_equiv_mask_character_image` | `R8 ≃ MaskCharacterImage` |

同一模块还把 Cayley side 补成真正双射:

| Lean anchor | 含义 |
|---|---|
| `V4Tensor.r8_equiv_xor_operator` | `R8 ≃ XorOperator` |
| `V4Tensor.cell_operator_comp` | 算子复合 = 代表元 XOR |
| `V4Tensor.cell_operator_self_inverse` | 每个 represented XOR operator 自逆 |

因此 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 5.2 / 5.4 中的「Triple Coincidence」当前应读作 finite-decidable closure 内的 Cayley represented-operator self-duality + Boolean character self-duality；analytic `U(1)` 外延未声称已建。

| Duality | 形式 | 在 R₈ 上 |
|---|---|---|
| Cayley | element ↔ self-action | R₈ ≅ XOR(R₈) (本文 § 6 严格 Lean 化) |
| Pontryagin | element ↔ character | R₈ ≅ finite Boolean character image |
| R-O frame | state-side ↔ operator-side | 同一 8-bit 二种 viewing |

---

## 9. Cell128 之 Phase A — (Z/2)⁷ 平行版本

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 6/§ 7 给出 (Z/2)⁷ 之同构 spine：

```lean
def Cell128.xor (c1 c2 : Cell128) : Cell128 :=
  (hexXor c1.1 c2.1, Bool.xor c1.2 c2.2)

def Cell128.origin : Cell128 := (Hexagram.qian, false)

instance : Add Cell128 := ⟨Cell128.xor⟩
instance : Zero Cell128 := ⟨Cell128.origin⟩
instance : Neg Cell128 := ⟨id⟩
instance : Sub Cell128 := ⟨Cell128.xor⟩
instance : SMul Cell128 Cell128 := ⟨Cell128.xor⟩

def Cell128.cayley (c : Cell128) : Cell128 → Cell128 := fun s => xor c s
def Cell128.epsAtOrigin (f : Cell128 → Cell128) : Cell128 := f origin

theorem Cell128.epsAtOrigin_cayley (c : Cell128) : epsAtOrigin (cayley c) = c
theorem Cell128.cayley_inj : Function.Injective cayley
theorem Cell128.cayley_hom (c1 c2 : Cell128) :
    cayley (xor c1 c2) = cayley c1 ∘ cayley c2
```

R₇ 上 V₄ 退化为 Z/2（只有 YinBit 一轴），但 Cayley 自对偶仍成立 — 即 Cell128 自身上的左平移构成全 128-元 abelian 群之 regular representation。R₈ 比 R₇ 多 1 bit (GuoBit)，整套机制无变化。

---

## 10. R₈ Phase A 摘要定理

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 9 之 `cell256_phaseA_summary`：

```lean
theorem cell256_phaseA_summary :
    -- (Z/2)⁸ identity + group laws
    (∀ c : Cell256, Cell256.xor Cell256.origin c = c)
    ∧ (∀ c : Cell256, Cell256.xor c c = Cell256.origin)
    ∧ (∀ a b : Cell256, Cell256.xor a b = Cell256.xor b a)
    ∧ (∀ a b c : Cell256,
        Cell256.xor (Cell256.xor a b) c = Cell256.xor a (Cell256.xor b c))
    -- Cayley fusion
    ∧ Function.Injective Cell256.cayley
    ∧ (∀ c : Cell256, Cell256.epsAtOrigin (Cell256.cayley c) = c)
    -- 印 / 投 mask involutions + commute
    ∧ (∀ c : Cell256, Cell256.yin (Cell256.yin c) = c)
    ∧ (∀ c : Cell256, Cell256.tou (Cell256.tou c) = c)
    ∧ (∀ c : Cell256, Cell256.yin (Cell256.tou c) = Cell256.tou (Cell256.yin c))
```

10 项一并 — (Z/2)⁸ 群律 4 项 + Cayley fusion 2 项 + 印/投 mask involutions 3 项。Cell128 之 § 8 `cell128_phaseA_summary` 是 R₇ 平行版本（少 GuoBit / `tou`，多 `yinM_eq_yin` 之 mask-vs-direct equivalence）。

---

## 11. R₈ closure bundle

[`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) § 7 之 `R8_complete` 把整个 R₈ 闭合层之所有保证打包：

- (1) 基数 256
- (2) R-hierarchy: R₈ = R₆ × Shi (definitional)
- (3) 算子 P/T/Y closure (parity / timeReversal / yComb)
- (4) 群作用 (Z/2)⁸ simply transitive on R₈ (经 anchor (qian, dao))
- (5) BenZheng 投影 + Mian 特权 (Mian only on benZheng quadrant)
- (6) 位置-算子树双射 (Sheng 6 × Shi ≃ R₈)
- (7) xuGua extension to R₈ (xuGua256: 256 元有序列)

`#print axioms R8_complete` 只依赖 `propext` + `native_decide` attestations，**无项目自定义公理**。

---

## 12. 与其他文档之关系

| 文档 | 关系 |
|---|---|
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 5 | 自对偶定理 (Cayley + Pontryagin + R-O frame Triple Coincidence) |
| [`yi-calculus-theorem.md`](yi-calculus-theorem.md) Theorem K | R-hierarchy R₁..R₈ 全 (Z/2)ⁿ closure |
| [`cell256-grid.md`](cell256-grid.md) | Cell256 之 256 元 ground inventory |
| [`v4-shi.md`](v4-shi.md) | Shi V₄ 群论之专文 |
| [`yin-tou-operators.md`](yin-tou-operators.md) | 印/投 mask form (= XOR with `yin_mask` / `tou_mask`) |
| [`operator-split.md`](operator-split.md) | Atomic XOR vs V4Outer perm 之总览 |
| [`lift-project.md`](lift-project.md) | 跨层 retract `proj ∘ lift = id` |

---

## 形式锚 (Lean modules)

- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7–§ 9 — Phase A spine, AddCommGroup-flavoured instances, Cayley `ι/ε`, `cell256_phaseA_summary`
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 6–§ 8 — Phase A spine (Z/2)⁷, `Cell128.cayley_inj`, `cell128_phaseA_summary`
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) § 7 — `R8_complete` closure bundle
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Yao`, `Hexagram`, `Hexagram.qian`
