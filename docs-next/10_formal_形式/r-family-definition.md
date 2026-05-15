# R-Family Definition (D2 — single source of truth)

> **Status**: D2 documentation companion to `wen-substrate.md` v1.0.3 §3.1.
> Scope: concretizes the 12-item structural definition of R-Family-over-$\mathbb{F}_2$
> as one mathematical object, bundles the existing Lean-side components, and
> positions the result against the parametric extension (D3) and Phase 0
> theorems (D4).

## Preface

This document concretizes [`wen-substrate.md`](./wen-substrate.md) v1.0.3 §3.1
(the 12-item definition of R-Family-over-$\mathbb{F}_2$) into a **single
mathematical object**, and points at the Lean modules that collectively realize
each item. Where wen-substrate v1.0.3 §3.1 lists 12 components in prose, this
document presents the same content as one structured tuple, gives it a
mathematical type, and indexes the code anchors.

**Why D2 exists**. Prior to D2, the 12 items of §3.1 were scattered across the
Lean tree (`Foundation/R/Basic.lean`, `Foundation/R/DirectSum.lean`,
`Foundation/R/Bilinear.lean`, `Foundation/R/Squaring.lean`, `Foundation/R/Hom.lean`,
`Foundation/R4/HomMat.lean`, `Foundation/R4/EndR2.lean`,
`Foundation/RInfty/Profinite.lean`, `Foundation/Atlas/Yi/ShiV4.lean`,
`Foundation/Atlas/Yi/Bagua.lean`, `Foundation/Atlas/Yi/Operators.lean`). No
single source bundled them into a coherent statement of **what R-Family is, as
one object**. D2 fills that gap on the documentation side; the companion Lean
module `Foundation.R.RFamilyStructure` fills the corresponding code-side gap.

**Cross-references**.
- `wen-substrate.md` v1.0.3 §3.1 (the 12-item definition).
- `wen-substrate.md` v1.0.3 §3.6 (parametric extension over arbitrary base $k$).
- [`r-family-parametric-bases.md`](./r-family-parametric-bases.md) — **D3**
  companion documenting the parametric framework per base.
- Phase 0 theorem-level discharge (D4) is forthcoming; this document does
  **not** prove the closure properties, only states the structural bundling.

**Reading order**. Read §1 to see the tuple. Read §2 for the categorical /
structural type. Read §3 for the parametric extension recap (or skip to D3 for
the full instantiation table). Read §4 for the code anchor map. Read §5 for the
reading guide that maps wen-substrate §3.1 line-by-line to this document.

---

## §1 The R-Family Object

**Definition (R-Family-over-$\mathbb{F}_2$, as a structured object)**. R-Family-over-$\mathbb{F}_2$ is the tuple

$$\mathcal{R}^{(\mathbb{F}_2)} \;:=\; \bigl(\,
\mathrm{Carrier},\;
\mathrm{Origin},\;
\oplus,\;
\mathrm{Rel},\;
\mathrm{Tower},\;
\mathrm{Hom},\;
\mathrm{Ring}_4,\;
\mathrm{Depth},\;
\mathrm{Modality}_2,\;
\mathrm{Alphabet}_3,\;
\mathrm{Atomic}_4,\;
\mathrm{Self}
\,\bigr)$$

instantiating the 12 items of `wen-substrate.md` v1.0.3 §3.1:

### Item 1 — Base elements (Carrier)

$$R_N \;:=\; \mathbb{F}_2^N \qquad (N \in \mathbb{N}_0)$$

The carrier family is $\{R_N\}_{N \in \mathbb{N}_0}$ — one $\mathbb{F}_2$-vector
space at each natural-number level. $|R_N| = 2^N$.

### Item 2 — Undifferentiated origin

$$R_0 \;=\; \{0\}, \qquad \text{the singleton (trivial) } \mathbb{F}_2\text{-space.}$$

R-Family **starts here**. $R_0$ is the **无极** (wu-ji, "no-polarity") layer:
the origin of all distinction, before any bit is committed.

### Item 3 — Composition (direct sum)

$$R_M \oplus R_N \;\cong\; R_{M+N}$$

The natural $\mathbb{F}_2$-direct-sum is **the** composition on the family: it
is the unique $\mathbb{F}_2$-natural way of combining two layers into a larger
layer, with the index $\mathbb{N}_0$ acting as the dimension grading.

### Item 4 — Three bilinear/quadratic layers (Relations)

Three layers of bilinear/quadratic structure:

- **L0 — Symmetric**: $\langle u, v \rangle = \sum_i u_i v_i$ (over $\mathbb{F}_2$,
  i.e. XOR of pairwise ANDs). Defined for all $N$.
- **L1 — Alternating**: $\sigma(u, v)$, the symplectic form on $R_{2k}$ for
  even-N levels.
- **L2 — Arf-classified quadratic refinements**: a family $\{q^c\}$ of quadratic
  refinements of $\sigma$, classified by the Arf invariant
  $\mathrm{arf}(c) = \bigoplus_k c_k$. There are exactly two Arf-classes
  ($0$ and $1$) of refinement at each even $R_{2k}$.

L0/L1/L2 together exhaust the bilinear/quadratic content of an $\mathbb{F}_2$-vector
space; see wen-substrate v1.0.3 §4 and `Foundation/R/Bilinear.lean`.

### Item 5 — Squaring tower with self-similarity

The squaring sub-tower

$$R_0 \;\hookrightarrow\; R_1 \;\hookrightarrow\; R_2 \;\hookrightarrow\; R_4 \;\hookrightarrow\; R_8 \;\hookrightarrow\; \cdots \;\hookrightarrow\; R_\infty$$

is equipped with three coherent natural maps:

- **Diagonal embedding** $\Delta_N : R_N \hookrightarrow R_{2N}, \quad v \mapsto (v, v)$
- **Projections** $\pi_i : R_{2N} \to R_N \quad (i \in \{0, 1\})$
- **Operation lift** $f \mapsto f^{\oplus 2}$, where for $f : R_N \to R_M$ we set
  $f^{\oplus 2}(u, v) := (f(u), f(v))$

These commute across scales — the tower is **self-similar**: any structure
defined at $R_N$ lifts coherently to $R_{2N}$.

### Item 6 — Self-referential morphism spaces (Hom-as-content)

$$\mathrm{Hom}_{\mathbb{F}_2}(R_n, R_m) \;\cong\; R_m \otimes R_n^* \;\cong\; R_{nm}$$

The morphism space is itself a member of the family. Hom-as-content is the
P5-property of wen-substrate: R-Family **internalizes its own morphisms**, so
that any linear map between two layers lives as a vector in a (third) layer.

### Item 7 — Canonical ring structure at $R_4$

$$R_4 \;\cong\; \mathrm{End}_{\mathbb{F}_2}(R_2) \;\cong\; M_2(\mathbb{F}_2)$$

as $\mathbb{F}_2$-algebras. This is **forced** — not chosen — by Item 6 applied
to the smallest non-trivial Hom-space ($\mathrm{Hom}(R_2, R_2)$), with
multiplication = composition of endomorphisms = matrix multiplication. By
Wedderburn-Artin, $M_2(\mathbb{F}_2)$ is the unique minimal non-commutative
central simple $\mathbb{F}_2$-algebra. So $R_4$ carries a canonical ring
structure with no degrees of freedom.

### Item 8 — Recursive depth

$$R_\infty \;=\; \hat{R} \;:=\; \lim_{\leftarrow}\,R_{2^k}$$

The inverse limit of the squaring tower under the bonding maps
$\pi_{k+1, k} : R_{2^{k+1}} \to R_{2^k}$ (first-half projection at each level).
Topologically, $R_\infty$ is a Cantor space — the profinite completion of the
squaring sub-tower. This is the **万物** (wan-wu, "ten-thousand-things") layer:
the formal limit point of recursive extension.

### Item 9 — $R_2$ as universal 4-modality carrier

$$R_2 \;\cong\; \mathbb{F}_2^2 \;\cong\; V_4 \quad (\text{Klein four-group}).$$

$R_2$ takes different semantic content in different roles:

- **四象** cosmologically (老阴 / 少阴 / 少阳 / 老阳).
- **$V_4$ transformations on hexagrams**: $\{\mathrm{id}, \mathrm{cuo}, \mathrm{zong}, \mathrm{cuo} \circ \mathrm{zong}\}$.
- **Dynamical modalities in $R_6$**.
- **Temporal modalities in $R_8 = R_6 \oplus R_2$**: $\{$道, 已, 今, 未$\}$.

$R_2$ is the **smallest carrier of 4-modality structure** — both algebraically
(as $V_4$) and as a Lorentzian 4-region causal carrier. This is the modality
component of the substrate.

### Item 10 — Aspect alphabet at $R_3$

$$R_3 \;=\; \mathbb{F}_2^3, \qquad |R_3| = 8 \quad (\text{the 8 trigrams}).$$

The 8 elements split as $4 + 4$ under the **zong involution** (reversal of the
3-tuple): 4 self-zong-fixed elements (**本**, "essence") and 4 elements forming
2 zong-pairs (**征**, "manifestation"). This 4 本 + 4 征 split is **forced** by
zong, not chosen. $R_3$ is the smallest single-axis aspect alphabet.

### Item 11 — Atomic operations at $R_4$

$$R_4 \;\cong\; M_2(\mathbb{F}_2), \qquad |R_4| = 16$$

The 16 atomic operations are simultaneously:

- **Linear endomorphisms of $R_2$** (item 7 view).
- **(本, 征) pairs** = aspect × manifestation, i.e. the product of two copies
  of the $R_3$ split structure.

This is the joint atomic-operation algebra at $R_4$ — the smallest joint
carrier and the smallest non-commutative central simple $\mathbb{F}_2$-algebra
(Wedderburn-Artin).

### Item 12 — Self-following (道法自然)

R-Family **generates itself** from $R_0$ to $R_\infty$ via internal operations:

- $R_0$ is the starting point (item 2).
- $R_{N+1}$ is obtained from $R_N$ by direct sum with $R_1$ (item 3).
- $R_{2N}$ is the squaring step (item 5).
- $\mathrm{Hom}$ closures land back inside the family (item 6).
- The limit $R_\infty$ closes the recursion (item 8).

Nothing external is invoked. This is the self-following / **道法自然** property
of wen-substrate v1.0.3 §3.5.6.

---

## §2 Mathematical type

We give R-Family-over-$\mathbb{F}_2$ a **structural type** beyond the tuple:

### §2.1 Layered reading

R-Family is, in increasing order of structure:

1. A **graded family of $\mathbb{F}_2$-modules** indexed by $\mathbb{N}_0$
   (items 1, 2).
2. Equipped with a **biproduct** structure on the family — the natural direct
   sum $\oplus$ acts as both coproduct and product on $\{R_N\}$ (item 3).
3. Plus a **bilinear-classification** at each level — L0 always, L1 at even
   levels, L2 Arf-classified at each $R_{2k}$ (item 4).
4. Plus a **self-referential Hom-internal** structure — $\mathrm{Hom}(R_n, R_m) \cong R_{nm}$
   internalized in the family itself, with $R_4 \cong \mathrm{End}(R_2)$ as the
   smallest closure point (items 6, 7).
5. Plus a **filtered tower with self-similarity** — the squaring sub-tower
   with $\Delta_N, \pi_i, f^{\oplus 2}$ coherent across scales (item 5).
6. Plus a **completion** — $R_\infty$ as the inverse limit, a Cantor space
   topologically (item 8).
7. Plus a **modality / aspect / atomic** layering at low $N$ — $R_2$ as
   4-modality $V_4$, $R_3$ as 8-aspect with 4+4 zong-split, $R_4$ as the
   16-atomic-operation matrix ring (items 9, 10, 11).
8. Closed under all the above — **self-following** is the assertion that
   nothing external is needed (item 12).

### §2.2 Categorical reading

In categorical terms, R-Family-over-$\mathbb{F}_2$ is the **smallest closed
substrate** under

$$\{\text{distinction},\, \text{composition},\, \text{relation},\, \text{operation},\, \text{recursion},\, \text{self-articulation}\}$$

starting from $\mathbb{F}_2$. Each closure operation maps to one structural
feature above:

| Closure operation | Substrate feature                                  | Items     |
| ----------------- | -------------------------------------------------- | --------- |
| distinction       | $R_0 \to R_1$ (the smallest non-trivial $R_N$)     | 1, 2      |
| composition       | $\oplus$ (direct sum), $R_M \oplus R_N \cong R_{M+N}$ | 3      |
| relation          | L0/L1/L2 bilinear-quadratic layers                 | 4         |
| operation         | $\mathrm{Hom}$ as content, ring-at-$R_4$           | 6, 7, 11  |
| recursion         | squaring tower with self-similarity, $R_\infty$    | 5, 8      |
| self-articulation | $R_2$ modality, $R_3$ alphabet, $R_4$ atomic ops   | 9, 10, 11 |
| closure           | self-following — nothing external                  | 12        |

### §2.3 Equivalent characterizations

R-Family-over-$\mathbb{F}_2$ admits at least three equivalent presentations:

- **As a tuple** (§1): the 12-item structured object.
- **As a closure** (§2.2): the smallest substrate closed under the 7 operations.
- **As a parametric instance** (§3 below): the $k = \mathbb{F}_2$ specialization
  of R-Family-over-$k$.

All three pick out the same mathematical object.

---

## §3 Parametric extension

Per `wen-substrate.md` v1.0.3 §3.6, the 12-item structure presented in §1 is
the **$k = \mathbb{F}_2$ instance** of a parametric framework
**R-Family-over-$k$**. We recap the essentials; for the full per-base
instantiation table, see [D3 — `r-family-parametric-bases.md`](./r-family-parametric-bases.md).

### §3.1 The parametric pattern

For any non-trivial commutative ring (cleanest: field) $k$, define

$$\mathcal{R}^{(k)} \;:=\; \bigl(\, \{R_N^{(k)} = k^N\}_{N},\; \oplus_k,\; \mathrm{Hom}_k,\; \mathrm{Rel}^{(k)},\; \mathrm{Tower}^{(k)},\; \mathrm{Modality}^{(k)},\; \mathrm{Self}^{(k)} \,\bigr)$$

Each item 1-12 of §1 lifts parametrically with **char-dependent adjustments**
to the bilinear-quadratic layer (Item 4):

- **Item 1, 2, 3, 5, 6, 8** lift verbatim (replace $\mathbb{F}_2$ by $k$).
- **Item 4 (bilinear-quadratic layers)** is char-dependent: in char $\neq 2$,
  symmetric and alternating split, and quadratic refinements behave
  differently. See wen-substrate §3.6.3.
- **Item 7** lifts as $R_4^{(k)} \cong M_2(k)$ — a ring at every base.
- **Items 9, 10, 11** lift, with the 4-modality / 8-aspect / 16-atomic readings
  taking $|k|$-many values per coordinate instead of 2.
- **Item 12** lifts: $\mathcal{R}^{(k)}$ self-follows over any $k$.

### §3.2 Status

- $\mathbb{F}_2$ instance: **fully Lean-formalized** (current document, items
  1-12 as §1).
- Other bases ($\mathbb{R}, \mathbb{C}, \mathbb{C}_p, \mathbb{Z}_p, \mathbb{Q}_p,
  \overline{\mathbb{F}_2}, \ldots$): **defined** structurally in §3.6; per-base
  Lean coverage tracked in D3.
- See `r-family-parametric-bases.md` §2 for per-base carriers, P1-P7
  specializations, and transfer functors.

---

## §4 Code anchor

The 12 items of §1 are realized **collectively** by the following Lean modules.
The umbrella module `Foundation.R.RFamilyStructure` (introduced in this D2
patch) re-exports them as a navigation hub.

| Item | Component                  | Lean module                                                       |
| ---- | -------------------------- | ----------------------------------------------------------------- |
| 1    | Carriers $R_N$             | `Foundation/R/Basic.lean` — `R N := Fin N → Bool`                 |
| 2    | Origin $R_0$               | `Foundation/R/Basic.lean` — `R 0` (with `R0_subsingleton`)        |
| 3    | Direct sum                 | `Foundation/R/DirectSum.lean` — `R.directSumEquiv`                |
| 4    | L0/L1/L2 bilinear layers   | `Foundation/R/Bilinear.lean` — dot / sigma / `q^c` / Arf          |
| 5    | Squaring tower             | `Foundation/R/Squaring.lean` — `squaringEquiv` + concrete witnesses |
| 6    | Hom-as-content             | `Foundation/R/Hom.lean` (base) + `Foundation/R4/HomMat.lean` (matrix-of-$R_4$ view) |
| 7    | Ring structure at $R_4$    | `Foundation/R4/EndR2.lean` — `applyR2`, `composeR2`, `idR4`       |
| 8    | $R_\infty$                 | `Foundation/RInfty/Profinite.lean` — `L_inf` as inverse limit / Cantor |
| 9    | $R_2$ as $V_4$ modality    | `Foundation/Atlas/Yi/ShiV4.lean` — `Shi` (= 道/已/今/未)           |
| 10   | $R_3$ aspect alphabet      | `Foundation/Atlas/Yi/Bagua.lean` — 8 trigrams; zong split via `Foundation/Atlas/Yi/Operators.lean` |
| 11   | Atomic operations at $R_4$ | `Foundation/R4/EndR2.lean` + `Foundation/R4/Enumeration.lean` (16 atoms) |
| 12   | Self-following / umbrella  | `Foundation/R.lean` — pulls the whole subtree in one import       |

**Parametric extension** (§3): `Foundation/R/Parametric.lean` — `RFamily k N :=
Fin N → k`, with `Bool`-specialization recovering the $\mathbb{F}_2$ instance
definitionally.

**Aggregator** (this D2 patch): `Foundation/R/RFamilyStructure.lean` — the
**single source-of-truth module** that imports the above and serves as the
navigation hub. Downstream code looking for "R-Family as one object" should
import or cite `Foundation.R.RFamilyStructure`.

---

## §5 Reading guide

### §5.1 wen-substrate.md → r-family-definition.md cross-walk

| wen-substrate v1.0.3                 | r-family-definition.md   | Notes                                           |
| ------------------------------------ | ------------------------ | ----------------------------------------------- |
| §3.1 (12-item definition)            | §1 (Items 1-12)          | The bundling                                    |
| §3.1 item 1-2 (carriers + $R_0$)     | §1 Items 1-2             | —                                               |
| §3.1 item 3 (direct sum)             | §1 Item 3                | —                                               |
| §3.1 item 4 (bilinear layers)        | §1 Item 4                | L0/L1/L2 detail per wen-substrate §4            |
| §3.1 item 5 (squaring tower)         | §1 Item 5                | —                                               |
| §3.1 item 6 (Hom-as-content)         | §1 Item 6                | $\mathrm{Hom}(R_n, R_m) \cong R_{nm}$           |
| §3.1 item 7 (ring at $R_4$)          | §1 Item 7                | Wedderburn-forced                               |
| §3.1 item 8 ($R_\infty$)             | §1 Item 8                | Cantor profinite limit                          |
| §3.1 item 9 ($R_2$ as $V_4$)         | §1 Item 9                | 4-modality carrier                              |
| §3.1 item 10 ($R_3$ alphabet)        | §1 Item 10               | 4 本 + 4 征                                     |
| §3.1 item 11 (atomic at $R_4$)       | §1 Item 11               | 16 atomic ops                                   |
| §3.1 item 12 (self-following)        | §1 Item 12               | 道法自然                                        |
| §3.6 (parametric over $k$)           | §3 (parametric recap)    | Full detail → D3                                |

### §5.2 Position relative to D3 and D4

- **D2 (this document)**: "What is R-Family?" — bundles §3.1 into one object
  + maps to code anchors. Read this **first** to know what R-Family is
  structurally.
- **D3 (`r-family-parametric-bases.md`)**: "What is R-Family-over-$k$ for $k
  \neq \mathbb{F}_2$?" — instantiates §3.6 per base, with transfer functors and
  per-base Lean status. Read for **breadth** across bases.
- **D4 (forthcoming Phase 0 theorems)**: "Why is R-Family universal /
  unique?" — discharges the proof obligations of wen-substrate Part VIII
  (T1–T5: existence, minimality, universality, generative coverage,
  uniqueness-up-to-equivalence). Read for **theoretical justification**.

D2 is the structural / definitional document. D3 is the parametric breadth
companion. D4 is the proof-side companion.

---

## Version history

- **v1.0** (2026-05-16): Initial D2 release. Bundles wen-substrate v1.0.3 §3.1
  into one structured-tuple definition (§1), gives the mathematical type (§2),
  recaps the parametric extension (§3), maps to existing Lean code anchors (§4),
  and provides a wen-substrate → D2 cross-walk (§5). Companion Lean module
  `Foundation/R/RFamilyStructure.lean` introduced in the same patch.
