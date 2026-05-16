# R-Family Parametric Bases (D3 companion)

> **Status**: D3 documentation companion to `wen-substrate.md` v1.4 §3.6 + §3.7.8 (now in [`wen-substrate/02-parametric.md`](./wen-substrate/02-parametric.md) and [`wen-substrate/03-operation-monism.md`](./wen-substrate/03-operation-monism.md)).
> Scope: concretizes the **algebraic-class** R-Family parametric framework per base; lists transfer
> functors between bases; maps Lean coverage to theoretical bases. The non-algebraic δ-realisations are siblings, surveyed at the end of §2.

## v1.4 reframing — δ-realisation parameter and the algebraic-class subset

Per `wen-substrate.md` v1.4 §3.7.8 (distinction monism), the substrate-most-primitive parameter is the **realisation δ** of the primitive binary distinction `o`/`x`. This document treats the **algebraic-class subset** of δ-realisations: those where δ = k for k a ring or field. The k-parametric framework of §3.6 (wen-substrate v1.0+) is preserved verbatim under this re-reading; what changes is that "base k" is now understood as the algebraic-class case of a broader **δ-realisation framework**, with non-algebraic δ-realisations (quantum basis labels, propositional `Prop`, per-language vocabularies, traditional 阳/阴) as first-class siblings.

Throughout this document, **k = ring/field** is the algebraic-class subset; **δ = realisation** is the broader parameter. Headers continue to read "base k" or "k = ℝ" etc. for the algebraic instances; the non-algebraic table at the end of §2 lays out the siblings. Companion Lean file [`Foundation/R/Distinction.lean`](../../formal/SSBX/Foundation/R/Distinction.lean) (~230 LOC, 0 sorry, 0 axiom) provides the substrate-most-primitive layer; the polymorphic `R N (δ : Type := Bool) : Type := Fin N → δ` in [`Foundation/R/Basic.lean`](../../formal/SSBX/Foundation/R/Basic.lean) (Route 3B refactor, 2026-05-16) makes the δ-substrate available to Lean code while preserving backward compatibility for the canonical δ = Bool default.

## Preface

This document concretizes [`wen-substrate/02-parametric.md`](./wen-substrate/02-parametric.md) — the
algebraic-class R-Family parametric framework over a base $k$. wen-substrate states the
abstract framework: R-Family is a **structural pattern** instantiable as
**R-Family-over-$k$** for various bases $k$, with the same P1–P7 closure
conditions stated parametrically (Layer A) and base-specific properties
(Layer B) varying per instance.

This document does **not** re-derive the framework — it instantiates it.
Section §1 recaps the parametric structure. Section §2 walks through six
canonical bases ($\mathbb{F}_2, \mathbb{F}_p, \mathbb{R}, \mathbb{C},
\mathbb{C}_p, \mathbb{Z}_p$) listing per-instance carrier definitions,
characteristic, P1–P7 specialization, and Lean-formalization status.
Section §3 catalogs the **transfer functors** linking instances. Section §4
gives the code-vs-theory status and what would be needed to lift the Lean
formalization beyond $\mathbb{F}_2$. Section §5 maps wen-substrate sections
to this document's sections.

**Authoritative cross-references**: wen-substrate.md §3.6.1 (Layer A / Layer
B split), §3.6.2 (instantiation table), §3.6.3 (P1–P7 parametric), §3.6.7
(code vs theory), §3.6.8 (carrier-vs-structure note for $\mathbb{C}$),
§4.1.5b (Pauli ↔ Hilbert duality, mod-phase functor, representation functor).
Part VIII §8.3 (T2 / T3 proof obligations).

## §1 The parametric structure

The R-Family-over-$k$ tower is

$$R\text{-Family}^{(k)} \;=\; \{R_N^{(k)}\}_{N \in \mathbb{N}_0},
\qquad R_N^{(k)} \;:=\; k^N.$$

Per wen-substrate.md §3.6.1, the content splits cleanly into two layers:

**Layer A — Structure** (independent of $k$, base-parametric):

- Carriers indexed by $\mathbb{N}_0$ with cardinality $|R_N^{(k)}| = |k|^N$.
- Direct sum: $R_M^{(k)} \oplus_k R_N^{(k)} \cong R_{M+N}^{(k)}$ (P2).
- Hom-as-content: $\mathrm{Hom}_k(R_n^{(k)}, R_m^{(k)}) \cong R_{mn}^{(k)}$
  as $k$-modules (P5).
- Squaring tower with self-similarity: $R_{2N}^{(k)} = R_N^{(k)} \oplus
  R_N^{(k)}$ with $\Delta$, $\pi_i$, $f^{\oplus 2}$ (P4).
- Modality carrier $R_2^{(k)} \cong k^2$ (P6).
- Atomic-operation algebra $R_4^{(k)} \cong M_2(k)$ — the smallest
  non-commutative matrix $k$-algebra (P7b).

**Layer B — Base $k$** (base-specific):

- Cardinality of $R_N^{(k)}$: finite ($k = \mathbb{F}_p$), countable
  ($k = \overline{\mathbb{F}_p}$), continuum ($k = \mathbb{R}, \mathbb{C},
  \mathbb{Q}_p, \mathbb{C}_p$).
- Topology: discrete, profinite, Euclidean, $p$-adic.
- Characteristic: 2 / $p$ / 0.
- Algebraic closure: open / partial / closed.
- Archimedean / non-Archimedean absolute value.
- Presence of $\sqrt{-1}$, roots of unity, $\frac{1}{2}$.

**The split**: the same P1–P7 closure conditions hold across bases; what
varies is the per-base unfolding of those conditions (the most striking
case is P3, see §2 below). R-Family **as a parametric pattern** is universal;
**a specific instance** R-Family-over-$k$ is one realization.

The minimum base is $k = \mathbb{F}_2$ (the smallest non-trivial field by
Occam P1). It is currently the only fully Lean-formalized instance.

> Cross-reference: wen-substrate.md §3.6.1 (Layer A / Layer B split).

## §2 Per-base instantiation

### §2.1 $k = \mathbb{F}_2$ — minimum-base, discrete, char 2, fully formalized

**Carrier**: $R_N^{(\mathbb{F}_2)} = \mathbb{F}_2^N$, implemented as
`Fin N → Bool`. Cardinality $|R_N^{(\mathbb{F}_2)}| = 2^N$.

**Characteristic**: 2. Critical consequences: $-1 = 1$, $\tfrac{1}{2}$
does not exist (no polarization shortcut), all elements are 2-torsion
($v + v = 0$ for all $v$).

**Topology**: discrete; the inverse limit $\hat{R}^{(\mathbb{F}_2)} =
\varprojlim R_{2^j}^{(\mathbb{F}_2)}$ is the Cantor set.

**P1–P7 specialization**:

- **P1**: $\mathbb{F}_2$ is the smallest non-trivial field; the substrate
  floor. The binary distinction $\{0, 1\} = \mathbb{F}_2$.
- **P2**: $\mathbb{F}_2^M \oplus \mathbb{F}_2^N \cong \mathbb{F}_2^{M+N}$
  fully formalized.
- **P3**: **three-layer classification** $L_0$ (symmetric) + $L_1$ (alternating)
  + $L_2$ (Arf-quadratic), with Arf-invariant binary classification of $L_2$.
  This is the **char-2-distinctive** relational structure — no polarization
  collapses $L_2$ into $L_1$.
- **P4**: squaring tower $R_N^{(\mathbb{F}_2)} \to R_{2N}^{(\mathbb{F}_2)}$
  fully formalized.
- **P5**: $\mathrm{End}_{\mathbb{F}_2}(R_2^{(\mathbb{F}_2)}) = M_2(\mathbb{F}_2)$
  — 16 elements, $GL_2(\mathbb{F}_2) \cong S_3$.
- **P6**: $R_2^{(\mathbb{F}_2)} =$ Klein four-group $V_4$ under XOR.
- **P7a**: $R_3^{(\mathbb{F}_2)}$ with zong involution: 4 本 (fixed) + 4 征
  (zong-paired) = 8 trigrams.
- **P7b**: 16 atomic operations at $R_4^{(\mathbb{F}_2)} \cong M_2(\mathbb{F}_2)$.

**Lean status**: **fully formalized**. Key files in `formal/SSBX/Foundation/R/`:

- `Basic.lean` — `def R (N : ℕ) : Type := Fin N → Bool`; XOR `AddCommGroup`
  instance; cardinality, basis vectors, distinguished elements `oo / xo / ox / xx`.
- `DirectSum.lean` — direct sum $R_M \oplus R_N \cong R_{M+N}$ (P2 formalized).
- `Tensor.lean` — tensor product structure.
- `Hom.lean` — Hom-as-content $\mathrm{Hom}(R_n, R_m) \cong R_{mn}$ (P5).
- `Bilinear.lean` — three-layer bilinear / quadratic classification (P3).
- `Aut.lean` — automorphism groups at low layers.
- `Squaring.lean` — squaring tower $R_N \to R_{2N}$ (P4).
- `DirectDecomp.lean` — squaring-tower direct decomposition.
- `BeyondR8.lean` — extension above the $R_8$ canonical ceiling.
- `SubTower.lean` — sub-tower projections.
- `Phantom.lean` — phantom-index variants.
- `Judgment/` — the 印 / 投 / 执 (information / attractor / behavior)
  judgment substrate over $R_N^{(\mathbb{F}_2)}$.

This is the **minimum specific universal formal substrate** (wen-substrate
§3.6.4 Tier 1). All Phase I / Phase 0 Lean obligations (Part VIII §8.8–§8.9)
are over this base.

### §2.2 $k = \mathbb{F}_p$ for $p > 2$ — discrete, char $p$, structurally analogous

**Carrier**: $R_N^{(\mathbb{F}_p)} = \mathbb{F}_p^N$ ($p$ a prime $> 2$).
Cardinality $|R_N^{(\mathbb{F}_p)}| = p^N$.

**Characteristic**: $p$. Since $p > 2$, $\tfrac{1}{2}$ exists; polarization
applies; P3 collapses to two layers (see below).

**Topology**: discrete; $\hat{R}^{(\mathbb{F}_p)} = \varprojlim R_{p^j}^{(\mathbb{F}_p)}$
is a Cantor-type space.

**P1–P7 specialization**:

- **P1**: $\mathbb{F}_p$ admits binary distinction $\{0, 1\} \subset \mathbb{F}_p$,
  but $\mathbb{F}_2$ is uniquely minimum among fields (P1 prefers $\mathbb{F}_2$).
- **P2, P4**: identical to $\mathbb{F}_2$ — fully parametric.
- **P3**: **two-layer classification** — symmetric ($L_0$) + alternating
  ($L_1$). The polarization $q(v) := \tfrac{1}{2} B(v, v)$ recovers a
  quadratic refinement from any symmetric bilinear form, so $L_2$ collapses
  into $L_1$. Classical: inner products + symplectic forms over $\mathbb{F}_p$.
- **P5**: $M_2(\mathbb{F}_p)$ contains $GL_2(\mathbb{F}_p)$ — order
  $(p^2 - 1)(p^2 - p)$; $SL_2(\mathbb{F}_p)$ relevant to representation theory.
- **P6**: $R_2^{(\mathbb{F}_p)} = \mathbb{F}_p^2$, a discrete $p$-state plane.
- **P7a–P7b**: lift directly with appropriate cardinality (e.g., $p^4$ atomic
  operations at $R_4^{(\mathbb{F}_p)} \cong M_2(\mathbb{F}_p)$).

**Lean status**: **not yet formalized**. Structurally analogous to $\mathbb{F}_2$;
porting requires replacing `Bool` with `ZMod p` (or `Fin p` with a `Field`
instance). Mathlib provides `ZMod p` as a `Field` when `p` is prime (via
`ZMod.instField`).

**Significance**: $\mathbb{F}_p$ is the $p$-state analog of the $\mathbb{F}_2$
binary; relevant to $p$-state classical structures, $q$-deformed objects,
and the residue side of the $\mathbb{Z}_p \to \mathbb{F}_p$ reduction
functor (see §3 and §2.6).

### §2.3 $k = \mathbb{R}$ — continuous, char 0, Archimedean

**Carrier**: $R_N^{(\mathbb{R})} = \mathbb{R}^N$ — the classical real
$N$-dimensional vector space. Cardinality continuum at every $N \geq 1$.

**Characteristic**: 0. Both $-1 \neq 1$ and $\tfrac{1}{2}$ exist.

**Topology**: Euclidean; Archimedean ($|n \cdot 1|_{\mathbb{R}}
\to \infty$ as $n \to \infty$); locally compact; complete.

**P1–P7 specialization**:

- **P1**: $\mathbb{R}$ extends the binary distinction with continuous
  amplitudes, multiplicative inverses, and transcendentals.
- **P2**: $\mathbb{R}^M \oplus \mathbb{R}^N \cong \mathbb{R}^{M+N}$ — standard
  direct sum of $\mathbb{R}$-vector spaces.
- **P3**: **two-layer classification** (char $\neq$ 2): symmetric ($L_0$,
  giving inner products) + alternating ($L_1$, giving symplectic forms).
  Polarization $q(v) = \tfrac{1}{2} B(v,v)$ collapses any third layer.
  No Arf invariant. Mathlib: `BilinForm`, `QuadraticForm` over $\mathbb{R}$.
- **P4**: squaring tower $\mathbb{R}^N \to \mathbb{R}^{2N}$ identical to
  $\mathbb{F}_2$ form (fully parametric, no char dependence).
- **P5**: $M_2(\mathbb{R})$ — the $2 \times 2$ real matrix algebra; contains
  $SL_2(\mathbb{R})$ (hyperbolic / Möbius group), foundational to 2D real
  Lie theory and modular forms.
- **P6**: $R_2^{(\mathbb{R})} = \mathbb{R}^2$ — the real plane. The discrete
  $V_4$ subgroup at $\{0, 1\}^2$ persists as the algebraic core.
- **P7a–P7b**: continuous Lie-algebra atomic operations $\mathfrak{gl}_2(\mathbb{R})$
  at $R_4^{(\mathbb{R})} \cong M_2(\mathbb{R})$.

**Lean status**: **not formalized as R-Family**. Mathlib provides:

- `Real`, `Real.instField`
- `BilinForm`, `QuadraticForm` over `Real`
- `Matrix.instRing` for $M_2(\mathbb{R})$
- `Module.Free.Finite` for $\mathbb{R}^N$

What's missing: the **parametric R-Family-over-$\mathbb{R}$** statement
linking these to the universal pattern (Layer A). Mathlib treats them as
isolated linear-algebra objects, not as R-Family instances. The Lean port
of R-Family-over-$\mathbb{R}$ is a Phase II / Phase III obligation
(wen-substrate §8.9).

**Domain**: classical mechanics, real analysis, calculus, real linear
algebra, real differential geometry. wen-substrate §3.6.5 ("R-Family-over-
$\mathbb{R}$ is continuous").

### §2.4 $k = \mathbb{C}$ — continuous, char 0, algebraically closed

**Carrier**: $R_N^{(\mathbb{C})} = \mathbb{C}^N$. **At index $N = 2^n$**,
this is the $n$-qubit Hilbert space carrier $\mathcal{H}_n = \mathbb{C}^{2^n}
= R_{2^n}^{(\mathbb{C})}$ (wen-substrate §3.6.8).

**Characteristic**: 0. Algebraically closed. Contains $\sqrt{-1}$.

**Topology**: Euclidean; Archimedean; complete; algebraically closed.

**P1–P7 specialization**:

- **P1**: $\mathbb{C}$ extends $\mathbb{R}$ with $\sqrt{-1}$; phases live
  here natively.
- **P2–P4**: standard $\mathbb{C}$-vector-space operations.
- **P3**: **char-0**, so $L_2$ collapses by polarization. **The natural
  P3 over $\mathbb{C}$ is sesquilinear / Hermitian** (not bilinear) — the
  Hermitian inner product of Hilbert space. Mathlib: `InnerProductSpace`.
- **P5**: $M_2(\mathbb{C})$ contains the **Pauli matrices** $\{I, X, Y, Z\}$
  and the complexified Lorentz Lie algebra $\mathfrak{sl}_2(\mathbb{C})$ —
  foundational to relativistic spinor physics.
- **P6**: $R_2^{(\mathbb{C})} = \mathbb{C}^2$ = **spinor space**; the
  Pauli matrices act on it; Pauli mod phase recovers $V_4$ from the
  $\mathbb{F}_2$-shadow (see §3 below).
- **P7a–P7b**: continuous $\mathfrak{gl}_2(\mathbb{C})$ atomic operations
  at $R_4^{(\mathbb{C})}$.

**Carrier-vs-structure precision** (wen-substrate §3.6.8 / §4.1.5b
"carrier identity vs full Hilbert-space structure"):

The identity $\mathbb{C}^{2^n} = R_{2^n}^{(\mathbb{C})}$ holds **at the
carrier level only**. Hilbert space's distinctive content — Hermitian inner
product, unitary group $U(2^n)$, spectral theorem — is **additional
Hermitian P3-enrichment** over the R-Family-over-$\mathbb{C}$ carrier, not
present in the bare carrier. The substantive content of §3.6.8 is the
**parametric lifting** of P1–P7 from $\mathbb{F}_2$ to $\mathbb{C}$, not the
trivial $\mathbb{C}^N = \mathbb{C}^N$ identification.

Honest framing (per wen-substrate §4.1.5b):

> **Hilbert space's carrier IS R-Family-over-$\mathbb{C}$.
> Hilbert space's full structure (carrier + inner product + unitary group +
> spectral theorem) is R-Family-over-$\mathbb{C}$ + Hermitian P3-enrichment.**

**Lean status**: **not formalized as R-Family**. Mathlib provides
`Complex`, `InnerProductSpace ℂ`, `EuclideanSpace ℂ (Fin n)`, `Matrix.IsUnitary`,
`Matrix.IsHermitian`; what's missing is the R-Family-pattern lifting and
the parametric Hom-as-content / squaring-tower statements over $\mathbb{C}$.

**Domain**: standard quantum mechanics (Hilbert), complex analysis,
holomorphic functions, complex Lie groups, complex algebraic geometry.

### §2.5 $k = \mathbb{C}_p$ (Tate's $p$-adic complex) — continuous, non-Archimedean

**Carrier**: $R_N^{(\mathbb{C}_p)} = \mathbb{C}_p^N$ where $\mathbb{C}_p$
is Tate's $p$-adic complex field — the completion of an algebraic closure
of $\mathbb{Q}_p$.

**Characteristic**: 0. Algebraically closed and complete. **Residue field**
$\overline{\mathbb{F}_p}$.

**Topology**: $p$-adic — **totally disconnected**, **non-Archimedean**,
locally compact ($\mathbb{Q}_p$-locally compact; $\mathbb{C}_p$ totally
disconnected complete extension).

**P1–P7 specialization**:

- **P1**: $\mathbb{C}_p$ extends the binary distinction with $p$-adic
  amplitudes and non-Archimedean absolute value $|\cdot|_p$.
- **P3**: **char-0 over $\mathbb{C}_p$** — two-layer relational classification
  (symmetric + alternating); but **non-Archimedean** specific phenomena
  appear (e.g., $|x + y|_p \leq \max(|x|_p, |y|_p)$).
- **P5**: $M_2(\mathbb{C}_p)$ — the $p$-adic spinor algebra; Pauli-analog
  operators exist since $\mathbb{C}_p$ contains all roots of unity.
- **P6**: $R_2^{(\mathbb{C}_p)} = \mathbb{C}_p^2$ — the $p$-adic spinor space.
- **P7b**: $p$-adic continuous atomic operations $\mathfrak{gl}_2(\mathbb{C}_p)$.

**Lean status**: **partial in Mathlib** ($\mathbb{C}_p$ is under construction
in Mathlib). Not yet formalized as R-Family-over-$\mathbb{C}_p$. Mathlib provides:

- `PadicInt` ($\mathbb{Z}_p$), `Padic` ($\mathbb{Q}_p$) — fully present.
- $\mathbb{C}_p$ — partial (algebraic-closure-then-completion in progress).

**Domain**: $p$-adic quantum mechanics (Vladimirov-Volovich, Khrennikov);
$p$-adic analysis; non-Archimedean physics; rigid analytic geometry
(connecting to Huber's adic spaces, wen-substrate §3.6.6).

**Significance**: R-Family-native for $p$-adic QM. wen-substrate §3.6.2
lists $\mathbb{C}_p$ as one of the four most foundationally significant
R-Family instances (alongside $\mathbb{F}_2, \mathbb{R}, \mathbb{C}$).

> Reference: Vladimirov–Volovich, "p-adic quantum mechanics", Comm. Math.
> Phys. 123 (1989); Khrennikov, "Non-Archimedean Analysis" (Kluwer, 1994).

### §2.6 $k = \mathbb{Z}_p$ — profinite, char 0 with residue $\mathbb{F}_p$

**Carrier**: $R_N^{(\mathbb{Z}_p)} = \mathbb{Z}_p^N$. $\mathbb{Z}_p$ is
the $p$-adic integers — the inverse limit $\varprojlim \mathbb{Z}/p^n$.

**Characteristic**: 0. Local ring (not a field; the maximal ideal is
$p\mathbb{Z}_p$). Residue field $\mathbb{Z}_p / p\mathbb{Z}_p \cong
\mathbb{F}_p$.

**Topology**: **profinite** — compact, totally disconnected, equivalent
to a Cantor set. Non-Archimedean.

**P1–P7 specialization**:

- **P2, P4**: lift naturally — $\mathbb{Z}_p$-modules form a clean algebraic
  category.
- **P3**: char 0 over a local ring — bilinear / quadratic forms over
  $\mathbb{Z}_p$ are well-studied (Hilbert symbol, Hasse invariants).
- **P5**: $M_2(\mathbb{Z}_p)$ — the $p$-adic-integer-coefficient matrix ring;
  $GL_2(\mathbb{Z}_p)$ is the standard compact open subgroup of $GL_2(\mathbb{Q}_p)$.

**The bridge role**: $\mathbb{Z}_p$ is the discrete-continuous bridge
(wen-substrate §3.6.2 table). Two reduction maps frame the bridge:

- **Reduction mod $p$**: $\mathbb{Z}_p \twoheadrightarrow \mathbb{F}_p$
  (residue map); kills the higher $p$-adic content, yielding the discrete
  $\mathbb{F}_p$ instance.
- **Generic fiber**: $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p$
  (localization at $p$); yields the continuous $p$-adic instance.

In Huber's adic-space language (wen-substrate §3.6.6): the **special
fiber** of an $\mathbb{Z}_p$-adic object is its $\mathbb{F}_p$ reduction
(discrete); the **generic fiber** is its $\mathbb{Q}_p$ extension
(continuous). R-Family-over-$\mathbb{Z}_p$ encodes both fibers in a single
parametric instance.

**Lean status**: **partial** — Mathlib provides `PadicInt p` as a complete
discrete-valuation ring; what's missing is the R-Family-pattern lifting.

**Domain**: $p$-adic arithmetic, Iwasawa theory, $p$-adic Hodge theory,
formal group laws, profinite limit constructions.

### §2.7 Non-algebraic δ-realisations (v1.4 siblings)

The above six instances are all **algebraic-class** δ-realisations: δ = k carries ring or field structure. Under `wen-substrate.md` v1.4 §3.7.8 (distinction monism), the broader δ-realisation framework admits non-algebraic siblings — first-class on the same substrate, requiring different per-realisation relational structure in place of P3's bilinear / sesquilinear forms.

| δ-realisation | δ type | algebraic? | additional structure | R-Family-over-δ instance |
|---|---|---|---|---|
| classical / Boolean (= F₂) | `Bool` | yes (field) | XOR, AND, ¬ | full P1–P7 in `Foundation/R/Basic.lean` (canonical δ = Bool default) |
| real / continuous | ℝ | yes (field) | order, completeness | algebraic-class, §2.3 of this doc |
| complex / Hilbert | ℂ | yes (field) | Hermitian inner product (P3-enrichment) | algebraic-class, §2.4; Hermitian via separate enrichment |
| p-adic | ℂ_p | yes (field) | non-Archimedean absolute value | algebraic-class, §2.5 |
| **quantum basis labels** | `{|0⟩, |1⟩}` | **no** | ℂ-amplitude algebra attached separately (substrate ≠ amplitude) | per-realisation bridge open; substrate carrier in `Foundation/R/Distinction.lean` |
| **propositional / logical** | `Prop` | **no** | proof-relevance (Curry-Howard) | per-realisation bridge open |
| **semantic / linguistic** | per-language `L` vocabulary | **no** | per-language syntax / semantics; `Sayable_L` / `Silent_L` predicates | per-realisation bridge open |
| **yi-jing traditional** | 阳 / 阴 | **no** | classical-Chinese tradition overlay | per-realisation bridge open; Atlas namespace |

**P3 cross-realisation note**. The bilinear / quadratic classification of §1.2 / §2's per-base entries is the **algebraic-class** form of substrate-level relational structure. For non-algebraic δ:

- Quantum δ: relational structure is **Hermitian sesquilinear** on ℂ-amplitude, not F₂-bilinear on the δ carrier. The substrate carries qubit basis labels; the amplitude algebra is separate.
- Propositional δ: relational structure is **proof-relevant** (intuitionistic / Heyting), with Curry-Howard correspondence between proofs and constructions.
- Semantic δ: relational structure is per-language **syntactic / pragmatic** (subject-of, object-of, modification, …), with each language providing its own `Sayable_L` predicate.
- Traditional 阳/阴: relational structure follows the classical-Chinese 易经 tradition's atom interactions; this is Atlas-level overlay, not substrate-level relational structure.

For all non-algebraic δ, the underlying carrier `R' N δ := Fin N → δ` is well-defined (substrate-level); the closure conditions P1, P2, P4 (binary distinction, direct sum, squaring tower) hold uniformly; P3, P5, P6, P7b require additional per-realisation structure layered over and above the carrier. The companion file [`Foundation/R/Distinction.lean`](../../formal/SSBX/Foundation/R/Distinction.lean) makes the substrate-level layer available; the per-realisation bridge files remain open work.

**Connection to modern algebraic frameworks** (condensed math / adic spaces / topos / stable ∞-categories): these tools apply at the **algebraic-class** layer. Non-algebraic δ-realisations may require different ambient frameworks (operator algebras for quantum; structured-language categories for semantic; type-theoretic categories with proof-relevance for propositional). This is documentary, not yet a formal claim.

## §3 Transfer functors between instances

R-Family instances at different bases are linked by **functorial maps**
that preserve the R-Family structure. Per wen-substrate §3.6.8 and §4.1.5b,
the following are the canonical transfer functors. All are
**conjectural at the formal level** — they sit as part of T2 / T3 in Part
VIII §8.3 (universality and naturality obligations), awaiting full
formalization.

### §3.1 Mod-phase functor — R-Family-over-$\mathbb{C}$ → R-Family-over-$\mathbb{F}_2$

The Pauli group $\mathcal{P}_n \subset U(\mathbb{C}^{2^n})$ has $4 \cdot 4^n$
elements. Modding by the phase subgroup $\langle iI \rangle$:

$$\mathcal{P}_n / \langle iI \rangle \;\cong\; R_{2n}^{(\mathbb{F}_2)}
\qquad \text{(as $\mathbb{F}_2$-symplectic module)}.$$

This **mod-phase forgetful functor** keeps the discrete X-content and
Z-content (binary $\mathbb{F}_2$ data) and discards the continuous phase
(killed by $-1 = 1$ in $\mathbb{F}_2$).

**Status**: stated in wen-substrate §4.1.5b; not yet formalized in Lean
as a transfer functor between R-Family instances. Phase III obligation.

### §3.2 Representation functor — R-Family-over-$\mathbb{F}_2$ → R-Family-over-$\mathbb{C}$

The standard Pauli embedding lifts each labeled R-Family-over-$\mathbb{F}_2$
element to an operator on $\mathcal{H}_n = R_{2^n}^{(\mathbb{C})}$:

$$R_{2n}^{(\mathbb{F}_2)} \hookrightarrow
  \mathcal{P}_n / \langle iI \rangle \hookrightarrow \mathrm{End}(\mathcal{H}_n)
  = M_{2^n}(\mathbb{C}) \subset R_{(2^n)^2}^{(\mathbb{C})}.$$

This is the **canonical R-Family functor** R-Family-over-$\mathbb{F}_2$ →
R-Family-over-$\mathbb{C}$ via Pauli embedding (wen-substrate §4.1.5b
"final reframing").

**Status**: stated; not formalized as a transfer functor. Phase III.

### §3.3 Reduction mod $p$ — R-Family-over-$\mathbb{Z}_p$ → R-Family-over-$\mathbb{F}_p$

The residue map $\mathbb{Z}_p \twoheadrightarrow \mathbb{F}_p$ extends
coordinate-wise:

$$R_N^{(\mathbb{Z}_p)} \;\twoheadrightarrow\; R_N^{(\mathbb{F}_p)}.$$

This is the **special-fiber functor** in Huber's adic-spaces language
(wen-substrate §3.6.6). It is base-change along the ring map
$\mathbb{Z}_p \to \mathbb{F}_p$.

**Status**: a straightforward base-change in the category of R-Family
instances; not formalized in Lean.

### §3.4 Lift — R-Family-over-$\mathbb{F}_p$ ↪ R-Family-over-$\mathbb{Z}_p$

Where applicable, lifting modulo $p$ in $\mathbb{F}_p$ to $p$-adic integers
$\mathbb{Z}_p$ extends coordinate-wise:

$$R_N^{(\mathbb{F}_p)} \;\hookrightarrow\; R_N^{(\mathbb{Z}_p)}.$$

This is **set-theoretic** (any lift of representatives) and **not
canonical** as a ring map — it factors through Teichmüller representatives
in the $p$-adic case. Properly framed, this is a **section** of the
reduction-mod-$p$ map (a torsor, in the etale-cohomology sense).

**Status**: conceptually clean (Witt-vectors, Teichmüller lifts); not
formalized as an R-Family transfer.

### §3.5 Generic-fiber functor — R-Family-over-$\mathbb{Z}_p$ → R-Family-over-$\mathbb{Q}_p$

Localization at $p$: $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p$ extends
coordinate-wise:

$$R_N^{(\mathbb{Z}_p)} \;\hookrightarrow\; R_N^{(\mathbb{Q}_p)}.$$

This is the **generic-fiber functor** in adic-space language (wen-substrate
§3.6.6). Composed with the further extension $\mathbb{Q}_p \hookrightarrow
\mathbb{C}_p$, this routes into the continuous $p$-adic R-Family.

### §3.6 The full functor lattice

Combining the above:

```
        R-Family-over-Z_p ────reduction mod p───→ R-Family-over-F_p
              │                                            │
   generic fiber                                  representation
   (extension to Q_p / C_p)                       (Pauli embedding)
              │                                            ↓
              ↓                                  R-Family-over-C
        R-Family-over-C_p                                  ↑
        (p-adic continuous)                       mod-phase functor
                                                            │
                                                            │
                                                    R-Family-over-F_2 ──Pauli embedding (§3.2)─→
```

All these functors are **conjectural at the formal level**: they are stated
naturally and follow standard mathematical practice (base change, residue,
lift, Pauli embedding), but have not been Lean-verified as **R-Family
transfer functors** preserving the parametric P1–P7 closure conditions.

The full functorial picture is a **T2 / T3 obligation** (wen-substrate
Part VIII §8.3): the categorical equivalence between R-Family-over-$k$
instances under base change, completing the parametric framework. Phase
III (1+ years, wen-substrate §8.9).

## §4 Code-vs-theory status

> Cross-reference: wen-substrate.md §3.6.7 "Code vs theory".

**Current Lean implementation** (this codebase, `formal/SSBX/Foundation/R/`):

```lean
def R (N : ℕ) : Type := Fin N → Bool   -- = F_2^N
```

i.e., the **$\mathbb{F}_2$-specific** carrier. This is the parameterless
specialization — the minimum-base instance per wen-substrate §3.6.4 Tier 1.

**Target parametric form**:

```lean
def RFamily (k : Type _) (N : ℕ) : Type _ := Fin N → k

def R (N : ℕ) : Type := RFamily Bool N    -- F_2-instance
-- def RR  (N : ℕ) := RFamily ℝ N         -- ℝ-instance (future)
-- def RC  (N : ℕ) := RFamily ℂ N         -- Hilbert-instance (future)
-- def RCp (p N : ℕ) := RFamily (ℂ_[p]) N -- p-adic-instance (future)
```

**Current stub**: `formal/SSBX/Foundation/R/Parametric.lean` introduces
`RFamily k N := Fin N → k` and shows `RFamily Bool N = R N` holds by `rfl`.
This is a **minimum scaffolding step**: a parametric type, plus the
$\mathbb{F}_2$-specialization identity, plus a `Fintype` instance when $k$
is finite. No proofs of P1–P7 over arbitrary $k$ are attempted at this stage.

**Why the code is currently $\mathbb{F}_2$-specific** (wen-substrate §3.6.7):

1. **Computability**: Lean's `decide` / `native_decide` tactics require
   finite computable types. $\mathbb{F}_2$ is fully computable; $\mathbb{R}$
   and $\mathbb{C}$ are not (they use classical Mathlib reals).
2. **Verification scope**: Phase I of the proof programme (wen-substrate
   §8.9) is the finite/computable case — Lean is the right tool. Continuous
   instances admit only partial Lean verification (via classical Mathlib
   foundations).
3. **Mathlib coverage**: $\mathbb{Z}_p, \mathbb{Q}_p$ are in Mathlib;
   $\mathbb{C}_p$ is partial; full $p$-adic R-Family Lean port is future work.

**Mathlib dependencies needed for non-$\mathbb{F}_2$ instances**:

| Base $k$ | Mathlib path | Notes |
|---|---|---|
| $\mathbb{F}_p$ | `ZMod p` with `[Fact (Nat.Prime p)]` | Field instance: `ZMod.instField` |
| $\mathbb{R}$ | `Real` | Classical, non-computable |
| $\mathbb{C}$ | `Complex` | Classical; `InnerProductSpace ℂ` for Hilbert |
| $\mathbb{Z}_p$ | `PadicInt p` | Full Mathlib coverage |
| $\mathbb{Q}_p$ | `Padic p` | Full Mathlib coverage |
| $\mathbb{C}_p$ | partial — under construction in Mathlib | Future |

**Estimated migration scope**:

- Most existing $\mathbb{F}_2$-specific proofs in `Foundation/R/Basic.lean`
  use `decide` / `native_decide` / `fin_cases`; these tactics **do not lift**
  to arbitrary $k$ (no decidability for $\mathbb{R}$). Parametric
  reformulations would need `simp` / `ring` / `linear_combination` over
  general fields, plus separate per-instance specializations where
  computability matters.
- The squaring-tower, direct-sum, and Hom-as-content statements (P2, P4, P5)
  generalize directly to arbitrary $k$-modules but require restating with
  `Module k` typeclass.
- The bilinear / quadratic theory (P3) **diverges by characteristic**;
  the char-2 three-layer classification (Arf) and the char-$\neq$-2
  two-layer classification (polarization) are separate theorems, both
  parametric in their respective scopes.
- The atomic-operations theory (P7b) at $R_4 \cong M_2(k)$ generalizes
  with `Matrix (Fin 2) (Fin 2) k`.

**Recommendation**: defer parametric proof porting until T2 / T3 proof
obligations explicitly demand it. The minimum stub (this PR) suffices to
**establish the parametric type structurally**; per-instance lifting is
incremental.

## §5 Reading guide

Mapping between wen-substrate.md §3.6 and this document:

| wen-substrate.md §3.6 | This document |
|---|---|
| §3.6.1 (Layer A / Layer B split) | §1 (The parametric structure) |
| §3.6.2 (Instantiation table) | §2 (Per-base instantiation) — six bases unpacked |
| §3.6.3 (P1–P7 parametric) | §2 per-subsection P1–P7 specialization rows |
| §3.6.4 (Two-tier minimality claim) | §2.1 preamble |
| §3.6.5 (Discrete/continuous as base properties) | §2 implicit; per-base topology rows |
| §3.6.6 (Condensed math / adic spaces / topos / spectra) | §3.3–§3.5 (adic-space fiber functors) |
| §3.6.7 (Code vs theory) | §4 (Code-vs-theory status) |
| §3.6.8 (ℂ-Hilbert = R-Family-over-ℂ carrier identity) | §2.4 (carrier-vs-structure precision) |
| §3.6.9 (Corrected universality statement) | implicit throughout |
| §3.6.10 (Encoding vs native articulation) | §3 functorial framing |
| §4.1.5b (Pauli ↔ Hilbert duality) | §3.1 (mod-phase) + §3.2 (representation) |
| Part VIII §8.3 (T2, T3) | §3 status; §4 conclusion |
| Part VIII §8.9 (Three-phase programme) | §4 recommendation |

**Bottom line** (per wen-substrate §3.6.9):

> R-Family is universal as a parametric structural pattern. R-Family-over-$\mathbb{F}_2$
> is the minimum specific instance (Lean-formalized). Other bases ($\mathbb{R},
> \mathbb{C}, \mathbb{C}_p, \mathbb{Z}_p, \ldots$) provide continuous,
> $p$-adic, profinite instances. All share the same P1–P7 closure conditions;
> all articulate formal structure; all are R-Family.

**One pattern, many instances. Discrete and continuous are not different
substrates — they are different bases.**
