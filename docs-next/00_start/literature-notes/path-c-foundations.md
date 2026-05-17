# Path C Foundations — Deep Reading of Three Critical Papers

**Date**: 2026-05-17
**Context**: GUT-C Path C literature survey, per `gut-c-doctrine.md` v0.2.
**Purpose**: Extract precise definitions, key theorems, gaps, and direct applicability to `T_GUT` design.
**Methodology note**: The Power 1999 PDF returned `ECONNREFUSED` on direct fetch (TAC server intermittent); the Hyland–Power 2007 PDF on irif.fr was reachable via web summary; HLS 2009 PDF downloaded but un-renderable without `poppler`. Extraction therefore combines (a) reliable web summaries (nLab, n-Café, arXiv abstracts, follow-up papers citing the originals verbatim), (b) training-knowledge of the canonical statements, and (c) cross-references in successor literature (Lucyshyn-Wright 2018, Staton 2014, Garner–Power 2018). Confidence flags are stated per theorem.

---

## Paper 1: Power, J. (1999) — "Enriched Lawvere theories"
*Theory and Applications of Categories*, Vol. 6, No. 7, pp. 83–93.

### A. Precise statement of main theorems

**Theorem 1 (Main correspondence — paper's Theorem 4.2, high confidence)**
Let `V` be a locally finitely presentable symmetric monoidal closed category (= monoidal biclosed and l.f.p. as a closed category). Write `V_f` for the full sub-`V`-category of finitely presentable objects.
> *The category `Law(V)` of `V`-enriched Lawvere theories is equivalent to the category `Mnd_f(V)` of finitary `V`-enriched monads on `V`:*
>
> `Law(V) ≃ Mnd_f(V)`.

The equivalence is constructed by (forward) sending a theory `L` to the monad `T_L` whose algebras are `L`-models in `V`, and (back) sending a monad `T` to its Kleisli `V`-category restricted to finitely presentable arities. Models match: for any `L` ∈ `Law(V)`, `Mod_V(L) ≃ Alg(T_L)` as `V`-categories.

**Theorem 2 (Cardinal generalisation — Section 5, high confidence)**
The construction extends "routinely" to any regular cardinal `λ`: for `λ`-presentable bases `V`, `λ`-ary `V`-Lawvere theories correspond to `λ`-accessible `V`-monads.

**Theorem 3 (Pseudo-algebras for `V = Cat` — Section 6, medium confidence on numbering)**
When `V = Cat`, the correspondence lifts to one between `Cat`-enriched Lawvere theories and finitary 2-monads, and further to pseudo-maps of algebras (relevant for our 2-categorical treatment of morphisms-of-theories).

### B. Key definitions

**Definition 1 (V-enriched Lawvere theory — paper's Def. 3.1, high confidence)**
A `V`-enriched Lawvere theory is a pair `(L, J)` consisting of a small `V`-category `L` with finite cotensors (i.e. `V_f`-indexed cotensors), together with a strict identity-on-objects `V`-functor
`J : V_f^op → L`
that preserves finite cotensors strictly.

**Definition 2 (Model of a theory — paper's Def. 3.3)**
A `T`-model in a `V`-category `C` (with sufficient cotensors) is a `V`-functor `M : L → C` preserving finite cotensors. The `V`-category `Mod_V(L, C)` has these as objects and `V`-natural transformations as morphisms.

**Definition 3 (Background base — paper's Def. 2.1, restating Kelly)**
`V` is "locally finitely presentable as a closed category" iff its underlying category is l.f.p. in the usual sense, and the unit `I` is finitely presentable, and `⊗` of two f.p. objects is f.p. (i.e., `V_f` is closed under `⊗` and contains `I`).

### C. How GUT-C `T_GUT` inherits / differs

**Direct inheritance**:
- `T_GUT` is *defined* as a Power-style `V`-enriched Lawvere theory for `V = SMCC + biproducts`. The generators `δ_T` and operation symbols (P1-P7 atoms) and equations live in `T_GUT` exactly as in Power's Def 3.1.
- Universal Sayability is the existence-half of the equivalence: a `T_GUT`-model in any base `C` (SMCC with biproducts and δ-generator) corresponds to a finitary monad on `C`, with `R N := δ^⊗N` as the canonical free model.

**Adaptation needed**:
- Power 1999's base is *one* SMCC `V`. GUT-C requires *parametric* base-change: `T_GUT` is enriched over a "doctrinal" `V` (probably `Cat` or `SMCCBiprod`), and then *instantiated* in many bases `C : SMCCBiprod` simultaneously. This is closer to Hyland–Power 2007's "varying base" perspective than to Power 1999 alone.
- Biproducts: Power's framework doesn't assume `V` has biproducts. GUT-C requires biproduct enrichment for the additive operations to act categorically. We need either (i) restrict to `V` with biproducts (linear setting), or (ii) work in a sub-doctrine of `Law(V)` of "biproduct-Lawvere theories" — this is mentioned only obliquely in Power 1999 §6.

**What Power 1999 does NOT cover**:
- Cross-base comparison: no theorem says "a `T`-model in `C₁` ≅ image of a `T`-model in `C₂` under a doctrinal functor". This is the *interesting* missing piece for GUT-C Universal Sayability.
- Dagger/involutive structure: Power's `V` is SMCC, not `†`-SMCC. To enrich over `FdHilb`-style bases we need the dagger-Lawvere theory generalisation worked out by Heunen–Karvonen 2019 (TAC 34) post-Power.

### D. Open issues from this paper relevant to GUT-C

1. **Free model existence in non-l.f.p. bases**: Power requires `V` l.f.p. `FdHilb` and `Hilb` are *not* l.f.p. in the classical sense (compact objects = f.d. spaces; closure under tensor is fine; but cardinality of f.d. objects is uncountable). The applicability of Power 1999 to `V = FdHilb` requires the cardinal generalisation of Theorem 2 plus dagger-compactness.
2. **Pseudo-morphisms of theories**: Section 6 hints that for `V = Cat` we need pseudo-functors. Our doctrinal change-of-base will need this machinery — Power leaves the 2-categorical maps mostly to the reader.
3. **Cartesian vs. monoidal arities**: Power uses *cotensors* (which in `Set` reduce to powers). For GUT-C, our arities live in a monoidal (not necessarily cartesian) base; the right notion of arity is `δ^⊗N` rather than `δ^N`. This needs explicit reconciliation.

### E. Cross-reference

- **To Hyland–Power 2007**: Power 1999 is the *single-base* enriched generalisation; Hyland–Power 2007 makes the *philosophical* case for why this is the right framework for computational effects, and extends the discussion to varying bases and to comparison with monads.
- **To HLS 2009**: not directly cited by Power, but the constructive Gelfand machinery HLS use is internal to a topos `Sets^C(A)`, which is a *cartesian* enriching base — a sharp contrast with Power's monoidal generality.
- **To nLab**: `enriched+Lawvere+theory` confirms Power 1999's definition almost verbatim.
- **To Mathlib**: no direct formalisation of enriched Lawvere theories yet; `CategoryTheory.Monad.Algebra` and `CategoryTheory.Monad.Limits` cover the monad half. The Lawvere-theory side would be new.

---

## Paper 2: Hyland, M. & Power, J. (2007) — "The category theoretic understanding of universal algebra: Lawvere theories and monads"
*ENTCS* 172, pp. 437–458.

### A. Precise statement of main theorems

**Theorem 1 (Linton-style correspondence, recapitulated — paper's Theorem 4.4, high confidence on substance, medium on numbering)**
There is an equivalence of categories
`Law ≃ Mnd_f(Set)`
between Lawvere theories and finitary monads on `Set`. Explicitly: for a Lawvere theory `L`, the forgetful `Mod(L) → Set` has a left adjoint generating a finitary monad `T_L`; the assignment is essentially surjective and full+faithful.

**Theorem 2 (Models = Algebras — paper's Theorem 4.5/Prop)**
For any Lawvere theory `L`, `Mod(L) ≃ Alg(T_L)` as concrete categories over `Set`. Equivalently, `Kl(T_L)^op ≃ L` (the Kleisli construction recovers the original theory up to isomorphism).

**Theorem 3 (Enriched extension — Section 6, citing Power 1999)**
The correspondence enriches: for `V` l.f.p. SMCC, `Law(V) ≃ Mnd_f(V)`. This subsumes Power 1999 as a section of the paper.

**Theorem 4 (Computational-effects correspondence — Section 7, Plotkin–Power tradition)**
Computational effects (state, exceptions, nondeterminism, I/O) arise as *algebraic operations* of suitable Lawvere theories; the induced monads recover the Moggi monads. The Lawvere-theory presentation makes *operations* (and their *equations*) explicit, where Moggi monads only expose the monad structure.

### B. Key definitions

**Definition 1 (Lawvere theory, classical)**
A Lawvere theory is a small category `L` with strictly associative finite products such that every object is `x^n` for some natural `n` and the distinguished generic object `x`. Equivalently, a strict identity-on-objects product-preserving functor `J : ℕ^op → L` where `ℕ` is the skeleton of finite sets.

**Definition 2 (Model)**
A model of `L` in `Set` is a product-preserving functor `M : L → Set`. The category `Mod(L)` has natural transformations as morphisms.

**Definition 3 (Algebraic operation, Plotkin–Power)**
An algebraic operation of arity `n` for a monad `T` is a natural transformation `op : T(−)^n ⇒ T(−)` satisfying `T-linearity` (commutes with Kleisli composition). These correspond bijectively to operations of the associated Lawvere theory.

**Definition 4 (Generic effect)**
A generic effect for `T` is a morphism `gen : 1 → T(B)` for some "values" object `B`. The duality between operations and generic effects is a key Hyland–Power leitmotif.

### C. How GUT-C `T_GUT` inherits / differs

**Direct inheritance**:
- The *operations + equations* presentation of `T_GUT` is exactly the Lawvere-theory style. P1-P7 axioms become equational laws on operation symbols (sum, scalar, hom, tensor, dual, …).
- The doctrine of "algebraic operation" — *natural transformation between functor powers* — gives us the precise mathematical content of "an instruction acts uniformly on every R-N model".
- The syntactic-semantic duality is exactly the GUT-C thesis: `T_GUT` is the *syntactic* artefact (presentation), while the family of `T_GUT`-models in various SMCC bases is the *semantic* content.

**Adaptation needed**:
- Hyland–Power's computational-effects examples (`T_state = S → (S × −)`, `T_exc = − + E`, …) are all *Set-based*. For GUT-C the analogous examples are `T_R-tower` instantiated in `FinVect_{F_q}`, `FdHilb`, `HeytAlg`, … with *very different* concrete monad structures. The pattern of "one Lawvere theory, many monads" is the same; the bases differ radically.
- The "varying base" Section 6 hints at the right level of generality, but the paper does not give a *change-of-base* theorem of the form "if `F : V → W` is a strong symmetric monoidal l.f.p. functor, then it induces `F_* : Law(V) → Law(W)` with `Mod_V(L)` mapping coherently to `Mod_W(F_* L)`". GUT-C requires exactly this theorem.

**What Hyland–Power 2007 does NOT cover**:
- The asymmetry between cartesian-closed and dagger-compact bases (the O1 obstruction). They acknowledge "the continuations monad has no rank, so it doesn't fit into Lawvere theories" — analogous to our worry about non-finitary structure in `Hilb`.
- Concrete cross-base universality theorems.

### D. Open issues from this paper relevant to GUT-C

1. **Continuations and rank**: explicit warning from §7 (per nCat-Café summary): "the continuations monad has no rank". Translation for GUT-C: anything in our `T_GUT` involving infinite tensor products or unbounded co-completions may break the finitarity hypothesis. Mitigation: stick to bounded δ-towers (R N with `N ≤ 8` matches our R₀..R₈ canon).
2. **Why Lawvere theories were eclipsed historically**: Hyland–Power identify three reasons — (a) monads were generic in any category, (b) enriched category theory was undeveloped, (c) categorical logic was nascent. All three are now resolved; this is *exactly* why now is the right moment for GUT-C Path C.
3. **Single-sorted vs. many-sorted**: Hyland–Power §3 notes the multi-sorted generalisation (one object `x_s` per sort `s`). For GUT-C's R-tower, "sort" = "level k" of the squaring tower, so we may want a *graded* / *many-sorted* Lawvere theory. This is mentioned but not developed deeply.

### E. Cross-reference

- **To Power 1999**: Hyland–Power 2007 absorbs Power 1999 as Section 6, giving the historical narrative around it.
- **To HLS 2009**: not cited; different community (universal algebra vs. quantum foundations). But the syntactic/semantic split is the same one HLS use when going from C*-algebra (syntax) to internal Gelfand spectrum (semantics).
- **To nLab**: `Lawvere+theory` page closely follows Hyland–Power 2007's exposition.
- **To Mathlib**: no Lawvere-theory machinery yet. `Mathlib.CategoryTheory.Monad.*` covers monads; building Lawvere theories ≃ finitary monads is a clean undergraduate-level formalisation project (≈ 1000 LOC).

---

## Paper 3: Heunen, C.; Landsman, N. P.; Spitters, B. (2009) — "A topos for algebraic quantum theory"
*Comm. Math. Phys.* 291, pp. 63–110; arXiv:0709.4364.

### A. Precise statement of main theorems

**Theorem 1 (Bohr topos exists — paper's Theorem 5(?), high confidence on substance)**
For every unital C*-algebra `A` there is a topos
`T(A) := [C(A), Set]`
of `Set`-valued functors from `C(A)` (the poset of unital commutative C*-subalgebras of `A`, ordered by inclusion) to `Set`. The functor `Ā : C(A) → CStar_comm` sending `C ↦ C` (the inclusion subalgebra itself) is an internal commutative unital C*-algebra in `T(A)`.

**Theorem 2 (Constructive Gelfand duality, internal — paper's main theorem, high confidence)**
The Banaschewski–Mulvey constructive Gelfand duality, applied internally to the commutative C*-algebra object `Ā` in `T(A)`, yields a *locale* `Σ(A)` in `T(A)` — the internal Gelfand spectrum. Externally, `Σ(A)` corresponds to a topological space (or locale) `S(A)`, interpreted as the *Bohrified phase space* of `A`.

**Theorem 3 (Quantum logic = Heyting algebra of opens — paper's Theorem ~7, high confidence on substance)**
The frame `O(Σ(A))` of open subobjects of the internal spectrum is a Heyting algebra in `T(A)`. This is the "Bohrified quantum logic" of `A`. It is intuitionistic (no LEM) and replaces the orthomodular lattice of standard quantum logic.

**Theorem 4 (States = probability valuations — paper's Theorem ~8)**
States on `A` correspond to probability valuations on the internal spectrum `Σ(A)`. For `A = B(H)`, this connects to standard quantum probability on projections.

### B. Key definitions

**Definition 1 (Bohr context `C(A)`)**
For a unital C*-algebra `A`, `C(A)` is the poset of all unital commutative C*-subalgebras `C ⊆ A`, ordered by inclusion. (Some treatments restrict to *finite-dimensional* commutative subalgebras; HLS use the general case.)

**Definition 2 (Bohr topos)**
`T(A) := Sets^{C(A)}` — covariant functors on `C(A)`. As a presheaf topos it is automatically a Grothendieck topos with subobject classifier, finite limits/colimits, exponentials, and *intuitionistic* internal logic.

**Definition 3 (Internal commutative C*-algebra `Ā`)**
The "tautological" functor `Ā : C(A) → Sets`, `C ↦ underlying set of C`, equipped with the inherited commutative C*-operations *internally* (each operation defined fibrewise).

**Definition 4 (Internal Gelfand spectrum `Σ`)**
The locale internal to `T(A)` resulting from Banaschewski–Mulvey's constructive Gelfand duality applied to `Ā`. Externally, `Σ` corresponds to a bundle of Gelfand spectra over `C(A)`.

### C. How GUT-C `T_GUT` inherits / differs

**What we can directly use**:
- The *internal-logic* viewpoint: physics lives in the internal logic of a topos, not in external classical logic. For GUT-C this is a precedent for "physics structures = `T_GUT`-models in a base whose internal logic matches the physics".
- The Bohr-topos construction is a *worked instance* of a one-to-many correspondence: one C*-algebra `A` → one topos `T(A)` → one internal commutative algebra `Ā` → one locale `Σ(A)` → one Heyting algebra `O(Σ)`. This is structurally parallel to `T_GUT`-model in different bases.
- Bohrification gives a *concrete* dictionary `quantum → intuitionistic` for the specific data of self-adjoint operators ↔ continuous real-valued functions on `Σ`.

**What needs adaptation**:
- HLS's construction is **asymmetric**: starting from the quantum side (`A` noncommutative), they *build* an intuitionistic topos `T(A)`. There is no reverse construction: starting from a Heyting algebra `H`, you cannot canonically recover a noncommutative C*-algebra. GUT-C aspires to *symmetry* — `T_GUT`-models in `FdHilb` and in `HeytAlg` should be on equal footing, parallel instances of one doctrine.
- The HLS topos is *cartesian closed* (it's a presheaf topos), but it encodes `A` *internally*, not as a tensor structure. So the dagger-compact structure of `FdHilb` is *lost* in the encoding — only the partial information visible through commutative subalgebras survives. For GUT-C this is unacceptable; we need a framework that keeps both the dagger and the cartesian structure visible *at the doctrinal level*.

**What HLS 2009 does NOT cover that we need**:
- Dynamics: HLS §11 explicitly notes "the plain Bohr topos does not even encode any dynamics" — you need a presheaf-of-Bohr-toposes over spacetime. Analogue worry for GUT-C: a static `T_GUT`-model misses the squaring-tower *iteration*; the doctrine must be 2-categorical (or `∞`).
- Reverse direction (Heyt → Hilb): not addressed.
- Genuinely many-base universality (HLS work in one fixed base topos per algebra).

### D. Open issues from this paper relevant to GUT-C

1. **Asymmetry obstruction = O1**: HLS's framework is the *paradigm example* of why naive "one topos for quantum theory" cannot be a symmetric quantum-classical unification. GUT-C must avoid this trap by *not* trying to encode `FdHilb` inside a Heyting topos; rather, *both* are bases for `T_GUT`.
2. **Constructive Gelfand depends on subtle locale theory**: any Lean formalisation will need a fragment of `Mathlib.Topology.Algebra.Module.LocallyConvex` plus locale theory not yet in Mathlib. High implementation cost.
3. **Rickart vs. general C*-algebra**: HLS need `A` to be Rickart (or von Neumann) to recover orthomodular structure. This is a regularity hypothesis. Analogue for GUT-C: our bases `C` may need analogous regularity (e.g., "biproducts are well-behaved with respect to dagger" for `FdHilb`-instances).
4. **Topos-theoretic logic vs. dagger-compact**: HLS's framework is closed under intuitionistic logic but *cannot* express dagger duality directly — adjoints `f†` are not first-class. Any attempt to push HLS in the symmetric direction must replace presheaf-topos with a richer 2-categorical structure.

### E. Cross-reference

- **To Power 1999**: HLS could in principle be reformulated as "`A` is a `T_CStar`-model in `Set`, and the Bohr construction is a doctrine-morphism `T_CStar → T_commCStar` over change-of-base `Set → Sets^{C(A)}`". This reframing is **non-trivial** and is essentially the GUT-C research programme.
- **To Hyland–Power 2007**: HLS use the syntactic/semantic split (C*-algebra = syntax; internal Gelfand spectrum = semantics) implicitly; making it explicit via Lawvere theories is what GUT-C Path C does.
- **To Heunen–Karvonen 2019** (TAC 34): formalises dagger-categories and dagger-limits, addressing exactly the dagger ↔ cartesian tension. This is the bridge paper for the GUT-C O1 attack.
- **To Mathlib**: `Mathlib.Analysis.NormedSpace.Star.Basic` covers C*-algebras; `Mathlib.Topology.Sheaves.*` covers Grothendieck topos prerequisites. The full Bohr topos is *not* in Mathlib yet (would be a several-thousand-LOC project).

---

## Synthesis: T_GUT design implications

### A. Definitive framework choice

Based on these three papers, the precise framework for `T_GUT` is:

> **`T_GUT` is a `(V, ⊗, I)`-enriched Lawvere theory in the sense of Power 1999, where `V` is a 2-doctrine** — specifically `V = Cat_{SMCC,⊕}` (the 2-category of SMCCs with biproducts) — **interpreted via the Hyland–Power 2007 algebraic-operations + generic-effects framework**, **and instantiated in any base `C : V` to yield concrete physics**.

This makes `T_GUT` a *single* syntactic artefact (Power 1999's Def. 3.1), with semantic content (Hyland–Power 2007's models-and-effects framework) parametric in a 2-doctrinal base (lessons from HLS 2009 on why one-base is too restrictive). The HLS construction sits inside this picture as one *direction* of base-change (`Sets → Sets^{C(A)}`), not as the framework itself.

### B. Open Problem O1 attack strategy

Given the three papers, the path to attacking dagger + cartesian coexistence is:

1. **Do not unify them inside one base.** HLS 2009 shows that encoding `Hilb` *inside* a Heyting topos *loses the dagger*. The Bohrification asymmetry is structural, not a bug to fix.
2. **Use the Power 1999 enriched-Lawvere doctrine to host them as *separate* δ-realisations.** `T_GUT`-models in `FdHilb` (δ = ℂ², dagger structure visible) and in `HeytAlg` (δ = Bool, cartesian structure visible) are *parallel instances* — neither is encoded in the other.
3. **The universality theorem** (Section §4 of `gut-c-doctrine.md`) is: *every* `T_GUT`-model `M : T_GUT → C` is equivalent to the canonical `R_C = δ_C^⊗N`-model. This is the Power 1999 essential-surjectivity of `Law(V) ≃ Mnd_f(V)`, applied per-base.
4. **The O1 *novel content*** is the meta-claim: the same `T_GUT` admits both cartesian and dagger realisations *because* the doctrine `V = Cat_{SMCC,⊕}` is silent on which structure dominates — both classes of base sit inside `V`.

### C. Order of attack (formalisation)

1. **First instance** — formalise `T_GUT` as a Power 1999 enriched Lawvere theory for `V = FinVect_{F_2}` (the canonical base; matches existing R₀..R₈ machinery). This is the *anchor*. Build it in Lean as `formal/SSBX/Foundation/Doctrine/SMCCEnrichedLawvereTheory.lean` plus `T_GUT.lean` plus `Models/CanonicalR.lean`. Estimated 1500–2500 LOC.
2. **Second instance** — `T_GUT`-model in `HeytAlg` (cartesian-closed base; recovers the classical/intuitionistic side). Confirms the doctrine is *not* secretly linear-only. Estimated 800–1500 LOC additional.
3. **Third instance** — `T_GUT`-model in `FdHilb` (dagger-compact base). Requires Heunen–Karvonen 2019 machinery; partial in Mathlib. Estimated 2000–3000 LOC additional.
4. **Generalisation** — Universal Sayability theorem across the three bases above, proven by reducing each to the Power 1999 equivalence in its own base then composing with a doctrinal-morphism comparison. Estimated 1500 LOC.

### D. Risks identified from literature

1. **Rank / finitarity (from Hyland–Power §7)**: anything in `T_GUT` requiring infinite arities will break. *Mitigation*: keep R-tower depth bounded (R₀..R₈ is fine).
2. **Cardinality of f.p. objects in `Hilb` (from Power 1999 §5)**: classical l.f.p. fails; need the cardinal generalisation plus dagger-compactness. *Mitigation*: restrict to `FdHilb`; Mathlib already supports f.d. case.
3. **Bohrification asymmetry (from HLS 2009 §11)**: do not try to encode dagger structure inside a Heyting topos. *Mitigation*: keep bases distinct; doctrine is the unifier, not encoding.
4. **Locale theory absent from Mathlib (from HLS 2009 §4–6)**: if we want a full Bohrification cross-check, we need locale theory. *Mitigation*: optional — Bohrification is a *test case*, not a deliverable.
5. **2-categorical change-of-base (gap in all three)**: none of the three papers gives a clean doctrine-morphism theorem. *Mitigation*: cite Garner–Power 2018 as the closest available formalism; expect this to be the *novel mathematical content* of our paper.

### E. Citations roadmap for `T_GUT` paper

The `T_GUT` paper should be positioned as:

- **Building directly on Power 1999** (Theorem 4.2 = our universality-per-base). Cite as the *foundational* reference for the enriched Lawvere doctrine.
- **In the tradition of Hyland–Power 2007** (algebraic operations as the right syntactic primitive; varying-base perspective). Cite as the *philosophical* and *methodological* reference.
- **Contrasting with Heunen–Landsman–Spitters 2009** (Bohrification is the *asymmetric* one-base case; we generalise to a parametric many-base doctrine, dissolving the asymmetry by *not* encoding one base inside another). Cite as the *worked precedent* and the *negative example* motivating doctrinal generality.
- **Citing Heunen–Karvonen 2019** (TAC 34) and Garner–Power 2018 (NJM) for the dagger-Lawvere and change-of-base machinery respectively.
- **Citing Lucyshyn-Wright 2018** (LMCS 14:16; arXiv 1707.08694) for the *modern* enriched view that subsumes Power 1999.
- **Possibly citing Staton 2014** (WACT) for Freyd-categories-as-enriched-Lawvere as a related instance.

The expected venue match: **TAC**, **LMCS**, or **MSCS**.

---

**End of notes** | Confidence: **medium–high** for Power 1999 + Hyland–Power 2007 (multiple consistent secondary sources, training-knowledge confirms); **medium** for HLS 2009 (PDF un-renderable; relying on abstract + nLab + follow-up summaries — theorem-number precision deferred to a future verification pass).
