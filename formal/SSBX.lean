-- 生生不息论 · SSBX Lean 4 形式化
-- 顶层入口；按子目录与簇分组导入。

import SSBX.Core
import SSBX.Roster

-- Pending empirical interfaces: certificate boundaries only; no roster promotion.
import SSBX.Pending.Interfaces
import SSBX.Pending.Examples

-- 文 / 字 / 算子目录
import SSBX.Text.Glyph
import SSBX.Text.WenyanOperators
import SSBX.Text.OperatorReadings
import SSBX.Text.OperatorSignatures
import SSBX.Text.OperatorFamilySemantics
import SSBX.Text.OperatorReachabilitySemantics
import SSBX.Text.OperatorInstructionSemantics
import SSBX.Text.OperatorCellCandidateSemantics
import SSBX.Text.OperatorCellSemantics
import SSBX.Text.Completeness

-- 真 / 模型 层
import SSBX.Truth.Basic
import SSBX.Truth.ClaimLedger
import SSBX.Truth.Semantics
import SSBX.Truth.Adequacy
import SSBX.Truth.Absolute
import SSBX.Model.Adequacy
import SSBX.Model.ConcreteLedger

-- Foundation/Core — 字根、注义、单根证书
import SSBX.Foundation.Core.Yuan
import SSBX.Foundation.Core.Monism
import SSBX.Foundation.Core.MonadRoot
import SSBX.Foundation.Core.AtomDerivation
import SSBX.Foundation.Core.MissingGlyphs
import SSBX.Foundation.Core.MathAxiomMap
import SSBX.Foundation.Core.ShengshengBuxi
import SSBX.Foundation.Core.Li
import SSBX.Foundation.Core.HumanAlignment
import SSBX.Foundation.Core.Attention
import SSBX.Foundation.Core.EvolutionDao
import SSBX.Foundation.Core.Alignment
import SSBX.Foundation.Core.Sincerity
import SSBX.Foundation.Core.Renlei

-- Foundation/Wen — 古文虚字 / 核 / 自释 / 类型化扩展 / 解析 / first-light demo
import SSBX.Foundation.Wen.Operators
import SSBX.Foundation.Wen.Kernel
import SSBX.Foundation.Wen.Layered
import SSBX.Foundation.Wen.Native
import SSBX.Foundation.Wen.WenyanText
import SSBX.Foundation.Wen.ClassicalTextRHierarchyBridge
import SSBX.Foundation.Wen.R8ProjectionCalculus
import SSBX.Foundation.Wen.R8ProjectionKernel
import SSBX.Foundation.Wen.RootRuleKernel
import SSBX.Foundation.Wen.RootOperator
import SSBX.Foundation.Wen.R8AxisIndependence
import SSBX.Foundation.Wen.RootRuleExamples
import SSBX.Foundation.Wen.RootRuleDemoInterpreter
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Wen.MetaInterp
import SSBX.Foundation.Wen.MetaInterp.SkipInstr
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlocks
import SSBX.Foundation.Wen.MetaInterp.Block_HuCuoZong
import SSBX.Foundation.Wen.MetaInterp.Block_SetShi_FlipYao
import SSBX.Foundation.Wen.MetaInterp.Block_Jump
import SSBX.Foundation.Wen.MetaInterp.Block_Branches
import SSBX.Foundation.Wen.MetaInterp.Block_PushPop
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlocksHard
import SSBX.Foundation.Wen.MetaInterp.Fetch
import SSBX.Foundation.Wen.MetaInterp.FetchProg
import SSBX.Foundation.Wen.MetaInterp.Dispatch
import SSBX.Foundation.Wen.MetaInterp.DispatchProg
import SSBX.Foundation.Wen.MetaInterp.PrologueProg
import SSBX.Foundation.Wen.MetaInterp.SubDispatch_BranchShiEq
import SSBX.Foundation.Wen.MetaInterp.SubDispatch_BranchYaoEq
import SSBX.Foundation.Wen.MetaInterp.OuterLoop
import SSBX.Foundation.Wen.MetaInterp.TargetContract
import SSBX.Foundation.Wen.MetaInterp.Assembly
import SSBX.Foundation.Wen.MetaInterp.Universal
import SSBX.Foundation.Wen.MetaInterp.GodelR8
import SSBX.Foundation.Wen.WenDef
import SSBX.Foundation.Wen.WenyanParser
import SSBX.Foundation.Wen.WenEval
import SSBX.Foundation.Wen.WenDefEval
import SSBX.Foundation.Wen.WenyanSyntax
import SSBX.Foundation.Wen.WenDefCompile
import SSBX.Foundation.Wen.WenyanParserGeneral
import SSBX.Foundation.Wen.WenSurface.Lex
import SSBX.Foundation.Wen.WenSurface.Reading
import SSBX.Foundation.Wen.WenSurface.DomainLaw
import SSBX.Foundation.Wen.WenSurface.Semantics
import SSBX.Foundation.Wen.WenSurface.Syntax
import SSBX.Foundation.Wen.WenSurface.Elaborate
import SSBX.Foundation.Wen.WenSurface.EndToEnd
import SSBX.Foundation.Wen.WenSurface.Namespace
import SSBX.Foundation.Wen.WenSurface.Coverage
import SSBX.Foundation.Wen.WenSurface.ErrorRender

-- Foundation/Jian — 间之核（14 字粒子核）
import SSBX.Foundation.Jian.JianOntology
import SSBX.Foundation.Jian.Jian
import SSBX.Foundation.Jian.JianSTLC
import SSBX.Foundation.Jian.JianMinimality
import SSBX.Foundation.Jian.JianModeKernel
import SSBX.Foundation.Jian.JianYiBridge

-- Foundation/Yi — 易之代数
import SSBX.Foundation.Atlas.Yi.Classical.Core.Yi
import SSBX.Foundation.Atlas.Yi.Classical.Core.YiCore

-- Foundation/Bagua — 八卦 / R7 / R8 / Gödel-Rice / 风险缓解
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.BaguaAlgebra
import SSBX.Foundation.Atlas.Yi.Classical.Cells.R7  -- R₇ 中间层 (Hexagram × YinBit, 128 cells, 印 算子)
import SSBX.Foundation.Hierarchy.R5_Wuyao  -- R₅ strict (Z/2)⁵ = 32 carrier (Mian × Bool)
import SSBX.Foundation.Hierarchy.LiftProject  -- Uniform Lift/Project pairs across R₀..R₈
import SSBX.Foundation.Hierarchy.Operators.Atomic  -- XOR subgroup re-export (imprint/project/flipᵢ/hexCuo)
import SSBX.Foundation.Hierarchy.Operators.V4  -- canonical V4 kernel + projections/actions
import SSBX.Foundation.Hierarchy.Operators.Interlace  -- non-V4 interlace projection
import SSBX.Foundation.Hierarchy.Operators.OXPrefix  -- variable-length o/x prefixes
import SSBX.Foundation.Hierarchy.RHierarchy  -- R₀..R₈ index-named alias umbrella
import SSBX.Foundation.Hierarchy.ZoneClassifier  -- 任意位 oxox 全轴判定 + 道/理/可理/墙 子集化
import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8  -- R₈ 闭合层 (Hexagram × Shi V₄, 256 cells, 投 算子)
import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8Stratify  -- R₇/R₈ 双层 stratification + R8_complete bundle
import SSBX.Foundation.Atlas.Yi.Classical.Computation.BaguaTuring
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.Newman
import SSBX.Foundation.Atlas.Yi.Classical.Diagonal.KleeneInternal
import SSBX.Foundation.Atlas.Yi.Classical.Diagonal.GodelLi
import SSBX.Foundation.Atlas.Yi.Classical.Computation.BaguaWenSpec
import SSBX.Text.OperatorAnchors
import SSBX.Text.OperatorCellMap
import SSBX.Foundation.Atlas.Yi.Classical.Computation.ChunkedDecide
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.CuoInvariance
import SSBX.Foundation.Atlas.Yi.Classical.Computation.FuelDiscipline

-- Foundation/Notation — `OX["..."]` 8-char Cell256 string literal macro
import SSBX.Foundation.Notation.OXNotation

-- Foundation/Lang — R-hierarchy Lisp (yao/yuan dual programming language)
import SSBX.Foundation.Lang.Sexp
import SSBX.Foundation.Lang.Pattern
import SSBX.Foundation.Lang.Rule
import SSBX.Foundation.Lang.Eval
import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Lang.L1_Yao
import SSBX.Foundation.Lang.L2_SiXiang
import SSBX.Foundation.Lang.L3_Trigram
import SSBX.Foundation.Lang.L4_Mian
import SSBX.Foundation.Lang.L5_Wuyao
import SSBX.Foundation.Lang.L6_Hexagram
import SSBX.Foundation.Lang.L7_Cell128
import SSBX.Foundation.Lang.Demo  -- 生生不息 / 道法自然 / R₂⊃R₁×R₁ runnable demos
import SSBX.Foundation.Lang.DaoJudge  -- 解释器+道判机: language closed in 128 cells
import SSBX.Foundation.Lang.Wuchang   -- 仁义礼智信 named constants + 五常归一 theorem
import SSBX.Foundation.Lang.Names     -- 64 卦 + R₄/R₅/R₇/R₈ name functions (字 → cell, cell → 字)
import SSBX.Foundation.Lang.Confucian -- 四端/八目/五伦/大同 named cells in R₃/R₅/R₆
import SSBX.Foundation.Lang.Lexicon   -- canonical Chinese↔English↔bit-string mapping

-- Foundation/Squaring is retired per the v0.6 R-Family doctrine.
-- Its content has been redistributed:
--   * squaring tower R₁→R₂→R₄→R₈ → `Foundation/R/Squaring.lean` (P1)
--   * beyond-R₈ extension (R₁₆/R₃₂/…) → `Foundation/R8/Squaring.lean` (P2)
--   * `Stream' (R 8)` trajectories → `Foundation/R8/Dynamics.lean` (P2)
--   * F₂ Mathlib instances → `Foundation/R8/MathlibInstances.lean` (P2)
--   * profinite limit (the only genuinely new content) → `Foundation/RInfty` (P4.4)

-- Foundation/Eight — 八衍：数 / 推 / 测 / 形 / 类 / 动 / 识 / 象
import SSBX.Foundation.Eight.ShuSuan
import SSBX.Foundation.Eight.LuoJi
import SSBX.Foundation.Eight.TongJi
import SSBX.Foundation.Eight.XingWei
import SSBX.Foundation.Eight.LeiYing
import SSBX.Foundation.Eight.DongLi
import SSBX.Foundation.Eight.XinZhi
import SSBX.Foundation.Eight.WuXiang

-- Phase 4 主体（Mathlib 接入 · 连续测度 / ℝ Cauchy / 量子叠加 / SU(N)）
import SSBX.Foundation.Modern.RCauchy
import SSBX.Foundation.Modern.Kolmogorov
import SSBX.Foundation.Modern.Quantum
import SSBX.Foundation.Modern.QuantumR8Bridge
import SSBX.Foundation.Modern.QuantumRelativityNoGo
import SSBX.Foundation.Modern.QuantumRelativityIntegration
import SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
import SSBX.Foundation.Modern.QuantumRelativityWenBoundary
import SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
import SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
import SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
import SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
import SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
import SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
import SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge
import SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
import SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
import SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
import SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge
import SSBX.Foundation.Modern.QuantumRelativityFinitePathSumAlgebraBridge
import SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge
import SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge
import SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge
import SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
import SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
import SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
import SSBX.Foundation.Modern.QuantumRelativityCanonicalRepresentativeBridge
import SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
import SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge
import SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge
import SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
import SSBX.Foundation.Modern.QuantumRelativityStepwiseUnificationBridge
import SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
import SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
import SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
import SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
import SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge
import SSBX.Foundation.Modern.QuantumRelativityChannelComposeAssociativityBridge
import SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
import SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge
import SSBX.Foundation.Modern.QuantumRelativityUnitaryCPTPLedgerBridge
import SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
import SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
import SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge
import SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
import SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
import SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge
import SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge
import SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge
import SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge
import SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge
import SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge
import SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge
import SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge
import SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedRecursiveCarrierBridge
import SSBX.Foundation.Modern.QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge
import SSBX.Foundation.Modern.QuantumRelativityTwoRouteKernelPathEnumerationBridge
import SSBX.Foundation.Modern.SUN

-- Phase 4 主体续（自然演绎 / Lebesgue 积分 / 连续 ODE / 神经科学 / 完备性深化）
import SSBX.Foundation.Modern.NaturalDeduction
import SSBX.Foundation.Modern.Lebesgue
import SSBX.Foundation.Modern.ODESmoothness
import SSBX.Foundation.Modern.Neuro
import SSBX.Foundation.Modern.KolmogorovExt
import SSBX.Foundation.Modern.RCauchyExt

-- Phase 4 主体三尾（几何位 / 范畴论扩展 / 道-理二分 cross-cutting）
import SSBX.Foundation.Modern.HexagramPosition
import SSBX.Truth.SelfDescription
import SSBX.Foundation.Modern.CatExt
import SSBX.Foundation.Modern.DaoLi
import SSBX.Foundation.Modern.HistoryTapeStructure
import SSBX.Foundation.Modern.WuJianShiTrinity

-- Phase 4 深化（Yoneda 全引理 / Lebesgue 深 (MCT/DCT/Fubini) / Picard-Lindelöf 一般化）
import SSBX.Foundation.Modern.YonedaFull
import SSBX.Foundation.Modern.LebesgueDepth
import SSBX.Foundation.Modern.PicardLindelofGen

-- Phase 4 终章（Cat.op + 函子范畴 / IID-aware WLLN / Bochner + IsPicardLindelof）
import SSBX.Foundation.Modern.CatOp
import SSBX.Foundation.Modern.IIDWlln
import SSBX.Foundation.Modern.BochnerPL

-- Phase 4 边界补章（统一 / 可知 / 可 / 量子时空互补）
import SSBX.Foundation.Modern.UnityBoundary
import SSBX.Foundation.Modern.KnowableBoundary
import SSBX.Foundation.Modern.KeBoundary
import SSBX.Foundation.Modern.QuantumSpacetime

-- v0.6 R-Family tower (per wen-algebra.md v0.6 + v4-foundation.md v0.5):
-- language-independent core (R N := Fin N → Bool), specialty modules
-- for R 4 / R 8, and application-layer Atlas overlays.
import SSBX.Foundation.R
import SSBX.Foundation.R4
import SSBX.Foundation.R8
import SSBX.Foundation.RInfty
import SSBX.Foundation.Atlas

-- T5 polymorphic-field scaffold (G11 cut-1: char(k)=2 + char(k)≠2 dispatch).
-- Per gut-roadmap.md §十二.
import SSBX.Foundation.R.UniquenessAlgebraic
import SSBX.Foundation.R.UniquenessGeneralField

-- G11 bottleneck-removal: install `IsSimpleRing` / `IsArtinianRing`
-- chain on `Matrix (Fin n) (Fin n) (ZMod p)` and `Matrix (Fin n) (Fin n) k`
-- so Mathlib's `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`
-- applies directly to our R₄-anchor ring.
-- Per gut-roadmap.md G11 (T5-B parametric over k).
import SSBX.Foundation.R.Algebra.MatFqInstances

-- Phase E: Wen/Core — PartialCell-native Wen kernel.
-- Parallel to legacy Foundation/Bagua/BaguaTuring.lean (which is Yi-flavored).
-- Yi semantics is provided via Foundation/Atlas/Yi/ as application overlay.
import SSBX.Foundation.Wen.Core

-- Phase G/I: Lang/Partial — PartialCell-based language layer (proof-of-concept).
import SSBX.Foundation.Lang.Partial

-- Representation closure: A/B/D locator strategies for concept → R-Family.
-- Per wen-substrate.md v1.4 §Representation.
import SSBX.Foundation.Representation

-- Closure (Knaster-Tarski lfp identification of D1, skeleton).
-- Per docs-next/00_start/lawvere-identification.md v0.2 §§4.5, 5.
import SSBX.Foundation.Closure.PhiOperator

-- Cross-base functor library (G7 gut-roadmap §三 Tier 2).
-- Mod-phase Hilbert ↔ Pauli ↔ R(2n) — reverse functors + RFamily k bridges.
import SSBX.Foundation.Wen.Embeddings.StabilizerQM
import SSBX.Foundation.Wen.Embeddings.HilbertPauliFunctor

-- GUT-C Path C foundation: elementary topos bundling (PR-1).
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §11.1.
-- Mathlib-PR-quality skeleton: bundles HasFiniteLimits + CartesianMonoidalCategory +
-- MonoidalClosed + HasSubobjectClassifier into a single `class ElementaryTopos`.
-- Includes canonical instance on `Type u` (Lawvere classical construction).
import SSBX.Foundation.CategoryTheory.ElementaryTopos

-- GUT-C Path C foundation: Lawvere theories + models API (PR-2).
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §11.1.
-- Mathlib-PR-quality skeleton: `class LawvereTheory T` (small finite-product
-- category with chosen generator and powers), `structure Model T C`
-- (finite-product-preserving functor), `structure LawvereTheoryHom T T'`
-- (morphism of theories), and a category instance on `Model T C`.
-- `free` Lawvere theory + Lawvere/finitary-monad equivalence stubs (`sorry`).
import SSBX.Foundation.Doctrine.LawvereTheory

-- GUT-C Path C foundation: V-enriched Lawvere theories (Power 1999, PR-3).
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §§3.2, 11.1.
-- Mathlib-PR-quality skeleton: `class EnrichedLawvereTheory V T` (V-enriched
-- ordinary category with conical V-finite-products + chosen generator),
-- `structure EnrichedModel V T C` (V-product-preserving V-functor),
-- `structure EnrichedLawvereTheoryHom`, plus skeleta for additive (V = Ab),
-- linear (V = Vect_K), 2-Lawvere (V = Cat), free V-category L_V, Power's
-- forgetful / free V-T-model functors, and the Power 1999 main theorem
-- (`enriched_lawvere_iff_finitary_v_monad`) stated with `sorry`-tolerant
-- placeholders pending Mathlib's weighted-enriched-limits API.
-- Cross-dep on G1: instance `LawvereTheory T ⇒ LawvereTheorySig T`.
import SSBX.Foundation.Doctrine.EnrichedLawvereTheory

-- GUT-C Path C Doctrine: T_GUT Lawvere theory skeleton.
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §§3.3, 3.4, 3.5.
-- Defines the signature `TGUTOp`, equational laws `TGUTLaw`, and the
-- `TGUTRealisation C δ` structure that any SMCC realisation satisfies.
-- Headline `universal_sayability` statement included; proof = γ.3 work.
import SSBX.Foundation.Doctrine.T_GUT

-- GUT-C Path C Doctrine: T_GUT algebraic instance — bridge from new
-- framework to existing GUT-A/B R-family-over-(ZMod q).
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §3.4 + §11.2.
-- Packages `Foundation/R/UniquenessGeneral.lean` + `UniquenessAlgebraic.lean`
-- as a concrete `TGUTRealisation (Type 0) (ZMod q)`, recovering
-- GUT-A's `T5_A_ringEquiv_at_4_zmod2` as a corollary of the algebraic
-- specialisation.
import SSBX.Foundation.Doctrine.Instance.Algebraic

-- GUT-C Path C Phase γ.2: first non-algebraic T_GUT instance (Heyting / δ=Prop).
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §3.4, §4.2 deliverable (4), §8.2.
-- Concrete `TGUTRealisation (Type 0) Prop` with Heyting-flavour generators
-- + Heyting-specific reformulations of P3 (lattice morphism classification,
--   `relate_heyting_pointwise_himp`) and P7b (minimum non-Boolean 4-element
--   Heyting algebra, `DiamondH4`).
-- Validates Path C framework in PARTIAL form: 11/11 generator slots filled;
-- 2 sorries (R_tensor matching Algebraic instance pattern; P3-Heyting
-- classification is research-level open problem).
import SSBX.Foundation.Doctrine.Instance.Heyting

-- GUT-C Path C Phase γ.2 sub-deliverable: DiamondH4 uniqueness theorem.
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §4.2.2 (DiamondH4 discovery).
-- Discharges the uniqueness flag on `P7b_heyting` from
-- Foundation/Doctrine/Instance/Heyting.lean §5: every non-Boolean
-- 4-element bounded distributive lattice (equivalently, every
-- non-Boolean 4-element Heyting algebra) is order-isomorphic to
-- `DiamondH4`.  Proven by `Finset.card_eq_four` enumeration +
-- exhaustive case-analysis on 16 pairs in the 4-element universe.
-- **0 sorries, 0 axioms** — fully discharges the open conjecture.
import SSBX.Foundation.Order.HeytingClassification

-- GUT-C Path C Phase γ.2 sub-deliverable: Heyting-bimorphism classification.
-- Per docs-next/00_start/gut-c-doctrine.md v0.3 §4.2.1 (research open #2 from G5).
-- Discharges the open `P3_heyting` flag from
-- Foundation/Doctrine/Instance/Heyting.lean §4 via the **collapse theorem**:
-- strong `IsHeytingBilinear` (= HeytingHom in each argument) is
-- PROVABLY VACUOUS on every non-degenerate Heyting algebra (`⊥ ≠ ⊤`).
-- The structurally-correct replacement is `IsSubBimorphism` (lattice-level,
-- without implication preservation), with 6 fundamental examples on every
-- bounded distributive lattice: `inf2`, `sup2`, `proj1`, `proj2`,
-- `constBot`, `constTop`.
-- **0 sorries, 0 axioms** — refines the conjecture from a single open
-- to a two-tier framework (strong-vacuous + sub-bimorphism-Birkhoff).
import SSBX.Foundation.Order.HeytingBimorphism

-- GUT-C γ.5-E Pauli ring iso research-open attack.
-- Lifts existing pauliBaseToHilbert to full ring-theoretic statement:
-- ℂ-linear independence of {I, X, Y, Z} as basis of Mat₂(ℂ);
-- F₂-subalgebra of Mat₂(ℂ) generated by Pauli matrices.
-- 0 sorries, 0 axioms (Mathlib `Complex.I` + Pauli matrix theory).
import SSBX.Foundation.Wen.Embeddings.PauliRingIso

-- GUT-C γ.5-F Frame bimorphism / Joyal-Tierney classification research-open attack.
-- Cartesian classification proved; non-cartesian (Joyal-Tierney) flagged
-- as Mathlib upstream gap (~1000-1500 LOC PR). 2 sorries documented.
import SSBX.Foundation.Order.FrameBimorphism

-- GUT-C Path C Phase γ.3: second non-algebraic T_GUT instance (quantum / δ=PauliBase).
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §3.4, §8.3.
-- Concrete `TGUTRealisation (Type 0) PauliBase` with stabilizer-quantum-flavour
-- generators built on the existing `StabilizerQM` + `HilbertPauliFunctor` infra.
-- Strategy: pivots from "abstract FdHilb category" (Mathlib doesn't have it)
-- to **concrete stabilizer-quantum substrate** via Pauli matrices.
-- Quantum-specific reformulations:
--   * P3 → symplectic form `R.sigma` (commutator detection in stabilizer);
--   * P7b → `Mat₂(ℂ)` anchor via `pauliToHilbert` (Pauli → Hilbert).
-- KEY RESULT: P6 (V₄ modality) is LITERAL Klein-four in quantum — single-qubit
-- Pauli {I, X, Y, Z} IS the V₄ group (the "Pauli-Klein4 coincidence").
-- Validates Path C framework in SAME PARTIAL form as Heyting; sufficient to
-- commit γ.3-topological + γ.4 paper.
import SSBX.Foundation.Doctrine.Instance.Quantum

-- GUT-C Path C Phase γ.3: third non-algebraic T_GUT instance
-- (topological / δ=Sierpinski Ω, ambient Frm).
-- Per docs-next/00_start/gut-c-doctrine.md v0.2 §3.4, §4.3 deliverable (2).
-- Concrete `TGUTRealisation (Type 0) SierpinskiOmega` (= Prop with frame
-- instance) reinterpreting the seven generators in **frame** (not Heyting)
-- flavour: frame product, frame morphism classification (P3-topological),
-- frame exponential, Sierpinski-square Wedderburn anchor (P7b-topological,
-- `Sierpinski2_Squared` = Boolean 4-element frame — distinct from Heyting's
-- non-Boolean `DiamondH4`).
-- Validates Path C framework in PARTIAL form with explicit BOUNDARY findings:
-- the Joyal-Tierney non-cartesian frame tensor and frame exponential are
-- Mathlib-upstream-PR-level gaps; the framework gracefully degrades to
-- cartesian-product approximations. No generator literally breaks.
-- 2 sorries: R_tensor (matching siblings), P3_topological classification.
-- P7b_topological_uniqueness + hom_NM_frame_exponential weakened to
-- type-level existence (Pi.instFrame), since the genuine OrderIso /
-- Joyal-Tierney machinery is out-of-scope (Mathlib-upstream-PR-level).
import SSBX.Foundation.Doctrine.Instance.Topological
