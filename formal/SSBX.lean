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
import SSBX.Foundation.Wen.WenyanText
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Wen.MetaInterp
import SSBX.Foundation.Wen.MetaInterp.SkipInstr
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
import SSBX.Foundation.Wen.MetaInterp.Block_HuCuoZong
import SSBX.Foundation.Wen.MetaInterp.Block_SetShi_FlipYao
import SSBX.Foundation.Wen.MetaInterp.Block_Jump
import SSBX.Foundation.Wen.MetaInterp.Block_Branches
import SSBX.Foundation.Wen.MetaInterp.Block_PushPop
import SSBX.Foundation.Wen.MetaInterp.Fetch
import SSBX.Foundation.Wen.MetaInterp.Dispatch
import SSBX.Foundation.Wen.MetaInterp.OuterLoop
import SSBX.Foundation.Wen.WenDef
import SSBX.Foundation.Wen.WenyanParser
import SSBX.Foundation.Wen.WenEval
import SSBX.Foundation.Wen.WenDefEval
import SSBX.Foundation.Wen.WenyanSyntax
import SSBX.Foundation.Wen.WenyanReflect
import SSBX.Foundation.Wen.WenDefCompile
import SSBX.Foundation.Wen.WenyanParserGeneral
import SSBX.Foundation.Wen.WenyanSelfHost
import SSBX.Foundation.Wen.WenyanQuine
import SSBX.Foundation.Wen.WenyanQuineRoutes
import SSBX.Foundation.Wen.WenyanQuineConcreteSearch
import SSBX.Foundation.Wen.WenyanQuineKleene
import SSBX.Foundation.Wen.WenyanLambdaRoute
import SSBX.Foundation.Wen.WenyanLambdaBridge
import SSBX.Foundation.Wen.WenSurface.Lex
import SSBX.Foundation.Wen.WenSurface.Reading
import SSBX.Foundation.Wen.WenSurface.Semantics
import SSBX.Foundation.Wen.WenSurface.Syntax
import SSBX.Foundation.Wen.WenSurface.Elaborate
import SSBX.Foundation.Wen.WenSurface.EndToEnd
import SSBX.Foundation.Wen.WenSurface.Coverage
import SSBX.Foundation.Wen.DaoSource
import SSBX.Foundation.Wen.Demo
import SSBX.Foundation.Wen.AntiSchmitt
import SSBX.Foundation.Wen.AlignmentFailures
import SSBX.Foundation.Wen.EconGame

-- Foundation/Jian — 间之核（14 字粒子核）
import SSBX.Foundation.Jian.JianOntology
import SSBX.Foundation.Jian.Jian
import SSBX.Foundation.Jian.JianSTLC
import SSBX.Foundation.Jian.JianMinimality
import SSBX.Foundation.Jian.JianModeKernel
import SSBX.Foundation.Jian.JianYiBridge

-- Foundation/Yi — 易之代数
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Yi.YiCore

-- Foundation/Bagua — 八卦 / 192 / Gödel-Rice / 风险缓解
import SSBX.Foundation.Bagua.BaguaAlgebra
import SSBX.Foundation.Bagua.Cell192
import SSBX.Foundation.Bagua.BaguaTuring
import SSBX.Foundation.Bagua.Newman
import SSBX.Foundation.Bagua.KleeneInternal
import SSBX.Foundation.Bagua.GodelLi
import SSBX.Foundation.Bagua.KleeneCarrier
import SSBX.Foundation.Bagua.BaguaWenSpec
import SSBX.Text.OperatorAnchors
import SSBX.Text.OperatorCellMap
import SSBX.Foundation.Bagua.ChunkedDecide
import SSBX.Foundation.Bagua.CuoInvariance
import SSBX.Foundation.Bagua.FuelDiscipline

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
import SSBX.Foundation.Modern.QuantumRelativityNoGo
import SSBX.Foundation.Modern.QuantumRelativityIntegration
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

-- Phase 4 深化（Yoneda 全引理 / Lebesgue 深 (MCT/DCT/Fubini) / Picard-Lindelöf 一般化）
import SSBX.Foundation.Modern.YonedaFull
import SSBX.Foundation.Modern.LebesgueDepth
import SSBX.Foundation.Modern.PicardLindelofGen

-- Phase 4 终章（Cat.op + 函子范畴 / IID-aware WLLN / Bochner + IsPicardLindelof）
import SSBX.Foundation.Modern.CatOp
import SSBX.Foundation.Modern.IIDWlln
import SSBX.Foundation.Modern.BochnerPL
