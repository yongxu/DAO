-- 生生不息论 · SSBX Lean 4 形式化
-- 顶层入口；按子目录与簇分组导入。

import SSBX.Core
import SSBX.Roster

-- 文 / 字 / 算子目录
import SSBX.Text.Glyph
import SSBX.Text.WenyanOperators
import SSBX.Text.Completeness

-- 真 / 模型 层
import SSBX.Truth.Basic
import SSBX.Truth.ClaimLedger
import SSBX.Truth.Semantics
import SSBX.Truth.Adequacy
import SSBX.Truth.Absolute
import SSBX.Model.Adequacy

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

-- Foundation/Wen — 古文虚字 / 核 / 自释 / 类型化扩展 / 解析 / first-light demo
import SSBX.Foundation.Wen.Operators
import SSBX.Foundation.Wen.Kernel
import SSBX.Foundation.Wen.WenyanText
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Wen.WenDef
import SSBX.Foundation.Wen.WenyanParser
import SSBX.Foundation.Wen.Demo

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
import SSBX.Foundation.Bagua.BaguaWenSpec
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
import SSBX.Foundation.Phase4.RCauchy
import SSBX.Foundation.Phase4.Kolmogorov
import SSBX.Foundation.Phase4.Quantum
import SSBX.Foundation.Phase4.SUN

-- Phase 4 主体续（自然演绎 / Lebesgue 积分 / 连续 ODE / 神经科学 / 完备性深化）
import SSBX.Foundation.Phase4.NaturalDeduction
import SSBX.Foundation.Phase4.Lebesgue
import SSBX.Foundation.Phase4.ODESmoothness
import SSBX.Foundation.Phase4.Neuro
import SSBX.Foundation.Phase4.KolmogorovExt
import SSBX.Foundation.Phase4.RCauchyExt
