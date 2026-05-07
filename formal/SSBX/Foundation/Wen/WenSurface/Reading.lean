/-
# WenSurface.Reading — 单读 resolver (v1)

把 GlyphTok 流映到 ResolvedTok 流。每个 ResolvedTok 携带：
  · 原 GlyphTok（位置 / surface）
  · ResolvedAtom：要么是 hex 常值，要么是 catalogue 算子读法

## v1 范围（最小闭环）

直接 surface map，硬编码：
  · **6 stdlib 算子**: 推/比/不/必/同/凡 → T_10/R_8/N_1/M_1/I_1/Q_1
    与 [WenDef.lean](../WenDef.lean) `Stdlib.{tui,bi,bu,biModal,tong,fan}Def` 一一对应。
  · **1 hex 常**: 一 → YiCore.«一»
  · 其他 surface → `.noReading`

Phase C（cue-aware）将取代此层；Phase B 仅为打通 lex→elab 管线。

## 状态

0 sorry / 0 axiom / 总函数. 关键例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.Lex
import SSBX.Text.OperatorReadings
import SSBX.Foundation.Yi.YiCore

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Text.Glyph
open SSBX.Text.WenyanOperators
open SSBX.Text.OperatorReadings
open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Yi.YiCore

/-! ## § 1  Resolved 类型 -/

/-- 已消歧的原子：卦字面值 / Bool 字面值 / catalogue 算子读法 /
    应用标记 / 迭代构式. -/
inductive ResolvedAtom where
  | hexConst    (h : Hexagram)
  | boolConst   (b : Bool)
  | catalogueOp (reading : OperatorReading)
  | appMarker             -- 「之」 等不发射 Tm 的 surface marker
  | iterate               -- 「之又」 迭代构式 marker：F X ↦ F (F X)
deriving DecidableEq, Repr

/-- 已消歧的 token：保留 GlyphTok 与解析结果. -/
structure ResolvedTok where
  tok  : GlyphTok
  atom : ResolvedAtom
deriving DecidableEq, Repr

/-- Resolver 错误。 -/
inductive ResolveErr where
  | noReading (surface : String) (col : Nat) : ResolveErr
deriving DecidableEq, Repr

/-! ## § 2  v1 surface map -/

/-- 6 个 stdlib 算子的 surface → catalogue reading. 每条 reading
    通过 `catalogueReading` factory 构造，与 [Stdlib WenDef](../WenDef.lean#L171)
    之 def 一一对应. -/
def resolveStdlibOp : Glyph → Option OperatorReading
  | "推" => some (catalogueReading "推" "T-10" "对象推进 / 生" (some .T_10)
                    .prefix [.expectedObject])
  | "比" => some (catalogueReading "比" "R-8"  "邻接对应"     (some .R_8)
                    .prefix [.expectedObject])
  | "不" => some (catalogueReading "不" "N-1"  "命题否定"     (some .N_1)
                    .prefix [.expectedProp])
  | "必" => some (catalogueReading "必" "M-1"  "必然 / □"     (some .M_1)
                    .prefix [.modalFrame])
  | "同" => some (catalogueReading "同" "I-1"  "恒等谓词"     (some .I_1)
                    .prefix [.expectedObject])
  | "凡" => some (catalogueReading "凡" "Q-1"  "凡量"         (some .Q_1)
                    .prefix [.quantifierDomain])
  | "損" | "损" =>
      some (catalogueReading "損" "T-12" "减一"         (some .T_12)
                    .prefix [.expectedObject])
  | "益" =>
      some (catalogueReading "益" "T-13" "加一"         (some .T_13)
                    .prefix [.expectedObject])
  | _   => none

/-- v1 hex 常值 surface → Hexagram。包含「一」与两个固定点「乾」「坤」. -/
def resolveHexConst : Glyph → Option Hexagram
  | "一" => some «一»
  | "乾" => some Hexagram.qian
  | "坤" => some Hexagram.kun
  | _    => none

/-- v1 Bool 字面值 surface → Bool。古汉语之「真」/「假」. -/
def resolveBoolConst : Glyph → Option Bool
  | "真" => some true
  | "假" => some false
  | _    => none

/-- 「之」/「以」 等 application marker —— 不发射 Tm，elab 阶段跳过. -/
def isApplicationMarker : Glyph → Bool
  | "之" => true   -- S_1 属格 / function application
  | _    => false

/-- 「之又」迭代构式：surface 之又 双字独立辨认，
    与单字「之」(appMarker) 互不冲突（不同 surface）. -/
def isIterateConstruction : Glyph → Bool
  | "之又" => true
  | _      => false

/-! ## § 3  Resolver -/

/-- 单 token resolver。优先级：iterate (「之又」) → appMarker (「之」) → bool 常值 →
    hex 常值 → stdlib 算子；全失败则 `.noReading`.

    注：「之又」与「之」是不同 GlyphTok surface（多字 vs 单字 lex 输出），
    优先序无歧义；此处先判 iterate 仅为可读性. -/
def resolveOne (t : GlyphTok) : Except ResolveErr ResolvedTok :=
  if isIterateConstruction t.surface then
    .ok ⟨t, .iterate⟩
  else if isApplicationMarker t.surface then
    .ok ⟨t, .appMarker⟩
  else match resolveBoolConst t.surface with
  | some b => .ok ⟨t, .boolConst b⟩
  | none =>
    match resolveHexConst t.surface with
    | some h => .ok ⟨t, .hexConst h⟩
    | none =>
      match resolveStdlibOp t.surface with
      | some r => .ok ⟨t, .catalogueOp r⟩
      | none   => .error (.noReading t.surface t.startCol)

/-- 全 token 列表 resolver。结构递归，总函数. -/
def resolveSimple : List GlyphTok → Except ResolveErr (List ResolvedTok)
  | []       => .ok []
  | t :: ts  =>
    match resolveOne t with
    | .error e => .error e
    | .ok r =>
      match resolveSimple ts with
      | .error e  => .error e
      | .ok rs    => .ok (r :: rs)

/-- 顶层 entry：String → ResolvedTok 流，串接 lex 与 resolve. -/
def lexAndResolve (s : String)
    : Except (LexErr ⊕ ResolveErr) (List ResolvedTok) :=
  match lexWen s with
  | .error e => .error (.inl e)
  | .ok toks =>
    match resolveSimple toks with
    | .error e => .error (.inr e)
    | .ok rs   => .ok rs

/-! ## § 4  Helper：从 ResolvedTok 抽 atom 列表 -/

/-- 从 resolve 结果抽 atom 序列（丢弃位置信息）. -/
def atomsOf : List ResolvedTok → List ResolvedAtom :=
  List.map (·.atom)

/-- 从 ResolvedAtom 抽 OperatorId（仅对 catalogueOp 有效）. -/
def ResolvedAtom.opId? : ResolvedAtom → Option OperatorId
  | .hexConst _    => none
  | .boolConst _   => none
  | .catalogueOp r => r.operator?
  | .appMarker     => none
  | .iterate       => none

/-- 判别 atom 是否为 appMarker（elab 阶段用）. -/
def ResolvedAtom.isAppMarker : ResolvedAtom → Bool
  | .appMarker => true
  | _          => false

/-! ## § 5  Sanity 例子 (native_decide) -/

/-- Helper: 提取 atom 的 OperatorId（hexConst → none）. -/
private def opIdsOf (s : String) : Option (List (Option OperatorId)) :=
  (lexAndResolve s).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?))

/-- 「推」单独 → catalogueOp T_10. -/
example : opIdsOf "推" = some [some OperatorId.T_10] := by native_decide

/-- 「一」单独 → hexConst «一». -/
example : opIdsOf "一" = some [none] := by native_decide

/-- 6 个 stdlib 算子 + 「一」全打通. -/
example :
    opIdsOf "推 比 不 必 同 凡 一"
      = some [some OperatorId.T_10, some OperatorId.R_8, some OperatorId.N_1,
              some OperatorId.M_1,  some OperatorId.I_1, some OperatorId.Q_1,
              none] :=
  by native_decide

/-- 「推 一」流：T_10 + hex const «一». -/
example :
    opIdsOf "推 一" = some [some OperatorId.T_10, none] :=
  by native_decide

/-- 「乾」 → hexConst Hexagram.qian. -/
example : opIdsOf "乾" = some [none] := by native_decide

/-- 「坤」 → hexConst Hexagram.kun. -/
example : opIdsOf "坤" = some [none] := by native_decide

/-- 「推 乾」 → T_10 + qian. -/
example : opIdsOf "推 乾" = some [some OperatorId.T_10, none] := by native_decide

/-- 「推 之 一」 → T_10 + appMarker + 一. -/
example : opIdsOf "推 之 一" = some [some OperatorId.T_10, none, none] := by native_decide

/-- 「之」 单独识别为 appMarker. -/
example :
    ((lexAndResolve "之").toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.isAppMarker)))
      = some [true] :=
  by native_decide

/-- 「之又」识别为 iterate atom（与单字「之」不同 surface, 不冲突）. -/
example :
    ((lexAndResolve "之又").toOption.map (fun rs => rs.map (·.atom)))
      = some [.iterate] :=
  by native_decide

/-- 未知 surface → ResolveErr. -/
example : opIdsOf "瓜" = none := by native_decide

/-- 空串 → 空 list. -/
example : opIdsOf "" = some [] := by native_decide

/-! ## § 6  结构性断言 -/

/-- v1 stdlib map 之全部 6 个 surface 都解析成 some. -/
example : (["推", "比", "不", "必", "同", "凡"].all
            (resolveStdlibOp · |>.isSome)) = true := by native_decide

/-- v1 hex 常值 map. -/
example : resolveHexConst "一" = some «一»          := by native_decide
example : resolveHexConst "乾" = some Hexagram.qian := by native_decide
example : resolveHexConst "坤" = some Hexagram.kun  := by native_decide
example : resolveHexConst "推" = none               := by native_decide

/-- 6 stdlib 算子的 OperatorId 互不相同（按定义顺序展开）. -/
example :
    (["推", "比", "不", "必", "同", "凡"].filterMap
       (fun s => (resolveStdlibOp s).bind (·.operator?)))
      = [OperatorId.T_10, OperatorId.R_8, OperatorId.N_1,
         OperatorId.M_1,  OperatorId.I_1, OperatorId.Q_1] :=
  by native_decide

/-! ### § 6.5  損/益 surface map (T-12 / T-13) -/

/-- 損/损/益 之 OperatorId — 繁简同读 T_12，益读 T_13. -/
example :
    (["損", "损", "益"].filterMap
       (fun s => (resolveStdlibOp s).bind (·.operator?)))
      = [OperatorId.T_12, OperatorId.T_12, OperatorId.T_13] :=
  by native_decide

/-- 「損」 → catalogueOp T_12. -/
example : opIdsOf "損" = some [some OperatorId.T_12] := by native_decide

/-- 「损」（简体）也读 T_12. -/
example : opIdsOf "损" = some [some OperatorId.T_12] := by native_decide

/-- 「益」 → catalogueOp T_13. -/
example : opIdsOf "益" = some [some OperatorId.T_13] := by native_decide

/-! ## § 7  Cue-based resolution (Phase C)

  v1 走 surface map，对「之」一律视为 noop appMarker —— S_1 的属格读法
  确实与 juxtaposition 之 application 同效，故 elab 阶段透明跳过即可。

  本节增加 cue-aware 通路：从邻居 GlyphTok 之 `canonicalKind` 推 ContextCue，
  再用 `OperatorReadings.contextualReadings` 过滤，若唯一则采用之。
  与 v1 通路并行 —— `resolveSimple` / `resolveOne` 不动。

  v1 重点：当左右皆为 `.glyph` (普通名物) 时发射 `.betweenNominals`，
  「之」据此唯一对应 `«之属格读法»` (operator? = some .S_1)。这与 stdlib
  6 算子相容（其 surface 单字 canonicalKind = .glyph），故 cue 路径与
  surface 路径在 stdlib 范围内殊途同归。

  其他 cue（如 .afterVerb / .beforeMotionVerb）需引入 verb / motion
  分类表，留作后续扩充；本节只交付 betweenNominals 启动样.
-/

/-- 取 `i` 处 token 之 surface 之 canonicalKind；越界返 none. -/
def kindAt? (toks : List GlyphTok) (i : Nat) : Option LexKind :=
  (toks[i]?).map (fun t => canonicalKind t.surface)

/-- 从相邻 GlyphTok 推 ContextCue。窗口 ±1 token.

    启动样：左右皆为 `.glyph` 时发射 `.betweenNominals` —— 此时「之」唯一
    对应 `«之属格读法»` (status = .catalogue, operator? = some .S_1).

    扩充时可加：
    - 左为 `.operator` (motion-like) 时 `.afterVerb`
    - 右为特定 motion verb 时 `.beforeMotionVerb`
    现版只覆盖 `.betweenNominals` 一例，避免 v1 范围外的语义判定.

    位置 0 由于无左邻居，返空 cues. -/
def computeCues (toks : List GlyphTok) (i : Nat) : List ContextCue :=
  match i with
  | 0     => []
  | j + 1 =>
    let leftKind  := kindAt? toks j
    let rightKind := kindAt? toks (j + 2)
    match leftKind, rightKind with
    | some .glyph, some .glyph => [.betweenNominals]
    | _,           _           => []

/-- 从给定 cue 上下文中查找 glyph 的唯一 catalogue reading
    （status = .catalogue ∧ operator?.isSome）.

    关键：当 cues 为空时直接返 none —— 不依赖 `contextualReadings` 的
    fallback（后者在空 cue 时会返所有 readings，让 cue 路径退化）.
    cue 路径 *只* 在显式 cue 下生效；其余情形退到 surface map. -/
def uniqueCatalogueReading (glyph : Glyph) (cues : List ContextCue)
    : Option OperatorReading :=
  if cues.isEmpty then none
  else
    let rs := contextualReadings glyph cues
    let cats := rs.filter (fun r => r.status = .catalogue ∧ r.operator?.isSome)
    match cats with
    | [r] => some r
    | _   => none

/-- Cue-aware 单 token resolver。优先级:
    appMarker 关闭后改走 cue 路径 → bool 常值 → hex 常值 → cue-唯一 catalogue
    → 默认 stdlib map → 错误.

    与 `resolveOne` 并存：appMarker 路径仍保留作 fallback，但若 cue 路径
    给出唯一 catalogue reading（如「之」在 betweenNominals 下→ S_1），
    则采用之；其余情形回到 surface map. -/
def resolveOneWithCues (toks : List GlyphTok) (i : Nat) (t : GlyphTok)
    : Except ResolveErr ResolvedTok :=
  match resolveBoolConst t.surface with
  | some b => .ok ⟨t, .boolConst b⟩
  | none =>
    match resolveHexConst t.surface with
    | some h => .ok ⟨t, .hexConst h⟩
    | none =>
      let cues := computeCues toks i
      match uniqueCatalogueReading t.surface cues with
      | some r => .ok ⟨t, .catalogueOp r⟩
      | none =>
        -- cue 路径无唯一答；回 surface map / appMarker
        if isApplicationMarker t.surface then
          .ok ⟨t, .appMarker⟩
        else
          match resolveStdlibOp t.surface with
          | some r => .ok ⟨t, .catalogueOp r⟩
          | none   => .error (.noReading t.surface t.startCol)

/-- 全 token 列表 cue-aware resolver。结构递归 on index. -/
def resolveWithCuesAux (toks : List GlyphTok)
    : Nat → List GlyphTok → Except ResolveErr (List ResolvedTok)
  | _, []       => .ok []
  | i, t :: ts  =>
    match resolveOneWithCues toks i t with
    | .error e => .error e
    | .ok r =>
      match resolveWithCuesAux toks (i + 1) ts with
      | .error e  => .error e
      | .ok rs    => .ok (r :: rs)

/-- 顶层 cue-aware resolver：对 GlyphTok 流做 cue 计算 + 消歧.
    与 `resolveSimple` 同 type，可作 drop-in 替换. -/
def resolveWithCues (toks : List GlyphTok)
    : Except ResolveErr (List ResolvedTok) :=
  resolveWithCuesAux toks 0 toks

/-! ### § 7.1  Cue 计算 sanity 例子 -/

/-- 「推 之 一」之 i=1 (「之」位置) 之 cues = [.betweenNominals]。
    「推」「一」皆 canonicalKind = .glyph (非 .operator/.particle/.modal). -/
example :
    computeCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩] 1
      = [ContextCue.betweenNominals] :=
  by native_decide

/-- i=0 (无左邻居) → 空 cues. -/
example :
    computeCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩] 0
      = ([] : List ContextCue) :=
  by native_decide

/-- 末位 (无右邻居) → 空 cues. -/
example :
    computeCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩] 2
      = ([] : List ContextCue) :=
  by native_decide

/-! ### § 7.2  uniqueCatalogueReading sanity -/

/-- 「之」在 betweenNominals 上下文 → 唯一 catalogue (S_1 属格). -/
example :
    (uniqueCatalogueReading "之" [.betweenNominals]).map (·.operator?)
      = some (some OperatorId.S_1) :=
  by native_decide

/-- 「之」无 cue → 多 reading，非唯一 catalogue（4 readings, 仅 1 catalogue
    但 isApplicationMarker 路径会 fallback；这里测的是 cue 路径本身）. -/
example : uniqueCatalogueReading "之" [] = none := by native_decide

/-- 「推」在任意 cue 下不在 cue 表（无对应 readings）→ none. -/
example : uniqueCatalogueReading "推" [.betweenNominals] = none := by native_decide

/-! ### § 7.3  resolveWithCues 端到端 -/

/-- Helper：从 cue-aware resolve 抽 OperatorId 序列. -/
private def opIdsOfCues (toks : List GlyphTok) : Option (List (Option OperatorId)) :=
  (resolveWithCues toks).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?))

/-- 「推 之 一」走 cue 路径 → [T_10, S_1, none]。注意此处「之」拿到 S_1
    catalogue reading（与 v1 noop appMarker 不同；elab 阶段 S_1 暂未支持，
    属本子任务范围外）. -/
example :
    opIdsOfCues
      [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩]
      = some [some OperatorId.T_10, some OperatorId.S_1, none] :=
  by native_decide

/-- resolveWithCues 在「推 之 一」上 success（.toOption.isSome = true）. -/
example :
    (resolveWithCues
        [⟨"推", 0, 1, false⟩, ⟨"之", 2, 1, false⟩, ⟨"一", 4, 1, false⟩]).toOption.isSome
      = true :=
  by native_decide

/-- 「之」单独（无邻居）走 fallback → appMarker，与 resolveSimple 一致. -/
example :
    ((resolveWithCues [⟨"之", 0, 1, false⟩]).toOption.map
       (fun rs => rs.map (·.atom |> ResolvedAtom.isAppMarker)))
      = some [true] :=
  by native_decide

/-- 「推 一」无「之」，与 resolveSimple 完全等价（atom 序列）. -/
example :
    opIdsOfCues [⟨"推", 0, 1, false⟩, ⟨"一", 2, 1, false⟩]
      = some [some OperatorId.T_10, none] :=
  by native_decide

/-! ### § 7.4  Cue → unique catalogue 桥定理

  和 OperatorReadings.zhi_between_nominals_unique（line 749-751）对齐:
  在 betweenNominals 上下文中，「之」唯一对应 S_1 catalogue reading. -/

/-- 在 betweenNominals 上下文，uniqueCatalogueReading 之 operator? 唯一为 S_1. -/
theorem zhi_between_nominals_unique_catalogue :
    (uniqueCatalogueReading "之" [.betweenNominals]).bind (·.operator?)
      = some OperatorId.S_1 :=
  by native_decide

/-- 在 afterVerb 上下文，「之」之 contextualReadings 唯一（zhi_after_verb_unique
    桥），但该读法 status = .contextual ∧ operator? = none —— 故
    uniqueCatalogueReading 返 none（catalogue gate 不通）. -/
theorem zhi_after_verb_no_catalogue :
    uniqueCatalogueReading "之" [.afterVerb] = none :=
  by native_decide

/-- 在 cue-空 上下文，「之」非 cue-唯一. -/
theorem zhi_no_cue_no_unique_catalogue :
    uniqueCatalogueReading "之" [] = none :=
  by native_decide

/-! ### § 7.5  resolveWithCues 不破坏现有路径

  对不包含「之」的 stdlib token 流，cue 路径与 surface 路径一致 —— 这
  通过 atom 序列对比见证. -/

/-- 6 stdlib 算子 + 「一」的 atom 序列同 resolveSimple. -/
example :
    ((resolveWithCues
        [⟨"推", 0, 1, false⟩, ⟨"比", 2, 1, false⟩, ⟨"不", 4, 1, false⟩,
         ⟨"必", 6, 1, false⟩, ⟨"同", 8, 1, false⟩, ⟨"凡", 10, 1, false⟩,
         ⟨"一", 12, 1, false⟩]).toOption.map (fun rs => rs.map (·.atom |> ResolvedAtom.opId?)))
      = some [some OperatorId.T_10, some OperatorId.R_8, some OperatorId.N_1,
              some OperatorId.M_1,  some OperatorId.I_1, some OperatorId.Q_1,
              none] :=
  by native_decide

end SSBX.Foundation.Wen.WenSurface
