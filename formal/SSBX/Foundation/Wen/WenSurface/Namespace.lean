/-
# WenSurface.Namespace — 用 NS_NAME 学派命名空间

Wen 2.0 item ③ (Tier 1, Phase α independent feature).

## 设计

文表层支持「`用 墨经；`」「`用 名家；`」式 namespace 声明语句。声明
*粘附* 后续 statement 直至下一次 `用 ...` 或程序结尾。声明本身不发射
`TypedTm`；它修改 program-level 之 `activeNamespaces` 状态。

* `Namespace.entries` —— 学派 surface → `OperatorGroup` 静态表。
  覆盖现有 OperatorGroup 中 12 个有「派别色彩」的 group：墨经 P / 名家 G /
  法家 L / 医家 Y / 社会秩序 X / 庄子 ZHU / 孙子 SUN / 楚辞 CHU /
  礼记 LIJ / 杂家 ZA / 史官 E / 补遗 Z. 兼收繁简 + 别名。
* `useStmtNamespace?` —— statement-level 检测：chunk = `用 SP* NS_NAME SP*` 时
  抽出 `OperatorGroup`. SP 含 ASCII / ideographic 空白.
* `wenyanCompileProgramWithNamespaces` —— `wenyanCompileProgram` 的 NS-aware
  变体；ouputs `(activeNamespaces 最终, List TypedTm)`. 默认 active 集为空
  时与 1.5 行为一致.

## 范围限制（v1）

本 v1 只实装 NS **声明 + 状态线程**。Resolver 仍按 cue-aware 路径解析；
NS 状态保留为可见 program-level metadata，可由 future filter 路径消费.
这是 task spec 「If blocked: ship namespace declaration syntax only
(no filtering yet)」的策略 — 不冒险破 318+ EndToEndTests，但仍能把
NS 概念在程序中显式声明、用作 audit / scope analysis 之 source of truth.

## 状态

0 sorry / 0 axiom / 总函数. 关键例由 native_decide 见证.
-/
import SSBX.Foundation.Wen.WenSurface.EndToEnd

set_option maxHeartbeats 8000000

namespace SSBX.Foundation.Wen.WenSurface

open SSBX.Text.WenyanOperators

/-! ## § 1  Namespace 表 -/

/-- 学派 surface → OperatorGroup 之静态映射。
    覆盖 OperatorGroup 中有「学派色彩」的 group；通用 group (R/C/T/F/B/Q/K/M/N/I/S/H/A/D)
    暂不归入 namespace（视作语言核心，任何 NS 下都可用）。 -/
def Namespace.entries : List (String × OperatorGroup) :=
  [ -- 墨家 / 墨经 (P)
    ("墨经", .P), ("墨經", .P), ("墨家", .P), ("墨", .P)
    -- 名家 (G)
  , ("名家", .G), ("名学", .G), ("名學", .G)
    -- 法家 (L)
  , ("法家", .L), ("法學", .L), ("法学", .L)
    -- 医家 (Y)
  , ("医家", .Y), ("醫家", .Y), ("中医", .Y), ("中醫", .Y), ("黄帝内经", .Y), ("黃帝內經", .Y)
    -- 庄子 (ZHU)
  , ("庄子", .ZHU), ("莊子", .ZHU), ("齐物", .ZHU), ("齊物", .ZHU)
    -- 孙子 / 兵家 (SUN)
  , ("孙子", .SUN), ("孫子", .SUN), ("兵家", .SUN), ("兵法", .SUN)
    -- 楚辞 (CHU)
  , ("楚辞", .CHU), ("楚辭", .CHU)
    -- 礼记 / 中庸 (LIJ)
  , ("礼记", .LIJ), ("禮記", .LIJ), ("中庸", .LIJ)
    -- 杂家 / 黄老 / 淮南 (ZA)
  , ("杂家", .ZA), ("雜家", .ZA), ("黄老", .ZA), ("黃老", .ZA), ("淮南", .ZA), ("淮南子", .ZA)
    -- 史官 / 春秋 (E)
  , ("史官", .E), ("春秋", .E)
    -- 社会秩序 / 荀子 (X)
  , ("社会", .X), ("社會", .X), ("荀子", .X)
    -- 补遗 (Z)
  , ("补遗", .Z), ("補遺", .Z) ]

/-- 学派 surface → `OperatorGroup`. -/
def Namespace.lookup? (name : String) : Option OperatorGroup :=
  let rec go : List (String × OperatorGroup) → Option OperatorGroup
    | [] => none
    | (k, v) :: rest => if k = name then some v else go rest
  go Namespace.entries

/-- 所有已知 namespace surface（用作 audit / list）。 -/
def Namespace.allNames : List String :=
  Namespace.entries.map Prod.fst

/-- 所有 namespace 之 OperatorGroup（可有重复，对应多别名）. -/
def Namespace.allGroups : List OperatorGroup :=
  Namespace.entries.map Prod.snd

/-! ## § 2  用 NS_NAME 语句检测 -/

/-- 一字符判定：ASCII space / tab / newline / CR / ideographic space (U+3000). -/
private def isNamespaceSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '　'

/-- 去字符串两端的 namespace-空白. 总函数（结构递归 on List Char）. -/
private def trimNamespaceSpaces (s : String) : String :=
  let cs := s.toList
  let dropLead := cs.dropWhile isNamespaceSpace
  let revCs := dropLead.reverse
  let dropTrail := revCs.dropWhile isNamespaceSpace
  String.mk dropTrail.reverse

/-- 一个 chunk 是 `用 SP* NS_NAME SP*` 声明，则返回对应 `OperatorGroup`. -/
def useStmtNamespace? (chunk : String) : Option OperatorGroup :=
  let trimmed := trimNamespaceSpaces chunk
  let cs := trimmed.toList
  match cs with
  | '用' :: rest =>
    -- 第二字必须为 空白 或 chunk 至此就是孤立「用」（孤立用作 H_8）
    match rest with
    | [] => none -- 孤立 「用」 → 不是 NS 声明，让正常 pipeline 处理
    | c :: _ =>
      if isNamespaceSpace c then
        let nsName := trimNamespaceSpaces (String.mk rest)
        Namespace.lookup? nsName
      else
        -- 如「用乾」黏字情况不视作 NS 声明
        none
  | _ => none

/-! ## § 3  Program-level Namespace 状态线程 -/

/-- Program-level statement 之分类。 -/
inductive ProgramStmt where
  | useDecl (group : OperatorGroup) (chunk : String)
  | code    (typed : TypedTm) (chunk : String)
deriving Repr

/-- `wenyanCompileProgram` 之 NS-aware 错误。要么是 `用 X` 中 X 是未知 NS_NAME，
    要么是 code chunk 编译失败. -/
inductive ProgramNsErr where
  | unknownNamespace (index : Nat) (name : String)
  | compile (index : Nat) (err : WenSurfaceErr)
deriving Repr

/-- NS-aware program 编译产物。包含 active 集合最终状态 + 已编译的 typed tm
    序列 (use-decl 不进 tm 序列，仅在 stmts 中保留 audit 记录). -/
structure ProgramNsResult where
  activeNamespaces : List OperatorGroup
  stmts            : List ProgramStmt
  typedTms         : List TypedTm
deriving Repr

/-- Helper: chunk 是否 *看起来* 想做 NS 声明（以「用 SP*」开头）. -/
private def looksLikeUseDecl (trimmed : String) : Bool :=
  let cs := trimmed.toList
  match cs with
  | '用' :: c :: _ => isNamespaceSpace c
  | _ => false

/-- 单步：处理一个 chunk，结合当前 active 集. -/
def stepProgramNs (i : Nat) (active : List OperatorGroup) (stmts : List ProgramStmt)
    (typedTms : List TypedTm) (chunk : String)
    : Except ProgramNsErr (Nat × List OperatorGroup × List ProgramStmt × List TypedTm) :=
  match useStmtNamespace? chunk with
  | some g =>
    -- 视为 NS 声明：将 g 加入 active（已在则 dedup）
    let active' := if active.contains g then active else active ++ [g]
    let stmts'  := stmts ++ [.useDecl g chunk]
    .ok (i + 1, active', stmts', typedTms)
  | none =>
    let trimmed := trimNamespaceSpaces chunk
    if looksLikeUseDecl trimmed then
      -- 「用 X」 X ≠ 已知 NS → unknownNamespace
      let rest := trimNamespaceSpaces (trimmed.drop 1).toString
      .error (.unknownNamespace i rest)
    else
      match wenyanCompile chunk with
      | .ok t    => .ok (i + 1, active, stmts ++ [.code t chunk], typedTms ++ [t])
      | .error e => .error (.compile i e)

/-- 多语句 NS-aware program 编译：threads `activeNamespaces` state. -/
def wenyanCompileProgramWithNamespaces (s : String)
    : Except ProgramNsErr ProgramNsResult :=
  let chunks := splitOnStatementSep s
  let init : Nat × List OperatorGroup × List ProgramStmt × List TypedTm :=
    (0, [], [], [])
  let step :
      (Nat × List OperatorGroup × List ProgramStmt × List TypedTm) → String →
        Except ProgramNsErr (Nat × List OperatorGroup × List ProgramStmt × List TypedTm)
    | (i, active, stmts, typedTms), chunk =>
      stepProgramNs i active stmts typedTms chunk
  match chunks.foldlM (init := init) step with
  | .ok (_, active, stmts, typedTms) =>
    .ok ⟨active, stmts, typedTms⟩
  | .error e => .error e

/-! ## § 4  Helpers for downstream consumers -/

/-- OperatorId 是否落入 active namespace 集合（空集合 = 任意）. -/
def OperatorId.inActiveNamespaces (id : OperatorId) (active : List OperatorGroup) : Bool :=
  active.isEmpty || active.contains id.group

/-! ## § 5  Sanity 例子 (native_decide) -/

example : Namespace.lookup? "墨经" = some .P := by native_decide
example : Namespace.lookup? "名家" = some .G := by native_decide
example : Namespace.lookup? "法家" = some .L := by native_decide
example : Namespace.lookup? "庄子" = some .ZHU := by native_decide
example : Namespace.lookup? "孙子" = some .SUN := by native_decide
example : Namespace.lookup? "兵家" = some .SUN := by native_decide
example : Namespace.lookup? "未知学派" = none := by native_decide
example : Namespace.lookup? "" = none := by native_decide

/-- 别名等价：墨经 / 墨經 / 墨家 / 墨 全归 .P. -/
example :
    [Namespace.lookup? "墨经", Namespace.lookup? "墨經",
     Namespace.lookup? "墨家", Namespace.lookup? "墨"]
      = [some .P, some .P, some .P, some .P] :=
  by native_decide

example : useStmtNamespace? "用 墨经" = some .P := by native_decide
example : useStmtNamespace? "用 名家" = some .G := by native_decide
example : useStmtNamespace? "用 法家" = some .L := by native_decide
example : useStmtNamespace? "  用  墨经  " = some .P := by native_decide
example : useStmtNamespace? "用 未知" = none := by native_decide
example : useStmtNamespace? "用乾" = none := by native_decide
example : useStmtNamespace? "推 一" = none := by native_decide
example : useStmtNamespace? "" = none := by native_decide
/-- 孤立「用」不视作 NS 声明（fallthrough 到 H_8 编译）. -/
example : useStmtNamespace? "用" = none := by native_decide

/-! ### Namespace 表覆盖性断言 -/

theorem namespace_entries_count :
    Namespace.entries.length = 42 := by native_decide

theorem namespace_groups_distinct_count :
    (Namespace.allGroups.foldl
      (fun acc g => if acc.contains g then acc else acc ++ [g]) ([] : List OperatorGroup)).length
      = 12 := by
  native_decide

/-- 覆盖之 OperatorGroup 集合：P G L Y ZHU SUN CHU LIJ ZA E X Z (12 个). -/
theorem namespace_groups_set :
    Namespace.allGroups.foldl
      (fun acc g => if acc.contains g then acc else acc ++ [g]) ([] : List OperatorGroup)
      = [.P, .G, .L, .Y, .ZHU, .SUN, .CHU, .LIJ, .ZA, .E, .X, .Z] := by
  native_decide

/-! ### Program-level NS-aware 编译 -/

/-- 默认（无 `用` 声明） 行为与 1.5 一致：active 集为空 + tm 序列对齐. -/
example :
    (wenyanCompileProgramWithNamespaces "推 一").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length))
      = some ([], 1) :=
  by native_decide

/-- 单纯 NS 声明：active 集生长，无 typedTm. -/
example :
    (wenyanCompileProgramWithNamespaces "用 墨经").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length))
      = some ([.P], 0) :=
  by native_decide

/-- NS 声明 + 一条 code：active 集生长，typedTm 1 个. -/
example :
    (wenyanCompileProgramWithNamespaces "用 墨经；推 一").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length))
      = some ([.P], 1) :=
  by native_decide

/-- 多 NS 声明：active 集累加，dedup. -/
example :
    (wenyanCompileProgramWithNamespaces "用 墨经；用 名家；用 墨经；推 一").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length))
      = some ([.P, .G], 1) :=
  by native_decide

/-- 默认（无任何 `用`）→ active=[], 行为 = 1.5；3 句 hex 程序长度 3. -/
example :
    (wenyanCompileProgramWithNamespaces "推 一；推 推 一；推 推 推 一").toOption.map
        (fun r => (r.activeNamespaces, r.typedTms.length))
      = some ([], 3) :=
  by native_decide

/-- 未知 NS_NAME → unknownNamespace 错误（带 index）. -/
example :
    (match wenyanCompileProgramWithNamespaces "推 一；用 不存在派" with
     | .error (.unknownNamespace i name) => decide (i = 1) && decide (name = "不存在派")
     | _ => false) = true :=
  by native_decide

/-- code 编译错误时返 .compile + index. -/
example :
    (match wenyanCompileProgramWithNamespaces "用 墨经；XYZ不存在" with
     | .error (.compile i _) => decide (i = 1)
     | _ => false) = true :=
  by native_decide

/-- 第一个 NS 声明 + 第二个 NS 声明：active = [P, G] (顺序保留). -/
example :
    (wenyanCompileProgramWithNamespaces "用 墨经；用 名家").toOption.map (·.activeNamespaces)
      = some [.P, .G] :=
  by native_decide

/-- 同 NS 重复声明 → dedup. -/
example :
    (wenyanCompileProgramWithNamespaces "用 墨经；用 墨经").toOption.map (·.activeNamespaces)
      = some [.P] :=
  by native_decide

/-- stmts 内部计数：1 NS decl + 1 code = 2 项. -/
example :
    (wenyanCompileProgramWithNamespaces "用 墨经；推 一").toOption.map (·.stmts.length)
      = some 2 :=
  by native_decide

/-- 空程序 → active=[], 无 stmts. -/
example :
    (wenyanCompileProgramWithNamespaces "").toOption.map
        (fun r => (r.activeNamespaces, r.stmts.length, r.typedTms.length))
      = some ([], 0, 0) :=
  by native_decide

/-! ### inActiveNamespaces -/

/-- T_10 (group T) 不在 active [.P] 中 → false. -/
example : OperatorId.inActiveNamespaces .T_10 [.P] = false := by native_decide

/-- T_10 在空 active 集中 → true (空 = 不限定). -/
example : OperatorId.inActiveNamespaces .T_10 [] = true := by native_decide

/-- P_1 (墨经群组) 在 active [.P] 中 → true. -/
example : OperatorId.inActiveNamespaces .P_1 [.P] = true := by native_decide

/-- L_10 (法家群组) 在 active [.L, .P] 中 → true. -/
example : OperatorId.inActiveNamespaces .L_10 [.L, .P] = true := by native_decide

end SSBX.Foundation.Wen.WenSurface
