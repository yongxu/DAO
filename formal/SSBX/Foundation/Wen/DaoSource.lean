/-
# DaoSource — «道源»: 完全自指之道

  Path 丙 § 收口篇。前已有 «微核源» 之 PoC（"展练十二字"），
  本篇立 «道源» — 一段「展练一段道」之文：
    其形遍十二字，其义即 是道非道判（中爻同则天道）。

  五相俱（与 «微核源» 同形式力，但语义负载升一级）：

    形 — «判型良 道程 = true»                                (native_decide)
    解 — «解程 道源 = some 道程»                            (native_decide)
    印 — «印程 道程 = 道源»                                 (native_decide)
    执 — ∀ h, runFuel 64 from init h halts                   (穷举 native_decide)
    义 — ∀ h, 末态.cur.2 = 已 ↔ h.y3 = h.y4                  (穷举 native_decide)

  另：
    · «道程_eq_daoJudge» — 与 BaguaTuring.daoJudge 之 末态 同 (锚于核层)
    · «道源_文核同源» — «验程» = `runFuel ∘ init` 之 reflective 同体 (rfl)

  与 «微核源» 之分：
    «微核源» — 形/数/解/执 四相俱，义即 "此程能运行"
    «道源» — 形/解/印/执/义 五相俱，义即 "是道非道之判"

## 道源之结构

```
  pc  wenyan          YiInstr                 道之相
  ──  ──────────────  ──────────────────────  ───────────────
   0  推              push                    太极 (留初象于带)
   1  错              complement                     阴阳生
   2  错              complement                     返本 (complement² = id)
   3  综              reverse                    反观
   4  综              reverse                    还本 (reverse² = id)
   5  互              interlace                      中之四象
   6  取              pop                     返于初 (history → cur)
   7  设时 今         setShi jin              立今
   8  比时 未 至 十   branchShiEq wei 10      若已未则跳 (false)
   9  比爻 三爻 四爻 至 十二                  中爻同则天道
  10  设时 未         setShi wei              心道 fall-through
  11  跳 至 十四      jump 14                 绕过天道
  12  设时 已         setShi ji               天道
  13  翻爻 初爻       flipYao 0               动初爻
  14  不动            nop                     无为
  15  终              halt                    终
```

  pc 1..4 之净效应为 id（complement² = reverse² = id）；
  pc 5 之 interlace 改变中爻位但 pc 6 之 pop 从 history 取回初象，
  故 pc 7 之状态恒为 (h, jin)；其后中爻同 ↔ 天道。

## 状态

  0 sorry / 0 axiom; 一切见证由 `native_decide` + 穷举 case 收尾。
-/
import SSBX.Foundation.Bagua.BaguaTuring
import SSBX.Foundation.Bagua.BaguaWenSpec
import SSBX.Foundation.Wen.WenyanParser
import SSBX.Foundation.Wen.WenyanReflect

namespace SSBX.Foundation.Wen.DaoSource

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanParser
open SSBX.Foundation.Wen.WenyanReflect

/-! ## § 0  «道源» — 文之源（受控文言之 16 命） -/

/-- «道源»：是道非道判 之 文言形式。16 命，遍十二字。 -/
def «道源» : String :=
  "«推»；«错»；«错»；«综»；«综»；«互»；«取»；" ++
  "«设时» «今»；«比时» «未» «至» «十»；" ++
  "«比爻» «三爻» «四爻» «至» «十二»；" ++
  "«设时» «未»；«跳» «至» «十四»；" ++
  "«设时» «已»；«翻爻» «初爻»；«不动»；«终»"

/-! ## § 1  «道程» — 文之形（List YiInstr） -/

/-- «道程»：«道源» 所对应之 YiInstr 程，16 条指令. -/
def «道程» : List YiInstr :=
  [ YiInstr.push                                            -- pc 0  推 · 太极
  , YiInstr.complement                                             -- pc 1  错 · 阴阳
  , YiInstr.complement                                             -- pc 2  错 · 返
  , YiInstr.reverse                                            -- pc 3  综 · 反观
  , YiInstr.reverse                                            -- pc 4  综 · 还
  , YiInstr.interlace                                              -- pc 5  互 · 中
  , YiInstr.pop                                             -- pc 6  取 · 返初
  , YiInstr.setShi Shi.jin                                  -- pc 7  设时 今
  , YiInstr.branchShiEq Shi.wei 10                          -- pc 8  比时 未
  , YiInstr.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ 12      -- pc 9  比爻 三 四
  , YiInstr.setShi Shi.wei                                  -- pc 10 心道
  , YiInstr.jump 14                                         -- pc 11 跳
  , YiInstr.setShi Shi.ji                                   -- pc 12 天道
  , YiInstr.flipYao ⟨0, by omega⟩                           -- pc 13 翻 初爻
  , YiInstr.nop                                             -- pc 14 不动
  , YiInstr.halt                                            -- pc 15 终
  ]

theorem «道程_length» : «道程».length = 16 := by native_decide

/-! ## § 2  形之自指 — 合度 -/

/-- «道程» 全程合度（target ∈ 1..64）。 -/
theorem «道程_形» : «判型良» «道程» = true := by native_decide

/-! ## § 3  解之自指 — 文 → 程 -/

/-- «解程» 「道源」所得 = «道程»；文之解还原文之形。 -/
theorem «道源_解» : «解程» «道源» = some «道程» := by native_decide

/-! ## § 4  印之自指 — 程 → 文 -/

/-- «印程» 「道程」所印 = «道源»；文之印还原文之源。 -/
theorem «道程_印» : «印程» «道程» = «道源» := by native_decide

/-- 解-印 fixpoint：源 →解→ 程 →印→ 自身。 -/
theorem «道之解印_fixpoint» :
    («解程» «道源»).map «印程» = some «道源» := by native_decide

/-! ## § 5  执之自指 — runFuel 收敛于 halted

  对全 64 卦穷举：以任卦为初象，跑 64 步皆 halt。
  实测 16 步内即可 halt（程长 16），fuel 64 充裕。 -/

/-- 任 hexagram 始，64 步内必 halt。 -/
theorem «道程_执» :
    ∀ h : Hexagram, ((YiState.init h «道程»).runFuel 64).halted = true := by
  intro h
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-! ## § 6  义之自指 — 末态时 ↔ 中爻同

  「中爻同 ↔ 天道」是 daoJudge 之命题内容；
  «道程» 在更长之文言流之上，给出同一命题之扩张表达。
-/

/-- «道程» 之义：末态.cur.2 = 已 ↔ h.y3 = h.y4 (= h.isTian之结构核). -/
theorem «道程_义» :
    ∀ h : Hexagram,
      ((YiState.init h «道程»).runFuel 64).cur.2 = Shi.ji ↔ h.y3 = h.y4 := by
  intro h
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-- «道程» 之 末态时 与 daoJudge h 同体（锚于 BaguaTuring 之核层判）。 -/
theorem «道程_eq_daoJudge» :
    ∀ h : Hexagram, ((YiState.init h «道程»).runFuel 64).cur.2 = daoJudge h := by
  intro h
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-! ## § 7  «文核同源» — 反射层之恒等

  «验程» (文层之 runFuel 别名) 与 `runFuel ∘ init` (核层) 字面同体；
  此即 WenyanReflect 之 «文核同源» 在 «道程» 上之 reification。 -/

theorem «道源_文核同源» (h : Hexagram) :
    «验程» «道程» h 64 = (YiState.init h «道程»).runFuel 64 :=
  «文核同源» «道程» h 64

/-! ## § 8  Sanity 见证 — 三卦之具体末态

  乾 (天天) 与 坤 (地地) 皆 中爻同 → 已 (天道)；
  否 (天地否)：y3=阴, y4=阳, 不同 → 未 (心道)。 -/

theorem «道源_乾_天道» :
    ((YiState.init Hexagram.heaven «道程»).runFuel 64).cur.2 = Shi.ji := by
  native_decide

theorem «道源_坤_天道» :
    ((YiState.init Hexagram.earth «道程»).runFuel 64).cur.2 = Shi.ji := by
  native_decide

/-- 否 = 天地否 = ⟨阴,阴,阴,阳,阳,阳⟩. -/
def «否» : Hexagram := ⟨.yin, .yin, .yin, .yang, .yang, .yang⟩

theorem «道源_否_心道» :
    ((YiState.init «否» «道程»).runFuel 64).cur.2 = Shi.wei := by
  native_decide

/-! ## § 9  «道之自指» — 五相俱之主公示

  此即 path 丙 之收口：«道源» 在 形 / 解 / 印 / 执 / 义 五相俱足。

  ╔══════════════════════════════════════════════════════════════════╗
  ║                                                                  ║
  ║    形  «判型良 道程 = true»                                     ║
  ║         · 16 条指令全合度，target ∈ 1..64                        ║
  ║                                                                  ║
  ║    解  «解程 道源 = some 道程»                                  ║
  ║         · 受控文言之 16 命 解析回 List YiInstr                   ║
  ║                                                                  ║
  ║    印  «印程 道程 = 道源»                                       ║
  ║         · 程印回文，与源逐字符同                                 ║
  ║                                                                  ║
  ║    执  ∀ h, runFuel 64 halts                                     ║
  ║         · 任卦为初象皆收敛于 halted                              ║
  ║                                                                  ║
  ║    义  ∀ h, .cur.2 = 已 ↔ h.y3 = h.y4                            ║
  ║         · 末态时 = 已（天道）当且仅当中爻同                      ║
  ║         · 等价于 daoJudge h（«道程_eq_daoJudge»）                ║
  ║                                                                  ║
  ╚══════════════════════════════════════════════════════════════════╝

  与 complement-equivariance ceiling 之关系：
    «道程» 全 complement-等变（每构造子皆 complement-等变），故落在 12-字 ISA 之表达力之内。
    其 义 ↔ 中爻同 — 此性质本身 complement-等变（complement 翻 yang/yin 不改 y3=y4），故合规。
-/

theorem «道之自指» :
    -- 形
    («判型良» «道程» = true) ∧
    -- 解
    («解程» «道源» = some «道程») ∧
    -- 印
    («印程» «道程» = «道源») ∧
    -- 执
    (∀ h : Hexagram, ((YiState.init h «道程»).runFuel 64).halted = true) ∧
    -- 义
    (∀ h : Hexagram,
      ((YiState.init h «道程»).runFuel 64).cur.2 = Shi.ji ↔ h.y3 = h.y4) :=
  ⟨«道程_形», «道源_解», «道程_印», «道程_执», «道程_义»⟩

end SSBX.Foundation.Wen.DaoSource
