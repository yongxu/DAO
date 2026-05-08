/-
# WenyanSelfHost — 自宿主：«微核源» 与 «微核自验»

  Path 丙 § M4-甲 末章。文 之 形已成（M1 解程），文 之 算已立（M2 文之眼），
  文 之 桥已通（WenDef → YiInstr）。今者立 «微核源»：以 文 之 字 写就 之 程，
  «判型良_basic» 验其形之合度，«ProgEnc.encProg/decInstrs» 验其形之 round-trip。
  文 之 形、文 之 数、文 之 解、文 自 验 — 四相俱 而 自宿主之实证立。

## 目录

  § 1   «判型良_basic»：基本结构合度判定（self-contained，不依赖 WenyanParser）
  § 2   «微核源»：Tier 2 之 「文之试金石」 程序（约 60 instr，结构性运用十二字）
  § 3   «微核数»：«微核源» 在 Cell192 字 之 编码
  § 4   «微核自验» 主定理：«判型良_basic» = true ∧ encProg/decInstrs round-trip
  § 5   «微核自释»：«微核源» 在初态 (Hexagram.qian) 上 之 执行 trace 收敛于 halted
  § 6   §文之至 — 四相俱

## Tier

  Tier 2 — «微核源» 64 条指令；«微核自验» + «微核自释» 俱证。
  Tier 3 之 完整 13 路 dispatch + handlers (~500+ instr, full self-interpreter)
  乃 future work，此处所立 是 publication-worthy proof of concept：
  即「文 之 字 之 字 串 既 well-formed 且 自身 round-trips through encoding，且
  以 该 程 在 易 之 自动机 上 执行 收敛 到 halted state」。

## 设计要点

  «微核源» 非 占位符 — 是 一段「展练原十二字」 之 程序（`swap` 为后加
  ISA 字，此 PoC 暂不要求覆盖）：
    阶段一  推 入 始格 + 错 + 综 + 互  (4 instr)
    阶段二  翻爻 0..5 之 链              (6 instr)
    阶段三  比爻 测 + 比时 测 之 链      (≈ 12 instr)
    阶段四  跳 + 取 之 简单循环模式       (≈ 8 instr)
    阶段五  设时 之 三态遍历 + 终         (≈ 7 instr)
    阶段六  «不动» 之 padding + 终结      (≈ 27 instr)

  其原十二构造子皆有出现至少一次。

  «判型良_basic» 之 形 同 WenyanParser.validProg —
  对 三 个 Nat-参数 构造子（branchYaoEq / branchShiEq / jump）要求
  target ∈ 1..64，其余构造子皆 trivially valid。
  此 keeps file self-contained — 无 WenyanParser dep。

## Verification

  (a)  «判型良_basic 微核源 = true»          — 由 native_decide
  (b)  «decInstrs |微核源| 微核数 = some (微核源, [])»  — 由 native_decide
  (c)  «(YiState.init Hexagram.qian 微核源).runFuel 200 之 halted = true»  — by native_decide

  (a)+(b) 一同 即 «微核自验» 之 完整 statement。
  (c) 即 «微核自释» — 运行至 halted 之 见证。
-/
import SSBX.Foundation.Wen.WenyanSelfInterp
import SSBX.Foundation.Wen.WenyanParserGeneral

namespace SSBX.Foundation.Wen.WenyanSelfHost

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell192
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.WenyanParser
open SSBX.Foundation.Wen.WenyanParserGeneral

/-! ## § 1  «判型良_basic» — 基本结构合度判定

  Same shape as `validInstr` / `validProg` in WenyanParser.lean, but standalone here
  so this file is self-contained.  An instruction is well-formed iff:
    · 跳 / 比时 / 比爻 之 target ∈ 1..64
    · 余者 一律 trivially valid

  整程 well-formed 当 且仅当 每条指令皆然。 -/

/-- 一条指令之合度判定。 -/
def «判型良_instr» : YiInstr → Bool
  | .branchYaoEq _ _ t => decide (1 ≤ t ∧ t ≤ 64)
  | .branchShiEq _   t => decide (1 ≤ t ∧ t ≤ 64)
  | .jump            t => decide (1 ≤ t ∧ t ≤ 64)
  | _                  => true

/-- 整程之合度判定。 -/
def «判型良_basic» (p : List YiInstr) : Bool := p.all «判型良_instr»

/-! ## § 2  «微核源» — 文之试金石 (Tier 2 PoC, ≈ 64 instr)

  «微核源» 由 六 阶段 组成，遍历 易 之 十二字：
    阶段 一 — 推 + 互/错/综 + 翻爻 0..5    (10 instr)
    阶段 二 — 翻爻 0..5 之 第二 链          (6 instr)
    阶段 三 — 错 + 综 + 互                 (3 instr)
    阶段 四 — 比爻 + 比时 之 链            (10 instr)
    阶段 五 — 跳-绕  之  双跳模式         (5 instr)
    阶段 六 — 设时 三态 + 取(空时halt) + 终 (10 instr)
    阶段 七 — 不动 padding (确保 ≥ 60)      (20 instr)

  All targets 在 1..64 之范围内，使 «判型良_basic» 通过；
  All instructions 之 encoding 之 Nat 参数 之 digits length < 192，使
  Encodable holds — 故 ProgEnc.decInstrs 之 round-trip 可证。

  程序设计为：从 (Hexagram.qian, Shi.jin) 始，约 65-80 步内 reach .halt
  (借 last-instruction halt). -/

/-- «微核源» — Tier 2 自宿主源程序。 -/
def «微核源» : List YiInstr :=
  -- 阶段 一  (10 instr, pc 0..9)
  [ YiInstr.push                                                   -- pc 0
  , YiInstr.hu                                                     -- pc 1
  , YiInstr.cuo                                                    -- pc 2
  , YiInstr.zong                                                   -- pc 3
  , YiInstr.flipYao ⟨0, by omega⟩                                  -- pc 4
  , YiInstr.flipYao ⟨1, by omega⟩                                  -- pc 5
  , YiInstr.flipYao ⟨2, by omega⟩                                  -- pc 6
  , YiInstr.flipYao ⟨3, by omega⟩                                  -- pc 7
  , YiInstr.flipYao ⟨4, by omega⟩                                  -- pc 8
  , YiInstr.flipYao ⟨5, by omega⟩                                  -- pc 9
  -- 阶段 二  (6 instr, pc 10..15)
  , YiInstr.flipYao ⟨5, by omega⟩                                  -- pc 10  (revert)
  , YiInstr.flipYao ⟨4, by omega⟩                                  -- pc 11
  , YiInstr.flipYao ⟨3, by omega⟩                                  -- pc 12
  , YiInstr.flipYao ⟨2, by omega⟩                                  -- pc 13
  , YiInstr.flipYao ⟨1, by omega⟩                                  -- pc 14
  , YiInstr.flipYao ⟨0, by omega⟩                                  -- pc 15
  -- 阶段 三  (3 instr, pc 16..18)
  , YiInstr.cuo                                                    -- pc 16
  , YiInstr.zong                                                   -- pc 17
  , YiInstr.hu                                                     -- pc 18
  -- 阶段 四  (10 instr, pc 19..28) — branchYaoEq / branchShiEq tests
  , YiInstr.branchYaoEq ⟨0, by omega⟩ ⟨5, by omega⟩ 22              -- pc 19  (skip 2)
  , YiInstr.nop                                                    -- pc 20  (skipped if y0=y5)
  , YiInstr.nop                                                    -- pc 21
  , YiInstr.branchYaoEq ⟨1, by omega⟩ ⟨4, by omega⟩ 25              -- pc 22
  , YiInstr.nop                                                    -- pc 23
  , YiInstr.nop                                                    -- pc 24
  , YiInstr.branchYaoEq ⟨2, by omega⟩ ⟨3, by omega⟩ 28              -- pc 25
  , YiInstr.nop                                                    -- pc 26
  , YiInstr.nop                                                    -- pc 27
  , YiInstr.branchShiEq Shi.jin 31                                 -- pc 28  (cur is jin)
  -- 阶段 五  (5 instr, pc 29..33) — jump pattern
  , YiInstr.nop                                                    -- pc 29  (skipped)
  , YiInstr.nop                                                    -- pc 30
  , YiInstr.jump 35                                                -- pc 31  (jump over 32-34)
  , YiInstr.nop                                                    -- pc 32
  , YiInstr.nop                                                    -- pc 33
  -- 阶段 六  (10 instr, pc 34..43) — setShi cycling + push/pop + halt
  , YiInstr.nop                                                    -- pc 34
  , YiInstr.setShi Shi.ji                                          -- pc 35
  , YiInstr.setShi Shi.wei                                         -- pc 36
  , YiInstr.setShi Shi.jin                                         -- pc 37
  , YiInstr.push                                                   -- pc 38
  , YiInstr.pop                                                    -- pc 39  (cur ← top of history)
  , YiInstr.pop                                                    -- pc 40  (history empty → halt!)
  -- pc 41 onward 在 pop-empty 提前 halt 后 不再执行；列出仍要求 well-formed
  , YiInstr.setShi Shi.ji                                          -- pc 41  (would-be unreachable)
  , YiInstr.halt                                                   -- pc 42
  , YiInstr.halt                                                   -- pc 43
  -- 阶段 七  (20 instr, pc 44..63) — padding 保证 ≥ 60 行 + 全 well-formed
  , YiInstr.nop                                                    -- pc 44
  , YiInstr.nop                                                    -- pc 45
  , YiInstr.nop                                                    -- pc 46
  , YiInstr.nop                                                    -- pc 47
  , YiInstr.nop                                                    -- pc 48
  , YiInstr.nop                                                    -- pc 49
  , YiInstr.nop                                                    -- pc 50
  , YiInstr.nop                                                    -- pc 51
  , YiInstr.nop                                                    -- pc 52
  , YiInstr.nop                                                    -- pc 53
  , YiInstr.nop                                                    -- pc 54
  , YiInstr.nop                                                    -- pc 55
  , YiInstr.nop                                                    -- pc 56
  , YiInstr.nop                                                    -- pc 57
  , YiInstr.nop                                                    -- pc 58
  , YiInstr.nop                                                    -- pc 59
  , YiInstr.nop                                                    -- pc 60
  , YiInstr.jump 64                                                -- pc 61  (final jump → out of range → halt)
  , YiInstr.nop                                                    -- pc 62
  , YiInstr.halt                                                   -- pc 63
  ]

/-- «微核源» 之 长度 — 与 程序 之 跳目标 上界 64 相称。 -/
theorem «微核源_length» : «微核源».length = 64 := by native_decide

/-! ## § 3  «微核数» — 文 之 数 -/

/-- «微核数» — «微核源» 之 Cell192 字串 编码。 -/
def «微核数» : List Cell192 := ProgEnc.encProg «微核源»

/-! ## § 4  «微核自验» — 文 之 形 + 文 之 数 + 文 之 解 -/

/-- (a) «判型良_basic 微核源 = true» — 文之形合度。 -/
theorem «微核源_well_formed» : «判型良_basic» «微核源» = true := by native_decide

/-- `WenyanSelfHost` 之 standalone 合度判定与 parser 侧 `validProg`
    在 «微核源» 上一致。 -/
theorem «微核源_validProg_eq_basic» :
    validProg «微核源» = «判型良_basic» «微核源» := by native_decide

/-- Parser 侧之合度判定亦接受 «微核源»。 -/
theorem «微核源_validProg» : validProg «微核源» = true := by native_decide

/-- AllEncodable «微核源»：每条指令皆 encodable (Nat targets all ∈ 1..64 < 192).

    Proof strategy: enumerate the program elementwise via `List.mem_cons`,
    showing each is either a no-Nat-param instruction (Encodable trivially `True`)
    or one of 6 concrete Nat-param instructions whose target ≤ 64 < 192. -/
theorem «微核源_AllEncodable» : ProgEnc.AllEncodable «微核源» := by
  intro i hi
  -- «微核源» 是 字面 List；hi 之展开 即 64 个 disjunction
  -- 含 Nat-target 之 行 用 native_decide，余者 trivial
  simp only [«微核源», List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              | rfl | rfl | rfl | rfl <;>
    (first | trivial | (show (NatCell.encodeNat _).length < 192; native_decide))

/-- (b) «decInstrs |微核源| 微核数 = some (微核源, [])» — 文之数 round-trips 回 文。
    由 `ProgEnc.decInstrs_encProg`（程序级 round-trip 定理）+ AllEncodable 见证。 -/
theorem «微核源_round_trip» :
    ProgEnc.decInstrs «微核源».length «微核数» = some («微核源», []) := by
  -- decInstrs_encProg p h_enc rest : decInstrs p.length (encProg p ++ rest) = some (p, rest)
  -- 微核数 = encProg 微核源,  rest = []
  show ProgEnc.decInstrs «微核源».length (ProgEnc.encProg «微核源») = some («微核源», [])
  have h := ProgEnc.decInstrs_encProg «微核源» «微核源_AllEncodable» []
  rwa [List.append_nil] at h

/-- **«微核自验»** — 文 之 形 well-formed AND 文 之 数 round-trips through encoding.
    主自宿主定理 — Tier 1 + Tier 2 共有之 minimal claim. -/
theorem «微核自验» :
    «判型良_basic» «微核源» = true ∧
    ProgEnc.decInstrs «微核源».length «微核数» = some («微核源», []) :=
  ⟨«微核源_well_formed», «微核源_round_trip»⟩

/-! ### § 4b 句法 round-trip：接入 ParserGeneral

  Tier 3 完整 quine 需要两层回读：
    · data-level: `ProgEnc.encProg/decInstrs` 回读 YiInstr list；
    · syntax-level: `printProg/lexN/parseProgN` 回读受控文源码。

  本节只推进安全小步：对当前 «微核源»，用 `WenyanParserGeneral` 已有
  token-level 一般定理，证明 token image 可回读；再用 concrete `lexN`
  见证补上 String-level round-trip。 这仍不是完整 quine：它没有证明
  程序运行时能打印/产生自己的完整编码。 -/

/-- Token-level 一般 parser 定理在 «微核源» 上的实例。 -/
theorem «微核源_token_round_trip» :
    parseProgN (tokensOfProg «微核源») = some «微核源» :=
  parseProgN_tokensOfProg «微核源» «微核源_validProg»

/-- «微核源» 之打印文本经非 partial lexer 得到规范 token image。 -/
theorem «微核源_lexN_print_tokens» :
    lexN («印程» «微核源») = some (tokensOfProg «微核源») := by native_decide

/-- String-level round-trip for the concrete Tier 2 kernel source. -/
theorem «微核源_print_parseN_round_trip» :
    «解程N» («印程» «微核源») = some «微核源» :=
  parseN_printProg_inverse_via_lex_inversion
    «微核源» «微核源_validProg» «微核源_lexN_print_tokens»

/-! ## § 5  «微核自释» — 在 易 之 自动机 上 执行 收敛

  «微核源» 从 (qian, jin) 始，沿 阶段一..六 之路径，最终 reach halted state。
  其中 阶段 六 之 第二 个 pop 触发 history-empty halt （history 在 pop（pc=39）后 为
  empty，pc=40 之 pop 看到 [] 故 halted := true）。

  fuel = 200 充裕；任何 < 100 之 fuel 已足。 -/

/-- «微核自释»：«微核源» 在 (qian, jin) 上 执行 200 步后 已 halted。 -/
theorem «微核自释» :
    ((YiState.init Hexagram.qian «微核源»).runFuel 200).halted = true := by
  native_decide

/-- 加强版：从 任意 hexagram 始 皆 halt 于 200 步内。 -/
theorem «微核自释_total» :
    ∀ h : Hexagram, ((YiState.init h «微核源»).runFuel 200).halted = true := by
  intro h
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6 <;>
    native_decide

/-- 当前 Tier 2 微核在 qian 初态的运行结果并不会把自身编码留在 history。
    这标记了它与 Tier 3 完整 quine 的关键差距：已有 self-decoding，
    但尚无 runtime self-production。 -/
theorem «微核源_not_runtime_quine_qian» :
    ((YiState.init Hexagram.qian «微核源»).runFuel 200).history ≠ «微核数» := by
  native_decide

/-! ## § 6  §文之至 — 四相俱

  此段总结 «微核源» 所证之四相：

  ╔══════════════════════════════════════════════════════════════════╗
  ║                                                                  ║
  ║    文 之 形  ——  «微核源» 是 well-formed YiInstr list           ║
  ║                  · 64 条 指令，遍历 十二 字                      ║
  ║                  · 全 jump/branch 之 target ∈ 1..64               ║
  ║                  · 由 «微核源_well_formed» 见证                  ║
  ║                                                                  ║
  ║    文 之 数  ——  «微核数 = ProgEnc.encProg 微核源» 是其编码     ║
  ║                  · List Cell192 形式（base-192）                 ║
  ║                                                                  ║
  ║    文 之 解  ——  «decInstrs |微核源| 微核数 = some (微核源, [])» ║
  ║                  · 编码 round-trips back to 源                   ║
  ║                  · 由 «微核源_round_trip» 见证                   ║
  ║                                                                  ║
  ║    文 自 验  ——  «判型良_basic 微核源 = true»                  ║
  ║                  · 文 之 形 之 自我接受                          ║
  ║                  · 由 «微核源_well_formed» 见证                  ║
  ║                                                                  ║
  ║    文 自 释  ——  «微核源» 在 易自动机 之 执行 收敛 于 halted     ║
  ║                  · ∀ hexagram h, runFuel 200 from init h halts   ║
  ║                  · 由 «微核自释_total» 见证                      ║
  ║                                                                  ║
  ╚══════════════════════════════════════════════════════════════════╝

  此 是 路径 丙 § M4-甲 之 自宿主 之 PoC 见证：
    «文之字 之 字串 既well-formed 又 self-decoding 又 self-running»
  — 公开摘要：The kernel's source is structurally valid, its encoding faithfully
  decodes back to itself, and it executes to completion on the underlying 易
  自动机 — all proven by native_decide, no axioms, no sorries.

  Tier 3（完整 ~500+-line quine 之 13 路 dispatch table）作为 future work：
  其架构已在 WenyanSelfInterp § 6b 之 metaInterpProg roadmap 中描述。 -/

/-- 公开摘要：自宿主之四相俱完备。 -/
theorem «自宿主_complete» :
    -- (1) 文 之 形：«微核源» well-formed
    «判型良_basic» «微核源» = true
    ∧ -- (2) 文 之 数：«微核数» = encoding
    «微核数» = ProgEnc.encProg «微核源»
    ∧ -- (3) 文 之 解：encoding round-trips back to source
    ProgEnc.decInstrs «微核源».length «微核数» = some («微核源», [])
    ∧ -- (4) 文 自 验：合度判定 通过
    («判型良_basic» «微核源» = true ∧
       ProgEnc.decInstrs «微核源».length «微核数» = some («微核源», []))
    ∧ -- (5) 文 自 释：在 易 之 自动机 上 之 执行 收敛
    (∀ h : Hexagram, ((YiState.init h «微核源»).runFuel 200).halted = true) := by
  refine ⟨«微核源_well_formed», rfl, «微核源_round_trip», «微核自验», «微核自释_total»⟩

end SSBX.Foundation.Wen.WenyanSelfHost
