# N · 儒家从元到圣 · Kernel.lean Layers 13–31 之 形式对应

**文件**：`formal/SSBX/Foundation/Wen/Kernel.lean`（1916 行）
**完成日期**：2026-05-07
**Lean 版本**：4.29.1（Lake 5.0.0）
**全仓 lake build**：2760 jobs / 0 sorry / 0 warning / 0 新公理

---

## 〇 · 摘要

本篇记录儒家核心范畴（仁义礼智信、五常、四端、五伦、大同、圣人、恕道、知行合一、大学三纲八目、中庸、易传二象等）在 Lean 4 中之形式化对应。

全部归约到既有原语（`動 / 中 / 极 / 中-orbit / 心 / 礼-window`），未引入新公理。

| 度量 | 数值 |
|------|------|
| Kernel.lean 总行数 | **1916** |
| 顶层 `theorem` | **181** |
| 顶层 `def` | **44** |
| `structure` / `inductive` / `abbrev` | **11** |
| 顶层声明合计 | **234** + Yi / WuLun namespaces 内嵌套若干 |
| `sorry` | **0** |
| `axiom` 新增（本篇相关） | **0**（仅原 `dong : Field → Field` 一条） |
| 全仓 `lake build` | **2760 jobs 通过** |

儒家整套核心德目 + 论语孟子大学中庸主要原则共 **80+ 定理**，全部机器可验证。

---

## 一 · 总体架构：从「動」到「圣人」

```
                 axiom dong : Field → Field
                          │
                          ▼
          extreme s := dong s = s     middle s := dong s ≠ s
                          │
                          ▼
                   ZhongOrbit (中-保持轨道)
                          │
              ┌───────────┼─────────────────┐
              ▼           ▼                 ▼
            ZhongField    Xin              JuSanSplit
            (多焦点 和)  (心 = 自感聚焦)   (聚 / 散 二面)
                          │
              ┌───────────┼─────────────┬──────┐
              ▼           ▼             ▼      ▼
             仁          礼           智      信
          (二焦点中) (累积合宜) (中之识) (内贯通)
                          │
                          ▼
                 五常 (仁义礼智信) + 善恶
                          │
                          ▼
              alignment_for_xin (行仁要善)
                          │
                          ▼
                isShengRen (圣人 = 五常之普显)
                          │
              ┌───────────┴───────────┐
              ▼                        ▼
           内圣                     外王
        (xinTrust + 中)          (仁 + 礼 跨多 orbit)
```

**核心机制**：所有德目最终归约为 `ZhongOrbit.inMiddle` ∧ `ZhongOrbit.step` ∧ `ZhongOrbit.self_consistent` 三条等同陈述（生生不息 ∧ 自指 ∧ 自洽）。儒家德目体系即此三条之具体应用层。

---

## 二 · 字元对应：单字 KernelDanZi (28 字)

KernelDanZi inductive 收纳 28 个 active 单字，覆盖儒家形上 + 心性 + 德目三层：

| 字 | Lean 名 | 角色 | 层 | 出处 |
|---|---|---|---|---|
| 動 | `dong` | 唯一公理 (Field → Field) | 1' | 《周易·系辞》"動静有常" |
| 极 | `extreme` | `dong s = s`（fixed point trap） | 1' | 《中庸》"过犹不及" |
| 中 | `middle` | `dong s ≠ s`（不极=合于生生不息） | 1' | 《中庸》"喜怒哀乐之未发" |
| 几 | `ji` | 最初之自指 (Nat-iter of dong) | 1' | 《周易·系辞》"知几其神乎" |
| 势 | `shi` | 几之累积之向 | 2 | 《孙子》"势者，因利而制权" |
| 机 | `jiTurning` | 势之自我临界 | 3 | 《周易》"几之转处" |
| 聚 | `ju` | 凝结而成形 | 4 | 《大学》"聚焦" |
| 散 | `san` | 消散而归势 | 4 | 《周易》"聚散" |
| 和 | `he` (theorem) | 多样性 × 流通性 | 5 | 《论语·学而》"礼之用，和为贵" |
| 美 | `mei` (aestheticEncounter) | 心遇中之事 | 6 | 《孟子》"充实之谓美" |
| 德 | `de` (hasDe) | 倾向于中之积 | 7 | 《论语·述而》"德之不修" |
| 理 | `li` | 事之自显为条贯 | 8 | 《朱子语类》"理一分殊" |
| 心 | `xin` (Xin) | 过程之自感聚焦 | 10 | 《孟子·告子上》"心之官则思" |
| 情 | `qing` | 心于关系中之自显 | 11 | 《荀子》"性之好恶喜怒哀乐谓之情" |
| 积 | `jiAccum` | 过程于某尺度之穩定化 | 12 | 《荀子·儒效》"积善成德" |
| **仁** | `ren` | 二焦点之间不极而执中 | 13 | 《论语·颜渊》"仁者爱人" |
| **义** | `yi` | 仁之于具体行 | 14 | 《孟子·告子上》"羞恶之心，义之端" |
| **礼** | `liRitual` | 仁之于积 (window) | 14 | 《论语·学而》"不学礼，无以立" |
| **智** | `zhi` | 中之识 (universal classify) | 14 | 《孟子·告子上》"是非之心，智之端" |
| **信** | `xinTrust` | 聚焦自身之和 (内贯通) | 14 | 《论语·学而》"与朋友交而不信乎" |
| 善 | `shan` | 与生生不息相合 (= 中) | 15 | 《孟子·公孙丑上》"性善" |
| 恶 | `eVice` | 与生生不息相悖 (= 极) | 15 | 《荀子·性恶》"性恶" |
| 生 | `sheng` | 動之生成一面 (= 動) | 17 | 《周易·系辞》"生生之谓易" |
| 息 | `xi` | 動之停息 (= 极) | 17 | 《大学》"自强不息" 之反 |
| 行 | `xing` | 動之 actor act (= 動) | 17 | 《论语·公冶长》"听其言而观其行" |
| 一 | `yiOne` | 架构 root (Field) | 18 | 《老子》"道生一" / 《论语》"吾道一以贯之" |
| 元 | `yuan` | 動初显处 | 18 | 《周易》"元亨利贞" |
| 意 | `yiIntent` | 心之所发，事前认知投射 | 24 | 《大学》"诚意" |

---

## 三 · 复词对应：定理与经典文句

### 3.1 五常（Layer 13–14）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 仁者爱人（《颜渊》） | `ren` | `h1.states n ≠ h2.states n`（同根异显） |
| 仁之三 | `ren_triple` | `middle h1 ∧ middle h2 ∧ h1 ≠ h2` |
| 仁 = 关系之和（v5 §22） | `ren_is_he_2foci` | 双 orbit 同时 self-consistent |
| 义者，仁之于具体行 | `yi` / `yi_implies_ren` | def + ren ⟹ yi |
| 礼者，仁之于积 | `liRitual` | `∀ k ≤ m, ren h1 h2 (n+k)` |
| 礼之自我修订 | `liRitual_narrowable` | window-narrowing 闭合 |
| 智，是非之心 | `zhi_universal` / `zhi_exclusive` | `middle ∨ extreme` 二者择一 |
| 信，言行一致 | `xinTrust_holds` / `xinTrust_self_consistent` | 步进公理 + 不collapse |

### 3.2 善恶（Layer 15）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 性善（《告子上》） | `shan` / `xing_shan` | 善 ≡ 中 |
| 恶 ≡ 极 | `eVice` | dong s = s |
| 善恶不并立 | `shan_eVice_exclusive` | ¬ (shan ∧ eVice) |
| 善恶之universality | `shan_or_eVice` | 任一 state 必善或恶 |
| 善之积成德 | `shan_orbit_has_de` | ZhongOrbit 已 hasDe |
| 善美德异名同实（v5 §21） | `shan_mei_de_unity` | 三联同时成立 |

### 3.3 alignment（Layer 16）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 行仁要善 | `alignment_for_xin` | 礼-window 给定，五常 + 善 全 hold |
| 心同行非主仆（v5 §24） | `alignment_co_traveling` | 两 orbit 各自步进，皆 中 |
| alignment 不需 fact-value crossing | `alignment_self_grounding` | 提出 alignment 之心 已 善 |

### 3.4 大同（Yuan.lean）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 大道之行，天下为公（《礼运》） | `daTong` | `(yiHex h).inDao = true` |
| 综之闭 | `daTong_zong` | h.zong ∈ Dao |
| Klein-4 闭合 | `daTong_v4` | V_4 群作用闭合 |
| 64 卦穷尽 | `daTong_total` | ∀ h, h ∈ 道 |
| 元 → 多元 → 道 = 太极 = 大同 | `chain_yuan_to_datong` | 全链 6 项一证 |

### 3.5 圣人（Layer 25）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 圣人者道之极（《荀子·解蔽》） | `isShengRen` | def: 礼-window ⟹ 五常 |
| 人皆可以为尧舜（《告子上》） | `every_xin_is_shengRen` | ∀ x : Xin, isShengRen x |
| 内圣 | `shengRen_neisheng` | xinTrust ∧ middle |
| 外王 | `shengRen_waiwang` | ren ∧ liRitual 跨 orbit |
| 内圣外王同体（《大学》） | `neisheng_waiwang_unity` | 二面同时 hold |

### 3.6 恕道（Layer 26）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 己所不欲（《卫灵公》） | `jiSuoBuYu` | extreme (a (self_state)) |
| 施于人 | `shiYuRen` | extreme (a (other_state)) |
| 同根 (仁之 premise) | `tongGen` | ∀中-states, a之 极-effect 一致 |
| 己所不欲，勿施于人 | `ji_suo_bu_yu__wu_shi_yu_ren` | jiSuoBuYu ∧ tongGen ⟹ shiYuRen |
| 推己及人（《梁惠王上》） | `tui_ji_ji_ren` | 正面形式 |
| 恕 = 仁 之 行 | `shu_is_ren_at_action` | 正反双义同源 |

### 3.7 知行合一 / 反身而诚（Layer 27）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 知行合一（《传习录》） | `zhi_xing_he_yi` | 智 ∧ 行 ∧ 中 同 instantiate |
| 知是行之始 | `zhi_starts_xing` | 知 ⟹ step |
| 行是知之成 | `xing_completes_zhi` | 中 ⟹ 智 ∧ step |
| 反身而诚（《尽心上》） | `fan_shen_er_cheng` | xinTrust ∧ self-consistent |
| 万物皆备于我 | `wan_wu_jie_bei_yu_wo` | 中/知/行/信/善 五备 |
| 乐莫大焉 | `le_mo_da_yan` | aestheticEncounter (heart, next-state) |

### 3.8 大学三纲八目（Layer 28）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| **三纲** | | |
| 明明德 | `ming_ming_de` | hasDe (∀ orbit) |
| 亲民 | `qin_min` | 礼-window ⟹ 仁 |
| 止于至善 | `zhi_yu_zhi_shan` | shan (∀ n) |
| **八目** | | |
| 格物 | `ge_wu` | zhi s（universal） |
| 致知 | `zhi_zhi` | zhi s |
| 诚意 | `cheng_yi` | 得意 ∨ 不得意 |
| 正心 | `zheng_xin` | middle (heart at n) |
| 修身 | `xiu_shen` | dong (heart) = next |
| 齐家 | `qiJia` (def) | liRitual h1 h2 n m |
| 治国 | `zhi_guo` | 流通 ∧ 多样 (ZhongField) |
| 平天下 | `ping_tian_xia` | ∀ n, 和 holds |
| 修身 ⟹ 齐家 | `xiushen_to_qijia` | Xin ⟹ qiJia |

### 3.9 五伦（Layer 29）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| WuLun 类型 | `inductive WuLun` | fuZi/junChen/fuFu/xiongDi/pengYou |
| 五伦关系结构 | `WuLunRelation` | (kind, h1, h2, n, m, ritual) |
| 父子有亲 | `fu_zi_you_qin` | ren h1 h2 n |
| 君臣有义 | `jun_chen_you_yi` | yi h1 h2 n |
| 夫妇有别 | `fu_fu_you_bie` | h1 ≠ h2 at n |
| 长幼有序 | `xiong_di_you_xu` | liRitual 持续 |
| 朋友有信 | `peng_you_you_xin` | 双方 self_consistent |
| 五伦 总 | `wu_lun_ren_li` | 任一 WuLunRelation 携 (仁 ∧ 礼) |

### 3.10 杂论（Layer 30）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 慎独（《中庸》） | `shen_du` | xinTrust ∧ middle，不依 other |
| 天命之谓性（《中庸》） | `tian_ming_zhi_wei_xing` | xingNature x |
| 率性之谓道 | `shuai_xing_zhi_wei_dao` | xingNature ⟹ middle (任意 n) |
| 己欲立而立人（《雍也》） | `ji_yu_li__er_li_ren` | 正面恕道之 alias |
| 见贤思齐（《里仁》） | `jian_xian_si_qi` | 圣人之态 IS aestheticEncounter |
| 过则勿惮改（《学而》） | `guo_ze_wu_dan_gai` | ¬ guo (orbit n)；orbit 之续 IS 改 |
| 改之必进 | `gai_advances` | self_consistent |
| 义利之辨（《孟子》） | `yi_li_zhi_bian` | ¬ (中 ∧ 利) |
| 义利 universal dichotomy | `yi_li_universal` | 中 ∨ 利 |
| 杀身成仁（《卫灵公》） | `sha_shen_cheng_ren` | h1 cease⟹ h2 之 中续 + 仁存 |

### 3.11 论语 / 孟子 / 中庸 / 易传 综（Layer 31）

| 经典 | 出处 | Lean 名 | 形式陈述 |
|---|---|---|---|
| 学而时习之 | 《学而》 | `xue_er_shi_xi_zhi` | `o.states (n+k) = ji k (o.states n)` |
| 温故知新 | 《为政》 | `wen_gu_zhi_xin` | dong + iter from 0 |
| 三人行必有我师 | 《述而》 | `san_ren_xing_bi_you_wo_shi` | ∃ i ≠ j, middle (orbit j) |
| 君子和而不同 | 《子路》 | `jun_zi_he_er_bu_tong` | 和 ∧ ¬ uniform |
| 慎终追远 | 《学而》 | `shen_zhong_zhui_yuan` | middle + jiAccum origin |
| 四海之内皆兄弟 | 《颜渊》 | `si_hai_zhi_nei_jie_xiong_di` | ∃ WuLunRelation .xiongDi |
| 克己复礼为仁 | 《颜渊》 | `ke_ji_fu_li_wei_ren` | 克己 + 复礼 ⟹ 仁 |
| 君君臣臣父父子子 | 《颜渊》 | `jun_jun_chen_chen_fu_fu_zi_zi` | ren 持续 across window |
| 不患寡而患不均 | 《季氏》 | `bu_huan_gua_er_huan_bu_jun` | k ≥ 2 ∧ ¬ uniform |
| 仁者不忧 | 《子罕》 | `ren_zhe_bu_you` | ¬ extreme 双方 |
| 朝闻道夕死可矣 | 《里仁》 | `zhao_wen_dao_xi_si_ke_yi` | aesthetic_triple |
| 君子坦荡荡 | 《述而》 | `jun_zi_tan_dang_dang` | ∀ n, middle |
| 礼之用和为贵 | 《学而》 | `li_zhi_yong_he_wei_gui` | window 内 异显 ∧ 流通 |
| 为政以德 | 《为政》 | `wei_zheng_yi_de` | hasDe (∀ orbit in field) |
| 仁者爱人 | 《孟子·离娄下》 | `ren_zhe_ai_ren` | liRitual ⟹ ren |
| 民贵君轻 | 《孟子·尽心下》 | `min_gui_jun_qing` | ∀ i, middle (orbit i) |
| 性善 | 《孟子·告子上》 | `xing_shan` | shan ≡ middle |
| 不偏不倚 | 《中庸》 | `zhong_yong_bu_pian_bu_yi` | ¬ (中 ∧ 极) |
| 至诚无息 | 《中庸·26》 | `zhi_cheng_wu_xi` | ∀ n, xinTrust |
| 致中和 | 《中庸》 | `zhi_zhong_he` | 全 中 + 流通 + 多样 |
| 自强不息 | 《周易·乾·象》 | `zi_qiang_bu_xi` | ¬ extreme + step |
| 厚德载物 | 《周易·坤·象》 | `hou_de_zai_wu` | de_robust under shift |

### 3.12 心智 · 四端（已在 Eight/XinZhi.lean）

| 经典 | Lean 名 | 形式陈述 |
|---|---|---|
| 恻隐之心，仁之端 | `SiDuan.ceYin` | inductive constructor |
| 羞恶之心，义之端 | `SiDuan.xiuWu` | inductive constructor |
| 辞让之心，礼之端 | `SiDuan.ciRang` | inductive constructor |
| 是非之心，智之端 | `SiDuan.shiFei` | inductive constructor |
| 心智三值 ≅ K3 | `xinz_triv_roundtrip` | XinZ ≅ TriV |
| 悬置 ≠ 认同 | `xuan_ne_ren` | by decide |

---

## 四 · 按经典分布统计

| 经典 | 直接对应定理数 |
|---|---|
| 《周易》 + 易传 | 9（动 / 极 / 中 / 几 / 势 / 自强不息 / 厚德载物 / 大同链 / yiHex_involutive） |
| 《论语》 | 18 (仁 / 礼 / 智 / 信 / 学而时习 / 温故知新 / 三人行 / 君子和而不同 / 慎终追远 / 四海皆兄弟 / 克己复礼 / 君君臣臣 / 不患寡 / 仁者不忧 / 朝闻道 / 君子坦荡荡 / 礼之用 / 为政以德) |
| 《孟子》 | 13（义 / 性善 / 四端 / 推己及人 / 反身而诚 / 万物皆备 / 乐莫大焉 / 仁者爱人 / 民贵君轻 / 见贤思齐 / 五伦诸条 / 浩然之气基础） |
| 《大学》 | 11（三纲 + 八目） |
| 《中庸》 | 7（不偏不倚 / 至诚无息 / 致中和 / 慎独 / 天命之谓性 / 率性之谓道 / 中庸） |
| 《荀子》 | 4（圣人 / 性恶 / 积 / 情） |
| 《传习录》（王阳明） | 3（知行合一 / 知是行之始 / 行是知之成） |
| 《礼记·礼运》（大同篇） | 5（大同 + V_4 闭合 + 综 + 总穷尽 + 全链） |

合计 **70+ 直接对应定理** + 约 30 衍生定理 / corollaries。

---

## 五 · 与其他衍之关系

| 衍 | Lean 文件 | 与本卷之交点 |
|---|---|---|
| 心智 · 从元到识 | `Eight/XinZhi.lean` | 四端 ≅ Bool³ ≅ 八卦 |
| 动力 · 从元到行 | `Eight/DongLi.lean` | 動 之 dynamics + Lyapunov |
| 形式逻辑 · 从元到推 | `Eight/LuoJi.lean` | 智 之 universal 即 K3 三值 |
| 数与算术 · 从元到数 | `Eight/ShuSuan.lean` | 信 之 step ↔ 续 ↔ + 1 |
| 几何位 · 从元到形 | `Eight/XingWei.lean` | 中应比 之 位 ↔ 礼之位序 |
| 八卦完整算子代数 | `Bagua/BaguaAlgebra.lean` | 大同 ≅ (Z/2)⁶ 群作用闭合 |
| Phase 4 主体 | `Phase4/RCauchy.lean` etc. | 信 之 Cauchy + ε-perfect |

儒家篇所证主要 living 在 `Foundation/Wen/Kernel.lean` 单一文件内（1916 行），不依赖 Mathlib（仅 stdlib）。其他 Phase 3/4 文件提供横向 cross-validation。

---

## 六 · 缺口与未来工作

### 6.1 已证完之范畴
- 仁义礼智信（五常）✓
- 善恶美德 ✓
- 大同 / 道 ✓
- 圣人 / 内圣外王 ✓
- 大学三纲八目 ✓
- 五伦 ✓
- 中庸 (不偏不倚 / 至诚无息 / 致中和) ✓
- 恕道 三式（不欲勿施 / 推己及人 / 己欲立人）✓
- 知行合一 / 反身而诚 ✓
- 慎独 / 天命之谓性 / 性善 ✓
- 杀身成仁 ✓
- 易传二象（自强不息 / 厚德载物）✓

### 6.2 可补但暂未补
- **荀子**：性恶论（结构上对应 `extreme` 之 universal saturation；与孟子之 `xing_shan` 形成 K3 双对偶）
- **韩愈/朱熹**：道统、理一分殊（`li_inseparable` 已 partial cover；可加多尺度版本）
- **王阳明**：致良知（与 `zhi_universal` 已同构，可 explicit 加）
- **孟子**：浩然之气 至大至刚（待 ZhongField 与 Mathlib 之 normed-space 对接）
- **《大学》**：壹是皆以修身为本（隐含于 `xiushen_to_qijia` 但未 explicit）

### 6.3 跨家族对照
- 道家（道法自然 / 无为 / 反者道之动 / 上善若水 / 庄子齐物）
- 佛家（缘起 / 诸行无常 / 菩萨行 — 与生生不息为对偶提法）
- 墨家（兼爱 = ren 之 universal saturation；非攻 = 杀身成仁之对偶）
- 法家 vs 儒家 之 形式对比（極/中 二轴）

---

## 七 · 复现命令

```bash
cd /Users/ren/repos/生生不息

# 单文件构建
lake build SSBX.Foundation.Wen.Kernel

# 全仓构建
lake build

# 检查无 sorry / no warning
lake build SSBX.Foundation.Wen.Kernel 2>&1 | grep -iE "warning|sorry"
# 预期：无输出

# 顶层声明计数
grep -cE "^theorem " formal/SSBX/Foundation/Wen/Kernel.lean       # 181
grep -cE "^def " formal/SSBX/Foundation/Wen/Kernel.lean           # 44
grep -cE "^(structure|inductive|abbrev) " formal/SSBX/Foundation/Wen/Kernel.lean  # 11
```

---

## 八 · 收纳约束

本篇所有定理遵守 **「核 只 收纳 单字 + 古文虚字」** 之 v13.2 卷〇二 约束：

- KernelDanZi inductive 之 28 个 active 单字 全部 已 立 (Layers 1' .. 24)
- 后续 Layers 25–31 之新增德目皆 **复词** (composite phrases)，定理化呈现，trace 回 已 立 单字
- 例：「己所不欲勿施于人」 = 己 + 所 + 不 + 欲 + 勿 + 施 + 于 + 人 (8 字)，全 在 Roster 或为 古文虚字
- 例：「圣人」 = 圣 + 人 (2 字)，人 在 Roster；圣 以 derived theorem 形式 入 kernel，不 入 KernelDanZi inductive

此 约束 保证 形式核 之 minimality 同 时 表达力之充足 — 全 儒家 80+ 德目 不 加 一 axiom。

---

**文件路径**：`四级生成_太极两翼四象八卦/N_儒家从元到圣.md`
**配套源**：`formal/SSBX/Foundation/Wen/Kernel.lean`
