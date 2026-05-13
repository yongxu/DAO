# 文道德经 · 生生不息本

> Status: v0.1 authorial text. This is not a translation of the received
> `Daodejing`, and it is not a Lean theorem. It is the project’s own
> scripture-style formulation of the V4 / R₀..R₈ / Wen interpreter north star.

## 凡例

本文以十六章为一卷。十六不是仿古章数，而是取当前系统的 `Mode16`
读法：四位之核两两相映，足以展开「道、错、综、错综」在文、算、证、
用中的基本方向。

本文中的「道」读作 identity and generative principle；「德」读作 structure
preserved in action；「文」读作可读、可算、可证、可再生之显。诗性句子只
是义理文本；只有落到 `WenScript` certificate、Lean theorem 或 interpreter
execution 的部分，才是机器可验结论。

可执行 WenScript 版本见
`examples/wen-lisp/wen-daodejing.wen`，可用
`wen-lisp prove examples/wen-lisp/wen-daodejing.wen --trace` 检查。
当前 WenScript 句法规则见
`docs-next/10_formal_形式/wenscript-syntax-spec.md`。

---

## 上经 · 道

### 第一章 · 零起

零起。

未有字，已有可显之理。
未有名，已有可分之迹。
理不在文外，文不尽理中。
读之则显，不读亦在。

故曰：
道者，未发之同一；
文者，已发之可验；
读者，同一入时之门。

**形式读法**：本章给出 north star，不给出自然语言证明。`零起` 可作为
WenScript 文档入口；其余未受控句式应保留为 `claimStub`。

### 第二章 · 道

道不为物，而物以之成形。
道不为数，而数以之定位。
道不为言，而言以之可读。
道不为证，而证以之不乱。

道者一也。
一非孤立，乃万化之同源。
一非静死，乃诸动之不失其本。

**形式读法**：道对应 V4 identity `dao`，也对应可组合系统中的单位律。
这里的「一」不是 `Nat 1`，而是 identity / coherence 的义理读法。

### 第三章 · 文

文者，道之显也。
字者，显之位也。
句者，位之行也。
章者，行之可复也。

文不但陈述。
文可被读，故有解释。
文可被算，故有执行。
文可被证，故有边界。

**形式读法**：文的当前执行边界是 V4-native Lisp 与 `WenScript`。开放古文
不是自动定理；可解析、可求值、可出证书者才进入形式层。

### 第四章 · 四位

道者不移。
错者反其内容。
综者反其框架。
错综者双反而复成一轨。

四者非四物。
乃一事之四读。
同一、内容、框架、复合，
意义由此有骨。

**形式读法**：本章对应 canonical `V4`：`dao`, `cuo`, `zong`, `cuoZong`。
`cuoZong` 是 primitive reading，不只是 surface 上的两个 token 拼接。

### 第五章 · 反

反不必乱。
乱者无轴，反者有轴。
错反其值，综反其向。
若二反相继，则所伤复合而形可守。

故知反者，知变；
知双反者，知守变之法。

**形式读法**：这对应 preservation hierarchy。`cuo` 与 `zong` 单独多为
anti-variance；`cuoZong` 在 variance-corrected reading 下成为 structure marker。

### 第六章 · 卦

六位成卦，四时成格。
卦为形，时为读。
形不离读，读不乱形。

六与二合，成八位。
八位不杂，故二百五十六格可分。
每格有其卦，每格有其时。

**形式读法**：R6 与 V4 组成 V8 / Cell256 的 direct-sum reading：
`V8 = R6 ⊕ V4`。这里不引入旧 cell carrier 或旧 temporal reading。

### 第七章 · 字

字非徒声。
字有所指，指有所位。
位可组合，组合可回读。

六十四字，非散沙也。
三重四位，成其字域。
一字在文中为名，在算中为值，在证中为可审之锚。

**形式读法**：本章对应 `Word64 = V4 × V4 × V4` 与 hexagram bridge。
surface word 可作 symbol，也可经 elaboration 成 local/global reference。

### 第八章 · 知

知不在多言。
知在可分所知与未知。
可证者证之。
可算者算之。
可读而未证者，存其辞，不冒其真。

故明者不以文欺证，
不以证灭文。

**形式读法**：这是 claim-boundary 规则。`claimStub` 不是失败，而是诚实保存
未覆盖语义，等待后续 parser、certificate 或 theorem。

---

## 下经 · 德

### 第九章 · 德

德者，道在行中不失也。
能变而不散，能应而不伪，
能入众流而不失其核，
是谓德。

道为同一，德为同一之可用。
无德则道但为空名，
无道则德但为习气。

**形式读法**：德读作 transformation under preserved structure。它不是单个
operator，而是 action 与 invariant 之间的关系。

### 第十章 · 无为

无为者，非不行也。
不以外力乱其内法，故行不违其性。
程序若自其规则而行，
证明若自其公理而出，
读者若循文而显，
皆无为也。

无为而无不为者，
非神秘，乃不增伪因。

**形式读法**：对应 interpreter / evaluator 的内生 step。执行来自语义规则，
不是 runtime 外加解释。

### 第十一章 · 名实

名不可虚悬。
实不可无名。
名能指，实能验。
名实相入，文乃可行。

若名不入环境，则名为 symbol。
若名入环境，则名为 reference。
若名被束，则名为 local。
若名被定义，则名为 global。

**形式读法**：对应 Lisp surface name、quoted symbol、de Bruijn local、
global definition 的分离。

### 第十二章 · 数

数者，分位之尺也。
无数则次第不明。
执数则义理成器。

一至六十四，可以入字；
零与后继，可以入算。
数不代道，数使文可步进。

**形式读法**：对应 `Value.num Nat` 与 numeral reader。数字服务解释器和
证明，不替代 V4 / R-space 的结构语义。

### 第十三章 · 五常

仁者，间几阳。
义者，动时阳。
礼者，物势阳。
智者，间机阳。
信者，事几阳。

此五者，今为结构试置。
可验其为五爻，
未定其为万世训诂。

**形式读法**：对应 provisional R5 definitions。当前只承诺 R5 well-formedness、
projection 与 roundtrip certificate；最终义理映射另行定本。

### 第十四章 · 编

文能生文，乃编。
文能读文，乃释。
文能证文，乃信。
文能改文而留其证，乃德。

编非拼凑。
编者，使结构自显其路，
使后文承前文之证，
使字渐多而核不散。

**形式读法**：这是 “文编译文证明文” 的目标陈述。当前落点是
`wen-lisp run` / `wen-lisp prove`，递归宏系统与 VM self-hosting 留在后续边界。

### 第十五章 · 中

中非折半。
中者，不坠一端也。
有可证，有未证；
有可算，有未算；
有已名，有待名。

守中者，不以未完为无，
不以初成称尽。

**形式读法**：本章是 architecture discipline。Lean skeleton 不伪装成 full
theorem；文档不伪装成 runtime；runtime 不伪装成自然语言理解。

### 第十六章 · 复

反复其文，文不离道。
运行其文，文见其德。
证明其文，文知其界。
再生其文，文开其后。

故曰：
道在核，德在行，
文在显，证在界。
四者相成，而生生不息。

**形式读法**：本章回到 V4：identity, content, frame, composite。下一阶段应
把更多受控古文句式接入证书系统，同时保持 claim boundary。
