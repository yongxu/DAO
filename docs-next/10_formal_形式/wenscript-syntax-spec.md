# WenScript Syntax Spec v0.2

> Status: implemented parser surface for `wen-lisp prove`.
> This spec describes syntax recognition and AST buckets only. It does not
> claim semantic proof for every parsed sentence.

## Purpose

WenScript is the controlled 古文 proof-script layer used by:

```bash
wen-lisp prove <file.wen> [--trace] [--strict]
```

It is the current first bridge for:

```text
受控古文文档 -> WenScript AST -> structural certificates / typed syntax
```

Every nonempty line after the required first line `零起` is parsed into a
`Sentence`. Certificate-producing forms are deliberately narrow. General prose
may parse into typed operator/control events, but those events are not promoted
to Lean theorems.

## File Shape

A WenScript file must start with:

```text
零起
```

Blank lines are ignored. Line comments start with `;`.

If the first nonempty line is not `零起`, parsing fails with
`missingZeroStart`.

## Operator-Centric Core

The parser no longer has a closed relation-verb whitelist. WenScript reads
surface words as operator tokens when possible, then records an
`operatorApp`:

```lean
operatorApp op args form
```

`form` is one of:

```text
prefix | infix | applicationParticle | mixfix | discourse
```

`op` carries its trust boundary:

| Carrier | Meaning | V4 guarantee |
|---|---|---|
| `v4Builtin` | `道/错/錯/综/綜/错综/錯綜` | yes |
| `applicationParticle` | `之` as application particle | yes only when applied to a V4-capable operator |
| `root512` | direct `R8 × {cell, operator}` root reading alias | yes for root XOR application |
| `textLayer` | entry found in the Wenyan operator catalogue | no, unless a later semantic bridge proves it |

This is the key v0.2 boundary: **a line parsing as `operatorApp` does not mean
it has been evaluated through V4**. Only `v4Builtin`, R4/R5 structural
constructors, and later explicitly bridged root operators carry V4/R-space
certificates.

## Core AST

Implemented in:

```text
formal/SSBX/Foundation/Wen/V4Kernel/WenScript.lean
```

Current `Sentence` variants:

| Variant | Meaning | Produces certificate? |
|---|---|---|
| `defineR5 name value` | controlled R5 structural definition | yes |
| `verifyR5 name` | verify an earlier R5 definition | yes if found |
| `topicComment subject body` | `X者Y也` / `X者Y` topic-comment | no |
| `implication condition conclusion` | `若X则Y` or `X则Y` control form | no |
| `universal domain predicate` | `凡X皆Y` controlled schema | yes, as schema registration |
| `instantiateUniversal name predicate` | `验 X 为Y` explicit schema instance | yes if schema exists |
| `operatorApp app` | operator-first typed application | no |
| `assertion body` | `X也` | no |
| `barePhrase text tokens` | recognized line without an operator/control form | no |
| `alias left right` | `X即Y` | yes, as a controlled alias certificate |
| `enumHead name` | `X者` heading | no |
| `readThenVerify` | exact `读之则验` / `讀之則驗` | yes if prior evidence exists |
| `claimStub text tokens` | malformed controlled form fallback | no |

`claimStub` is not the ordinary bucket for prose. It is reserved for malformed
controlled syntax, for example a broken alias with an empty side or an unknown
R5 verification target.

Every parsed sentence is also stored with a source span in `LocatedSentence`.
The CLI reports span diagnostics for parsed forms that are syntactically valid
but do not yet have executable semantics or proof generation:

```text
diagnostic[0] span=5:1-5 unsupportedImplicationProof: ...
```

## Certificate-Producing Forms

### R5 Compact Definition

```text
仁者 间几阳 也
```

Pattern:

```text
<name>者 <ben><zheng><extension> 也
```

### R5 Split Definition

```text
仁者 间 几 阳 也
```

Pattern:

```text
<name>者 <ben> <zheng> <extension> 也
```

### R5 Verification

```text
验 仁 为五爻
驗 仁 為五爻
```

If `仁` has already been defined, verification emits another R5 certificate for
that definition. If the name is unknown, it becomes a `claimStub`.

### Universal Schema And Explicit Instance

```text
凡文皆可证
验 文 为可证
```

`凡文皆可证` registers a controlled universal schema and emits
`semanticCert ... universalSchema`. This is a schema-registration certificate,
not a claim that arbitrary natural-language universals are proved.

`验 文 为可证` emits `semanticCert ... universalInstantiation` only when the
matching schema has already appeared in the current report. Without that prior
schema, it receives `unsupportedUniversalInstantiation`.

### Read Then Verify

```text
读之则验
```

This emits `semanticCert ... readThenVerifyAvailable` only when the preceding
report already contains a structural/semantic certificate or executable V4 /
Root512 action trace. If it appears before any evidence, it receives
`unsupportedReadThenVerify`.

### R5 Coordinates

`ben` choices:

| 字 | Internal | V4 |
|---|---|---|
| 物 | `thing` | `dao` |
| 动 | `motion` | `zong` |
| 间 / 間 | `interval` | `cuo` |
| 事 | `event` | `cuoZong` |

`zheng` choices:

| 字 | Internal | V4 |
|---|---|---|
| 几 | `trace` | `dao` |
| 势 / 勢 | `momentum` | `zong` |
| 机 / 機 | `pivot` | `cuo` |
| 时 / 時 | `occasion` | `cuoZong` |

`extension` choices:

| 字 | Internal | Bool |
|---|---|---|
| 阳 / 陽 | `yang` | `false` |
| 阴 / 陰 | `yin` | `true` |

## Typed Syntax Forms

These forms are parsed and counted, but they do not currently produce Lean
theorems or structural certificates.

### Topic Comment

```text
道者一也
道者一
生生不息者往复而不穷也
```

Result:

```text
topicComment "道" "一"
```

If the body is exactly an R5 compact coordinate, this form is upgraded to
`defineR5`:

```text
仁者间几阳也
```

The only current topic-comment sentence upgraded into a semantic certificate is
the controlled persistence form plus exact V4 kernel topic readings:

```text
生生不息者往复而不穷也
生生不息者往復而不窮也
道者不移
错者反其内容
综者反其框架
错综者双反而复成一轨
```

The persistence form emits `semanticCert ... cyclicPersistence`. The four V4
topic lines emit `semanticCert ... v4OperatorTopic`. Other topic-comments emit
`semanticCert ... topicRegistration`, which means the sentence is admitted into
the controlled document stream; it is not a Lean theorem.

The same V4 topic bridge is also available for the compact operator-first
readings currently used by `wen-daodejing.wen`:

```text
错反其值
综反其向
道在核
```

These remain narrow kernel readings; they do not make arbitrary `X者Y也` prose
into theorems.

### Implication

```text
若名不入环境则名为symbol
读之则显
若错之乾则坤
若不之乾则坤
```

Results:

```text
implication "名不入环境" "名为symbol"
implication "读之" "显"
```

The exact line `读之则验` is parsed as `readThenVerify` before generic
implication parsing.

The parser avoids treating `则/則` as an implication delimiter inside common
lexical compounds such as `规则`.

Controlled implication proof is currently available only when:

1. the condition parses as one executable application;
2. the application result is a 64-word cell at temporal origin;
3. the conclusion is the same known 64-word token.

Examples:

```text
若错之乾则坤
若不之乾则坤
```

Both emit `semanticCert ... rootActionImplication`. Other implications emit
`semanticCert ... implicationRegistration`, which records controlled syntax
without claiming an implication proof.

The current 64-word Lisp name boundary also has four controlled implication
bridges:

```text
若名不入环境则名为symbol
若名入环境则名为reference
若名被束则名为local
若名被定义则名为global
```

These emit `semanticCert ... nameResolutionRule`. They are not general
implication proving; they document the existing symbol/reference/local/global
elaboration boundary.

There is also a state-aware controlled implication rule. If the condition can
produce a semantic certificate from the current proof report, and the
conclusion can produce a semantic certificate after that condition certificate
is added, the implication emits `semanticCert ... stateImplication`.

Example:

```text
文即理
理即道
若文不离道则有可证
```

Here `文不离道` is backed by the alias chain, and `有可证` is backed by the
condition certificate.

### Universal

```text
凡文皆可读
凡文皆可证
```

Result:

```text
universal "文" "可读"
universal "文" "可证"
```

#### Controlled Universal Schema And Instance

The controlled schema surface is:

```text
凡文皆可证
```

This line emits `semanticCert ... universalSchema`. It is a schema-registration
certificate; it must not by itself mean that every open prose line has become a
Lean theorem.

The explicit instance surface is:

```text
验 文 为可证
```

This emits `semanticCert ... universalInstantiation` only when a matching prior
schema is present. Spaced `验 ...` remains compatible with R5 structural
verification:

```text
验 仁 为五爻
```

If `验 文 为可证` appears before `凡文皆可证`, it receives
`unsupportedUniversalInstantiation`.

### Alias

```text
名即实
道者一也
```

Result:

```text
alias "名" "实"
topic-alias "道" "一"
```

Aliases are stored in the proof report and emit `semanticCert ...
aliasIdentity`. Alias lookup uses a finite transitive closure, so a chain can
support later controlled forms. For example, after:

```text
文即理
理即道
```

the line:

```text
文不离道
```

emits `semanticCert ... aliasInseparability`.

`X者Y也` only becomes a topic-alias when `Y` is a plain name token. Complex
topic comments such as `道者未发之同一` remain topic theorem frontier entries.

### Operator Application

Operator applications are recognized through V4 built-ins, `之`, or the
small Root512 aliases, or the existing Wenyan operator catalogue. Examples:

```text
错 之 乾
错之乾
错之综之乾
综 之 既济
恒 之 乾
印 之 乾
不之乾
文不离道
文可被读故有解释
有可证
卦为形
程序若自其规则而行
文见其德
文开其后
```

Representative results:

```text
operatorApp "错" ["乾"] applicationParticle   -- carrier: v4Builtin
operatorApp "错" ["乾"] applicationParticle   -- compact `错之乾`
operatorApp "错" ["综之乾"] applicationParticle -- nested executable fragment
operatorApp "综" ["既济"] applicationParticle -- carrier: v4Builtin
operatorApp "恒" ["乾"] applicationParticle   -- carrier: root512 / operator
operatorApp "印" ["乾"] applicationParticle   -- carrier: root512 / operator
operatorApp "不" ["乾"] applicationParticle   -- carrier: root512 / operator
operatorApp "不" ["文", "离道"] infix         -- carrier: root512 / operator
operatorApp "见" ["文", "其德"] infix        -- local text-layer operator
operatorApp "开" ["文", "其后"] infix        -- local text-layer operator
operatorApp "可" ["文", "被读故有解释"] infix -- carrier: textLayer / modal
operatorApp "有" ["可证"] prefix             -- carrier: textLayer / quantifier
operatorApp "为" ["卦", "形"] infix          -- carrier: textLayer / relate
operatorApp "若" ["程序", "自其规则而行"] infix -- carrier: textLayer / discourse
```

Most operator applications are typed syntax events, not semantic relation
theorems. When no executable bridge exists, they emit `semanticCert ...
operatorRegistration`, not a proof or V4 execution result. A few small
state-dependent bridges are implemented:

Nested `之` is supported only inside the executable V4/Root512 fragment. For
example `错之综之乾` first computes `综之乾`, then applies `错` to that result.
Unknown words and general prose still remain diagnostics or typed syntax.
Unknown 64-word arguments in executable application position remain hard
diagnostics.

- `文不离道`-style forms produce `aliasInseparability` only when a prior alias
  has linked the two names, for example `文即道`.
- `文为道`, `文是道`, and `文同道`-style copula forms produce `copulaAlias`
  only when the two sides are syntactically equal or connected by the current
  alias closure.
- `有可证` produces `certificateAvailability` only when the preceding report
  already contains at least one structural or semantic certificate.
- `有未证` produces `openObligationAvailability` only when preceding located
  diagnostics or claim stubs have opened a frontier obligation.
- `无未证` produces `frontierClean` only when the preceding report has no
  located diagnostics and no claim stubs.
- `有可算` / `有未算` report whether the preceding script has any executable
  or calculable surface, and whether unresolved calculation/operator frontier
  remains. `有未算` includes registration-only operator applications because
  those lines are syntactically admitted but do not yet have an execution
  bridge.
- `有已名` / `有待名` report whether names have been introduced, and whether
  unresolved frontier still leaves naming work pending.
- `文可被读故有解释`, `文可被算故有执行`, and `文可被证故有边界`
  emit `wenCapability`: these are controlled capability statements about the
  current interpreter boundary, not open-ended modal logic.
- `文能生文乃编`, `文能读文乃释`, `文能证文乃信`, and
  `文能改文而留其证乃德` also emit `wenCapability`. These are the controlled
  self-description forms for the current compiler/prover direction; they are
  not recursive macro execution and not VM self-hosting.
- `X不为Y而Y以之P` emits `textSchemaInstantiation` when it instantiates the
  non-object instrumental schema. The parser checks the structure rather than
  matching one whole line: the left clause must be `X不为Y`, the right clause
  must reuse the same `Y`, and `之` resolves to `X`. Current examples include
  `道不为物而物以之成形`, `道不为数而数以之定位`, and same-shape variants such
  as `道不为名而名以之立实`. A mismatched sentence such as
  `道不为名而实以之立名` does not instantiate this schema.
- `X可被A故有B` emits `textSchemaInstantiation` through the passive capability
  schema when `X` is `文` or has already been linked to `文` by aliases. Current
  examples include `文可被读故有解释`, `文可被算故有执行`, and
  `文可被证故有边界`.
- `X能A乃B` emits `textSchemaInstantiation` through the active capability
  schema under the same `文`/alias boundary. Current examples include
  `文能生文乃编`, `文能读文乃释`, `文能证文乃信`, and
  `文能改文而留其证乃德`.
- Structural readings also emit `textSchemaInstantiation` when their subjects
  are in the controlled structural vocabulary. Current forms include
  `X在Y中为Z`, `X为Y`, `X成Y`, `每X有其Y`, `X在Y`, `X有所Y`,
  `X不Y`, and `X可Y` / `X可以Y`. Examples include `一字在文中为名`,
  `卦为形`, `六位成卦`, `每格有其卦`, `字有所指`, `形不离读`,
  `位可组合`, and `一至六十四可以入字`.
- V4 duality readings emit `textSchemaInstantiation` for the controlled
  duality surfaces `X之四读`, `X内容框架复合`, `X由此有骨`, and
  `反复X`. Current examples include `乃一事之四读`, `同一内容框架复合`,
  `意义由此有骨`, and `反复其文`.
- Discourse readings emit `textSchemaInstantiation` for controlled dependency
  surfaces. Current forms include `无X则Y但为Z`, `X若自其Y而Z`, and selected
  causative `使X承Y` / `使X渐Y` forms whose `X` is in the structural
  vocabulary. Current examples include `无德则道但为空名`,
  `无道则德但为习气`, `程序若自其规则而行`, `证明若自其公理而出`,
  `使后文承前文之证`, and `使字渐多而核不散`.

### Assertion

```text
系统也
```

Result:

```text
assertion "系统"
```

### Bare Phrase

```text
未识别短语
```

Result:

```text
barePhrase "未识别短语" ["未", "识", "别", "短", "语"]
```

This is the lowest typed syntax bucket. It records the line and char-level
tokens so later semantic passes can revisit it.

## Report Counters

`wen-lisp prove` prints:

```text
sentences=<n>  definitions=<n>  certificates=<n>  claimStubs=<n>
semanticCertificates=<n>  checked=<n>  registrations=<n>  diagnostics=<n>
certificateKinds executable=<n>  status=<n>  evidence=<n>
registrations topic=<n>  implication=<n>  operator=<n>  universalSchema=<n>
frontier topic=<n> implication=<n> universal=<n> readThen=<n> textLayer=<n> application=<n> unknownArg=<n> claimStub=<n>
aliases=<n>  enums=<n>  readThenVerify=<n>
topicComments=<n>  implications=<n>  universals=<n>
operatorApps=<n>  v4Actions=<n>
rootApplications=<n>
assertions=<n>  barePhrases=<n>
```

Interpretation:

- `definitions`: number of R5 definitions.
- `certificates`: R5 definition certificates plus successful R5 verification certificates.
- `semanticCertificates`: controlled semantic certificates, currently the
  narrow `生生不息者往复而不穷也` persistence form, action-result
  implications such as `若错之乾则坤`, alias identity such as `文即理`,
  alias-backed copula/inseparability such as `文即理` and `理即道` followed by
  `文为道` or `文不离道`, and report-backed availability such as `有可证`, plus
  state-aware implication over these controlled certificates, and controlled
  universal schema/instantiation certificates such as `凡文皆可证` followed
  by `验 文 为可证`, evidence-backed `读之则验`, and executable action-trace
  certificates for V4/Root512 applications such as `错之乾` and `印之乾`,
  frontier-state certificates such as `有未证` and `无未证`, and registration
  certificates for admitted topic, implication, and operator lines whose
  semantic bridge is not yet implemented. The generated `wen-daodejing.wen`
  also uses typed schema bridges for `X不为Y而Y以之P`, `X可被A故有B`,
  `X能A乃B`, structural readings, possibility readings, and V4 duality
  readings, plus discourse dependency readings such as `无X则Y但为Z` and
  `X若自其Y而Z`, plus exact controlled bridges for:
  `wenBoundary` (interpreter/proof-boundary discipline),
  `nameValueLaw` (name/value/proof-anchor readings),
  `v4DualityLaw` (V4 reflection/composite readings), and
  `rootStructureLaw` (Word64/Root512/R-structure readings).
  Exact bridges are stored as small registries in `WenScript.lean`:
  `controlledTopicBridges`, `controlledImplicationBridges`, and
  `controlledOperatorBridges`. New reusable semantic behavior should become a
  typed schema bridge first; only truly atomic controlled readings should be
  added as exact registry rows.
- `checked`: semantic certificates excluding registration-only certificates.
- `registrations`: schema or syntax registrations such as unsupported-but-typed
  topic, implication, operator lines, and universal schemas. These are audit
  records, not proof conclusions.
- `registrations topic/implication/operator/universalSchema`: registration
  breakdown. This is the main map for future semantic bridge work after a file
  is strict-clean but still mostly registered rather than proved.
- `certificateKinds`: useful subcounts. `executable` means a computed V4 or
  Root512 action, or an implication backed by such an action. `status` means a
  report-state certificate such as `有可证`, `无未证`, `有可算`, or `有已名`.
  `evidence` is what `有可证` may depend on: R5 certificates and semantic
  certificates that are neither registrations nor report-state status.
- `diagnostics`: located explanations for parsed syntax that has no executable
  semantics or proof generation and cannot even be safely registered, such as
  unknown 64-word action arguments.
- `frontier`: diagnostics grouped by the next proof/semantic bridge needed.
  This is the actionable boundary for later grammar work: each nonzero bucket
  is a deliberately open obligation, not a failed parser state.
- `claimStubs`: malformed controlled forms or unknown R5 verification targets.
- `operatorApps`: typed operator/control applications.
- `v4Actions`: computed V4 actions for `v4Builtin 之 <64-word>` forms.
- `rootApplications`: computed Root512 applications for direct root aliases
  such as `恒/印/投/印投 之 <64-word>`.
- all other counters: typed syntax only, not proof.

With `--strict`, `prove` exits nonzero when either `diagnostics` or
`claimStubs` is nonempty. This lets a controlled `.wen` file be used as a
compiler-checked artifact without pretending that all parsed prose is proved.

With `--strict-proved`, `prove` also exits nonzero when registration-only
certificates remain. This is the stronger boundary for files that should have
semantic bridges for every admitted topic, implication, operator, and universal
schema line.

As of WenScript v0.2, `examples/wen-lisp/wen-daodejing.wen` is expected to pass
`--strict-proved`: every line has either an executable/structural/status
certificate or a narrow exact controlled semantic bridge, and no registration
certificate remains.

With `--trace`, operator applications are printed with carrier and form so a
reader can distinguish `v4Builtin` from `textLayer`. Computed V4 action lines
are printed separately, for example `错 之 乾 => 坤`.

Computed Root512 application lines are also printed separately. Root512 is:

```text
R8 × {cell, operator}
= (Word64 × V4) × {cell, operator}
= V4^4 × {cell, operator}
```

The aliases currently bridged are deliberately small and structural:

| Surface | Root512 reading |
|---|---|
| `恒` / `恆` | origin/no-op operator |
| `印` | trace-bit temporal operator |
| `投` | projection-bit temporal operator |
| `印投` | compound temporal operator |
| `非` / `不` | 64-word complement mask at temporal origin |

These aliases do not revive the old catalogue as ontology. They are direct
root readings.

Current diagnostic kinds:

| Kind | Meaning |
|---|---|
| `unsupportedTopicTheorem` | reserved for topic-comment theorem failures; current valid topic-comments register instead |
| `unsupportedImplicationProof` | reserved for implication proof failures; current valid implications register instead |
| `unsupportedUniversalInstantiation` | explicit `验 X 为Y` has no matching prior universal schema |
| `unsupportedReadThenVerify` | `读之则验` has no prior certificate or executable action trace |
| `unsupportedTextLayerOperator` | reserved for unregistrable text-layer operators; current valid operators register instead |
| `unsupportedApplicationGrammar` | reserved for unregistrable root/V4 operator grammar; current valid operators register instead |
| `unknownActionArgument` | executable operator was applied to an unknown 64-word token |
| `claimStub` | malformed controlled form or unknown certificate target |

The frontier summary is computed from those diagnostic kinds:

| Frontier bucket | Diagnostic kind |
|---|---|
| `topic` | `unsupportedTopicTheorem` |
| `implication` | `unsupportedImplicationProof` |
| `universal` | `unsupportedUniversalInstantiation` |
| `readThen` | `unsupportedReadThenVerify` |
| `textLayer` | `unsupportedTextLayerOperator` |
| `application` | `unsupportedApplicationGrammar` |
| `unknownArg` | `unknownActionArgument` |
| `claimStub` | `claimStub` |

## Completion Criteria

WenScript syntax completion means:

- every nonempty line after `零起` parses into a `Sentence`;
- every parsed line retains source location for diagnostics;
- R5 definitions and successful R5 verifications produce structural certificates;
- the controlled `生生不息者往复而不穷也` topic-comment produces a semantic
  persistence certificate;
- action-result implications such as `若错之乾则坤` produce semantic
  implication certificates;
- V4 built-in action syntax records V4-carried operator applications and
  computes R6 action results when the argument is a known 64-word token or a
  nested executable `之` application;
- Root512 aliases record root-carried operator applications and compute the
  R8 reading result when the argument is a known 64-word token;
- text-layer catalogue operators are recognized without claiming V4 execution;
- unsupported but parsed forms receive registration certificates when safe;
- unsupported semantics remain registrations or claim stubs, not fake proofs.

It does not mean:

- every operator application has executable semantics;
- every parsed prose line has a Lean theorem;
- every text-layer catalogue operator is already bridged to V4/R-space.
