# 字文语言规范 v0

> Status: Draft v0, compiler-front-end specification.
> Scope: source text, lexical normalization, indentation, grammar, AST, dynamic semantics, standard glyph library, diagnostics, and conformance tests.
> Non-scope: IR, bytecode, VM, memory model, optimizer, Lean formalization, or any existing interpreter implementation.

---

## 0. 目标与边界

字文是一门“以字为语法”的小语言。源码由 Unicode 文字、ASCII 数字、换行、tab、空格和少量 ASCII 算符别名组成。语法关键结构必须由字表达；ASCII 算符只作为输入别名，归一化后仍是字。

v0 的编译器前端产物是：

1. 归一化字符流。
2. 单字 token 流。
3. `INDENT` / `DEDENT` / `NEWLINE` token。
4. 规范 AST。
5. 名字解析与动态语义检查结果。

v0 不定义低层 IR、字节码、寄存器机、运行时堆布局或外部模块系统。

---

## 1. 源文件与字符

### 1.1 编码

- 源文件必须是 UTF-8。
- 换行接受 LF 和 CRLF，前端在词法阶段统一为 LF。
- 文件末尾若无换行，前端视为有一个虚拟换行。

### 1.2 允许字符类

| 类 | 用途 |
|---|---|
| CJK 字、兼容汉字、常用古文异体 | 语法字、标准库字、变量名 |
| ASCII digits `0..9` | 数字字面量 |
| ASCII operators `+ - * / % ^ == < >` | 数学算子输入别名 |
| tab `\t` | 行首块缩进 |
| space ` ` | 可选分隔和排版 |
| newline LF | 语句分隔和块结构 |

v0 不支持注释。以后若增加注释，推荐使用以 `注` 开头的整行形式，避免引入非字语法标记。

---

## 2. 字形归一化

前端必须先对源码做字形归一化，再进行 token 化。归一化不改变源位置映射；诊断仍报告原始源码位置。

### 2.1 正字策略

每个语义选择一个 canonical 字。简繁、异体、兼容字作为输入别名归一到 canonical 字。

### 2.2 v0 必备归一化表

| 输入 | canonical |
|---|---|
| `陽` | `阳` |
| `陰` | `阴` |
| `變` | `变` |
| `動` | `动` |
| `靜` | `静` |
| `錯` | `错` |
| `綜` | `综` |
| `兌` | `兑` |
| `離` | `离` |
| `應` | `应` |
| `屬` | `属` |
| `際` | `际` |
| `間` | `间` |
| `對` | `对` |
| `並` | `并` |
| `與` | `与` |
| `內` | `内` |
| `裡` | `里` |
| `復` | `复` |
| `還` | `还` |
| `轉` | `转` |
| `損` | `损` |
| `進` | `进` |
| `來` | `来` |
| `終` | `终` |
| `極` | `极` |
| `節` | `节` |
| `無` | `无` |
| `當` | `当` |
| `異` | `异` |
| `別` | `别` |
| `則` | `则` |
| `雖` | `虽` |
| `將` | `将` |
| `嘗` | `尝` |
| `為` | `为` |
| `體` | `体` |
| `實` | `实` |
| `漸` | `渐` |
| `驟` | `骤` |
| `屢` | `屡` |
| `兩` | `两` |
| `餘` | `余` |
| `書` | `书` |
| `稱` | `称` |
| `諱` | `讳` |
| `譏` | `讥` |
| `術` | `术` |
| `勢` | `势` |
| `罰` | `罚` |
| `氣` | `气` |
| `開` | `开` |
| `闔` | `阖` |
| `樞` | `枢` |
| `經` | `经` |
| `絡` | `络` |
| `熱` | `热` |
| `虛` | `虚` |
| `補` | `补` |
| `瀉` | `泻` |
| `調` | `调` |
| `順` | `顺` |
| `逆` | `逆` |
| `標` | `标` |
| `營` | `营` |
| `衛` | `卫` |
| `滯` | `滞` |
| `偽` | `伪` |
| `義` | `义` |
| `積` | `积` |
| `隱` | `隐` |
| `顯` | `显` |

实现可增加更多别名，但不得改变本表 canonical 结果。

---

## 3. 词法

### 3.1 Token 类

词法器只产生以下 token：

| Token | 内容 |
|---|---|
| `Glyph` | 一个归一化后的单字 |
| `Number` | 一个或多个 ASCII digits |
| `NEWLINE` | 逻辑行结束 |
| `INDENT` | tab 缩进级增加 |
| `DEDENT` | tab 缩进级减少 |
| `EOF` | 文件结束 |

双字不是词法 token。词法器必须把 `树和` 产成两个 `Glyph`：`树`、`和`。parser 和名字解析阶段按上下文组合双字或多字名字。

### 3.2 ASCII 数学别名

ASCII 算符在词法阶段归一化为 canonical `Glyph` 或 `Glyph` 序列。

| 输入 | token |
|---|---|
| `+` | `Glyph("加")` |
| `-` | `Glyph("减")` |
| `*` | `Glyph("乘")` |
| `/` | `Glyph("除")` |
| `%` | `Glyph("余")` |
| `^` | `Glyph("幂")` |
| `==` | `Glyph("等")` |
| `<` | `Glyph("小")` |
| `>` | `Glyph("大")` |

单独的 `=` 非法。等号只允许 `==`，因为赋义使用字 `为`。

### 3.3 空格

空格不产生 token。

空格的用途：

1. 分隔相邻变量名、数字和语法字，避免歧义。
2. 排版和美学对齐。

空格不得表示块缩进。行首空格被忽略，直到遇到第一个非空格字符；如果行首空格之后又出现 tab，则报 `E001 MixedIndent`。

### 3.4 Tab 缩进

缩进规则与 Python 的块模型相同，但只允许 tab 作为缩进单位。

词法器维护缩进栈，初始为 `[0]`。

每个非空逻辑行：

1. 统计行首连续 tab 数 `n`。行首空格不计入缩进。
2. 若 `n > stack.top`，压栈并产生一个 `INDENT`。
3. 若 `n = stack.top`，不产生缩进 token。
4. 若 `n < stack.top`，持续弹栈并产生 `DEDENT`，直到等于 `n`。
5. 若弹栈后没有等于 `n` 的历史缩进级，报 `E002 BadDedent`。

文件结束时，前端必须产生足够的 `DEDENT` 回到 0，然后产生 `EOF`。

---

## 4. 核心字库

### 4.1 语法关键字

这些字参与语法结构，不能作为变量名：

```text
令 为 法 返 若 否则 观 之 与 起 止 叶 枝 左 右 成 真 假 空
```

说明：

- `否则` 在 token 流中是 `否` `则`，parser 必须按相邻双字识别。
- `之` 是调用 marker。
- `与` 是多参数分隔，也是逻辑/组合标准算子；在调用实参位置优先按分隔符解释。

### 4.2 八经卦核心值

八经卦是核心值，不是普通变量：

| 字 | 象 | 三爻，自下而上 | 传统象 |
|---|---|---|---|
| `乾` | `☰` | `阳 阳 阳` | 天 |
| `坤` | `☷` | `阴 阴 阴` | 地 |
| `震` | `☳` | `阳 阴 阴` | 雷 |
| `巽` | `☴` | `阴 阳 阳` | 风 |
| `坎` | `☵` | `阴 阳 阴` | 水 |
| `离` | `☲` | `阳 阴 阳` | 火 |
| `艮` | `☶` | `阴 阴 阳` | 山 |
| `兑` | `☱` | `阳 阳 阴` | 泽 |

输入 `離`、`兌` 必须分别归一为 `离`、`兑`。

### 4.3 八卦核心算子单字

这些字必须在标准库中有定义，并可在表达式中使用：

```text
爻 阴 阳 卦 动 化 变 错 综 互 重 分 内 外 初 二 三 四 五 上
```

最低语义要求：

| 字 | v0 语义 |
|---|---|
| `阴` `阳` | 爻值 |
| `爻` | 爻类型/构造域名 |
| `卦` | 卦类型/构造域名 |
| `动` `化` `变` | 三个单爻 flip 生成元，作用于八卦时分别翻初/中/上爻 |
| `错` | 全爻取反 |
| `综` | 爻序上下反转 |
| `互` | 互卦/中间结构抽取；八卦上 v0 可作为标准库函数，六爻语义留给 64 卦附录 |
| `重` | 两个八卦重成六爻卦 |
| `分` | 六爻卦拆为内外八卦 |
| `内` `外` | 取内卦/外卦或标记内外方向 |
| `初` `二` `三` `四` `五` `上` | 爻位名 |

### 4.4 数学与逻辑基础字

```text
加 减 乘 除 余 幂 等 小 大 不 且 或
```

动态语义见 §8。

### 4.5 标准算子字库

`wenyan-operators.md` 是标准算子字库来源。v0 前端只把少数字作为语法关键字；其余算子是普通标准库名字，不阻止用户在局部作用域遮蔽，除非实现选择启用严格模式。

v0 标准算子字库按下列类目组织：

| 类 | 字集 |
|---|---|
| 关系 | `在 属 际 间 中 正 应 比 承 乘 对 偶 并 与 偕` |
| 含包 | `含 包 容 中 外 内 表 里` |
| 变换 | `化 变 易 革 改 反 复 还 转 推 致 损 益 屈 伸` |
| 流动 | `往 来 进 退 升 降 出 入 行 动 静 通` |
| 边界 | `始 终 起 止 立 成 极 节` |
| 量化 | `凡 皆 各 莫 或 有 无 唯` |
| 因果 | `故 由 自 至 致 使 令 以` |
| 模态 | `必 或 当 宜 可 能 得 应` |
| 否定/对偶 | `不 非 弗 勿 毋 反 异 别` |
| 同一/分异 | `同 一 即 是 为 分 合 别` |
| 序贯虚词 | `之 而 则 若 虽 然 故 乃 既 将 方 尝 者 也 于 所 未 已` |
| 高阶 | `道 理 势 机 法 象 名 体 用` |
| 定义/名实 | `体 兼 同 异 久 宇 动 止 端 尺 中 圆 平 撄 仳 次 法 名 知 指 物 实 位 离 然` |
| 史官/法家/医家/社会 | `书 曰 称 讳 讥 削 术 势 形 参 柄 因 任 守 利 制 度 罚 赏 气 血 精 神 开 阖 枢 经 络 寒 热 虚 实 补 泻 和 调 顺 逆 标 本 营 卫 滞 性 伪 群 礼 义 解 积` |
| 补遗 | `相 互 交 错 综 杂 隐 显 藏 露 守 持 居 处 聚 集 散` |

若同一个字在多类中出现，名字解析得到同一个字形名字；具体语义由标准库导出绑定决定。

---

## 5. 名字

### 5.1 名字构成

变量名是一个或多个相邻 `Glyph` 组成的名字串。变量名不能包含 `Number`。

允许：

```text
甲
左树
求和
临时值
```

不允许：

```text
1甲
甲1
令
乾
树和
```

### 5.2 保留规则

以下名字不可作为用户变量：

1. 语法关键字：§4.1。
2. 八经卦核心值：§4.2。
3. 八卦核心算子：§4.3。
4. 数学与逻辑基础字：§4.4。
5. v0 标准树名：`树`, `列`, `树和`, `先序`, `中序`, `后序`, `树数`, `树高`。

标准算子字库中非核心的普通算子默认可被局部遮蔽。编译器可提供 warning，但不得在 v0 默认模式报错。

### 5.3 歧义分隔

当相邻字串可被解释为多个名字组合时，parser 采用最长已绑定名字优先；若仍无法唯一判断，报 `E020 AmbiguousName`，用户必须用空格分隔。

例：

```text
令 左 为 1
令 树 为 2
令 左树 为 3
左树      # 解析为名字 左树
左 树     # 解析为两个名字，若语法位置允许
```

---

## 6. 语法

### 6.1 记号

此处 EBNF 使用英文元符号描述；源码本身不用这些符号。

```ebnf
Program       ::= StmtList EOF
StmtList      ::= Stmt (NEWLINE Stmt)* NEWLINE*
Block         ::= NEWLINE INDENT StmtList DEDENT

Stmt          ::= LetStmt
                | FunctionStmt
                | ReturnStmt
                | IfStmt
                | MatchStmt
                | ExprStmt

LetStmt       ::= "令" Name "为" Expr
FunctionStmt  ::= "法" Name ParamList? Block
ReturnStmt    ::= "返" Expr
IfStmt        ::= "若" Expr Block ElsePart?
ElsePart      ::= "否则" Block
MatchStmt     ::= "观" Expr Block

ExprStmt      ::= Expr
ParamList     ::= Name+
```

### 6.2 模式匹配语法

`观` 块中的每条语句可以是普通语句，也可以是模式分支。v0 只定义树模式：

```ebnf
MatchBranch   ::= LeafPattern Block | NodePattern Block
LeafPattern   ::= "叶" Name
NodePattern   ::= "枝" Name "左" Name "右" Name
```

如果 `观` 的被观察值是树，必须至少覆盖 `叶` 和 `枝` 两种形态，否则报 `E050 NonExhaustiveMatch`。

### 6.3 表达式语法与优先级

```ebnf
Expr          ::= OrExpr
OrExpr        ::= AndExpr ("或" AndExpr)*
AndExpr       ::= NotExpr ("且" NotExpr)*
NotExpr       ::= "不" NotExpr | CompareExpr
CompareExpr   ::= AddExpr (("等" | "小" | "大") AddExpr)?
AddExpr       ::= MulExpr (("加" | "减") MulExpr)*
MulExpr       ::= PowExpr (("乘" | "除" | "余") PowExpr)*
PowExpr       ::= CallExpr ("幂" PowExpr)?
CallExpr      ::= Primary ("之" ArgList)?
ArgList       ::= Expr ("与" Expr)*
Primary       ::= Number
                | Name
                | CoreLiteral
                | TreeLiteral
                | "起" Expr "止"

CoreLiteral   ::= "真" | "假" | "空"
                | "阴" | "阳"
                | "乾" | "坤" | "震" | "巽" | "坎" | "离" | "艮" | "兑"

TreeLiteral   ::= "叶" Expr
                | "枝" Expr "左" Expr "右" Expr "成"
```

优先级从高到低：

1. `起 ... 止`、字面量、名字。
2. 调用 `之`。
3. `幂`，右结合。
4. `乘 除 余`，左结合。
5. `加 减`，左结合。
6. `等 小 大`，不可链式比较。
7. `不`。
8. `且`。
9. `或`。

---

## 7. AST

实现的 AST 必须至少能表达以下节点。字段名可不同，但结构必须等价。

```text
Program(stmts: List[Stmt])

Stmt =
  Let(name: Name, expr: Expr)
  Function(name: Name, params: List[Name], body: List[Stmt])
  Return(expr: Expr)
  If(cond: Expr, thenBody: List[Stmt], elseBody: List[Stmt]?)
  Match(scrutinee: Expr, branches: List[Branch])
  ExprStmt(expr: Expr)

Branch =
  Leaf(valueName: Name, body: List[Stmt])
  Node(valueName: Name, leftName: Name, rightName: Name, body: List[Stmt])

Expr =
  Number(value: Nat)
  Bool(value: Bool)
  Empty
  Yao(value: Yin|Yang)
  Trigram(name: 乾|坤|震|巽|坎|离|艮|兑)
  Name(name: Name)
  TreeLeaf(value: Expr)
  TreeNode(value: Expr, left: Expr, right: Expr)
  Call(fn: Expr, args: List[Expr])
  Unary(op: 不, expr: Expr)
  Binary(op: 加|减|乘|除|余|幂|等|小|大|且|或, left: Expr, right: Expr)
```

Parser 组合双字后必须在 AST 中存 canonical 名字。例如源码 `樹和` 若未来加入 `樹→树` 归一化，应进入 AST 为 `Name("树和")`。

---

## 8. 动态语义

### 8.1 动态值

运行时值集合：

```text
数
布尔
爻
卦
树
列
函数
空
```

### 8.2 基础字面量

| 源 | 值 |
|---|---|
| ASCII digits | `数` |
| `真` | `布尔(true)` |
| `假` | `布尔(false)` |
| `空` | `空` |
| `阴` `阳` | `爻` |
| 八经卦 | `卦` |
| `叶 Expr` | `树叶(value)` |
| `枝 Expr 左 Expr 右 Expr 成` | `树枝(value,left,right)` |

树节点值 v0 必须求值为 `数`，否则报 `E061 TreeValueType`。

### 8.3 作用域

- 顶层是全局作用域。
- 函数调用创建局部作用域，参数绑定在局部作用域中。
- `令` 在当前作用域中绑定名字；同一作用域重复绑定同名报 `E031 DuplicateName`。
- 内层作用域可以遮蔽外层用户名字，但不能绑定保留名。

### 8.4 函数

`法 名 参数...` 定义函数值。

- 函数可递归：函数名在函数体解析前进入当前作用域。
- 实参数必须等于参数数，否则报 `E042 ArityMismatch`。
- 执行到 `返` 时返回该值。
- 函数体运行结束而无 `返`，返回 `空`。

### 8.5 条件

`若` 条件必须求值为 `布尔`，否则报 `E060 ConditionType`。

`否则` 必须与对应 `若` 同缩进级。

### 8.6 匹配

`观 Expr` 对 `Expr` 的运行时值做模式分派。

v0 树匹配：

- 若值为 `叶 v`，进入 `叶 名` 分支，并绑定 `名 = v`。
- 若值为 `枝 v left right`，进入 `枝 值 左 左名 右 右名` 分支，并绑定三个名字。
- 若值不是树，报 `E062 MatchType`。
- 若缺少对应分支，报 `E050 NonExhaustiveMatch`。

### 8.7 数学算子

| 字 | 参数 | 结果 | 错误 |
|---|---|---|---|
| `加` | 数 数 | 数 | `E063 MathType` |
| `减` | 数 数 | 数 | `E063 MathType`; 结果若为负，v0 报 `E064 NegativeNat` |
| `乘` | 数 数 | 数 | `E063 MathType` |
| `除` | 数 数 | 数 | `E063 MathType`; 除以 0 报 `E065 DivideByZero` |
| `余` | 数 数 | 数 | `E063 MathType`; 除以 0 报 `E065 DivideByZero` |
| `幂` | 数 数 | 数 | `E063 MathType` |
| `等` | 任意同类值 | 布尔 | 跨类比较返回 `假` |
| `小` `大` | 数 数 | 布尔 | `E063 MathType` |

### 8.8 逻辑算子

`不`、`且`、`或` 只接受 `布尔`。

`且`、`或` 短路求值：

- `假 且 X` 不求值 `X`。
- `真 或 X` 不求值 `X`。

### 8.9 树标准算子

标准库必须提供：

| 名 | 签名 | 语义 |
|---|---|---|
| `树和` | 树 -> 数 | 全部节点值求和 |
| `先序` | 树 -> 列 | node, left, right |
| `中序` | 树 -> 列 | left, node, right |
| `后序` | 树 -> 列 | left, right, node |
| `树数` | 树 -> 数 | 节点数 |
| `树高` | 树 -> 数 | 叶高为 1 |

---

## 9. 诊断

诊断必须包含：

- code
- message
- source span
- optional hint

v0 必备诊断：

| Code | 条件 | 示例 message |
|---|---|---|
| `E001 MixedIndent` | 行首空格后出现 tab | `缩进只能使用 tab；行首空格只可作排版。` |
| `E002 BadDedent` | dedent 不匹配历史缩进级 | `缩进级未对齐任何外层块。` |
| `E010 IllegalCharacter` | 字符不在允许集合 | `非法字符。` |
| `E011 SingleEquals` | 出现单独 `=` | `请使用 等 或 ==；绑定使用 为。` |
| `E020 AmbiguousName` | 名字组合无法唯一判断 | `相邻字串有歧义，请用空格分隔。` |
| `E021 ReservedName` | 保留名作为变量 | `此字为语言保留名，不可绑定。` |
| `E030 UnboundName` | 名字未绑定 | `未见此名。` |
| `E031 DuplicateName` | 同一作用域重复绑定 | `此名已在当前作用域中绑定。` |
| `E040 CallNonFunction` | 调用非函数 | `之 的左侧不是函数。` |
| `E042 ArityMismatch` | 实参数不等于形参数 | `函数参数个数不合。` |
| `E050 NonExhaustiveMatch` | 树匹配缺少叶或枝 | `观树必须覆盖叶与枝。` |
| `E060 ConditionType` | 条件不是布尔 | `若 的条件必须为布尔。` |
| `E061 TreeValueType` | 树节点值不是数 | `树节点值必须为数。` |
| `E062 MatchType` | 非树进入树模式匹配 | `观 的值不是树。` |
| `E063 MathType` | 数学算子参数不是数 | `数学算子只接受数。` |
| `E064 NegativeNat` | 自然数减法产生负数 | `数为自然数，减法结果不可为负。` |
| `E065 DivideByZero` | 除以 0 或余 0 | `不可除以零。` |

---

## 10. 标准库附录：六十四卦

v0 核心语法只保留八经卦。六十四卦作为标准库常量表，不是语法关键字。

标准库应至少预留下列常量名，具体卦值按传统序卦表：

```text
乾 坤 屯 蒙 需 讼 师 比 小畜 履 泰 否
同人 大有 谦 豫 随 蛊 临 观 噬嗑 贲 剥 复
无妄 大畜 颐 大过 坎 离 咸 恒 遁 大壮 晋 明夷
家人 睽 蹇 解 损 益 夬 姤 萃 升 困 井 革 鼎
震 艮 渐 归妹 丰 旅 巽 兑 涣 节 中孚 小过 既济 未济
```

其中八个重卦名 `乾 坤 坎 离 震 艮 巽 兑` 与八经卦同字。上下文需要六爻卦时，标准库应提供显式转换或构造；v0 不把这种重载放进语法核心。

---

## 11. 验收样例

### 11.1 八卦字面量归一化

源码：

```text
令 甲 为 乾
令 乙 为 離
令 丙 为 兌
```

预期：

- `乾` 解析为核心卦值 `乾`。
- `離` 归一为 `离`。
- `兌` 归一为 `兑`。

### 11.2 数学别名 AST 等价

源码 A：

```text
1 + 2 * 3
```

源码 B：

```text
1 加 2 乘 3
```

二者必须生成同一 AST：

```text
Binary(加,
  Number(1),
  Binary(乘, Number(2), Number(3)))
```

运行结果为 `7`。

### 11.3 空格不改变 AST

源码 A：

```text
令 甲 为 1 加 2
甲 加 3
```

源码 B：

```text
令    甲    为    1   加   2
甲       加       3
```

二者 AST 必须相同。

### 11.4 树求和

源码：

```text
令 甲 为 枝 5 左 枝 2 左 叶 1 右 叶 3 成 右 叶 4 成
树和 之 甲
```

预期结果：

```text
15
```

### 11.5 递归函数写树遍历

源码：

```text
法 求和 树
	观 树
		叶 值
			返 值
		枝 值 左 左树 右 右树
			返 值 加 求和 之 左树 加 求和 之 右树

令 甲 为 枝 5 左 枝 2 左 叶 1 右 叶 3 成 右 叶 4 成
求和 之 甲
```

预期结果：

```text
15
```

### 11.6 必备错误样例

混合缩进：

```text
法 甲
 	返 1
```

必须报 `E001 MixedIndent`。

保留字作变量：

```text
令 乾 为 1
```

必须报 `E021 ReservedName`。

未绑定变量：

```text
甲 加 1
```

必须报 `E030 UnboundName`。

调用非函数：

```text
令 甲 为 1
甲 之 2
```

必须报 `E040 CallNonFunction`。

模式不覆盖树形：

```text
法 求和 树
	观 树
		叶 值
			返 值
```

必须报 `E050 NonExhaustiveMatch`。

---

## 12. 实现顺序建议

1. 归一化器：UTF-8 输入 -> canonical 字符流，保留 source map。
2. Lexer：canonical 字符流 -> `Glyph` / `Number` / layout token。
3. Layout checker：tab 缩进栈与 `INDENT` / `DEDENT`。
4. Parser：单字 token 流 -> AST，包含双字/多字名字组合。
5. Name resolver：作用域、保留名、最长名字优先与歧义诊断。
6. Dynamic checker/evaluator：按 §8 实现最小运行语义。
7. Conformance tests：跑 §11 全部样例。

任何扩展必须先更新本规范，再更新实现和验收样例。
