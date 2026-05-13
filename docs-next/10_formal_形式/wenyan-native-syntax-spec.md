# 文言 Native Algorithm Syntax Spec v0.1

> Status: target syntax spec for pure-wenyan native algorithm files.
> Current implementation covers the quicksort subset; this document fixes the
> next grammar target before extending the parser.
> Lean anchors: `SSBX.Foundation.Wen.WenyanAlgorithms`,
> `SSBX.Foundation.Wen.Native.Surface`, `SSBX.Foundation.Wen.Native.Program`.

## Purpose

This syntax is the controlled pure-wenyan algorithm layer used by:

```bash
wenyan-algorithm <file.wen> [N...]
```

The intended execution chain is:

```text
文言 source
  -> Wenyan AST
  -> Native.SurfaceTopForm 8
  -> Native.TopForm 8
  -> Native.Value 8
```

This is not Lisp / S-expression syntax, and it is not arbitrary classical
Chinese prose.  It is a small line-oriented algorithm language whose forms must
lower audibly to native Wen expressions.

## File Shape

A file is a sequence of function blocks plus optional sample lines.

```text
document ::= item*
item     ::= function | sample | blank
blank    ::= empty line
```

Blank lines are ignored.  No comment syntax is specified in v0.1.

The first function in a file is the default entry function unless the CLI later
adds an explicit entry selector.  A sample line supplies default input only; CLI
arguments override it.

```text
sample ::= "试以" nat-list "。" | "試以" nat-list "。"
```

## Lexical Units

Identifiers are nonempty text fragments that do not contain structural
punctuation:

```text
identifier excludes: 。 ， 、 （ ） whitespace
```

Reserved words cannot be used as identifiers in parsed positions:

```text
法曰 受 若 则 則 否则 否則 归 歸 取 之首 之余 名曰 令 为 為
空 结 並 并 择 擇 折 映 施 于 於 加 零
不大于 大于
```

Numerals accepted at this layer are Arabic numerals and simple Chinese natural
numbers:

```text
nat      ::= arabic-nat | wen-nat
wen-nat  ::= 零 | 一 | 二 | 三 | 四 | 五 | 六 | 七 | 八 | 九 | 十
           | 一十...九十 | 十一...十九 | 二十...九十九
nat-list ::= nat ("、" nat)*
```

## Function Blocks

```text
function ::= header param* stmt+
header   ::= "法曰" identifier "。"
param    ::= "受" parameter-list "。"
parameter-list ::= identifier ("，" identifier)*
                 | identifier ("，受" identifier)*
```

`受函，受列。` and the split spelling below are equivalent after
normalization:

```text
受函。
受列。
```

is treated as:

```text
受函。
受列。
```

Each function lowers to a curried native lambda:

```text
法曰f。
受x，y。
...
```

lowers as:

```text
define f (lambda x (lambda y ...))
```

Top-level lambda definitions are recursive in native evaluation: a function may
call itself by name inside its body.

## Statements

Statements are line-oriented and execute in order.  Every executable path must
end in `归 expr。` or `歸 expr。`.

```text
stmt ::= return-if-empty
       | return-if
       | return-else
       | let-head
       | let-tail
       | let-value
       | return
```

### Empty-list Guard

```text
return-if-empty ::= "若" identifier "空，归" expr "。"
                  | "若" identifier "空，歸" expr "。"
```

Meaning:

```text
if (null identifier) then expr else rest-of-statements
```

### General Conditional Return

```text
return-if   ::= "若" expr "，归" expr "。"
              | "若" expr "，歸" expr "。"
return-else ::= "否则归" expr "。"
              | "否則歸" expr "。"
```

`return-if` may be followed immediately by `return-else`; together they lower
to one native `if0`.  Without `return-else`, the else branch is the remaining
statements.

This form is needed for `择`:

```text
若判施于甲，归结甲于择判乙。
否则归择判乙。
```

### List Destructuring

```text
let-head ::= "取" identifier "之首，名曰" identifier "。"
let-tail ::= "取" identifier "之余，名曰" identifier "。"
```

Meaning:

```text
let target = car source in rest
let target = cdr source in rest
```

The source must be a nonempty native list at runtime.

### Let Binding

```text
let-value ::= "令" identifier "为" expr "。"
            | "令" identifier "為" expr "。"
```

Meaning:

```text
let identifier = expr in rest
```

### Return

```text
return ::= "归" expr "。" | "歸" expr "。"
```

## Expressions

Expressions are parsed by the following precedence, from tightest to loosest.

```text
expr ::= nil
       | numeral
       | identifier
       | application
       | call
       | cons
       | append
       | filter
       | paren-expr
```

### Atoms

```text
nil     ::= "空"
numeral ::= nat | "零"
```

`零` in expression position lowers to native number `0`; `空` lowers to native
nil.

### Function Call

Function call has compact prefix form:

```text
call ::= identifier expr+
```

Examples:

```text
速排小者
映函乙
择判乙
折并始列
```

Parsing rule: the longest known function name is taken as the callee; the
remaining text is parsed as one or more arguments according to function arity.

For v0.1 implementation, known function names are the names introduced by
`法曰...` in the current document plus generated helper names.

### Application

```text
application ::= expr ("施于" | "施於") expr
              | "施" expr ("于" | "於") expr
              | expr ("于" | "於") expr
```

The forms are left-associative.  `施 f 于 x` and `f 施于 x` both lower to native
application:

```text
判施于甲       => 判 甲
施函于甲       => 函 甲
```

This supplies ordinary higher-order application for `映/择/折`.

### Cons

Two spellings are accepted:

```text
cons ::= "结" expr "于" expr
       | "结" expr expr
```

Examples:

```text
结甲于择判乙
结枢空
```

Both lower to native `cons`.

### Append

```text
append ::= ("并" | "並") expr ("、" expr)+
```

Example:

```text
并速排小者、结枢空、速排大者
```

This lowers to generated native helper `append`.

### Filter

The compact filter form is retained for quicksort:

```text
filter ::= ("择" | "擇") "（" predicate "）" expr
predicate ::= "不大于" identifier | "大于" identifier
```

Examples:

```text
择（不大于枢）余
择（大于枢）余
```

They lower to generated native helpers `filterLe` and `filterGt`.

The general higher-order `择判乙` form is a normal function call and should be
preferred once `择` itself is defined in the document.

### Fold And Add

`折` is not primitive syntax.  It is an ordinary function name.  The expression:

```text
折加零列
```

is parsed as:

```text
(((折 加) 零) 列)
```

`加` lowers to native numeric addition as a function value.

### Parentheses

```text
paren-expr ::= "（" expr "）"
```

Parentheses group expressions only.  They do not introduce tuples.

## Native Lowering Contract

The parser must not evaluate source terms directly.  It must lower to native
forms and then call native evaluation:

```text
ParsedSource + input
  -> List (Native.SurfaceTopForm 8)
  -> List (Native.TopForm 8)
  -> Native.Program.evalTopFormsFinalFuel
```

Generated helper definitions may be prepended to the program.  In v0.1 these
helpers are:

```text
append xs ys
filterLe pivot xs
filterGt pivot xs
```

All helpers are ordinary native recursive functions.  They are not special
Lean-side evaluator branches.

Name lowering is document-local and deterministic:

```text
first seen identifier -> next nonzero Cell 8
```

The origin cell is reserved and must not be assigned to source identifiers.

## Current Implementation Boundary

Implemented now:

- quicksort block syntax: `法曰/受/若...空/取...首余/令...为/归/试以`.
- compact `并`, compact `结`, compact `择（不大于...）`, `择（大于...）`.
- lowering to native `SurfaceTopForm 8 / TopForm 8`.
- native recursive top-level lambdas.
- native numeric comparisons `numLe / numLt`.

Specified next:

- `否则/否則`.
- multi-parameter `受`.
- general compact function calls with known arity.
- application particle `施/于/於`.
- first-class function parameters needed by `映/择/折`.
- `加` and `零` expression forms.

Out of scope for v0.1:

- arbitrary prose.
- mutation or assignment after `令`.
- pattern matching beyond `取...之首/之余`.
- user-defined infix precedence.
- comments.
- stable global hashing of names across files.

## Acceptance Examples

The following quicksort must parse, lower, and run:

```text
法曰速排。
受列。
若列空，归空。
取列之首，名曰枢。
取列之余，名曰余。
令小者为择（不大于枢）余。
令大者为择（大于枢）余。
归并速排小者、结枢空、速排大者。

试以三、一、二、一。
```

The following list basics are the next parser target:

```text
法曰映。
受函，受列。
若列空，归空。
取列之首，名曰甲。
取列之余，名曰乙。
归结施函于甲于映函乙。

法曰择。
受判，受列。
若列空，归空。
取列之首，名曰甲。
取列之余，名曰乙。
若判施于甲，归结甲于择判乙。
否则归择判乙。

法曰折。
受并，受始，受列。
若列空，归始。
取列之首，名曰甲。
取列之余，名曰乙。
归折并（并始甲）乙。

法曰和。
受列。
归折加零列。
```
