# Wen Lisp / WenScript Demos

These examples show the current execution boundary.

## Runnable Lisp

```bash
wen-lisp run examples/wen-lisp/demo-lisp-algorithm.wen --trace --fuel 256
```

Shows:

- immutable global snapshots captured by closures;
- curried lambda over 64-word variable names;
- V4-native `compose` / `v4-eq`;
- Word64 `wordCompose`;
- provisional R5-slice predicates and coordinate projection.

```bash
wen-lisp run examples/wen-lisp/demo-lisp-homoiconic-boundary.wen --trace --fuel 128
```

Shows:

- quoted symbols and scalar `eval` work;
- compound surface lists are still data at this boundary;
- full macro/source-list evaluation is not implemented yet.

## Runnable WenScript

```bash
wen-lisp prove examples/wen-lisp/demo-shengsheng-buxi-proof.wen --trace
```

Shows:

- a controlled “生生不息” proof-script;
- provisional R5 certificates for `生` and `息`;
- V4/R6 action loops such as `错 之 乾 => 坤` and `错 之 坤 => 乾`;
- text-layer claims remain typed syntax, not fake theorems.

```bash
wen-lisp prove examples/wen-lisp/demo-wen-action-syntax.wen --trace
```

Shows:

- new WenScript action syntax, not Lisp;
- `错/综/错综/道 之 <64-word>` is evaluated through the V4 action on R6;
- trace prints both the typed `operatorApp` and the computed `v4Action`.

```bash
wen-lisp prove examples/wen-lisp/demo-root512-operators.wen --trace
```

Shows:

- Root512 syntax, not Lisp;
- `恒/印/投/印投 之 <64-word>` is evaluated through
  `Root512 = (Word64 × V4) × {cell, operator}`;
- these root applications are separate from V4/R6 actions such as `错 之 乾`.

```bash
wen-lisp prove examples/wen-lisp/demo-wenscript-diagnostics.wen --trace
```

Shows:

- a controlled semantic certificate for `生生不息者往复而不穷也`;
- controlled implication certificates for executable conditions such as
  `若错之乾则坤` and `若不之乾则坤`;
- state-aware implication over already controlled certificates, such as
  `若文不离道则有可证` when `文即理` and `理即道` are in scope;
- compact application syntax such as `错之乾`, `印之乾`, and `不之乾`;
- `有可证` becomes a certificate-availability event once earlier certificates
  exist;
- `有未证` reports that the preceding diagnostics are intentional open proof
  obligations;
- located diagnostics for unsupported implication proof, unsupported
  application grammar, and unknown 64-word arguments such as `龘龘`.
- `--strict` can be used to fail the command when such diagnostics remain.

```bash
wen-lisp prove examples/wen-lisp/demo-wenscript-strict-ok.wen --strict --trace
```

Shows:

- a strict-clean controlled WenScript file;
- semantic certificates, transitive-alias-backed `文不离道`,
  alias-backed copula such as `文为道`, certificate-backed `有可证`,
  state-aware implication, plus executable V4/Root512 applications with
  action-trace certificates;
- nested executable application such as `错之综之乾`;
- `无未证` records a clean frontier at that point in the script;
- zero diagnostics and zero claim stubs.
- `--strict-proved` is stricter than this demo: it also fails while
  registration-only semantic certificates remain.

```bash
wen-lisp prove examples/wen-lisp/wen-daodejing.wen --strict-proved --trace
```

Shows:

- the generated controlled-wen Daodejing file;
- zero diagnostics, zero claim stubs, and zero registration-only certificates;
- typed schema certificates for `X不为Y而Y以之P`, including
  `道不为物而物以之成形`;
- typed capability schema certificates for `X可被A故有B` and `X能A乃B`,
  including `文可被读故有解释` and `文能生文乃编`;
- typed structural and V4-duality schema certificates, including
  `一字在文中为名`, `六位成卦`, `每格有其卦`, `位可组合`,
  `乃一事之四读`, and `意义由此有骨`;
- typed discourse schema certificates, including `无德则道但为空名`,
  `程序若自其规则而行`, and `使后文承前文之证`;
- exact controlled bridges for V4 duality, Root512/R-structure, name/value
  laws, and proof-boundary discipline;
- exact bridges are registry-backed controlled rows in `WenScript.lean`, so
  this example is strict-proved without treating arbitrary prose as theorem.

```bash
wen-lisp prove examples/wen-lisp/demo-wenscript-universal-schema.wen --trace
```

Shows:

- controlled universal schema `凡文皆可证`;
- explicit schema instance `验 文 为可证`;
- `universalSchema` and `universalInstantiation` semantic certificates;
- report-backed `有可证` after earlier controlled certificates exist;
- evidence-backed `读之则验`;
- compatibility with current R5 `验 <name> 为五爻` verification syntax.

```bash
wen-lisp prove examples/wen-lisp/demo-wenscript-operator-boundary.wen --trace
```

Shows:

- R5 definitions still produce certificates;
- `错 之 乾` and `综 之 既济` are V4-carried operator applications;
- text-layer operators such as `不` and `有` are typed as catalogue operators,
  not V4-executed proofs;
- unknown prose can remain a `barePhrase` instead of becoming a fake theorem.

## Expected Failure

```bash
wen-lisp run examples/wen-lisp/demo-expected-failure-recursion.wen --trace --fuel 64
```

Expected result: evaluation fails with exit code 3.

This demonstrates that `define` is non-recursive. Recursive bindings, recursive
macros, and VM/metaInterp self-hosting remain later boundaries.
