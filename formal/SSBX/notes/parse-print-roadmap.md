# WenyanParser parse-print roadmap

## Claim boundary

The unrestricted theorem

```lean
parseProg (lex (printProg p)) = some p
```

is false as stated, modulo the existing public API shape where `lex` returns
`Option (List Tok)`.  The top-level statement should be written as:

```lean
∀ p, validProg p = true → «解程» («印程» p) = some p
```

The necessary well-formedness condition is exactly the current `validProg`:
every `branchYaoEq`, `branchShiEq`, and `jump` target must satisfy
`1 ≤ t ∧ t ≤ 64`.  This is not cosmetic.  `printNumeral 0` and
`printNumeral n` for `n > 64` print `«?»`, and `parseNumeral "?" = none`, so
those programs cannot round-trip.

## Implemented in `WenyanParser.lean`

The file now contains a complete finite universe of valid single instructions:

* 7 nullary instructions
* 3 `setShi`
* 6 `flipYao`
* 6 * 6 * 64 `branchYaoEq`
* 3 * 64 `branchShiEq`
* 64 `jump`

This universe has length 2576 and is mechanically checked by:

```lean
validInstrUniverse_length
validInstrUniverse_all_valid
validInstrUniverse_singleton_roundtrip
```

The file also records concrete boundary witnesses:

```lean
jump_zero_print_not_roundtrip
jump_65_print_not_roundtrip
```

Together with the existing multi-instruction tests, this proves the most
important finite surface: every valid single instruction shape and every
invertible Nat target round-trips through the public `printInstr`/`«解程»`
entry points.

## Remaining proof plan

To turn the finite surface into the full list theorem, prove these reusable
lemmas in order:

1. `parseNumeral_printNumeral` under `1 ≤ n ∧ n ≤ 64`.
   This is the only arithmetic-heavy piece; split into the printer branches
   `1..9`, `10`, `11..19`, `20..64` with remainder zero/nonzero.

2. `lex` prefix/append lemmas for printed tokens.
   The current lexer is total, but the `«... »` branch carries termination
   evidence that makes dependent rewrites awkward.  A fuel-indexed lexer helper
   would likely make these lemmas much easier while preserving the public
   `lex` behavior.

3. `parseInstr_printInstr`:
   for any `i`, `validInstr i = true` implies the printed instruction lexes to
   tokens that `parseInstr` consumes as `i`.

4. `parseProgFuel` monotonic/enough-fuel lemma:
   parsing a printed program succeeds when the supplied fuel is at least the
   printed token program length.

5. Main induction over `List YiInstr`:
   use `List.all_cons` on `validProg`, the instruction lemma for the head, and
   the induction hypothesis for the tail.

The final theorem should keep the existing public entry semantics unchanged:

```lean
theorem parse_print_valid (p : List YiInstr) :
    validProg p = true → «解程» («印程» p) = some p
```

## Closed in v3.1 (M1 v3.1)

The character-level lex inversion is now fully proved (no hypothesis):

* `WenyanParserGeneral.lean § lexN_printProg_thm` — `lexN (printProg p) = some (tokensOfProg p)` for valid `p`.
* `WenyanParserGeneral.lean § parseN_printProg_inverse_universal` — `«解程N» («印程» p) = some p` for valid `p` (theorem, not conditional).

Proof structure (≈190 lines):
* § 2.5 lex fuel monotonicity, splitOnClose lemmas, `lexFuel_bracket_group`, whitespace/separator skip
* § 5.5 `printInstrChars`/`printShiChars`/`printYaoChars`/`printNumeralChars` + bridge `(printInstr i).toList = printInstrChars i`
* § 5.6 12-constructor `lexFuel_printInstrChars_app` per-instr bridge
* § 9 `progLexFuel`, `lexFuel_printProg_exact` (structural induction over `List YiInstr`), `progLexFuel_le_length`, final `lexN_printProg_thm` via `lexFuel_mono`
