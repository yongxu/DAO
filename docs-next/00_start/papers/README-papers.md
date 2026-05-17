# `docs-next/00_start/papers/` — README

Submission package for the GUT-C paper. Generated 2026-05-17.

---

## File inventory

| File | Purpose | Status | Notes |
|---|---|---|---|
| `gut-c-tac-submission.md` | Canonical 26 k-word markdown source for the GUT-C TAC paper. | Source of truth | Do not edit casually; this is the canonical reference. |
| `gut-c-tac-submission.tex` | LaTeX conversion (`article` class, swap-ready for `tac`/`lmcs2e`/`cambridge6`). | Draft v0.1 | Best-effort conversion from the `.md`; hand polish needed before submission. |
| `gut-c-tac-submission.bib` | BibTeX bibliography for the LaTeX source. | Draft v0.1 | ~60 entries covering all `\cite{...}` keys in the `.tex`. |
| `cover-letter-draft.md` | Editor cover letter (draft, ~1280 words). | Draft v0.1 | Trim to ~800 words for final submission. |
| `mathlib-pr-1-elementary-topos.md` | PR proposal: `ElementaryTopos` bundling (PR-1 of §7.4). | Earlier draft | Independent of this submission. |
| `mathlib-pr-2-lawvere-theory.md` | PR proposal: `LawvereTheory` + `Model` API (PR-2 of §7.4). | Earlier draft | Independent of this submission. |
| `README-papers.md` | This file. | — | — |

---

## Conversion approach (md → tex)

The LaTeX conversion uses the standard `article` class, parameterised so it can be swapped for venue-specific classes (`tac`, `lmcs2e`, `cambridge6`) by changing one line. Key structural choices:

1. **Math.** All inline `$…$` and display `$$…$$` markdown blocks transcribed as LaTeX math; common Unicode (`δ`, `ε`, `⊗`, `≅`, `⊥`, `⊤`, etc.) re-rendered as `\delta`, `\varepsilon`, `\otimes`, `\cong`, `\bot`, `\top`. Custom shorthands defined in the preamble (`\TGUT`, `\PauliBase`, `\DiamondH`, `\Sierp`, `\FdHilb`, `\HeytAlg`, `\Frm`, `\FinVect`).
2. **Theorem environments.** Standard `amsthm` setup with `\newtheorem{theorem}{Theorem}[section]`, plus shared counter for `lemma`/`proposition`/`corollary`/`definition`/`example`/`construction`/`conjecture`/`openproblem`/`observation`/`remark`/`notation`. Definition / remark styles split per `\theoremstyle{definition}` / `{remark}`.
3. **Cross-references.** Markdown section refs (`§5.2`, etc.) converted to `\cref{sec:inst:heyting}` etc.; all `\section{...}` blocks carry an explicit `\label{sec:...}` (and similar for tables, theorems, definitions).
4. **Citations.** Markdown `[Pow99]`, `[Law63]`, etc. converted to `\cite{Pow99}`, `\cite{Law63}` keys. Bibliography file `gut-c-tac-submission.bib` provides the entries.
5. **Tables.** Markdown pipe tables converted to `booktabs`-styled `\begin{tabular}` blocks (with `\toprule` / `\midrule` / `\bottomrule`) wrapped in `\begin{table}[h!]` floats with `\caption{...}` and `\label{tab:...}`. Wider tables (Table 4: per-property status) use `\small` or `\scriptsize` font size.
6. **Lean code blocks.** Markdown ` ```...``` ` blocks converted to `\begin{lstlisting}[language=Lean]...\end{lstlisting}` with a `listings` package definition of Lean syntax in the preamble. Unicode tokens that `listings` mis-handles in `pdflatex` mode (e.g., `→`, `≅`, `⟨`, `⟩`, `▶`, `≪≫`) have been transliterated (`->`, `≅` kept where safe; some replaced with ASCII to ensure `pdflatex` compatibility). For `xelatex` builds, the listings could be restored with `fontspec` + a CJK-aware font.
7. **Diagrams.** Two commutative-square diagrams converted to `tikz-cd` blocks (compose-compatibility square in §4.3 and the doctrine-diagram in §6.2 — the latter is rendered as a plain `lstlisting` ASCII art in the current draft and should be re-done in `tikz-cd` before submission).
8. **Lists.** `enumitem` `[leftmargin=*]` style used for both `itemize` and `enumerate` to match the markdown's left-flush appearance.
9. **Hyperlinks.** `hyperref` + `cleveref` for clickable cross-refs and bibliography links.

---

## Known issues / hand-polish list

The LaTeX conversion is **best-effort** rather than press-ready. Items that need attention before final submission:

1. **Lean code Unicode.** A few Lean snippets in the appendix still contain `≅`, `≪≫`, `⊗i`, `≃*`, `▶` etc. These render under `xelatex` with `fontspec` + a Unicode font; under `pdflatex` they need ASCII transliteration. The current `.tex` uses ASCII for compatibility but the result reads less naturally than the source markdown.
2. **CJK content.** The markdown source mentions terms like "道源" / "已" / "今" / "未" (the V₄ Shi labels). These have been transliterated as "Way / Already / Now / Not-yet" in the LaTeX where they appear in flowing prose, but a full polish should ensure consistency.
3. **Diagrams (especially §6.2 doctrine diagram).** Currently rendered as ASCII art in a `lstlisting` block. A proper `tikz-cd` or `forest` diagram would be much more readable and should be drawn before submission.
4. **Table 4 (per-property status).** Wide table; currently fits at `\small`. May need landscape orientation or splitting in some venue classes.
5. **Footnotes vs in-text citations.** The markdown source does not use footnotes; the LaTeX likewise has none, except for the author-affiliation `\thanks{...}` blocks under `\author`. This is fine for TAC; LMCS / MSCS may prefer different affiliation handling.
6. **Bibliography style.** Currently `plain`. TAC uses its own style; LMCS prefers `alpha` or its own; MSCS uses Cambridge style. Swap on final submission per venue.
7. **Cross-reference labels.** All sections have `\label{sec:...}`; a final pass should check that every `\cref{...}` in the body has a matching `\label{...}`. Compile log will flag any undefined refs.
8. **Compile-test environment.** Has not yet been compiled (`pdflatex` / `xelatex` not available in this worktree's environment as of 2026-05-17). A compile pass should be done on a machine with TeX Live + Mathlib-aware Unicode fonts before submission.

---

## Venue switching

To switch the LaTeX file from generic `article` to a venue-specific class:

```latex
% TAC:
\documentclass{tac}

% LMCS:
\documentclass{lmcs2e}    % see https://lmcs.episciences.org/page/instructions-for-authors

% MSCS:
\documentclass{cambridge6} % see https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/information/instructions-for-authors
```

Replace the first `\documentclass{...}` line of `gut-c-tac-submission.tex`. Most other markup should port without change; check theorem environment names and bibliography style in particular.

---

## Word count / page estimate

- **Markdown source:** ~26 000 words (1859 lines)
- **LaTeX file:** ~2 000 lines (preamble + body + appendices)
- **BibTeX entries:** ~60 entries (covering ~85 unique citation keys from the markdown)
- **Cover letter:** ~1 280 words (draft); trim to ~800 for submission.
- **Estimated TAC pages:** 45–55 (at ~600 words / page in TAC formatting).

---

## Build instructions (for reference, once `pdflatex` is available)

```bash
# in this directory:
pdflatex gut-c-tac-submission
bibtex   gut-c-tac-submission
pdflatex gut-c-tac-submission
pdflatex gut-c-tac-submission

# or with xelatex (recommended for Unicode):
xelatex  gut-c-tac-submission
bibtex   gut-c-tac-submission
xelatex  gut-c-tac-submission
xelatex  gut-c-tac-submission
```

For a quick syntax sanity check:

```bash
pdflatex -draftmode -interaction=nonstopmode gut-c-tac-submission.tex 2>&1 | grep -E '(Error|Warning|Undefined)'
```

---

## Open question for next pass

- **Co-author confirmation (Prof. John Power, Macquarie).** The author line currently lists Prof. Power as provisional. The cover letter discusses the contingency. If Power declines, simplify byline to single author and adjust acknowledgments accordingly.
- **ORCID + funding acknowledgment.** Both blank in the current draft; insert before submission.
- **Final venue selection.** Currently drafted for TAC (primary). Confirm before swapping `\documentclass` and bibliography style.
