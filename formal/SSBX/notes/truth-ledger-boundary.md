# Truth / ClaimLedger / Absolute claim strength audit

Scope: audit of the current Lean chain
`SSBX.Truth.Basic` -> `SSBX.Truth.ClaimLedger` ->
`SSBX.Truth.Semantics` -> `SSBX.Truth.Adequacy` ->
`SSBX.Truth.Absolute`, with `SSBX.Model.Adequacy` as the optional model bridge.

This note is descriptive. It does not change Lean source.

## Bottom line

The strongest defensible reading of the current formal chain is:

> Given an inhabited `SSBXAxiomLedger`, Lean constructs an
> `AbsoluteTruthCertificate SSBXTheory` whose registered claims have formal
> semantic coverage, whose text/operator registries are covered, and whose
> finite recommendation cases compute to `Tri.top`.

It is not a no-premise proof that reality itself is fully captured. The word
`AbsoluteTruth` is a formal certificate name; the theorem
`ssbx_absolute_truth : SSBXAxiomLedger -> AbsoluteTruth SSBXTheory` is explicitly
ledger-dependent.

## Claim status classes

The status constructors are declared in `Truth.Basic`:

- `machineChecked`
- `ledgerDependent`
- `modelComputed`
- `registryChecked`
- `pending`

Current `ClaimLedger.claimEntry` usage:

| Status | Current claims |
|---|---|
| `machineChecked` | `triValueConservativity`, `generatedRootsDiscipline`, `recursiveSemanticsDiscipline`, `rosterTextComplete`, `wenyanOperatorTableComplete`, `semanticAdequacyClaim`, `rootToSsbxLiClaim` |
| `ledgerDependent` | `openDefinition`, `closeDefinition`, `rightDefinition`, `wrongDefinition`, `goodDefinition`, `badDefinition`, `freedomDefinition`, `flourishingDefinition`, `yiDefinition`, `shanDefinition`, `renDefinition`, `daoDefinition`, `trueDaoDefinition`, `auditUnbrokenDefinition`, `omegaInterface`, `omegaBInterface`, `piOpenInterface`, `thresholdProtocol`, `sourceTextClaimMapping`, `openValueAxiomClaim`, `auditReliabilityAxiomClaim`, `omegaAdequacyAxiomClaim`, `omegaBAdequacyAxiomClaim`, `piOpenAdequacyAxiomClaim`, `truthPathAxiomClaim`, `recommendationI2CandidateTrueDao`, `absoluteTruthClaim` |
| `modelComputed` | `recommendationI1Evil`, `recommendationI2Right`, `recommendationI2Ren`, `recommendationI3ProtectiveClosure` |
| `registryChecked` | unused in the current claim ledger |
| `pending` | unused in the current claim ledger |

Notes:

- The two registry-kind claims, `rosterTextComplete` and
  `wenyanOperatorTableComplete`, are currently marked `machineChecked`, not
  `registryChecked`. That is defensible if the intended meaning is "Lean checked
  finite registry coverage"; otherwise the ledger should later distinguish
  registry coverage status from theorem status.
- `pending` exists as a status constructor and there are pending nodes elsewhere
  in the roster/diagram layer, but no current `ClaimId` entry is marked pending.
- `recommendationI2CandidateTrueDao` is marked `ledgerDependent`, while
  `RecommendationCaseTruth` is currently built by `rfl` through
  `recommendationVerdict`. If "candidate true dao" is intended to depend on
  `truth_path_axiom`, the current certificate does not enforce that dependency.

## Machine-checked status boundary

`SSBX.Truth.ClaimLedger` now exposes the current status boundary as small Lean
objects rather than prose only:

- `machineCheckedClaims`
- `ledgerDependentClaims`
- `modelComputedClaims`
- `registryCheckedClaims`
- `pendingClaims`
- `ClaimsWithStatus`

For each status list there is an `_exact` theorem proving equivalence with
`(claimEntry id).status`. The current ledger also proves:

- `claimEntry_status_current`: every `ClaimId` currently has status
  `machineChecked`, `ledgerDependent`, or `modelComputed`.
- `currentStatusClaims_complete`: every `ClaimId` is in one of the three
  nonempty current status lists.
- `no_registryChecked_claimEntry` / `no_formal_claim_registryChecked`:
  no registered claim currently uses `registryChecked`.
- `no_pending_claimEntry` / `no_formal_claim_pending`: no registered claim
  currently uses `pending`.

This proof direction is correct and useful as a regression boundary: if
`claimEntry` changes without updating the status lists, `lake build
SSBX.Truth.ClaimLedger` should fail.

It should not be strengthened into a semantic classification theorem saying,
for example, that every registry-kind claim must have `registryChecked` status,
or that every recommendation verdict that computes by `rfl` must be
`modelComputed`. The current design intentionally records claim-specific audit
strength as ledger metadata. Two examples show why a stronger classification
would be misleading today:

- `rosterTextComplete` and `wenyanOperatorTableComplete` have kind `registry`
  but status `machineChecked`.
- `recommendationI2CandidateTrueDao` computes in `RecommendationCaseTruth`, but
  is marked `ledgerDependent` because the intended "true dao" reading carries a
  ledger/path dependency.

So the defensible theorem is an exact finite audit of current status assignments,
not a universal law from `ClaimKind` or model-computation shape to `TruthStatus`.

## What semantic adequacy proves

`semantic_adequacy_complete` proves, for every `ClaimId`, a nonempty
`SemanticAdequacy id`. The two components are:

- `HasFormalSemantics id`: the generated `FormalSemantics` has the same id and
  its `source` is not `uninterpreted`.
- `SourceClaimMapped id`: the ledger entry has nonempty `sourceRef`.

Therefore this layer proves registration and formal semantic coverage. It does
not prove that every ledger-dependent or model-facing claim is true in the
external world. For many claims the semantic term is only a predicate label,
interface name, theorem reference, or finite case judgement.

## AbsoluteTruthCertificate dependencies

`AbsoluteTruthCertificate` has these fields:

| Certificate field | Current provider in `absolute_truth_certificate` | Dependency strength |
|---|---|---|
| `ledger` | the input `L : SSBXAxiomLedger` | stores the whole ledger |
| `ledger_holds` | `ledger_axioms_hold L` | copies all proof fields already carried by `L` |
| `all_claims_semantically_adequate` | `semantic_adequacy_complete` | machine-checked coverage over registered `ClaimId`s |
| `roster_text_complete` | `SSBX.Text.Completeness.roster_text_complete` | machine-checked registry coverage |
| `operator_table_complete` | `SSBX.Text.Completeness.operator_table_complete` | machine-checked registry coverage |
| `recommendation_case` | `recommendation_case_truth L` | finite computation by `rfl`; the argument `L` is unused |

The ledger fields actually copied by `ledger_axioms_hold L` are all nine
axiom/proof pairs in `SSBXAxiomLedger`:

- `open_value_axiom` / `open_value_holds`
- `audit_reliability_axiom` / `audit_reliability_holds`
- `omega_adequacy_axiom` / `omega_adequacy_holds`
- `omegaB_adequacy_axiom` / `omegaB_adequacy_holds`
- `pi_open_adequacy_axiom` / `pi_open_adequacy_holds`
- `threshold_reliability_axiom` / `threshold_reliability_holds`
- `truth_path_axiom` / `truth_path_holds`
- `text_adequacy_axiom` / `text_adequacy_holds`
- `case_data_reliability_axiom` / `case_data_reliability_holds`

No individual field is inspected semantically in `Truth.Absolute`; they are
accepted as premises packaged inside `L`. Thus `truth_depends_on_ledger L` proves
that a fully supplied ledger yields a certificate, not that the ledger itself is
externally established.

## Model bridge

`Model.Adequacy` provides a possible grounding route:

- `AdequateModel` packages model adequacy principles.
- `ModelSupportsLedger A L` maps selected model principles into the nine ledger
  axioms.
- `ledger_from_adequate_model A L S` produces `LedgerAxiomsHold L`.
- `model_grounded_truth_certificate A L S` stores both the model support and
  `absolute_truth := truth_depends_on_ledger L`.

This bridge is still premise-bearing: an adequate model and support maps must be
provided. The absolute-truth theorem itself does not compute those support maps.

## README wording boundary

The current README heading "真理 -- 此卷所证, 即真理" and nearby prose overstate the
Lean result if read literally. A defensible replacement is:

```markdown
### 9.1 有界真理 claim -- 账本条件下的形式证书

此卷在 Lean 中证明的是有边界的体系内 claim：给定 `SSBXAxiomLedger`
的九组前提及其 `holds` 证明，系统可构造
`AbsoluteTruthCertificate SSBXTheory`。该证书覆盖已登记 claim 的形式语义、
名册文字覆盖、文言算子覆盖，并对有限推荐案例给出计算结果。

因此可防御地说：在明示账本、注册表和 64 元形式模型边界内，相关 registered
claims 得到机器检查的覆盖与条件性证书。将其称为 reality 的 actual structure，
或外推到任何自然/心理/社会 dynamics，仍依赖模型充分性、经验校验与跨文本/跨域
论证；这不是当前 Lean 链条单独给出的无前提结论。

> 在内部一致性、公理账本成立且模型支持被给出的前提下，`ProcessAligned`
> 的持续性结论是体系内形式 claim；其现实解释范围由这些前提决定。
```

English README analogue:

```markdown
### 9.1 Bounded truth claim -- a ledger-conditioned formal certificate

What Lean proves here is not premise-free Truth, but a bounded in-system claim:
given an `SSBXAxiomLedger` with its nine premise/proof pairs, the system
constructs an `AbsoluteTruthCertificate SSBXTheory`. External reality claims
remain model-adequacy and evidence-dependent.
```

## ConcreteLedger task B boundary

`SSBX.Model.ConcreteLedger` adds a minimal toy support example without changing
the abstract truth chain. The model is the existing `unitModel`: all fields,
intervals, scales, windows, and states are `Unit`, `validIntervals` returns the
single interval, `step` preserves the unit field, and `omega`, `omegaB`, and
`audit` return `Tri.top`.

The toy adequate model makes each adequacy principle a small proposition about
that channel, for example:

- `predictive`: every `omega` query returns `Tri.top`.
- `auditable`: every audit query returns `Tri.top`.
- `bounded_error`: no `omega` query returns `Tri.bot`.
- `cross_sample_stable` and `plural_check`: `omegaB` is stable at `Tri.top`.
- `domain_bounded` and `intervention_capable`: the unit model has exactly the
  singleton interval behavior and stepping preserves the field.
- `reproducible`: repeated audit queries are equal.

For this toy ledger, all nine ledger fields are concretely supported by choosing
each ledger proposition to be the corresponding adequacy proposition:

| Ledger field | Toy support principle |
|---|---|
| `open_value_axiom` | `intervention_capable` |
| `audit_reliability_axiom` | `auditable` |
| `omega_adequacy_axiom` | `predictive` |
| `omegaB_adequacy_axiom` | `plural_check` |
| `pi_open_adequacy_axiom` | `comparable` |
| `threshold_reliability_axiom` | `bounded_error` |
| `truth_path_axiom` | `cross_sample_stable` |
| `text_adequacy_axiom` | `domain_bounded` |
| `case_data_reliability_axiom` | `reproducible` |

That proof direction is correct in Lean because the ledger proposition and the
model principle are definitionally the same proposition in `toyLedger`, so each
`ModelSupportsLedger` field is an identity-style implication.

What remains premise-bearing is the general, non-toy reading. If a future ledger
uses stronger domain propositions, such as real empirical audit reliability,
textual adequacy over a corpus, or cross-sample truth-path adequacy, the current
types still require explicit support maps from model principles to those ledger
claims. `ConcreteLedger` does not prove that the unit toy model is externally
adequate, nor that the nine real-world ledger claims follow from the abstract
principle names alone. It only proves that the bridge is inhabitable when the
ledger is intentionally defined at the same formal strength as the toy model's
adequacy propositions.
