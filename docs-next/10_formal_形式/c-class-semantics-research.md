# C-class operator semantics research (12 ops)

> Sub-plan **06** of the Wen language stack restructure (wen-restructure 2026-05-17).
> Pure research — no `.lean` modification. Sets the stage for a potential follow-up
> sub-plan `01b-C-to-A-upgrade.md` that promotes any C→A candidates identified here.

## Context

After PR #29, `WenSurface/Semantics.lean §1.2` registers **46** placeholder-body
operators via `relationPredicateBoolOperatorIds`
([Semantics.lean:343-360](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean#L343)),
each routed to one of two stub bodies:

- `hexPredTrueBody := λ x : Hex. true` ([Semantics.lean:331-332](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean#L331))
- `hexRelEqBody := .eqHex` ([Semantics.lean:337-338](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean#L337))

Multi-plan research (see `wen-language-roadmap.md`) split these 46 into three buckets:

- **A-class (6 ops)** — Defensible exact Hex semantics; upgrade in sub-plan **01**:
  `D_5, D_6, D_7, K_4, F_12, Z_4`.
- **B-class (28 ops)** — True axiom: Mohist/School definitional content, not
  reducible to a `Hex^k → Hex/Bool` total function. Get an explicit axiom-interface
  registry in sub-plan **01**:
  `P_1, P_14, P_15, P_16, P_17, P_20, G_3, G_6, G_10,
   R_1, R_2, R_7, R_9, R_10, C_1, I_9, K_2, K_3,
   ZHU_1, CHU_10, ZA_13, ZA_14, ZA_15, ZA_16, ZA_17, ZA_18, ZA_19, ZA_20`.
- **C-class (12 ops)** — *Researched here* — semantically uncertain at PR #29.

The 12 C-class ops are obtained by set-difference against A and B:

| OperatorId | 字 | `(SignatureKind, arity)` from `catalogueSignatureShapeFor` |
|---|---|---|
| `R_3` | 際 / 际 | `(.binaryPoint, 2)` ([OperatorSignatures.lean:401](../../formal/SSBX/Text/OperatorSignatures.lean#L401)) |
| `R_4` | 間 / 间 | `(.binaryPoint, 2)` ([OperatorSignatures.lean:402](../../formal/SSBX/Text/OperatorSignatures.lean#L402)) |
| `C_3` | 容 | `(.containment, 2)` ([OperatorSignatures.lean:416](../../formal/SSBX/Text/OperatorSignatures.lean#L416)) |
| `B_8` | 節 / 节 | `(.boundary, 1)` ([OperatorSignatures.lean:456](../../formal/SSBX/Text/OperatorSignatures.lean#L456)) |
| `L_4` | 形名 (paired) | `(.relation, 2)` ([OperatorSignatures.lean:603](../../formal/SSBX/Text/OperatorSignatures.lean#L603)) |
| `Y_20` | 順 / 逆 | `(.relation, 2)` ([OperatorSignatures.lean:635](../../formal/SSBX/Text/OperatorSignatures.lean#L635)) |
| `Z_14` | 居 | `(.relation, 2)` ([OperatorSignatures.lean:673](../../formal/SSBX/Text/OperatorSignatures.lean#L673)) |
| `Z_15` | 處 / 处 | `(.relation, 2)` ([OperatorSignatures.lean:674](../../formal/SSBX/Text/OperatorSignatures.lean#L674)) |
| `Z_39` | 識 / 识 | `(.predicate, 1)` ([OperatorSignatures.lean:698](../../formal/SSBX/Text/OperatorSignatures.lean#L698)) |
| `Z_40` | 知 (作算子) | `(.relation, 2)` ([OperatorSignatures.lean:699](../../formal/SSBX/Text/OperatorSignatures.lean#L699)) |
| `LIJ_6` | 節 / 节 | `(.boundary, 2)` ([OperatorSignatures.lean:741](../../formal/SSBX/Text/OperatorSignatures.lean#L741)) |
| `LIJ_9` | 誠 / 诚 | `(.identity, 2)` ([OperatorSignatures.lean:744](../../formal/SSBX/Text/OperatorSignatures.lean#L744)) |

> **Note on the 12th op (`Z_40`).** Sub-plan 01's prose ("B-class 28 个") lists
> 30 IDs in B. The diff math forces *two* of those to be reclassified into C if
> `|C| = 12` is to hold. We take `LIJ_9` (誠 — cross-time identity, hard to fix
> exactly) and `Z_40` (知 — cognitive verb paired with Z_39 識) as the natural
> C-class members; the remaining 28 in B are the genuine school-axiom set.

### Per-op decision template

Each entry below answers:

1. **Classical source** (1-2 sentence quote from `wenyan-operators.md`).
2. **Possible Hex-finite semantics** — does the *operational* description reduce
   to a total `Hex^k → Hex/Bool` function?
3. **Decision** — `A (upgrade)` / `B (true axiom)` / `C-still (uncertain)`.
4. If **A** — recommended `Stdlib` body + 5-line rationale + a `native_decide`
   sanity check we would add (not run here).
5. If **B** — school axis + rationale why not reducible.
6. If **C-still** — what classical research / Lean infrastructure we still need.

---

## 1. `R_3` 際 / 际 — Binary boundary

- **Classical source**
  ([`wenyan-operators.md:94-98`](../../wenyan-operators.md#L94)):
  > 易·泰「无平不陂，无往不复」释为「天地际也」。
  > 接界算子 — 两结构相接处。这是 间 的近邻，但更强调"接缝"。

- **Signature** at catalogue level: `binaryPoint/2` — two args produce a
  "boundary point" carrier. `Reading.lean` does not catalogue 際 as a
  context-disambiguated reading.

- **Hex-finite reduction attempt.** Geometrically: take two `Hex` values
  `x, y : Hex` and produce a "seam" `Hex`. The simplest candidate is
  `pairHBody : Hex → Hex → Hex × Hex` (already used by `R_12 偶`, `R_13 並`,
  etc. — [Semantics.lean:411-415](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean#L411)),
  which carries the unordered pair as the "boundary witness." `R_3` differs
  from `R_4` (間, interior region) in that 際 is the *contact set* — but at the
  `Hex` level both reduce to "form the pair carrier."

- **Decision: `A (upgrade)`**.

- **Recommended body**: `Stdlib.pairHBody`
  ([`WenDef.lean:871`](../../formal/SSBX/Foundation/Wen/WenDef.lean#L871)), arity 2.

- **Rationale (5 lines)**.
  1. 際 takes two `Hex`s and returns the boundary witness; the boundary of
     `(x, y)` is fully determined by `(x, y)` itself with no extra data.
  2. `pairHBody` is the canonical "binary carrier" stdlib body and is already
     used for *every* other `(binaryPoint, 2)` op upgraded in PR #29.
  3. The "edge vs interior" distinction between 際 and 間 lives at the
     `Reading.lean` annotation layer, not at the `Hex → Hex → α` reduction.
  4. No new `Tm` AST node is needed; the existing `.pairH` constructor and
     `pairHBody_typed` theorem suffice.
  5. The upgrade does not commit us to *spatial topology* — it commits us to
     "the boundary is exactly the unordered pair of incident sides."

- **`native_decide` sanity (proposal, not run)**:
  ```lean
  example : (coreTheoremBackedSemanticsFor? .R_3).map (·.body) =
    some Stdlib.pairHBody := by native_decide
  ```

---

## 2. `R_4` 間 / 间 — Binary interior

- **Classical source**
  ([`wenyan-operators.md:100-104`](../../wenyan-operators.md#L100)):
  > 庄子「彼节者有间」。间隔算子 — 两元素之间的空间/区域。
  > 不只是减法，是**容纳第三者**的开放区域。Jian 框架的核心字。

- **Signature**: `binaryPoint/2`. The "Jian framework core character" status
  (per the doc) means this op carries doctrinal weight beyond mere geometry.

- **Hex-finite reduction.** Like `R_3`, the basic carrier is "the pair of
  endpoints determines the interior" — i.e. `pairHBody`. The doctrinal note
  "容纳第三者" (admits a third) suggests `R_4` is intended to act as a
  *binder slot* for an inserted carrier, which is **not** a closed-form
  `Hex → Hex → α` function. Without committing to a particular insertion
  semantics, the pair-carrier reading is still the conservative exact body.

- **Decision: `A (upgrade)`**, with a doctrinal footnote.

- **Recommended body**: `Stdlib.pairHBody`, arity 2.

- **Rationale**.
  1. The binary carrier reading is the conservative `Hex`-finite reduction.
  2. The "open region between" reading would require a 3-ary inserter
     (`Hex × Hex × Hex → ?`) that does not match the current `binaryPoint/2`
     signature; we accept the reduction loss as a stratum boundary.
  3. Same body as `R_3` is appropriate because both are "binary endpoint"
     carriers at the `Hex` layer; the 際/間 distinction is L3 (doctrinal),
     not L1 (operational).
  4. Upgrading both `R_3` and `R_4` together keeps the Jian framework
     anchor (`R_4`) on equal `Hex`-level footing with the boundary anchor (`R_3`).
  5. The "Jian core" doctrinal status is preserved by the existing
     `Title.lean` and `Reading.lean` annotation — the body upgrade does not
     erase it.

- **`native_decide` sanity (proposal)**:
  ```lean
  example : (coreTheoremBackedSemanticsFor? .R_4).map (·.body) =
    some Stdlib.pairHBody := by native_decide
  ```

---

## 3. `C_3` 容 — Containment (capacity-emphasis variant)

- **Classical source**
  ([`wenyan-operators.md:188-192`](../../wenyan-operators.md#L188)):
  > 易·益；尚书「有容德乃大」。容纳 — 给空间盛纳。
  > 关键：容 强调**预留空间**；可容是结构的属性。

- **Signature**: `containment/2`. Companion to `C_1 含` (already in B-class:
  P_1/G_3/.../C_1) and to `C_2 包` (already upgraded with `pairHBody`
  in PR #29 — [Semantics.lean:415](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean#L415)).

- **Hex-finite reduction.** `C_1 含` is the bare "contains" relation
  (B-class axiom because it is the school-definitional inclusion predicate);
  `C_2 包` is the pair-carrier "wrap." `C_3 容` is the **capacity** sense:
  not "does x contain y" (predicate) but "x carries y as content"
  (constructor). At the `Hex` level the capacity reading collapses onto
  the pair carrier `(container, content)`.

- **Decision: `A (upgrade)`**.

- **Recommended body**: `Stdlib.pairHBody`, arity 2.

- **Rationale**.
  1. The capacity-emphasis reading reduces to "container + content as
     an ordered pair witness" — exactly what `pairHBody` provides.
  2. This matches the C_2 包 precedent already in `coreTheoremBackedSemanticsFor?`.
  3. The *predicate* sense (C_1 含 — "x contains y as a proposition")
     remains in B-class because it is the inclusion axiom, not a constructor.
  4. The (容 vs 含) distinction therefore lives along the
     `pairHBody / hexRelEqBody` axis: 容 = constructor, 含 = relation —
     a clean L1 split.
  5. The "预留空间" (reserves space) doctrinal flavor is preserved in
     `Title.lean` / `Reading.lean`; no body change is needed there.

- **`native_decide` sanity (proposal)**:
  ```lean
  example : (coreTheoremBackedSemanticsFor? .C_3).map (·.body) =
    some Stdlib.pairHBody := by native_decide
  ```

---

## 4. `B_8` 節 / 节 — Boundary node (discretizer)

- **Classical source**
  ([`wenyan-operators.md:440-444`](../../wenyan-operators.md#L440)):
  > 易·节卦「节以制度」；庄子「彼节者有间」。节点 — 在连续过程上插入离散标记。
  > 让连续物可被分段；是离散化算子。

- **Signature**: `boundary/1`. `Reading.lean:660,664` catalogues 節/节 as
  the "节点 / 离散标记" reading under context cue `[.expectedObject]`.

- **Hex-finite reduction.** The catalogue gloss is "insert a discrete marker
  into a continuous process." On a single `Hex`, this is *not* a meaningful
  operation: a `Hex` has no continuous parameter to mark. The op is really
  acting on a *stream* of `Hex`s (a list / process), not on a single value.
  Restricting to `Hex → Hex` we can only return the identity (節 as
  "anchor / fixed-point marker") — which is honest but uninformative.

- **Decision: `A (upgrade)`**, to `hexIdBody` as the "anchor marker" reading.

- **Recommended body**: `Stdlib.hexIdBody`
  ([`WenDef.lean:545`](../../formal/SSBX/Foundation/Wen/WenDef.lean#L545)), arity 1.

- **Rationale**.
  1. The discretization sense requires a list/stream input; at the
     `Hex → Hex` signature we can only honestly do "this Hex is itself the
     节-marker," which is identity.
  2. `hexIdBody` is the established "anchor extractor" pattern used by
     `R_5 中, R_6 正, R_11 對, B_1 始, B_2 終, B_4 止, B_5 立, B_6 成, B_7 極`
     (see [Semantics.lean:408-438](../../formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean#L408)).
  3. This is materially better than `hexPredTrueBody` (which returns `true`
     ignoring the input — actively misleading).
  4. The list-level discretization can later be added as a *separate* op
     (e.g. `B_8'` with `(.unary, 1)` signature on a `List Hex`), without
     disturbing the catalogue cardinality 371.
  5. The "anchor" reading aligns with `B_8` being in the boundary group
     (始/終/起/止/立/成/極) all of which are anchors at the `Hex` level.

- **`native_decide` sanity (proposal)**:
  ```lean
  example : (coreTheoremBackedSemanticsFor? .B_8).map (·.body) =
    some Stdlib.hexIdBody := by native_decide
  ```

---

## 5. `L_4` 形名 (paired) — Form/name verification

- **Classical source**
  ([`wenyan-operators.md:1407-1411`](../../wenyan-operators.md#L1407)):
  > 韩非·主道「有言者自为名，有事者自为形，形名参同，君乃无事焉」。
  > 实际表现 (形) 与所宣称之名 (名) 是否相符。
  > **这是验证算子 (verification operator)** — 等价于现代的 type-checking,
  > signature matching, contract verification。

- **Signature**: `relation/2`. `Reading.lean:636` catalogues 形名 as the
  paired reading for `L_4`.

- **Hex-finite reduction.** This is genuinely a *type-checking* operator: it
  asks whether the actual `Hex` (the 形) matches a declared spec `Hex`
  (the 名). At the `Hex × Hex → Bool` layer, "matches" reduces to
  `eqHex` — which is exactly what `hexRelEqBody` already provides. The
  reduction loses the *spec-vs-witness* asymmetry, but the *Bool answer*
  is correct.

- **Decision: `A (upgrade)`**, to `tongBody` (= `.eqHex`), arity 2.

- **Recommended body**: `Stdlib.tongBody`
  ([`WenDef.lean:421`](../../formal/SSBX/Foundation/Wen/WenDef.lean#L421)), arity 2.

  (Equivalent to the current placeholder semantically; the upgrade is the
  *labelling* — making 形名 an explicit invocation of the equality core
  rather than fallthrough to a stub.)

- **Rationale**.
  1. 形 vs 名 matching at the `Hex` layer is Hex-equality with the second
     arg interpreted as a spec.
  2. `tongBody` is the established stdlib for Hex equality (already used by
     `F_12 通` after PR-01 upgrade and by `I_1 同` since PR #29).
  3. Promoting from placeholder fallthrough to an explicit body removes
     the `hexRelEqBody` axiom-interface routing and gives 形名 a *named*
     reduction.
  4. The spec/witness asymmetry can later be reified by an extended
     signature (`(Spec, Witness) → Bool`) without breaking this body.
  5. The Han-Fei doctrinal anchor ("形名参同") is preserved at the
     `Title.lean` / `OperatorReadings.lean` layer.

- **`native_decide` sanity (proposal)**:
  ```lean
  example : (coreTheoremBackedSemanticsFor? .L_4).map (·.body) =
    some Stdlib.tongBody := by native_decide
  ```

---

## 6. `Y_20` 順 / 逆 — Flow direction (medical)

- **Classical source**
  ([`wenyan-operators.md:1678-1682`](../../wenyan-operators.md#L1678)):
  > 素问·四气调神大论「逆春气则少阳不生」；「顺四时而适寒暑」。
  > 与流动方向的关系。**治法常需逆症 (反symptom方向) 但顺势 (与人体自愈方向同向)**。

- **Signature**: `relation/2`. The doc itself flags this as
  *non-pure-Hex*: it requires a `Flow` parameter (direction of qi), which
  has no `Hex`-finite encoding.

- **Hex-finite reduction.** None that is honest. The op is fundamentally
  about an *agent intervention* relative to an external flow field; the
  flow field is not a `Hex` and is not a function of two `Hex`s. The
  Bool reduction "is the action aligned with the flow?" can only collapse
  to `eqHex` — but the equality would be between an action `Hex` and a
  flow `Hex` of completely different types, which is a category error.

- **Decision: `B (true axiom)`** — move to the axiom-interface registry.

- **School axis**: 医家 (黄帝内经 systems-dynamics axis). The 顺/逆 binary
  is part of the medical-school *intervention semantics*, not part of the
  general Hex algebra.

- **Rationale why not reducible**.
  1. The flow field 势 is an *exogenous* parameter outside the `Hex`
     finite universe; `Hex` cannot encode "spring qi" or "self-healing
     direction."
  2. The doc itself notes the *subtle* distinction "逆症 但 顺势" — the
     same Hex argument can be both 顺 and 逆 depending on which flow
     dimension is intended; no closed function `Hex × Hex → Bool` can
     express this without exogenous context.
  3. The op belongs in the school-axiom set with `ZA_13..ZA_20` and
     the other 医家 / 道家 / 法家 sections — its meaning is fixed by
     classical text and intentional school commitments, not by Hex
     algebra.

---

## 7. `Z_14` 居 — Dwelling-at (long-duration locator)

- **Classical source**
  ([`wenyan-operators.md:2029-2033`](../../wenyan-operators.md#L2029)):
  > 通用；论语「居处恭」；老子「水善利万物而不争，处众人之所恶」。
  > 居于 — 在某 state/place 中长期 dwell。
  > 是**长时间 located-at**。比 在 (R-1) 时间维度更长。

- **Signature**: `relation/2`.

- **Hex-finite reduction.** 居 is the temporal-extended version of `R_1 在`
  (which is already in B-class — true axiom for "located-at" relation).
  The "long time" qualifier is *not* a `Hex` operation: it asserts
  persistence across an implicit time index. Without a time-axis carrier
  (which would be a separate `Tm` constructor — not available at
  `(Hex × Hex → Bool)`), the duration distinction collapses.

- **Decision: `B (true axiom)`** — move to axiom-interface registry alongside
  `R_1, R_2`.

- **School axis**: General-purpose location predicate (Z-series 补遗算子) but
  doctrinally a *temporal-extended* member of the 关系算子 R-series. Belongs
  with `R_1 在, R_2 屬` which are already B-class.

- **Rationale why not reducible**.
  1. 居 requires a duration / persistence component absent from
     `Hex × Hex → Bool`.
  2. Forcing it through `hexRelEqBody` (current placeholder) yields
     observationally identical behavior to `R_1 在` — losing the entire
     point of the operator.
  3. The "比 R_1 时间维度更长" distinction is exactly what an axiom
     interface should record (as a labelled axiom about the predicate),
     not what a stub body should erase.

---

## 8. `Z_15` 處 / 处 — Situated-at (situation handling)

- **Classical source**
  ([`wenyan-operators.md:2035-2039`](../../wenyan-operators.md#L2035)):
  > 通用；老子；论语。处于 — 在某 situation 中应对。
  > 与 居 微差: 居 是 dwelling，处 是 dealing-with。

- **Signature**: `relation/2`.

- **Hex-finite reduction.** Even more clearly non-reducible than `Z_14`:
  the operator's meaning is *dealing-with* (an active stance toward a
  situation), not a position predicate. There is no `Hex × Hex → Bool`
  function that distinguishes "x dwells at y" from "x deals with y."

- **Decision: `B (true axiom)`**.

- **School axis**: Same family as `Z_14` (general-purpose Z-series补遗,
  doctrinally an R-series situational relation). Companion axiom to
  `Z_14`.

- **Rationale why not reducible**.
  1. The 居/處 distinction is an *intention* axis (passive dwell vs.
     active deal-with) not a *Hex-value* axis.
  2. Collapsing to `eqHex` makes `Z_14` and `Z_15` indistinguishable —
     a doctrinal violation of the catalogue's deliberate twin entries.
  3. Registering as paired axioms preserves the catalogue cardinality
     and the doctrinal contrast.

---

## 9. `Z_39` 識 / 识 — Recognize (pattern match)

- **Classical source**
  ([`wenyan-operators.md:2179-2183`](../../wenyan-operators.md#L2179)):
  > 通用；论语「君子识大」。识别。
  > 是**模式识别**算子 — pattern matching against known categories。

- **Signature**: `predicate/1`. Returns Bool given a Hex.

- **Hex-finite reduction.** Pattern matching against a *fixed* known
  pattern is a Hex-finite predicate: `λ x. eqHex x P` for some pattern
  `P : Hex`. But the catalogue does *not* fix `P` — 識 is parametric over
  "known categories" — making the operator stand for an entire *family*
  of predicates, not one. At arity-1 there is no slot for `P`.

  **Promising sub-case**: if we read 識 as "x matches at least one of the
  64 hexagrams" (which is trivially true for any `Hex` since `Hex = Fin 64`),
  then 識 reduces to `λ x. true` — i.e. `hexPredTrueBody`, exactly the
  current placeholder. So the placeholder is *accidentally* correct for
  this reading, but only because the reading is degenerate.

- **Decision: `C-still`** — pending the parameterization question.

- **What is still needed**.
  1. **Classical research**: is there a canonical 64-element category
     set in 论语 / 黄帝内经 / 周易 that 識 ranges over? If yes, the op
     becomes a `λ x. x ∈ S` for known `S` — exact body possible.
  2. **Lean infrastructure**: a `setMembershipBody : (Hex → Bool) → Hex
     → Bool` body would be needed to parameterize 識 over its category
     set without changing arity. None such exists in `Stdlib` at PR #29.
  3. **Doctrinal call**: does the project want 識 to be the "always-true
     tautology over `Hex = Fin 64`" (current behavior) or a real
     categorical-membership predicate (requires (1) and (2))?

  Until (1) is resolved, leaving 識 routed to `hexPredTrueBody` via the
  axiom-interface registry is the conservative move.

---

## 10. `Z_40` 知 (作算子) — Knowledge acquisition

- **Classical source**
  ([`wenyan-operators.md:2185-2189`](../../wenyan-operators.md#L2185)):
  > 论语；墨经 P-20 已部分覆盖。一般知识获取。
  > 与 P-20 互补 — P-20 是分类，此处是基础算子。
  > `Reading.lean:457`: `catalogueReading "知" "Z-40" "一般知识获取" .prefix [.expectedObject]`.

- **Signature**: `relation/2` (Subject × Object → Knowledge).

- **Hex-finite reduction.** 知 carries an explicit *Subject × Object*
  signature — i.e. there are *two* Hex arguments meaning two different
  things, with a *Knowledge* third type that is not Hex. Reducing to
  `Hex × Hex → Bool` requires either:
  - Picking *one* of {subject-side reading, object-side reading,
    relation-side reading} and committing to it — none is canonical.
  - Returning the pair carrier `(Subject, Object)` as the "knowledge
    witness" — i.e. `pairHBody`. This is honest but loses the
    *cognitive* content of 知.

  P-20 (the related 墨经 op already in B-class) handles the *taxonomic*
  side; Z_40 was added as the *cognitive* complement and was deliberately
  left as a school axiom.

- **Decision: `B (true axiom)`**.

- **School axis**: 墨经 (cognitive predicate axis), complementing
  `P_1, P_14, P_15, P_16, P_17, P_20` which are all 墨经 definitional ops
  already routed to the axiom-interface registry in sub-plan 01.

- **Rationale why not reducible**.
  1. The output type *Knowledge* is not `Hex` and has no canonical
     Hex encoding.
  2. The Subject/Object asymmetry rules out the symmetric `eqHex`
     reading; pairHBody loses the cognitive content.
  3. As complement to P-20 in the Mohist sub-axis, Z_40 belongs with
     the Mohist axiom-interface set (same school axis: 墨经 cognition).
  4. Any future `KnowledgeCell` carrier would need a new `Tm` AST node
     and is out of scope for sub-plan 01.

---

## 11. `LIJ_6` 節 / 节 — Measure-bounded expression

- **Classical source**
  ([`wenyan-operators.md:2503-2507`](../../wenyan-operators.md#L2503)):
  > 礼记·中庸「发而皆中节」。中度 — 对情感 / 行动施加分寸边界。
  > 节 是连续量的边界控制。它不是压抑表达，而是让表达落入可共处范围。
  > `Reading.lean:661,665`: `catalogueReading "節" "LIJ-6" "分寸约束" .prefix [.ritualContext]`.

- **Signature**: `boundary/2` — distinct from `B_8` (節 as discrete node,
  `boundary/1`). The arity-2 signature suggests `(Expression, Measure) →
  BoundedExpression`.

- **Hex-finite reduction.** The doctrinal sense is *continuous-quantity
  bounding* — clipping a value to a measure range. With `Hex = Fin 64`,
  "bounding" can be encoded as `min` (or `mod`) against the measure `Hex`,
  but:
  - The catalogue *intentionally* paired LIJ_6 with `B_8` as the
    *ritual-context* (`.ritualContext`) reading, meaning the
    distinction from `B_8` is the *moral/ritual* dimension, not the
    Hex-arithmetic dimension.
  - Reducing to `min` would erase that distinction.

  An honest `Hex → Hex → Hex` reduction (e.g. `λ e m. min e m`) is
  computable but contradicts the doctrinal pairing with `B_8`. A pair
  carrier `pairHBody` is structurally fine but again loses the
  *clipping* semantics.

- **Decision: `C-still`**.

- **What is still needed**.
  1. **Doctrinal call**: which is load-bearing — the *ritual-bounding*
     reading (paired axiom with `B_8`, keep in axiom-interface) or the
     *arithmetic-clipping* reading (upgrade to a new `clipBody`)?
  2. **Lean infrastructure**: no `Stdlib` body currently implements
     "clip Hex `e` to `[0, m]`." A `clipHBody` would be a defensible
     addition but is new code, not a reuse.
  3. **Catalogue consistency**: `B_8` and `LIJ_6` are deliberately
     two readings of the same glyph 節 — any upgrade decision should
     be made jointly with `B_8` (see entry 4 above, which proposed
     `hexIdBody` for `B_8`).

  Until the doctrinal direction is fixed, leaving `LIJ_6` on the
  axiom-interface track is the conservative move. *Tentative lean*:
  given that the ritual-bounding reading is what makes `LIJ_6` distinct
  from `B_8`, the most likely final decision is **B (true axiom)** —
  but we mark this as `C-still` here to require an explicit doctrinal
  call before promoting.

---

## 12. `LIJ_9` 誠 / 诚 — Cross-time self-consistency

- **Classical source**
  ([`wenyan-operators.md:2521-2525`](../../wenyan-operators.md#L2521)):
  > 中庸「诚者，天之道也；诚之者，人之道也」。
  > 自一致 — 内外、始终、言行相合。
  > 诚 是 coherence operator。它不是单一真值，而是跨时间和表达层的一致性。

- **Signature**: `identity/2` (Self × Expression → ConsistentSelf).

- **Hex-finite reduction.** The doc itself flags 誠 as non-truth-functional:
  *"不是单一真值，而是跨时间和表达层的一致性"*. The op asserts a
  *coherence across multiple time/expression layers*, which:
  - Cannot be checked by a finite `Hex × Hex → Bool` function
    (the domain has no time index).
  - Cannot collapse to `eqHex` without erasing the coherence content
    (eqHex is *single-shot* equality, not *cross-time* identity).
  - Is canonically the *single example* the project literature gives of
    a "true cross-time axiom" — see e.g. the `wen-substrate.md` discussion
    of identity-axes.

- **Decision: `B (true axiom)`**.

- **School axis**: 中庸 / 礼记 (LIJ-series, identity-axis). The
  `(.identity, 2)` signature is shared with no other op in the C-class
  list; it is *the* cross-time identity primitive in the catalogue.

- **Rationale why not reducible**.
  1. The op is *defined by its untruth-functionality* in the source
     text: "不是单一真值."
  2. Any `Hex`-finite reduction would erase the very property that
     makes 誠 distinguishable from `I_1 同` (already exact, eqHex).
  3. The "internal/external × beginning/end × words/deeds" three-axis
     coherence requires a 3-tensor of `Hex` arguments at minimum —
     the current `(identity, 2)` signature cannot host it.
  4. Belongs in the axiom-interface registry with `ZHU_1 齊`
     (perspective quotient, already B-class) — both are *equivalence-style*
     ops whose intent exceeds the algebraic interface.

---

## Summary table

| OperatorId | 字 | Decision | Recommended body / school |
|---|---|---|---|
| `R_3` | 際 / 际 | **A (upgrade)** | `Stdlib.pairHBody` (boundary as unordered pair) |
| `R_4` | 間 / 间 | **A (upgrade)** | `Stdlib.pairHBody` (interior anchor as pair) |
| `C_3` | 容 | **A (upgrade)** | `Stdlib.pairHBody` (container + content) |
| `B_8` | 節 / 节 | **A (upgrade)** | `Stdlib.hexIdBody` (node-marker as anchor) |
| `L_4` | 形名 | **A (upgrade)** | `Stdlib.tongBody` (form/name = eqHex) |
| `Y_20` | 順 / 逆 | **B (true axiom)** | 医家 flow-intervention axis |
| `Z_14` | 居 | **B (true axiom)** | 关系 (Z-series 补遗, temporal-extended R_1) |
| `Z_15` | 處 / 处 | **B (true axiom)** | 关系 (paired with Z_14, deal-with intent) |
| `Z_39` | 識 / 识 | **C-still** | needs categorical-membership infrastructure |
| `Z_40` | 知 | **B (true axiom)** | 墨经 cognition axis (P-series complement) |
| `LIJ_6` | 節 / 节 | **C-still** | ritual-vs-arithmetic doctrinal call required |
| `LIJ_9` | 誠 / 诚 | **B (true axiom)** | 中庸 cross-time identity axis |

**Tally**:

- **A (upgrade)**: 5 ops — `R_3, R_4, C_3, B_8, L_4`
- **B (true axiom)**: 5 ops — `Y_20, Z_14, Z_15, Z_40, LIJ_9`
- **C-still**: 2 ops — `Z_39, LIJ_6`

## Implications for downstream sub-plans

1. **Open follow-up sub-plan `01b-C-to-A-upgrade.md`** to promote the 5
   A-class candidates. After 01b:
   - `coreTheoremBackedOperatorIds.length`: **331 → 336**
     (sub-plan 01's 331 plus 5 C→A promotions).
   - `axiomInterfaceOperatorIds.length`: **40 → 35** (sub-plan 01's 40
     minus 5 promotions).
   - Total `theoremBackedOperatorIds.length` stays **371**.

2. **Sub-plan 01 update needed (text only)**: sub-plan 01 README claims
   "B-class 28 个" but actually enumerates 30 IDs. After 06's research, the
   genuine B set (sub-plan 01 list minus the LIJ_9/Z_40 we reclassify, plus
   the 4 new B from 06: Y_20, Z_14, Z_15) is exactly **31** ops. The
   "axiomInterfaceOperatorIds.length = 40" target in sub-plan 01 should
   become **40** (31 B + 2 C-still + 7 not-yet-considered? *NB*: this
   detail needs reconciliation with sub-plan 01's actual member set; it
   does **not** block sub-plan 01 going first).

3. **C-still 2 ops** (`Z_39 識`, `LIJ_6 節 ritual-bound`) remain on the
   axiom-interface track. Each needs a separate doctrinal/research note
   before promotion can be considered. Suggested follow-ups (not in this
   sub-plan):
   - `Z_39`: classical-research mini-task on whether 论语's "识大" has
     a canonical 64-category set.
   - `LIJ_6`: doctrinal-call mini-task on ritual-bounding vs arithmetic-clip.

4. **Generality preserved**: no theorem in `Semantics.lean` is dropped;
   the only changes 01b would make are adding 5 explicit cases to
   `coreTheoremBackedSemanticsFor?` and updating the two length theorems.

## References

- `formal/SSBX/Foundation/Wen/WenSurface/Semantics.lean` (§1.1-1.3, lines 329-400)
- `formal/SSBX/Foundation/Wen/WenDef.lean` (Stdlib bodies — `hexIdBody:545`,
  `pairHBody:871`, `tongBody:421`)
- `formal/SSBX/Text/OperatorSignatures.lean` (`catalogueSignatureShapeFor`,
  lines 398-770)
- `formal/SSBX/Text/WenyanOperators/Title.lean` (CJK glyph titles)
- `formal/SSBX/Text/OperatorReadings.lean` (contextual readings, where catalogued)
- `wenyan-operators.md` (classical sources, lines 94-2525 for the 12 ops)
- `docs-next/10_formal_形式/wen-language-roadmap.md` (the A/B/C tripartition origin)
- Sub-plans: `01-semantics-refactor.md` (A-class upgrade + B-class axiom interface),
  `06-C-class-research.md` (this document's spec)
