#!/usr/bin/env python3
"""Register missing glyph atoms and attach them to the one-root proof.

The source of truth for the glyphs is the current Jiankai wenyan proof
manifest.  This script is intentionally mechanical: it updates the exhaustive
Lean registries, creates a focused theorem file for the recovered glyphs, and
writes a human-readable recovery report.
"""
from __future__ import annotations

from pathlib import Path
import json
import re


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "生生不息论_三本文完整版/03_补篇一_间开本_致知版_古文证明版/manifest.json"
ROSTER = ROOT / "formal/SSBX/Roster.lean"
MONAD_ROOT = ROOT / "formal/SSBX/Foundation/Core/MonadRoot.lean"
GLYPH = ROOT / "formal/SSBX/Text/Glyph.lean"
MISSING_GLYPHS_LEAN = ROOT / "formal/SSBX/Foundation/Core/MissingGlyphs.lean"
SSBX_IMPORTS = ROOT / "formal/SSBX.lean"
REPORT = ROOT / "formal/SSBX/notes/MissingGlyphRootReport.md"

RECOVERED_GLYPHS = list(
    "七三不与中乃九事二五亦仍以件位例保值全八六其册冒准凡出判别前十卷原口古句只名含四型增"
    "始字守完导尺常式当录律得微德指推收故整文易有本束极染根此渲版皆空立箱篇籍类终经缺美背"
    "致补表见言语诸谓象连述递遇量锚随非项高黑"
)


CORE_MAP = {
    "七": "算", "三": "算", "九": "算", "二": "算", "五": "算", "八": "算", "六": "算", "十": "算", "四": "算",
    "量": "算", "值": "度", "全": "算", "尺": "度", "极": "度",
    "位": "模", "型": "模", "类": "模", "项": "模", "象": "模", "高": "模", "例": "物", "件": "物", "事": "物", "空": "模", "箱": "法",
    "式": "证", "准": "证", "判": "审", "递": "理", "锚": "证", "根": "一",
    "原": "元", "始": "元", "本": "元",
    "不": "法", "与": "法", "乃": "法", "亦": "法", "仍": "续", "以": "法", "其": "法", "凡": "法", "只": "法",
    "含": "法", "故": "法", "此": "法", "皆": "法", "诸": "法", "非": "法", "有": "法", "当": "法", "别": "法", "前": "法",
    "名": "法", "口": "法", "古": "法", "句": "法", "字": "法", "文": "法", "言": "法", "语": "法", "谓": "法", "述": "法",
    "篇": "法", "卷": "法", "册": "法", "版": "法", "表": "法", "录": "法", "籍": "法", "缺": "法", "补": "法",
    "守": "法", "律": "法", "常": "法", "保": "正",
    "中": "正", "德": "正", "美": "正", "背": "邪", "黑": "法",
    "冒": "审", "见": "审",
    "导": "理", "指": "理", "推": "理", "致": "理", "经": "理", "连": "续", "易": "变", "微": "变", "随": "续",
    "出": "成", "增": "生", "立": "成", "得": "成", "完": "成", "收": "成", "束": "成", "整": "成", "终": "续",
    "遇": "心", "染": "法", "渲": "法",
}

FACE_MAP = {
    "七": "模面", "三": "模面", "九": "模面", "二": "模面", "五": "模面", "八": "模面", "六": "模面", "十": "模面", "四": "模面",
    "量": "模面", "值": "模面", "全": "模面", "尺": "模面", "极": "模面",
    "位": "模面", "型": "模面", "类": "模面", "项": "模面", "象": "模面", "高": "模面", "例": "物面", "件": "物面", "事": "物面", "空": "模面", "箱": "文面",
    "式": "证明面", "准": "证明面", "判": "审校面", "递": "证明面", "锚": "证明面", "根": "证明面",
    "原": "证明面", "始": "证明面", "本": "文面",
    "不": "文面", "与": "文面", "乃": "文面", "亦": "文面", "仍": "文面", "以": "文面", "其": "文面", "凡": "文面", "只": "文面",
    "含": "文面", "故": "文面", "此": "文面", "皆": "文面", "诸": "文面", "非": "文面", "有": "文面", "当": "文面", "别": "文面", "前": "文面",
    "名": "文面", "口": "文面", "古": "文面", "句": "文面", "字": "文面", "文": "文面", "言": "文面", "语": "文面", "谓": "文面", "述": "文面",
    "篇": "文面", "卷": "文面", "册": "文面", "版": "文面", "表": "文面", "录": "文面", "籍": "文面", "缺": "文面", "补": "文面",
    "守": "文面", "律": "文面", "常": "价值面", "保": "价值面",
    "中": "价值面", "德": "价值面", "美": "价值面", "背": "价值面", "黑": "文面",
    "冒": "审校面", "见": "审校面",
    "导": "理面", "指": "理面", "推": "理面", "致": "理面", "经": "理面", "连": "理面", "易": "理面", "微": "理面", "随": "理面",
    "出": "生面", "增": "生面", "立": "证明面", "得": "证明面", "完": "证明面", "收": "证明面", "束": "证明面", "整": "证明面", "终": "文面",
    "遇": "心面", "染": "文面", "渲": "文面",
}

MATH_INTERFACE_GLYPHS = list("七三九二五位值全八六十四尺极量")
PROOF_LANGUAGE_PENDING_GLYPHS = list("冒准判原始名型完导式录律得指推收整束根立籍见谓述递锚项")
VALUE_AXIOM_PENDING_GLYPHS = list("中保常德美背")
TEXT_ONLY_PENDING_GLYPHS = list("染渲册箱黑")
TEXT_OPERATOR_OR_RECORD_GLYPHS = list("不与乃亦仍以其凡别前卷口古句只含字守当故文有本此版皆篇缺补表言语诸非")
MODEL_OR_OBJECT_PENDING_GLYPHS = list("事件例出增微易空类终经致象连遇随高")

CLASS_ORDER = [
    ("mathInterface", "数学/计量接口", MATH_INTERFACE_GLYPHS, "结构可证；接 `MathAxiomMap.naturalNumber` / `algebra` 接口；逐字义证未展开"),
    ("proofLanguagePending", "证明术语类", PROOF_LANGUAGE_PENDING_GLYPHS, "已接证明语言层；待义证；当前不可标为语义已证"),
    ("valueAxiomPending", "价值词类", VALUE_AXIOM_PENDING_GLYPHS, "已接价值面与价值 claim；待义证；当前不可标为语义已证"),
    ("textOnlyPending", "仅文本登记", TEXT_ONLY_PENDING_GLYPHS, "仅文本登记，义核待审；当前不作对象语言义证"),
    ("textOperatorOrRecord", "文本/句法/记录类", TEXT_OPERATOR_OR_RECORD_GLYPHS, "文本覆盖可证；不主张对象义核"),
    ("modelOrObjectPending", "模型/对象候选类", MODEL_OR_OBJECT_PENDING_GLYPHS, "结构可证；模型或对象义证待展开"),
]

CLASS_BY_GLYPH = {
    ch: (key, label, status)
    for key, label, glyphs, status in CLASS_ORDER
    for ch in glyphs
}


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def chunked(items: list[str], size: int) -> list[list[str]]:
    return [items[i : i + size] for i in range(0, len(items), size)]


def quoted(ch: str) -> str:
    return f"«{ch}»"


def dot_quoted(ch: str) -> str:
    return f".«{ch}»"


def extract_atom_constructors(text: str) -> list[str]:
    block = text.split("inductive AtomName where", 1)[1].split("  deriving DecidableEq, Repr", 1)[0]
    return re.findall(r"«([^»]+)»", block)


def remove_accidental_ty_atoms(text: str, chars: list[str]) -> str:
    char_set = set(chars)
    start = text.index("inductive Ty where")
    end = text.index("\n\ninductive Kind where", start)
    block = text[start:end]
    kept: list[str] = []
    for line in block.splitlines():
        names = re.findall(r"«([^»]+)»", line)
        if names and set(names).issubset(char_set):
            continue
        kept.append(line)
    return text[:start] + "\n".join(kept) + text[end:]


def extract_label_cases(text: str) -> list[str]:
    block = text.split("namespace AtomName", 1)[1].split("end AtomName", 1)[0]
    return re.findall(r"\|\s+\.?«([^»]+)»\s+=>", block)


def extract_all_atoms(text: str) -> list[str]:
    block = text.split("def allAtoms : List AtomName := [", 1)[1].split("\n]", 1)[0]
    return re.findall(r"\.?\s*«([^»]+)»", block)


def extract_match_cases(text: str, start_marker: str, end_marker: str) -> list[str]:
    block = text.split(start_marker, 1)[1].split(end_marker, 1)[0]
    return re.findall(r"\|\s+\.«([^»]+)»\s+=>", block)


def render_constructor_lines(chars: list[str]) -> str:
    return "\n".join("  | " + " | ".join(quoted(ch) for ch in group) for group in chunked(chars, 14))


def render_label_lines(chars: list[str]) -> str:
    return "\n".join(
        "  | " + " | ".join(f"{dot_quoted(ch)} => \"{ch}\"" for ch in group)
        for group in chunked(chars, 8)
    )


def render_all_atom_body(chars: list[str]) -> str:
    return "\n".join(
        "  " + ", ".join(dot_quoted(ch) for ch in group) + ("," if i + 14 < len(chars) else "")
        for i, group in zip(range(0, len(chars), 14), chunked(chars, 14))
    )


def render_core_lines(chars: list[str]) -> str:
    return "\n".join(f"  | {dot_quoted(ch)} => .«{CORE_MAP[ch]}»" for ch in chars)


def render_face_lines(chars: list[str]) -> str:
    return "\n".join(f"  | {dot_quoted(ch)} => .«{FACE_MAP[ch]}»" for ch in chars)


def render_glyph_sense_body(chars: list[str]) -> str:
    return "\n".join(
        "  " + ", ".join(f"senseOfGlyph \"{ch}\"" for ch in group) + ("," if i + 10 < len(chars) else "")
        for i, group in zip(range(0, len(chars), 10), chunked(chars, 10))
    )


def manifest_chars() -> list[str]:
    data = json.loads(read(MANIFEST))
    missing = list(data["full_markdown_missing_chars"].keys())
    return missing if missing else RECOVERED_GLYPHS


def update_roster(chars: list[str]) -> tuple[list[str], list[str], list[str]]:
    text = read(ROSTER)
    text = remove_accidental_ty_atoms(text, chars)

    constructors = extract_atom_constructors(text)
    add_constructors = [ch for ch in chars if ch not in constructors]
    if add_constructors:
        start = text.index("inductive AtomName where")
        marker_at = text.index("  deriving DecidableEq, Repr", start)
        text = text[:marker_at] + render_constructor_lines(add_constructors) + "\n" + text[marker_at:]

    labels = extract_label_cases(text)
    add_labels = [ch for ch in chars if ch not in labels]
    if add_labels:
        marker = "\n\nend AtomName"
        text = text.replace(marker, "\n" + render_label_lines(add_labels) + marker, 1)

    all_atoms = extract_all_atoms(text)
    add_all_atoms = [ch for ch in chars if ch not in all_atoms]
    if add_all_atoms:
        new_all_atoms = all_atoms + add_all_atoms
        start = text.index("def allAtoms : List AtomName := [") + len("def allAtoms : List AtomName := [")
        end = text.index("\n]", start)
        text = text[:start] + "\n" + render_all_atom_body(new_all_atoms) + text[end:]

    write(ROSTER, text)
    return add_constructors, add_labels, add_all_atoms


def update_monad_root(chars: list[str]) -> tuple[list[str], list[str]]:
    text = read(MONAD_ROOT)

    core_cases = extract_match_cases(text, "def atomCore : AtomName -> CoreAtom", "\ndef CoreDerives")
    add_core = [ch for ch in chars if ch not in core_cases]
    if add_core:
        marker = "\n\ndef CoreDerives"
        text = text.replace(marker, "\n" + render_core_lines(add_core) + marker, 1)
    for ch in chars:
        text = re.sub(
            rf"  \| \.«{re.escape(ch)}» => \.«[^»]+»",
            f"  | .«{ch}» => .«{CORE_MAP[ch]}»",
            text,
            count=1,
        )

    face_cases = extract_match_cases(text, "def atomPrimaryFace : AtomName -> Face", "\n\n/-- Extra faces")
    add_face = [ch for ch in chars if ch not in face_cases]
    if add_face:
        marker = "\n\n/-- Extra faces"
        text = text.replace(marker, "\n" + render_face_lines(add_face) + marker, 1)
    start = text.index("def atomPrimaryFace : AtomName -> Face")
    end = text.index("\n\n/-- Extra faces", start)
    prefix, block, suffix = text[:start], text[start:end], text[end:]
    for ch in chars:
        block = re.sub(
            rf"  \| \.«{re.escape(ch)}» => \.«[^»]+»",
            f"  | .«{ch}» => .«{FACE_MAP[ch]}»",
            block,
            count=1,
        )
    text = prefix + block + suffix

    write(MONAD_ROOT, text)
    return add_core, add_face


def update_glyph_registry(chars: list[str]) -> None:
    text = read(GLYPH)
    body = (
        "def recoveredMissingGlyphSenses : List GlyphSense := [\n"
        + render_glyph_sense_body(chars)
        + "\n]\n\n"
    )
    if "def recoveredMissingGlyphSenses : List GlyphSense := [" in text:
        start = text.index("def recoveredMissingGlyphSenses : List GlyphSense := [")
        end = text.index("\n\n/-- Total glyph-sense table", start)
        text = text[:start] + body + text[end + 2 :]
    else:
        marker = "\n\n/-- Total glyph-sense table"
        text = text.replace(marker, "\n\n" + body + "/-- Total glyph-sense table", 1)

    marker = "  ] ++\n  ["
    replacement = "  ] ++ recoveredMissingGlyphSenses ++\n  ["
    if replacement not in text:
        text = text.replace(marker, replacement, 1)
    write(GLYPH, text)


def write_missing_glyphs_file(chars: list[str]) -> None:
    body = [
        "/-",
        "Recovered missing glyph admission ledger.",
        "",
        "This file separates structural recovery from semantic admission.",
        "`recovered_missing_glyphs_return_to_root` only proves root reachability.",
        "It is not a proof that the provisional core/face choice is semantically",
        "justified.  Pending classes below make that gap machine-visible.",
        "-/",
        "import SSBX.Foundation.MonadRoot",
        "import SSBX.Foundation.MathAxiomMap",
        "import SSBX.Text.Completeness",
        "import SSBX.Truth.Adequacy",
        "",
        "namespace SSBX.Foundation.MissingGlyphs",
        "",
        "open SSBX.Roster",
        "open SSBX.Foundation.MonadRoot",
        "open SSBX.Foundation.MathAxiomMap",
        "open SSBX.Text.Glyph",
        "open SSBX.Truth",
        "open SSBX.Truth.ClaimLedger",
        "",
        "def recoveredMissingGlyphs : List AtomName := [",
        render_all_atom_body(chars),
        "]",
        "",
        "def mathInterfaceGlyphs : List AtomName := [",
        render_all_atom_body(MATH_INTERFACE_GLYPHS),
        "]",
        "",
        "def proofLanguagePendingGlyphs : List AtomName := [",
        render_all_atom_body(PROOF_LANGUAGE_PENDING_GLYPHS),
        "]",
        "",
        "def valueAxiomPendingGlyphs : List AtomName := [",
        render_all_atom_body(VALUE_AXIOM_PENDING_GLYPHS),
        "]",
        "",
        "def textOnlyPendingGlyphs : List AtomName := [",
        render_all_atom_body(TEXT_ONLY_PENDING_GLYPHS),
        "]",
        "",
        "def textOperatorOrRecordGlyphs : List AtomName := [",
        render_all_atom_body(TEXT_OPERATOR_OR_RECORD_GLYPHS),
        "]",
        "",
        "def modelOrObjectPendingGlyphs : List AtomName := [",
        render_all_atom_body(MODEL_OR_OBJECT_PENDING_GLYPHS),
        "]",
        "",
        "def classifiedRecoveredGlyphs : List AtomName :=",
        "  mathInterfaceGlyphs ++ proofLanguagePendingGlyphs ++ valueAxiomPendingGlyphs ++",
        "  textOnlyPendingGlyphs ++ textOperatorOrRecordGlyphs ++ modelOrObjectPendingGlyphs",
        "",
        "inductive GlyphAdmissionKind where",
        "  | mathInterface",
        "  | proofLanguagePending",
        "  | valueAxiomPending",
        "  | textOnlyPending",
        "  | textOperatorOrRecord",
        "  | modelOrObjectPending",
        "  | semanticProved",
        "  deriving DecidableEq, Repr",
        "",
        "def admissionKind (a : AtomName) : GlyphAdmissionKind :=",
        "  if a ∈ mathInterfaceGlyphs then .mathInterface",
        "  else if a ∈ proofLanguagePendingGlyphs then .proofLanguagePending",
        "  else if a ∈ valueAxiomPendingGlyphs then .valueAxiomPending",
        "  else if a ∈ textOnlyPendingGlyphs then .textOnlyPending",
        "  else if a ∈ textOperatorOrRecordGlyphs then .textOperatorOrRecord",
        "  else if a ∈ modelOrObjectPendingGlyphs then .modelOrObjectPending",
        "  else .textOperatorOrRecord",
        "",
        "def HasObjectSemanticProof (a : AtomName) : Prop :=",
        "  admissionKind a = .semanticProved",
        "",
        "instance hasObjectSemanticProofDecidable (a : AtomName) :",
        "    Decidable (HasObjectSemanticProof a) := by",
        "  unfold HasObjectSemanticProof",
        "  infer_instance",
        "",
        "def StructuralProofAvailable (a : AtomName) : Prop :=",
        "  a ∈ allAtoms ∧",
        "  CoveredSymbol (Symbol.atom a) ∧",
        "  Reachable «一元» (.atom a)",
        "",
        "def naturalNumberGlyphs : List AtomName := [",
        render_all_atom_body(list("七三九二五八六十四")),
        "]",
        "",
        "def mathInterfaceFamily (a : AtomName) : AxiomFamily :=",
        "  if a ∈ naturalNumberGlyphs then .naturalNumber else .algebra",
        "",
        "def proofLanguageAnchor (_ : AtomName) : ClaimId :=",
        "  .semanticAdequacyClaim",
        "",
        "def valueAxiomAnchor : AtomName -> ClaimId",
        "  | .«背» => .wrongDefinition",
        "  | _ => .openValueAxiomClaim",
        "",
        "def recoveredMissingGlyphRootSummary : List (AtomName × CoreAtom × Face) :=",
        "  recoveredMissingGlyphs.map (fun a => (a, atomCore a, atomPrimaryFace a))",
        "",
        "theorem recovered_missing_glyphs_registered {a : AtomName} :",
        "    a ∈ recoveredMissingGlyphs -> a ∈ allAtoms := by",
        "  intro _",
        "  cases a <;> native_decide",
        "",
        "theorem recovered_classification_complete {a : AtomName} :",
        "    a ∈ recoveredMissingGlyphs -> a ∈ classifiedRecoveredGlyphs := by",
        "  cases a <;> native_decide",
        "",
        "theorem recovered_classification_sound {a : AtomName} :",
        "    a ∈ classifiedRecoveredGlyphs -> a ∈ recoveredMissingGlyphs := by",
        "  cases a <;> native_decide",
        "",
        "theorem recovered_classification_has_no_duplicates :",
        "    classifiedRecoveredGlyphs.Nodup := by",
        "  native_decide",
        "",
        "theorem recovered_missing_glyphs_return_to_root {a : AtomName} :",
        "    a ∈ recoveredMissingGlyphs ->",
        "      Reachable «一元» (.core (atomCore a)) ∧",
        "      DirectEdge (.core (atomCore a)) (.atom a) ∧",
        "      Reachable «一元» (.atom a) := by",
        "  intro _",
        "  exact all_atoms_return_through_core a",
        "",
        "theorem recovered_missing_glyphs_structural_proof {a : AtomName} :",
        "    a ∈ recoveredMissingGlyphs -> StructuralProofAvailable a := by",
        "  intro h",
        "  exact ⟨",
        "    recovered_missing_glyphs_registered h,",
        "    SSBX.Text.Completeness.roster_text_complete (Symbol.atom a),",
        "    (all_atoms_return_through_core a).2.2",
        "  ⟩",
        "",
        "theorem math_interface_connected {a : AtomName} :",
        "    a ∈ mathInterfaceGlyphs ->",
        "      admissionKind a = .mathInterface ∧",
        "      hasRootOrMap (entry (mathInterfaceFamily a)) ∧",
        "      contractReady (entry (mathInterfaceFamily a)) := by",
        "  intro h",
        "  have hk : a ∈ mathInterfaceGlyphs -> admissionKind a = .mathInterface := by",
        "    cases a <;> native_decide",
        "  exact ⟨hk h, math_axiom_interfaces_have_root_or_map (mathInterfaceFamily a),",
        "    math_axiom_contracts_ready (mathInterfaceFamily a)⟩",
        "",
        "theorem proof_language_layer_ready :",
        "    hasRootOrMap (entry .proofLegality) ∧",
        "    contractReady (entry .proofLegality) := by",
        "  exact ⟨math_axiom_interfaces_have_root_or_map .proofLegality,",
        "    math_axiom_contracts_ready .proofLegality⟩",
        "",
        "theorem proof_language_pending_connected {a : AtomName} :",
        "    a ∈ proofLanguagePendingGlyphs ->",
        "      admissionKind a = .proofLanguagePending ∧",
        "      claimEntry (proofLanguageAnchor a) ∈ allClaims := by",
        "  intro h",
        "  have hk : a ∈ proofLanguagePendingGlyphs -> admissionKind a = .proofLanguagePending := by",
        "    cases a <;> native_decide",
        "  exact ⟨hk h, all_claims_have_entries (proofLanguageAnchor a)⟩",
        "",
        "theorem value_pending_connected_to_value_axioms {a : AtomName} :",
        "    a ∈ valueAxiomPendingGlyphs ->",
        "      admissionKind a = .valueAxiomPending ∧",
        "      atomPrimaryFace a = .«价值面» ∧",
        "      claimEntry (valueAxiomAnchor a) ∈ allClaims := by",
        "  intro h",
        "  have hk : a ∈ valueAxiomPendingGlyphs -> admissionKind a = .valueAxiomPending := by",
        "    cases a <;> native_decide",
        "  have hf : a ∈ valueAxiomPendingGlyphs -> atomPrimaryFace a = .«价值面» := by",
        "    cases a <;> native_decide",
        "  exact ⟨hk h, hf h, all_claims_have_entries (valueAxiomAnchor a)⟩",
        "",
        "theorem text_only_pending_kept_textual {a : AtomName} :",
        "    a ∈ textOnlyPendingGlyphs ->",
        "      admissionKind a = .textOnlyPending ∧",
        "      atomCore a = .«法» ∧",
        "      atomPrimaryFace a = .«文面» ∧",
        "      ¬ HasObjectSemanticProof a := by",
        "  cases a <;> native_decide",
        "",
        "theorem proof_language_pending_not_semantically_proved {a : AtomName} :",
        "    a ∈ proofLanguagePendingGlyphs -> ¬ HasObjectSemanticProof a := by",
        "  cases a <;> native_decide",
        "",
        "theorem value_pending_not_semantically_proved {a : AtomName} :",
        "    a ∈ valueAxiomPendingGlyphs -> ¬ HasObjectSemanticProof a := by",
        "  cases a <;> native_decide",
        "",
        "theorem model_or_object_pending_not_semantically_proved {a : AtomName} :",
        "    a ∈ modelOrObjectPendingGlyphs -> ¬ HasObjectSemanticProof a := by",
        "  cases a <;> native_decide",
        "",
        "theorem recovered_missing_glyphs_have_no_object_semantic_proof {a : AtomName} :",
        "    a ∈ recoveredMissingGlyphs -> ¬ HasObjectSemanticProof a := by",
        "  cases a <;> native_decide",
        "",
        "end SSBX.Foundation.MissingGlyphs",
        "",
    ]
    write(MISSING_GLYPHS_LEAN, "\n".join(body))


def update_imports() -> None:
    text = read(SSBX_IMPORTS)
    line = "import SSBX.Foundation.MissingGlyphs"
    if line in text:
        return
    anchor = "import SSBX.Foundation.AtomDerivation\n"
    text = text.replace(anchor, anchor + line + "\n", 1)
    write(SSBX_IMPORTS, text)


def admission_for(ch: str) -> tuple[str, str, str]:
    return CLASS_BY_GLYPH[ch]


def glyph_join(chars: list[str]) -> str:
    return "、".join(chars)


def write_report(chars: list[str], unmapped: list[str]) -> None:
    lines = [
        "# 缺字补入、归根与义证状态记录",
        "",
        "来源：首次补字时 `生生不息论_三本文完整版/03_补篇一_间开本_致知版_古文证明版/manifest.json` 的 `full_markdown_missing_chars`；补齐后清单固化为脚本内 `RECOVERED_GLYPHS`，便于复跑时保留证明记录。",
        "",
        "重要校正：本记录不再把“登记后可达一元根”说成“语义已证明”。归根定理只证明结构可达；每个字是否有对象语言义证，另列如下。",
        "",
        "代码证明入口：",
        "",
        "- `formal/SSBX/Foundation/Core/MissingGlyphs.lean`",
        "- `recovered_missing_glyphs_structural_proof`：补字皆已登记、文本覆盖、可达一元根。",
        "- `proof_language_pending_connected`：证明术语类已接到 `proofLegality` 与 claim 账本，但仍是待义证。",
        "- `value_pending_connected_to_value_axioms`：价值词类已接到价值面与价值 claim，但仍是待义证。",
        "- `text_only_pending_kept_textual`：牵强项只保留文本路由，不作对象语言义核。",
        "- `recovered_missing_glyphs_have_no_object_semantic_proof`：本轮 104 字均不得标为对象语义已证。",
        "",
        "## 机器可证与未证边界",
        "",
        "| 命题 | 结论 | 代码位置 |",
        "|---|---|---|",
        "| 字形登记 | 可证 | `recovered_missing_glyphs_registered` |",
        "| 文本覆盖 | 可证 | `recovered_missing_glyphs_structural_proof` |",
        "| 回到一元根 | 可证 | `recovered_missing_glyphs_return_to_root` |",
        "| 证明术语义证 | 未证，已接证明语言层 | `proof_language_pending_connected` / `proof_language_pending_not_semantically_proved` |",
        "| 价值词义证 | 未证，已接价值面与 claim | `value_pending_connected_to_value_axioms` / `value_pending_not_semantically_proved` |",
        "| 牵强项义核 | 未证，仅文本登记 | `text_only_pending_kept_textual` |",
        "",
        "## 分类总表",
        "",
        "| 类 | 字 | 当前可证 | 对象义证状态 |",
        "|---|---|---|---|",
    ]
    for _key, label, glyphs, status in CLASS_ORDER:
        lines.append(f"| {label} | {glyph_join(glyphs)} | 登记、文本覆盖、归根可证 | {status} |")
    lines += [
        "",
        "## 逐字表",
        "",
        "| 字 | 类 | 临时核心 | 临时面 | 结构证明 | 对象义证 |",
        "|---|---|---|---|---|---|",
    ]
    for ch in chars:
        if ch in unmapped:
            lines.append(f"| {ch} | 未分类 | - | - | 不可证：未补入 | 不可证：无核心/面映射 |")
        else:
            _key, label, status = admission_for(ch)
            if _key == "textOnlyPending":
                semantic = "未证；仅文本登记，义核待审"
            elif _key == "proofLanguagePending":
                semantic = "未证；已接证明语言层，待义证"
            elif _key == "valueAxiomPending":
                semantic = "未证；已接价值面/价值 claim，待义证"
            elif _key == "mathInterface":
                semantic = "接口已接；逐字义证未展开"
            elif _key == "modelOrObjectPending":
                semantic = "未证；模型/对象义证待展开"
            else:
                semantic = "不主张对象义核；仅文本/句法登记"
            lines.append(
                f"| {ch} | {label} | {CORE_MAP[ch]} | {FACE_MAP[ch]} | 可证：登记、文本覆盖、归根 | {semantic} |"
            )
    lines += [
        "",
        "## 当前不可作对象义证的字",
        "",
        "| 类 | 字 | 处理 |",
        "|---|---|---|",
        f"| 证明术语类 | {glyph_join(PROOF_LANGUAGE_PENDING_GLYPHS)} | 已接证明语言层；不得标为语义已证 |",
        f"| 价值词类 | {glyph_join(VALUE_AXIOM_PENDING_GLYPHS)} | 已接价值面与价值 claim；不得标为语义已证 |",
        f"| 牵强项 | {glyph_join(TEXT_ONLY_PENDING_GLYPHS)} | 仅文本登记，义核待审；`箱`、`黑` 已降级为 `法/文面` 路由 |",
        "",
        "## 无法归根记录",
        "",
    ]
    if unmapped:
        for ch in unmapped:
            lines.append(f"- `{ch}`：缺少明确核心字或面映射，未写入对象语言根。")
    else:
        lines.append("- 无。")
    lines.append("")
    write(REPORT, "\n".join(lines))


def main() -> None:
    chars = manifest_chars()
    unmapped = [ch for ch in chars if ch not in CORE_MAP or ch not in FACE_MAP]
    if unmapped:
        write_report(chars, unmapped)
        raise SystemExit(f"unmapped glyphs: {''.join(unmapped)}")

    add_constructors, add_labels, add_all_atoms = update_roster(chars)
    add_core, add_face = update_monad_root(chars)
    update_glyph_registry(chars)
    write_missing_glyphs_file(chars)
    update_imports()
    write_report(chars, unmapped)

    print(f"target glyphs: {len(chars)}")
    print(f"added constructors: {len(add_constructors)}")
    print(f"added labels: {len(add_labels)}")
    print(f"added allAtoms entries: {len(add_all_atoms)}")
    print(f"added atomCore cases: {len(add_core)}")
    print(f"added atomPrimaryFace cases: {len(add_face)}")
    print(f"unmapped: {len(unmapped)}")


if __name__ == "__main__":
    main()
