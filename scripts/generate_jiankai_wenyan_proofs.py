#!/usr/bin/env python3
"""Generate formal-provable wenyan versions for the Jiankai supplement.

Each source file in
生生不息论_三本文完整版/03_补篇一_间开本_致知版
gets a corresponding concise wenyan proof file.  Missing glyphs are checked
against SSBX.Roster.AtomName and recorded.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import json
import re


ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIR = ROOT / "生生不息论_三本文完整版/03_补篇一_间开本_致知版"
TARGET_DIR = ROOT / "生生不息论_三本文完整版/03_补篇一_间开本_致知版_古文证明版"
ROSTER = ROOT / "formal/SSBX/Roster.lean"


def read(path: Path) -> str:
    return path.read_text()


def extract_inductive_names(text: str, type_name: str) -> list[str]:
    block = text.split(f"inductive {type_name} where", 1)[1].split("deriving", 1)[0]
    out: list[str] = []
    for line in block.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        for part in [p.strip() for p in line[1:].split("|")]:
            if not part:
                continue
            quoted = re.fullmatch(r"«([^»]+)»", part)
            out.append(quoted.group(1) if quoted else part.split()[0])
    return out


def cjk_chars(text: str) -> list[str]:
    return re.findall(r"[\u3400-\u4dbf\u4e00-\u9fff]", text)


def source_title(path: Path) -> str:
    for line in path.read_text().splitlines():
        if line.startswith("#"):
            return re.sub(r"^#+\s+", "", line).strip()
    return path.stem


PROOFS: dict[str, list[str]] = {
    "00_补篇一_间开本_致知版_全量收入.md": [
        "此篇为间开致知之全入。",
        "全篇诸名，皆归字元、生成、原始、递归、待校五类。",
        "名有根，式有型，递归有语义，待校不冒真。",
        "故此篇可入证明；未入籍者，别录待补。",
    ],
    "01_生生不息论.md": [
        "显未尽，未尽生间。",
        "间合法而入场，场以生合续。",
        "心感间，行择间，诸间共开而不相闭。",
        "自由者，邪径迫未成，可识可达之径存也。",
        "道者，正续而夺共续未成，度期周而受校未败也。",
    ],
    "02_卷一_立位.md": [
        "三相一理：事见其生，物见其成，场见其通。",
        "三相互校；极间、极物、极场，皆可成闭。",
        "场者，焦、关系、态、制之合也。",
        "生合者，场与间相入而成续也。",
        "气者，间域、权重、耦、扰之流也。",
    ],
    "03_卷二_发生.md": [
        "元者，间动也。",
        "几者，元动未形也。",
        "势者，几积而向显也。",
        "机者，势临岐也。",
        "聚者，势凝为形；散者，形散而迹存。",
    ],
    "04_卷三_判准.md": [
        "开者，未尽、可生、能应、能转也。",
        "闭者，断、冻、夺、蔽、伪也。",
        "伪开者，似开而实闭也。",
        "自似者，层层同形也。",
        "因生因者，生复生，开复开维也。",
        "尺度异，判准随度期而校。",
    ],
    "05_卷四_境与模.md": [
        "境者，场之经验相也。",
        "模者，形、因、结、场之可校相也。",
        "格物者，格物而知也。",
        "四校者，异入、众应、迹查、互证也。",
        "模可高下；高者，显理、识机、辨伪、护开、导行。",
    ],
    "06_卷五_价值之相.md": [
        "中者，极闭之校也。",
        "平者，势强息而开存也。",
        "和者，共开而夺未成也。",
        "美者，心遇开而自开也。",
        "德者，行积向正而能护开也。",
    ],
    "07_卷六_心物.md": [
        "理者，事之序也。",
        "心者，场中能感、识、择、校之焦也。",
        "情者，间入心，权重显也。",
        "积者，行迹入续也。",
        "理、心、情、积，非四物，乃一场四显。",
    ],
    "08_卷七_道之相.md": [
        "善者，正生而邪息也。",
        "好者，开可续之形也。",
        "自由者，可识可达，邪径迫未成也。",
        "繁荣者，众自由共开共续也。",
        "道者，正续而夺共续未成，平和为域也。",
    ],
    "09_卷八_五常.md": [
        "仁者，己续入共续也。",
        "义者，机中择正也。",
        "礼者，正行之形也。",
        "智者，知能辨度期、正邪、开闭也。",
        "信者，关系可续也。",
    ],
    "10_卷九_行与性.md": [
        "行者，焦择间入场也。",
        "行入场，场续，迹入积。",
        "性者，行之积向，稳择间之模也。",
        "行受校，性可修，修而复开。",
    ],
    "11_卷十_收.md": [
        "易之微连，以间、位、变、应显。",
        "意图向齐生者，意图、目标、控制、对齐皆入齐生之校。",
        "生生不息者，生复生，续复续，开未尽也。",
        "一例可校，故非空言；入场可行，故为模型。",
    ],
    "12_四十二、终式.md": [
        "全式：场生间，间成物，物含间，心感间，行择间。",
        "筛间，格物生合法，因生因开新维。",
        "平和成好，自由为底，繁荣显共。",
        "智辨度期，善护共开，仁通己续共续。",
        "事见其生，物见其成，场见其通；是谓生生不息。",
    ],
    "13_终言.md": [
        "此论成，亦此论所指之一行也。",
        "文可校，行可校，开可校。",
        "成闭者，自背也。",
        "护开者，入道也。",
        "终而未尽，故仍可续。",
    ],
}

ANCHORS: dict[str, list[str]] = {
    "00_补篇一_间开本_致知版_全量收入.md": ["no_unregistered_formal_term", "generated_terms_have_roots", "recursive_terms_have_semantics", "unk_not_assertable"],
    "01_生生不息论.md": ["未尽", "候间", "合法", "生合", "共开", "自由", "道"],
    "02_卷一_立位.md": ["三相一理", "场态", "生合", "气", "type_preservation"],
    "03_卷二_发生.md": ["元", "几", "势", "机", "聚散"],
    "04_卷三_判准.md": ["开", "闭", "伪开", "自似", "开维法", "度期周"],
    "05_卷四_境与模.md": ["境", "模", "格物", "异入", "众应", "迹查", "互证"],
    "06_卷五_价值之相.md": ["平", "和", "好", "善", "护开"],
    "07_卷六_心物.md": ["理", "心", "情", "积", "聚焦"],
    "08_卷七_道之相.md": ["善", "好", "自由", "繁荣", "道"],
    "09_卷八_五常.md": ["仁", "义", "礼", "智", "信"],
    "10_卷九_行与性.md": ["行", "性", "择", "入", "复开"],
    "11_卷十_收.md": ["易之微连", "意图向齐生", "对齐", "生生不息", "recommendationI2Right"],
    "12_四十二、终式.md": ["全式", "续", "合法", "平", "和", "自由", "繁荣", "仁", "道"],
    "13_终言.md": ["可校", "护开", "道", "生生不息"],
}


def render_file(source: Path, allowed: set[str]) -> tuple[str, Counter[str], Counter[str]]:
    rel = source.relative_to(ROOT)
    title = source_title(source)
    lines = [
        f"# {title} · 古文证明版",
        "",
        f"源：`{rel}`",
        "",
        "## 证明口径",
        "",
        "此版不增义根；诸句皆回指正篇注册表、递归语义、三值保守律与相应生成项。",
        "凡字未入当前 `AtomName` 者，入缺字记录；未补义位前，不作对象语言之正式根。",
        "",
        "## 古文定本",
        "",
    ]
    for item in PROOFS[source.name]:
        lines.append(f"- {item}")
    lines += [
        "",
        "## 形式锚",
        "",
    ]
    for anchor in ANCHORS[source.name]:
        lines.append(f"- `{anchor}`")
    lines += [
        "",
        "## 可证式",
        "",
        "1. 名皆有籍，故可入式。",
        "2. 生成项皆有根，故非黑箱。",
        "3. 递归项皆有语义，故可收束。",
        "4. 待校项不得推出真，故证明保守。",
        "5. 本文件古文定本只作上述形式锚之文言渲染。",
        "",
    ]
    text = "\n".join(lines)
    full_missing = Counter(ch for ch in cjk_chars(text) if ch not in allowed)
    proof_text = "\n".join(PROOFS[source.name])
    proof_missing = Counter(ch for ch in cjk_chars(proof_text) if ch not in allowed)
    return text, full_missing, proof_missing


def main() -> None:
    allowed = set(extract_inductive_names(read(ROSTER), "AtomName"))
    TARGET_DIR.mkdir(parents=True, exist_ok=True)

    manifest: list[dict[str, object]] = []
    global_full_missing: Counter[str] = Counter()
    global_proof_missing: Counter[str] = Counter()
    per_full_char_files: dict[str, set[str]] = defaultdict(set)
    per_proof_char_files: dict[str, set[str]] = defaultdict(set)

    sources = sorted(SOURCE_DIR.glob("*.md"))
    expected = set(PROOFS)
    actual = {p.name for p in sources}
    if actual != expected:
        raise SystemExit(f"source/proof map mismatch: missing={sorted(actual ^ expected)}")

    for source in sources:
        text, full_missing, proof_missing = render_file(source, allowed)
        target = TARGET_DIR / source.name
        target.write_text(text)
        for ch, count in full_missing.items():
            global_full_missing[ch] += count
            per_full_char_files[ch].add(target.name)
        for ch, count in proof_missing.items():
            global_proof_missing[ch] += count
            per_proof_char_files[ch].add(target.name)
        manifest.append(
            {
                "source": str(source.relative_to(ROOT)),
                "target": str(target.relative_to(ROOT)),
                "title": source_title(source),
                "proof_missing_chars": dict(sorted(proof_missing.items())),
                "full_markdown_missing_chars": dict(sorted(full_missing.items())),
            }
        )

    readme = [
        "# 间开本 · 致知版 · 古文证明版",
        "",
        "本目录为 `03_补篇一_间开本_致知版` 的一一对应古文证明版。",
        "",
        "约束：",
        "",
        "- 不增义根；只作已登记形式项、递归语义、三值保守律之文言渲染。",
        "- 缺字未补义位前，不作对象语言正式根。",
        "- 每个源文件对应一个同名输出文件。",
        "",
        "文件：",
        "",
    ]
    for item in manifest:
        readme.append(f"- [{item['title']}]({Path(str(item['target'])).name})")
    (TARGET_DIR / "README.md").write_text("\n".join(readme) + "\n")

    missing_lines = [
        "# 缺字记录",
        "",
        "主表检查范围：各文件 `古文定本` 段。",
        "附表检查范围：本目录生成的古文证明版 Markdown 全文。",
        "依据：`formal/SSBX/Roster.lean` 中 `AtomName` 已登记单字。",
        "",
        f"- 输出文件数：{len(manifest)}",
        f"- 古文定本缺字种数：{len(global_proof_missing)}",
        f"- 全文缺字种数：{len(global_full_missing)}",
        "",
        "## 古文定本缺字总表",
        "",
        "| 字 | 次数 | 文件 |",
        "|---|---:|---|",
    ]
    for ch, count in sorted(global_proof_missing.items(), key=lambda kv: (-kv[1], kv[0])):
        files = "、".join(sorted(per_proof_char_files[ch]))
        missing_lines.append(f"| {ch} | {count} | {files} |")
    missing_lines += [
        "",
        "## 全文缺字总表",
        "",
        "| 字 | 次数 | 文件 |",
        "|---|---:|---|",
    ]
    for ch, count in sorted(global_full_missing.items(), key=lambda kv: (-kv[1], kv[0])):
        files = "、".join(sorted(per_full_char_files[ch]))
        missing_lines.append(f"| {ch} | {count} | {files} |")
    missing_lines += [
        "",
        "## 说明",
        "",
        "缺字可作为下一轮补义位候选；补入前，相关字只视作元语言说明或待校标签。",
        "",
    ]
    (TARGET_DIR / "缺字记录.md").write_text("\n".join(missing_lines))

    (TARGET_DIR / "manifest.json").write_text(
        json.dumps(
            {
                "source_dir": str(SOURCE_DIR.relative_to(ROOT)),
                "target_dir": str(TARGET_DIR.relative_to(ROOT)),
                "files": manifest,
                "proof_missing_chars": {
                    ch: {
                        "count": count,
                        "files": sorted(per_proof_char_files[ch]),
                    }
                    for ch, count in sorted(global_proof_missing.items())
                },
                "full_markdown_missing_chars": {
                    ch: {
                        "count": count,
                        "files": sorted(per_full_char_files[ch]),
                    }
                    for ch, count in sorted(global_full_missing.items())
                },
            },
            ensure_ascii=False,
            indent=2,
        )
        + "\n"
    )

    print(f"wrote {len(manifest)} files to {TARGET_DIR.relative_to(ROOT)}")
    print(f"proof missing chars: {len(global_proof_missing)}")
    print(f"full markdown missing chars: {len(global_full_missing)}")


if __name__ == "__main__":
    main()
