#!/usr/bin/env python3
"""Split 生生不息论_三本文完整版.md into non-duplicated chapter files.

The original full file is replaced with a short index.  The body text is kept
exactly once in the target folder.  Before replacing the original file, this
script verifies that concatenating all split files reproduces the original
content byte-for-byte.
"""
from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "生生不息论_三本文完整版.md"
TARGET = ROOT / "生生不息论_三本文完整版"


@dataclass(frozen=True)
class Segment:
    title: str
    lines: list[str]
    top_title: str
    order: int


def heading_level(line: str) -> int | None:
    match = re.match(r"^(#{1,6})\s+", line)
    return len(match.group(1)) if match else None


def clean_title(line: str) -> str:
    return re.sub(r"^#{1,6}\s+", "", line).strip() or "untitled"


def slug(title: str) -> str:
    value = title
    value = value.replace("·", "_")
    value = value.replace("——", "_")
    value = re.sub(r"[`*_{}\\$<>:：/|?？!！,，.;；\[\]（）()]+", "_", value)
    value = re.sub(r"\s+", "_", value)
    value = re.sub(r"_+", "_", value).strip("_")
    return value[:80] or "untitled"


def top_key(top_title: str) -> tuple[str, str]:
    if top_title.startswith("正篇"):
        return ("01_正篇_v13.2形式项总清与类型校正版", "正篇")
    if top_title.startswith("补篇〇"):
        return ("02_补篇〇_可运行模型与实例化校正版", "补篇〇")
    if top_title.startswith("补篇一"):
        return ("03_补篇一_间开本_致知版", "补篇一")
    if top_title.startswith("补篇二"):
        return ("04_补篇二_间生论_主篇", "补篇二")
    if top_title.startswith("合订版结语"):
        return ("05_合订版结语", "结语")
    return ("00_编校说明", "编校")


def should_split(line: str, current_top: str) -> bool:
    level = heading_level(line)
    if level is None:
        return False
    if level == 1:
        return True
    if level == 2:
        return True
    if level == 3 and current_top.startswith("补篇二"):
        return True
    return False


def split_segments(text: str) -> list[Segment]:
    lines = text.splitlines(keepends=True)
    segments: list[Segment] = []
    current: list[str] = []
    current_title = "生生不息论 · 三本文完整版"
    current_top = "生生不息论 · 三本文完整版"

    def flush() -> None:
        nonlocal current
        if not current:
            return
        segments.append(Segment(current_title, current, current_top, len(segments)))
        current = []

    for line in lines:
        if should_split(line, current_top if current else clean_title(line)):
            flush()
            current_title = clean_title(line)
            if heading_level(line) == 1:
                current_top = current_title
            current = [line]
        else:
            current.append(line)
    flush()
    return segments


def write_split(text: str, segments: list[Segment]) -> list[dict[str, str]]:
    if TARGET.exists():
        existing = sorted(p for p in TARGET.rglob("*") if p.is_file())
        if existing:
            raise SystemExit(f"target folder already has files; refusing to duplicate: {TARGET}")
    TARGET.mkdir(parents=True, exist_ok=True)

    counters: dict[str, int] = {}
    manifest: list[dict[str, str]] = []
    for segment in segments:
        folder_name, _ = top_key(segment.top_title)
        folder = TARGET / folder_name
        folder.mkdir(parents=True, exist_ok=True)
        count = counters.get(folder_name, 0)
        counters[folder_name] = count + 1
        filename = f"{count:02d}_{slug(segment.title)}.md"
        path = folder / filename
        path.write_text("".join(segment.lines))
        manifest.append(
            {
                "path": str(path.relative_to(ROOT)),
                "title": segment.title,
                "top": segment.top_title,
            }
        )

    reconstructed = "".join((ROOT / item["path"]).read_text() for item in manifest)
    if reconstructed != text:
        raise SystemExit("split verification failed: reconstructed text differs from source")
    return manifest


def write_indexes(original_text: str, manifest: list[dict[str, str]]) -> None:
    digest = hashlib.sha256(original_text.encode()).hexdigest()
    by_top: dict[str, list[dict[str, str]]] = {}
    for item in manifest:
        by_top.setdefault(item["top"], []).append(item)

    readme_lines = [
        "# 生生不息论 · 三本文完整版（拆分目录）",
        "",
        "正文已从根目录同名 Markdown 拆出；每段正文只在本文件夹内保留一份。",
        "",
        "## 完整性",
        "",
        f"- 原全文 SHA-256: `{digest}`",
        f"- 拆分文件数: {len(manifest)}",
        "- 验证方式: 按 manifest 顺序拼接所有拆分文件，结果与拆分前全文完全一致。",
        "",
        "## 文件序列",
        "",
    ]
    for top, items in by_top.items():
        readme_lines.append(f"### {top}")
        readme_lines.append("")
        for item in items:
            rel = Path(item["path"]).relative_to(TARGET.name)
            readme_lines.append(f"- [{item['title']}]({rel.as_posix()})")
        readme_lines.append("")
    (TARGET / "README.md").write_text("\n".join(readme_lines))

    manifest_data = {
        "source": SOURCE.name,
        "sha256_before_split": digest,
        "files": manifest,
    }
    (TARGET / "manifest.json").write_text(
        json.dumps(manifest_data, ensure_ascii=False, indent=2) + "\n"
    )

    index = [
        "# 生生不息论 · 三本文完整版",
        "",
        "本文件已拆分为文件夹内的一系列文件：",
        "",
        "- [拆分目录](生生不息论_三本文完整版/README.md)",
        "- [拆分 manifest](生生不息论_三本文完整版/manifest.json)",
        "",
        "正文内容不再保留在本索引中，以避免与拆分文件重复。",
        "",
        f"拆分前全文 SHA-256: `{digest}`",
        "",
    ]
    SOURCE.write_text("\n".join(index))


def main() -> None:
    original_text = SOURCE.read_text()
    segments = split_segments(original_text)
    manifest = write_split(original_text, segments)
    write_indexes(original_text, manifest)
    print(f"split {SOURCE.name} into {len(manifest)} files under {TARGET.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
