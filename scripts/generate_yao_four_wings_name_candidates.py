#!/usr/bin/env python3
"""Generate a review table for yao-position to four-wing naming candidates."""

from __future__ import annotations

import re
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "docs-next" / "40_reference_参考" / "yao-four-wings-name-candidates.md"


YAO_POSITIONS = [
    ("Y1", 0, "初", "初爻", "下始", "始", "发端", "发端", "初心", "始生", "initial line", "first coordinate / lower boundary"),
    ("Y2", 1, "二", "二爻", "下中", "承", "承接", "中正", "受持", "承载", "second line", "lower-middle support coordinate"),
    ("Y3", 2, "三", "三爻", "下终", "际", "临界", "慎独", "转处", "关口", "third line", "inner threshold / phase boundary"),
    ("Y4", 3, "四", "四爻", "上始", "进", "进入", "近君", "趋向", "升转", "fourth line", "outer-entry coordinate"),
    ("Y5", 4, "五", "五爻", "上中", "中", "中位", "中庸", "正中", "中和", "fifth line", "upper-middle governing coordinate"),
    ("Y6", 5, "上", "上爻", "上终", "终", "终极", "成德", "究竟", "复归", "top line", "terminal coordinate / overflow boundary"),
]


# Working four-wing grouping for this review table.  The canonical 十翼 can be
# split more finely later; this table keeps the naming surface compact.
WINGS = [
    ("TUAN", 0, "彖", "彖传", "断", "断义", "总断", "断义", "判相", "裁成", "judgment", "global classifier / summary predicate"),
    ("XIANG", 1, "象", "象传", "象", "取象", "象意", "观象", "现相", "取象", "image", "observable representation"),
    ("WENYAN", 2, "文", "文言", "文", "文释", "文义", "修辞", "名言", "文理", "wording", "semantic annotation"),
    ("XICI", 3, "系", "系辞", "系", "系辞", "关联", "系理", "缘系", "连属", "appended statement", "recursive linkage / meta-theory"),
]


OPERATORS = [
    ("YOP-1", "yao", "升", "上行", "YaoPos -> Option YaoPos", "初→二→三→四→五→上", "move upward", "successor on finite line positions"),
    ("YOP-2", "yao", "降", "下行", "YaoPos -> Option YaoPos", "上→五→四→三→二→初", "move downward", "predecessor on finite line positions"),
    ("YOP-3", "yao", "比", "相邻", "YaoPos × YaoPos -> Bool", "相邻爻位", "adjacent", "path adjacency"),
    ("YOP-4", "yao", "应", "相应", "YaoPos × YaoPos -> Bool", "初/四、二/五、三/上", "correspond", "paired coordinate relation"),
    ("YOP-5", "yao", "中", "中位", "YaoPos -> Bool", "二、五为中", "middle position", "middle-coordinate predicate"),
    ("YOP-6", "yao", "正", "当位", "YaoPos × YaoPolarity -> Bool", "阳居阳位、阴居阴位", "correct position", "parity-position predicate"),
    ("YOP-7", "yao", "承", "承上", "YaoPos × YaoPos -> Bool", "下位承其上一位", "support above", "ordered support relation"),
    ("YOP-8", "yao", "乘", "乘下", "YaoPos × YaoPos -> Bool", "上位乘其下一位", "ride below", "reverse ordered support relation"),
    ("WOP-1", "wing", "转", "翼转", "Wing -> Wing", "彖→象→文→系→彖", "rotate wing", "cyclic successor on four lenses"),
    ("WOP-2", "wing", "综", "统综", "List Wing -> WingSummary", "四翼合看", "synthesize", "fold over interpretive lenses"),
    ("WOP-3", "wing", "分", "析分", "WingSummary -> List Wing", "统义分回四翼", "decompose", "projection from summary to lenses"),
    ("WOP-4", "wing", "互", "互释", "Wing × Wing -> Relation", "翼与翼互相解释", "cross-interpret", "binary relation between lenses"),
    ("GOP-1", "grid", "释", "翼释爻", "Wing × YaoPos -> YaoWing", "用一翼解释一爻", "interpret line", "product introduction"),
    ("GOP-2", "grid", "取", "取爻", "YaoWing -> YaoPos", "从格点取爻位", "project line", "first projection"),
    ("GOP-3", "grid", "属", "取翼", "YaoWing -> Wing", "从格点取所属翼", "project wing", "second projection"),
    ("GOP-4", "grid", "同爻", "同一爻位", "YaoWing × YaoWing -> Bool", "爻位相同", "same line", "first-coordinate equality"),
    ("GOP-5", "grid", "同翼", "同一解释翼", "YaoWing × YaoWing -> Bool", "翼相同", "same wing", "second-coordinate equality"),
    ("GOP-6", "grid", "进爻", "同翼升爻", "YaoWing -> Option YaoWing", "同一翼内上行一爻", "advance line", "map successor over first coordinate"),
    ("GOP-7", "grid", "转翼", "同爻转翼", "YaoWing -> YaoWing", "同一爻位转到下一翼", "advance wing", "map successor over second coordinate"),
]


def md(s: object) -> str:
    return str(s).replace("|", "\\|")


def line(cols: list[object]) -> str:
    return "| " + " | ".join(md(c) for c in cols) + " |\n"


def read_text(path: str) -> str:
    p = ROOT / path
    return p.read_text(encoding="utf-8") if p.exists() else ""


def split_cjk_chars(s: str) -> set[str]:
    return {ch for ch in s if "\u4e00" <= ch <= "\u9fff"}


def code_of_ctor(ctor: str) -> str:
    return ctor.replace("_", "-")


@lru_cache(maxsize=1)
def collision_sets() -> tuple[dict[str, set[str]], dict[str, set[str]], set[str]]:
    reading_text = read_text("formal/SSBX/Text/OperatorReadings.lean")
    operator_text = read_text("formal/SSBX/Text/WenyanOperators.lean")
    surface_readings: dict[str, set[str]] = {}
    for surface, code in re.findall(r'catalogueReading\s+"([^"]+)"\s+"([^"]+)"', reading_text):
        surface_readings.setdefault(surface, set()).add(code)

    operator_form_chars: dict[str, set[str]] = {}
    for ctor, form in re.findall(r'\|\s+\.([A-Z0-9_]+)\s+=>\s+textToSenses\s+"([^"]+)"', operator_text):
        for ch in split_cjk_chars(form):
            operator_form_chars.setdefault(ch, set()).add(code_of_ctor(ctor))
    for ctor, sense in re.findall(r'\|\s+\.([A-Z0-9_]+)\s+=>\s+\[«([^»]+)1»\]', operator_text):
        for ch in split_cjk_chars(sense):
            operator_form_chars.setdefault(ch, set()).add(code_of_ctor(ctor))

    reserved = {"之", "者", "令", "真", "假", "已", "今", "未"}
    return surface_readings, operator_form_chars, reserved


def collision_info(surface: str) -> tuple[str, str]:
    surface_readings, operator_forms, reserved = collision_sets()
    flags: list[str] = []
    codes: set[str] = set()
    if surface in surface_readings:
        flags.append("reading")
        codes.update(surface_readings[surface])
    if surface in operator_forms:
        flags.append("operator-form")
        codes.update(operator_forms[surface])
    if surface in reserved:
        flags.append("reserved")
    return (", ".join(flags) if flags else "open", ", ".join(sorted(codes)) if codes else "")


def pair_surface(yao: tuple, wing: tuple) -> str:
    return yao[2] + wing[2]


def pair_alias(yao: tuple, wing: tuple) -> str:
    return yao[2] + "之" + wing[2]


def main() -> None:
    rows = [(yao, wing) for yao in YAO_POSITIONS for wing in WINGS]
    assert len(YAO_POSITIONS) == 6
    assert len(WINGS) == 4
    assert len(rows) == 24
    assert len({pair_surface(yao, wing) for yao, wing in rows}) == 24
    assert len(OPERATORS) == 19

    out: list[str] = []
    out.append("# 爻位到四翼自然命名候选表\n\n")
    out.append("> Generated by `python3 scripts/generate_yao_four_wings_name_candidates.py`.\n")
    out.append("> Working definition: 四翼 = `彖 / 象 / 文言 / 系辞`. This is a naming review table, not a parser or theorem change.\n\n")
    out.append("目的：给六爻位与四个解释翼之间的 24 个组合准备可审阅 surface 候选。它与 `Cell192` 命名表相同，只登记候选、别名、跨传统说明、英文和形式逻辑对应；后续是否 promotion 到 WenSurface 另行决定。\n\n")
    out.append("## 审阅规则\n\n")
    out.append("- 枚举顺序为 `初/二/三/四/五/上 × 彖/象/文/系`。\n")
    out.append("- `古文候选` 是短 surface；`保留别名` 使用 `爻位之翼`，更可读但更长。\n")
    out.append("- `四翼` 在此先合并十翼为四类：彖断、象观、文言释义、系辞系理；说卦/序卦/杂卦可另表追加。\n")
    out.append("- `冲突提示` 只提示与当前 operator/readings/reserved 字的静态冲突，不代表禁用。\n\n")
    out.append("## 覆盖审计\n\n")
    out.append("| Item | Count |\n|---|---:|\n")
    out.append(line(["Yao positions", len(YAO_POSITIONS)]))
    out.append(line(["Four wings", len(WINGS)]))
    out.append(line(["Yao-wing rows", len(rows)]))
    out.append(line(["Unique pair surfaces", len({pair_surface(yao, wing) for yao, wing in rows})]))
    out.append(line(["Candidate operators", len(OPERATORS)]))

    out.append("\n## 6 爻位基础义名\n\n")
    out.append("| yao_code | fin_index | 爻位 | 古文单字候选 | 保留别名 | 结构位 | 儒 | 释 | 道 | English | Formal logic | 冲突提示 | operator_collision_ids |\n")
    out.append("|---|---:|---|---|---|---|---|---|---|---|---|---|---|\n")
    for yao in YAO_POSITIONS:
        code, idx, short, name, structural, default, modern, ru, fo, dao, english, formal = yao
        collision, ids = collision_info(short)
        out.append(line([code, idx, name, short, default, structural, ru, fo, dao, english, formal, collision, ids]))

    out.append("\n## 4 翼基础义名\n\n")
    out.append("| wing_code | wing_index | 翼 | 古文单字候选 | 保留别名 | 双字/现代汉语 | 儒 | 释 | 道 | English | Formal logic | 冲突提示 | operator_collision_ids |\n")
    out.append("|---|---:|---|---|---|---|---|---|---|---|---|---|---|\n")
    for wing in WINGS:
        code, idx, short, name, default, compound, modern, ru, fo, dao, english, formal = wing
        collision, ids = collision_info(short)
        out.append(line([code, idx, name, short, name, modern, ru, fo, dao, english, formal, collision, ids]))

    out.append("\n## 候选算子目录\n\n")
    out.append("| op_id | layer | 古文算子 | 保留别名 | type sketch | law / relation | English | Formal logic | 冲突提示 | operator_collision_ids |\n")
    out.append("|---|---|---|---|---|---|---|---|---|---|\n")
    for op_id, layer, surface, alias, type_sketch, law, english, formal in OPERATORS:
        collision, ids = collision_info(surface)
        out.append(line([op_id, layer, surface, alias, type_sketch, law, english, formal, collision, ids]))

    out.append("\n## 24 爻翼候选全表\n\n")
    out.append("| # | yao_index | wing_index | pair_code | 爻位 | 翼 | 古文候选 | 保留别名 | 双字/现代汉语 | 儒 | 释 | 道 | English | Formal logic | 冲突提示 | operator_collision_ids |\n")
    out.append("|---:|---:|---:|---|---|---|---|---|---|---|---|---|---|---|---|---|\n")
    for idx, (yao, wing) in enumerate(rows, 1):
        y_code, y_idx, y_short, y_name, y_struct, y_default, y_modern, y_ru, y_fo, y_dao, y_english, y_formal = yao
        w_code, w_idx, w_short, w_name, w_default, w_compound, w_modern, w_ru, w_fo, w_dao, w_english, w_formal = wing
        surface = pair_surface(yao, wing)
        collision, ids = collision_info(surface)
        out.append(line([
            idx,
            y_idx,
            w_idx,
            f"{y_code}.{w_code}",
            y_name,
            w_name,
            surface,
            pair_alias(yao, wing),
            y_modern + w_modern,
            y_ru + w_ru,
            y_fo + w_fo,
            y_dao + w_dao,
            f"{y_english} {w_english}",
            f"{y_formal} × {w_formal}",
            collision,
            ids,
        ]))

    out.append("\n## 后续 promotion 检查\n\n")
    out.append("1. 若要进入 parser，先决定 `初彖` 这类短 surface 是否优先于 `初之彖` 长别名。\n")
    out.append("2. 如果后续把十翼拆细，保留本表四翼作为 compact alias，不直接删除旧 surface。\n")
    out.append("3. 进入 WenSurface 前补 lex 单 token 审计、冲突提示和 native_decide 覆盖计数。\n")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("".join(out), encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)} with {len(rows)} yao-wing rows")


if __name__ == "__main__":
    main()
