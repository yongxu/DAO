#!/usr/bin/env python3
"""Generate a review table for proposed natural names of the 192 cells."""

from __future__ import annotations

import itertools
import re
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "docs-next" / "40_reference_参考" / "cell192-name-candidates.md"


SHI = [
    ("JI", 0, "Shi.ji", "已", "已", "已成", "past state"),
    ("JIN", 1, "Shi.jin", "今", "今", "当前", "present state"),
    ("WEI", 2, "Shi.wei", "未", "未", "未来", "future state"),
]


HEX_ALIASES = {
    "讼": "訟",
    "师": "師",
    "谦": "謙",
    "随": "隨",
    "蛊": "蠱",
    "临": "臨",
    "观": "觀",
    "贲": "賁",
    "剥": "剝",
    "复": "復",
    "无妄": "無妄",
    "颐": "頤",
    "大过": "大過",
    "离": "離",
    "恒": "恆",
    "晋": "晉",
    "大壮": "大壯",
    "损": "損",
    "渐": "漸",
    "归妹": "歸妹",
    "丰": "豐",
    "兑": "兌",
    "涣": "渙",
    "节": "節",
    "既济": "既濟",
    "未济": "未濟",
}


PROMOTED_GAP_FORMS = {
    "待", "争", "蓄", "塞", "备", "从", "临", "决", "断", "饰",
    "养", "过", "险", "附", "感", "壮", "难", "遇", "困", "归",
    "丰", "远", "悦", "信", "阻",
}


UNPROMOTED_GAP_FORMS = {"丽", "井", "鼎", "震", "大", "小"}


TRIGRAMS = {
    "111": ("乾", "天", "heaven"),
    "000": ("坤", "地", "earth"),
    "100": ("震", "雷", "thunder"),
    "010": ("坎", "水", "water"),
    "001": ("艮", "山", "mountain"),
    "110": ("兑", "泽", "lake"),
    "101": ("离", "火", "fire"),
    "011": ("巽", "风", "wind"),
}


# Bits are yao 1..6 from bottom to top, with 1 = yang and 0 = yin.
# Profiles are keyed by the six-bit hexagram literal and carry King Wen ordinal
# metadata. Cell192 rows below are emitted in Hexagram.allHex order and
# cross-reference this profile table.
HEX_PROFILES = [
    ("111111", 1, "乾", "䷀", "健", "健行", "创发", "自强", "妙有", "自然", "creative force", "top valuation / generative object"),
    ("000000", 2, "坤", "䷁", "顺", "承顺", "承载", "厚德", "空寂", "柔弱", "receptive ground", "bottom valuation / carrier object"),
    ("100010", 3, "屯", "䷂", "萌", "屯难", "初难", "创业", "缘起", "始生", "sprouting difficulty", "initial partial state"),
    ("010001", 4, "蒙", "䷃", "蒙", "蒙启", "启蒙", "教化", "无明", "朴", "unformed learning", "unknown proposition"),
    ("111010", 5, "需", "䷄", "待", "需待", "等待", "时中", "待缘", "守时", "waiting", "delayed obligation"),
    ("010111", 6, "讼", "䷅", "争", "讼争", "争讼", "辨义", "诤论", "不争", "contention", "contradiction / dispute"),
    ("010000", 7, "师", "䷆", "众", "师众", "组织", "正众", "众缘", "用兵", "organized multitude", "context set"),
    ("000010", 8, "比", "䷇", "亲", "亲比", "邻比", "亲仁", "和合", "相亲", "affiliation", "adjacency relation"),
    ("111011", 9, "小畜", "䷈", "蓄", "小蓄", "小蓄积", "蓄德", "薰习", "微积", "small accumulation", "bounded buffer"),
    ("110111", 10, "履", "䷉", "履", "履礼", "履行", "践礼", "戒行", "行道", "treading", "typed transition"),
    ("111000", 11, "泰", "䷊", "通", "通泰", "通泰", "太和", "安乐", "冲和", "peaceful passage", "consistent composition"),
    ("000111", 12, "否", "䷋", "塞", "否塞", "阻塞", "闭塞", "障", "闭", "blockage", "inconsistent blockage"),
    ("101111", 13, "同人", "䷌", "同", "同人", "协同", "同仁", "同体", "齐物", "fellowship", "equivalence class"),
    ("111101", 14, "大有", "䷍", "有", "大有", "富有", "富德", "福德", "有余", "great possession", "existential abundance"),
    ("001000", 15, "谦", "䷎", "谦", "谦德", "谦抑", "谦让", "无我", "不盈", "modesty", "weakening / lowering"),
    ("000100", 16, "豫", "䷏", "豫", "豫备", "预备", "悦豫", "随喜", "豫游", "readiness", "prepared possibility"),
    ("100110", 17, "随", "䷐", "随", "随顺", "跟随", "从善", "随缘", "因循", "following", "morphism following"),
    ("011001", 18, "蛊", "䷑", "治", "治蛊", "整治", "改过", "烦恼治", "反腐", "repairing corruption", "repair rewrite"),
    ("110000", 19, "临", "䷒", "临", "临下", "临近", "临民", "现前", "莅临", "approach", "evaluation context"),
    ("000011", 20, "观", "䷓", "观", "观照", "观察", "观德", "观照", "玄览", "contemplation", "observation function"),
    ("100101", 21, "噬嗑", "䷔", "决", "噬决", "裁决", "明刑", "择法", "断碍", "decisive biting", "decision / cut"),
    ("101001", 22, "贲", "䷕", "饰", "文饰", "文饰", "文质", "庄严", "素饰", "adornment", "annotation / presentation"),
    ("000001", 23, "剥", "䷖", "剥", "剥落", "剥落", "去伪", "坏灭", "损有", "stripping", "deletion"),
    ("100000", 24, "复", "䷗", "复", "返复", "返回", "复礼", "还灭", "反复", "return", "recursion / reset"),
    ("100111", 25, "无妄", "䷘", "诚", "无妄", "无妄", "诚正", "正念", "无妄", "without falsity", "soundness"),
    ("111001", 26, "大畜", "䷙", "藏", "大蓄", "大蓄积", "畜德", "藏识", "蓄势", "great storage", "memory store"),
    ("100001", 27, "颐", "䷚", "养", "颐养", "养护", "养正", "资粮", "养生", "nourishment", "input resource"),
    ("011110", 28, "大过", "䷛", "过", "大过", "过载", "过中", "过患", "过度", "great excess", "overflow / exception"),
    ("010010", 29, "坎", "䷜", "陷", "险陷", "险陷", "习险", "苦", "险", "abyss", "constraint trap"),
    ("101101", 30, "离", "䷝", "丽", "附丽", "明辨", "明德", "明", "离明", "radiance", "distinction / embedding"),
    ("001110", 31, "咸", "䷞", "感", "感通", "感通", "感应", "触", "相感", "influence", "coupling"),
    ("011100", 32, "恒", "䷟", "恒", "恒久", "恒常", "恒德", "相续", "常道", "duration", "invariant"),
    ("001111", 33, "遁", "䷠", "遁", "退遁", "退避", "避世", "出离", "遁世", "withdrawal", "abstraction / hiding"),
    ("111100", 34, "大壮", "䷡", "壮", "壮大", "壮盛", "刚健", "精进", "强行", "great vigor", "strengthening"),
    ("000101", 35, "晋", "䷢", "进", "晋进", "晋升", "进德", "增上", "进火", "advance", "monotone progress"),
    ("101000", 36, "明夷", "䷣", "晦", "明夷", "晦明", "韬光", "暗蔽", "藏明", "darkening of light", "hidden information"),
    ("101011", 37, "家人", "䷤", "家", "家序", "家序", "齐家", "眷属", "室家", "household order", "local context"),
    ("110101", 38, "睽", "䷥", "异", "睽异", "分歧", "辨异", "别相", "殊方", "divergence", "disequality"),
    ("001010", 39, "蹇", "䷦", "阻", "蹇阻", "艰阻", "知止", "难行", "艰难", "obstruction", "proof obligation"),
    ("010100", 40, "解", "䷧", "解", "解纷", "解除", "释难", "解脱", "释结", "release", "resolution"),
    ("110001", 41, "损", "䷨", "损", "损减", "减损", "省己", "损减", "减损", "decrease", "decrement"),
    ("100011", 42, "益", "䷩", "益", "增益", "增益", "益善", "增益", "滋益", "increase", "increment"),
    ("111110", 43, "夬", "䷪", "断", "决断", "决断", "决义", "决择", "决", "breakthrough", "cut / decide"),
    ("011111", 44, "姤", "䷫", "遇", "相遇", "遭遇", "遇合", "遇缘", "邂逅", "encounter", "event encounter"),
    ("000110", 45, "萃", "䷬", "聚", "萃聚", "聚集", "群萃", "和集", "会聚", "gathering", "aggregation"),
    ("011000", 46, "升", "䷭", "升", "升进", "上升", "升德", "增上", "上升", "ascending", "lifting"),
    ("010110", 47, "困", "䷮", "困", "困穷", "困局", "困而学", "苦缚", "困", "exhaustion", "saturated constraint"),
    ("011010", 48, "井", "䷯", "井", "井养", "井养", "养民", "法泉", "不迁", "well", "shared resource"),
    ("101110", 49, "革", "䷰", "革", "变革", "变革", "革故", "转依", "变", "revolution", "rewrite transform"),
    ("011101", 50, "鼎", "䷱", "鼎", "鼎定", "定器", "立器", "法器", "器", "cauldron", "container / composition"),
    ("100100", 51, "震", "䷲", "动", "震动", "震动", "警惧", "动相", "动", "arousal", "event trigger"),
    ("001001", 52, "艮", "䷳", "止", "艮止", "止息", "知止", "止", "止", "stillness", "fixed point"),
    ("001011", 53, "渐", "䷴", "渐", "渐进", "渐进", "渐修", "次第", "渐化", "gradual progress", "convergence"),
    ("110100", 54, "归妹", "䷵", "归", "归妹", "归配", "正位", "眷属", "归", "marrying maiden", "dependent pairing"),
    ("101100", 55, "丰", "䷶", "丰", "丰盛", "丰盛", "丰亨", "光明", "盛", "abundance", "fullness"),
    ("001101", 56, "旅", "䷷", "旅", "旅居", "旅居", "行旅", "行脚", "游", "travelling", "transient state"),
    ("011011", 57, "巽", "䷸", "入", "巽入", "入顺", "逊顺", "入法", "入", "penetration", "substitution"),
    ("110110", 58, "兑", "䷹", "悦", "兑悦", "喜悦", "悦民", "喜", "悦", "joyous exchange", "satisfaction"),
    ("010011", 59, "涣", "䷺", "散", "涣散", "涣散", "散难", "散乱", "散", "dispersion", "distribution"),
    ("110010", 60, "节", "䷻", "节", "节制", "节制", "制礼", "律仪", "节", "limitation", "restriction"),
    ("110011", 61, "中孚", "䷼", "信", "中信", "中信", "诚信", "信", "孚", "inner trust", "sound witness"),
    ("001100", 62, "小过", "䷽", "逾", "小过", "小过", "过慎", "轻过", "微过", "small excess", "local exception"),
    ("101010", 63, "既济", "䷾", "济", "既济", "完成", "成事", "圆成", "既成", "completion", "settled proof"),
    ("010101", 64, "未济", "䷿", "涉", "未济", "未成", "慎终", "未圆", "未成", "not yet complete", "open obligation"),
]


def md(s: object) -> str:
    return str(s).replace("|", "\\|")


def read_text(path: str) -> str:
    p = ROOT / path
    return p.read_text(encoding="utf-8") if p.exists() else ""


def split_cjk_chars(s: str) -> set[str]:
    return {ch for ch in s if "\u4e00" <= ch <= "\u9fff"}


def code_of_ctor(ctor: str) -> str:
    return ctor.replace("_", "-")


@lru_cache(maxsize=1)
def collision_sets() -> tuple[
    dict[str, set[str]],
    dict[str, set[str]],
    dict[str, set[str]],
    set[str],
]:
    reading_text = read_text("formal/SSBX/Text/OperatorReadings.lean")
    operator_text = read_text("formal/SSBX/Text/WenyanOperators.lean")
    lex_text = read_text("formal/SSBX/Foundation/Wen/WenSurface/Lex.lean")
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

    compound_surfaces: dict[str, set[str]] = {}
    for surface, ctor in re.findall(r'\("([^"]+)",\s*\.([A-Z0-9_]+)\)', lex_text):
        compound_surfaces.setdefault(surface, set()).add(code_of_ctor(ctor))

    hex_names = {p[2] for p in HEX_PROFILES}
    return surface_readings, operator_form_chars, compound_surfaces, hex_names


def collision_info(single: str, compound: str, modern: str) -> tuple[str, str, str]:
    surface_readings, operator_forms, compound_surfaces, hex_names = collision_sets()
    flags: list[str] = []
    codes: set[str] = set()
    if single in surface_readings:
        flags.append("reading")
        codes.update(surface_readings[single])
    if single in operator_forms:
        flags.append("operator-form")
        codes.update(operator_forms[single])
    if single in hex_names or compound in hex_names:
        flags.append("hex-name")
    if single in PROMOTED_GAP_FORMS:
        flags.append("promoted-gap")
    if single in UNPROMOTED_GAP_FORMS:
        flags.append("unpromoted-gap")
    if single in {"已", "今", "未", "之", "者", "令", "真", "假"}:
        flags.append("reserved")
    if compound in compound_surfaces or modern in compound_surfaces:
        flags.append("compound-surface")
        codes.update(compound_surfaces.get(compound, set()))
        codes.update(compound_surfaces.get(modern, set()))
    gap_policy = (
        "promoted" if single in PROMOTED_GAP_FORMS else
        "unpromoted" if single in UNPROMOTED_GAP_FORMS else
        "none"
    )
    return (
        ", ".join(flags) if flags else "open",
        ", ".join(sorted(codes)) if codes else "",
        gap_policy,
    )


def alias_source(name: str) -> str:
    alias = HEX_ALIASES.get(name)
    if alias is None:
        return "canonical"
    return f"canonical; trad={alias}"


def cell_id(bits: str, shi_code: str) -> str:
    return f"H{bits}.{shi_code}"


def trigram_label(bits: str) -> str:
    lower = bits[:3]
    upper = bits[3:]
    lo_name, lo_image, _ = TRIGRAMS[lower]
    up_name, up_image, _ = TRIGRAMS[upper]
    return f"上{up_name}下{lo_name} / {up_image}{lo_image}"


def line(cols: list[object]) -> str:
    return "| " + " | ".join(md(c) for c in cols) + " |\n"


def main() -> None:
    profiles_by_bits = {row[0]: row for row in HEX_PROFILES}
    assert len(HEX_PROFILES) == 64
    assert len(profiles_by_bits) == 64
    all_bits = ["".join(bits) for bits in itertools.product("10", repeat=6)]
    assert len(all_bits) == 64
    assert set(all_bits) == set(profiles_by_bits)

    rows: list[tuple[str, tuple, tuple]] = []
    for bits in all_bits:
        profile = profiles_by_bits[bits]
        for shi in SHI:
            rows.append((bits, shi, profile))
    assert len(rows) == 192
    assert len({cell_id(bits, shi[0]) for bits, shi, _ in rows}) == 192

    out: list[str] = []
    out.append("# Cell192 自然命名候选全表\n\n")
    out.append("> Generated by `python3 scripts/generate_cell192_name_candidates.py`.\n")
    out.append("> Sources: `formal/SSBX/Foundation/Bagua/Cell192.lean`, `formal/SSBX/Foundation/Yi/Yi.lean`, `formal/SSBX/Foundation/Wen/WenSurface/Reading.lean`.\n\n")
    out.append("目的：给 192 个 `Cell192 = Hexagram × Shi` 格点准备可审阅的自然语言 surface 候选。六十四卦名继续保留为 canonical alias；本表只提出额外的古文/现代汉语/跨传统/英文/形式逻辑对应名，后续由人工挑选后再 promotion 到 parser。\n\n")
    out.append("## 审阅规则\n\n")
    out.append("- 枚举顺序跟 `Cell192.all` 一致：`Hexagram.allHex` 的六爻 bit 序，外乘 `已/今/未`。\n")
    out.append("- `Habcdef.SHI` 中 `abcdef` 是自下而上的六爻，`1=阳`、`0=阴`。\n")
    out.append("- `古文单字候选` 是 parser 主候选；`192 古文候选` 用 `已/今/未 + 单字` 保持 192 格唯一。\n")
    out.append("- `双字/现代汉语候选` 可以更自然，但 promotion 时要检查最长词法、同字歧义与已有 operator reading。\n")
    out.append("- `冲突提示` 是保守静态提示：`reading`/`operator-form`/`hex-name`/`promoted-gap`/`unpromoted-gap`/`reserved`/`compound-surface` 不等于禁用，只表示需要显式 resolver 规则。\n\n")
    out.append("## 覆盖审计\n\n")
    out.append("| Item | Count |\n|---|---:|\n")
    out.append(line(["Hex profiles", len(HEX_PROFILES)]))
    out.append(line(["Shi phases", len(SHI)]))
    out.append(line(["Cell192 rows", len(rows)]))
    out.append(line(["Unique cell ids", len({cell_id(bits, shi[0]) for bits, shi, _ in rows})]))
    out.append("\n## 64 基础义名\n\n")
    out.append("| 序卦 | 卦 | bits | 八卦/卦象 | alias_source | 古文单字候选 | 古文复合 | 双字/现代汉语 | 儒 | 释 | 道 | English | Formal logic | 冲突提示 | operator_collision_ids | gap_policy |\n")
    out.append("|---:|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n")
    for profile in sorted(HEX_PROFILES, key=lambda p: p[1]):
        bits, kw, name, symbol, single, compound, modern, ru, fo, dao, english, formal = profile
        collision, operator_ids, gap_policy = collision_info(single, compound, modern)
        out.append(line([
            kw,
            f"{symbol} {name}",
            bits,
            trigram_label(bits),
            alias_source(name),
            single,
            compound,
            modern,
            ru,
            fo,
            dao,
            english,
            formal,
            collision,
            operator_ids,
            gap_policy,
        ]))

    out.append("\n## 192 Cell 候选全表\n\n")
    out.append("| # | cell_index_0_191 | Cell192 | enum_source | hex_all_index | shi_index | shi_ctor | 卦序 | 卦 | 时 | hex_literal_y1_y6 | 八卦/卦象 | alias_source | 古文单字候选 | 192 古文候选 | 双字/现代汉语候选 | 儒 | 释 | 道 | English | Formal logic | resolve_atom_kind | duplicate_key_check | 冲突提示 | operator_collision_ids | gap_policy |\n")
    out.append("|---:|---:|---|---|---:|---:|---|---:|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n")
    for idx, (bits, shi, profile) in enumerate(rows, 1):
        shi_code, shi_index, shi_ctor, shi_zh, shi_prefix, shi_modern, shi_formal = shi
        _, kw, name, symbol, single, compound, modern, ru, fo, dao, english, formal = profile
        cell = cell_id(bits, shi_code)
        collision, operator_ids, gap_policy = collision_info(single, compound, modern)
        out.append(line([
            idx,
            idx - 1,
            cell,
            "Hexagram.allHex × Shi.all",
            (idx - 1) // 3,
            shi_index,
            shi_ctor,
            kw,
            f"{symbol} {name}",
            shi_zh,
            bits,
            trigram_label(bits),
            alias_source(name),
            single,
            f"{shi_prefix}{single}",
            f"{shi_modern}{modern}",
            f"{shi_zh}{ru}",
            f"{shi_zh}{fo}",
            f"{shi_zh}{dao}",
            f"{shi_formal} of {english}",
            f"{shi_formal} × {formal}",
            "candidate Cell literal",
            "unique",
            collision,
            operator_ids,
            gap_policy,
        ]))

    out.append("\n## 后续 promotion 检查\n\n")
    out.append("1. 对候选主 surface 做 `lexWen` 最长匹配审计，尤其是双字/现代汉语候选。\n")
    out.append("2. 对 `reading`、`operator-form`、`hex-name`、`promoted-gap`、`unpromoted-gap`、`reserved` 标记逐项决定优先级；不要隐式覆盖现有八卦/卦名 literal。\n")
    out.append("3. 先登记 alias 与诊断，再让 evaluator 接语义；Cell literal promotion 不应伪装成 operator denotation。\n")
    out.append("4. promotion 后补 native_decide：64 基础义名、192 组合义名、旧卦名 alias 全部可解析且无漏项。\n")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("".join(out), encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)} with {len(rows)} Cell192 rows")


if __name__ == "__main__":
    main()
