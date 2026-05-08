#!/usr/bin/env python3
"""Smoke checks for the `wenyan-surface` CLI JSON mode.

The human-facing modes intentionally include diagrams, Lean `repr` output, and
diagnostic prose.  This script only asserts the stable JSON behavior surface.
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys


REPO_ROOT = Path(__file__).resolve().parents[1]
BUILT_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "wenyan-surface"

CASES = [
    ("推 一", {"ok": True, "kind": "hex", "idx": 2}),
    ("損 乾", {"ok": True, "kind": "hex", "idx": 63}),
    ("同 一 一", {"ok": True, "kind": "bool", "value": True}),
    ("之又 不 真", {"ok": True, "kind": "bool", "value": True}),
    ("错 乾", {"ok": True, "kind": "hex", "idx": 63}),
    ("轉 乾", {"ok": True, "kind": "hex", "idx": 0}),
    ("伸 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("屈 乾", {"ok": True, "kind": "hex", "idx": 63}),
    ("止 乾", {"ok": True, "kind": "hex", "idx": 0}),
    ("進 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("退 乾", {"ok": True, "kind": "hex", "idx": 63}),
    ("藏 乾", {"ok": True, "kind": "hex", "idx": 63}),
    ("露 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("使 推 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("若 真", {"ok": True, "kind": "bool", "value": True}),
    ("再 推 乾", {"ok": True, "kind": "hex", "idx": 2}),
    ("宜 真 假", {"ok": True, "kind": "bool", "value": False}),
    ("能 假 真", {"ok": True, "kind": "bool", "value": True}),
    ("凡 甲 同 甲 甲", {"ok": True, "kind": "bool", "value": True}),
    ("（推 一）", {"ok": True, "kind": "hex", "idx": 2}),
    ("同 （推 一） （推 一）", {"ok": True, "kind": "bool", "value": True}),
    ("則 真 假", {"ok": True, "kind": "bool", "value": False}),
    ("遂 真 假", {"ok": True, "kind": "bool", "value": False}),
    ("且 真 假", {"ok": True, "kind": "bool", "value": False}),
    ("但 真 假", {"ok": True, "kind": "bool", "value": False}),
    ("非 乾 坤", {"ok": True, "kind": "bool", "value": True}),
    ("莫 者 甲 同 甲 一", {"ok": True, "kind": "bool", "value": False}),
    ("或 者 甲 同 甲 一", {"ok": True, "kind": "bool", "value": True}),
    ("過半 者 甲 真", {"ok": True, "kind": "bool", "value": True}),
    ("（而 者 甲 推 甲 者 甲 損 甲） 之 一", {"ok": True, "kind": "hex", "idx": 1}),
    ("而 推 損 一", {"ok": True, "kind": "hex", "idx": 1}),
    ("而 损 推 一", {"ok": True, "kind": "hex", "idx": 1}),
    ("（推） 一", {"ok": True, "kind": "hex", "idx": 2}),
    ("（同 乾） 乾", {"ok": True, "kind": "bool", "value": True}),
    ("者 甲 推 甲 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("比", {"ok": True, "kind": "hex", "idx": 47}),
    ("同 比 比", {"ok": True, "kind": "bool", "value": True}),
    ("比 乾 坤", {"ok": True, "kind": "bool", "value": False}),
    ("同 益 乾", {"ok": True, "kind": "bool", "value": False}),
    ("在 乾 乾", {"ok": True, "kind": "bool", "value": True}),
    ("在 乾 坤", {"ok": True, "kind": "bool", "value": False}),
    ("含 乾 坤", {"ok": True, "kind": "bool", "value": False}),
    ("識 乾", {"ok": True, "kind": "bool", "value": True}),
    ("大一 乾", {"ok": True, "kind": "bool", "value": True}),
    ("偶 乾 坤", {"ok": True, "kind": "hexPair", "values": [{"idx": 0, "label": " («乾»)"}, {"idx": 63, "label": " («坤»)"}]}),
    ("偕 乾 坤", {"ok": True, "kind": "hexPair", "values": [{"idx": 0, "label": " («乾»)"}, {"idx": 63, "label": " («坤»)"}]}),
    ("兩 乾", {"ok": True, "kind": "hexPair", "values": [{"idx": 0, "label": " («乾»)"}, {"idx": 0, "label": " («乾»)"}]}),
    ("聚 乾", {"ok": True, "kind": "hexList", "values": [{"idx": 0, "label": " («乾»)"}]}),
    ("散 聚 乾", {"ok": True, "kind": "hex", "idx": 0}),
    ("五行 乾", {"ok": True, "kind": "hexList", "values": [{"idx": 0, "label": " («乾»)"}]}),
    ("改 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("起 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("静 乾", {"ok": True, "kind": "hex", "idx": 0}),
    ("恒 乾", {"ok": True, "kind": "hex", "idx": 0}),
    ("不动 乾", {"ok": True, "kind": "hex", "idx": 0}),
    ("錯綜 乾", {"ok": True, "kind": "hex", "idx": 63}),
    ("交错 乾", {"ok": True, "kind": "hex", "idx": 63}),
    ("复 乾", {"ok": True, "kind": "hex", "idx": 0}),
    ("归一 乾", {"ok": True, "kind": "hex", "idx": 0}),
    ("展 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("初动 乾", {"ok": True, "kind": "hex", "idx": 1}),
    ("承变 乾", {"ok": True, "kind": "hex", "idx": 2}),
    ("际变 乾", {"ok": True, "kind": "hex", "idx": 4}),
    ("化 乾", {"ok": True, "kind": "hex", "idx": 2}),
    ("反 乾", {"ok": True, "kind": "hex", "idx": 63}),
    ("反 真", {"ok": True, "kind": "bool", "value": False}),
    ("器", {"ok": True, "kind": "hex", "idx": 17}),
    ("鼎", {"ok": True, "kind": "hex", "idx": 17}),
    ("大壯", {"ok": True, "kind": "hex", "idx": 48}),
    ("曰 乾 乾", {"ok": True, "kind": "catalogue", "operatorCode": "E-2", "operatorTitle": "曰", "signatureKind": "TEXT", "arity": 2}),
]

NEGATIVE_CASES = [
    ("瓜", {"phase": "resolve", "code": "no_reading", "surface": "瓜", "startCol": 0, "endCol": 1}),
    ("推 乾 之", {"phase": "parse", "code": "leftover_tokens", "surface": "之", "startCol": 4, "endCol": 5, "leftoverCount": 1}),
    ("达 乾 坤", {"phase": "resolve", "code": "no_reading", "surface": "达", "startCol": 0, "endCol": 1}),
    ("径 乾", {"phase": "resolve", "code": "no_reading", "surface": "径", "startCol": 0, "endCol": 1}),
    ("隙 乾", {"phase": "resolve", "code": "no_reading", "surface": "隙", "startCol": 0, "endCol": 1}),
    ("名分 乾", {"phase": "resolve", "code": "ambiguous_reading", "surface": "名分", "startCol": 0, "endCol": 2, "candidateCount": 2}),
    ("鼎 乾", {"phase": "unsupported", "code": "unpromoted_hexagram_gap", "surface": "鼎", "startCol": 0, "endCol": 1}),
    ("丽", {"phase": "unsupported", "code": "unpromoted_hexagram_gap", "surface": "丽", "startCol": 0, "endCol": 1}),
    ("大", {"phase": "unsupported", "code": "unpromoted_hexagram_gap", "surface": "大", "startCol": 0, "endCol": 1}),
    ("乾 之 坤", {"phase": "type", "code": "type_mismatch", "expectedType": "function", "actualType": "Hex"}),
    ("不 乾", {"phase": "type", "code": "type_mismatch", "expectedType": "Bool", "actualType": "Hex"}),
    ("曰 真 真", {"phase": "type", "code": "type_mismatch", "expectedType": "Hex", "actualType": "Bool"}),
    ("或 真", {"phase": "resolve", "code": "ambiguous_reading", "surface": "或", "startCol": 0, "endCol": 1, "candidateCount": 2}),
    ("故 假 假", {"phase": "resolve", "code": "ambiguous_reading", "surface": "故", "startCol": 0, "endCol": 1, "candidateCount": 3}),
    ("而 不 不 真", {"phase": "type", "code": "type_mismatch", "expectedType": "(Hex -> Hex)", "actualType": "(Bool -> Bool)", "surface": "不", "startCol": 2, "endCol": 3}),
    ("在 乾", {"phase": "denote", "code": "denote_failed", "expectedType": "Hex", "actualType": "(Hex -> Bool)"}),
    ("（推 一", {"phase": "parse", "code": "unmatched_open_bracket", "surface": "（", "startCol": 0, "endCol": 1}),
    ("推 一）", {"phase": "parse", "code": "unmatched_close_bracket", "surface": "）", "startCol": 3, "endCol": 4}),
]

CLI_CASES = [
    (["--tokens", "推 一"], "0:推/w1\n2:一/w1"),
    (["--tokens", "推　一"], "0:推/w1\n2:一/w1"),
    (["--tokens", "（推 一）"], "0:（/w1\n1:推/w1\n3:一/w1\n4:）/w1"),
    (["--resolve", "推 一"], "0:推/w1 => op[T-10:推]"),
    (["--resolve", "在"], "0:在/w1 => op[R-1:在]"),
    (["--resolve", "五行"], "0:五行/w2 => op[Y-2:五行"),
    (["--resolve", "陰与陽"], "0:陰与陽/w3 => op[Y-1:"),
    (["--ast", "推 一"], "SurfaceExpr.app"),
    (["--ast", "（推 一）"], "SurfaceExpr.grouped"),
    (["--ast", "乾 之 坤"], "SurfaceExpr.marker"),
    (["--typecheck", "同 一 一"], "type Bool"),
    (["--typecheck", "（推 一）"], "type Hex"),
    (["--typecheck", "推"], "type (Hex -> Hex)"),
    (["--typecheck", "改"], "type (Hex -> Hex)"),
    (["--typecheck", "不"], "type (Bool -> Bool)"),
    (["--typecheck", "同 乾"], "type (Hex -> Bool)"),
    (["--typecheck", "三"], "type ((Hex -> Bool) -> Bool)"),
    (["--typecheck", "在 乾"], "type (Hex -> Bool)"),
    (["--typecheck", "偶 乾 坤"], "type (Hex * Hex)"),
    (["--typecheck", "聚 乾"], "type List[Hex]"),
    (["--typecheck", "（推）"], "type (Hex -> Hex)"),
    (["--typecheck", "（同 乾）"], "type (Hex -> Bool)"),
    (["--operator", "T-10"], "executable: yes"),
    (["--operator", "T-1"], "executable note: 化: Hex y2 transform"),
    (["--operator", "R-6"], "executable note: 正: Hex identity / normalize in place"),
    (["--operator", "Z-32"], "executable note: 自: reflexive Hex endomap application"),
    (["--operator", "Q-8"], "executable note: 唯: finite unique-existence"),
    (["--operator", "D-10"], "executable note: 過半/大半: finite majority"),
    (["--operator", "F-3"], "executable note: 進/进: forward Hex motion"),
    (["--operator", "K-6"], "executable note: 使: causative Hex endomap application"),
    (["--operator", "M-3"], "executable note: 當/当: guarded modal condition"),
    (["--operator", "M-5"], "executable note: 可: finite possibility"),
    (["--operator", "S-4"], "executable note: 若: truth-core conditional marker"),
    (["--operator", "D-2"], "executable note: 再: repeat a Hex endomap once"),
    (["--operator", "Z-10"], "executable note: 藏: concealment transition"),
    (["--operator", "R-12"], "executable note: 偶/耦: Hex pair carrier constructor"),
    (["--operator", "R-14"], "executable note: 與/与: Hex pair carrier constructor"),
    (["--operator", "R-15"], "executable note: 偕: Hex pair carrier constructor"),
    (["--operator", "T-3"], "executable note: 易: binary object exchange carrier"),
    (["--operator", "T-11"], "executable note: 致: binary object carrier"),
    (["--operator", "K-5"], "executable note: 致: causative binary object carrier"),
    (["--operator", "N-8"], "executable note: 別/别: binary object distinction carrier"),
    (["--operator", "I-7"], "executable note: 合: binary object combination carrier"),
    (["--operator", "P-11"], "executable note: 尺: Hex pair carrier constructor; no metric semantics"),
    (["--operator", "P-13"], "executable note: 圜/圆: Hex pair carrier constructor; no geometric semantics"),
    (["--operator", "P-22"], "executable note: 說/说: Hex pair carrier constructor; no rhetorical semantics"),
    (["--operator", "D-8"], "executable note: 餘/余: Hex pair carrier constructor; no arithmetic remainder"),
    (["--operator", "L-5"], "executable note: 參同/参同: singleton Hex list carrier; no verification semantics"),
    (["--operator", "X-4"], "executable note: 群: singleton Hex list carrier; no social grouping semantics"),
    (["--operator", "Z-7"], "executable note: 雜/杂: singleton Hex list carrier; no mixture semantics"),
    (["--operator", "Z-21"], "executable note: 攝/摄: singleton Hex list carrier; no subsumption semantics"),
    (["--operator", "X-14"], "executable note: 積/积: two-input aggregate carrier; no arithmetic accumulation"),
    (["--operator", "Z-19"], "executable note: 積/积: two-input aggregate carrier; no arithmetic accumulation"),
    (["--operator", "CHU-9"], "executable note: 集: singleton Hex list carrier"),
    (["--operator", "H-8"], "executable note: 體/体與用: paired facet carrier via duplicate Hex; no essence/function decomposition"),
    (["--operator", "Y-1"], "executable note: 陰/阴與陽/阳: paired facet carrier via duplicate Hex; no yin-yang decomposition"),
    (["--operator", "Y-6"], "executable note: 氣/气: medical state projection anchor as identity; no qi physiology semantics"),
    (["--operator", "Y-7"], "executable note: 血: medical state projection anchor as identity; no blood physiology semantics"),
    (["--operator", "Y-8"], "executable note: 精: medical state projection anchor as identity; no essence physiology semantics"),
    (["--operator", "Y-10"], "executable note: 升/降: medical movement-state projection anchor as identity; no directional physiology semantics"),
    (["--operator", "Y-11"], "executable note: 開/闔/樞: medical phase projection anchor as identity; no channel mechanics semantics"),
    (["--operator", "Y-12"], "executable note: 經/絡: medical channel projection anchor as identity; no meridian semantics"),
    (["--operator", "Y-13"], "executable note: 表/裡: medical surface/interior projection anchor as identity; no diagnostic semantics"),
    (["--operator", "Y-14"], "executable note: 寒/熱: medical thermal-state projection anchor as identity; no pathology semantics"),
    (["--operator", "Y-15"], "executable note: 虛/實: medical deficiency/excess projection anchor as identity; no pathology semantics"),
    (["--operator", "Y-21"], "executable note: 標/标本: paired facet carrier via duplicate Hex; no root/branch decomposition"),
    (["--operator", "Y-22"], "executable note: 營/营與衛/卫: paired facet carrier via duplicate Hex; no medical channel decomposition"),
    (["--operator", "Y-23"], "executable note: 通/滯: medical patency projection anchor as identity; no treatment semantics"),
    (["--operator", "Y-24"], "executable note: 五运六气: medical cosmological-state projection anchor as identity; no calendrical physiology semantics"),
    (["--operator", "Y-25"], "executable note: 上工/中工/下工: medical skill-grade projection anchor as identity; no practitioner evaluation semantics"),
    (["--operator", "Y-26"], "executable note: 出/入: medical ingress/egress projection anchor as identity; no physiological motion semantics"),
    (["--operator", "Y-27"], "executable note: 候: diagnostic query anchor as identity; no observation protocol semantics"),
    (["--operator", "X-1"], "executable note: 性: social nature-state projection anchor as identity; no anthropology semantics"),
    (["--operator", "C-5"], "executable note: 外: Hex projection anchor as identity; no spatial model"),
    (["--operator", "C-6"], "executable note: 內/内: Hex projection anchor as identity; no spatial model"),
    (["--operator", "B-1"], "executable note: 始: Hex endpoint/extractor anchor as identity"),
    (["--operator", "B-7"], "executable note: 極/极: Hex endpoint/extractor anchor as identity"),
    (["--operator", "R-5"], "executable note: 中: positional extractor anchor as identity; no geometry semantics"),
    (["--operator", "C-4"], "executable note: 中: containment extractor anchor as identity; no spatial model"),
    (["--operator", "C-7"], "executable note: 表: surface projection anchor as identity; no spatial model"),
    (["--operator", "C-8"], "executable note: 裡/里: interior projection anchor as identity; no spatial model"),
    (["--operator", "B-2"], "executable note: 終/终: Hex endpoint/extractor anchor as identity"),
    (["--operator", "P-10"], "executable note: 端: Mohist endpoint anchor as identity; no geometry semantics"),
    (["--operator", "P-12"], "executable note: 中: Mohist middle-point anchor as identity; no geometry semantics"),
    (["--operator", "G-8"], "executable note: 兼/合: Names-school binary constructor carrier; no ontology semantics"),
    (["--operator", "P-3"], "executable note: 兼: singleton Hex aggregate carrier; no universal inclusion semantics"),
    (["--operator", "L-13"], "executable note: 一: Legalist unification aggregate carrier; no legal theory semantics"),
    (["--operator", "G-9"], "executable note: 別/别: Names-school facet carrier via duplicate Hex; no separation semantics"),
    (["--operator", "H-1"], "executable note: 道: extractor anchor as identity; no Dao semantics"),
    (["--operator", "H-2"], "executable note: 理: extractor anchor as identity; no principle semantics"),
    (["--operator", "H-3"], "executable note: 勢/势: extractor anchor as identity; no tendency semantics"),
    (["--operator", "H-4"], "executable note: 機/机: extractor anchor as identity; no opportunity semantics"),
    (["--operator", "H-5"], "executable note: 法: Hex pair carrier constructor; no law/norm semantics"),
    (["--operator", "H-6"], "executable note: 象: extractor anchor as identity; no image semantics"),
    (["--operator", "P-2"], "executable note: 體/体: Mohist part extractor anchor as identity; no part-whole semantics"),
    (["--operator", "P-6"], "executable note: 久: temporal extractor anchor as identity; no duration semantics"),
    (["--operator", "P-7"], "executable note: 宇: spatial extractor anchor as identity; no spatial extent semantics"),
    (["--operator", "P-18"], "executable note: 法: Mohist model extractor anchor as identity; no rule semantics"),
    (["--operator", "P-24"], "executable note: 類/类: Mohist class extractor anchor as identity; no taxonomy semantics"),
    (["--operator", "G-2"], "executable note: 物: concrete object anchor as identity; no ontology semantics"),
    (["--operator", "G-4"], "executable note: 實/实: concrete actuality anchor as identity; no ontology semantics"),
    (["--operator", "G-5"], "executable note: 位: position extractor anchor as identity; no role ontology"),
    (["--operator", "L-3"], "executable note: 勢/势: Legalist power-position extractor anchor as identity; no governance semantics"),
    (["--operator", "L-12"], "executable note: 利: benefit extractor anchor as identity; no utility semantics"),
    (["--operator", "L-15"], "executable note: 度: Legalist measure extractor anchor as identity; no metric semantics"),
    (["--operator", "Z-23"], "executable note: 萌: incipient object anchor as identity; no germination semantics"),
    (["--operator", "Z-24"], "executable note: 兆: omen extractor anchor as identity; no prognostic semantics"),
    (["--operator", "Z-26"], "executable note: 占: divination query anchor as identity; no divinatory semantics"),
    (["--operator", "Z-27"], "executable note: 卜: divination query anchor as identity; no divinatory semantics"),
    (["--operator", "Z-34"], "executable note: 觀/观: observation query anchor as identity; no perceptual semantics"),
    (["--operator", "Z-35"], "executable note: 察: inspection query anchor as identity; no investigation semantics"),
    (["--operator", "ZHU-9"], "executable note: 天理: Zhuangzi pattern extractor anchor as identity; no cosmological semantics"),
    (["--operator", "ZHU-10"], "executable note: 方: modifier anchor as identity; no direction/method semantics"),
    (["--operator", "SUN-1"], "executable note: 形: military signal anchor as identity; no formation semantics"),
    (["--operator", "SUN-2"], "executable note: 勢/势: military two-input extractor carrier; no force-position semantics"),
    (["--operator", "SUN-3"], "executable note: 虛/虚: military weakness extractor anchor as identity; no tactical semantics"),
    (["--operator", "SUN-4"], "executable note: 實/实: military strength extractor anchor as identity; no tactical semantics"),
    (["--operator", "SUN-5"], "executable note: 奇: military process anchor as identity; no tactical-surprise semantics"),
    (["--operator", "SUN-14"], "executable note: 知: military intelligence extractor carrier; no epistemic semantics"),
    (["--operator", "CHU-4"], "executable note: 登: Chu-ci ascent extractor anchor as identity; no elevation semantics"),
    (["--operator", "CHU-5"], "executable note: 望: Chu-ci vantage extractor carrier; no visual semantics"),
    (["--operator", "LIJ-4"], "executable note: 位: ritual role-position extractor anchor as identity; no ritual ontology"),
    (["--operator", "LIJ-5"], "executable note: 儀/仪: ritual protocol anchor as identity; no ritual-procedure semantics"),
    (["--operator", "LIJ-7"], "executable note: 中: ritual equilibrium extractor anchor as identity; no affective semantics"),
    (["--operator", "LIJ-11"], "executable note: 獨/独: ritual solitude extractor anchor as identity; no individuation semantics"),
    (["--operator", "ZA-3"], "executable note: 心君: supervisory anchor as identity; no heart-governance semantics"),
    (["--operator", "ZA-5"], "executable note: 精: inner-cultivation process anchor as identity; no cultivation semantics"),
    (["--operator", "ZA-6"], "executable note: 時/时: monthly-order time anchor as identity; no calendrical semantics"),
    (["--operator", "ZA-7"], "executable note: 令: monthly-order directive anchor as identity; no calendrical mandate semantics"),
    (["--operator", "ZA-11"], "executable note: 督: supervisory anchor as identity; no control semantics"),
    (["--operator", "S-9"], "executable note: 既: aspect anchor as identity; no completed-time semantics"),
    (["--operator", "S-10"], "executable note: 將/将: aspect anchor as identity; no prospective-time semantics"),
    (["--operator", "S-11"], "executable note: 方: aspect anchor as identity; no progressive-time semantics"),
    (["--operator", "S-12"], "executable note: 嘗/尝: aspect anchor as identity; no experiential-time semantics"),
    (["--operator", "S-17"], "executable note: 未: aspect anchor as identity; no future/negation semantics"),
    (["--operator", "S-18"], "executable note: 已: aspect anchor as identity; no completed-time semantics"),
    (["--operator", "A-1"], "executable note: 漸/渐: aspect anchor as identity; no gradual-time semantics"),
    (["--operator", "A-2"], "executable note: 驟/骤: aspect anchor as identity; no sudden-time semantics"),
    (["--operator", "A-3"], "executable note: 忽: aspect anchor as identity; no abrupt-time semantics"),
    (["--operator", "A-7"], "executable note: 屢/屡: aspect anchor as identity; no frequency semantics"),
    (["--operator", "A-8"], "executable note: 愈: adverbial modifier anchor as identity; no degree semantics"),
    (["--operator", "A-9"], "executable note: 益: adverbial modifier anchor as identity; no increment semantics"),
    (["--operator", "A-10"], "executable note: 寖/浸: aspect anchor as identity; no gradual-time semantics"),
    (["--operator", "A-15"], "executable note: 亦: adverbial modifier anchor as identity; no focus/additive semantics"),
    (["--operator", "A-16"], "executable note: 已: aspect anchor as identity; no completed-time semantics"),
    (["--operator", "A-17"], "executable note: 未: aspect anchor as identity; no future/negation semantics"),
    (["--operator", "A-18"], "executable note: 將/将: aspect anchor as identity; no prospective-time semantics"),
    (["--operator", "A-19"], "executable note: 方: aspect anchor as identity; no progressive-time semantics"),
    (["--operator", "A-20"], "executable note: 嘗/尝: aspect anchor as identity; no experiential-time semantics"),
    (["--operator", "Z-18"], "executable note: 散: first Hex projection from a list carrier"),
    (["--operator", "F-1"], "executable note: 往: directional flow as Hex endomap application; no path semantics"),
    (["--operator", "F-2"], "executable note: 來/来: return flow as Hex endomap application; no path semantics"),
    (["--operator", "F-7"], "executable note: 出: outbound flow as Hex endomap application; no boundary topology"),
    (["--operator", "F-8"], "executable note: 入: inbound flow as Hex endomap application; no boundary topology"),
    (["--operator", "P-23"], "executable note: 辯/辨/辩: Bool discrimination as exclusive-or"),
    (["--operator", "S-19"], "executable note: 的: explicit modifier application as Hex endomap application; no modern-grammar semantics"),
    (["--operator", "P-21"], "executable note: 辭/辞: text/proposition anchor as identity; no argument-content semantics"),
    (["--operator", "E-1"], "executable note: 書/书: text-record anchor as identity; no writing semantics"),
    (["--operator", "E-4"], "executable note: 諱/讳: taboo-text anchor as identity; no historiographic omission semantics"),
    (["--operator", "E-5"], "executable note: 譏/讥: critical-text anchor as identity; no critique semantics"),
    (["--operator", "E-6"], "executable note: 與/与: recognition-text anchor as identity; no Spring-Autumn judgment semantics"),
    (["--operator", "E-7"], "executable note: 削: deletion-text anchor as identity; no redaction semantics"),
    (["--operator", "E-8"], "executable note: 筆/笔: inscription-text anchor as identity; no recording semantics"),
    (["--operator", "E-9"], "executable note: 褒/貶: appraisal-text anchor as identity; no praise/blame semantics"),
    (["--operator", "S-13"], "executable note: 者: binder particle anchor as identity; no binding semantics"),
    (["--operator", "S-14"], "executable note: 也: predication/finality particle anchor as identity; no assertion semantics"),
    (["--operator", "S-16"], "executable note: 所: nominalization particle anchor as identity; no nominalization semantics"),
    (["--operator", "H-7"], "executable note: 名: name-assignment anchor as identity; no naming/reference semantics"),
    (["--operator", "P-19"], "executable note: 名: Mohist name-class anchor as identity; no naming/reference semantics"),
    (["--operator", "SUN-12"], "executable note: 分合: parts/whole paired facet carrier via duplicate Hex; no military formation semantics"),
    (["--operator", "ZA-4"], "executable note: 官分: role-partition paired facet carrier via duplicate Hex; no organ/office semantics"),
    (["--operator", "X-5"], "executable note: 分: social role-partition paired facet carrier via duplicate Hex; no hierarchy/conflict semantics"),
    (["--operator", "X-8"], "executable note: 別/别: social distinction paired facet carrier via duplicate Hex; no stratification semantics"),
    (["--operator", "L-6"], "executable note: 二柄: paired-handle carrier via duplicate Hex; no reward/punishment governance semantics"),
    (["--operator", "Y-9"], "executable note: 神: singleton Hex aggregate carrier; no emergence/coherence physiology semantics"),
    (["--operator", "L-14"], "executable note: 制: institutional constructor carrier as singleton Hex list; no legal-control semantics"),
    (["--operator", "Y-2"], "executable note: 五行: five-phase constructor carrier as singleton Hex list; no phase-cycle semantics"),
    (["--operator", "X-6"], "executable note: 礼: ritual constructor carrier as singleton Hex list; no ritual-order semantics"),
    (["--operator", "X-9"], "executable note: 制: social constructor carrier as singleton Hex list; no institutional semantics"),
    (["--operator", "Z-30"], "executable note: 譬/喻: analogy constructor carrier as singleton Hex list; no metaphor semantics"),
    (["--operator", "X-12"], "executable note: 名分: name-role partition paired facet carrier via duplicate Hex; no social-name semantics"),
    (["--operator", "X-3"], "executable note: 化性: nature-transformation anchor as identity; no moral-cultivation semantics"),
    (["--operator", "Z-38"], "executable note: 悟: realization-state anchor as identity; no enlightenment semantics"),
    (["--operator", "SUN-7"], "executable note: 迂: indirect-route anchor as identity; no tactical path semantics"),
    (["--operator", "SUN-8"], "executable note: 直: direct-route anchor as identity; no tactical path semantics"),
    (["--operator", "ZHU-5"], "executable note: 喪/丧: debinding paired facet carrier via duplicate Hex; no Zhuangzi self-loss semantics"),
    (["--operator", "ZA-9"], "executable note: 統/统: integration carrier as singleton Hex list; no unification semantics"),
    (["--operator", "ZA-12"], "executable note: 調/调: harmonization carrier as singleton Hex list; no Huainanzi tuning semantics"),
    (["--operator", "R-1"], "executable note: exact Bool relation/predicate package"),
    (["--operator", "LIJ-9"], "executable note: exact Bool relation/predicate package"),
    (["--operator", "Y-2"], "compound surfaces: 五行"),
    (["--operator", "E-2"], "executable note: structural catalogue normal form"),
    (["--operators", "executable"], "operators executable: 371 shown; 371 registered / 371 executable"),
    (["--operators", "known-not-executable"], "operators known-not-executable: 0 shown; 371 registered / 371 executable"),
    (["--operators", "unsupported"], "operators unsupported: 0 shown; 371 registered / 371 executable"),
    (["--coverage"], "surface readings: 82 surfaces / 193 readings"),
    (["--coverage"], "operators: 371 registered / 371 executable"),
    (["--coverage"], "operator forms: 371 ids with at least one form"),
    (["--help"], "wenyan-surface --json --operators [all|executable|known-not-executable|unsupported]"),
    (["--help"], "317 exact/theorem-backed; 54 structural catalogue normal forms"),
]

JSON_CLI_CASES = [
    (["--json", "--tokens", "推 一"], {"mode": "tokens"}),
    (["--json", "--resolve", "在"], {"mode": "resolve"}),
    (["--json", "--ast", "推 一"], {"mode": "ast"}),
    (["--json", "--typecheck", "同 一 一"], {"mode": "typecheck", "type": "Bool"}),
    (["--json", "--explain", "推 一"], {"mode": "explain"}),
    (["--json", "--operator", "Y-2"], {
        "mode": "operator",
        "operatorCode": "Y-2",
        "support": "executable",
        "executable": True,
    }),
    (["--json", "--operators", "executable"], {
        "mode": "operators",
        "filter": "executable",
        "count": 371,
        "operatorsRegistered": 371,
        "executableOperators": 371,
        "knownNotExecutableOperators": 0,
    }),
    (["--json", "--operators", "known-not-executable"], {
        "mode": "operators",
        "filter": "known-not-executable",
        "count": 0,
        "operatorsRegistered": 371,
        "executableOperators": 371,
        "knownNotExecutableOperators": 0,
    }),
    (["--json", "--operators", "unsupported"], {
        "mode": "operators",
        "filter": "unsupported",
        "count": 0,
        "operatorsRegistered": 371,
        "executableOperators": 371,
        "knownNotExecutableOperators": 0,
    }),
    (["--json", "--coverage"], {
        "mode": "coverage",
        "surfaceCount": 82,
        "readingCount": 193,
        "operatorsRegistered": 371,
        "executableOperators": 371,
        "operatorCellRows": 71232,
        "operatorCellSemanticRows": 71232,
    }),
]

NEGATIVE_CLI_CASES = [
    (["--tokens", "abc"], "lex error"),
    (["--tokens", "推，一"], "lex error at col 1"),
    (["--tokens", "推。一"], "lex error at col 1"),
    (["--resolve", "瓜"], "no known reading"),
    (["--resolve", "或"], "is ambiguous"),
    (["--resolve", "或"], "Why ambiguous"),
    (["--resolve", "或"], "quantifierDomain"),
    (["--resolve", "反"], "expectedOperator"),
    (["--ast", "推 乾 之"], "leftover token"),
    (["--ast", "（推 一"], "unmatched open bracket"),
    (["--ast", "推 一）"], "unmatched close bracket"),
    (["--typecheck", "不 乾"], "type error"),
    (["--explain", "或 真"], "Suggestions:"),
    (["--operator", "NOPE"], "no such catalogue OperatorId"),
    (["--operators", "bad"], "unknown filter"),
]


def run_cli(args: list[str], *, allow_failure: bool = False) -> subprocess.CompletedProcess[str]:
    cmd = [str(BUILT_BIN), *args] if BUILT_BIN.exists() else ["lake", "exe", "wenyan-surface", *args]
    completed = subprocess.run(
        cmd,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=REPO_ROOT,
    )
    if completed.returncode != 0 and not allow_failure:
        raise AssertionError(
            f"lake exe failed for {args!r} with code {completed.returncode}\n"
            f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        )
    return completed


def run_json(program: str, *, allow_failure: bool = False) -> tuple[dict, int]:
    completed = run_cli(["--json", program], allow_failure=allow_failure)
    try:
        return json.loads(completed.stdout), completed.returncode
    except json.JSONDecodeError as exc:
        raise AssertionError(f"invalid JSON for {program!r}: {completed.stdout!r}") from exc


def main() -> int:
    failures: list[str] = []

    for program, expected in CASES:
        actual, returncode = run_json(program)
        if returncode != 0:
            failures.append(f"{program!r}: expected exit 0, got {returncode}")
        if actual != expected:
            failures.append(f"{program!r}: expected {expected!r}, got {actual!r}")

    for program, expected_fields in NEGATIVE_CASES:
        actual, returncode = run_json(program, allow_failure=True)
        if returncode == 0:
            failures.append(f"{program!r}: expected nonzero exit for diagnostic JSON")
        if actual.get("ok") is not False:
            failures.append(f"{program!r}: expected ok=false, got {actual!r}")
            continue
        for key, expected in expected_fields.items():
            if actual.get(key) != expected:
                failures.append(
                    f"{program!r}: expected {key}={expected!r}, got {actual.get(key)!r}"
                )
        if program == "名分 乾":
            candidates = actual.get("candidates")
            if not isinstance(candidates, list) or len(candidates) != 2:
                failures.append(f"{program!r}: expected 2 structured candidates, got {candidates!r}")
            elif {c.get("support") for c in candidates} != {"executable"}:
                failures.append(f"{program!r}: expected executable candidates, got {candidates!r}")
        if program.startswith("或 "):
            suggestions = actual.get("suggestions")
            if not isinstance(suggestions, list) or len(suggestions) != 2:
                failures.append(f"{program!r}: expected 2 ambiguity suggestions, got {suggestions!r}")
            else:
                cue_families = {cue for suggestion in suggestions for cue in suggestion.get("cueFamilies", [])}
                if not {"quantifierDomain", "modalFrame"}.issubset(cue_families):
                    failures.append(f"{program!r}: expected quantifier/modal cue suggestions, got {suggestions!r}")
        if program == "反 乾":
            suggestions = actual.get("suggestions")
            if not isinstance(suggestions, list) or len(suggestions) != 3:
                failures.append(f"{program!r}: expected 3 ambiguity suggestions, got {suggestions!r}")
            else:
                cue_families = {cue for suggestion in suggestions for cue in suggestion.get("cueFamilies", [])}
                if not {"expectedObject", "expectedProp", "expectedOperator"}.issubset(cue_families):
                    failures.append(f"{program!r}: expected object/prop/operator cue suggestions, got {suggestions!r}")

    for args, expected_substring in CLI_CASES:
        actual = run_cli(args).stdout
        if expected_substring not in actual:
            failures.append(
                f"{args!r}: expected stdout to contain {expected_substring!r}, got {actual!r}"
            )

    for args, expected_substring in NEGATIVE_CLI_CASES:
        completed = run_cli(args, allow_failure=True)
        if completed.returncode == 0:
            failures.append(f"{args!r}: expected nonzero exit")
        if expected_substring not in completed.stdout:
            failures.append(
                f"{args!r}: expected stdout to contain {expected_substring!r}, got {completed.stdout!r}"
            )

    for args, expected_fields in JSON_CLI_CASES:
        completed = run_cli(args)
        try:
            actual = json.loads(completed.stdout)
        except json.JSONDecodeError as exc:
            failures.append(f"{args!r}: invalid JSON {completed.stdout!r}: {exc}")
            continue
        if actual.get("ok") is not True:
            failures.append(f"{args!r}: expected ok=true, got {actual!r}")
            continue
        for key, expected in expected_fields.items():
            if actual.get(key) != expected:
                failures.append(
                    f"{args!r}: expected {key}={expected!r}, got {actual.get(key)!r}"
                )
        if args[:2] == ["--json", "--tokens"]:
            tokens = actual.get("tokens")
            if not isinstance(tokens, list) or [t.get("surface") for t in tokens] != ["推", "一"]:
                failures.append(f"{args!r}: unexpected token JSON {tokens!r}")
        if args[:2] == ["--json", "--resolve"]:
            tokens = actual.get("tokens")
            atom = tokens[0].get("atom") if isinstance(tokens, list) and tokens else None
            reading = atom.get("reading") if isinstance(atom, dict) else None
            if not isinstance(reading, dict) or reading.get("operatorCode") != "R-1":
                failures.append(f"{args!r}: unexpected resolve JSON {tokens!r}")
        if args[:2] == ["--json", "--explain"]:
            for key in ["tokens", "resolve", "ast", "typecheck", "run"]:
                if not isinstance(actual.get(key), dict):
                    failures.append(f"{args!r}: expected nested object for {key}, got {actual.get(key)!r}")
        if args[:2] == ["--json", "--operators"]:
            operators = actual.get("operators")
            if not isinstance(operators, list) or len(operators) != expected_fields["count"]:
                failures.append(f"{args!r}: unexpected operator list length {operators!r}")
            elif args[2] == "executable" and {op.get("support") for op in operators} != {"executable"}:
                failures.append(f"{args!r}: expected executable operator list, got {operators!r}")
            elif (
                args[2] in {"known-not-executable", "unsupported"}
                and operators
                and {op.get("support") for op in operators} != {"known-not-executable"}
            ):
                failures.append(f"{args!r}: expected unsupported operator list, got {operators!r}")

    bad_filter_completed = run_cli(["--json", "--operators", "bad"], allow_failure=True)
    bad_filter = json.loads(bad_filter_completed.stdout)
    if bad_filter_completed.returncode == 0:
        failures.append("bad operator filter: expected nonzero exit")
    if bad_filter.get("ok") is not False or bad_filter.get("code") != "unknown_operator_filter":
        failures.append(f"bad operator filter: unexpected JSON {bad_filter!r}")

    bad_explain_completed = run_cli(["--json", "--explain", "瓜"], allow_failure=True)
    bad_explain = json.loads(bad_explain_completed.stdout)
    if bad_explain_completed.returncode == 0:
        failures.append("bad explain JSON: expected nonzero exit")
    if bad_explain.get("ok") is not False or not isinstance(bad_explain.get("resolve"), dict):
        failures.append(f"bad explain JSON: unexpected JSON {bad_explain!r}")
    elif bad_explain["resolve"].get("code") != "no_reading":
        failures.append(f"bad explain JSON: expected resolve no_reading, got {bad_explain!r}")

    ambiguous_explain_completed = run_cli(["--json", "--explain", "或 真"], allow_failure=True)
    ambiguous_explain = json.loads(ambiguous_explain_completed.stdout)
    if ambiguous_explain_completed.returncode == 0:
        failures.append("ambiguous explain JSON: expected nonzero exit")
    resolve = ambiguous_explain.get("resolve")
    suggestions = resolve.get("suggestions") if isinstance(resolve, dict) else None
    if not isinstance(suggestions, list) or not any(
        "modalFrame" in suggestion.get("cueFamilies", []) for suggestion in suggestions
    ):
        failures.append(f"ambiguous explain JSON: expected cue suggestions, got {ambiguous_explain!r}")

    empty_stdin = run_cli([], allow_failure=True)
    if empty_stdin.returncode == 0 or "Usage:" not in empty_stdin.stdout:
        failures.append(f"empty stdin: expected usage with nonzero exit, got {empty_stdin!r}")

    if failures:
        print("wenyan-surface CLI smoke failures:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1

    total = (
        len(CASES)
        + len(NEGATIVE_CASES)
        + len(CLI_CASES)
        + len(NEGATIVE_CLI_CASES)
        + len(JSON_CLI_CASES)
        + 4
    )
    print(f"wenyan-surface CLI smoke passed ({total} cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
