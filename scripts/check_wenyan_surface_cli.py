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
    ("五行 乾", {"ok": True, "kind": "catalogue", "operatorCode": "Y-2", "operatorTitle": "五行 (木火土金水)", "signatureKind": "CONS", "arity": 1}),
    ("鼎", {"ok": True, "kind": "hex", "idx": 17}),
    ("大壯", {"ok": True, "kind": "hex", "idx": 48}),
]

NEGATIVE_CASES = [
    ("瓜", {"phase": "resolve", "code": "no_reading", "surface": "瓜", "startCol": 0, "endCol": 1}),
    ("推 乾 之", {"phase": "parse", "code": "leftover_tokens", "surface": "之", "startCol": 4, "endCol": 5, "leftoverCount": 1}),
    ("名分 乾", {"phase": "resolve", "code": "ambiguous_reading", "surface": "名分", "startCol": 0, "endCol": 2, "candidateCount": 2}),
    ("鼎 乾", {"phase": "unsupported", "code": "unpromoted_hexagram_gap", "surface": "鼎", "startCol": 0, "endCol": 1}),
    ("丽", {"phase": "unsupported", "code": "unpromoted_hexagram_gap", "surface": "丽", "startCol": 0, "endCol": 1}),
    ("大", {"phase": "unsupported", "code": "unpromoted_hexagram_gap", "surface": "大", "startCol": 0, "endCol": 1}),
    ("乾 之 坤", {"phase": "type", "code": "type_mismatch", "expectedType": "function", "actualType": "Hex"}),
    ("不 乾", {"phase": "type", "code": "type_mismatch", "expectedType": "Bool", "actualType": "Hex"}),
    ("或 者 甲 同 甲 一", {"phase": "resolve", "code": "ambiguous_reading", "surface": "或", "startCol": 0, "endCol": 1, "candidateCount": 2}),
    ("故 假 假", {"phase": "resolve", "code": "ambiguous_reading", "surface": "故", "startCol": 0, "endCol": 1, "candidateCount": 3}),
    ("反 乾", {"phase": "resolve", "code": "ambiguous_reading", "surface": "反", "startCol": 0, "endCol": 1, "candidateCount": 3}),
    ("而 不 不 真", {"phase": "type", "code": "type_mismatch", "expectedType": "(Hex -> Hex)", "actualType": "(Bool -> Bool)", "surface": "不", "startCol": 2, "endCol": 3}),
    ("在 乾", {"phase": "denote", "code": "denote_failed", "expectedType": "Hex", "actualType": "(Hex -> Bool)"}),
    ("（推 一", {"phase": "parse", "code": "unmatched_open_bracket", "surface": "（", "startCol": 0, "endCol": 1}),
    ("推 一）", {"phase": "parse", "code": "unmatched_close_bracket", "surface": "）", "startCol": 3, "endCol": 4}),
]

CLI_CASES = [
    (["--tokens", "推 一"], "0:推/w1\n2:一/w1"),
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
    (["--typecheck", "（推）"], "type (Hex -> Hex)"),
    (["--typecheck", "（同 乾）"], "type (Hex -> Bool)"),
    (["--operator", "T-10"], "executable: yes"),
    (["--operator", "T-1"], "executable note: 化: Hex y2 transform"),
    (["--operator", "Q-8"], "executable note: 唯: finite unique-existence"),
    (["--operator", "D-10"], "executable note: 過半/大半: finite majority"),
    (["--operator", "F-3"], "executable note: 進/进: forward Hex motion"),
    (["--operator", "K-6"], "executable note: 使: causative Hex endomap application"),
    (["--operator", "M-3"], "executable note: 當/当: guarded modal condition"),
    (["--operator", "M-5"], "executable note: 可: finite possibility"),
    (["--operator", "S-4"], "executable note: 若: truth-core conditional marker"),
    (["--operator", "D-2"], "executable note: 再: repeat a Hex endomap once"),
    (["--operator", "Z-10"], "executable note: 藏: concealment transition"),
    (["--operator", "R-1"], "executable note: exact Bool relation/predicate package"),
    (["--operator", "LIJ-9"], "executable note: exact Bool relation/predicate package"),
    (["--operator", "Y-2"], "compound surfaces: 五行"),
    (["--operator", "Y-2"], "executable note: structural catalogue normal form"),
    (["--operators", "executable"], "operators executable: 371 shown; 371 registered / 371 executable"),
    (["--operators", "known-not-executable"], "operators known-not-executable: 0 shown; 371 registered / 371 executable"),
    (["--operators", "unsupported"], "operators unsupported: 0 shown; 371 registered / 371 executable"),
    (["--coverage"], "surface readings: 82 surfaces / 193 readings"),
    (["--coverage"], "operators: 371 registered / 371 executable"),
    (["--coverage"], "operator forms: 371 ids with at least one form"),
    (["--help"], "wenyan-surface --json --operators [all|executable|known-not-executable|unsupported]"),
    (["--help"], "0 symbolic catalogue-shape"),
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
    (["--resolve", "瓜"], "no known reading"),
    (["--resolve", "或"], "is ambiguous"),
    (["--resolve", "或"], "Why ambiguous"),
    (["--resolve", "或"], "quantifierDomain"),
    (["--resolve", "反"], "expectedOperator"),
    (["--ast", "推 乾 之"], "leftover token"),
    (["--ast", "（推 一"], "unmatched open bracket"),
    (["--ast", "推 一）"], "unmatched close bracket"),
    (["--typecheck", "不 乾"], "type error"),
    (["--explain", "或 者 甲 同 甲 一"], "Suggestions:"),
    (["--explain", "反 乾"], "expectedObject"),
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

    ambiguous_explain_completed = run_cli(["--json", "--explain", "或 者 甲 同 甲 一"], allow_failure=True)
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
