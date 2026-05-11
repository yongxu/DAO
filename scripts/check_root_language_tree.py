#!/usr/bin/env python3
"""Consistency checks for the R0-R8 root language tree review package."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys


REPO_ROOT = Path(__file__).resolve().parents[1]
TREE_DIR = REPO_ROOT / "docs-next" / "10_formal_形式" / "root-language-tree"
LAYER_DIR = TREE_DIR / "layers"
R8_SLICE_DIR = TREE_DIR / "r8-64"

EXPECTED_LAYER_COUNTS = {n: 2 ** (n + 1) for n in range(9)}
R8_SLICE_SUFFIXES = {
    "dao": "oo",
    "ji": "xo",
    "wei": "ox",
    "jin": "xx",
}
OX_RE = re.compile(r"^[ox]+$")


@dataclass(frozen=True)
class RootRow:
    path: Path
    line: int
    id: str
    ox: str
    role: str
    wen: str
    zh: str
    english: str
    formal: str
    scheme: str
    reason: str


@dataclass(frozen=True)
class R8SliceRow:
    path: Path
    line: int
    number: int
    hex_ox6: str
    cell_ox8: str
    cell_wen: str
    cell_zh: str
    operator_wen: str
    operator_zh: str
    english: str
    formal: str
    reason: str


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def parse_markdown_table(path: Path, expected_columns: int) -> tuple[list[tuple[int, list[str]]], list[str]]:
    errors: list[str] = []
    rows: list[tuple[int, list[str]]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        text = line.strip()
        if not (text.startswith("|") and text.endswith("|")):
            continue
        columns = [column.strip() for column in text.strip("|").split("|")]
        first = columns[0] if columns else ""
        if first == "" or first == "id" or first == "#" or set(first) <= {"-", ":"}:
            continue
        if len(columns) != expected_columns:
            errors.append(
                f"{rel(path)}:{line_number}: expected {expected_columns} columns, found {len(columns)}"
            )
            continue
        rows.append((line_number, columns))
    return rows, errors


def read_root_rows(path: Path) -> tuple[list[RootRow], list[str]]:
    table_rows, errors = parse_markdown_table(path, 9)
    rows: list[RootRow] = []
    for line_number, columns in table_rows:
        row_id = columns[0]
        if not (row_id == "ROOT-undivided" or row_id.startswith("R")):
            continue
        rows.append(RootRow(path, line_number, *columns))
    return rows, errors


def read_r8_slice_rows(path: Path) -> tuple[list[R8SliceRow], list[str]]:
    table_rows, errors = parse_markdown_table(path, 10)
    rows: list[R8SliceRow] = []
    for line_number, columns in table_rows:
        if not columns[0].isdigit():
            continue
        rows.append(R8SliceRow(path, line_number, int(columns[0]), *columns[1:]))
    return rows, errors


def check_unique(label: str, values: list[str | int], errors: list[str]) -> None:
    seen: set[str | int] = set()
    duplicates: set[str | int] = set()
    for value in values:
        if value in seen:
            duplicates.add(value)
        seen.add(value)
    if duplicates:
        sample = ", ".join(str(value) for value in sorted(duplicates, key=str)[:8])
        errors.append(f"{label}: duplicate values: {sample}")


def check_root_row_shape(row: RootRow, layer: int, errors: list[str]) -> None:
    if row.role not in {"cell", "operator"}:
        errors.append(f"{rel(row.path)}:{row.line}: role must be cell/operator, found {row.role!r}")
    if layer == 0:
        if row.ox != "ε":
            errors.append(f"{rel(row.path)}:{row.line}: R0 ox must be ε, found {row.ox!r}")
    elif len(row.ox) != layer or OX_RE.fullmatch(row.ox) is None:
        errors.append(f"{rel(row.path)}:{row.line}: R{layer} ox must be {layer} o/x bits, found {row.ox!r}")

    expected_id = f"R{layer}-{row.ox}-{row.role}"
    if row.id != expected_id:
        errors.append(f"{rel(row.path)}:{row.line}: expected id {expected_id!r}, found {row.id!r}")


def check_layers(errors: list[str]) -> list[RootRow]:
    layer_rows: list[RootRow] = []
    for layer, expected_count in EXPECTED_LAYER_COUNTS.items():
        path = LAYER_DIR / f"R{layer}.md"
        rows, parse_errors = read_root_rows(path)
        errors.extend(parse_errors)
        if len(rows) != expected_count:
            errors.append(f"{rel(path)}: expected {expected_count} root interface rows, found {len(rows)}")

        check_unique(f"{rel(path)} id", [row.id for row in rows], errors)
        for row in rows:
            check_root_row_shape(row, layer, errors)

        by_ox: dict[str, set[str]] = {}
        for row in rows:
            by_ox.setdefault(row.ox, set()).add(row.role)
        expected_ox_count = 2**layer
        if len(by_ox) != expected_ox_count:
            errors.append(f"{rel(path)}: expected {expected_ox_count} distinct ox values, found {len(by_ox)}")
        missing_roles = [ox for ox, roles in by_ox.items() if roles != {"cell", "operator"}]
        if missing_roles:
            sample = ", ".join(sorted(missing_roles)[:8])
            errors.append(f"{rel(path)}: ox values without both cell/operator rows: {sample}")

        layer_rows.extend(rows)
    return layer_rows


def check_all_1023(expected_layer_rows: list[RootRow], errors: list[str]) -> None:
    path = TREE_DIR / "all-1023.md"
    rows, parse_errors = read_root_rows(path)
    errors.extend(parse_errors)

    if len(rows) != 1023:
        errors.append(f"{rel(path)}: expected 1023 review rows, found {len(rows)}")
    check_unique(f"{rel(path)} id", [row.id for row in rows], errors)

    if rows:
        root = rows[0]
        if (root.id, root.ox, root.role, root.wen) != ("ROOT-undivided", "ε", "undivided", "道"):
            errors.append(
                f"{rel(path)}:{root.line}: first row must be ROOT-undivided / ε / undivided / 道"
            )

    compact_all = [(row.id, row.ox, row.role, row.wen, row.zh, row.english, row.formal, row.scheme, row.reason) for row in rows[1:]]
    compact_layers = [
        (row.id, row.ox, row.role, row.wen, row.zh, row.english, row.formal, row.scheme, row.reason)
        for row in expected_layer_rows
    ]
    if compact_all != compact_layers:
        for index, (all_row, layer_row) in enumerate(zip(compact_all, compact_layers), start=1):
            if all_row != layer_row:
                errors.append(
                    f"{rel(path)}: row {index + 1} after ROOT does not match layer concatenation "
                    f"(all id {all_row[0]!r}, layer id {layer_row[0]!r})"
                )
                break
        else:
            errors.append(f"{rel(path)}: rows after ROOT do not match R0-R8 layer concatenation")


def check_r8_slices(r8_rows: list[RootRow], errors: list[str]) -> None:
    r8_by_ox_role = {(row.ox, row.role): row for row in r8_rows}
    r8_cell_ox = {row.ox for row in r8_rows if row.role == "cell"}
    combined_slice_ox: set[str] = set()

    for slice_name, suffix in R8_SLICE_SUFFIXES.items():
        path = R8_SLICE_DIR / f"{slice_name}.md"
        rows, parse_errors = read_r8_slice_rows(path)
        errors.extend(parse_errors)

        if len(rows) != 64:
            errors.append(f"{rel(path)}: expected 64 rows, found {len(rows)}")
        numbers = [row.number for row in rows]
        check_unique(f"{rel(path)} #", numbers, errors)
        if set(numbers) != set(range(1, 65)):
            errors.append(f"{rel(path)}: # column must contain the King Wen numbers 1..64 exactly once")

        check_unique(f"{rel(path)} hex ox6", [row.hex_ox6 for row in rows], errors)
        check_unique(f"{rel(path)} cell ox8", [row.cell_ox8 for row in rows], errors)

        for row in rows:
            if len(row.hex_ox6) != 6 or OX_RE.fullmatch(row.hex_ox6) is None:
                errors.append(f"{rel(row.path)}:{row.line}: hex ox6 must be six o/x bits, found {row.hex_ox6!r}")
            expected_ox8 = row.hex_ox6 + suffix
            if row.cell_ox8 != expected_ox8:
                errors.append(
                    f"{rel(row.path)}:{row.line}: expected cell ox8 {expected_ox8!r}, found {row.cell_ox8!r}"
                )

            cell = r8_by_ox_role.get((row.cell_ox8, "cell"))
            operator = r8_by_ox_role.get((row.cell_ox8, "operator"))
            if cell is None or operator is None:
                errors.append(f"{rel(row.path)}:{row.line}: cell ox8 {row.cell_ox8!r} is missing in R8 layer rows")
                continue

            copied_fields = [
                ("cell 文言候选", row.cell_wen, cell.wen),
                ("cell 中文候选", row.cell_zh, cell.zh),
                ("operator 文言候选", row.operator_wen, operator.wen),
                ("operator 中文候选", row.operator_zh, operator.zh),
                ("English", row.english, cell.english),
            ]
            for label, found, expected in copied_fields:
                if found != expected:
                    errors.append(
                        f"{rel(row.path)}:{row.line}: {label} differs from R8.md for {row.cell_ox8}: "
                        f"found {found!r}, expected {expected!r}"
                    )

            expected_formal = f'`cell OX["{row.cell_ox8}"]; op(s) = OX["{row.cell_ox8}"] xor s`'
            if row.formal != expected_formal:
                errors.append(f"{rel(row.path)}:{row.line}: formal field does not match canonical R8 slice form")

        combined_slice_ox.update(row.cell_ox8 for row in rows)

    if combined_slice_ox != r8_cell_ox:
        missing = sorted(r8_cell_ox - combined_slice_ox)[:8]
        extra = sorted(combined_slice_ox - r8_cell_ox)[:8]
        if missing:
            errors.append(f"r8-64 slices: missing R8 cell ox values: {', '.join(missing)}")
        if extra:
            errors.append(f"r8-64 slices: extra ox values not present in R8 layer: {', '.join(extra)}")


def main() -> int:
    errors: list[str] = []
    layer_rows = check_layers(errors)
    check_all_1023(layer_rows, errors)
    r8_rows = [row for row in layer_rows if row.id.startswith("R8-")]
    check_r8_slices(r8_rows, errors)

    if errors:
        print("root language tree check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("ok: root language tree review package verified (1023 entries; R8 4x64 slices)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
