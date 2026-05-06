#!/usr/bin/env python3
"""Generate a plain-text single-root tree.

Output shape:

一元
  -> 面
    -> 单字
      -> 复合概念
        -> 判准 / 模型 / 定理 / 案例

The tree is generated from the Lean roster and monad-root mapping so it stays
aligned with the formal registry.
"""
from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ROSTER = ROOT / "formal/SSBX/Roster.lean"
MONAD = ROOT / "formal/SSBX/Foundation/Core/MonadRoot.lean"
MONISM = ROOT / "formal/SSBX/Foundation/Core/Monism.lean"
CLAIMS = ROOT / "formal/SSBX/Truth/ClaimLedger.lean"
BASIC = ROOT / "formal/SSBX/Truth/Basic.lean"
OUT = ROOT / "formal/SSBX/diagrams/MonadTree.txt"


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


def extract_def_block(text: str, def_name: str, next_marker: str = "\ndef ") -> str:
    start = text.split(f"def {def_name}", 1)[1]
    if next_marker in start:
        return start.split(next_marker, 1)[0]
    return start


def parse_atom_faces(monad: str) -> dict[str, list[str]]:
    primary_block = extract_def_block(monad, "atomPrimaryFace")
    extras_block = extract_def_block(monad, "atomExtraFaces")
    out: dict[str, list[str]] = {}
    for atom, face in re.findall(r"\| \.«([^»]+)» => \.«([^»]+)»", primary_block):
        out.setdefault(atom, []).append(face)
    for atom, rhs in re.findall(r"\| \.«([^»]+)» => \[(.*?)\]", extras_block):
        faces = re.findall(r"\.«([^»]+)»", rhs)
        out.setdefault(atom, [])
        for face in faces:
            if face not in out[atom]:
                out[atom].append(face)
    return out


def parse_roster_roots(roster: str) -> dict[str, list[str]]:
    block = roster.split("def rootsOfGenerated", 1)[1].split("def depsOfGenerated", 1)[0]
    return {
        name: re.findall(r"A \.«([^»]+)»", rhs)
        for name, rhs in re.findall(r"\| \.«([^»]+)» => \[(.*?)\]", block)
    }


def parse_atom_function(monad: str, def_name: str) -> dict[str, list[str]]:
    block = extract_def_block(monad, def_name)
    out: dict[str, list[str]] = {}
    for raw_name, rhs in re.findall(r"\| \.([^=]+?) => \[(.*?)\]", block):
        name = raw_name.strip()
        quoted = re.fullmatch(r"«([^»]+)»", name)
        name = quoted.group(1) if quoted else name
        out[name] = re.findall(r"\.«([^»]+)»", rhs)
    return out


def parse_single_atom_function(monad: str, def_name: str) -> dict[str, str]:
    block = extract_def_block(monad, def_name)
    return {
        name: atom
        for name, atom in re.findall(r"\| \.([A-Za-z0-9_]+) => \.«([^»]+)»", block)
    }


def parse_claim_labels(text: str) -> dict[str, str]:
    return {
        claim: label
        for claim, label in re.findall(r"\| \.([A-Za-z0-9_]+) => \{[^\n]*label := \"([^\"]+)\"", text)
    }


def parse_claim_formals(monad: str) -> dict[str, tuple[str, str]]:
    block = extract_def_block(monad, "claimPrimaryFormal")
    out: dict[str, tuple[str, str]] = {}
    pattern = re.compile(r"\| \.([A-Za-z0-9_]+) => \.(generated|primitive|recursive|pending) \.([^\n]+)")
    kind_map = {"generated": "复合概念", "primitive": "模型接口", "recursive": "判准", "pending": "待校接口"}
    for claim, kind, raw in pattern.findall(block):
        raw = raw.strip()
        quoted = re.fullmatch(r"«([^»]+)»", raw)
        name = quoted.group(1) if quoted else raw
        out[claim] = (kind_map[kind], name)
    return out


def add_unique(mapping: dict[str, list[str]], key: str, value: str) -> None:
    if value not in mapping[key]:
        mapping[key].append(value)


def main() -> None:
    roster = read(ROSTER)
    monad = read(MONAD)
    monism = read(MONISM)
    claims_text = read(CLAIMS)

    faces = extract_inductive_names(monad, "Face")
    atoms = extract_inductive_names(roster, "AtomName")
    generated = extract_inductive_names(roster, "GenName")
    primitives = extract_inductive_names(roster, "PrimName")
    recursive = extract_inductive_names(roster, "RecName")
    pending = extract_inductive_names(roster, "PendingName")
    construction = extract_inductive_names(monism, "ConstructionId")
    claims = extract_inductive_names(read(BASIC), "ClaimId")

    atom_faces = parse_atom_faces(monad)
    gen_roots = parse_roster_roots(roster)
    primitive_atoms = parse_atom_function(monad, "primitiveAtoms")
    recursive_atoms = parse_atom_function(monad, "recursiveAtoms")
    pending_atoms = parse_atom_function(monad, "pendingAtoms")
    construction_atoms = parse_single_atom_function(monad, "constructionPrimaryAtom")
    claim_labels = parse_claim_labels(claims_text)
    claim_formals = parse_claim_formals(monad)

    atom_generated: dict[str, list[str]] = defaultdict(list)
    atom_bottom: dict[str, list[str]] = defaultdict(list)
    concept_bottom: dict[str, list[str]] = defaultdict(list)

    for name in generated:
        for atom in gen_roots.get(name, []):
            add_unique(atom_generated, atom, name)

    for name in primitives:
        for atom in primitive_atoms.get(name, []):
            add_unique(atom_bottom, atom, f"模型接口: {name}")

    for name in recursive:
        for atom in recursive_atoms.get(name, []):
            add_unique(atom_bottom, atom, f"判准: {name}")

    for name in pending:
        for atom in pending_atoms.get(name, []):
            add_unique(atom_bottom, atom, f"待校接口: {name}")

    for name in construction:
        atom = construction_atoms[name]
        add_unique(atom_bottom, atom, f"模型/构造: {name}")

    for claim in claims:
        kind, formal = claim_formals[claim]
        label = claim_labels.get(claim, claim)
        item = f"定理/claim: {label} ({claim})"
        if kind == "复合概念":
            add_unique(concept_bottom, formal, item)
        else:
            # Non-generated claims are anchored under the first atom of their formal interface.
            atom_sources: list[str] = []
            if kind == "模型接口":
                atom_sources = primitive_atoms.get(formal, [])
            elif kind == "判准":
                atom_sources = recursive_atoms.get(formal, [])
            elif kind == "待校接口":
                atom_sources = pending_atoms.get(formal, [])
            for atom in atom_sources[:1]:
                add_unique(atom_bottom, atom, item)

    atoms_by_face: dict[str, list[str]] = defaultdict(list)
    for atom in atoms:
        for face in atom_faces.get(atom, []):
            add_unique(atoms_by_face, face, atom)

    lines: list[str] = [
        "一元生成全树 / Monad Full Text Tree",
        "",
        "方向约定: 一元 -> 面 -> 单字 -> 复合概念 -> 判准 / 模型 / 定理 / 案例",
        "",
        "完整性口径:",
        f"- 面: {len(faces)}",
        f"- 单字: {len(atoms)}",
        f"- 复合概念: {len(generated)}",
        f"- 模型接口: {len(primitives)}",
        f"- 判准/递归项: {len(recursive)}",
        f"- 待校接口: {len(pending)}",
        f"- 模型/构造阶段: {len(construction)}",
        f"- 定理/claim: {len(claims)}",
        "",
        "一元",
    ]

    for face in faces:
        lines.append(f"  -> {face}")
        for atom in sorted(atoms_by_face.get(face, [])):
            lines.append(f"    -> {atom}")
            concepts = sorted(atom_generated.get(atom, []))
            bottom = sorted(atom_bottom.get(atom, []))
            if concepts:
                for concept in concepts:
                    lines.append(f"      -> {concept}")
                    for item in sorted(concept_bottom.get(concept, [])):
                        lines.append(f"        -> {item}")
            if bottom:
                lines.append("      -> 判准 / 模型 / 定理 / 案例")
                for item in bottom:
                    lines.append(f"        -> {item}")

    OUT.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
