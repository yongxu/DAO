#!/usr/bin/env python3
"""Generate the single-root SSBX Monad DAG from Lean source.

This graph is intentionally different from ConceptDAG:
- ConceptDAG is a registry/dependency graph and can have many lexical roots.
- MonadDAG is the proof-shape graph:
  一元 -> 面 -> 核心单字 -> 单字 -> 正式项 -> claim.
"""
from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ROSTER = ROOT / "formal/SSBX/Roster.lean"
MONAD = ROOT / "formal/SSBX/Foundation/MonadRoot.lean"
MONISM = ROOT / "formal/SSBX/Foundation/Monism.lean"
CLAIMS = ROOT / "formal/SSBX/Truth/ClaimLedger.lean"
OUT_DIR = ROOT / "formal/SSBX"

CLASS_DEF = [
    "  classDef root fill:#111827,stroke:#111827,color:#ffffff;",
    "  classDef face fill:#fef9c3,stroke:#ca8a04,color:#713f12;",
    "  classDef core fill:#fef3c7,stroke:#d97706,color:#78350f;",
    "  classDef atom fill:#f8fafc,stroke:#64748b,color:#0f172a;",
    "  classDef generated fill:#ecfeff,stroke:#0891b2,color:#164e63;",
    "  classDef primitive fill:#f0fdf4,stroke:#16a34a,color:#14532d;",
    "  classDef recursive fill:#fff7ed,stroke:#ea580c,color:#7c2d12;",
    "  classDef pending fill:#fef2f2,stroke:#dc2626,color:#7f1d1d;",
    "  classDef construction fill:#eef2ff,stroke:#4f46e5,color:#312e81;",
    "  classDef claim fill:#f5f3ff,stroke:#7c3aed,color:#3b0764;",
]

KIND_LABEL = {
    "root": "唯一根",
    "face": "面",
    "core": "核心单字",
    "atom": "单字",
    "G": "生成项",
    "P": "原始算子",
    "R": "递归项",
    "U": "待校项",
    "C": "构造阶段",
    "claim": "claim",
}

CLASS_NAME = {
    "root": "root",
    "face": "face",
    "core": "core",
    "atom": "atom",
    "G": "generated",
    "P": "primitive",
    "R": "recursive",
    "U": "pending",
    "C": "construction",
    "claim": "claim",
}

@dataclass(frozen=True, order=True)
class Node:
    kind: str
    name: str

@dataclass(frozen=True)
class Edge:
    source: Node
    target: Node
    label: str


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
        faces = re.findall(r"\. «([^»]+)»", rhs)
        if not faces:
            faces = re.findall(r"\.«([^»]+)»", rhs)
        out.setdefault(atom, [])
        for face in faces:
            if face not in out[atom]:
                out[atom].append(face)
    return out


def parse_core_glyphs(monad: str) -> dict[str, str]:
    block = monad.split("def glyph : CoreAtom -> AtomName", 1)[1].split("end CoreAtom", 1)[0]
    return {
        core: glyph
        for core, glyph in re.findall(r"\| \.«([^»]+)» => \.«([^»]+)»", block)
    }


def parse_atom_cores(monad: str) -> dict[str, str]:
    block = monad.split("def atomCore : AtomName -> CoreAtom", 1)[1].split("def CoreDerives", 1)[0]
    return {
        atom: core
        for atom, core in re.findall(r"\| \.«([^»]+)» => \.«([^»]+)»", block)
    }


def parse_roster_roots(roster: str) -> dict[str, list[str]]:
    block = roster.split("def rootsOfGenerated", 1)[1].split("def depsOfGenerated", 1)[0]
    out: dict[str, list[str]] = {}
    for name, rhs in re.findall(r"\| \.«([^»]+)» => \[(.*?)\]", block):
        out[name] = re.findall(r"A \.«([^»]+)»", rhs)
    return out


def parse_atom_function(monad: str, def_name: str) -> dict[str, list[str]]:
    block = extract_def_block(monad, def_name)
    out: dict[str, list[str]] = {}
    for raw_name, rhs in re.findall(r"\| \.([^=]+?) => \[(.*?)\]", block):
        name = raw_name.strip()
        quoted = re.fullmatch(r"«([^»]+)»", name)
        name = quoted.group(1) if quoted else name
        out[name] = re.findall(r"\. «([^»]+)»", rhs)
        if not out[name]:
            out[name] = re.findall(r"\.«([^»]+)»", rhs)
    return out


def parse_single_atom_function(monad: str, def_name: str) -> dict[str, str]:
    block = extract_def_block(monad, def_name)
    return {
        name: atom
        for name, atom in re.findall(r"\| \.([A-Za-z0-9_]+) => \.«([^»]+)»", block)
    }


def parse_claim_labels(text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for claim, label in re.findall(r"\| \.([A-Za-z0-9_]+) => \{[^\n]*label := \"([^\"]+)\"", text):
        out[claim] = label
    return out


def parse_claim_formals(monad: str) -> dict[str, Node]:
    block = extract_def_block(monad, "claimPrimaryFormal")
    out: dict[str, Node] = {}
    pattern = re.compile(r"\| \.([A-Za-z0-9_]+) => \.(generated|primitive|recursive|pending) \.([^\n]+)")
    kind_map = {"generated": "G", "primitive": "P", "recursive": "R", "pending": "U"}
    for claim, kind, raw in pattern.findall(block):
        raw = raw.strip()
        quoted = re.fullmatch(r"«([^»]+)»", raw)
        name = quoted.group(1) if quoted else raw
        out[claim] = Node(kind_map[kind], name)
    return out


def node_label(node: Node, claim_labels: dict[str, str]) -> str:
    if node.kind == "root":
        return "一元｜唯一根"
    if node.kind == "claim":
        label = claim_labels.get(node.name, node.name)
        return f"{label}｜claim"
    return f"{node.name}｜{KIND_LABEL[node.kind]}"


def node_order(node: Node) -> tuple[int, str]:
    order = {"root": 0, "face": 1, "core": 2, "atom": 3, "G": 4, "P": 5, "R": 6, "U": 7, "C": 8, "claim": 9}
    return (order.get(node.kind, 99), node.name)


def node_id_map(nodes: list[Node]) -> dict[Node, str]:
    return {node: f"n{i}" for i, node in enumerate(sorted(nodes, key=node_order))}


def mermaid_node(node: Node, ids: dict[Node, str], claim_labels: dict[str, str]) -> str:
    return f"  {ids[node]}[\"{node_label(node, claim_labels)}\"]:::{CLASS_NAME[node.kind]}"


def mermaid_edge(edge: Edge, ids: dict[Node, str]) -> str:
    return f"  {ids[edge.source]} -->|{edge.label}| {ids[edge.target]}"


def unique_sources(nodes: list[Node], edges: list[Edge]) -> list[Node]:
    indeg = {n: 0 for n in nodes}
    for e in edges:
        indeg[e.target] += 1
        indeg.setdefault(e.source, 0)
    return sorted([n for n, d in indeg.items() if d == 0], key=node_order)


def acyclic(nodes: list[Node], edges: list[Edge]) -> bool:
    adj: dict[Node, list[Node]] = defaultdict(list)
    indeg = {n: 0 for n in nodes}
    for e in edges:
        adj[e.source].append(e.target)
        indeg[e.target] += 1
    q = deque([n for n, d in indeg.items() if d == 0])
    seen = 0
    while q:
        n = q.popleft()
        seen += 1
        for m in adj[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                q.append(m)
    return seen == len(nodes)


def main() -> None:
    roster = read(ROSTER)
    monad = read(MONAD)
    monism = read(MONISM)
    claims_text = read(CLAIMS)

    atoms = extract_inductive_names(roster, "AtomName")
    core_atoms = extract_inductive_names(monad, "CoreAtom")
    generated = extract_inductive_names(roster, "GenName")
    primitives = extract_inductive_names(roster, "PrimName")
    recursive = extract_inductive_names(roster, "RecName")
    pending = extract_inductive_names(roster, "PendingName")
    construction = extract_inductive_names(monism, "ConstructionId")
    claims = extract_inductive_names(read(ROOT / "formal/SSBX/Truth/Basic.lean"), "ClaimId")
    faces = extract_inductive_names(monad, "Face")

    atom_faces = parse_atom_faces(monad)
    core_glyphs = parse_core_glyphs(monad)
    atom_cores = parse_atom_cores(monad)
    gen_roots = parse_roster_roots(roster)
    primitive_atoms = parse_atom_function(monad, "primitiveAtoms")
    recursive_atoms = parse_atom_function(monad, "recursiveAtoms")
    pending_atoms = parse_atom_function(monad, "pendingAtoms")
    construction_atoms = parse_single_atom_function(monad, "constructionPrimaryAtom")
    claim_labels = parse_claim_labels(claims_text)
    claim_formals = parse_claim_formals(monad)

    formal_atoms: dict[Node, list[str]] = {}
    for name, atoms_for_name in gen_roots.items():
        formal_atoms[Node("G", name)] = atoms_for_name
    for name, atoms_for_name in primitive_atoms.items():
        formal_atoms[Node("P", name)] = atoms_for_name
    for name, atoms_for_name in recursive_atoms.items():
        formal_atoms[Node("R", name)] = atoms_for_name
    for name, atoms_for_name in pending_atoms.items():
        formal_atoms[Node("U", name)] = atoms_for_name

    nodes: set[Node] = {Node("root", "一元")}
    edges: set[Edge] = set()

    for face in faces:
        node = Node("face", face)
        nodes.add(node)
        edges.add(Edge(Node("root", "一元"), node, "显面"))

    for core in core_atoms:
        core_node = Node("core", core)
        nodes.add(core_node)
        glyph = core_glyphs[core]
        for face in atom_faces.get(glyph, []):
            edges.add(Edge(Node("face", face), core_node, "显核"))

    for atom in atoms:
        atom_node = Node("atom", atom)
        nodes.add(atom_node)
        edges.add(Edge(Node("core", atom_cores[atom]), atom_node, "派生"))

    for name in generated:
        node = Node("G", name)
        nodes.add(node)
        for atom in gen_roots.get(name, []):
            edges.add(Edge(Node("atom", atom), node, "生成"))

    for name in primitives:
        node = Node("P", name)
        nodes.add(node)
        for atom in primitive_atoms.get(name, []):
            edges.add(Edge(Node("atom", atom), node, "锚定"))

    for name in recursive:
        node = Node("R", name)
        nodes.add(node)
        for atom in recursive_atoms.get(name, []):
            edges.add(Edge(Node("atom", atom), node, "递归锚"))

    for name in pending:
        node = Node("U", name)
        nodes.add(node)
        for atom in pending_atoms.get(name, []):
            edges.add(Edge(Node("atom", atom), node, "待校锚"))

    for name in construction:
        node = Node("C", name)
        nodes.add(node)
        edges.add(Edge(Node("atom", construction_atoms[name]), node, "构造锚"))

    for claim in claims:
        claim_node = Node("claim", claim)
        nodes.add(claim_node)
        formal = claim_formals[claim]
        edges.add(Edge(Node("atom", formal_atoms[formal][0]), claim_node, "回字"))
        edges.add(Edge(formal, claim_node, "承载"))

    node_list = sorted(nodes, key=node_order)
    edge_list = sorted(edges, key=lambda e: (node_order(e.source), node_order(e.target), e.label))
    sources = unique_sources(node_list, edge_list)
    is_acyclic = acyclic(node_list, edge_list)
    root_only = sources == [Node("root", "一元")]

    ids = node_id_map(node_list)
    lines = [
        "%% Generated by scripts/generate_monad_dag.py from Lean sources.",
        "%% Single-root proof-shape graph: 一元 -> 面 -> 核心单字 -> 单字 -> 正式项 -> claim.",
        f"%% Unique root: {str(root_only).lower()}",
        f"%% Acyclic: {str(is_acyclic).lower()}",
        "flowchart TB",
    ]

    # Keep the first layers readable in rendered output.
    lines.append("  subgraph RootLayer[\"唯一根\"]")
    lines.append(mermaid_node(Node("root", "一元"), ids, claim_labels))
    lines.append("  end")
    for kind, title in [("face", "一元之面"), ("core", "核心单字"), ("atom", "派生单字/登记单字"), ("G", "生成项"), ("P", "原始算子"), ("R", "递归项"), ("U", "待校项"), ("C", "构造阶段"), ("claim", "Claim Ledger")]:
        group_nodes = [n for n in node_list if n.kind == kind]
        if not group_nodes:
            continue
        group_id = re.sub(r"[^A-Za-z0-9]", "", kind) or "Group"
        lines.append(f"  subgraph {group_id}Layer[\"{title}\"]")
        for node in group_nodes:
            lines.append(mermaid_node(node, ids, claim_labels))
        lines.append("  end")

    lines.append("")
    for edge in edge_list:
        lines.append(mermaid_edge(edge, ids))
    lines += CLASS_DEF

    (OUT_DIR / "MonadDAG.mmd").write_text("\n".join(lines) + "\n")

    md = [
        "# Monad DAG / 一元单根生成图",
        "",
        "方向约定：`一元 -> 面 -> 核心单字 -> 单字 -> 正式项 -> claim`。",
        "",
        "## 完整性口径",
        "",
        f"- 面：{len(faces)} 个",
        f"- 核心单字：{len(core_atoms)} 个",
        f"- 单字：{len(atoms)} 个",
        f"- 生成项：{len(generated)} 个",
        f"- 原始算子：{len(primitives)} 个",
        f"- 递归项：{len(recursive)} 个",
        f"- 待校项：{len(pending)} 个",
        f"- 构造阶段：{len(construction)} 个",
        f"- claim：{len(claims)} 个",
        f"- 总节点：{len(node_list)} 个",
        f"- 依赖边：{len(edge_list)} 条",
        f"- 唯一根：{root_only}",
        f"- 环检测：{'无环' if is_acyclic else '有环'}",
        "",
        "## Mermaid Source",
        "",
        "- `formal/SSBX/MonadDAG.mmd`",
        "- `formal/SSBX/MonadDAG.svg`",
        "",
        "## 图",
        "",
        "```mermaid",
        *lines[4:],
        "```",
        "",
    ]
    (OUT_DIR / "MonadDAG.md").write_text("\n".join(md))

    if not root_only:
        raise SystemExit(f"MonadDAG has non-root sources: {sources}")
    if not is_acyclic:
        raise SystemExit("MonadDAG has a cycle")
    print(f"wrote {OUT_DIR / 'MonadDAG.mmd'}")
    print(f"nodes={len(node_list)} edges={len(edge_list)} unique_root={root_only} acyclic={is_acyclic}")


if __name__ == "__main__":
    main()
