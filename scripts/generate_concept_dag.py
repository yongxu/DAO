#!/usr/bin/env python3
"""Generate SSBX concept DAG visualizations from the Lean roster.

Completeness policy:
- every AtomName, GenName, PrimName, RecName, PendingName is a node;
- rootsOfGenerated creates root edges into generated terms;
- depsOfGenerated creates additional dependency edges when it differs from roots;
- recDeps creates dependency edges into recursive terms;
- isolated registered symbols remain visible.
"""
from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ROSTER = ROOT / "formal/SSBX/Roster.lean"
OUT_DIR = ROOT / "formal/SSBX"

KIND_LABEL = {
    "A": "字根",
    "G": "生成",
    "P": "原始算子",
    "R": "递归",
    "U": "待校",
}

CLASS_NAME = {
    "A": "atom",
    "G": "generated",
    "P": "primitive",
    "R": "recursive",
    "U": "pending",
}

CLASS_DEF = [
    "  classDef atom fill:#f8fafc,stroke:#64748b,color:#0f172a;",
    "  classDef generated fill:#ecfeff,stroke:#0891b2,color:#164e63;",
    "  classDef primitive fill:#f0fdf4,stroke:#16a34a,color:#14532d;",
    "  classDef recursive fill:#fff7ed,stroke:#ea580c,color:#7c2d12;",
    "  classDef pending fill:#fef2f2,stroke:#dc2626,color:#7f1d1d;",
    "  classDef external fill:#f5f3ff,stroke:#7c3aed,color:#3b0764;",
]

@dataclass(frozen=True, order=True)
class Node:
    kind: str
    name: str

@dataclass(frozen=True)
class Edge:
    source: Node
    target: Node
    relation: str


def read_roster() -> str:
    return ROSTER.read_text()


def extract_inductive_names(text: str, type_name: str) -> list[str]:
    block = text.split(f"inductive {type_name} where", 1)[1].split("deriving", 1)[0]
    out: list[str] = []
    for line in block.splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        parts = [p.strip() for p in line[1:].split("|")]
        for part in parts:
            if not part:
                continue
            quoted = re.fullmatch(r"«([^»]+)»", part)
            if quoted:
                out.append(quoted.group(1))
            else:
                out.append(part.split()[0])
    return out


def extract_function_block(text: str, start: str, end: str) -> str:
    return text.split(start, 1)[1].split(end, 1)[0]


def parse_symbol(token: str) -> Node | None:
    token = token.strip()
    m = re.fullmatch(r"([AGRPU]) \.«([^»]+)»", token)
    if m:
        return Node(m.group(1), m.group(2))
    m = re.fullmatch(r"([AGRPU]) \.([A-Za-z0-9_ΓΩΘΦΠκμ]+)", token)
    if m:
        return Node(m.group(1), m.group(2))
    return None


def parse_rhs_symbols(rhs: str) -> list[Node]:
    out: list[Node] = []
    for token in rhs.split(","):
        node = parse_symbol(token)
        if node is not None:
            out.append(node)
    return out


def parse_cases(block: str, target_kind: str) -> dict[Node, list[Node]]:
    out: dict[Node, list[Node]] = {}
    for line in block.splitlines():
        m = re.match(r"^\s*\| \.«([^»]+)» => \[(.*)\]", line)
        if not m:
            m = re.match(r"^\s*\| \.([A-Za-z0-9_ΓΩΘΦΠκμ]+) => \[(.*)\]", line)
        if not m:
            continue
        target = Node(target_kind, m.group(1))
        out[target] = parse_rhs_symbols(m.group(2))
    return out


def dedup_edges(edges: list[Edge]) -> list[Edge]:
    seen: set[Edge] = set()
    out: list[Edge] = []
    for edge in edges:
        if edge not in seen:
            out.append(edge)
            seen.add(edge)
    return out


def node_label(node: Node) -> str:
    return f"{node.name}｜{KIND_LABEL[node.kind]}"


def node_id_map(nodes: list[Node]) -> dict[Node, str]:
    order = {"A": 0, "G": 1, "P": 2, "R": 3, "U": 4}
    sorted_nodes = sorted(nodes, key=lambda n: (order.get(n.kind, 9), n.name))
    return {node: f"n{i}" for i, node in enumerate(sorted_nodes)}


def mermaid_node(node: Node, ids: dict[Node, str]) -> str:
    return f"  {ids[node]}[\"{node_label(node)}\"]:::{CLASS_NAME[node.kind]}"


def mermaid_edge(edge: Edge, ids: dict[Node, str]) -> str:
    if edge.relation == "root":
        return f"  {ids[edge.source]} -->|根| {ids[edge.target]}"
    if edge.relation == "dep":
        return f"  {ids[edge.source]} -.->|依| {ids[edge.target]}"
    if edge.relation == "rec":
        return f"  {ids[edge.source]} -->|递归依| {ids[edge.target]}"
    return f"  {ids[edge.source]} --> {ids[edge.target]}"


def cycle_check(nodes: list[Node], edges: list[Edge]) -> bool:
    adj: dict[Node, list[Node]] = defaultdict(list)
    indeg: dict[Node, int] = {node: 0 for node in nodes}
    for edge in edges:
        adj[edge.source].append(edge.target)
        indeg[edge.target] = indeg.get(edge.target, 0) + 1
        indeg.setdefault(edge.source, 0)
    q = deque([node for node, degree in indeg.items() if degree == 0])
    visited = 0
    while q:
        node = q.popleft()
        visited += 1
        for nxt in adj[node]:
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                q.append(nxt)
    return visited == len(indeg)


def generated_category(name: str) -> str:
    groups = [
        ("开闭生成", {"可生", "复开", "再生", "断闭", "绝闭", "机闭", "成闭", "元闭", "夺闭", "蔽闭", "伪闭", "似开", "实闭", "伪开", "偏闭", "强护开", "归开"}),
        ("审校生成", {"回观", "回观稳", "回观不败", "异入", "众应", "迹查", "互证", "源独", "受入", "受黜", "迹蔽", "证源同执", "审校不败"}),
        ("共同体与行动", {"共开", "共续", "己续", "夺依", "护开", "护闭", "正行", "邪行", "正危", "正筛", "邪势", "状态夺"}),
        ("价值与真道", {"自由", "繁荣", "真道", "度期周", "正续", "夺共续", "续能", "夺益", "生生不息"}),
        ("限域与可校", {"可识", "可择", "可校", "未定", "限试", "限域", "限期", "限损", "基线替径", "格物", "相关度期", "异可显", "异可通", "被迫"}),
    ]
    for group, names in groups:
        if name in names:
            return group
    return "基础生成"


def write_complete_mmd(nodes: list[Node], edges: list[Edge], acyclic: bool) -> None:
    ids = node_id_map(nodes)
    lines = [
        "%% Generated by scripts/generate_concept_dag.py from formal/SSBX/Roster.lean.",
        "%% Complete registered-symbol graph. Direction: root/dependency --> concept.",
        f"%% Acyclic: {str(acyclic).lower()}",
        "flowchart LR",
    ]
    for node in sorted(nodes, key=lambda n: ids[n]):
        lines.append(mermaid_node(node, ids))
    for edge in edges:
        lines.append(mermaid_edge(edge, ids))
    lines += CLASS_DEF
    (OUT_DIR / "ConceptDAG.complete.mmd").write_text("\n".join(lines) + "\n")
    # Keep this filename as the audit graph for existing links.
    (OUT_DIR / "ConceptDAG.full.mmd").write_text("\n".join(lines) + "\n")


def write_layered_mmd(nodes: list[Node], edges: list[Edge], acyclic: bool) -> None:
    ids = node_id_map(nodes)
    lines = [
        "%% Generated by scripts/generate_concept_dag.py from formal/SSBX/Roster.lean.",
        "%% Layered complete view: all registered nodes, grouped by registry class.",
        f"%% Acyclic: {str(acyclic).lower()}",
        "flowchart TB",
        "  subgraph Atoms[\"字根项 AtomName\"]",
    ]
    for node in sorted([n for n in nodes if n.kind == "A"], key=lambda n: n.name):
        lines.append(mermaid_node(node, ids))
    lines.append("  end")

    gen_nodes = sorted([n for n in nodes if n.kind == "G"], key=lambda n: n.name)
    by_group: dict[str, list[Node]] = defaultdict(list)
    for node in gen_nodes:
        by_group[generated_category(node.name)].append(node)
    group_ids = {
        "基础生成": "GBase",
        "开闭生成": "GOpenClose",
        "审校生成": "GAudit",
        "共同体与行动": "GCommunityAction",
        "价值与真道": "GValueTruth",
        "限域与可校": "GBoundedAudit",
    }
    for group in ["基础生成", "开闭生成", "审校生成", "共同体与行动", "价值与真道", "限域与可校"]:
        lines.append(f"  subgraph {group_ids[group]}[\"{group} GenName\"]")
        for node in by_group.get(group, []):
            lines.append(mermaid_node(node, ids))
        lines.append("  end")

    for kind, title in [("P", "原始算子项 PrimName"), ("R", "递归项 RecName"), ("U", "待校项 PendingName")]:
        lines.append(f"  subgraph {kind}Group[\"{title}\"]")
        for node in sorted([n for n in nodes if n.kind == kind], key=lambda n: n.name):
            lines.append(mermaid_node(node, ids))
        lines.append("  end")

    lines.append("")
    for edge in edges:
        lines.append(mermaid_edge(edge, ids))
    lines += CLASS_DEF
    (OUT_DIR / "ConceptDAG.layered.mmd").write_text("\n".join(lines) + "\n")


def write_core_mmd() -> None:
    core = '''%% Reading-oriented summary. Not complete; use ConceptDAG.complete.mmd for full registry coverage.
flowchart TB
  subgraph W["物面 / 格物"]
    物["物｜字根"]:::atom
    面["面｜字根"]:::atom
    格["格｜字根"]:::atom
    域["域｜字根"]:::atom
    验["验｜字根"]:::atom
    格物["格物｜生成"]:::generated
    经验校准["经验校准｜待校"]:::pending
  end

  subgraph M["模 / 科学评价"]
    模["模｜字根"]:::atom
    评["评｜字根"]:::atom
    价["价｜字根"]:::atom
    科["科｜字根"]:::atom
    学["学｜字根"]:::atom
    可校["可校｜生成"]:::generated
    互证["互证｜生成"]:::generated
    审校不败["审校不败｜生成"]:::generated
  end

  subgraph F["形式证明 / CIC 位置"]
    逻["逻｜字根"]:::atom
    辑["辑｜字根"]:::atom
    构["构｜字根"]:::atom
    造["造｜字根"]:::atom
    纳["纳｜字根"]:::atom
    证["证｜字根"]:::atom
    明["明｜字根"]:::atom
    算["算｜字根"]:::atom
    理["理｜字根"]:::atom
    CIC模["CIC / 归纳构造演算｜外部模"]:::external
  end

  subgraph C["核心价值递归"]
    开["开｜递归"]:::recursive
    闭["闭｜递归"]:::recursive
    正["正｜递归"]:::recursive
    邪["邪｜递归"]:::recursive
    共开["共开｜递归"]:::recursive
    坏["坏｜递归"]:::recursive
    义["义｜递归"]:::recursive
    善["善｜递归"]:::recursive
    仁["仁｜递归"]:::recursive
    道["道｜递归"]:::recursive
    真["真｜递归"]:::recursive
    真道["真道｜生成"]:::generated
  end

  物 --> 格物
  格 --> 格物
  格物 --> 经验校准
  域 --> 经验校准
  验 --> 经验校准

  模 --> 可校
  评 --> 可校
  价 --> 可校
  科 --> 可校
  学 --> 可校
  审["审｜字根"]:::atom --> 审校不败
  校["校｜字根"]:::atom --> 审校不败
  败["败｜字根"]:::atom --> 审校不败
  可校 --> 审校不败
  互证 --> 审校不败

  逻 --> CIC模
  辑 --> CIC模
  构 --> CIC模
  造 --> CIC模
  纳 --> CIC模
  证 --> CIC模
  明 --> CIC模
  算 --> CIC模
  理 --> CIC模
  CIC模 --> 可校

  经验校准 --> 开
  审校不败 --> 正
  开 --> 正
  闭 --> 邪
  开 --> 共开
  闭 --> 坏
  正 --> 义
  义 --> 善
  共开 --> 道
  坏 --> 道
  审校不败 --> 真
  真 --> 真道
  道 --> 真道

  可校 --> 真

  classDef atom fill:#f8fafc,stroke:#64748b,color:#0f172a;
  classDef generated fill:#ecfeff,stroke:#0891b2,color:#164e63;
  classDef recursive fill:#fff7ed,stroke:#ea580c,color:#7c2d12;
  classDef pending fill:#fef2f2,stroke:#dc2626,color:#7f1d1d;
  classDef external fill:#f5f3ff,stroke:#7c3aed,color:#3b0764;
'''
    (OUT_DIR / "ConceptDAG.core.mmd").write_text(core)


def write_markdown(node_counts: dict[str, int], edge_count: int, acyclic: bool) -> None:
    core = (OUT_DIR / "ConceptDAG.core.mmd").read_text().strip()
    md = f'''# Concept DAG / 概念有向无环图

方向约定：`字根 / 依赖项 --> 生成项 / 递归项`。

边界声明：`ConceptDAG` 是名册依赖图，不是单根生成证明；单根证明以 `MonadDAG` 和 `Foundation/MonadRoot.lean` 为准。

## 完整性口径

这次的“完整图”不是摘要图，而是覆盖 Lean 名册中全部登记项：

- `AtomName`：{node_counts['A']} 个
- `GenName`：{node_counts['G']} 个
- `PrimName`：{node_counts['P']} 个
- `RecName`：{node_counts['R']} 个
- `PendingName`：{node_counts['U']} 个
- 总节点：{sum(node_counts.values())} 个
- 依赖边：{edge_count} 条
- 环检测：{'无环，可作为 DAG 阅读' if acyclic else '发现环，需要检查名册依赖'}

## 核心摘要图

这张只用于说明主干，不声称完整。

```mermaid
{core}
```

## 完整图文件

- [ConceptDAG.complete.mmd](./ConceptDAG.complete.mmd)：完整登记图，所有名册节点都显示，包括孤立字根、原始算子、待校项。
- [ConceptDAG.layered.mmd](./ConceptDAG.layered.mmd)：完整分层图，按字根、生成项、递归项、原始算子项、待校项分组。
- [ConceptDAG.full.mmd](./ConceptDAG.full.mmd)：同完整登记图，保留旧文件名用于兼容。

## 读法

- `atom`：单字根，不再向下拆。
- `generated`：由字根或其他生成项合成。
- `primitive`：模型/度量/算子接口，不由字元生成。
- `recursive`：价值/真理类递归谓词，需要三值、不动点或外部审校语义。
- `pending`：经验或模型项，不能冒称已真。
- `external`：说明性外部对象，例如 CIC；它参与摘要说明，但不是当前名册中的生成项。

## 注意

这张图证明的是“名册依赖形状可作为 DAG 展示”。它不是额外哲学证明；哲学真理仍由 `Truth` 和 `Model` 层的公理账本与模型充分性承载。
'''
    (OUT_DIR / "ConceptDAG.md").write_text(md)


def main() -> None:
    text = read_roster()
    names = {
        "A": extract_inductive_names(text, "AtomName"),
        "G": extract_inductive_names(text, "GenName"),
        "P": extract_inductive_names(text, "PrimName"),
        "R": extract_inductive_names(text, "RecName"),
        "U": extract_inductive_names(text, "PendingName"),
    }
    nodes = [Node(kind, name) for kind, group in names.items() for name in group]

    roots_block = extract_function_block(text, "def rootsOfGenerated", "def depsOfGenerated")
    deps_block = extract_function_block(text, "def depsOfGenerated", "def recDeps")
    rec_block = extract_function_block(text, "def recDeps", "def recSemOf")

    root_cases = parse_cases(roots_block, "G")
    dep_cases = parse_cases(deps_block, "G")
    rec_cases = parse_cases(rec_block, "R")

    edges: list[Edge] = []
    for target, sources in root_cases.items():
        for source in sources:
            edges.append(Edge(source, target, "root"))
    for target, sources in dep_cases.items():
        for source in sources:
            # Keep dependency edges even if roots also exist; relation differs and is useful in the audit graph.
            edges.append(Edge(source, target, "dep"))
    for target, sources in rec_cases.items():
        for source in sources:
            edges.append(Edge(source, target, "rec"))
    edges = dedup_edges(edges)

    node_set = set(nodes)
    missing = sorted(({edge.source for edge in edges} | {edge.target for edge in edges}) - node_set)
    if missing:
        missing_text = ", ".join(f"{node.kind}:{node.name}" for node in missing)
        raise SystemExit(f"dependency mentions unregistered nodes: {missing_text}")

    acyclic = cycle_check(nodes, edges)
    write_complete_mmd(nodes, edges, acyclic)
    write_layered_mmd(nodes, edges, acyclic)
    write_core_mmd()
    write_markdown({kind: len(group) for kind, group in names.items()}, len(edges), acyclic)
    print(f"nodes={len(nodes)} edges={len(edges)} acyclic={acyclic}")
    print(f"wrote {OUT_DIR / 'ConceptDAG.md'}")
    print(f"wrote {OUT_DIR / 'ConceptDAG.complete.mmd'}")
    print(f"wrote {OUT_DIR / 'ConceptDAG.layered.mmd'}")


if __name__ == "__main__":
    main()
