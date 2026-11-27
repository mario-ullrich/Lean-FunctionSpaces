#!/usr/bin/env python3
"""Write ``dep_graph_overview.html``: the main results of the project as Graphviz source.

The dependency graph read off the Lean proofs (``blueprint/graph/data.json``, published as
``graph/flow.html``) has one node per main result, grouped into the blocks of the project.
This script turns it into a small Graphviz graph: one cluster per block, one node per result,
and the arrows that are not implied by others. It writes the source into
``blueprint/web/dep_graph_overview.html`` as ``.renderDot(`...`)``, the form in which
leanblueprint's graph pages carry their graphs, so that a picture elsewhere (the Lean page of
the author's homepage) can lay it out with the Graphviz build of this site.

Nodes look like those of leanblueprint's graph: definitions as boxes in light green, results
as ellipses in green, all with a green border. As there, an arrow runs from a result to the
results that use it, and the graph runs from left to right: the base results on the left. With
few ranks and many results per rank, the picture comes out taller than wide. Run it from the
project root after ``leanblueprint web``. It fails if a node names a block that does not exist.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

DATA = Path("blueprint/graph/data.json")
PAGE = Path("blueprint/web/dep_graph_overview.html")


def quote(s: str) -> str:
    """A Graphviz string literal."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def dot_source(data: dict) -> str:
    groups = {g["id"]: g["title"] for g in data["groups"]}
    lines = [
        'strict digraph "" {',
        "  graph [bgcolor=transparent, rankdir=LR];",
        '  node [label="\\N", penwidth=1.8];',
        "  edge [arrowhead=vee];",
    ]
    members: dict[str, list[str]] = {g: [] for g in groups}
    for n in data["nodes"]:
        if n["group"] not in groups:
            sys.exit(f"node {n['id']} names the unknown block {n['group']}")
        members[n["group"]].append(n["id"])
        if n["kind"] == "definition":
            style = 'shape=box, fillcolor="#B0ECA3"'
        else:
            style = 'shape=ellipse, fillcolor="#1CAC78"'
        lines.append(f"  {quote(n['id'])} [color=green, style=filled, {style}];")
    for i, (gid, title) in enumerate(groups.items()):
        ids = " ".join(f"{quote(m)};" for m in members[gid])
        lines.append(
            f"  subgraph cluster_{i} {{ label={quote(title)}; labeljust=l; "
            'fontname="Helvetica"; fontcolor="#808080"; color="#b0b0b0"; style=rounded; '
            f"penwidth=1; margin=12; {ids} }}"
        )
    # In data.json an edge runs from a result to a result it uses.
    for e in data["edges"]:
        if not e.get("redundant"):
            lines.append(f"  {quote(e['target'])} -> {quote(e['source'])};")
    lines.append("}")
    return "\n".join(lines)


def main() -> int:
    data = json.loads(DATA.read_text(encoding="utf-8"))
    dot = dot_source(data)
    if "`" in dot:
        sys.exit("a backtick in the graph would end the template literal")
    title = data.get("meta", {}).get("title", "Dependency graph")
    PAGE.write_text(
        "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n"
        "<meta name=\"robots\" content=\"noindex\">\n"
        f"<title>{title}: overview</title>\n</head>\n<body>\n"
        "<p>The main results and their blocks as Graphviz source, for pictures elsewhere. "
        "The interactive dependency graph is <a href=\"graph/flow.html\">here</a>.</p>\n"
        "<script type=\"text/plain\">\n.renderDot(`" + dot + "`)\n</script>\n"
        "</body>\n</html>\n",
        encoding="utf-8",
    )
    print(f"wrote {PAGE}: {len(data['nodes'])} nodes, "
          f"{sum(not e.get('redundant') for e in data['edges'])} edges")
    return 0


if __name__ == "__main__":
    sys.exit(main())
