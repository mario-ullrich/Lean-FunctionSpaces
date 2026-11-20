#!/usr/bin/env python3
"""Hide the helper lemmas of the dependency graph, and add a second graph grouped into blocks.

leanblueprint (through plastexdepgraph) writes the dependency graph as DOT source into
``dep_graph_document.html``, where the browser lays it out with Graphviz. With every result
of the project the graph has several hundred nodes. This script rewrites the DOT source:

* **Steps are hidden.** The graph keeps the theorems, the corollaries and the definitions
  they use. A lemma or proposition that is fully proved is a step towards them (``STEPS``),
  and a definition used only by steps belongs to them; both are left out, and every arrow
  into one of them now points to the results that use it. The transitive reduction is then
  taken again, as plastexdepgraph does, so no arrow repeats what a path already says. A lemma
  or proposition without a complete proof stays, so the graph shows what is left to prove.
* **Every edge is drawn solid.** plastexdepgraph dashes the edges that come from a ``\\uses``
  inside a statement; here they only say that a statement uses a definition, and an arrow
  through a hidden lemma has no single kind, so one kind of arrow suffices.
* **The source is sorted** by block and name. plastexdepgraph emits nodes and edges in the
  order of a Python set, which changes from run to run and makes Graphviz mirror the picture
  between builds; a fixed order gives the same picture every time.

The result replaces the graph of ``dep_graph_document.html``. A copy of the page,
``dep_graph_grouped.html``, shows the same graph with its nodes **grouped into blocks**,
framed and titled, along the blocks of the README, some of them split into parts
(``BLOCKS``); the blocks are **stacked in columns** (``COLUMNS``). A node's block comes from the
chapter, and for the long chapters the section, that holds its ``\\label`` in the blueprint
source. On both pages

* the legend gains a line saying which nodes are not shown;
* the header links to the other page;
* the graph can be zoomed in further: d3-graphviz stops at ten times the fitted size, too
  little to read a graph of this width (``ZOOM``);
* ctrl+wheel and touchpad pinches zoom the graph instead of the page (``PINCH``).

The main graph runs from left to right (``MAIN_ATTRS``); the grouped one from top to bottom,
since its columns are stacked vertically.

The script fails if a node's chapter, or its section in a chapter split by sections, belongs
to no block, so new material cannot silently fall outside every frame. A second run changes
nothing.

Usage::

    python blueprint/scripts/tidy_dep_graph.py [--web DIR] [--tex TEX]
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

# The blocks, in the order in which their frames are emitted. Each entry is the frame's title
# and the chapters it holds; a chapter given as (chapter, [sections]) contributes only those
# sections. A node goes to the first block that names its chapter or its section, so a section
# listed in an earlier block leaves the rest of its chapter to a later one: the section on
# n-term approximation from a Hilbert basis stands with the approximation spaces, the rest of
# the chapter on spectral schemes with the measure spaces. The titles are those of
# `blueprint/src/content.tex` and of the files it includes with `\input`.
INTERVALS = "Polynomial approximation on intervals"
BESOV_RD = r"Besov spaces on \texorpdfstring{$\R^d$}{R\^{}d}"
SOB = r"Sobolev spaces on \texorpdfstring{$\R^d$}{R\^{}d}"
BLOCKS: list[tuple[str, list]] = [
    ("Approximation spaces: general theory", [
        "Approximation schemes", "Sequence spaces", "Approximation spaces",
        "Lifting and the Nikolskii transfer theorem",
        "Interpolation and the representation theorem",
        ("Spectral schemes", ["Nonlinear approximation from a Hilbert basis"])]),
    ("Real interpolation of couples", ["Real interpolation of couples"]),
    ("Decompositions, traces and moduli", [
        "Block decompositions and projections", "Traces and intrinsic norms",
        "Moduli of smoothness and approximation"]),
    ("Besov and Sobolev spaces on measure spaces", [
        "Besov spaces and their embeddings", "Sobolev spaces and their embeddings",
        "Spectral schemes"]),
    ("Convolution and the Fourier transform", [
        r"Convolution and the Fourier transform on \texorpdfstring{$\R^d$}{R\^{}d}"]),
    ("Maximal functions and the Fefferman–Stein inequality", ["Maximal functions"]),
    ("Interpolation of operators", ["Interpolation of operators"]),
    ("The torus", ["The torus", "Classical definitions on the torus"]),
    ("The Haar system and multiwavelets", [
        "Filtrations and martingale differences",
        (INTERVALS, ["Haar coefficients",
                     r"Dyadic step functions for \texorpdfstring{$0 < p \leq 1$}{0 < p <= 1}",
                     r"The Haar system for \texorpdfstring{$0 < p \leq 1$}{0 < p <= 1}",
                     "Local projections and multiscale details", "Multiwavelets"])]),
    ("Piecewise polynomials on intervals", [
        (INTERVALS, ["Differences and moduli", "Polynomials on intervals", "Steklov smoothing",
                     "Whitney's inequality", "Dyadic piecewise polynomials",
                     "Piecewise polynomials on the circle"])]),
    ("Splines", [
        (INTERVALS, ["Cardinal B-splines", "Dyadic splines",
                     "The inverse inequality for splines", "A spline quasi-interpolant",
                     "Jackson's inequality for splines and the coincidence theorem",
                     "Splines on the circle", "Differences of every order"])]),
    ("The cube", ["Approximation on the cube"]),
    ("Littlewood–Paley blocks", [
        (BESOV_RD, ["Band-limited approximation", "The Littlewood--Paley decomposition"])]),
    ("Differences and local means", [
        (BESOV_RD, ["Differences and moduli of smoothness", "Moduli of smoothness on subsets",
                    "Moment kernels", "Jackson's inequality", "The inverse inequality",
                    "Besov spaces by differences", "Sobolev--Slobodeckij norms",
                    "Local means",
                    "Besov spaces as interpolation spaces"])]),
    ("Multipliers and atoms", [
        (BESOV_RD, ["Pointwise multipliers", "Atoms", "Atomic decompositions"])]),
    ("Smooth atoms and changes of variables", [
        (BESOV_RD, ["Smooth atoms", "Invariance under changes of variables"])]),
    ("Daubechies wavelets", ["Daubechies wavelets"]),
    ("Dominating mixed smoothness", [
        r"Dominating mixed smoothness on \texorpdfstring{$\R^d$}{R\^{}d}"]),
    ("Triebel–Lizorkin spaces", ["Triebel--Lizorkin spaces"]),
    ("Vector-valued singular integrals", ["Vector-valued singular integrals"]),
    ("Sobolev spaces: the bridge for p = 2", [
        (SOB, ["Weak derivatives on open sets", "Changes of variables and cutoffs",
               r"Mathlib's Sobolev spaces \texorpdfstring{$H^s$}{H\^{}s} by Littlewood--Paley blocks",
               "Rellich compactness"])]),
    ("Sobolev spaces W^m_p", [
        (SOB, ["The Leibniz rule", "Derivative kernels", "Divergence kernels",
               "Sobolev spaces as Triebel--Lizorkin spaces",
               "Sobolev embeddings", "The critical Sobolev embedding",
               "The Gagliardo--Nirenberg--Sobolev inequality",
               "Sobolev spaces and real interpolation"])]),
    ("Sobolev spaces on the torus", ["Sobolev spaces on the torus"]),
    ("Bessel potential spaces", ["Bessel potential spaces"]),
    ("Fourier multipliers", ["Fourier multipliers"]),
    ("Lipschitz domains", ["Lipschitz domains"]),
    ("Traces", ["Traces on Lipschitz domains"]),
    ("Sobolev spaces on domains and boundaries", ["Sobolev spaces on domains"]),
    ("Eigenbases of the Laplacian", ["Eigenbases of the Laplacian"]),
    ("Compact manifolds", ["Besov spaces on compact manifolds",
                           "Eigenfunction expansions on compact manifolds"]),
]

# Columns of blocks: in each list, every block is placed below the one before it. Without
# them Graphviz sets most blocks side by side, in a band some 250 inches wide; stacked, the
# picture is about square. Between two stacked blocks an invisible node takes the arrows from
# the lowest results of the upper block to the first results of the lower one, and keeps a
# free row between the frames.
COLUMNS: list[list[str]] = [
    ["Approximation spaces: general theory", "Decompositions, traces and moduli",
     "Besov and Sobolev spaces on measure spaces", "Convolution and the Fourier transform",
     "Littlewood–Paley blocks", "Differences and local means", "Lipschitz domains",
     "Multipliers and atoms", "Smooth atoms and changes of variables", "Traces",
     "Compact manifolds", "Dominating mixed smoothness"],
    ["Besov and Sobolev spaces on measure spaces", "The torus", "Daubechies wavelets"],
    ["Differences and local means", "Piecewise polynomials on intervals",
     "The Haar system and multiwavelets", "Splines", "The cube",
     "Dominating mixed smoothness"],
    ["Convolution and the Fourier transform",
     "Maximal functions and the Fefferman–Stein inequality", "Triebel–Lizorkin spaces",
     "Sobolev spaces: the bridge for p = 2", "Interpolation of operators",
     "Vector-valued singular integrals", "Sobolev spaces W^m_p", "Sobolev spaces on the torus",
     "Bessel potential spaces", "Fourier multipliers"],
    ["Traces", "Sobolev spaces on domains and boundaries", "Eigenbases of the Laplacian"],
    ["Approximation spaces: general theory", "Real interpolation of couples"],
]
GAP = 2

# Attributes of the grouped graph. The columns need `newrank`: without it Graphviz ranks each
# block on its own and ignores the invisible arrows between blocks. The columns, the gap and
# `mclimit` (more passes against crossings) were chosen by counting edge crossings in the
# layout of the page's own Graphviz (2.44): about 2550, against 3400 for the graph without
# blocks and with every lemma.
GRAPH_ATTRS = "newrank=true; mclimit=4;"

# The two pages, their headings, and the link from each to the other.
MAIN_PAGE = "dep_graph_document.html"
GROUPED_PAGE = "dep_graph_grouped.html"
GROUPED_TITLE = "Dependencies, grouped"
SWITCH = '<a class="graph-switch" href="{href}">{text}</a>'

# Attributes of the main graph: base results on the left, derived results on the right.
MAIN_ATTRS = "rankdir=LR;"

# The zoom range of d3-graphviz, as multiples of the fitted size (default [0.1, 10]).
ZOOM = ".zoomScaleExtent([0.1, 200])"

# Run when the graph is drawn: the graph, not the page, takes ctrl+wheel and touchpad pinches
# (a pinch reaches the page as ctrl+wheel). d3's zoom ignores ctrl+wheel by default, so the
# browser zoomed the whole page, and with it the statement that opens on a click, which then
# lay outside the window or came out huge. A pinch moves little, so its steps are enlarged.
PINCH = """
    var zoom = document.getElementById("graph").__graphviz__.zoomBehavior();
    if (zoom) {
        zoom.filter(function () { return !d3.event.button; })
            .wheelDelta(function () {
                var e = d3.event;
                return -e.deltaY * (e.deltaMode === 1 ? 0.05 : e.deltaMode ? 1 : 0.002)
                    * (e.ctrlKey ? 10 : 1);
            });
    }
    document.getElementById("graph").addEventListener("wheel", function (e) {
        if (e.ctrlKey) { e.preventDefault(); }
    }, {passive: false});
"""

# The frame of a block: a thin grey rounded line, the title at the top left.
CLUSTER_ATTRS = ('labeljust=l; style=rounded; color="#b0b0b0"; fontcolor="#808080"; '
                 'penwidth=1; margin=28;')

# Fill colours of a node whose proof is formalized (alone, or with all its ancestors).
PROVED = {"#B0ECA3", "#1CAC78"}

# The label prefixes of the steps: the kinds of result that the graph leaves out once proved.
STEPS = ("lem", "prop")

LEGEND_ROW = ("<dt>Not shown</dt><dd>lemmas and propositions, and the definitions only they "
              "use; their arrows pass through to the theorems</dd>")

DOT_RE = re.compile(r"renderDot\(`(.*?)`\)", re.S)
BACKSLASH = re.escape("\\")
CHAPTER_RE = re.compile(BACKSLASH + r"chapter\{(.*)\}")
SECTION_RE = re.compile(BACKSLASH + r"section\*?\{(.*)\}")
LABEL_RE = re.compile(BACKSLASH + r"label\{([^}]+)\}")
INPUT_RE = re.compile(BACKSLASH + r"input\{([^}]*)\}")


def read_tex(path: Path) -> str:
    """The text of `path`, each input command replaced by the text of the file it names."""
    text = path.read_text(encoding="utf-8")
    return INPUT_RE.sub(
        lambda m: read_tex(path.parent / (m.group(1).strip().removesuffix(".tex") + ".tex")),
        text)


def statements(body: str) -> list[str]:
    """Split a DOT body at the semicolons that lie outside quotes and brackets."""
    out, cur, depth, quoted, escaped = [], [], 0, False, False
    for ch in body:
        if quoted:
            cur.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                quoted = False
            continue
        if ch == '"':
            quoted = True
        elif ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        elif ch == ";" and depth == 0:
            out.append("".join(cur).strip())
            cur = []
            continue
        cur.append(ch)
    if "".join(cur).strip():
        out.append("".join(cur).strip())
    return [s for s in out if s]


def attributes(text: str) -> dict[str, str]:
    """The attributes `key=value, ...` inside a pair of brackets, values unquoted."""
    attrs = {}
    for key, quoted, bare in re.findall(r'(\w+)\s*=\s*(?:"((?:[^"\\]|\\.)*)"|([^,\s\]]+))', text):
        attrs[key] = quoted if quoted or not bare else bare
    return attrs


def quote(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def node_places(tex: str) -> dict[str, tuple[str, str | None]]:
    """The chapter and the section (within that chapter) of every `\\label`."""
    marks = [(m.start(), "chapter", m.group(1)) for m in CHAPTER_RE.finditer(tex)]
    marks += [(m.start(), "section", m.group(1)) for m in SECTION_RE.finditer(tex)]
    marks += [(m.start(), "label", m.group(1)) for m in LABEL_RE.finditer(tex)]
    places, chapter, section = {}, None, None
    for _, kind, name in sorted(marks):
        if kind == "chapter":
            chapter, section = name, None
        elif kind == "section":
            section = name
        else:
            places[name] = (chapter, section)
    return places


def block_of(chapter: str, section: str | None) -> int | None:
    for index, (_, parts) in enumerate(BLOCKS):
        for part in parts:
            if part == chapter:
                return index
            if isinstance(part, tuple) and part[0] == chapter and section in part[1]:
                return index
    return None


def transitive_reduction(nodes: list[str], edges: set[tuple[str, str]]) -> set[tuple[str, str]]:
    """Drop `u -> v` when `v` is reachable from another successor of `u`."""
    succ: dict[str, set[str]] = defaultdict(set)
    for u, v in edges:
        succ[u].add(v)
    memo: dict[str, set[str]] = {}

    def below(n: str) -> set[str]:
        if n not in memo:
            memo[n] = set()
            reach: set[str] = set()
            for m in succ[n]:
                reach.add(m)
                reach |= below(m)
            memo[n] = reach
        return memo[n]

    for n in nodes:
        below(n)
    return {(u, v) for u, v in edges if not any(v in below(w) for w in succ[u] if w != v)}


def column_lines(kept: list[str], block: dict[str, int],
                 edges: list[tuple[str, str]]) -> list[str]:
    """The invisible nodes and arrows that stack the blocks of each column (`COLUMNS`)."""
    titles = [title for title, _ in BLOCKS]
    inner_succ, inner_pred = set(), set()
    for u, v in edges:
        if block[u] == block[v]:
            inner_succ.add(u)
            inner_pred.add(v)
    lines = []
    for column in COLUMNS:
        for upper, lower in zip(column, column[1:]):
            a, b = titles.index(upper), titles.index(lower)
            sinks = [n for n in kept if block[n] == a and n not in inner_succ]
            sources = [n for n in kept if block[n] == b and n not in inner_pred]
            if not sinks or not sources:
                continue
            gap = quote(f"gap:{a}-{b}")
            lines.append(f'\t{gap} [style=invis, label="", width=0, height=0, fixedsize=true];')
            lines += [f"\t{quote(n)} -> {gap} [style=invis, weight=0];" for n in sinks]
            lines += [f"\t{gap} -> {quote(n)} [style=invis, weight=0, minlen={GAP}];"
                      for n in sources]
    return lines


def node_line(n: str, attrs: dict[str, str], indent: str) -> str:
    text = ", ".join(f"{k}={quote(v)}" for k, v in attrs.items())
    return f"{indent}{quote(n)}" + (f" [{text}];" if text else ";")


def finish_page(html: str, match: re.Match[str], dot: str, link: str,
                title: str | None = None) -> str | None:
    """Put `dot` into the page, and add the legend line, the link, the zoom and the title."""
    html = html[:match.start(1)] + dot + html[match.end(1):]
    legend_end = html.find("</dl>", html.find('<dl class="legend">'))
    header_end = html.find("</header>")
    fit = html.find(".fit(true)")
    hook = html.find("function interactive() {")
    if min(legend_end, header_end, fit, hook) < 0:
        return None
    hook += len("function interactive() {")
    html = html[:hook] + PINCH + html[hook:]
    html = html[:fit] + ".fit(true)" + ZOOM + html[fit + len(".fit(true)"):]
    html = html[:legend_end] + LEGEND_ROW + "\n    " + html[legend_end:]
    header_end = html.find("</header>")
    html = html[:header_end] + "  " + link + "\n" + html[header_end:]
    if title:
        html = html.replace('<h1 id="doc_title">Dependencies</h1>',
                            f'<h1 id="doc_title">{title}</h1>', 1)
        html = html.replace("<title>Dependency graph</title>", f"<title>{title}</title>", 1)
    return html


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--web", default="blueprint/web")
    parser.add_argument("--tex", default="blueprint/src/content.tex")
    args = parser.parse_args()

    page = Path(args.web) / MAIN_PAGE
    html = page.read_text(encoding="utf-8")
    if LEGEND_ROW in html:
        print("dependency graph already tidied; nothing to do")
        return 0
    match = DOT_RE.search(html)
    if match is None:
        print("error: no renderDot(`...`) in the page -- has the upstream template changed?")
        return 1
    dot = match.group(1)

    # Parse the DOT source: the opening line, default attributes, nodes and edges.
    head, _, rest = dot.partition("{")
    body = rest.rsplit("}", 1)[0]
    defaults, nodes, edges = [], {}, set()
    for stmt in statements(body):
        edge = re.match(r'"((?:[^"\\]|\\.)*)"\s*->\s*"((?:[^"\\]|\\.)*)"', stmt)
        node = re.match(r'"((?:[^"\\]|\\.)*)"\s*(?:\[(.*)\])?\s*$', stmt, re.S)
        if edge:
            edges.add((edge.group(1), edge.group(2)))
        elif node:
            nodes[node.group(1)] = attributes(node.group(2) or "")
        elif re.match(r"(graph|node|edge)\s*\[", stmt):
            defaults.append(re.sub(r"\s+", " ", stmt))
        # anything else (e.g. a `rankdir=...` added by an older tidy step) is dropped
    for u, v in edges:
        nodes.setdefault(u, {})
        nodes.setdefault(v, {})

    # Chapter, section and block of every node.
    places = node_places(read_tex(Path(args.tex)))
    block: dict[str, int] = {}
    unplaced = []
    for n in nodes:
        chapter, section = places.get(n, (None, None))
        index = block_of(chapter, section)
        if index is None:
            unplaced.append(f"{n} (chapter {chapter!r}, section {section!r})")
        else:
            block[n] = index
    if unplaced:
        print("error: nodes outside every block; extend BLOCKS in this script:")
        for line in unplaced:
            print("  " + line)
        return 1

    # Hide the steps and let their arrows pass through: every proved lemma and proposition,
    # and every definition whose users are all steps. A definition nothing uses stays, as an
    # isolated node that shows the gap in the `\uses` of the blueprint.
    succ: dict[str, set[str]] = defaultdict(set)
    for u, v in edges:
        succ[u].add(v)
    steps = {n for n, a in nodes.items()
             if n.split(":")[0] in STEPS and a.get("fillcolor") in PROVED}
    hidden = steps | {n for n in nodes
                      if n.startswith("def:") and succ[n] and succ[n] <= steps}

    def targets(n: str) -> set[str]:
        out, stack = set(), list(succ[n])
        while stack:
            v = stack.pop()
            if v in hidden:
                stack.extend(succ[v])
            else:
                out.add(v)
        return out

    kept = sorted((n for n in nodes if n not in hidden), key=lambda n: (block[n], n))
    new_edges = {(u, v) for u in kept for v in targets(u)}
    new_edges = sorted(transitive_reduction(kept, new_edges))
    edge_lines = [f"\t{quote(u)} -> {quote(v)};" for u, v in new_edges]
    opening = [head.strip() + " {"]

    # The main graph: the nodes, then the edges. The page embeds the source in one line, as
    # plastexdepgraph does.
    flat = opening + ["\t" + MAIN_ATTRS] + ["\t" + d + ";" for d in defaults]
    flat += [node_line(n, nodes[n], "\t") for n in kept] + edge_lines + ["}"]

    # The grouped graph: one cluster per block, the edges, the columns.
    grouped = opening + ["\t" + GRAPH_ATTRS] + ["\t" + d + ";" for d in defaults]
    for index, (title, _) in enumerate(BLOCKS):
        members = [n for n in kept if block[n] == index]
        if not members:
            continue
        grouped.append(f"\tsubgraph cluster_{index} {{ label={quote(title)}; {CLUSTER_ATTRS}")
        grouped += [node_line(n, nodes[n], "\t\t") for n in members]
        grouped.append("\t}")
    grouped += edge_lines + column_lines(kept, block, new_edges) + ["}"]

    main_html = finish_page(html, match, "\t".join(flat),
                            SWITCH.format(href=GROUPED_PAGE, text="Grouped by blocks"))
    grouped_html = finish_page(html, match, "\t".join(grouped),
                               SWITCH.format(href=MAIN_PAGE, text="Ungrouped"), GROUPED_TITLE)
    if main_html is None or grouped_html is None:
        print("error: legend, header, fit(true) or interactive() missing -- has the upstream "
              "template changed?")
        return 1
    page.write_text(main_html, encoding="utf-8")
    (Path(args.web) / GROUPED_PAGE).write_text(grouped_html, encoding="utf-8")

    between = sum(1 for u, v in new_edges if block[u] != block[v])
    print(f"nodes: {len(nodes)}, hidden steps: {len(hidden)}, shown: {len(kept)}")
    print(f"edges: {len(edges)} before, {len(new_edges)} after, {between} between blocks")
    for index, (title, _) in enumerate(BLOCKS):
        print(f"  {sum(1 for n in kept if block[n] == index):3d}  {title}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
