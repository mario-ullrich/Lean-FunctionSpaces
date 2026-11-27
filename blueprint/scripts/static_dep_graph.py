#!/usr/bin/env python3
"""Let the two leanblueprint graph pages show their precomputed pictures.

``dep_graph_document.html`` and ``dep_graph_grouped.html`` hand their Graphviz source to
d3-graphviz, which lays the graph out in the browser on every visit. With about 800 nodes and
2000 arrows this takes long, and the page also sets every formula of its about 1900 hidden
statements with MathJax before it is usable. ``dep_graph_svg.js`` already draws the same
graphs with the same Graphviz build as ``dep_graph.svg`` and ``dep_graph_grouped.svg``. This
script makes each page load its picture instead:

* the call ``graphviz(...).renderDot(`...`)`` is replaced by loading the SVG into ``#graph``,
  fitted to the window, with zoom and pan by d3 in the zoom range the pages had before;
* d3-graphviz and its Graphviz build are no longer loaded;
* ``interactive()`` of the page then runs as before, so a click on a node opens its statement,
  and the pinch and ctrl+wheel zoom added by ``tidy_dep_graph.py`` applies to the picture;
* MathJax sets no formula at load, only those of a statement when it is opened.

Run it from the project root after ``dep_graph_svg.js``. It fails if a page lacks one of the
pieces it replaces, which is how a change of the upstream template would show up.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

WEB = Path(sys.argv[1] if len(sys.argv) > 1 else "blueprint/web")
PAGES = [("dep_graph_document.html", "dep_graph.svg"),
         ("dep_graph_grouped.html", "dep_graph_grouped.svg")]

RENDER_RE = re.compile(r'graphContainer\.graphviz\(\{useWorker: true\}\)[\s\S]*?'
                       r'\.on\("end", interactive\);')
DROP = ['<script src="js/hpcc.min.js"></script>', '<script src="js/d3-graphviz.js"></script>']
MATHJAX = ('<script type="text/javascript" '
           'src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js">')
MATHJAX_CONFIG = "<script>window.MathJax = {startup: {typeset: false}};</script>\n"

LOAD = """fetch("{svg}").then(function (r) {{ return r.text(); }}).then(function (text) {{
    var box = graphContainer.node();
    box.innerHTML = text.slice(text.indexOf("<svg"));
    var svg = graphContainer.select("svg").attr("width", width).attr("height", height);
    var g = svg.select("g.graph");
    var base = g.attr("transform");
    var zoom = d3.zoom().scaleExtent([0.1, 200]).on("zoom", function () {{
        g.attr("transform", d3.event.transform + " " + base);
    }});
    svg.call(zoom);
    box.__graphviz__ = {{zoomBehavior: function () {{ return zoom; }}}};
    interactive();
    d3.selectAll(".node").on("click.math", function () {{
        var title = d3.select(this).selectAll("title").text().trim();
        var statement = document.getElementById(title + "_modal");
        if (statement && window.MathJax && MathJax.typesetPromise) {{
            MathJax.typesetPromise([statement]);
        }}
    }});
}});"""


def convert(html: str, svg: str) -> str | None:
    match = RENDER_RE.search(html)
    if match is None or MATHJAX not in html or any(tag not in html for tag in DROP):
        return None
    html = html[:match.start()] + LOAD.format(svg=svg) + html[match.end():]
    for tag in DROP:
        html = html.replace(tag, "", 1)
    return html.replace(MATHJAX, MATHJAX_CONFIG + MATHJAX, 1)


def main() -> int:
    for page, svg in PAGES:
        path = WEB / page
        if not (WEB / svg).exists():
            print(f"error: {svg} is missing; run dep_graph_svg.js first")
            return 1
        html = convert(path.read_text(encoding="utf-8"), svg)
        if html is None:
            print(f"error: {page} lacks the renderDot call, the MathJax script or the "
                  "d3-graphviz scripts -- has the upstream template changed?")
            return 1
        path.write_text(html, encoding="utf-8")
        print(f"{page}: shows {svg}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
