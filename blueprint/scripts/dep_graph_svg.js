// Draw the dependency graphs of the blueprint as SVG images, with the pages' own Graphviz.
//
// `dep_graph_document.html` and `dep_graph_grouped.html` hold their graph as DOT source and
// lay it out in the browser with Graphviz 2.44, the hpcc-js WebAssembly build in `js/`. This
// script runs that same build under Node and writes the pictures the pages show as
// `dep_graph.svg` and `dep_graph_grouped.svg`, for viewers that run no JavaScript: GitHub
// displays SVG files in the browser, also in a private repository, where Pages is not
// available. The images are static; the statements of the nodes are on the pages.
//
// The pages draw the graph on a transparent background; the images get a white one, since
// black arrows and labels would vanish on the dark background of GitHub's dark mode.
//
// The bundle is written for browsers, so `document` and `fetch` are supplied here: the
// script URL tells it where the wasm files lie, and fetch reads them from disk.
//
// Run it after `tidy_dep_graph.py` and the recolouring step of the workflow, so that the
// images show the final graphs:
//
//     node blueprint/scripts/dep_graph_svg.js [WEB_DIR]
//
// It fails if a page holds no `renderDot(`...`)`, which is how a change of the upstream
// template would show up.

const fs = require("fs");
const path = require("path");

const web = path.resolve(process.argv[2] || "blueprint/web");
const js = path.join(web, "js");
const GRAPHS = [
  ["dep_graph_document.html", "dep_graph.svg"],
  ["dep_graph_grouped.html", "dep_graph_grouped.svg"],
];

global.document = { currentScript: { src: "file:///js/hpcc.min.js" } };
global.fetch = async (url) => {
  const body = fs.readFileSync(path.join(js, String(url).split("/").pop()));
  return new Response(body, { status: 200, headers: { "Content-Type": "application/wasm" } });
};
const hpcc = require(path.join(js, "hpcc.min.js"));

// The DOT source of a page, on a white background. It stands in a JavaScript template
// literal, so it is read the way the browser reads it.
function dotOf(page) {
  const html = fs.readFileSync(path.join(web, page), "utf8");
  const match = /renderDot\(`([\s\S]*?)`\)/.exec(html);
  if (!match) {
    throw new Error(`no renderDot(\`...\`) in ${page}; has the upstream template changed?`);
  }
  const dot = Function(`"use strict"; return \`${match[1]}\`;`)();
  return dot.replace('bgcolor="transparent"', 'bgcolor="white"');
}

(async () => {
  for (const [page, image] of GRAPHS) {
    const svg = await hpcc.graphviz.layout(dotOf(page), "svg", "dot");
    fs.writeFileSync(path.join(web, image), svg);
    console.log(`${image}: ${svg.length} bytes`);
  }
})().catch((err) => {
  console.error(`error: ${err.message || err}`);
  process.exit(1);
});
