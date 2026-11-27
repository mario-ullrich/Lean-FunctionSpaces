/*
 * Flow, a view of the advanced style: the foundations on the left, the results on the right.
 * The places from left to right come from ELK's layered layout; "Grouped" stacks the groups as
 * bands, one below the other, over the same places, so that every arrow runs to the right in
 * both modes. An arrow is a smooth curve, level where it leaves and enters a node: one curve
 * from node to node if that passes no third node, else ELK's route without its vertical steps,
 * else ELK's route; in Grouped, one curve or a detour through the gap between two bands.
 */
'use strict';

window.AdvancedFlow = (() => {

const { state } = KG;
const D = Advanced;

const ELK_OPTIONS = {
  'elk.algorithm': 'layered',
  'elk.direction': 'RIGHT', // from what is used to what uses it: foundations on the left
  'elk.edgeRouting': 'POLYLINE',
  'elk.layered.spacing.nodeNodeBetweenLayers': '64',
  'elk.spacing.nodeNode': '16',
  'elk.spacing.edgeNode': '12',
  'elk.spacing.edgeEdge': '8',
  'elk.layered.spacing.edgeNodeBetweenLayers': '16',
  'elk.layered.spacing.edgeEdgeBetweenLayers': '8',
  'elk.layered.nodePlacement.strategy': 'NETWORK_SIMPLEX',
  'elk.layered.considerModelOrder.strategy': 'NODES_AND_EDGES',
  'elk.padding': '[top=20,left=20,bottom=20,right=20]',
};
const BAND_TOP = 46;   // room for the title of a band
const BAND_PAD = 16;
const BAND_GAP = 24;
const SPACE_Y = 14;

let elk = null;

/** Cubic pieces through the route points, level at each of them. */
function levelPieces(pts) {
  const segs = [];
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1], b = pts[i], h = Math.max(0, (b.x - a.x) / 2);
    segs.push([a, { x: a.x + h, y: a.y }, { x: b.x - h, y: b.y }, b]);
  }
  return segs;
}

/** The route without its vertical steps: both ends of every vertical piece between bends go. */
function withoutSteps(pts) {
  const P = [pts[0]];
  for (let i = 1; i < pts.length - 1; i++) {
    const next = pts[i + 1];
    if (i + 1 < pts.length - 1 && Math.abs(next.x - pts[i].x) < 3) { i++; continue; }
    if (Math.abs(pts[i].x - P[P.length - 1].x) < 3) continue;
    P.push(pts[i]);
  }
  P.push(pts[pts.length - 1]);
  return P;
}

/** Where an arrow leaves (side +1) or enters (side -1) a node: level with `y`, on its border. */
function onSide(v, y, side) {
  const hb = v.h / 2;
  const dy = Math.max(-0.8 * hb, Math.min(0.8 * hb, y - v.y));
  if (v.shape === 'box') return { x: v.x + side * v.w / 2, y: v.y + dy };
  return { x: v.x + side * (v.w / 2) * Math.sqrt(1 - (dy / hb) ** 2), y: v.y + dy };
}

/**
 * Stacks the groups as bands, one below the other, each across the whole width. The nodes keep
 * their places from left to right and their order from top to bottom; each moves up in its
 * band as far as the nodes above it allow.
 */
function bands(nodes, width) {
  const clusters = [];
  let top = 20;
  for (const g of state.data.groups) {
    const members = [...nodes.values()].filter((v) => v.n.group === g.id).sort((a, b) => a.y - b.y);
    if (!members.length) continue;
    const placed = [];
    for (const v of members) {
      let y = top + BAND_TOP + v.h / 2;
      for (let moved = true; moved;) {
        moved = false;
        for (const p of placed) {
          const side = Math.abs(p.x - v.x) < (p.w + v.w) / 2 + 12;
          // (the tolerance keeps rounding from moving a node to the same place again)
          if (side && Math.abs(p.y - y) < (p.h + v.h) / 2 + SPACE_Y - 0.01) {
            y = p.y + (p.h + v.h) / 2 + SPACE_Y;
            moved = true;
          }
        }
      }
      v.y = y;
      placed.push(v);
    }
    const bottom = Math.max(...placed.map((p) => p.y + p.h / 2)) + BAND_PAD;
    clusters.push({ id: g.id, title: g.title, x: 6, y: top, w: width - 12, h: bottom - top, colour: KG.groupColor(g.id) });
    top = bottom + BAND_GAP;
  }
  return { clusters, height: top - BAND_GAP + 20 };
}

function bandMarkup(clusters) {
  const r1 = (x) => Math.round(x * 10) / 10;
  return clusters.map((c) => `<g class="lane" data-group="${KG.esc(c.id)}">` +
    `<rect x="${r1(c.x)}" y="${r1(c.y)}" width="${r1(c.w)}" height="${r1(c.h)}" rx="10" ` +
    `fill="${c.colour}" fill-opacity="0.07" stroke="${c.colour}" stroke-opacity="0.6"/>` +
    `<rect x="${r1(c.x + 16)}" y="${r1(c.y + 14)}" width="5" height="18" fill="${c.colour}"/>` +
    `<text class="ft" x="${r1(c.x + 28)}" y="${r1(c.y + 28)}">${KG.esc(c.title)}</text></g>`).join('');
}

/** The layout of the view (see Advanced.svg for its shape); `graph` has edges "source uses target". */
async function layout(graph, { grouped = false } = {}) {
  if (!elk) elk = new ELK();
  const recs = new Map(D.nodeRecords(graph).map((r) => [r.id, r]));
  const res = await elk.layout({
    id: 'root',
    layoutOptions: ELK_OPTIONS,
    children: [...recs.values()].map((r) => ({ id: r.id, width: r.w, height: r.h })),
    edges: graph.edges.map((e, i) => ({ id: 'e' + i, sources: [e.target], targets: [e.source] })),
  });
  const nodes = new Map();
  for (const c of res.children) {
    const v = { ...recs.get(c.id), x: c.x + c.width / 2, y: c.y + c.height / 2 };
    v.flatY = v.y;
    nodes.set(c.id, v);
  }
  const routes = res.edges.map((re, i) => {
    const sec = re.sections && re.sections[0];
    if (sec) return [sec.startPoint, ...(sec.bendPoints || []), sec.endPoint].map((p) => ({ x: p.x, y: p.y }));
    const e = graph.edges[i], A = nodes.get(e.target), B = nodes.get(e.source);
    return [{ x: A.x, y: A.y }, { x: B.x, y: B.y }];
  });
  let clusters = [], height = res.height;
  if (grouped) ({ clusters, height } = bands(nodes, res.width));
  // horizontal lanes free of nodes: the gaps between the bands, above and below them
  const lanes = grouped ? [clusters[0].y - BAND_GAP / 2, ...clusters.map((c) => c.y + c.h + BAND_GAP / 2)] : [];
  const all = [...nodes.values()];
  const edges = graph.edges.map((e, i) => {
    const A = nodes.get(e.target), B = nodes.get(e.source); // the arrow runs from A to B
    const flat = routes[i];
    // leave and enter at the height ELK chose relative to the centres
    const P = onSide(A, A.y + flat[0].y - A.flatY, 1);
    const Q = onSide(B, B.y + flat[flat.length - 1].y - B.flatY, -1);
    let candidates;
    if (grouped) {
      const d = Math.min(70, (Q.x - P.x) / 4), mid = (P.y + Q.y) / 2;
      candidates = [[P, Q], ...lanes.slice().sort((a, b) => Math.abs(a - mid) - Math.abs(b - mid))
        .map((y) => [P, { x: P.x + d, y }, { x: Q.x - d, y }, Q])];
    } else {
      const route = [P, ...flat.slice(1, -1), Q];
      candidates = [[P, Q], withoutSteps(route), route];
    }
    const best = candidates.find((C) => D.passesClear(levelPieces(C), A, B, all)) ||
      (grouped ? candidates[0] : candidates[candidates.length - 1]);
    return { s: e.target, t: e.source, segs: levelPieces(best), manual: !!e.manual, example: !!e.example,
      xf: grouped && A.n.group !== B.n.group };
  });
  return { x0: 0, y0: 0, w: res.width, h: height, nodes, edges, clusters, backdrop: bandMarkup(clusters),
    order: (p) => p.x / (res.width || 1) };
}

D.boot({
  layout,
  reading: 'The foundations stand on the left, the results on the right.',
  using: ' <i>Grouped</i> gives every group a band of its own.',
});

return { layout };

})();
