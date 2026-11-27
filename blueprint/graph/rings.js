/*
 * Rings, a view of the advanced style: the foundations in the middle and every ring one layer
 * of dependencies further out, so every arrow points outwards to what follows. The results
 * with Lean code fill a disc in the middle; the results without (planned or informal) lie on
 * rings around it, so what is done sits in the centre and what is to come outside. In each of
 * the two zones every group owns a coloured sector, as wide as its fullest ring needs, with the
 * group's name written large in its background. The placement is that of the Rings view in
 * plain/radial.js (every ring at the smallest radius at which no two boxes touch, `KG.rings`);
 * an arrow is a curve bowed gently outwards, more strongly where that keeps it off a node.
 */
'use strict';

window.AdvancedRings = (() => {

const { state } = KG;
const D = Advanced;
const { TAU, RING_GAP, boxAt, searchRadius, nearestOf, farthestOf, byBarycentre } = KG.rings;
const SECTOR_GAP = 0.03;    // radians between two sectors
const ZONE_MARGIN = 20;     // free space between the boxes of a zone and the rim of its sectors
const ZONE_GAP = 60;        // between the sectors of the inner and of the outer zone
const TITLE_MAX = 260;      // the largest type of a sector's title
const TITLE_MIN = 36;
const TITLE_LINE = 1.15;    // its line height, relative to the type
const titleFont = (px) => `800 ${px}px "Archivo", "Helvetica Neue", Arial, sans-serif`;
const r1 = (x) => Math.round(x * 10) / 10;

/** Results without Lean code (planned or informal) go to the outer zone. */
const isOuter = (v) => !v.n.lean;

/**
 * The layer of each node within its zone: 0 if it uses nothing of the zone, else one more
 * than the deepest node of the zone it uses.
 */
function zoneLayers(zone, deps) {
  const inZone = new Set(zone.map((n) => n.id));
  const memo = new Map();
  const depth = (id, guard = new Set()) => {
    if (memo.has(id)) return memo.get(id);
    guard.add(id);
    let d = 0;
    for (const m of deps.get(id) || []) if (inZone.has(m) && !guard.has(m)) d = Math.max(d, depth(m, guard) + 1);
    guard.delete(id);
    memo.set(id, d);
    return d;
  };
  for (const n of zone) depth(n.id);
  return memo;
}

/** The angle by which a title along the circle at angle `a` is turned, to read left to right. */
function tangentRotation(a) {
  let t = a + Math.PI / 2;
  while (t > Math.PI) t -= TAU;
  while (t <= -Math.PI) t += TAU;
  if (t > Math.PI / 2) t -= Math.PI;
  if (t <= -Math.PI / 2) t += Math.PI;
  return t;
}

/**
 * The sectors of one zone: every group as wide as its fullest ring needs, relative to the
 * others, in the order of the groups; the whole zone turned so that the groups face, on
 * average, the nodes further in that they use (without such nodes the first group starts at
 * the top).
 */
function zoneSectors(zone, groups, layerOf, deps, angle) {
  const need = (n) => n.w + RING_GAP;
  const maxLayer = Math.max(0, ...layerOf.values());
  const cellNeed = (g, L) => zone.filter((n) => n.group === g && layerOf.get(n.id) === L)
    .reduce((s, n) => s + need(n), 0);
  const demand = new Map(groups.map((g) => {
    let d = 1;
    for (let L = 0; L <= maxLayer; L++) d = Math.max(d, cellNeed(g, L));
    return [g, d];
  }));
  const total = [...demand.values()].reduce((s, x) => s + x, 0);
  const avail = TAU - SECTOR_GAP * groups.length;
  const rel = new Map();
  let cursor = 0;
  for (const g of groups) {
    const width = avail * demand.get(g) / total;
    rel.set(g, { from: cursor, width, mid: cursor + width / 2 });
    cursor += width + SECTOR_GAP;
  }
  let sx = 0, sy = 0;
  for (const n of zone) {
    for (const m of deps.get(n.id)) {
      if (!angle.has(m)) continue;
      const d = angle.get(m) - rel.get(n.group).mid;
      sx += Math.cos(d);
      sy += Math.sin(d);
    }
  }
  const start = Math.hypot(sx, sy) > 1e-9 ? Math.atan2(sy, sx) : -Math.PI / 2;
  return new Map(groups.map((g) => {
    const { from, width, mid } = rel.get(g);
    return [g, { from: start + from, width, mid: start + mid }];
  }));
}

/**
 * The name of a group in the background of its sector: along the circle through the middle of
 * the sector, in the largest type (at most TITLE_MAX) at which its lines fit the sector.
 */
function sectorTitle(w) {
  const text = state.groupTitle.get(w.group);
  const pie = !(w.inner > 0);
  const r = pie ? 0.58 * w.r : (w.inner + w.r) / 2;
  const depth = pie ? 0.75 * w.r : 0.8 * (w.r - w.inner);
  const width = Math.max(120, 0.85 * 2 * r * Math.sin(Math.min(w.width, Math.PI) / 2));
  for (let px = TITLE_MAX; px > TITLE_MIN; px = Math.floor(px * 0.92)) {
    const t = KG.wrap(text, width, titleFont(px));
    if (t.width <= width && t.lines.length * TITLE_LINE * px <= depth) return { group: w.group, lines: t.lines, px, r, a: w.mid };
  }
  return { group: w.group, lines: KG.wrap(text, width, titleFont(TITLE_MIN)).lines, px: TITLE_MIN, r, a: w.mid };
}

/**
 * The places on the rings: the inner zone (results with Lean code), then the outer zone
 * (results without), each with rings by layer and a sector for every group of the zone.
 * `deps` maps a node to the nodes it uses.
 */
function placeOnRings(nodes, deps) {
  const zones = [nodes.filter((n) => !isOuter(n)), nodes.filter(isOuter)].filter((z) => z.length);
  const need = (n) => n.w + RING_GAP;
  const angle = new Map();
  const targets = new Map();
  const radii = [];
  const placed = [];
  const wedges = [];
  let prevR = 0;
  let zoneStart = 0;
  zones.forEach((zone, zi) => {
    const layerOf = zoneLayers(zone, deps);
    const maxLayer = Math.max(0, ...layerOf.values());
    const groups = state.data.groups.map((g) => g.id).filter((g) => zone.some((n) => n.group === g));
    const sector = zoneSectors(zone, groups, layerOf, deps, angle);
    const cell = (g, L) => zone.filter((n) => n.group === g && layerOf.get(n.id) === L);
    const cellNeed = (g, L) => cell(g, L).reduce((s, n) => s + need(n), 0);
    const inner = zoneStart > 0 ? zoneStart + ZONE_MARGIN : 0;
    const fits = (b) => nearestOf(b) >= inner;
    const zoneBoxes = [];
    for (let L = 0; L <= maxLayer; L++) {
      const cells = groups.map((g) => [g, byBarycentre(cell(g, L), deps, angle, sector.get(g).from)])
        .filter(([, c]) => c.length);
      if (!cells.length) continue;
      const count = cells.reduce((s, [, c]) => s + c.length, 0);
      const r0 = zi === 0 && L === 0 && count === 1 ? 0
        : Math.max(prevR + 40, inner, ...cells.map(([g]) => cellNeed(g, L) / sector.get(g).width));
      let chosen = new Map();
      const res = searchRadius(r0, (r) => {
        chosen = new Map();
        for (const [g, c] of cells) {
          const arc = r > 0 ? cellNeed(g, L) / r : 0;
          let s = 0;
          for (const n of c) {
            chosen.set(n.id, r > 0 ? sector.get(g).mid - arc / 2 + (s + need(n) / 2) / r : 0);
            s += need(n);
          }
        }
        return cells.flatMap(([, c]) => c.map((n) => boxAt(n, r, chosen.get(n.id))));
      }, placed, fits);
      for (const [, c] of cells) {
        for (const n of c) {
          angle.set(n.id, chosen.get(n.id));
          targets.set(n.id, { r: res.r, a: chosen.get(n.id) });
        }
      }
      placed.push(...res.boxes);
      zoneBoxes.push(...res.boxes);
      if (res.r > 0) radii.push(res.r);
      prevR = res.r;
    }
    const wedgeR = Math.max(0, ...zoneBoxes.map(farthestOf)) + ZONE_MARGIN;
    groups.forEach((g) => wedges.push({ group: g, ...sector.get(g), inner: zoneStart, r: wedgeR }));
    zoneStart = wedgeR + ZONE_GAP;
  });
  return { targets, radii, wedges, captions: wedges.map(sectorTitle) };
}

/** The outline of a sector: a slice of the disc, or the part of the slice beyond `inner`. */
function wedgePath(w) {
  const P = (r, a) => `${r1(r * Math.cos(a))},${r1(r * Math.sin(a))}`;
  const a0 = w.from, a1 = w.from + w.width, large = w.width > Math.PI ? 1 : 0;
  if (!(w.inner > 0)) return `M0,0 L${P(w.r, a0)} A${r1(w.r)},${r1(w.r)} 0 ${large} 1 ${P(w.r, a1)} Z`;
  return `M${P(w.inner, a0)} L${P(w.r, a0)} A${r1(w.r)},${r1(w.r)} 0 ${large} 1 ${P(w.r, a1)} ` +
    `L${P(w.inner, a1)} A${r1(w.inner)},${r1(w.inner)} 0 ${large} 0 ${P(w.inner, a0)} Z`;
}

function backdropMarkup({ radii, wedges, captions }) {
  const out = [];
  for (const w of wedges) {
    const c = KG.groupColor(w.group);
    out.push(`<path class="wedge" d="${wedgePath(w)}" fill="${c}" fill-opacity="0.09"/>`);
  }
  for (const r of radii) out.push(`<circle class="ring" cx="0" cy="0" r="${r1(r)}"/>`);
  for (const t of captions) {
    const x = t.r * Math.cos(t.a), y = t.r * Math.sin(t.a), deg = tangentRotation(t.a) * 180 / Math.PI;
    const spans = t.lines.map((l, i) =>
      `<tspan x="0" y="${r1((i - (t.lines.length - 1) / 2) * TITLE_LINE * t.px + 0.35 * t.px)}">${KG.esc(l)}</tspan>`).join('');
    out.push(`<text class="sector-title" text-anchor="middle" font-size="${t.px}" fill="${KG.groupColor(t.group)}" ` +
      `fill-opacity="0.3" transform="translate(${r1(x)} ${r1(y)}) rotate(${r1(deg)})">${spans}</text>`);
  }
  return out.join('');
}

/** The layout of the view (see Advanced.svg for its shape); `graph` has edges "source uses target". */
async function layout(graph) {
  const recs = D.nodeRecords(graph).map((r) => ({ ...r, group: r.n.group }));
  const deps = new Map(recs.map((r) => [r.id, []]));
  for (const e of graph.edges) if (deps.has(e.source)) deps.get(e.source).push(e.target);
  const placing = placeOnRings(recs, deps);
  const nodes = new Map();
  for (const r of recs) {
    const t = placing.targets.get(r.id);
    nodes.set(r.id, { ...r, x: t.r * Math.cos(t.a), y: t.r * Math.sin(t.a) });
  }
  const all = [...nodes.values()];
  const edges = graph.edges.map((e) => {
    const A = nodes.get(e.target), B = nodes.get(e.source); // the arrow runs from A to B
    const dist = Math.hypot(B.x - A.x, B.y - A.y);
    const mid = { x: (A.x + B.x) / 2, y: (A.y + B.y) / 2 };
    const perp = D.unit(A.y - B.y, B.x - A.x);
    // bowed gently outwards; if that passes a node, more strongly to either side
    const out = perp.x * mid.x + perp.y * mid.y >= 0 ? 1 : -1;
    const curves = [0.1, -0.1, 0.22, -0.22, 0.38, -0.38].map((f) => {
      const o = out * Math.sign(f) * Math.max(24, Math.abs(f) * dist);
      const c = { x: mid.x + perp.x * o, y: mid.y + perp.y * o };
      // the quadratic curve through the control point c, as a cubic piece
      const c1 = { x: A.x + (c.x - A.x) * 2 / 3, y: A.y + (c.y - A.y) * 2 / 3 };
      const c2 = { x: B.x + (c.x - B.x) * 2 / 3, y: B.y + (c.y - B.y) * 2 / 3 };
      const p0 = D.boundary(A, D.unit(c.x - A.x, c.y - A.y));
      const p3 = D.boundary(B, D.unit(c.x - B.x, c.y - B.y));
      return [[p0, c1, c2, p3]];
    });
    const segs = curves.find((S) => D.passesClear(S, A, B, all)) || curves[0];
    return { s: e.target, t: e.source, segs, manual: !!e.manual, example: !!e.example, xf: false };
  });
  const R = Math.max(60, ...placing.wedges.map((w) => w.r), ...all.map((v) => Math.hypot(v.x, v.y) + Math.hypot(v.w, v.h) / 2)) + 20;
  return { x0: -R, y0: -R, w: 2 * R, h: 2 * R, nodes, edges, wedges: placing.wedges, radii: placing.radii,
    backdrop: backdropMarkup(placing), order: (p) => Math.hypot(p.x, p.y) / R };
}

D.boot({
  layout,
  reading: 'The foundations stand in the middle, every ring one layer further out; the results ' +
    'with Lean code fill the inner disc, the planned and informal ones lie around it.',
});

return { layout };

})();
