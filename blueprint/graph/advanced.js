/*
 * The advanced style: a second look of the knowledge graph, separate from the views in plain/.
 * A deep ink masthead counts the nodes by where they stand in Lean; below it lies a sheet
 * with a drawing grid, the drawing (or a list) on the left and the sheet of the open node on the right.
 * It has two views: Flow (flow.js), the foundations on the left and the results on the right,
 * and Rings (rings.js), the foundations in the middle and every ring one layer further out.
 *
 * This file holds what both views share: the nodes and arrows to draw, the shapes, the SVG
 * drawing, the camera, the chains of a node, the list, the panel and the controls. A view only
 * lays the graph out. The data layer is that of plain/common.js (KG): loading, profiles, the
 * visible graph, the content of the panel, the search and the address.
 *
 * A left click on a node traces its chains, what it needs in blue and what needs it in red; a
 * right click opens another node in the panel while the chains stay. "Nodes" switches between
 * the main nodes and all nodes (with the details of level 2); "Arrows" between the arrows that
 * no longer path implies and all arrows between the nodes drawn.
 */
'use strict';

window.Advanced = (() => {

const { state, $ } = KG;

// ---------------------------------------------------------------- nodes and arrows

const LABEL_PX = 12;
const LABEL_LINE = 14.5;
const LABEL_WIDTH = 150;
const LABEL_FAMILY = '"Archivo", "Helvetica Neue", Arial, sans-serif';
const ARROW = 8;

const labelFont = (n) => `${KG.levelOf(n) === 2 ? 'italic ' : ''}500 ${LABEL_PX}px ${LABEL_FAMILY}`;

/** Where a node stands in Lean, as the masthead counts it. */
function standing(n) {
  if (n.status === 'sorry') return 'sorry';
  if (n.lean) return /^Mathlib(\.|$)/.test(n.lean.module || '') ? 'mathlib' : 'lean';
  return n.status === 'planned' ? 'planned' : 'informal';
}

/** The standings in the order of the masthead, with their names for this graph. */
function standings() {
  const src = ((state.data && state.data.meta.source && state.data.meta.source.name) || 'the project')
    .replace(/^Lean-/, '');
  return [
    { key: 'mathlib', label: 'In Mathlib' },
    { key: 'lean', label: `In ${src}` },
    { key: 'sorry', label: 'With sorry' },
    { key: 'planned', label: 'Planned' },
    { key: 'informal', label: 'Informal' },
  ];
}
const standingLabel = (k) => (standings().find((s) => s.key === k) || { label: k }).label;

/** Label lines and size of a node: an ellipse around the label, a box for a definition. */
function geometry(n) {
  const { lines, width } = KG.wrap(KG.nodeLabel(n), LABEL_WIDTH, labelFont(n));
  const u = width / 2, t = (lines.length * LABEL_LINE) / 2;
  const box = n.kind === 'definition';
  // an ellipse with half axes a, b holds the label block u × t when (u/a)² + (t/b)² ≤ 1
  const a = box ? u + 12 : u * 1.22 + 12;
  const b = box ? t + 9 : t * 1.32 + 9;
  return { lines, shape: box ? 'box' : 'ellipse', w: Math.max(2 * a, 64), h: Math.max(2 * b, 32) };
}

/**
 * Every arrow between the given nodes, through hidden nodes where the proof passes them, in
 * data direction ("source uses target"); `KG.visibleGraph` keeps only those that no longer
 * path implies.
 */
function everyArrow(nodes) {
  const shown = new Set(nodes.map((n) => n.id));
  const found = new Map();
  for (const a of shown) {
    const stack = (state.out.get(a) || []).map((e) => [e, e.kind === 'manual']);
    const seen = new Set();
    while (stack.length) {
      const [e, manual] = stack.pop();
      const b = e.target;
      if (shown.has(b)) {
        const key = a + '\u0001' + b;
        const old = found.get(key);
        if (!old) found.set(key, { source: a, target: b, manual });
        else if (!manual) old.manual = false;
        continue;
      }
      if (seen.has(b)) continue;
      seen.add(b);
      for (const f of state.out.get(b) || []) stack.push([f, manual || f.kind === 'manual']);
    }
  }
  return [...found.values()].sort((x, y) => (x.source + x.target).localeCompare(y.source + y.target));
}

/**
 * The nodes and arrows to draw: the main nodes or all nodes, the reduced or all arrows. With
 * all nodes, the examples of a result stand next to it, joined to it by a dotted arrow.
 */
function graph({ allNodes = false, allArrows = false } = {}) {
  state.showDetails = allNodes;
  const view = KG.visibleGraph();
  if (allArrows) view.edges = everyArrow(view.nodes);
  if (!allNodes) return view;
  const drawn = new Set(view.nodes.map((n) => n.id));
  const add = (parent) => {
    for (const ex of KG.examplesOf(parent.id)) {
      if (drawn.has(ex.id)) continue;
      drawn.add(ex.id);
      view.nodes.push({ ...ex, group: parent.group });
      view.edges.push({ source: ex.id, target: parent.id, manual: false, example: true });
      add(ex);
    }
  };
  for (const n of [...view.nodes]) add(n);
  return view;
}

// ---------------------------------------------------------------- curves

const unit = (dx, dy) => { const l = Math.hypot(dx, dy) || 1; return { x: dx / l, y: dy / l }; };

/** Is the point inside the node's shape, `margin` units in from its border? */
function inShape(v, p, margin = 3) {
  const dx = p.x - v.x, dy = p.y - v.y, a = v.w / 2 - margin, b = v.h / 2 - margin;
  if (v.shape === 'box') return Math.abs(dx) < a && Math.abs(dy) < b;
  return (dx * dx) / (a * a) + (dy * dy) / (b * b) < 1;
}

/** The point on the node's border in the direction `dir` (a unit vector) from its centre. */
function boundary(v, dir) {
  const a = v.w / 2, b = v.h / 2;
  const t = v.shape === 'box'
    ? Math.min(dir.x ? a / Math.abs(dir.x) : Infinity, dir.y ? b / Math.abs(dir.y) : Infinity)
    : 1 / Math.sqrt((dir.x / a) ** 2 + (dir.y / b) ** 2);
  return { x: v.x + dir.x * t, y: v.y + dir.y * t };
}

/** Points along a curve given as cubic pieces [p0, c1, c2, p3], 19 inside each piece. */
function samples(segs) {
  const out = [];
  for (const [a, c1, c2, b] of segs) {
    for (let k = 1; k < 20; k++) {
      const t = k / 20, s = 1 - t;
      out.push({ x: s * s * s * a.x + 3 * s * s * t * c1.x + 3 * s * t * t * c2.x + t * t * t * b.x,
        y: s * s * s * a.y + 3 * s * s * t * c1.y + 3 * s * t * t * c2.y + t * t * t * b.y });
    }
  }
  return out;
}

/** Does the curve from A to B pass no third node? */
function passesClear(segs, A, B, nodes) {
  return !samples(segs).some((s) => nodes.some((v) => v !== A && v !== B && inShape(v, s)));
}

// ---------------------------------------------------------------- drawing

const r1 = (x) => Math.round(x * 10) / 10;
const pt = (p) => `${r1(p.x)},${r1(p.y)}`;

/** The path of an arrow, shortened at its end by the arrow head, and the head. */
function arrowMarkup(segs) {
  const S = segs.map((s) => s.slice());
  const last = S[S.length - 1];
  const [p0, , c2, p3] = last;
  const u = Math.hypot(p3.x - c2.x, p3.y - c2.y) > 0.5 ? unit(p3.x - c2.x, p3.y - c2.y) : unit(p3.x - p0.x, p3.y - p0.y);
  const base = { x: p3.x - u.x * ARROW, y: p3.y - u.y * ARROW };
  last[2] = { x: c2.x - u.x * ARROW, y: c2.y - u.y * ARROW };
  last[3] = base;
  const d = `M${pt(S[0][0])}` + S.map(([, c1, cc2, b]) => ` C${pt(c1)} ${pt(cc2)} ${pt(b)}`).join('');
  const w = { x: -u.y * 3.6, y: u.x * 3.6 };
  const head = `${pt(p3)} ${pt({ x: base.x + w.x, y: base.y + w.y })} ${pt({ x: base.x - w.x, y: base.y - w.y })}`;
  return { d, head };
}

function shapeMarkup(v, cls) {
  if (v.shape === 'box') {
    return `<rect class="${cls}" x="${r1(v.x - v.w / 2)}" y="${r1(v.y - v.h / 2)}" width="${r1(v.w)}" height="${r1(v.h)}" rx="5"/>`;
  }
  return `<ellipse class="${cls}" cx="${r1(v.x)}" cy="${r1(v.y)}" rx="${r1(v.w / 2)}" ry="${r1(v.h / 2)}"/>`;
}

/** The style of a picture without the page: the light colours of the page. */
const PICTURE_STYLE = `
.bg { fill: #ffffff; }
.lane .ft { font: 700 15px "JetBrains Mono", Consolas, monospace; fill: #2c3144; }
.ring { fill: none; stroke: #c8cfdd; stroke-width: 1; }
.sector-title { font-family: Archivo, "Segoe UI", "Helvetica Neue", Arial, sans-serif; font-weight: 800; }
.edge path { fill: none; stroke: #4c5570; stroke-width: 1.1; }
.edge polygon { fill: #4c5570; }
.edge.manual path { stroke-dasharray: 5 4; }
.edge.example path { stroke-dasharray: 1.5 3; }
.edge.xf { opacity: 0.35; }
.node .halo { fill: none; stroke: none; }
.node .shape { stroke: #2c3144; stroke-width: 1.4; }
.node.imp1 .shape { stroke-width: 1; }
.node.imp3 .shape { stroke-width: 2.6; }
.st-mathlib .shape { fill: #8eddbb; }
.st-lean .shape { fill: #bfebd5; }
.st-sorry .shape { fill: #ffe9a8; stroke: #b98a14; }
.st-planned .shape { fill: #eef1f7; stroke-dasharray: 5 3; }
.st-informal .shape { fill: #ffffff; stroke-dasharray: 2 3; }
.node text { font: 500 ${LABEL_PX}px Archivo, "Segoe UI", "Helvetica Neue", Arial, sans-serif; fill: #0b0d14; }
.node.lvl2 text { font-style: italic; }
`;

/**
 * The drawing as SVG markup: the backdrop of the view, the arrows, the nodes. `lay` is
 * { x0, y0, w, h, backdrop, nodes: Map id → { id, n, x, y, w, h, shape, lines }, edges:
 * [{ s, t, segs, manual, example, xf }] }, an arrow running from s to t. With `standalone` a
 * complete SVG document with its own style, for a README; `width` is its displayed width.
 */
function svg(lay, { standalone = false, width = 1000 } = {}) {
  const out = [];
  if (standalone) {
    const pad = 8, X = lay.x0 - pad, Y = lay.y0 - pad, W = lay.w + 2 * pad, H = lay.h + 2 * pad;
    out.push(`<svg xmlns="http://www.w3.org/2000/svg" viewBox="${r1(X)} ${r1(Y)} ${r1(W)} ${r1(H)}" ` +
      `width="${width}" height="${Math.round(width * H / W)}"><style>${PICTURE_STYLE}</style>` +
      `<rect class="bg" x="${r1(X)}" y="${r1(Y)}" width="${r1(W)}" height="${r1(H)}"/>`);
  }
  out.push(`<g class="backdrop">${lay.backdrop || ''}</g><g class="edges">`);
  for (const e of lay.edges) {
    const { d, head } = arrowMarkup(e.segs);
    const cls = ['edge', e.manual && 'manual', e.example && 'example', e.xf && 'xf'].filter(Boolean).join(' ');
    out.push(`<g class="${cls}" data-s="${KG.esc(e.s)}" data-t="${KG.esc(e.t)}"><path d="${d}"/><polygon points="${head}"/></g>`);
  }
  out.push('</g><g class="nodes">');
  for (const v of lay.nodes.values()) {
    const n = v.n;
    const cls = ['node', `st-${standing(n)}`, `imp${KG.importance(n)}`, KG.levelOf(n) === 2 && 'lvl2', `k-${n.kind}`]
      .filter(Boolean).join(' ');
    const y0 = v.y - ((v.lines.length - 1) * LABEL_LINE) / 2 + LABEL_PX * 0.36;
    const spans = v.lines.map((l, i) => `<tspan x="${r1(v.x)}" y="${r1(y0 + i * LABEL_LINE)}">${KG.esc(l)}</tspan>`).join('');
    const attrs = standalone ? '' : ` data-id="${KG.esc(n.id)}" tabindex="0" role="button" aria-label="${KG.esc(n.title)}"`;
    out.push(`<g class="${cls}"${attrs}>${shapeMarkup(v, 'halo')}${shapeMarkup(v, 'shape')}` +
      `<text text-anchor="middle">${spans}</text></g>`);
  }
  out.push('</g>');
  if (standalone) out.push('</svg>');
  return out.join('');
}

/** Node records for a layout: label, shape and size of every node of the view. */
function nodeRecords(view) {
  return view.nodes.map((n) => ({ id: n.id, n, ...geometry(n) }));
}

// ---------------------------------------------------------------- the page

const STORE = 'kg-advanced';
const ui = {
  view: null,                 // { layout, grouping } of the page
  mode: 'graph', grouped: false, allNodes: false, allArrows: false,
  sel: null, peek: null, usedPeek: false,
  flt: null, hoverFlt: null, hover: null,
  lay: null, uses: new Map(), usedBy: new Map(),
  cam: null, touched: false, auto: false, anim: 0,
};
const REDUCED_MOTION = KG.REDUCED_MOTION;
const CAN_RIGHT_CLICK = !window.matchMedia || matchMedia('(hover: hover)').matches;
const MOUSE_L = '<svg class="mi" viewBox="0 0 12 16" width="12" height="16" aria-hidden="true"><rect x=".75" y=".75" width="10.5" height="14.5" rx="5" fill="none" stroke="currentColor" stroke-width="1.5"/><path d="M6 1A5 5 0 0 0 1 6V7H6Z" fill="currentColor"/><path d="M6 1V7" stroke="currentColor"/></svg>';
const MOUSE_R = '<svg class="mi" viewBox="0 0 12 16" width="12" height="16" aria-hidden="true"><rect x=".75" y=".75" width="10.5" height="14.5" rx="5" fill="none" stroke="currentColor" stroke-width="1.5"/><path d="M6 1A5 5 0 0 1 11 6V7H6Z" fill="currentColor"/><path d="M6 1V7" stroke="currentColor"/></svg>';

function loadSettings() {
  try {
    const s = JSON.parse(localStorage.getItem(STORE) || '{}');
    ui.mode = s.mode === 'list' ? 'list' : 'graph';
    ui.grouped = !!s.grouped;
    ui.allNodes = !!s.allNodes;
    ui.allArrows = !!s.allArrows;
  } catch (err) { /* the settings are only a convenience */ }
}
function saveSettings() {
  try {
    localStorage.setItem(STORE, JSON.stringify({ mode: ui.mode, grouped: ui.grouped, allNodes: ui.allNodes, allArrows: ui.allArrows }));
  } catch (err) { /* the settings are only a convenience */ }
}

const svgEl = () => $('drawing');
const stage = () => $('stage');

/** Everything reachable from `id` along `map` (uses or used by), in the drawing. */
function closure(id, map) {
  const seen = new Set();
  const todo = [...(map.get(id) || [])];
  while (todo.length) {
    const x = todo.pop();
    if (seen.has(x)) continue;
    seen.add(x);
    todo.push(...(map.get(x) || []));
  }
  return seen;
}

// ---------------------------------------------------------------- camera

function area() {
  const r = stage().getBoundingClientRect();
  return { W: r.width || 1, H: Math.max(1, r.height - 40), r };
}
function applyCam() {
  const a = area(), c = ui.cam;
  svgEl().setAttribute('viewBox', `${c.x} ${c.y} ${a.W / c.k} ${a.H / c.k}`);
  let cell = 40;
  while (cell * c.k < 14) cell *= 2;
  const st = stage().style;
  st.setProperty('--gs', `${cell * c.k}px`);
  st.setProperty('--gx', `${-c.x * c.k}px`);
  st.setProperty('--gy', `${-c.y * c.k}px`);
}
function fitTarget() {
  const a = area(), L = ui.lay;
  const k = Math.min(a.W / L.w, a.H / L.h) * 0.97;
  return { k, x: L.x0 + (L.w - a.W / k) / 2, y: L.y0 + (L.h - a.H / k) / 2 };
}
function fit() {
  const t = fitTarget();
  ui.cam = { ...t, min: t.k * 0.7, max: Math.max(t.k * 30, 6) };
  ui.touched = false;
  ui.auto = false;
  applyCam();
}
function moveTo(t) {
  cancelAnimationFrame(ui.anim);
  if (REDUCED_MOTION || ui.mode !== 'graph') { Object.assign(ui.cam, t); applyCam(); return; }
  const s = { k: ui.cam.k, x: ui.cam.x, y: ui.cam.y }, t0 = performance.now(), T = 260;
  const step = (now) => {
    const p = Math.min(1, (now - t0) / T), e = p * p * (3 - 2 * p);
    ui.cam.k = Math.exp(Math.log(s.k) * (1 - e) + Math.log(t.k) * e);
    ui.cam.x = s.x + (t.x - s.x) * e;
    ui.cam.y = s.y + (t.y - s.y) * e;
    applyCam();
    if (p < 1) ui.anim = requestAnimationFrame(step);
  };
  ui.anim = requestAnimationFrame(step);
}
function zoomAt(px, py, f) {
  const c = ui.cam, k = Math.min(c.max, Math.max(c.min, c.k * f));
  cancelAnimationFrame(ui.anim);
  const sx = c.x + px / c.k, sy = c.y + py / c.k;
  c.k = k; c.x = sx - px / k; c.y = sy - py / k;
  ui.touched = true; ui.auto = false;
  applyCam();
}
function pan(dx, dy) {
  const c = ui.cam;
  cancelAnimationFrame(ui.anim);
  c.x -= dx / c.k; c.y -= dy / c.k;
  ui.touched = true; ui.auto = false;
  applyCam();
}
/** Brings the node and its direct neighbours into view, close enough to read. */
function frame(id) {
  if (ui.mode !== 'graph' || !ui.cam || !ui.lay.nodes.has(id)) return;
  const ids = [id, ...(ui.uses.get(id) || []), ...(ui.usedBy.get(id) || [])];
  const vs = ids.map((x) => ui.lay.nodes.get(x)).filter(Boolean);
  const x0 = Math.min(...vs.map((v) => v.x - v.w / 2)) - 40, x1 = Math.max(...vs.map((v) => v.x + v.w / 2)) + 40;
  const y0 = Math.min(...vs.map((v) => v.y - v.h / 2)) - 30, y1 = Math.max(...vs.map((v) => v.y + v.h / 2)) + 30;
  const a = area(), base = fitTarget().k;
  const k = Math.max(base, Math.min(Math.min(a.W / (x1 - x0), a.H / (y1 - y0)) * 0.96, 1.6));
  ui.touched = true; ui.auto = true;
  moveTo({ k, x: (x0 + x1) / 2 - a.W / k / 2, y: (y0 + y1) / 2 - a.H / k / 2 });
}

/** The arrows draw themselves once on load, from the foundations towards the results. */
function intro() {
  if (REDUCED_MOTION || ui.sel || !Element.prototype.animate) return;
  const k = ui.cam.k, order = ui.lay.order || ((p) => (p.x - ui.lay.x0) / ui.lay.w);
  svgEl().querySelectorAll('g.edge').forEach((g) => {
    const p = g.querySelector('path'), head = g.querySelector('polygon');
    const L = p.getTotalLength() * k + 1, delay = Math.max(0, Math.min(1, order(p.getPointAtLength(0)))) * 850;
    p.style.strokeDasharray = `${L} ${L}`;
    const done = () => { p.style.strokeDasharray = ''; };
    p.animate([{ strokeDashoffset: L }, { strokeDashoffset: 0 }], { duration: 560, delay, easing: 'ease-out', fill: 'backwards' })
      .finished.then(done, done);
    if (head) head.animate([{ opacity: 0 }, { opacity: 1 }], { duration: 160, delay: delay + 460, fill: 'backwards' });
  });
}

// ---------------------------------------------------------------- state of the drawing

/** Lays out and draws the graph for the current settings; keeps the camera if it was moved. */
async function rebuild() {
  state.selected = ui.sel;
  const view = graph({ allNodes: ui.allNodes, allArrows: ui.allArrows });
  ui.lay = await ui.view.layout(view, { grouped: ui.grouped });
  ui.uses = new Map([...ui.lay.nodes.keys()].map((id) => [id, []]));
  ui.usedBy = new Map([...ui.lay.nodes.keys()].map((id) => [id, []]));
  for (const e of ui.lay.edges) {
    if (e.example) continue;
    ui.uses.get(e.t).push(e.s);
    ui.usedBy.get(e.s).push(e.t);
  }
  svgEl().innerHTML = svg(ui.lay);
  // the counts on the switches: all nodes of the profile, all arrows between the nodes drawn
  const every = graph({ allNodes: true });
  state.showDetails = ui.allNodes;
  $('n-all').textContent = `All ${every.nodes.length}`;
  $('a-all').textContent = `All ${ui.allArrows ? view.edges.length : everyArrow(view.nodes).length}`;
  masthead();
  if (!ui.cam || !ui.touched) fit(); else applyCam();
  paint();
  renderList();
}

/** The counts of the masthead, for the nodes drawn now. */
function masthead() {
  const ns = [...ui.lay.nodes.values()].map((v) => v.n);
  const count = new Map(standings().map((s) => [s.key, 0]));
  for (const n of ns) count.set(standing(n), count.get(standing(n)) + 1);
  const inLean = ns.filter((n) => n.lean).length;
  $('state-h').innerHTML = `<b>${inLean} of ${ns.length}</b> in Lean`;
  const present = standings().filter((s) => count.get(s.key));
  $('bar').innerHTML = present.map((s) =>
    `<button type="button" class="sb sb-${s.key}" style="flex:${count.get(s.key)} 1 0" data-f="${s.key}" ` +
    `data-label="${KG.esc(s.label)}" aria-label="${KG.esc(s.label)}: ${count.get(s.key)} nodes"></button>`).join('');
  $('keys').innerHTML = present.map((s) =>
    `<button type="button" class="key" data-f="${s.key}" data-label="${KG.esc(s.label)}">` +
    `<i class="sb-${s.key}"></i><b>${count.get(s.key)}</b> ${KG.esc(s.label)}</button>`).join('');
}

function markFilters() {
  document.querySelectorAll('[data-f]').forEach((el) => {
    el.classList.toggle('on', el.dataset.f === ui.flt);
    el.classList.toggle('hv', el.dataset.f === ui.hoverFlt);
  });
}

/** Marks the chains of the open node, or the nodes of the standing pointed at. */
function paint() {
  const f = ui.hoverFlt || ui.flt;
  const sel = ui.hoverFlt ? null : ui.sel;
  const drawn = sel && ui.lay.nodes.has(sel);
  const up = drawn ? closure(sel, ui.uses) : null, down = drawn ? closure(sel, ui.usedBy) : null;
  const peeked = drawn ? ui.peek : null;
  const lit = (id) => (drawn ? id === sel || up.has(id) || down.has(id) : !f || standing(ui.lay.nodes.get(id).n) === f);
  svgEl().querySelectorAll('g.node').forEach((g) => {
    const id = g.dataset.id;
    g.classList.toggle('dim', !lit(id) && id !== peeked);
    g.classList.toggle('sel', id === sel);
    g.classList.toggle('peek', id === peeked);
  });
  svgEl().querySelectorAll('g.edge').forEach((g) => {
    const a = g.dataset.s, b = g.dataset.t;
    const isUp = !!drawn && (b === sel || up.has(b)) && up.has(a);
    const isDown = !!drawn && (a === sel || down.has(a)) && down.has(b);
    g.classList.toggle('up', isUp);
    g.classList.toggle('down', isDown);
    g.classList.toggle('dim', drawn ? !(isUp || isDown) : !!f && !(lit(a) && lit(b)));
  });
  $('mousekey').classList.toggle('armed', !!ui.sel && !ui.usedPeek);
  markFilters();
  showHint();
}

function showHint() {
  let msg = '';
  const f = ui.hoverFlt || ui.flt;
  if (ui.hover && ui.lay.nodes.has(ui.hover)) {
    const n = ui.lay.nodes.get(ui.hover).n;
    msg = `${n.title} · ${n.kind} · ${standingLabel(standing(n))}`;
  } else if (f && (ui.hoverFlt || !ui.sel)) {
    const k = [...ui.lay.nodes.values()].filter((v) => standing(v.n) === f).length;
    msg = `${standingLabel(f)}: ${k} node${k === 1 ? '' : 's'}`;
  } else if (ui.sel && !ui.peek && !ui.usedPeek && CAN_RIGHT_CLICK && ui.mode === 'graph') {
    msg = 'Right-click another node to read it and keep these arrows.';
  }
  const el = $('hint');
  el.textContent = msg;
  el.hidden = !msg;
}

// ---------------------------------------------------------------- list

function swatch(n) {
  return `<i class="sw st-${standing(n)}${n.kind === 'definition' ? ' box' : ''}"></i>`;
}

function renderList() {
  if (ui.mode !== 'list') return;
  const f = ui.flt;
  const all = [...ui.lay.nodes.values()].map((v) => v.n);
  const ids = all.filter((n) => !f || standing(n) === f);
  const keys = standings().map((s) => s.key);
  let body = '';
  for (const g of state.data.groups) {
    const row = ids.filter((n) => n.group === g.id)
      .sort((a, b) => (KG.levelOf(a) - KG.levelOf(b)) || a.title.localeCompare(b.title));
    if (!row.length) continue;
    const bar = keys.map((k) => {
      const c = row.filter((n) => standing(n) === k).length;
      return c ? `<i class="sb-${k}" style="flex:${c} 1 0"></i>` : '';
    }).join('');
    body += `<tr class="gr" style="--c:${KG.groupColor(g.id)}"><td colspan="5"><div class="gr-in">` +
      `<span class="gr-t"><i class="gtab"></i>${KG.esc(g.title)}</span><span class="gbar">${bar}</span>` +
      `<span class="gn">${row.length}</span></div></td></tr>`;
    for (const n of row) {
      const lean = n.lean ? `<code>${KG.esc(n.lean.name)}</code>` : '';
      body += `<tr data-id="${KG.esc(n.id)}" tabindex="0"${n.id === ui.sel ? ' class="sel"' : ''}>` +
        `<td class="nm${KG.levelOf(n) === 2 ? ' lvl2' : ''}">${swatch(n)}${KG.esc(n.title)}</td>` +
        `<td class="opt mute">${KG.esc(n.kind)}</td>` +
        `<td><span class="pill st-${standing(n)}">${KG.esc(standingLabel(standing(n)))}</span></td>` +
        `<td class="opt">${lean}</td>` +
        `<td class="num">${(ui.uses.get(n.id) || []).length} · ${(ui.usedBy.get(n.id) || []).length}</td></tr>`;
    }
  }
  if (!ids.length) body = '<tr><td colspan="5" class="mute">No node matches. Click the count again to see all nodes.</td></tr>';
  const head = f
    ? `<p><b>${KG.esc(standingLabel(f))}</b>: ${ids.length} of ${all.length} nodes.</p>`
    : `<p><b>All nodes</b>: ${all.length}, by group. Click a row to open it.</p>`;
  $('list').innerHTML = `<div class="lh">${head}</div><table class="nt"><thead><tr><th>Node</th>` +
    '<th class="opt">Kind</th><th>Lean</th><th class="opt">Lean name</th><th>Needs · needed by</th>' +
    `</tr></thead><tbody>${body}</tbody></table>`;
}

// ---------------------------------------------------------------- panel

function legendHtml() {
  const counts = new Map();
  for (const v of ui.lay.nodes.values()) counts.set(standing(v.n), (counts.get(standing(v.n)) || 0) + 1);
  const rows = standings().filter((s) => counts.get(s.key)).map((s) =>
    `<button type="button" class="lr" data-f="${s.key}" data-label="${KG.esc(s.label)}">` +
    `<svg width="30" height="16" viewBox="0 0 30 16" aria-hidden="true"><ellipse class="lg-${s.key}" cx="15" cy="8" rx="13" ry="6.5"/></svg>` +
    `<span>${KG.esc(s.label)}</span><span class="n">${counts.get(s.key)}</span></button>`).join('');
  const src = (state.data.meta.source && state.data.meta.source.name) || 'the project';
  return `<h2>How to read the graph</h2>
    <p class="lede">Each node is a main result or a central definition around ${KG.esc(src)}. An arrow
      from A to B means that B uses A. ${ui.view.reading}</p>
    <div class="mhow">
      <p>${MOUSE_L}<span><b>Left-click</b> a node to open it here. Its arrows show everything it
        connects to: blue for what it needs, red for what needs it.</span></p>
      <p>${MOUSE_R}<span><b>Right-click</b> another node to read that one while the arrows stay, so
        that a chain can be followed without losing the place.</span></p>
    </div>
    <h3>Where the nodes stand</h3>
    <div class="lg">${rows}</div>
    <p class="hint">Point at a row, or at the bar above, to find those nodes; click to keep them marked.</p>
    <h3>Shapes and arrows</h3>
    <div class="lg">
      <div class="lr"><svg width="30" height="16" viewBox="0 0 30 16" aria-hidden="true"><ellipse class="lg-shape" cx="15" cy="8" rx="13" ry="6.5"/></svg><span>a result: theorem, characterization, embedding</span></div>
      <div class="lr"><svg width="30" height="16" viewBox="0 0 30 16" aria-hidden="true"><rect class="lg-shape" x="3" y="2" width="24" height="12" rx="2"/></svg><span>a definition</span></div>
      <div class="lr"><svg width="30" height="16" viewBox="0 0 30 16" aria-hidden="true"><ellipse class="lg-shape thick" cx="15" cy="8" rx="13" ry="6.5"/></svg><span>a main result: thick border</span></div>
      <div class="lr"><svg width="30" height="16" viewBox="0 0 30 16" aria-hidden="true"><path class="lg-edge" d="M2 8H25"/><path class="lg-head" d="M28 8l-6-3v6z"/></svg><span>read off the Lean proofs</span></div>
      <div class="lr"><svg width="30" height="16" viewBox="0 0 30 16" aria-hidden="true"><path class="lg-edge dashed" d="M2 8H25"/><path class="lg-head" d="M28 8l-6-3v6z"/></svg><span>given by hand</span></div>
    </div>
    <h3>Using it</h3>
    <p>Drag to move the graph; scroll or pinch to zoom; <kbd>Esc</kbd> steps back. <i>List</i>
      shows every node in a table by group. <i>Nodes</i> chooses the main results or all
      nodes, with special cases, corollaries and auxiliary definitions. <i>Arrows</i> chooses
      the arrows that no longer path implies or all of them.${ui.view.using || ''}</p>`;
}

/** The node's direct neighbours in the drawing: what it needs on the left, what needs it on the right. */
function flowBlock(id) {
  const side = (ids, cls) => {
    const list = ids.map((x) => ui.lay.nodes.get(x)).filter(Boolean).map((v) => v.n)
      .sort((a, b) => a.title.localeCompare(b.title));
    if (!list.length) return `<div class="fs ${cls}"><span class="none">none</span></div>`;
    const shown = list.slice(0, 8).map((n) =>
      `<button type="button" class="fb" data-goto="${KG.esc(n.id)}">${swatch(n)}<span class="fbt">${KG.esc(n.title)}</span></button>`).join('');
    const more = list.length > 8 ? `<span class="none">and ${list.length - 8} more</span>` : '';
    return `<div class="fs ${cls}">${shown}${more}</div>`;
  };
  const n = ui.lay.nodes.get(id).n;
  return `<div class="flow"><svg class="fl-lines" aria-hidden="true"></svg>` +
    '<div class="fh need-t">Needs</div><div></div><div class="fh used-t">Needed by</div>' +
    side(ui.uses.get(id) || [], 'fs-l') +
    `<div class="fm"><span class="fc">${KG.esc(n.kind)}</span></div>` +
    side(ui.usedBy.get(id) || [], 'fs-r') + '</div>';
}

function drawFlow() {
  const f = $('panel').querySelector('.flow');
  if (!f) return;
  const lines = f.querySelector('.fl-lines'), R = f.getBoundingClientRect(), c = f.querySelector('.fc').getBoundingClientRect();
  if (!R.width) return;
  const cy = c.top + c.height / 2 - R.top, cl = c.left - R.left - 7, cr = c.right - R.left + 7;
  let out = '';
  const curveTo = (x0, y0, x1, y1, cls) => {
    const m = (x0 + x1) / 2;
    out += `<path class="fl ${cls}" d="M${x0},${y0} C${m},${y0} ${m},${y1} ${x1 - 6},${y1}"/>` +
      `<path class="fa ${cls}" d="M${x1},${y1} l-7,-3.6 v7.2 z"/>`;
  };
  f.querySelectorAll('.fs-l .fb').forEach((b) => { const r = b.getBoundingClientRect(); curveTo(r.right - R.left + 1, r.top + r.height / 2 - R.top, cl, cy, 'need'); });
  f.querySelectorAll('.fs-r .fb').forEach((b) => { const r = b.getBoundingClientRect(); curveTo(cr, cy, r.left - R.left - 1, r.top + r.height / 2 - R.top, 'used'); });
  lines.innerHTML = out;
}

function renderPanel() {
  const id = ui.peek || ui.sel;
  const panel = $('panel');
  panel.classList.toggle('peeking', !!ui.peek);
  if (!id || !state.byId.has(id)) {
    $('panel-body').innerHTML = legendHtml();
    panel.scrollTop = 0;
    markFilters();
    return;
  }
  KG.showPanel(id);
  const body = $('panel-body');
  const n = state.byId.get(id);
  const h2 = body.querySelector('h2'), badges = body.querySelector('.badges');
  const head = document.createElement('div');
  head.className = `nhead st-${standing(n)}`;
  head.innerHTML = `<div class="head"><span class="gname">${KG.esc(state.groupTitle.get(n.group) || '')}</span>` +
    '<button type="button" class="close" id="close">Close</button></div>';
  body.insertBefore(head, h2);
  head.appendChild(h2);
  if (badges) head.appendChild(badges);
  if (ui.lay.nodes.has(id)) head.insertAdjacentHTML('afterend', `<h3>How it connects</h3>${flowBlock(id)}`);
  if (ui.peek) {
    const sel = state.byId.get(ui.sel);
    body.insertAdjacentHTML('afterbegin', `<div class="peekbar"><span>Reading <b>${KG.esc(n.title)}</b>. ` +
      `The arrows still show <b>${KG.esc(sel ? sel.title : '')}</b>.</span>` +
      '<button type="button" id="peek-back">Back</button><button type="button" id="peek-move">Show its arrows</button></div>');
  }
  panel.scrollTop = 0;
  drawFlow();
}

// ---------------------------------------------------------------- opening a node

/** Opens a node: its chains in the drawing, its sheet in the panel, its name in the address. */
async function select(id, { fromHistory = false } = {}) {
  if (id && !state.byId.has(id)) id = null;
  const before = ui.sel;
  ui.sel = id;
  ui.peek = null;
  // a node of level 2 is drawn while it is open
  const needsLayout = (id && !ui.lay.nodes.has(id)) ||
    (before && before !== id && ui.lay.nodes.has(before) && !ui.allNodes && KG.levelOf(state.byId.get(before)) === 2);
  if (needsLayout) await rebuild();
  $('app').classList.toggle('sheet', !!id);
  paint();
  renderPanel();
  renderList();
  if (id) frame(id);
  else if (ui.auto && ui.mode === 'graph') { ui.touched = false; ui.auto = false; moveTo(fitTarget()); }
  if (!fromHistory) KG.writeHash({ node: id }, { push: !!id && id !== before });
}

/** A right click: the panel changes, the arrows and the view stay. Without an open node, it opens. */
function peek(id) {
  if (!ui.sel) { if (id) select(id); return; }
  const next = id && id !== ui.sel ? id : null;
  if (next === ui.peek) return;
  ui.peek = next;
  if (next) ui.usedPeek = true;
  paint();
  renderPanel();
}

function escape() {
  if (ui.peek) peek(null);
  else if (ui.sel) select(null);
  else if (ui.flt) { ui.flt = null; paint(); renderList(); }
}

function show() {
  stage().hidden = ui.mode !== 'graph';
  $('list').hidden = ui.mode !== 'list';
  const seg = $('seg-layout');
  if (seg) seg.hidden = ui.mode !== 'graph';
  if (ui.mode === 'graph') {
    if (!ui.touched) fit(); else applyCam();
    if (ui.sel) frame(ui.sel);
  }
  renderList();
  const pressed = [['v-graph', ui.mode === 'graph'], ['v-list', ui.mode === 'list'],
    ['n-main', !ui.allNodes], ['n-all', ui.allNodes], ['a-reduced', !ui.allArrows], ['a-all', ui.allArrows]];
  if (seg) pressed.push(['l-flat', !ui.grouped], ['l-grouped', ui.grouped]);
  for (const [b, on] of pressed) $(b).setAttribute('aria-pressed', String(on));
  saveSettings();
}

// ---------------------------------------------------------------- wiring

function wire() {
  $('v-graph').onclick = () => { ui.mode = 'graph'; show(); };
  $('v-list').onclick = () => { ui.mode = 'list'; show(); };
  const relayout = async (patch) => {
    Object.assign(ui, patch);
    ui.touched = false;
    await rebuild();
    show();
    if (ui.sel) frame(ui.sel);
  };
  if ($('seg-layout')) {
    $('l-flat').onclick = () => relayout({ grouped: false });
    $('l-grouped').onclick = () => relayout({ grouped: true });
  }
  $('n-main').onclick = () => relayout({ allNodes: false });
  $('n-all').onclick = () => relayout({ allNodes: true });
  $('a-reduced').onclick = () => relayout({ allArrows: false });
  $('a-all').onclick = () => relayout({ allArrows: true });
  const centre = (f) => { const a = area(); zoomAt(a.W / 2, a.H / 2, f); };
  $('z-in').onclick = () => centre(1.4);
  $('z-out').onclick = () => centre(1 / 1.4);
  $('z-fit').onclick = () => fit();

  const panel = $('panel');
  panel.addEventListener('click', (ev) => {
    if (ev.target.closest('#close')) select(null);
    else if (ev.target.closest('#peek-back')) peek(null);
    else if (ev.target.closest('#peek-move')) select(ui.peek);
  });
  panel.addEventListener('contextmenu', (ev) => {
    const b = ev.target.closest && ev.target.closest('[data-goto]');
    if (!b || !ui.sel || ui.mode !== 'graph') return;
    ev.preventDefault();
    peek(b.dataset.goto);
  });
  const list = $('list');
  list.addEventListener('click', (ev) => {
    const r = ev.target.closest('tr[data-id]');
    if (r) select(r.dataset.id);
  });
  list.addEventListener('keydown', (ev) => {
    const r = ev.target.closest && ev.target.closest('tr[data-id]');
    if (r && (ev.key === 'Enter' || ev.key === ' ')) { ev.preventDefault(); select(r.dataset.id); }
  });

  // rows of the legend and segments of the masthead find their nodes in the drawing
  document.addEventListener('pointerover', (ev) => {
    if (ev.pointerType === 'touch' || !ev.target.closest) return;
    const b = ev.target.closest('[data-f]');
    if (b && ui.hoverFlt !== b.dataset.f) { ui.hoverFlt = b.dataset.f; paint(); }
  });
  document.addEventListener('pointerout', (ev) => {
    if (!ev.target.closest) return;
    const b = ev.target.closest('[data-f]');
    const to = ev.relatedTarget && ev.relatedTarget.closest ? ev.relatedTarget.closest('[data-f]') : null;
    if (b && to !== b) { ui.hoverFlt = null; paint(); }
  });
  document.addEventListener('click', (ev) => {
    const b = ev.target.closest && ev.target.closest('[data-f]');
    if (!b) return;
    ui.flt = ui.flt === b.dataset.f ? null : b.dataset.f;
    ui.hoverFlt = null;
    if (ui.sel) select(null); else paint();
    renderList();
  });

  // dragging moves the drawing; the wheel, ctrl+wheel and touchpad pinches zoom it
  const st = stage();
  const pts = new Map();
  let dragged = false, pinch = 0;
  st.addEventListener('wheel', (ev) => {
    ev.preventDefault();
    const a = area(), u = ev.deltaMode === 1 ? 16 : ev.deltaMode === 2 ? a.H : 1;
    zoomAt(ev.clientX - a.r.left, ev.clientY - a.r.top, Math.exp(-ev.deltaY * u * (ev.ctrlKey ? 0.012 : 0.0016)));
  }, { passive: false });
  st.addEventListener('pointerdown', (ev) => {
    if (ev.target.closest('.ctl') || ev.button === 2) return;
    pts.set(ev.pointerId, { x: ev.clientX, y: ev.clientY });
    dragged = false;
  });
  st.addEventListener('pointermove', (ev) => {
    const p = pts.get(ev.pointerId);
    if (!p) return;
    const dx = ev.clientX - p.x, dy = ev.clientY - p.y;
    if (pts.size === 1) {
      if (!dragged && Math.hypot(dx, dy) < 4) return;
      if (!dragged) {
        dragged = true;
        st.classList.add('grabbing');
        try { st.setPointerCapture(ev.pointerId); } catch (err) { /* dragging works without capture */ }
      }
      pan(dx, dy);
      p.x = ev.clientX; p.y = ev.clientY;
    } else if (pts.size === 2) {
      dragged = true;
      p.x = ev.clientX; p.y = ev.clientY;
      const two = [...pts.values()], d = Math.hypot(two[0].x - two[1].x, two[0].y - two[1].y), a = area();
      if (pinch) zoomAt((two[0].x + two[1].x) / 2 - a.r.left, (two[0].y + two[1].y) / 2 - a.r.top, d / pinch);
      pinch = d;
    }
  });
  const release = (ev) => { pts.delete(ev.pointerId); pinch = 0; st.classList.remove('grabbing'); };
  st.addEventListener('pointerup', release);
  st.addEventListener('pointercancel', release);
  st.addEventListener('pointerover', (ev) => {
    if (ev.pointerType === 'touch') return;
    const g = ev.target.closest('g.node');
    if (g) { ui.hover = g.dataset.id; showHint(); }
  });
  st.addEventListener('pointerout', (ev) => { if (ev.target.closest('g.node')) { ui.hover = null; showHint(); } });
  st.addEventListener('click', (ev) => {
    if (dragged) { dragged = false; return; }
    if (ev.target.closest('.ctl')) return;
    const g = ev.target.closest('g.node');
    select(g ? g.dataset.id : null);
  });
  st.addEventListener('contextmenu', (ev) => {
    const g = ev.target.closest && ev.target.closest('g.node');
    if (!g) return;
    ev.preventDefault();
    peek(g.dataset.id);
  });
  st.addEventListener('keydown', (ev) => {
    const g = ev.target.closest && ev.target.closest('g.node');
    if (g && (ev.key === 'Enter' || ev.key === ' ')) {
      ev.preventDefault();
      if (ev.shiftKey) peek(g.dataset.id); else select(g.dataset.id);
    }
  });
  if (window.ResizeObserver) {
    new ResizeObserver(() => {
      if (ui.mode !== 'graph' || !ui.lay) return;
      if (!ui.touched) fit(); else applyCam();
    }).observe(st);
    new ResizeObserver(drawFlow).observe(panel);
  }
}

async function fontsReady() {
  if (!document.fonts || !document.fonts.load) return;
  await Promise.race([
    Promise.all([document.fonts.load(`500 ${LABEL_PX}px Archivo`), document.fonts.load('800 40px Archivo'),
      document.fonts.load('700 15px "JetBrains Mono"')]).catch(() => {}),
    KG.wait(2500),
  ]);
}

/**
 * Starts a page of the style. `view` is { layout: async (graph, { grouped }) => lay, reading:
 * a sentence on where the foundations and results stand, using: a sentence on its own
 * controls }.
 */
async function start(view) {
  ui.view = view;
  if (typeof ELK !== 'function') {
    KG.setStatus('The layout library could not be loaded (elkjs, from a CDN).', true);
    return;
  }
  try {
    await KG.loadData();
  } catch (err) {
    KG.setStatus(`Could not load the graph data: ${err.message}`, true);
    return;
  }
  KG.header();
  loadSettings();
  KG.hooks.goto = (id) => select(id);
  KG.hooks.gotoDecl = (key) => { ui.peek = null; KG.showDeclPanel(key); };
  KG.hooks.popstate = (h) => select(h.node || null, { fromHistory: true });
  // the switch "Nodes" replaces the checkbox of plain/ that common.js listens to
  KG.initCommon({ onPick: (id) => select(id), onEscape: escape, onDetails: () => {} });
  wire();
  await fontsReady();
  await rebuild();
  show();
  KG.setStatus('');
  const h = KG.readHash();
  if (h.node) await select(h.node, { fromHistory: true });
  else { renderPanel(); intro(); }
  window.knowledgeGraph = { select, count: () => ui.lay.nodes.size };
  document.body.dataset.ready = 'true';
}

/** Runs `start` once the page has loaded, unless a test loads the style without a page. */
function boot(view) {
  if (window.ADVANCED_HEADLESS) return;
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', () => start(view));
  else start(view);
}

return { graph, everyArrow, geometry, standing, nodeRecords, inShape, boundary, samples, passesClear,
  unit, svg, boot, LABEL_PX };

})();
