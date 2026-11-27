/*
 * The part of the knowledge-graph page that its three views share (classic.js: layers,
 * force.js: forces, radial.js: rings): the data and its indexes, the visible graph, node
 * sizes, colours, the panel, the search, the header, the address, and the view inside a node.
 *
 * Data contract (written by `lake exe extract`; README.md and schema.json describe it in full):
 *   meta   { graph, title, generated_at, source { name, repo, commit, dirty }, mathlib_commit,
 *            lean_toolchain, lean_version, tool_commit, public_source_links, publish {...},
 *            profiles [{ id, title, nest_examples, nodes?: [id] }] }
 *   groups [{ id, title }]
 *   nodes  [{ id, title, kind, group, level (1 | 2), status (proved | sorry | planned | informal),
 *             lean?: { name, keyword, module, source { file, line_start, line_end }, source_url,
 *                      docgen_url, links_public, docstring, signature, source_text, axioms,
 *                      supporting: [key], uses: [key], uses_nodes: [id] },
 *             statement_tex?, refs? }]
 *   edges  [{ source, target, kind (computed | manual), via?: [key], redundant }]
 *   declarations { key: { name, keyword, module, source, source_url, links_public, docstring,
 *                         uses: [key], uses_nodes: [id] } }
 * In data.json an edge `source → target` means that `source` uses `target`. The views draw the
 * arrow the other way round, from what is used to the result that follows from it.
 */
'use strict';

window.KG = (() => {

const params = new URLSearchParams(location.search);
const DATA_URL = params.get('data') || './data.json';
const STANDARD_AXIOMS = ['Classical.choice', 'Quot.sound', 'propext'];
const FONT_FAMILY = 'system-ui, -apple-system, "Segoe UI", sans-serif';
const REDUCED_MOTION = window.matchMedia
  ? matchMedia('(prefers-reduced-motion: reduce)').matches : false;

const state = {
  data: null,
  byId: new Map(),     // node id → node
  out: new Map(),      // node id → edges leaving it (all edges, redundant ones included)
  inc: new Map(),      // node id → edges arriving at it
  groupTitle: new Map(),
  groupIndex: new Map(),
  groupSlot: new Map(),  // group id → colour slot 0-7, or -1 (grey)
  declUsers: new Map(), // declaration key → { decls: [key], nodes: [id] } that use it
  showDetails: false,
  focus: null,
  folded: new Set(),
  selected: null,
  profile: null,         // id of the profile in use (meta.profiles; ?profile= in the address)
  examples: new Map(),   // node id → the nodes that are examples of it (example_of)
};

/** What the views plug in: where a click in the panel or the search leads. */
const hooks = {
  goto: (id) => {},
  gotoDecl: (key) => {},
  popstate: null,        // (hash) => void: the browser went back or forward
};

const $ = (id) => document.getElementById(id);

function setStatus(text, isError = false) {
  const el = $('status');
  if (!el) return;
  el.textContent = text;
  el.classList.toggle('error', isError);
}

// ---------------------------------------------------------------- data

async function loadData() {
  const res = await fetch(DATA_URL, { cache: 'no-cache' });
  if (!res.ok) throw new Error(`${DATA_URL}: ${res.status} ${res.statusText}`);
  const data = await res.json();
  data.declarations = data.declarations || {};
  state.data = data;
  data.meta = data.meta || {};
  if (!data.meta.profiles || !data.meta.profiles.length) {
    data.meta.profiles = [{ id: 'main', title: 'Main results', nest_examples: true }];
  }
  const wanted = params.get('profile');
  state.profile = data.meta.profiles.some((p) => p.id === wanted) ? wanted : data.meta.profiles[0].id;
  const listed = currentProfile().nodes;
  if (listed) restrictToNodes(data, listed);
  data.groups.forEach((g, i) => { state.groupTitle.set(g.id, g.title); state.groupIndex.set(g.id, i); });
  assignColourSlots(data);
  for (const n of data.nodes) {
    state.byId.set(n.id, n);
    state.out.set(n.id, []);
    state.inc.set(n.id, []);
  }
  for (const e of data.edges) {
    if (!state.byId.has(e.source) || !state.byId.has(e.target)) continue;
    state.out.get(e.source).push(e);
    state.inc.get(e.target).push(e);
  }
  const users = (key) => {
    if (!state.declUsers.has(key)) state.declUsers.set(key, { decls: [], nodes: [] });
    return state.declUsers.get(key);
  };
  for (const [key, d] of Object.entries(data.declarations)) {
    for (const u of d.uses || []) users(u).decls.push(key);
  }
  for (const n of data.nodes) {
    for (const u of (n.lean && n.lean.uses) || []) users(u).nodes.push(n.id);
  }
  for (const n of data.nodes) {
    if (!n.example_of) continue;
    if (!state.examples.has(n.example_of)) state.examples.set(n.example_of, []);
    state.examples.get(n.example_of).push(n);
  }
  return data;
}

// ---------------------------------------------------------------- profiles, examples, importance

function currentProfile() {
  return state.data.meta.profiles.find((p) => p.id === state.profile) || state.data.meta.profiles[0];
}

/**
 * Keeps only the nodes `ids` (a profile with a node list) and the groups they belong to. Kept
 * nodes are joined wherever a path ran between them through dropped nodes; such an arrow lists
 * the supporting declarations of a shortest such path, and `redundant` marks the arrows that
 * other kept arrows imply. An example whose general result is dropped stands on its own.
 */
function restrictToNodes(data, ids) {
  const keep = new Set(ids);
  const outAll = new Map(data.nodes.map((n) => [n.id, []]));
  for (const e of data.edges) {
    if (outAll.has(e.source) && outAll.has(e.target)) outAll.get(e.source).push(e);
  }
  const joined = new Map();
  for (const a of keep) {
    // breadth first, so that the first path to reach a kept node is a shortest one
    const queue = (outAll.get(a) || []).map((e) => ({ e, manual: e.kind === 'manual', via: e.via || [] }));
    const seen = new Set();
    for (let i = 0; i < queue.length; i++) {
      const { e, manual, via } = queue[i];
      const b = e.target;
      if (keep.has(b)) {
        const key = a + '\u0001' + b;
        const old = joined.get(key);
        if (!old) joined.set(key, { source: a, target: b, kind: manual ? 'manual' : 'computed', via });
        else if (!manual) old.kind = 'computed';
        continue;
      }
      if (seen.has(b)) continue;
      seen.add(b);
      for (const f of outAll.get(b) || []) {
        queue.push({ e: f, manual: manual || f.kind === 'manual', via: [...via, ...(f.via || [])] });
      }
    }
  }
  const succ = new Map([...keep].map((v) => [v, []]));
  for (const e of joined.values()) succ.get(e.source).push(e.target);
  const reachMemo = new Map();
  const reach = (v, guard = new Set()) => {
    if (reachMemo.has(v)) return reachMemo.get(v);
    guard.add(v);
    const r = new Set();
    for (const w of succ.get(v)) {
      r.add(w);
      if (!guard.has(w)) for (const x of reach(w, guard)) r.add(x);
    }
    guard.delete(v);
    reachMemo.set(v, r);
    return r;
  };
  for (const e of joined.values()) {
    e.redundant = succ.get(e.source).some((c) => c !== e.target && reach(c).has(e.target));
  }
  data.nodes = data.nodes.filter((n) => keep.has(n.id));
  for (const n of data.nodes) if (n.example_of && !keep.has(n.example_of)) delete n.example_of;
  data.edges = [...joined.values()];
  const used = new Set(data.nodes.flatMap((n) => [n.group, ...(n.also_in || [])]));
  data.groups = data.groups.filter((g) => used.has(g.id));
}

/** The level of a node in the profile in use: `levels[profile]`, or else `level`. */
function levelOf(n) {
  return (n.levels && n.levels[state.profile]) || n.level;
}

/** Shown with the current setting of "Show details"? */
function shownLevel(n) {
  return state.showDetails || levelOf(n) === 1;
}

/** Is the node an example that the profile puts below its general result? */
function isNested(n) {
  return !!(n && n.example_of && currentProfile().nest_examples);
}

/** The examples shown below the node (none in a profile that does not nest them). */
function examplesOf(id) {
  if (!currentProfile().nest_examples) return [];
  return (state.examples.get(id) || []).filter(shownLevel);
}

const DEFAULT_EMPHASIS = { characterization: 3, embedding: 3, theorem: 2, definition: 2, lemma: 1 };

/** How prominently a node is shown, 1 to 3: its `weight`, or else the emphasis of its kind,
 * one less on level 2. */
function importance(n) {
  if (n.weight) return n.weight;
  const em = { ...DEFAULT_EMPHASIS, ...(state.data.meta.emphasis || {}) };
  const v = em[n.kind] || 2;
  return levelOf(n) === 2 ? Math.max(1, v - 1) : v;
}

/** Everything `id` depends on, transitively, `id` included. */
function dependencyClosure(id) {
  const seen = new Set([id]);
  const stack = [id];
  while (stack.length) {
    for (const e of state.out.get(stack.pop()) || []) {
      if (!seen.has(e.target)) { seen.add(e.target); stack.push(e.target); }
    }
  }
  return seen;
}

/**
 * The nodes and edges to draw, edges in the direction "source uses target". Hidden nodes
 * (details, outside the focus) are bridged: a visible node is joined to the first visible
 * nodes reached through hidden ones, and edges implied by longer paths are dropped again.
 * Folded groups then become single nodes `g:<group>`.
 */
function visibleGraph() {
  const { data } = state;
  const closure = state.focus ? dependencyClosure(state.focus) : null;
  const visible = new Set();
  for (const n of data.nodes) {
    if (isNested(n)) continue; // shown below its general result
    const byLevel = shownLevel(n) || n.id === state.selected || n.id === state.focus;
    if (byLevel && (!closure || closure.has(n.id))) visible.add(n.id);
  }

  const induced = new Map();
  for (const a of visible) {
    const stack = (state.out.get(a) || []).map((e) => [e, e.kind === 'manual']);
    const seen = new Set();
    while (stack.length) {
      const [e, manual] = stack.pop();
      const b = e.target;
      if (visible.has(b)) {
        const key = a + '\u0001' + b;
        const old = induced.get(key);
        if (!old) induced.set(key, { source: a, target: b, manual });
        else if (!manual) old.manual = false;
        continue;
      }
      if (seen.has(b)) continue;
      seen.add(b);
      for (const f of state.out.get(b) || []) stack.push([f, manual || f.kind === 'manual']);
    }
  }

  const succ = new Map([...visible].map((v) => [v, []]));
  for (const e of induced.values()) succ.get(e.source).push(e.target);
  const reachMemo = new Map();
  const reach = (v, guard = new Set()) => {
    if (reachMemo.has(v)) return reachMemo.get(v);
    guard.add(v);
    const r = new Set();
    for (const w of succ.get(v)) {
      r.add(w);
      if (!guard.has(w)) for (const x of reach(w, guard)) r.add(x);
    }
    guard.delete(v);
    reachMemo.set(v, r);
    return r;
  };
  let edges = [...induced.values()].filter((e) =>
    !succ.get(e.source).some((c) => c !== e.target && reach(c).has(e.target)));

  const rep = (id) => {
    const g = state.byId.get(id).group;
    return state.folded.has(g) ? 'g:' + g : id;
  };
  const folded = new Map();
  const nodes = [];
  for (const id of visible) {
    const n = state.byId.get(id);
    if (state.folded.has(n.group)) folded.set(n.group, (folded.get(n.group) || 0) + 1);
    else nodes.push(n);
  }
  const merged = new Map();
  for (const e of edges) {
    const s = rep(e.source), t = rep(e.target);
    if (s === t) continue;
    const key = s + '\u0001' + t;
    const old = merged.get(key);
    if (!old) merged.set(key, { source: s, target: t, manual: e.manual });
    else if (!e.manual) old.manual = false;
  }
  edges = [...merged.values()];
  edges.sort((x, y) => (x.source + x.target).localeCompare(y.source + y.target));
  nodes.sort((x, y) => (state.groupIndex.get(x.group) - state.groupIndex.get(y.group)) ||
    x.id.localeCompare(y.id));
  return { nodes, edges, folded };
}

/** Longest chain of dependencies below each node of a graph given as "source uses target". */
function depths(ids, edges) {
  const uses = new Map(ids.map((i) => [i, []]));
  for (const e of edges) if (uses.has(e.source) && uses.has(e.target)) uses.get(e.source).push(e.target);
  const memo = new Map();
  const depth = (v, guard = new Set()) => {
    if (memo.has(v)) return memo.get(v);
    guard.add(v);
    let d = 0;
    for (const w of uses.get(v)) if (!guard.has(w)) d = Math.max(d, depth(w, guard) + 1);
    guard.delete(v);
    memo.set(v, d);
    return d;
  };
  for (const i of ids) depth(i);
  return memo;
}

/** Can one look inside the node: does its proof pass through lemmas of the project, or does it
 * have examples below it? */
function hasInside(n) {
  return !!(n && ((n.lean && n.lean.supporting && n.lean.supporting.length >= 3) || examplesOf(n.id).length));
}

// ---------------------------------------------------------------- the view inside a node

const DECL_LIMIT = 40;

function moduleTail(m) {
  const parts = (m || '').split('.');
  return parts.slice(-2).join('/');
}

function shortName(name) {
  const parts = name.split('.');
  return parts[parts.length - 1];
}

/**
 * The proof of node `id` as a graph: its supporting declarations, or, when there are many,
 * the files they lie in (`module` given: the declarations of that file). Edges point from what
 * is used to what uses it. Portals lead out of the view: the main results it uses (`in`), the
 * main results that use it (`out`), and in a file view the other files (`file`).
 */
function insideView(id, module = null) {
  const n = state.byId.get(id);
  const T = state.data.declarations;
  const S = new Set((n.lean && n.lean.supporting) || []);
  const byModules = !module && S.size > DECL_LIMIT;
  const items = new Map();
  const itemOf = new Map(); // declaration key or 'root' → item id

  items.set('root', { id: 'root', kind: 'root', node: n, label: n.title });
  itemOf.set('root', 'root');
  for (const key of S) {
    const d = T[key];
    if (!d) continue;
    if (byModules) {
      const mid = 'm:' + d.module;
      if (!items.has(mid)) items.set(mid, { id: mid, kind: 'module', module: d.module, label: moduleTail(d.module), count: 0 });
      items.get(mid).count++;
      itemOf.set(key, mid);
    } else if (!module || d.module === module) {
      const did = 'd:' + key;
      items.set(did, { id: did, kind: 'decl', key, decl: d, label: shortName(d.name) });
      itemOf.set(key, did);
    } else {
      const mid = 'f:' + d.module;
      itemOf.set(key, mid); // created on demand: only files next to this one are shown
    }
  }

  const edges = new Map();
  const addEdge = (from, to, kind) => {
    if (from === to) return;
    for (const x of [from, to]) {
      if (!items.has(x) && x.startsWith('f:')) {
        items.set(x, { id: x, kind: 'file', module: x.slice(2), label: moduleTail(x.slice(2)) });
      }
    }
    const k = from + '\u0001' + to;
    if (!edges.has(k)) edges.set(k, { source: from, target: to, kind, weight: 0 });
    edges.get(k).weight++;
  };
  // In a file view only what touches a declaration of the file is shown.
  const isDecl = (x) => items.has(x) && items.get(x).kind === 'decl';
  const users = [['root', n.lean || {}], ...[...S].map((k) => [k, T[k] || {}])];
  for (const [u, rec] of users) {
    const ui = itemOf.get(u);
    if (!ui) continue;
    for (const v of rec.uses || []) {
      const vi = itemOf.get(v);
      if (!vi || !S.has(v)) continue;
      if (module && !isDecl(ui) && !isDecl(vi)) continue;
      addEdge(vi, ui, 'inner');
    }
    if (module && !isDecl(ui)) continue;
    for (const m of rec.uses_nodes || []) {
      if (m === id || !state.byId.has(m)) continue;
      const pid = 'in:' + m;
      if (!items.has(pid)) items.set(pid, { id: pid, kind: 'portal-in', node: state.byId.get(m), label: state.byId.get(m).title });
      addEdge(pid, ui, 'portal');
    }
  }
  if (!module) {
    for (const e of state.inc.get(id) || []) {
      const src = state.byId.get(e.source);
      if (isNested(src) && src.example_of === id) continue; // shown as an example below
      const pid = 'out:' + e.source;
      if (!items.has(pid)) items.set(pid, { id: pid, kind: 'portal-out', node: state.byId.get(e.source), label: state.byId.get(e.source).title });
      addEdge('root', pid, 'portal');
    }
    // the examples of the result, below it
    for (const ex of examplesOf(id)) {
      const eid = 'ex:' + ex.id;
      items.set(eid, { id: eid, kind: 'example', node: ex, label: ex.title });
      addEdge('root', eid, 'example');
    }
  } else {
    // the root only if it uses a declaration of the file
    const rootUsed = [...edges.values()].some((e) => e.target === 'root');
    if (!rootUsed) items.delete('root');
  }
  // drop edges to items that were not created (a file view leaves the other files out)
  let list = [...edges.values()].filter((e) => items.has(e.source) && items.has(e.target));
  list = reduceEdges(list);
  // many portals of one kind become one: "N more results"
  for (const [kind, prefix] of [['portal-in', 'in:'], ['portal-out', 'out:']]) {
    const ps = [...items.values()].filter((it) => it.kind === kind)
      .sort((a, b) => (levelOf(a.node) - levelOf(b.node)) || a.label.localeCompare(b.label));
    if (ps.length <= PORTAL_LIMIT) continue;
    const rest = new Set(ps.slice(PORTAL_LIMIT - 1).map((p) => p.id));
    for (const r of rest) items.delete(r);
    const more = { id: prefix + '*', kind, more: rest.size, label: `${rest.size} more results` };
    items.set(more.id, more);
    list = list.filter((e) => !rest.has(e.source) && !rest.has(e.target));
    const anchor = items.has('root') ? 'root'
      : ([...items.values()].find((it) => it.kind === 'decl') || {}).id;
    if (!anchor) continue;
    list.push(kind === 'portal-in'
      ? { source: more.id, target: anchor, kind: 'portal', weight: rest.size }
      : { source: anchor, target: more.id, kind: 'portal', weight: rest.size });
  }
  return { node: n, module, byModules, items: [...items.values()], edges: list };
}

const PORTAL_LIMIT = 8;

/**
 * Leaves out the edges between lemmas (or files) that follow from two others. Lean's files
 * form an acyclic graph, so this keeps which item leads to which; portal edges stay.
 */
function reduceEdges(list) {
  const succ = new Map();
  for (const e of list) {
    if (e.kind !== 'inner') continue;
    if (!succ.has(e.source)) succ.set(e.source, []);
    succ.get(e.source).push(e.target);
  }
  const memo = new Map();
  const reach = (v, guard = new Set()) => {
    if (memo.has(v)) return memo.get(v);
    guard.add(v);
    const r = new Set();
    for (const w of succ.get(v) || []) {
      r.add(w);
      if (!guard.has(w)) for (const x of reach(w, guard)) r.add(x);
    }
    guard.delete(v);
    memo.set(v, r);
    return r;
  };
  return list.filter((e) => e.kind !== 'inner' ||
    !(succ.get(e.source) || []).some((c) => c !== e.target && reach(c).has(e.target)));
}

// ---------------------------------------------------------------- text and boxes

const measure = document.createElement('canvas').getContext('2d');
/** The type sizes of every view, in pixels at zoom 1; one scale, so that the overviews read alike. */
const TYPE = { node: 16, small: 14, root: 18, groupTitle: 24, caption: 36, cellTitle: 22 };
const fontOf = (px, weight = 'normal', style = 'normal') => `${style} ${weight} ${px}px ${FONT_FAMILY}`;
const LINE_HEIGHT = 19;
const NODE_FONT = fontOf(TYPE.node);
const SMALL_FONT = fontOf(TYPE.small);
const GROUP_FONT = fontOf(TYPE.groupTitle, 700);
const PAD_X = 16;
const PAD_Y = 10;

/** Greedy word wrap at `maxWidth` pixels; returns the lines and the widest line's width. */
function wrap(text, maxWidth, font) {
  measure.font = font;
  const lines = [];
  let line = '';
  for (const word of String(text).split(/\s+/)) {
    const next = line ? line + ' ' + word : word;
    if (line && measure.measureText(next).width > maxWidth) { lines.push(line); line = word; }
    else line = next;
  }
  if (line) lines.push(line);
  const width = Math.max(0, ...lines.map((l) => measure.measureText(l).width));
  return { lines, width };
}

function textWidth(text, font) {
  measure.font = font;
  return measure.measureText(text).width;
}

/**
 * Label and size of a node, with a margin of PAD_X / PAD_Y between the text and the border.
 * Shapes that cut their corners get room for them: on a hexagon or a tag, the shape at height
 * y from the centre reaches only a(1 - c|y|/b) to the side, so the text block (half-width u,
 * half-height t) fits when a(1 - c t/b) ≥ u; an ellipse needs (u/a)² + (t/b)² ≤ 1.
 */
function nodeBox(label, kind, { font = NODE_FONT, maxWidth = 220, lineHeight = LINE_HEIGHT } = {}) {
  const { lines, width } = wrap(label, maxWidth, font);
  const u = width / 2 + PAD_X;
  const t = (lines.length * lineHeight) / 2;
  let a = u, b = t + PAD_Y;
  if (kind === 'characterization') a = u / (1 - 0.5 * t / b);
  else if (kind === 'embedding') a = u / (1 - 0.75 * t / b);
  else if (kind === 'lemma') { b = t * 1.45 + PAD_Y; a = u / Math.sqrt(1 - (t / b) ** 2); }
  return { label: lines.join('\n'), w: Math.max(2 * a, 64), h: Math.max(2 * b, 30) };
}

/** The box of a lemma name: names have no spaces, so they wrap after underscores. */
function identBox(name) {
  const segs = name.split(/(?<=_)/);
  const lines = [];
  let line = '';
  for (const s of segs) {
    if (line && textWidth(line + s, SMALL_FONT) > 190) { lines.push(line); line = s; }
    else line += s;
  }
  if (line) lines.push(line);
  const width = Math.max(...lines.map((l) => textWidth(l, SMALL_FONT)));
  return { label: lines.join('\n'), w: width + 24, h: lines.length * 17 + 16 };
}

function nodeLabel(n) {
  return (n.status === 'sorry' ? '⚠ ' : '') + n.title;
}

/**
 * The type of a node's label: on level 1 by importance (14, 16 or 18 px), on level 2 small and
 * italic; with the width of its border.
 */
function nodeType(n) {
  const detail = levelOf(n) === 2;
  const imp = importance(n);
  const px = detail ? TYPE.small : Math.round(TYPE.node * (1 + 0.12 * (imp - 2)));
  return { px, italic: detail, font: fontOf(px, 'normal', detail ? 'italic' : 'normal'),
    lineHeight: Math.round(px * 1.2), border: detail ? 1.2 : [1.4, 2, 2.6][imp - 1] };
}

/** The box of a node with its type: label, size, font size and border width. */
function boxFor(n, label = nodeLabel(n), maxWidth = 220) {
  const t = nodeType(n);
  const b = nodeBox(label, n.kind, { font: t.font, lineHeight: t.lineHeight, maxWidth });
  return { ...b, fs: t.px, bw: t.border, italic: t.italic, lh: t.lineHeight / t.px };
}

// ---------------------------------------------------------------- colours

function cssVar(name) {
  return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
}

/**
 * The colour slots of the groups. The groups with results that have no Lean code (planned or
 * informal) form a second set apart from the others, and each set takes the eight colours in
 * the fixed order of its groups; a group beyond the eighth of its set is grey. The second set
 * starts at the colour where its groups share the fewest colours with the groups they use, so
 * that a group does not wear the colour of what it builds on. In the Rings view the two sets lie
 * in separate zones, and every group carries its name, so a colour in both sets is not ambiguous.
 */
function assignColourSlots(data) {
  const outer = new Set(data.nodes.filter((n) => !n.lean).map((n) => n.group));
  const inner = data.groups.filter((g) => !outer.has(g.id));
  const rest = data.groups.filter((g) => outer.has(g.id));
  inner.forEach((g, i) => state.groupSlot.set(g.id, i < 8 ? i : -1));
  const groupOf = new Map(data.nodes.map((n) => [n.id, n.group]));
  const restIndex = new Map(rest.map((g, i) => [g.id, i]));
  // weight[j][slot]: arrows from the j-th group of the second set to inner groups of that colour
  const weight = rest.map(() => new Array(8).fill(0));
  for (const e of data.edges) {
    const j = restIndex.get(groupOf.get(e.source));
    const s = state.groupSlot.get(groupOf.get(e.target));
    if (j !== undefined && s !== undefined && s >= 0 && !outer.has(groupOf.get(e.target))) weight[j][s]++;
  }
  const cost = (k) => rest.reduce((c, g, j) => c + (j < 8 ? weight[j][(k + j) % 8] : 0), 0);
  let best = inner.length % 8;
  for (let k = 0; k < 8; k++) if (cost(k) < cost(best)) best = k;
  rest.forEach((g, j) => state.groupSlot.set(g.id, j < 8 ? (best + j) % 8 : -1));
}

/** The colour slot of a group (0-7), or -1 for grey. */
const colourSlot = (gid) => (state.groupSlot.has(gid) ? state.groupSlot.get(gid) : -1);

/** The categorical colour of a group (see `assignColourSlots`). */
function groupColor(gid) {
  const i = colourSlot(gid);
  return i >= 0 ? cssVar(`--g${i + 1}`) : cssVar('--muted');
}

/** Node shapes and label settings common to all views. */
function shapeStyle() {
  return [
    { selector: 'node.k-theorem', style: { 'shape': 'rectangle' } },
    { selector: 'node.k-characterization', style: { 'shape': 'hexagon' } },
    { selector: 'node.k-embedding', style: { 'shape': 'tag' } },
    { selector: 'node.k-lemma', style: { 'shape': 'ellipse' } },
    { selector: 'node.k-definition', style: { 'shape': 'round-rectangle' } },
  ];
}

// ---------------------------------------------------------------- panel

function esc(s) {
  return String(s).replace(/[&<>"']/g, (c) =>
    ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
}

/** Enough Markdown for docstrings: paragraphs, lists, inline code, bold, italics, links. */
function markdown(text) {
  const codes = [];
  let t = esc(text).replace(/`([^`]+)`/g, (_, c) => { codes.push(c); return `\u0000${codes.length - 1}\u0000`; });
  t = t.replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>')
    .replace(/(^|[\s(])\*([^*\s][^*]*?)\*(?=[\s).,;:]|$)/g, '$1<em>$2</em>')
    .replace(/\[([^\]]+)\]\((https?:[^)\s]+)\)/g, '<a href="$2" rel="noopener">$1</a>');
  const html = t.split(/\n\s*\n/).map((block) => {
    const lines = block.split('\n').filter((l) => l.trim());
    if (lines.length && lines.every((l) => /^\s*[-*] /.test(l))) {
      return '<ul>' + lines.map((l) => `<li>${l.replace(/^\s*[-*] /, '')}</li>`).join('') + '</ul>';
    }
    return lines.length ? `<p>${lines.join(' ')}</p>` : '';
  }).join('');
  return html.replace(/\u0000(\d+)\u0000/g, (_, i) => `<code>${codes[+i]}</code>`);
}

function renderMath(el) {
  if (typeof window.renderMathInElement !== 'function') return;
  window.renderMathInElement(el, {
    delimiters: [
      { left: '$$', right: '$$', display: true }, { left: '\\[', right: '\\]', display: true },
      { left: '$', right: '$', display: false }, { left: '\\(', right: '\\)', display: false },
    ],
    throwOnError: false,
  });
}

/** A link into the sources; links into a private repository are marked as such. */
function sourceLink(url, text, isPublic) {
  if (!url) return '';
  if (isPublic) return `<a href="${esc(url)}" target="_blank" rel="noopener">${esc(text)}</a>`;
  return `<a class="private" href="${esc(url)}" target="_blank" rel="noopener"
    title="The repository is private: this link works only for its owner">${esc(text)}</a>`;
}

function lineCount(src) {
  return src ? src.line_end - src.line_start + 1 : 0;
}

/** "Uses" or "Used by": the other end of each edge, in data direction. */
function depList(edges, end) {
  if (!edges.length) return '<p class="muted">None among the nodes of this graph.</p>';
  const items = edges
    .map((e) => ({ e, n: state.byId.get(e[end]) }))
    .sort((a, b) => a.n.title.localeCompare(b.n.title))
    .map(({ e, n }) => {
      const via = e.via && e.via.length
        ? `<div class="via">through ${e.via.map((v) => `<button type="button" class="decl-link" data-goto-decl="${esc(v)}"><code>${esc(v)}</code></button>`).join(', ')}</div>` : '';
      const manual = e.kind === 'manual' ? ' <span class="muted">(by hand)</span>' : '';
      return `<li><button type="button" data-goto="${esc(n.id)}">${esc(n.title)}</button>${manual}${via}</li>`;
    });
  return `<ul class="deps">${items.join('')}</ul>`;
}

function declList(keys) {
  if (!keys.length) return '<p class="muted">None.</p>';
  return `<ul class="deps">${keys.slice().sort().map((k) =>
    `<li><button type="button" data-goto-decl="${esc(k)}"><code>${esc(k)}</code></button></li>`).join('')}</ul>`;
}

function nodeButtons(ids) {
  if (!ids.length) return '';
  return `<ul class="deps">${ids.map((i) => state.byId.get(i)).filter(Boolean)
    .sort((a, b) => a.title.localeCompare(b.title))
    .map((n) => `<li><button type="button" data-goto="${esc(n.id)}">${esc(n.title)}</button></li>`).join('')}</ul>`;
}

function openPanel(html) {
  const body = $('panel-body');
  body.innerHTML = html;
  $('panel').hidden = false;
  $('panel').scrollTop = 0;
  renderMath(body);
  return body;
}

function hidePanel() {
  $('panel').hidden = true;
}

/** The panel of a node: statement, documentation, proof, links, neighbours, supporting lemmas. */
function showPanel(id, { insideButton = false } = {}) {
  const n = state.byId.get(id);
  if (!n) { hidePanel(); return; }
  const L = n.lean;
  const parts = [];
  parts.push(`<h2>${esc(n.title)}</h2>`);
  const statusText = { proved: n.kind === 'definition' ? 'formalized' : 'proved', sorry: '⚠ sorry',
    planned: 'planned', informal: 'informal' }[n.status] || n.status;
  parts.push(`<div class="badges"><span class="badge">${esc(n.kind)}</span>` +
    `<span class="badge ${esc(n.status)}">${esc(statusText)}</span>` +
    [n.group, ...(n.also_in || [])].map((g) => `<span class="badge">${esc(state.groupTitle.get(g) || g)}</span>`).join('') +
    (n.level === 2 ? '<span class="badge">detail</span>' : '') + '</div>');
  if (n.example_of && state.byId.has(n.example_of)) {
    parts.push(`<p class="example-of">Example of <button type="button" data-goto="${esc(n.example_of)}">${esc(state.byId.get(n.example_of).title)}</button></p>`);
  }
  if (insideButton && hasInside(n)) {
    parts.push(`<p><button type="button" class="inside-btn" data-inside="${esc(n.id)}">Look inside</button></p>`);
  }
  if (L) {
    parts.push(`<div class="lean-name">${esc(L.name)}<button type="button" data-copy="${esc(L.name)}">copy</button></div>`);
  }
  const usesE = state.out.get(id) || [], usedE = state.inc.get(id) || [];
  parts.push(`<h3>Uses (${usesE.length})</h3>${depList(usesE, 'target')}`);
  parts.push(`<h3>Used by (${usedE.length})</h3>${depList(usedE, 'source')}`);
  const exs = (state.examples.get(id) || []);
  if (exs.length) parts.push(`<h3>Examples (${exs.length})</h3>${nodeButtons(exs.map((x) => x.id))}`);
  if (n.statement_tex) parts.push(`<h3>Statement</h3><div class="statement">${esc(n.statement_tex)}</div>`);
  if (L && L.signature) {
    parts.push(n.statement_tex
      ? `<details class="proof"><summary>Lean statement</summary><pre>${esc(L.signature)}</pre></details>`
      : `<h3>Lean statement</h3><pre>${esc(L.signature)}</pre>`);
  }
  if (L && L.docstring) parts.push(`<h3>Documentation</h3><div class="doc">${markdown(L.docstring)}</div>`);
  if (L) {
    const where = L.source ? `${L.source.file}, lines ${L.source.line_start}–${L.source.line_end}` : '';
    const links = [sourceLink(L.source_url, 'Source on GitHub', L.links_public),
      sourceLink(L.docgen_url, 'Documentation', true)].filter(Boolean).join('');
    if (L.source_text) {
      parts.push(`<details class="proof"><summary>Proof (Lean source, ${lineCount(L.source)} lines)</summary>` +
        `<pre>${esc(L.source_text)}</pre></details>`);
    } else if (L.source) {
      parts.push(`<h3>Proof</h3><p class="muted">${esc(where)} (${lineCount(L.source)} lines)</p>`);
    }
    if (links) parts.push(`<div class="links">${links}</div>`);
    if (L.axioms) {
      const extra = L.axioms.filter((a) => !STANDARD_AXIOMS.includes(a));
      parts.push(extra.length
        ? `<p class="warn">Rests on axioms beyond the standard three: ${extra.map((a) => `<code>${esc(a)}</code>`).join(', ')}</p>`
        : '<p class="muted">Axioms: only the standard ones (<code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>).</p>');
    }
  }
  if (L && L.supporting && L.supporting.length) {
    parts.push(`<details class="supporting" id="supporting"><summary>Supporting declarations ` +
      `(${L.supporting.length}): the declarations of the project on the way</summary>` +
      `<ul class="supporting-list"></ul></details>`);
  }
  if (n.refs && n.refs.length) {
    parts.push(`<h3>References</h3><ul>${n.refs.map((r) => `<li>${esc(r)}</li>`).join('')}</ul>`);
  }
  const body = openPanel(parts.join(''));
  const sup = body.querySelector('#supporting');
  if (sup) {
    sup.addEventListener('toggle', () => {
      const ul = sup.querySelector('ul');
      if (!sup.open || ul.childElementCount) return;
      ul.innerHTML = L.supporting.map((key) => supportingItem(key)).join('');
      renderMath(ul);
    });
  }
}

function supportingItem(key) {
  const s = state.data.declarations[key] || { name: key, keyword: '' };
  const first = s.docstring ? s.docstring.split(/\n\s*\n/)[0] : '';
  const loc = s.source ? `${s.module}, line ${s.source.line_start}` : (s.module || '');
  return `<li><div class="name">${sourceLink(s.source_url, s.name, s.links_public) || esc(s.name)}</div>` +
    `<div class="loc">${esc(s.keyword)} · ${esc(loc)}</div>` +
    (first ? `<div class="sdoc">${markdown(first)}</div>` : '') + '</li>';
}

/** The panel of a supporting declaration. */
function showDeclPanel(key) {
  const d = state.data.declarations[key];
  if (!d) { hidePanel(); return; }
  const users = state.declUsers.get(key) || { decls: [], nodes: [] };
  const parts = [];
  parts.push(`<h2 class="decl-title">${esc(shortName(d.name))}</h2>`);
  parts.push(`<div class="badges"><span class="badge">${esc(d.keyword)}</span><span class="badge">supporting</span></div>`);
  parts.push(`<div class="lean-name">${esc(d.name)}<button type="button" data-copy="${esc(d.name)}">copy</button></div>`);
  const usesNodes0 = d.uses_nodes || [], usesDecls0 = d.uses || [];
  parts.push(`<h3>Uses (${usesNodes0.length + usesDecls0.length})</h3>${usesNodes0.length ? nodeButtons(usesNodes0) : ''}${declList(usesDecls0)}`);
  parts.push(`<h3>Used by (${users.nodes.length + users.decls.length})</h3>${users.nodes.length ? nodeButtons(users.nodes) : ''}${declList(users.decls)}`);
  if (d.docstring) parts.push(`<h3>Documentation</h3><div class="doc">${markdown(d.docstring)}</div>`);
  else parts.push('<p class="muted">No docstring.</p>');
  if (d.source) {
    parts.push(`<p class="muted">${esc(d.module)}, lines ${d.source.line_start}–${d.source.line_end} (${lineCount(d.source)} lines)</p>`);
  }
  const link = sourceLink(d.source_url, 'Source on GitHub', d.links_public);
  if (link) parts.push(`<div class="links">${link}</div>`);
  openPanel(parts.join(''));
}

function onPanelClick(ev) {
  const inside = ev.target.closest('[data-inside]');
  if (inside && hooks.inside) { hooks.inside(inside.dataset.inside); return; }
  const go = ev.target.closest('[data-goto]');
  if (go) { hooks.goto(go.dataset.goto); return; }
  const gd = ev.target.closest('[data-goto-decl]');
  if (gd) { hooks.gotoDecl(gd.dataset.gotoDecl); return; }
  const copy = ev.target.closest('[data-copy]');
  if (copy && navigator.clipboard) {
    navigator.clipboard.writeText(copy.dataset.copy).then(() => {
      copy.textContent = 'copied';
      setTimeout(() => { copy.textContent = 'copy'; }, 1200);
    }, () => {});
  }
}

// ---------------------------------------------------------------- search

/** Subsequence match: every character of the query in order; earlier and tighter is better. */
function fuzzyScore(query, text) {
  const q = query.toLowerCase(), t = text.toLowerCase();
  const direct = t.indexOf(q);
  if (direct >= 0) return 1000 - direct;
  let pos = -1, gaps = 0;
  for (const ch of q) {
    const next = t.indexOf(ch, pos + 1);
    if (next < 0) return -1;
    gaps += next - pos - 1;
    pos = next;
  }
  return 500 - gaps;
}

function initSearch(onPick) {
  const input = $('search');
  const list = $('search-results');
  let hits = [];
  let active = 0;
  const show = (html) => {
    list.innerHTML = html;
    list.hidden = false;
    input.setAttribute('aria-expanded', 'true');
  };
  /** Every node, by group in the order of the node list, examples under their result. */
  const index = () => {
    hits = [];
    const rows = [];
    const row = (n, depth) => {
      const i = hits.push(n) - 1;
      rows.push(`<li role="option" data-i="${i}" class="${levelOf(n) === 2 ? 'lvl2' : ''}" style="padding-left: ${10 + 16 * depth}px">${esc(n.title)}</li>`);
    };
    const below = (n, depth) => {
      if (!currentProfile().nest_examples) return;
      for (const ex of (state.examples.get(n.id) || [])) {
        row(ex, depth);
        below(ex, depth + 1);
      }
    };
    for (const g of state.data.groups) {
      // a node of two groups (`also_in`) is listed under both
      const members = state.data.nodes.filter((n) => (n.group === g.id || (n.also_in || []).includes(g.id)) && !isNested(n))
        .sort((a, b) => (levelOf(a) - levelOf(b)) || a.title.localeCompare(b.title));
      if (!members.length) continue;
      rows.push(`<li class="index-group" aria-disabled="true">${esc(g.title)}</li>`);
      for (const n of members) { row(n, 0); below(n, 1); }
    }
    active = -1;
    show(rows.join(''));
  };
  const update = () => {
    const q = input.value.trim();
    if (!q) { index(); return; }
    hits = state.data.nodes
      .map((n) => ({ n, s: Math.max(fuzzyScore(q, n.title), n.lean ? fuzzyScore(q, n.lean.name) - 50 : -1) }))
      .filter((h) => h.s >= 0)
      .sort((a, b) => b.s - a.s)
      .slice(0, 10)
      .map((h) => h.n);
    active = 0;
    show(hits.length
      ? hits.map((n, i) => `<li role="option" data-i="${i}" aria-selected="${i === 0}">${esc(n.title)}` +
          (n.lean ? `<span class="sub">${esc(n.lean.name)}</span>` : '') + '</li>').join('')
      : '<li class="muted">No match</li>');
  };
  const pick = (i) => {
    const n = hits[i];
    if (!n) return;
    input.value = '';
    list.hidden = true;
    input.blur();
    onPick(n.id);
  };
  input.addEventListener('input', update);
  input.addEventListener('focus', update);
  input.addEventListener('keydown', (ev) => {
    if (ev.key === 'ArrowDown' || ev.key === 'ArrowUp') {
      if (!hits.length) return;
      ev.preventDefault();
      active = ((active < 0 ? -1 : active) + (ev.key === 'ArrowDown' ? 1 : hits.length - 1)) % hits.length;
      list.querySelectorAll('li[data-i]').forEach((li) => li.setAttribute('aria-selected', String(+li.dataset.i === active)));
      const cur = list.querySelector(`li[data-i="${active}"]`);
      if (cur && cur.scrollIntoView) cur.scrollIntoView({ block: 'nearest' });
    } else if (ev.key === 'Enter') {
      ev.preventDefault();
      pick(Math.max(0, active));
    }
  });
  list.addEventListener('mousedown', (ev) => {
    const li = ev.target.closest('li[data-i]');
    if (li) { ev.preventDefault(); pick(+li.dataset.i); }
  });
  input.addEventListener('blur', () => setTimeout(() => { list.hidden = true; }, 150));
  return { clear: () => { input.value = ''; update(); } };
}

// ---------------------------------------------------------------- header and address

function header() {
  const { meta, nodes } = state.data;
  document.title = meta.title || 'Knowledge graph';
  $('title').textContent = meta.title || 'Knowledge graph';
  const src = meta.source || {};
  const short = src.commit ? src.commit.slice(0, 7) : '';
  const commit = short && src.repo
    ? sourceLink(`${src.repo}/commit/${src.commit}`, short, meta.public_source_links) : esc(short);
  const date = meta.generated_at ? meta.generated_at.slice(0, 10) : '';
  const lean = nodes.filter((n) => n.lean);
  const proved = lean.filter((n) => n.status === 'proved').length;
  $('provenance').innerHTML =
    `Generated from ${esc(src.name || 'the project')}${short ? ` @ ${commit}` : ''}` +
    `${src.dirty ? ' (with uncommitted changes)' : ''}${date ? ` on ${esc(date)}` : ''}` +
    ` · ${proved} of ${lean.length} Lean nodes without sorry` +
    (nodes.length > lean.length ? ` · ${nodes.length - lean.length} informal or planned` : '');
  // the switch between profiles (node lists), when there is more than one
  const ps = state.data.meta.profiles;
  const sw = $('profile-switch');
  if (sw && ps.length > 1) {
    sw.innerHTML = `<label>Node list <select id="profile">${ps.map((p) =>
      `<option value="${esc(p.id)}"${p.id === state.profile ? ' selected' : ''}>${esc(p.title)}</option>`).join('')}</select></label>`;
    sw.querySelector('select').addEventListener('change', (ev) => {
      const q = new URLSearchParams(location.search);
      q.set('profile', ev.target.value);
      location.href = `${location.pathname}?${q}${location.hash}`;
    });
  }
  // the legend starts folded on narrow screens
  const legend = document.querySelector('details.legend');
  if (legend && window.innerWidth < 1100) legend.open = false;
  // the view links keep the data parameter and the address fragment
  document.querySelectorAll('a[data-view]').forEach((a) => {
    a.addEventListener('click', () => { a.href = a.getAttribute('data-view') + location.search + location.hash; });
  });
}

/** The address fragment as key/value pairs: node, focus, inside, module. */
function readHash() {
  const p = new URLSearchParams(location.hash.slice(1));
  const out = {};
  for (const k of ['node', 'focus', 'inside', 'module', 'part', 'group']) if (p.get(k)) out[k] = p.get(k);
  if (out.group && !state.groupTitle.has(out.group)) delete out.group;
  if (out.node && !state.byId.has(out.node)) delete out.node;
  if (out.focus && !state.byId.has(out.focus)) delete out.focus;
  if (out.inside && !state.byId.has(out.inside)) delete out.inside;
  return out;
}

/** Writes the address fragment; `push` makes a new entry of the browser's history (a change of
 * level), so that its back button goes back a level. */
function writeHash(obj, { push = false } = {}) {
  const p = new URLSearchParams();
  for (const [k, v] of Object.entries(obj)) if (v) p.set(k, v);
  const h = p.toString() ? '#' + p.toString() : '';
  if (location.hash === h) return;
  const url = h || location.pathname + location.search;
  if (push) history.pushState(null, '', url); else history.replaceState(null, '', url);
}

/** Wires the parts every view has: panel clicks, close button, search, details toggle, keys. */
function initCommon({ onPick, onEscape, onDetails }) {
  $('panel').addEventListener('click', onPanelClick);
  const search = initSearch(onPick);
  window.addEventListener('popstate', () => { if (hooks.popstate) hooks.popstate(readHash()); });
  $('details').addEventListener('change', (ev) => { state.showDetails = ev.target.checked; onDetails(); });
  document.addEventListener('keydown', (ev) => {
    const typing = ev.target instanceof HTMLInputElement || ev.target instanceof HTMLTextAreaElement;
    if (ev.key === '/' && !typing) { ev.preventDefault(); $('search').focus(); }
    else if (ev.key === 'Escape') {
      if (typing && $('search').value) search.clear();
      else { $('search').blur(); onEscape(); }
    }
  });
}

function librariesLoaded() {
  if (typeof cytoscape !== 'function') {
    setStatus('The graph library could not be loaded (Cytoscape.js, from a CDN).', true);
    return false;
  }
  return true;
}

/** A promise that resolves after `ms` milliseconds. */
const wait = (ms) => new Promise((r) => setTimeout(r, ms));

// ---------------------------------------------------------------- touchpad and mouse wheel

/**
 * Two fingers on a touchpad move the picture, spreading them zooms (browsers report a pinch
 * as a wheel event with ctrlKey, Safari as gesture events); a mouse wheel zooms. Cytoscape
 * alone zooms on every wheel event, so ours runs first, in the capture phase on the parent.
 */
function touchpad(cy) {
  const box = cy.container();
  if (!box || !box.parentElement) return; // headless, as in the tests
  const host = box.parentElement;
  const clampZoom = (z) => Math.min(cy.maxZoom(), Math.max(cy.minZoom(), z));
  const at = (e) => {
    const r = box.getBoundingClientRect();
    return { x: e.clientX - r.left, y: e.clientY - r.top };
  };
  let lastTouchpad = -Infinity;
  host.addEventListener('wheel', (e) => {
    if (!box.contains(e.target)) return;
    e.preventDefault();
    e.stopPropagation();
    const unit = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? box.clientHeight : 1;
    const dx = e.deltaX * unit, dy = e.deltaY * unit;
    // A mouse wheel moves in whole notches (100, 120 or 125 pixels) and never sideways; a
    // touchpad sends small, fractional or sideways steps, and a fast swipe right after them.
    const now = performance.now();
    if (e.deltaMode === 0 && (e.deltaX !== 0 || !Number.isInteger(e.deltaY) || Math.abs(e.deltaY) < 50)) lastTouchpad = now;
    const notch = [100, 120, 125].some((n) => Math.abs(dy) % n === 0);
    const wheel = e.deltaMode !== 0 ||
      (now - lastTouchpad > 800 && e.deltaX === 0 && Math.abs(dy) >= 50 && Number.isInteger(dy) && notch);
    if (e.ctrlKey || wheel) {
      const factor = Math.exp(-dy * (e.ctrlKey ? 0.012 : 0.0018));
      cy.zoom({ level: clampZoom(cy.zoom() * factor), renderedPosition: at(e) });
    } else {
      cy.panBy({ x: -dx, y: -dy });
    }
  }, { passive: false, capture: true });
  for (const legacy of ['mousewheel', 'DOMMouseScroll']) {
    host.addEventListener(legacy, (e) => { if (box.contains(e.target)) { e.preventDefault(); e.stopPropagation(); } },
      { passive: false, capture: true });
  }
  let startZoom = 1;
  host.addEventListener('gesturestart', (e) => { e.preventDefault(); startZoom = cy.zoom(); }, { capture: true });
  host.addEventListener('gesturechange', (e) => {
    e.preventDefault();
    cy.zoom({ level: clampZoom(startZoom * e.scale), renderedPosition: at(e) });
  }, { capture: true });
}

// ---------------------------------------------------------------- hover titles

/**
 * Shows the full title of the node under the pointer in large type next to it, so that a
 * block can be read before zooming in. Elements carry the text in `data.title`.
 */
function hoverTitles(cy) {
  const box = cy.container();
  if (!box || !box.parentElement) return;
  const tip = document.createElement('div');
  tip.className = 'hover-title';
  tip.hidden = true;
  box.parentElement.appendChild(tip);
  const place = (p) => {
    const x = Math.min(p.x + 18, box.clientWidth - tip.offsetWidth - 8);
    const y = p.y + 22 + tip.offsetHeight > box.clientHeight ? p.y - tip.offsetHeight - 14 : p.y + 22;
    tip.style.left = `${Math.max(8, x)}px`;
    tip.style.top = `${Math.max(8, y)}px`;
  };
  cy.on('mouseover', 'node', (ev) => {
    const t = ev.target.data('title');
    if (!t) return;
    tip.textContent = t;
    tip.hidden = false;
    place(ev.renderedPosition || ev.target.renderedPosition());
  });
  cy.on('mousemove', (ev) => { if (!tip.hidden && ev.renderedPosition) place(ev.renderedPosition); });
  cy.on('mouseout', 'node', () => { tip.hidden = true; });
  cy.on('viewport tapstart', () => { tip.hidden = true; });
}

// ---------------------------------------------------------------- rings

/*
 * Placing boxes on concentric rings without collisions, shared by the views Rings and Cells.
 * Every ring gets the smallest radius at which none of its boxes touches another box; a ring
 * with many boxes is spread over a few staggered rings.
 */
const TAU = 2 * Math.PI;
const RING_GAP = 34;      // arc length between neighbouring boxes on a ring
const RING_MARGIN = 12;   // free space around every box
const SUB_RING = 560;     // a ring that would need a larger radius is split

const boxAt = (n, r, a) => {
  const x = r * Math.cos(a), y = r * Math.sin(a);
  const m = RING_MARGIN / 2;
  return { x1: x - n.w / 2 - m, x2: x + n.w / 2 + m, y1: y - n.h / 2 - m, y2: y + n.h / 2 + m };
};
const boxesHit = (a, b) => a.x1 < b.x2 && b.x1 < a.x2 && a.y1 < b.y2 && b.y1 < a.y2;

function collides(boxes, placed) {
  for (let i = 0; i < boxes.length; i++) {
    for (const p of placed) if (boxesHit(boxes[i], p)) return true;
    for (let j = i + 1; j < boxes.length; j++) if (boxesHit(boxes[i], boxes[j])) return true;
  }
  return false;
}

/**
 * The smallest radius from `r0` on (in steps of 10) at which `place(r)` gives no collision and
 * every box passes `fits` (by default every box does).
 */
function searchRadius(r0, place, placed, fits = () => true) {
  let r = r0;
  for (let i = 0; i < 800; i++, r += 10) {
    const boxes = place(r);
    if (!collides(boxes, placed) && boxes.every(fits)) return { r, boxes };
  }
  return { r, boxes: place(r) };
}

/** The distance from the centre to the nearest and to the farthest point of a box. */
const nearestOf = (b) => Math.hypot(Math.max(b.x1, 0, -b.x2), Math.max(b.y1, 0, -b.y2));
const farthestOf = (b) => Math.hypot(Math.max(Math.abs(b.x1), Math.abs(b.x2)), Math.max(Math.abs(b.y1), Math.abs(b.y2)));

/** Sorts nodes by the mean angle of their neighbours already placed (barycentre heuristic). */
function byBarycentre(nodes, neighbours, angle, from) {
  const key = (n) => {
    const as = (neighbours.get(n.id) || []).filter((m) => angle.has(m)).map((m) => {
      let a = angle.get(m) - from;
      while (a < 0) a += TAU;
      while (a >= TAU) a -= TAU;
      return a;
    });
    return as.length ? as.reduce((s, a) => s + a, 0) / as.length : TAU;
  };
  return nodes.map((n) => [key(n), n]).sort((x, y) => x[0] - y[0]).map((x) => x[1]);
}

/**
 * The inside of a result on rings: the result (`kind` root) in the centre; around it the
 * lemmas or files (`decl`, `module`) it uses directly, then those they use, by shortest
 * distance; without a root, the items that nothing else uses come first. Everything else
 * (portals, neighbouring files) goes outside. Edges point from what is used to what uses it.
 * Returns the place { r, a, ring } of every node and the radii of the rings.
 */
function ringLayout(nodes, edges) {
  const isInner = (n) => n.kind === 'decl' || n.kind === 'module';
  const byId = new Map(nodes.map((n) => [n.id, n]));
  const usedBy = new Map(nodes.map((n) => [n.id, []]));
  const uses = new Map(nodes.map((n) => [n.id, []]));
  for (const e of edges) {
    if (usedBy.has(e.source)) usedBy.get(e.source).push(e.target);
    if (uses.has(e.target)) uses.get(e.target).push(e.source);
  }
  const root = nodes.find((n) => n.kind === 'root');
  const ring = new Map();
  const queue = [];
  if (root) { ring.set(root.id, 0); queue.push(root.id); }
  else {
    for (const n of nodes) {
      if (isInner(n) && !usedBy.get(n.id).some((m) => isInner(byId.get(m)))) { ring.set(n.id, 1); queue.push(n.id); }
    }
  }
  while (queue.length) {
    const v = queue.shift();
    for (const w of uses.get(v)) {
      if (!ring.has(w) && isInner(byId.get(w))) { ring.set(w, ring.get(v) + 1); queue.push(w); }
    }
  }
  let maxRing = 1;
  for (const n of nodes) if (isInner(n) && ring.has(n.id)) maxRing = Math.max(maxRing, ring.get(n.id));
  for (const n of nodes) if (isInner(n) && !ring.has(n.id)) ring.set(n.id, maxRing + 1);
  maxRing = Math.max(1, ...nodes.filter(isInner).map((n) => ring.get(n.id)));
  for (const n of nodes) if (!isInner(n) && n !== root) ring.set(n.id, maxRing + 1);
  return placeOnRings(nodes, edges, ring, root);
}

/**
 * Places nodes on the rings given by `ring` (id → 1, 2, ...), `root` (if any) in the centre;
 * within a ring by the barycentre of the neighbours already placed, every ring at the smallest
 * radius free of collisions. Returns the place { r, a, ring } of every node and the radii.
 */
function placeOnRings(nodes, edges, ring, root = null) {
  const usedBy = new Map(nodes.map((n) => [n.id, []]));
  for (const e of edges) if (usedBy.has(e.source)) usedBy.get(e.source).push(e.target);
  const targets = new Map();
  const angle = new Map();
  const placed = [];
  const radii = [];
  if (root) {
    targets.set(root.id, { r: 0, a: 0, ring: 0 });
    angle.set(root.id, 0);
    placed.push(boxAt(root, 0, 0));
  }
  let prevR = 0;
  const maxK = Math.max(0, ...nodes.filter((n) => n !== root).map((n) => ring.get(n.id) || 0));
  for (let k = 1; k <= maxK; k++) {
    const members = nodes.filter((n) => n !== root && ring.get(n.id) === k);
    if (!members.length) continue;
    const ordered = k === 1 && !root ? members : byBarycentre(members, usedBy, angle, -Math.PI / 2);
    const m = ordered.length;
    const total = ordered.reduce((s, n) => s + n.w + RING_GAP, 0);
    const parts = Math.max(1, Math.ceil(total / (TAU * SUB_RING)));
    const angleOf = (i) => -Math.PI / 2 + (i + 0.5) / m * TAU;
    ordered.forEach((n, i) => angle.set(n.id, angleOf(i)));
    for (let j = 0; j < parts; j++) {
      const sub = ordered.map((n, i) => [n, i]).filter(([, i]) => i % parts === j);
      const r0 = Math.max(prevR + 30, sub.reduce((s, [n]) => s + n.w + RING_GAP, 0) / TAU);
      const res = searchRadius(r0, (r) => sub.map(([n, i]) => boxAt(n, r, angleOf(i))), placed);
      for (const [n, i] of sub) targets.set(n.id, { r: res.r, a: angleOf(i), ring: k });
      placed.push(...res.boxes);
      radii.push(res.r);
      prevR = res.r;
    }
  }
  return { targets, radii };
}

const rings = { TAU, RING_GAP, RING_MARGIN, boxAt, collides, searchRadius, nearestOf, farthestOf, byBarycentre,
  ringLayout, placeOnRings };

return {
  state, hooks, $, setStatus, loadData, dependencyClosure, visibleGraph, depths, hasInside,
  insideView, shortName, moduleTail, wrap, textWidth, nodeBox, identBox, nodeLabel, nodeType, boxFor,
  levelOf, shownLevel, isNested, examplesOf, importance, currentProfile, TYPE, fontOf, cssVar, groupColor, colourSlot,
  shapeStyle, esc, markdown, renderMath, showPanel, showDeclPanel, hidePanel, header, readHash,
  writeHash, initCommon, librariesLoaded, wait, touchpad, hoverTitles, rings, FONT_FAMILY, NODE_FONT,
  SMALL_FONT, GROUP_FONT, LINE_HEIGHT, REDUCED_MOTION,
};

})();
