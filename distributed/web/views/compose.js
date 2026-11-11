// Compose: pick or start a scenario, shape its network on the diagram (sites, nodes, links, home routers), set the
// stacks, the workload and the fault schedule, see every problem before a run, save the file, run it.
import { h, clear, api, toast, numField, textField, selectField } from "../lib/dom.js";
import { Topo } from "../lib/topo.js";
import { STACKS } from "../lib/fmt.js";

const NATS = [["none", "routed"], ["port-restricted", "home router, port-restricted"], ["symmetric", "home router, symmetric"]];
const ROLES = [["peer", "peer"], ["hub", "hub"], ["relay", "relay"]];
const TESTS = {
  setup: { label: "connection setup", params: [["count", "connections", ""]], init: { count: 20 } },
  resume: { label: "resumed setup", params: [["count", "connections", ""]], init: { count: 20 } },
  latency: { label: "request latency", params: [["size", "size", "B"], ["round_trips", "round trips", ""]], init: { size: 64, round_trips: 200 } },
  throughput: { label: "throughput", params: [["bytes", "bytes", "B"], ["streams", "streams", ""]], init: { bytes: 16777216, streams: 1 } },
  many: { label: "many connections", params: [["connections", "clients", ""], ["bytes_each", "bytes each", "B"]], init: { connections: 200, bytes_each: 65536 } },
};
const KINDS = [["transport", "Transport tests"], ["pubsub", "Publish and subscribe"], ["sync", "Sync a value"], ["reconcile", "Reconcile sets"]];
const HINTS = {
  transport: "Transport tests: the comparison benches' scenarios between a client and a server node; each pair runs every test, every stack, every repetition.",
  pubsub: "Every node joins the topic through the hubs; the publishers send at their rate and the subscribers' deliveries are counted: latency, losses, duplicates, bytes on the wire.",
  sync: "The providers hold a value of each size in turn; the consumers fetch it at once. Time, goodput and bytes on the wire per payload byte.",
  reconcile: "Two nodes hold sets of the same size that differ in a few items on each side; the second starts the round. Only stacks with a reconciliation protocol are measured.",
};
// What a workload of each kind starts as, from the names of the nodes.
const WORKLOADS = {
  transport: (n) => ({ kind: "transport", timeout_s: 300, pairs: [{ client: n[0] || "", server: n[1] || "" }], tests: [{ test: "setup", count: 20 }] }),
  pubsub: (n) => ({ kind: "pubsub", topic: "bench", publishers: n[0] ? [n[0]] : [], subscribers: [], messages: 1000, size: 256, rate_hz: 50, join_s: 30, warmup_s: 5, drain_s: 5 }),
  sync: (n) => ({ kind: "sync", providers: n[0] ? [n[0]] : [], consumers: n[1] ? [n[1]] : [], sizes: [1048576], timeout_s: 300, warmup_s: 5 }),
  reconcile: (n) => ({ kind: "reconcile", a: n[0] || "", b: n[1] || "", items: [1000], differences: [10], timeout_s: 120, warmup_s: 5 }),
};
const FAULTS = {
  set: "reshape a link", cut: "cut a link", restore: "restore a link", partition: "partition a site", heal: "heal a site",
  pause: "pause a node", resume: "resume a node", kill: "kill a node", restart: "restart a node",
};

function template() {
  const lan = { delay_ms: 0.05, jitter_ms: 0, loss_pct: 0, rate_mbit: 1000 };
  return {
    name: "new-scenario", about: "", stacks: [...STACKS], repetitions: 3, resources: { cpus: 2, memory_mib: 2048 },
    sites: [{ name: "a", nat: "none", lan: { ...lan }, pos: [160, 200] }, { name: "b", nat: "none", lan: { ...lan }, pos: [560, 200] }],
    nodes: [{ name: "n1", site: "a", count: 1, role: "peer" }, { name: "n2", site: "b", count: 1, role: "peer" }],
    links: [{ a: "a", b: "b", shape: { delay_ms: 10, jitter_ms: 0, loss_pct: 0, rate_mbit: 100 } }],
    workload: { kind: "transport", timeout_s: 300, pairs: [{ client: "n1", server: "n2" }], tests: [{ test: "setup", count: 20 }] },
    faults: [],
  };
}

// The nodes of the scenario with groups expanded, named as the harness names them (Scenario::expand).
function expand(sc) {
  const idx = new Map(sc.sites.map((s, i) => [s.name, i]));
  const out = [];
  sc.nodes.forEach((g, gi) => {
    if (!idx.has(g.site)) return;
    const n = Math.max(0, g.count ?? 1);
    for (let i = 1; i <= n; i++) out.push({ name: n === 1 ? g.name : `${g.name}-${i}`, site: idx.get(g.site), role: g.role || "peer", group: gi });
  });
  return out;
}

function patched(base, p) { return p ? { ...base, ...Object.fromEntries(Object.entries(p).filter(([, v]) => v !== undefined && v !== null)) } : base; }

function model(sc) {
  const idx = new Map(sc.sites.map((s, i) => [s.name, i]));
  return {
    sites: sc.sites.map((s, i) => ({ name: s.name, nat: s.nat, pos: s.pos, lan: `10.${i + 1}.0.0/24` })),
    nodes: expand(sc),
    links: sc.links.filter((l) => idx.has(l.a) && idx.has(l.b)).map((l) => ({ a: idx.get(l.a), b: idx.get(l.b), forward: l.shape || {}, reverse: patched(l.shape || {}, l.reverse) })),
  };
}

let st = null;

export function mount(el, ctx) {
  st = { ctx, list: [], file: null, sc: null, dirty: false, sel: null, problems: [], plan: null, toml: "", dock: "workload", timer: 0 };
  const listBody = h("div", { class: "list" });
  const listPane = h("aside", { class: "pane", "aria-label": "Scenarios" },
    h("div", { class: "pane-head" }, h("h2", {}, "Scenarios"),
      h("button", { class: "btn", type: "button", onclick: () => openScenario(null) }, "New")),
    listBody);
  const topoBox = h("div", { class: "topo" });
  const legend = h("div", { class: "legend" },
    h("span", {}, h("i", {}), "link"), h("span", {}, h("i", { class: "nat" }), "home router"),
    h("span", {}, "drag a site to move it; click to edit"));
  topoBox.append(legend);
  const toolbar = h("div", { class: "toolbar" });
  const dock = h("div", { class: "dock" });
  const center = h("section", { class: "pane compose-center", style: { gridTemplateRows: "auto minmax(260px, 1fr) auto" } }, toolbar, topoBox, dock);
  const inspector = h("aside", { class: "pane inspector", "aria-label": "Inspector" });
  el.append(h("div", { class: "view compose" }, listPane, center, inspector));
  st.el = { listBody, toolbar, dock, inspector, topoBox };
  st.topo = new Topo(topoBox, {
    editable: true,
    onSelect: (sel) => { st.sel = sel.kind === "node" ? { kind: "group", index: expand(st.sc)[sel.index]?.group } : sel; drawTopo(); drawInspector(); },
    onMove: (i, pos) => { st.sc.sites[i].pos = pos; changed({ topo: true }); },
  });
  loadList();
}

export function unmount() {
  clearTimeout(st?.timer);
  st = null;
}

async function loadList(select) {
  try {
    st.list = await api("/api/scenarios");
  } catch (e) {
    st.list = [];
    toast(`The scenarios could not be listed: ${e.message}`, true);
  }
  drawList();
  const pick = select || st.file || st.list.find((x) => x.name)?.file;
  if (!st.sc && pick) openScenario(pick);
  else if (!st.sc) openScenario(null);
}

function drawList() {
  const L = clear(st.el.listBody);
  if (!st.list.length) {
    L.append(h("div", { class: "empty" }, h("strong", {}, "No scenario files yet"), "Press New to start one."));
    return;
  }
  for (const x of st.list) {
    const bad = x.error || (x.problems && x.problems.length);
    L.append(h("button", {
      class: "item", type: "button", "aria-current": x.file === st.file ? "true" : "false",
      onclick: () => confirmLeave() && openScenario(x.file),
    },
    h("div", { class: "item-top" }, h("span", { class: "item-name" }, x.name || x.file), h("span", { class: "spacer" }),
      bad ? h("span", { class: "chip bad glyph-bad", title: "has problems" }) : null),
    x.error ? h("div", { class: "item-about" }, x.error) : h("div", { class: "item-about" }, x.about || "No description."),
    x.error ? null : h("div", { class: "item-meta" }, `${x.sites} site${x.sites === 1 ? "" : "s"} · ${x.nodes} node${x.nodes === 1 ? "" : "s"} · ${x.stacks.join(", ")} · ${x.repetitions}×`)));
  }
}

function confirmLeave() {
  return !st.dirty || window.confirm("This scenario has unsaved changes. Leave them?");
}

async function openScenario(file) {
  if (!st) return;
  if (file) {
    try {
      const d = await api(`/api/scenarios/${encodeURIComponent(file)}`);
      if (!d.scenario) {
        toast(`${file}.toml cannot be read: ${d.error}`, true);
        return;
      }
      st.sc = d.scenario;
      st.toml = d.toml;
    } catch (e) {
      toast(e.message, true);
      return;
    }
  } else {
    st.sc = template();
  }
  st.sc.faults ||= [];
  st.sc.links ||= [];
  st.file = file;
  st.dirty = !file;
  st.sel = null;
  drawList();
  drawAll();
  validate();
}

function drawAll() {
  drawToolbar();
  drawTopo();
  drawInspector();
  drawDock();
}

function drawTopo() {
  // A selected node group is shown by the inspector; the diagram marks sites and links.
  st.topo.render(model(st.sc), st.sel && st.sel.kind !== "group" ? st.sel : null);
}

function changed({ topo = true, inspector = false, dock = false } = {}) {
  st.dirty = true;
  if (topo) drawTopo();
  if (inspector) drawInspector();
  if (dock) drawDock();
  drawToolbar();
  clearTimeout(st.timer);
  st.timer = setTimeout(validate, 300);
}

async function validate() {
  if (!st) return;
  try {
    const d = await api("/api/validate", { method: "POST", body: st.sc });
    if (!st) return;
    st.problems = d.problems || [];
    st.plan = d.plan || null;
    st.toml = d.toml || st.toml;
  } catch (e) {
    st.problems = [{ path: "", message: e.message }];
  }
  drawToolbar();
  drawProblems();
  if (st.dock === "file") drawDock();
}

function drawToolbar() {
  const T = clear(st.el.toolbar);
  const bad = st.problems.length;
  const running = st.ctx.store.running;
  T.append(
    h("strong", { class: "mono" }, `${st.sc.name}.toml`),
    st.dirty ? h("span", { class: "chip warn" }, "unsaved") : h("span", { class: "chip" }, "saved"),
    h("span", { class: "spacer" }),
    h("button", { class: "btn", type: "button", onclick: addSite }, "Add site"),
    h("button", { class: "btn", type: "button", onclick: addGroup }, "Add nodes"),
    h("button", { class: "btn", type: "button", onclick: addLink, disabled: st.sc.sites.length < 2 }, "Add link"),
    bad ? h("span", { class: "chip bad glyph-bad", title: "see the problems in the inspector" }, ` ${bad} problem${bad === 1 ? "" : "s"}`) : h("span", { class: "chip good glyph-good" }, " valid"),
    h("button", { class: "btn", type: "button", onclick: save }, "Save"),
    h("button", { class: "btn primary", type: "button", disabled: !!bad || running, title: running ? "a run is going" : "", onclick: run }, "Run"),
  );
}

function drawProblems() {
  const box = st.el.inspector.querySelector(".problems-box");
  if (!box) return;
  clear(box);
  if (!st.problems.length) {
    box.append(h("div", { class: "ok-line" }, h("span", { class: "glyph-good" }), "Ready to run"));
    return;
  }
  box.append(h("div", { class: "problems" }, st.problems.map((p) => h("div", { class: "problem" }, h("code", {}, p.path || "file"), h("span", {}, p.message)))));
}

function shapeFields(obj, { optional = false, onchange } = {}) {
  const o = { optional, onchange };
  return h("div", { class: "grid2" },
    numField("delay", obj, "delay_ms", { ...o, unit: "ms", min: 0 }),
    numField("jitter", obj, "jitter_ms", { ...o, unit: "ms", min: 0 }),
    numField("loss", obj, "loss_pct", { ...o, unit: "%", min: 0, max: 100 }),
    numField("rate", obj, "rate_mbit", { ...o, optional: true, unit: "Mbit/s", min: 0, placeholder: optional ? "" : "no limit" }),
    numField("buffer", obj, "queue_ms", { ...o, optional: true, unit: "ms of rate", min: 0, placeholder: optional ? "" : "50" }));
}

function renameEverywhere(kind, from, to) {
  const sc = st.sc;
  if (kind === "site") {
    sc.nodes.forEach((g) => { if (g.site === from) g.site = to; });
    sc.links.forEach((l) => { if (l.a === from) l.a = to; if (l.b === from) l.b = to; });
  }
  sc.faults.forEach((f) => { for (const k of ["a", "b", "site", "node"]) if (f.action[k] === from) f.action[k] = to; });
  if (kind === "node") {
    const w = sc.workload;
    (w.pairs || []).forEach((p) => { if (p.client === from) p.client = to; if (p.server === from) p.server = to; });
    for (const k of ["publishers", "subscribers", "providers", "consumers"]) if (w[k]) w[k] = w[k].map((x) => (x === from ? to : x));
    for (const k of ["a", "b"]) if (w[k] === from) w[k] = to;
  }
}

function drawInspector() {
  const I = clear(st.el.inspector);
  const sc = st.sc;
  const sel = st.sel;
  const sec = (title, ...kids) => h("section", {}, h("h3", {}, title), ...kids);
  I.append(h("div", { class: "pane-head" }, h("h2", {}, sel ? { site: "Site", group: "Nodes", link: "Link" }[sel.kind] : "Scenario"),
    sel ? h("button", { class: "btn", type: "button", onclick: () => { st.sel = null; drawTopo(); drawInspector(); } }, "Scenario settings") : null));
  const body = h("div", { class: "pane-body" });
  I.append(body);
  body.append(h("div", { class: "problems-box" }));
  if (!sel) {
    const stacks = h("div", { class: "row" }, STACKS.map((s) => h("label", { class: `row stack-${s}` },
      h("input", { type: "checkbox", style: { width: "auto", height: "auto" }, checked: sc.stacks.includes(s),
        onchange: (e) => { sc.stacks = STACKS.filter((x) => (x === s ? e.target.checked : sc.stacks.includes(x))); changed({ topo: false }); } }),
      h("span", { class: "swatch" }), s)));
    const nameField = textField("name", sc, "name", { onchange: () => changed({ topo: false }) });
    body.append(
      sec("About", nameField, textField("description", sc, "about", { onchange: () => changed({ topo: false }) })),
      sec("Stacks", stacks, h("p", { class: "hint" }, "They run one after the other on the same network, interleaved per repetition.")),
      sec("Each node gets", h("div", { class: "grid3" },
        numField("CPUs", sc.resources, "cpus", { min: 1, step: 1, onchange: () => changed({ topo: false }) }),
        numField("memory", sc.resources, "memory_mib", { unit: "MiB", min: 64, step: 64, onchange: () => changed({ topo: false }) }),
        numField("repetitions", sc, "repetitions", { min: 1, step: 1, onchange: () => changed({ topo: false }) }))),
    );
    if (st.plan) {
      body.append(sec("Plan", st.plan.shared_cpus ? h("p", { class: "chip warn" }, "nodes share CPUs: this machine has fewer than the scenario asks") : null,
        h("table", {}, h("thead", {}, h("tr", {}, h("th", {}, "node"), h("th", {}, "address"), h("th", {}, "CPUs"))),
          h("tbody", {}, st.plan.nodes.slice(0, 64).map((n) => h("tr", {}, h("td", {}, n.name), h("td", { class: "v" }, n.ip), h("td", { class: "v" }, n.cpus))))),
        st.plan.nodes.length > 64 ? h("p", { class: "hint" }, `and ${st.plan.nodes.length - 64} more`) : null));
    }
  } else if (sel.kind === "site") {
    const s = sc.sites[sel.index];
    if (!s) { st.sel = null; return drawInspector(); }
    const old = { name: s.name };
    body.append(
      sec("Site", textField("name", s, "name", { onchange: () => { renameEverywhere("site", old.name, s.name); old.name = s.name; changed(); } }),
        selectField("router", s.nat || "none", NATS, (v) => { s.nat = v; changed(); })),
      sec("Each node's access link", h("p", { class: "dir-head" }, "both directions"), shapeFields(s.lan, { onchange: () => changed() })),
      h("div", { class: "row" }, h("button", { class: "btn danger", type: "button", onclick: () => removeSite(sel.index) }, "Remove site, its nodes and links")),
    );
  } else if (sel.kind === "group") {
    const g = sc.nodes[sel.index];
    if (!g) { st.sel = null; return drawInspector(); }
    const old = { name: g.name };
    const patch = g.link || (g.link = {});
    body.append(
      sec("Nodes", textField("name", g, "name", { onchange: () => { renameEverywhere("node", old.name, g.name); old.name = g.name; changed(); } }),
        h("div", { class: "grid2" },
          selectField("site", g.site, sc.sites.map((s) => [s.name, s.name]), (v) => { g.site = v; changed(); }),
          numField("count", g, "count", { min: 1, step: 1, onchange: () => changed() })),
        selectField("role", g.role || "peer", ROLES, (v) => { g.role = v; changed(); }),
        h("p", { class: "hint" }, g.count > 1 ? `Named ${g.name}-1 to ${g.name}-${g.count}.` : "One node.")),
      sec("Access link changes", h("p", { class: "dir-head" }, "empty fields keep the site's"), shapeFields(patch, { optional: true, onchange: () => { if (!Object.keys(patch).length) delete g.link; changed(); } })),
      h("div", { class: "row" }, h("button", { class: "btn danger", type: "button", onclick: () => { sc.nodes.splice(sel.index, 1); st.sel = null; changed({ inspector: true, dock: true }); } }, "Remove these nodes")),
    );
  } else if (sel.kind === "link") {
    const l = sc.links[sel.index];
    if (!l) { st.sel = null; return drawInspector(); }
    const rev = l.reverse || (l.reverse = {});
    const names = sc.sites.map((s) => [s.name, s.name]);
    body.append(
      sec("Link", h("div", { class: "grid2" },
        selectField("from", l.a, names, (v) => { l.a = v; changed({ inspector: true }); }),
        selectField("to", l.b, names, (v) => { l.b = v; changed({ inspector: true }); }))),
      sec(`${l.a} → ${l.b}`, h("p", { class: "dir-head" }, "and back, unless changed below"), shapeFields(l.shape, { onchange: () => changed() })),
      sec(`${l.b} → ${l.a} changes`, h("p", { class: "dir-head" }, "empty fields keep the forward direction's"), shapeFields(rev, { optional: true, onchange: () => { if (!Object.keys(rev).length) delete l.reverse; changed(); } })),
      h("div", { class: "row" }, h("button", { class: "btn danger", type: "button", onclick: () => { sc.links.splice(sel.index, 1); st.sel = null; changed({ inspector: true }); } }, "Remove link")),
    );
  }
  drawProblems();
}

function freshName(prefix, taken) {
  for (let i = 1; ; i++) if (!taken.has(`${prefix}${i}`)) return `${prefix}${i}`;
}

function addSite() {
  const taken = new Set([...st.sc.sites.map((s) => s.name), ...st.sc.nodes.map((n) => n.name)]);
  const name = freshName("site", taken);
  st.sc.sites.push({ name, nat: "none", lan: { delay_ms: 0.05, jitter_ms: 0, loss_pct: 0, rate_mbit: 1000 } });
  st.sel = { kind: "site", index: st.sc.sites.length - 1 };
  changed({ inspector: true });
}

function addGroup() {
  if (!st.sc.sites.length) { toast("Add a site first: nodes live in a site."); return; }
  const taken = new Set([...st.sc.sites.map((s) => s.name), ...expand(st.sc).map((n) => n.name)]);
  const site = st.sel && st.sel.kind === "site" ? st.sc.sites[st.sel.index].name : st.sc.sites[0].name;
  st.sc.nodes.push({ name: freshName("n", taken), site, count: 1, role: "peer" });
  st.sel = { kind: "group", index: st.sc.nodes.length - 1 };
  changed({ inspector: true, dock: true });
}

function addLink() {
  const sites = st.sc.sites.map((s) => s.name);
  const linked = new Set(st.sc.links.map((l) => [l.a, l.b].sort().join(" ")));
  for (let i = 0; i < sites.length; i++) {
    for (let j = i + 1; j < sites.length; j++) {
      if (!linked.has([sites[i], sites[j]].sort().join(" "))) {
        st.sc.links.push({ a: sites[i], b: sites[j], shape: { delay_ms: 10, jitter_ms: 0, loss_pct: 0, rate_mbit: 100 } });
        st.sel = { kind: "link", index: st.sc.links.length - 1 };
        changed({ inspector: true });
        return;
      }
    }
  }
  toast("Every pair of sites is already linked.");
}

function removeSite(i) {
  const name = st.sc.sites[i].name;
  st.sc.sites.splice(i, 1);
  st.sc.nodes = st.sc.nodes.filter((g) => g.site !== name);
  st.sc.links = st.sc.links.filter((l) => l.a !== name && l.b !== name);
  st.sel = null;
  changed({ inspector: true, dock: true });
}

function drawDock() {
  const D = clear(st.el.dock);
  const tabs = [["workload", "Workload"], ["faults", `Faults (${st.sc.faults.length})`], ["file", "File"]];
  D.append(h("div", { class: "dock-tabs", role: "tablist" }, tabs.map(([k, label]) =>
    h("button", { type: "button", role: "tab", "aria-selected": st.dock === k ? "true" : "false", onclick: () => { st.dock = k; drawDock(); } }, label))));
  const body = h("div", { class: "dock-body" });
  D.append(body);
  if (st.dock === "workload") drawWorkload(body);
  else if (st.dock === "faults") drawFaults(body);
  else body.append(h("p", { class: "hint" }, "The file Save writes, as the harness reads it."), h("textarea", { readonly: true, rows: 18, value: st.toml || "" }));
}

function drawWorkload(body) {
  const w = st.sc.workload;
  const nodes = expand(st.sc).map((n) => [n.name, n.name]);
  const redraw = () => { changed({ topo: false }); drawDock(); };
  body.append(h("div", { class: "row" },
    selectField("Workload", w.kind, KINDS, (v) => { st.sc.workload = WORKLOADS[v](nodes.map((n) => n[0])); redraw(); }),
    h("span", { class: "spacer" })));
  body.append(h("p", { class: "hint" }, HINTS[w.kind] || ""));
  if (w.kind === "pubsub") drawPubsub(body, w, nodes, redraw);
  else if (w.kind === "sync") drawSync(body, w, nodes, redraw);
  else if (w.kind === "reconcile") drawReconcile(body, w, nodes);
  else drawTransport(body, w, nodes, redraw);
}

// A set of node names as a row of check boxes.
function nodeSet(label, arr, nodes, note) {
  const boxes = nodes.map(([v, text]) => h("label", { class: "chip" },
    h("input", { type: "checkbox", checked: arr.includes(v), onchange: (e) => {
      const at = arr.indexOf(v);
      if (e.target.checked && at < 0) arr.push(v);
      if (!e.target.checked && at >= 0) arr.splice(at, 1);
      changed({ topo: false });
    } }), text));
  return h("fieldset", { class: "field" }, h("legend", {}, label, note ? h("span", { class: "unit" }, note) : null), h("div", { class: "chips" }, boxes));
}

// A list of numbers typed as "1, 2, 3".
function listField(label, obj, key, { unit = "" } = {}) {
  return h("label", { class: "field" }, h("span", {}, label, unit ? h("span", { class: "unit" }, unit) : null),
    h("input", { type: "text", value: (obj[key] || []).join(", "), spellcheck: "false", oninput: (e) => {
      obj[key] = e.target.value.split(/[ ,]+/).filter(Boolean).map(Number).filter((x) => Number.isFinite(x));
      changed({ topo: false });
    } }));
}

function drawPubsub(body, w, nodes) {
  const c = () => changed({ topo: false });
  body.append(h("div", { class: "grid2" }, textField("Topic", w, "topic", { onchange: c }),
    numField("Messages per publisher", w, "messages", { min: 1, step: 1, onchange: c }),
    numField("Size", w, "size", { unit: "B", min: 16, step: 1, onchange: c }),
    numField("Rate per publisher", w, "rate_hz", { unit: "msg/s", min: 0.01, onchange: c }),
    numField("Longest wait to join", w, "join_s", { unit: "s", min: 1, step: 1, onchange: c }),
    numField("Settle before the first", w, "warmup_s", { unit: "s", min: 0, onchange: c }),
    numField("Drain after the last", w, "drain_s", { unit: "s", min: 0, onchange: c })));
  body.append(nodeSet("Publishers", w.publishers, nodes), nodeSet("Subscribers", w.subscribers, nodes, "none ticked: every peer"));
}

function drawSync(body, w, nodes) {
  const c = () => changed({ topo: false });
  body.append(h("div", { class: "grid2" }, listField("Sizes", w, "sizes", { unit: "B" }),
    numField("Longest fetch", w, "timeout_s", { unit: "s", min: 1, step: 1, onchange: c }),
    numField("Settle before the first", w, "warmup_s", { unit: "s", min: 0, onchange: c })));
  body.append(nodeSet("Providers", w.providers, nodes, "several: fetched from all"), nodeSet("Consumers", w.consumers, nodes));
}

function drawReconcile(body, w, nodes) {
  const c = () => changed({ topo: false });
  body.append(h("div", { class: "grid2" },
    selectField("Holder", w.a, nodes, (v) => { w.a = v; c(); }), selectField("Starts the round", w.b, nodes, (v) => { w.b = v; c(); }),
    listField("Set sizes", w, "items", { unit: "items" }), listField("Differences", w, "differences", { unit: "items each side" }),
    numField("Longest round", w, "timeout_s", { unit: "s", min: 1, step: 1, onchange: c }),
    numField("Settle before the first", w, "warmup_s", { unit: "s", min: 0, onchange: c })));
}

function drawTransport(body, w, nodes, redraw) {
  body.append(h("div", { class: "row" }, h("h3", {}, "Pairs"), h("span", { class: "spacer" }),
    numField("timeout per client run", w, "timeout_s", { unit: "s", min: 1, step: 1, onchange: () => changed({ topo: false }) }),
    h("button", { class: "btn", type: "button", disabled: nodes.length < 2, onclick: () => { w.pairs.push({ client: nodes[0][0], server: nodes[1][0] }); redraw(); } }, "Add pair")));
  body.append(h("table", {}, h("thead", {}, h("tr", {}, h("th", {}, "client"), h("th", {}, "server"), h("th", {}, ""))),
    h("tbody", {}, w.pairs.map((p, i) => h("tr", {},
      h("td", {}, selectField("", p.client, nodes, (v) => { p.client = v; changed({ topo: false }); })),
      h("td", {}, selectField("", p.server, nodes, (v) => { p.server = v; changed({ topo: false }); })),
      h("td", {}, h("button", { class: "x", type: "button", "aria-label": "remove pair", onclick: () => { w.pairs.splice(i, 1); redraw(); } }, "✕")))))));
  body.append(h("div", { class: "row", style: { marginTop: "var(--space-4)" } }, h("h3", {}, "Tests"), h("span", { class: "spacer" }),
    h("button", { class: "btn", type: "button", onclick: () => { w.tests.push({ test: "latency", ...TESTS.latency.init }); redraw(); } }, "Add test")));
  body.append(h("table", {}, h("tbody", {}, w.tests.map((t, i) => h("tr", {},
    h("td", {}, selectField("", t.test, Object.entries(TESTS).map(([k, v]) => [k, v.label]), (v) => { w.tests[i] = { test: v, ...TESTS[v].init }; redraw(); })),
    h("td", {}, h("div", { class: "grid2" }, TESTS[t.test].params.map(([k, label, unit]) => numField(label, t, k, { unit, min: 1, step: 1, onchange: () => changed({ topo: false }) })))),
    h("td", {}, h("button", { class: "x", type: "button", "aria-label": "remove test", onclick: () => { w.tests.splice(i, 1); redraw(); } }, "✕")))))));
}

function drawFaults(body) {
  const f = st.sc.faults;
  const sites = st.sc.sites.map((s) => [s.name, s.name]);
  const nodes = expand(st.sc).map((n) => [n.name, n.name]);
  const ends = [...sites, ...nodes];
  const redraw = () => { changed({ topo: false }); drawDock(); };
  const span = Math.max(30, ...f.map((x) => x.at_s + 5));
  const tl = h("div", { class: "timeline", "aria-label": "Fault schedule of each repetition" });
  const step = span > 120 ? 30 : span > 60 ? 10 : 5;
  for (let t = 0; t <= span; t += step) tl.append(h("span", { class: "tick", style: { left: `${(t / span) * 100}%` } }, `${t} s`));
  f.forEach((x) => tl.append(h("span", { class: `ev ${x.action.do}`, style: { left: `${(x.at_s / span) * 100}%` } }, x.action.do)));
  body.append(h("p", { class: "hint" }, "Each fault happens at its time into every repetition; after the repetition the network is put back as the scenario has it."), tl);
  body.append(h("div", { class: "row" }, h("span", { class: "spacer" }),
    h("button", { class: "btn", type: "button", disabled: st.sc.sites.length < 1, onclick: () => {
      const l = st.sc.links[0];
      f.push(l ? { at_s: 5, action: { do: "cut", a: l.a, b: l.b } } : { at_s: 5, action: { do: "pause", node: nodes[0]?.[0] || "" } });
      redraw();
    } }, "Add fault")));
  if (!f.length) {
    body.append(h("div", { class: "empty" }, "No faults: the network keeps the scenario's shape for the whole run."));
    return;
  }
  body.append(h("table", {}, h("tbody", {}, f.map((x, i) => {
    const a = x.action;
    const kindSel = selectField("", a.do, Object.entries(FAULTS), (v) => {
      const base = { do: v };
      if (["set", "cut", "restore"].includes(v)) Object.assign(base, { a: a.a || ends[0]?.[0], b: a.b || ends[1]?.[0] }, v === "set" ? { shape: { loss_pct: 5 } } : {});
      else if (["partition", "heal"].includes(v)) base.site = a.site || sites[0]?.[0];
      else base.node = a.node || nodes[0]?.[0];
      x.action = base;
      redraw();
    });
    let targets;
    if ("a" in a) {
      targets = h("div", { class: "grid2" }, selectField("", a.a, ends, (v) => { a.a = v; changed({ topo: false }); }), selectField("", a.b, ends, (v) => { a.b = v; changed({ topo: false }); }));
    } else if ("site" in a) {
      targets = selectField("", a.site, sites, (v) => { a.site = v; changed({ topo: false }); });
    } else {
      targets = selectField("", a.node, nodes, (v) => { a.node = v; changed({ topo: false }); });
    }
    return h("tr", {},
      h("td", { style: { width: "7rem" } }, numField("", x, "at_s", { unit: "s", min: 0, onchange: () => changed({ topo: false }) })),
      h("td", {}, kindSel),
      h("td", {}, targets, a.do === "set" ? shapeFields(a.shape, { optional: true, onchange: () => changed({ topo: false }) }) : null,
        a.do === "pause" || a.do === "resume" ? h("label", { class: "chip" }, h("input", { type: "checkbox", checked: !!a.graceful, onchange: (e) => { if (e.target.checked) a.graceful = true; else delete a.graceful; changed({ topo: false }); } }), "tell the group (VINC)") : null),
      h("td", {}, h("button", { class: "x", type: "button", "aria-label": "remove fault", onclick: () => { f.splice(i, 1); redraw(); } }, "✕")));
  }))));
}

async function save() {
  const name = st.sc.name;
  try {
    const d = await api(`/api/scenarios/${encodeURIComponent(name)}`, { method: "PUT", body: st.sc });
    st.file = name;
    st.dirty = false;
    st.problems = d.problems || [];
    toast(d.problems && d.problems.length ? `Saved ${name}.toml with ${d.problems.length} problem(s) to fix before a run` : `Saved ${name}.toml`);
    drawToolbar();
    loadList(name);
    validate();
    return true;
  } catch (e) {
    toast(`Not saved: ${e.message}`, true);
    return false;
  }
}

async function run() {
  if ((st.dirty || st.file !== st.sc.name) && !(await save())) return;
  try {
    await api("/api/runs", { method: "POST", body: { scenario: st.sc.name } });
    st.ctx.go("live");
  } catch (e) {
    toast(`Not started: ${e.message}`, true);
  }
}

