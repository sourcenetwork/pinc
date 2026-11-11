// Live: the network as it runs (each link's traffic, drops and cuts, each node's CPU and state), the progress, the
// fault timeline of the repetition, moving charts, the comparison table as measurements finish, and the log.
import { h, clear, api, toast } from "../lib/dom.js";
import { Topo } from "../lib/topo.js";
import { LineChart } from "../lib/chart.js";
import { num, clock } from "../lib/fmt.js";
import { tablesView } from "./results.js";

const PER_REP = {
  setup: ["p50_us", "time to first byte p50", "us"],
  resume: ["p50_us", "time to first byte p50", "us"],
  latency: ["p50_us", "round trip p50", "us"],
  throughput: ["mib_s", "goodput", "MiB/s"],
  many: ["all_done_s", "all connected and moved", "s"],
};

let st = null;

export function mount(el, ctx) {
  st = { ctx, el, cut: new Set(), nodeState: new Map(), fetchTimer: 0, tick: 0 };
  draw();
  st.off = ctx.on(onEvent);
  st.tick = setInterval(() => { if (st?.ctx.store.running) paintProgress(); }, 1000);
}

export function unmount() {
  if (!st) return;
  st.off?.();
  clearInterval(st.tick);
  clearTimeout(st.fetchTimer);
  for (const c of st.charts || []) c.destroy();
  st = null;
}

function draw() {
  for (const c of st.charts || []) c.destroy();
  st.charts = [];
  const store = st.ctx.store;
  const root = clear(st.el);
  if (!store.run) {
    root.append(h("div", { class: "view" }, h("div", { class: "empty", style: { alignSelf: "center" } },
      h("strong", {}, "No run is going."),
      "Pick a scenario in Compose and press Run; it shows here as it happens.",
      h("button", { class: "btn", type: "button", onclick: () => st.ctx.go("compose") }, "Open Compose"))));
    return;
  }
  const topoBox = h("div", { class: "topo" }, h("div", { class: "legend" },
    h("span", {}, h("i", { class: "flow" }), "traffic, width by use of the link's rate"),
    h("span", {}, h("i", { class: "cut" }), "cut"),
    h("span", {}, h("i", { class: "nat" }), "home router")));
  const side = h("aside", { class: "side" });
  const results = h("div", {});
  const log = h("div", { class: "log", role: "log", "aria-label": "Run log" });
  root.append(h("div", { class: "view live" }, topoBox, side, h("div", { class: "bottom" }, results, log)));
  st.parts = { topoBox, side, results, log };
  st.topo = new Topo(topoBox, {});
  if (store.topo) renderTopo();
  drawSide();
  drawLog();
  fetchResults();
}

function renderTopo() {
  const t = st.ctx.store.topo;
  st.topo.render({ sites: t.sites, nodes: t.nodes, links: t.links }, null);
  st.topo.live({ topo: t, sample: st.ctx.store.samples.at(-1), cut: st.cut, nodeState: st.nodeState });
}

function drawSide() {
  const S = clear(st.parts.side);
  const r = st.ctx.store.run;
  const stop = h("button", { class: "btn danger", type: "button", disabled: !st.ctx.store.running, onclick: stopRun }, "Stop and tear down");
  st.prog = { phase: h("div", { class: "sub" }), what: h("div", { class: "mono" }), fill: h("div", { class: "bar-fill" }), time: h("span", { class: "sub mono" }), quiet: h("div", { class: "sub" }) };
  st.tl = h("div", { class: "timeline", "aria-label": "Faults of this repetition" });
  const traffic = h("canvas", { "aria-label": "Traffic on the wire, all nodes" });
  const drops = h("canvas", { "aria-label": "Packets dropped by the shapers" });
  const perRep = h("canvas", { "aria-label": "Per repetition result of the current test" });
  st.perRepTitle = h("strong", {}, "per repetition");
  S.append(
    h("div", { class: "pane-head" }, h("h2", {}, r.scenario), h("span", { class: "chip mono" }, r.id), stop),
    h("div", { class: "pane-body" },
      h("div", { class: "progress" }, h("div", { class: "row" }, st.prog.phase, h("span", { class: "spacer" }), st.prog.time), st.prog.what, h("div", { class: "bar-track" }, st.prog.fill), st.prog.quiet),
      r.faults.length ? h("div", {}, h("h3", {}, "Faults of this repetition"), st.tl) : h("p", { class: "hint" }, "No faults in this scenario."),
      h("div", { class: "chart" }, h("div", { class: "chart-head" }, h("strong", {}, "Traffic on the wire"), h("span", { class: "legend" }, legendFor(r.stacks))), traffic),
      h("div", { class: "chart" }, h("div", { class: "chart-head" }, h("strong", {}, "Shaper drops"), h("span", { class: "sub" }, "loss emulation and full queues")), drops),
      h("div", { class: "chart" }, h("div", { class: "chart-head" }, st.perRepTitle, h("span", { class: "legend" }, legendFor(r.stacks))), perRep)));
  st.cTraffic = new LineChart(traffic, { yUnit: "Mbit/s", yFmt: (v) => num(v), xFmt: (v) => num(v), windowSpan: 120 });
  st.cDrops = new LineChart(drops, { yUnit: "packets/s", yFmt: (v) => num(v), xFmt: (v) => num(v), windowSpan: 120 });
  st.cRep = new LineChart(perRep, { yUnit: "", yFmt: (v) => num(v), xFmt: (v) => num(v), xUnit: "", markers: true });
  st.charts.push(st.cTraffic, st.cDrops, st.cRep);
  paintProgress();
  paintTimeline();
  paintCharts();
  paintPerRep();
}

function legendFor(stacks) {
  return stacks.map((s) => h("span", { class: `stack-${s}` }, h("span", { class: "swatch" }), s));
}

function paintProgress() {
  const r = st.ctx.store.run;
  if (!r || !st.prog) return;
  const p = r.progress;
  const done = r.ended ? r.total : p ? p.index : 0;
  st.prog.phase.textContent = r.ended ? (r.ended.ok ? "Finished; torn down" : `Ended: ${r.ended.error || "the teardown left something"}`) : r.phase;
  st.prog.what.textContent = p ? `${p.index + 1} of ${p.total} · ${p.test} · ${p.stack} · rep ${p.rep + 1}/${p.reps} · ${p.pair}` : "preparing the network";
  st.prog.fill.style.width = `${r.total ? (100 * done) / r.total : 0}%`;
  const q = st.ctx.store.quiet;
  clear(st.prog.quiet).append(q
    ? h("span", { class: q.clean ? "status-good" : "status-bad" }, q.clean ? "\u2713 host quiet" : "\u2715 host busy",
      ` \u00b7 other processes ${num(q.other_pct)}% of a core \u00b7 steal ${num(q.steal_pct)}%${q.clean || !q.top ? "" : ` \u00b7 most: ${q.top}`}`)
    : h("span", {}, "host check: waiting for the first window"));
  const end = r.ended ? (r.endedAt || Date.now()) : Date.now();
  st.prog.time.textContent = clock(end - r.startedAt);
  paintTimeline();
}

function paintTimeline() {
  const r = st.ctx.store.run;
  if (!r || !r.faults.length || !st.tl) return;
  const span = Math.max(30, ...r.faults.map((f) => f.at_s + 5));
  const T = clear(st.tl);
  const step = span > 120 ? 30 : span > 60 ? 10 : 5;
  for (let t = 0; t <= span; t += step) T.append(h("span", { class: "tick", style: { left: `${(t / span) * 100}%` } }, `${t} s`));
  const fired = new Set(r.faultLog.filter((f) => !r.repStart || f.at_ms >= r.repStart).map((f) => f.at_s));
  r.faults.forEach((f) => T.append(h("span", { class: `ev ${f.action.do}`, style: { left: `${(f.at_s / span) * 100}%`, opacity: fired.has(f.at_s) ? 1 : 0.45 } }, f.action.do)));
  if (r.repStart && st.ctx.store.running) {
    const t = (Date.now() - r.repStart) / 1000;
    if (t <= span) T.append(h("span", { class: "cursor", style: { left: `${(t / span) * 100}%` } }));
  }
}

function paintCharts() {
  const store = st.ctx.store;
  const r = store.run;
  if (!r || !st.cTraffic) return;
  const t0 = r.startedAt;
  const traffic = store.samples.map((s) => [(s.at_ms - t0) / 1000, s.nodes.reduce((a, n) => a + (n.tx_bps || 0), 0) / 1e6]);
  const drops = store.samples.map((s) => [(s.at_ms - t0) / 1000, s.shapers.reduce((a, q) => a + (q.drops_ps || 0), 0)]);
  const bands = r.bands.map((b) => ({ stack: b.stack, from: (b.from - t0) / 1000, to: ((b.to === b.from ? Date.now() : b.to) - t0) / 1000 }));
  st.cTraffic.set([{ stack: "all", color: "--ink-2", points: traffic }], bands);
  st.cDrops.set([{ stack: "all", color: "--warn", points: drops }], bands);
}

function paintPerRep() {
  const r = st.ctx.store.run;
  if (!r || !st.cRep) return;
  const test = r.progress?.test || r.rows.at(-1)?.test;
  if (!test) return;
  const kind = test.split("_")[0];
  const [key, label, unit] = PER_REP[kind] || PER_REP.setup;
  st.perRepTitle.textContent = `${test}: ${label} by repetition`;
  st.cRep.o.yUnit = unit;
  const pair = r.progress?.pair;
  const series = r.stacks.map((s) => ({
    stack: s,
    points: r.rows.filter((x) => x.test === test && x.stack === s && (!pair || x.pair === pair) && x.status === "ok" && Number.isFinite(x.node?.[key])).map((x) => [x.rep + 1, x.node[key]]),
  }));
  st.cRep.set(series);
}

function drawLog() {
  const L = clear(st.parts.log);
  for (const n of st.ctx.store.log.slice(-300)) L.append(logLine(n));
  L.scrollTop = L.scrollHeight;
}

function logLine(n) {
  const r = st.ctx.store.run;
  const t = r ? clock(n.at_ms - r.startedAt) : "";
  let cls = "", msg;
  switch (n.type) {
    case "started": msg = `started ${n.scenario}: ${n.total} measurements, results in ${n.results}`; break;
    case "phase": msg = n.what; break;
    case "quiet": cls = "warn"; msg = `host busy: other processes ${num(n.other_pct)}% of a core, steal ${num(n.steal_pct)}%${n.top ? `, most: ${n.top}` : ""}`; break;
    case "progress": msg = `measuring ${n.test} · ${n.stack} · rep ${n.rep + 1}/${n.reps} · ${n.pair}`; break;
    case "row": cls = n.status === "ok" ? "" : "warn"; msg = `${n.test} · ${n.stack} · rep ${n.rep + 1}: ${n.status}`; break;
    case "fault": cls = "fault"; msg = `${num(n.at_s)} s into the repetition: ${n.what}`; break;
    case "log": cls = n.level; msg = n.msg; break;
    case "ended": cls = n.ok ? "" : "error"; msg = n.ok ? "finished; everything torn down" : `ended: ${n.error || ""}${n.left?.length ? ` left: ${n.left.join(", ")}` : ""}`; break;
    default: msg = n.type;
  }
  return h("div", { class: cls }, h("time", {}, t), h("span", {}, msg));
}

function applyFault(n) {
  const topo = st.ctx.store.topo;
  if (!topo) return;
  const a = n.action;
  const siteIdx = (name) => topo.sites.findIndex((x) => x.name === name);
  const nodeIdx = (name) => topo.nodes.findIndex((x) => x.name === name);
  const linkOf = (x, y) => topo.links.findIndex((l) => {
    const A = topo.sites[l.a]?.name, B = topo.sites[l.b]?.name;
    return (A === x && B === y) || (A === y && B === x);
  });
  const accessNode = (x, y) => { const i = nodeIdx(x); return i >= 0 && topo.sites[topo.nodes[i].site]?.name === y ? i : -1; };
  if (a.do === "cut" || a.do === "restore") {
    const k = linkOf(a.a, a.b);
    if (k >= 0) { if (a.do === "cut") st.cut.add(k); else st.cut.delete(k); }
    const nd = accessNode(a.a, a.b) >= 0 ? accessNode(a.a, a.b) : accessNode(a.b, a.a);
    if (nd >= 0) { if (a.do === "cut") st.nodeState.set(nd, "cut"); else st.nodeState.delete(nd); }
  } else if (a.do === "partition" || a.do === "heal") {
    const s = siteIdx(a.site);
    topo.links.forEach((l, k) => { if (l.a === s || l.b === s) { if (a.do === "partition") st.cut.add(k); else st.cut.delete(k); } });
  } else if (a.node) {
    const i = nodeIdx(a.node);
    if (i >= 0) st.nodeState.set(i, { pause: "paused", resume: "active", kill: "killed", restart: "active" }[a.do] || "");
  }
}

function onEvent(n) {
  if (!st) return;
  const store = st.ctx.store;
  if (n.type === "snapshot" || n.type === "started") {
    st.cut = new Set();
    st.nodeState = new Map();
    for (const e of store.log) if (e.type === "fault") applyFault(e);
    draw();
    return;
  }
  if (!store.run || !st.parts) { draw(); return; }
  switch (n.type) {
    case "topology": renderTopo(); return;
    case "sample":
      st.topo.live({ topo: store.topo, sample: n, cut: st.cut, nodeState: st.nodeState });
      paintCharts();
      return;
    case "progress": {
      st.cut = new Set();
      st.nodeState = new Map();
      const [c, s] = n.pair.split(">");
      for (const name of [c, s]) {
        const i = store.topo ? store.topo.nodes.findIndex((x) => x.name === name) : -1;
        if (i >= 0) st.nodeState.set(i, "active");
      }
      st.topo.live({ topo: store.topo, cut: st.cut, nodeState: st.nodeState });
      paintProgress();
      paintPerRep();
      break;
    }
    case "fault":
      applyFault(n);
      st.topo.live({ topo: store.topo, cut: st.cut, nodeState: st.nodeState });
      paintTimeline();
      break;
    case "row":
      paintPerRep();
      paintProgress();
      clearTimeout(st.fetchTimer);
      st.fetchTimer = setTimeout(fetchResults, 800);
      break;
    case "ended":
      store.run.endedAt = n.at_ms;
      st.nodeState = new Map();
      st.cut = new Set();
      drawSide();
      fetchResults();
      break;
    case "theme": for (const c of st.charts || []) c.redraw(); return;
    case "quiet": paintProgress(); if (n.clean) return; break;
    default: paintProgress();
  }
  if (n.type !== "theme") {
    const L = st.parts.log;
    const atEnd = L.scrollHeight - L.scrollTop - L.clientHeight < 24;
    L.append(logLine(n));
    while (L.childElementCount > 300) L.firstChild.remove();
    if (atEnd) L.scrollTop = L.scrollHeight;
  }
}

async function fetchResults() {
  const r = st?.ctx.store.run;
  if (!r || !st.parts) return;
  try {
    const d = await api(`/api/results/${encodeURIComponent(r.dir)}`);
    if (!st) return;
    clear(st.parts.results).append(h("div", { class: "pane-head" }, h("h2", {}, "Measured so far"), h("span", { class: "sub" }, `${d.rows.length} of ${r.total}`)),
      tablesView(d.tables, d.stacks));
  } catch (_) {
    if (st) clear(st.parts.results).append(h("div", { class: "empty" }, "No measurement has finished yet."));
  }
}

async function stopRun(e) {
  e.target.disabled = true;
  try {
    await api("/api/runs/stop", { method: "POST" });
    toast("Stopping: the run tears down everything it created.");
  } catch (err) {
    toast(`Not stopped: ${err.message}`, true);
    e.target.disabled = false;
  }
}
