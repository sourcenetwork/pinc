// The dashboard's shell: the four views, the live event stream from the orchestrator, the run state in the bar, the
// theme, and the keyboard (1 to 4 switch views when no field has focus).
import { clear } from "./lib/dom.js";
import { clock } from "./lib/fmt.js";
import * as compose from "./views/compose.js";
import * as live from "./views/live.js";
import * as results from "./views/results.js";
import * as hostView from "./views/host.js";

const VIEWS = { compose, live, results, host: hostView };
const KEEP_SAMPLES = 240;

// What the stream has told us, shared by the views.
export const store = {
  connected: false,
  running: false,
  scenario: null,
  run: null,        // { id, scenario, results, dir, stacks, reps, total, faults, startedAt, phase, progress, rows, faultLog, ended }
  topo: null,
  quiet: null,
  samples: [],
  log: [],
  listeners: new Set(),
};

export function on(fn) {
  store.listeners.add(fn);
  return () => store.listeners.delete(fn);
}

function apply(n) {
  const r = store.run;
  switch (n.type) {
    case "started":
      store.run = {
        id: n.run, scenario: n.scenario, results: n.results, dir: n.results.split("/").pop(),
        stacks: n.stacks || [], reps: n.reps, total: n.total, faults: n.faults || [], startedAt: n.at_ms,
        phase: "starting", progress: null, rows: [], faultLog: [], ended: null, bands: [],
      };
      store.topo = null;
      store.samples = [];
      store.log = [];
      store.running = true;
      store.scenario = n.scenario;
      break;
    case "topology": store.topo = n; break;
    case "quiet": store.quiet = n; break;
    case "sample":
      store.samples.push(n);
      if (store.samples.length > KEEP_SAMPLES) store.samples.shift();
      break;
    case "phase": if (r) r.phase = n.what; break;
    case "progress":
      if (r) {
        r.progress = { ...n };
        r.repStart = n.at_ms;
        const last = r.bands[r.bands.length - 1];
        if (last) last.to = n.at_ms;
        r.bands.push({ stack: n.stack, from: n.at_ms, to: n.at_ms });
      }
      break;
    case "row": if (r) r.rows.push(n); break;
    case "fault": if (r) r.faultLog.push({ ...n }); break;
    case "ended":
      if (r) { r.ended = n; r.phase = n.ok ? "finished" : "ended"; }
      store.running = false;
      break;
    default: break;
  }
  if (n.type !== "sample" && n.type !== "topology" && !(n.type === "quiet" && n.clean)) {
    store.log.push(n);
    if (store.log.length > 2000) store.log.shift();
  }
}

function emit(n) {
  for (const fn of store.listeners) {
    try { fn(n); } catch (e) { console.error(e); }
  }
}

function connect() {
  const es = new EventSource("/api/events");
  es.addEventListener("snapshot", (e) => {
    const st = JSON.parse(e.data);
    store.connected = true;
    store.run = null; store.topo = null; store.samples = []; store.log = [];
    for (const n of st.recent) apply(n);
    store.running = st.running;
    store.scenario = st.scenario;
    if (store.run && !st.running && !store.run.ended) store.run.phase = "ended";
    emit({ type: "snapshot" });
    paintState();
  });
  es.onmessage = (e) => {
    const n = JSON.parse(e.data);
    apply(n);
    emit(n);
    if (n.type !== "sample") paintState();
  };
  es.onerror = () => {
    store.connected = false;
    paintState();
  };
}

function paintState() {
  const el = document.getElementById("runstate");
  const txt = el.querySelector(".txt");
  const r = store.run;
  if (!store.connected) {
    el.dataset.state = "offline";
    txt.textContent = "Not connected to the orchestrator; retrying";
    return;
  }
  if (store.running && r) {
    const stopping = r.phase === "tearing down";
    el.dataset.state = stopping ? "stopping" : "running";
    const p = r.progress;
    const where = p ? `${p.test} · ${p.stack} · rep ${p.rep + 1}/${p.reps} · ${p.index + 1}/${p.total}` : r.phase;
    txt.textContent = `${r.scenario} · ${stopping ? "tearing down" : where}`;
  } else {
    el.dataset.state = "idle";
    txt.textContent = r && r.ended ? `Idle · last run ${r.ended.ok ? "finished" : "ended with an error"}` : "Idle";
  }
}

setInterval(() => {
  const r = store.run;
  if (store.running && r) {
    const el = document.getElementById("runstate");
    el.title = `running for ${clock(Date.now() - r.startedAt)}`;
  }
}, 1000);

let current = null;
function route() {
  const name = (location.hash.replace(/^#\//, "").split("/")[0]) || "compose";
  const view = VIEWS[name] ? name : "compose";
  for (const a of document.querySelectorAll(".tabs a")) {
    if (a.dataset.view === view) a.setAttribute("aria-current", "page");
    else a.removeAttribute("aria-current");
  }
  current?.unmount?.();
  const main = clear(document.getElementById("view"));
  current = VIEWS[view];
  current.mount(main, { store, on, go: (v) => { location.hash = `#/${v}`; } });
}

const THEMES = ["auto", "light", "dark"];
function setTheme(t) {
  if (t === "auto") delete document.documentElement.dataset.theme;
  else document.documentElement.dataset.theme = t;
  try { localStorage.setItem("vd-theme", t); } catch (_) { /* private mode: the choice lasts this page */ }
  const b = document.getElementById("theme");
  b.textContent = t === "auto" ? "Auto" : t === "light" ? "Light" : "Dark";
  b.setAttribute("aria-label", `Theme: ${b.textContent}. Change`);
  emit({ type: "theme" });
}

document.getElementById("theme").addEventListener("click", () => {
  const cur = document.documentElement.dataset.theme || "auto";
  setTheme(THEMES[(THEMES.indexOf(cur) + 1) % THEMES.length]);
});
setTheme(document.documentElement.dataset.theme || "auto");

document.addEventListener("keydown", (e) => {
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const t = e.target;
  if (t && (t.tagName === "INPUT" || t.tagName === "TEXTAREA" || t.tagName === "SELECT" || t.isContentEditable)) return;
  const v = { 1: "compose", 2: "live", 3: "results", 4: "host" }[e.key];
  if (v) { location.hash = `#/${v}`; e.preventDefault(); }
});

window.addEventListener("hashchange", route);
connect();
route();
paintState();
