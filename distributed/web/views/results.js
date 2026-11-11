// Results: every run on disk, its conditions (backend, machine, CPU sets, MTU, versions), the comparison tables with
// the best value of each row marked, the raw rows per repetition, and the exports.
import { h, clear, api, toast } from "../lib/dom.js";
import { num, when } from "../lib/fmt.js";

function cell(c, best) {
  if (c && typeof c === "object" && "median" in c) {
    const range = c.n > 1 ? h("span", { class: "rng" }, `[${num(c.min)}..${num(c.max)}]`) : null;
    return h("td", { class: `v${best ? " best" : ""}`, title: `${c.n} value${c.n === 1 ? "" : "s"}${best ? ", best of the row" : ""}` }, num(c.median), range);
  }
  return h("td", { class: "v missing" }, String(c || "not measured").replace(/^not measured: /, "not measured: "));
}

// The comparison tables, as the summary file has them (computed by the harness, not here).
export function tablesView(tables, stacks, { rows = null } = {}) {
  if (!tables || !tables.length) return h("div", { class: "empty" }, "No measurement has finished yet.");
  return h("div", { class: "pane-body", style: { padding: 0 } }, tables.map((t) => {
    const head = h("tr", {}, h("th", {}, "metric"), stacks.map((s) => h("th", { class: `stack-${s}`, style: { textAlign: "right" } }, h("span", { class: "swatch" }), s)));
    const body = t.lines.map((l) => h("tr", {},
      h("th", { scope: "row" }, l.label, l.unit ? h("span", { class: "metric-unit" }, l.unit) : null,
        l.better === "lower" ? h("span", { class: "metric-unit", title: "lower is better" }, "↓") : l.better === "higher" ? h("span", { class: "metric-unit", title: "higher is better" }, "↑") : null),
      l.cells.map((c, i) => cell(c, l.best === i))));
    const mine = rows ? rows.filter((r) => r.test === t.test && r.pair === t.pair) : [];
    return h("div", { class: "table-block" },
      h("header", {}, h("h2", {}, t.test), h("span", { class: "sub mono" }, t.pair)),
      h("table", {}, h("thead", {}, head), h("tbody", {}, body)),
      t.notes.length ? h("div", { class: "note" }, t.notes.join(" · ")) : null,
      mine.length ? rawRows(mine) : null);
  }));
}

function rawRows(rows) {
  const keys = ["p50_us", "p99_us", "mib_s", "failed", "connected_and_moved", "all_done_s"].filter((k) => rows.some((r) => k in r.node));
  return h("details", { class: "raw" }, h("summary", {}, `${rows.length} raw row${rows.length === 1 ? "" : "s"}`),
    h("table", {}, h("thead", {}, h("tr", {}, h("th", {}, "stack"), h("th", {}, "rep"), h("th", {}, "status"), h("th", {}, "host"), keys.map((k) => h("th", { style: { textAlign: "right" } }, k)),
      h("th", { style: { textAlign: "right" } }, "client CPU s"), h("th", { style: { textAlign: "right" } }, "server CPU s"), h("th", { style: { textAlign: "right" } }, "client peak MiB"), h("th", { style: { textAlign: "right" } }, "client wire bytes"))),
    h("tbody", {}, rows.map((r) => {
      const c = r.kernel?.client || {}, sv = r.kernel?.server || {};
      const q = r.host;
      const hostCell = q ? h("span", { class: q.clean ? "status-good" : "status-bad", title: `other processes ${num(q.other_pct)}% of a core, steal ${num(q.steal_pct)}%${q.top ? `, most: ${q.top}` : ""}` }, q.clean ? "\u2713 clean" : "\u2715 busy") : h("span", { class: "sub" }, "not checked");
      return h("tr", {}, h("td", { class: `stack-${r.stack}` }, h("span", { class: "swatch" }), r.stack), h("td", { class: "v" }, r.rep + 1),
        h("td", {}, r.status === "ok" ? h("span", { class: "chip good glyph-good" }) : h("span", { class: r.status.startsWith("discarded") ? "chip warn" : "sub" }, r.status)),
        h("td", {}, hostCell),
        keys.map((k) => h("td", { class: "v" }, num(r.node[k]))),
        h("td", { class: "v" }, num(c.cpu_s)), h("td", { class: "v" }, num(sv.cpu_s)), h("td", { class: "v" }, num(c.peak_mib)),
        h("td", { class: "v" }, c.eth0 ? num(c.eth0.tx_bytes + c.eth0.rx_bytes) : "-"));
    }))));
}

export function conditionsView(run) {
  if (!run || !run.host) return h("div", { class: "conditions" }, "This run has not finished: its conditions are written when it ends.");
  const host = run.host;
  const versions = Object.entries(run.versions || {}).map(([k, v]) => `${k} ${v}`).join(", ");
  const sets = (run.nodes || []).map((n) => `${n.name} ${n.cpus}`).join(", ");
  return h("div", { class: "conditions" },
    h("div", {}, h("strong", {}, run.backend === "containers" ? "Containers on one machine." : `${run.backend}.`), " ", run.about_backend || ""),
    h("div", {}, `${host.cpu}, ${host.cpus} CPUs, ${host.mem_gib} GiB, kernel ${host.kernel}. MTU ${run.mtu} on every interface.`),
    h("div", {}, `Each node: CPU set ${sets.length > 220 ? `${sets.slice(0, 220)}…` : sets}; ${run.nodes?.[0]?.memory_mib ?? "?"} MiB.${run.shared_cpus ? " Nodes share CPUs." : ""}`),
    h("div", {}, `Versions: ${versions}. VINC at ${run.git}. ${run.built_for ? `Every stack compiled for ${run.built_for}. ` : ""}${run.repetitions} repetition${run.repetitions === 1 ? "" : "s"}. CPU governor: ${run.governor || "not recorded"}.`),
    run.isolation ? h("div", {}, `Isolation: ${run.isolation}; the orchestrator on CPU ${run.orchestrator_cpus}.`) : null,
    run.quiet ? h("div", {}, `Quiet host: other processes at most ${run.quiet.other_pct}% of a core and steal at most ${run.quiet.steal_pct}% over each measurement; up to ${run.quiet.retries} repeats, then not measured.`) : h("div", { class: "status-bad" }, "This run predates the quiet-host check."),
    run.reduced ? h("div", { class: "chip warn" }, "a reduced run: fewer repetitions than the scenario asks; do not quote it") : null,
    h("div", {}, run.status === "ok" ? h("span", { class: "status-good" }, "Completed. ") : h("span", { class: "status-bad" }, `Ended: ${run.status}. `),
      (run.teardown_left || []).length ? h("span", { class: "status-bad" }, `Teardown left: ${run.teardown_left.join(", ")}`) : h("span", {}, "Teardown verified clean.")));
}

let st = null;

export function mount(el, ctx) {
  st = { ctx, list: [], sel: null };
  const listBody = h("div", { class: "list" });
  const detail = h("section", { class: "pane" });
  el.append(h("div", { class: "view results" },
    h("aside", { class: "pane", "aria-label": "Runs" }, h("div", { class: "pane-head" }, h("h2", {}, "Runs"), h("button", { class: "btn", type: "button", onclick: load }, "Refresh")), listBody),
    detail));
  st.el = { listBody, detail };
  load();
  st.off = ctx.on((n) => { if (n.type === "ended") load(); });
}

export function unmount() {
  st?.off?.();
  st = null;
}

async function load() {
  try {
    st.list = await api("/api/results");
  } catch (e) {
    toast(`The results could not be listed: ${e.message}`, true);
    return;
  }
  const L = clear(st.el.listBody);
  if (!st.list.length) {
    L.append(h("div", { class: "empty" }, h("strong", {}, "No results yet"), "Run a scenario; its results appear here."));
    clear(st.el.detail).append(h("div", { class: "empty" }, "Nothing to show."));
    return;
  }
  for (const r of st.list) {
    const ok = r.status === "ok";
    L.append(h("button", { class: "item", type: "button", "aria-current": r.dir === st.sel ? "true" : "false", onclick: () => open(r.dir) },
      h("div", { class: "item-top" }, h("span", { class: "item-name" }, r.scenario || r.dir), h("span", { class: "spacer" }),
        !r.finished ? h("span", { class: "chip accent" }, "running") : ok ? h("span", { class: "chip good glyph-good" }) : h("span", { class: "chip bad glyph-bad" }),
        r.reduced ? h("span", { class: "chip warn" }, "reduced") : null),
      h("div", { class: "item-meta" }, `${when(r.started)} · ${r.rows} row${r.rows === 1 ? "" : "s"}`),
      h("div", { class: "item-meta" }, r.dir)));
  }
  if (!st.sel) open(st.list[0].dir);
}

async function open(dir) {
  st.sel = dir;
  for (const b of st.el.listBody.querySelectorAll("button.item")) b.setAttribute("aria-current", b.textContent.includes(dir) ? "true" : "false");
  const D = clear(st.el.detail);
  D.append(h("div", { class: "empty" }, "Loading…"));
  let d;
  try {
    d = await api(`/api/results/${encodeURIComponent(dir)}`);
  } catch (e) {
    clear(D).append(h("div", { class: "empty" }, `This run cannot be read: ${e.message}`));
    return;
  }
  if (st?.sel !== dir) return;
  clear(D).append(
    h("div", { class: "pane-head" }, h("h2", {}, d.run?.scenario || dir), h("span", { class: "sub mono" }, dir),
      h("a", { class: "btn", href: `/api/results/${encodeURIComponent(dir)}/raw.jsonl`, download: `${dir}.jsonl` }, "JSON lines"),
      h("a", { class: "btn", href: `/api/results/${encodeURIComponent(dir)}/raw.csv`, download: `${dir}.csv` }, "CSV")),
    h("div", { class: "pane-body" }, conditionsView(d.run), tablesView(d.tables, d.stacks, { rows: d.rows })));
}
