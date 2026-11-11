// The topology diagram: sites as boxes holding their nodes, links between the sites' routers with their shaping.
// Live, each link carries one flow line per direction (width by use of its rate), its rates and drops; a cut link is
// drawn broken and crossed; a node shows its CPU and its state by outline and fill.
import { s, clear } from "./dom.js";
import { bits, num, shape } from "./fmt.js";

const CELL_W = 30, CELL_H = 34, PAD = 12, HEAD = 36;

function shortName(node, site) {
  const n = node.name;
  if (n.startsWith(`${site}-`)) return n.slice(site.length + 1);
  return n.length > 6 ? `${n.slice(0, 5)}…` : n;
}

function boxOf(site, count) {
  const cols = Math.max(2, Math.min(6, Math.ceil(Math.sqrt(count * 1.6))));
  const rows = Math.max(1, Math.ceil(count / cols));
  return { cols, w: Math.max(150, cols * CELL_W + PAD * 2), h: HEAD + rows * CELL_H + PAD };
}

function autoPos(i, n) {
  if (n === 1) return [320, 220];
  const a = Math.PI + (2 * Math.PI * i) / n;
  const r = n === 2 ? 230 : 240;
  return [400 + r * Math.cos(a), 260 + r * Math.sin(a) * 0.82];
}

export class Topo {
  constructor(el, { editable = false, onSelect = () => {}, onMove = () => {} } = {}) {
    this.el = el;
    this.o = { editable, onSelect, onMove };
    this.svg = s("svg", { role: "img", "aria-label": "Network topology" });
    el.append(this.svg);
    this.model = null;
    this.linkEls = [];
    this.nodeEls = [];
    this.siteEls = [];
  }

  render(model, sel) {
    this.model = model;
    clear(this.svg);
    this.linkEls = [];
    this.nodeEls = [];
    this.siteEls = [];
    const counts = model.sites.map((_, i) => model.nodes.filter((n) => n.site === i).length);
    const geo = model.sites.map((site, i) => {
      const b = boxOf(site, counts[i]);
      const [cx, cy] = site.pos || autoPos(i, model.sites.length);
      return { ...b, cx, cy, x: cx - b.w / 2, y: cy - b.h / 2 };
    });
    this.geo = geo;
    if (!geo.length) {
      this.svg.setAttribute("viewBox", "0 0 400 200");
      this.svg.append(s("text", { x: 200, y: 100, "text-anchor": "middle", fill: "currentColor", class: "sub" }, "Add a site to start"));
      return;
    }
    const minX = Math.min(...geo.map((g) => g.x)) - 120, minY = Math.min(...geo.map((g) => g.y)) - 60;
    const maxX = Math.max(...geo.map((g) => g.x + g.w)) + 120, maxY = Math.max(...geo.map((g) => g.y + g.h)) + 60;
    this.svg.setAttribute("viewBox", `${minX} ${minY} ${maxX - minX} ${maxY - minY}`);
    const links = s("g", {});
    const sites = s("g", {});
    const labels = s("g", {});
    this.svg.append(links, sites, labels);
    model.links.forEach((l, k) => {
      const A = geo[l.a], B = geo[l.b];
      if (!A || !B) return;
      const dx = B.cx - A.cx, dy = B.cy - A.cy, len = Math.hypot(dx, dy) || 1;
      const nx = -dy / len * 3.5, ny = dx / len * 3.5;
      const g = s("g", { class: "link", "data-k": k });
      const wire = s("line", { class: "wire", x1: A.cx, y1: A.cy, x2: B.cx, y2: B.cy });
      const fwd = s("line", { class: "flow", x1: A.cx + nx, y1: A.cy + ny, x2: B.cx + nx, y2: B.cy + ny, "stroke-width": 0 });
      const rev = s("line", { class: "flow", x1: A.cx - nx, y1: A.cy - ny, x2: B.cx - nx, y2: B.cy - ny, "stroke-width": 0 });
      const mx = (A.cx + B.cx) / 2, my = (A.cy + B.cy) / 2;
      const cut = s("g", { class: "cutmark", visibility: "hidden" },
        s("line", { x1: mx - 6 - ny, y1: my - 6 + nx, x2: mx + 6 - ny, y2: my + 6 + nx }),
        s("line", { x1: mx - 6 + ny, y1: my + 6 - nx, x2: mx + 6 + ny, y2: my - 6 - nx }));
      const hit = s("line", { class: "hit", x1: A.cx, y1: A.cy, x2: B.cx, y2: B.cy });
      if (this.o.editable) hit.addEventListener("click", () => this.o.onSelect({ kind: "link", index: k }));
      g.append(wire, fwd, rev, cut, hit);
      links.append(g);
      const same = JSON.stringify(l.forward) === JSON.stringify(l.reverse);
      const lines = [shape(l.forward)];
      if (!same) lines.push(`back ${shape(l.reverse)}`);
      const lab = s("g", { class: "link label" });
      const rect = s("rect", { rx: 3 });
      const texts = lines.map((t, i) => s("text", { x: mx, y: my + 26 + i * 12, "text-anchor": "middle" }, t));
      const liveText = s("text", { x: mx, y: my + 26 + lines.length * 12, "text-anchor": "middle", class: "live" }, "");
      lab.append(rect, ...texts, liveText);
      labels.append(lab);
      this.linkEls[k] = { g, fwd, rev, cut, liveText, rect, lab, lines: lines.length, mx, my, link: l };
      if (sel && sel.kind === "link" && sel.index === k) g.classList.add("sel");
    });
    model.sites.forEach((site, i) => {
      const G = geo[i];
      const g = s("g", { class: `site${site.nat && site.nat !== "none" ? " nat" : ""}`, transform: `translate(${G.x},${G.y})`, tabindex: this.o.editable ? 0 : -1 });
      const box = s("rect", { class: "box", width: G.w, height: G.h, rx: 6 });
      const meta = [site.lan || "", site.nat && site.nat !== "none" ? `NAT ${site.nat}` : ""].filter(Boolean).join(" · ");
      g.append(box,
        s("circle", { class: "router", cx: G.w - 12, cy: 12, r: 5 }),
        s("text", { class: "name", x: 10, y: 16 }, site.name),
        s("text", { class: "meta", x: 10, y: 29 }, meta));
      if (sel && sel.kind === "site" && sel.index === i) g.classList.add("sel");
      const mine = model.nodes.map((n, j) => [n, j]).filter(([n]) => n.site === i);
      mine.forEach(([n, j], k) => {
        const col = k % G.cols, row = Math.floor(k / G.cols);
        const nx = PAD + col * CELL_W, ny = HEAD + row * CELL_H;
        const ng = s("g", { class: `node ${n.role || "peer"}`, transform: `translate(${nx},${ny})` });
        const rect = s("rect", { width: 18, height: 18, rx: 3 });
        const cpu = s("rect", { class: "cpu", x: 2, y: 16, width: 14, height: 0 });
        const x = s("g", { class: "mark-x", visibility: "hidden" }, s("line", { x1: 3, y1: 3, x2: 15, y2: 15 }), s("line", { x1: 15, y1: 3, x2: 3, y2: 15 }));
        const title = s("title", {}, `${n.name}${n.ip ? ` ${n.ip}` : ""}${n.cpus ? ` cpus ${n.cpus}` : ""}`);
        ng.append(title, rect, cpu, x, s("text", { x: 9, y: 29, "text-anchor": "middle" }, shortName(n, site.name)));
        if (this.o.editable) {
          ng.style.cursor = "pointer";
          ng.addEventListener("click", (e) => { e.stopPropagation(); this.o.onSelect({ kind: "node", index: j }); });
        }
        if (sel && sel.kind === "node" && sel.index === j) ng.classList.add("sel");
        g.append(ng);
        this.nodeEls[j] = { g: ng, cpu, x };
      });
      if (this.o.editable) this.dragSite(g, i, G);
      sites.append(g);
      this.siteEls[i] = g;
    });
    this.fitLabels();
  }

  fitLabels() {
    for (const e of this.linkEls) {
      if (!e) continue;
      try {
        const b = e.lab.getBBox();
        const pad = 4;
        const bb = [...e.lab.querySelectorAll("text")].reduce((a, t) => {
          const r = t.getBBox();
          return r.width ? { x0: Math.min(a.x0, r.x), y0: Math.min(a.y0, r.y), x1: Math.max(a.x1, r.x + r.width), y1: Math.max(a.y1, r.y + r.height) } : a;
        }, { x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity });
        if (Number.isFinite(bb.x0)) {
          e.rect.setAttribute("x", bb.x0 - pad); e.rect.setAttribute("y", bb.y0 - pad / 2);
          e.rect.setAttribute("width", bb.x1 - bb.x0 + pad * 2); e.rect.setAttribute("height", bb.y1 - bb.y0 + pad);
        } else if (b) {
          e.rect.setAttribute("width", 0);
        }
      } catch (_) { /* not laid out yet (hidden view): the label keeps no background */ }
    }
  }

  dragSite(g, i, G) {
    let start = null;
    const pt = (ev) => {
      const m = this.svg.getScreenCTM();
      if (!m) return [0, 0];
      const p = new DOMPoint(ev.clientX, ev.clientY).matrixTransform(m.inverse());
      return [p.x, p.y];
    };
    g.addEventListener("pointerdown", (ev) => {
      if (ev.target.closest(".node")) return;
      start = { p: pt(ev), cx: G.cx, cy: G.cy, moved: false };
      g.setPointerCapture(ev.pointerId);
    });
    g.addEventListener("pointermove", (ev) => {
      if (!start) return;
      const [x, y] = pt(ev);
      const dx = x - start.p[0], dy = y - start.p[1];
      if (Math.abs(dx) + Math.abs(dy) > 3) start.moved = true;
      if (start.moved) g.setAttribute("transform", `translate(${start.cx + dx - G.w / 2},${start.cy + dy - G.h / 2})`);
    });
    g.addEventListener("pointerup", (ev) => {
      if (!start) return;
      const [x, y] = pt(ev);
      const moved = start.moved;
      const pos = [Math.round(start.cx + x - start.p[0]), Math.round(start.cy + y - start.p[1])];
      start = null;
      if (moved) this.o.onMove(i, pos);
      else this.o.onSelect({ kind: "site", index: i });
    });
    g.addEventListener("keydown", (ev) => {
      if (ev.key === "Enter" || ev.key === " ") { ev.preventDefault(); this.o.onSelect({ kind: "site", index: i }); }
    });
  }

  // Live: per-node CPU, link flows and their text, link and node states.
  live({ topo, sample, cut = new Set(), nodeState = new Map() }) {
    if (!topo || !this.model) return;
    if (sample) {
      topo.nodes.forEach((n, j) => {
        const e = this.nodeEls[j];
        const ns = sample.nodes[j];
        if (!e || !ns) return;
        const cpus = Math.max(1, (n.cpus || "").split(",").length);
        const frac = Math.min(1, (ns.cpu || 0) / (100 * cpus));
        e.cpu.setAttribute("height", (14 * frac).toFixed(1));
        e.cpu.setAttribute("y", (16 - 14 * frac).toFixed(1));
      });
      const per = new Map();
      topo.shapers.forEach((sh, i) => {
        if (sh.of.kind !== "link") return;
        const v = sample.shapers[i];
        if (!v) return;
        const cur = per.get(sh.of.link) || { fwd: 0, rev: 0, drops: 0 };
        if (sh.of.forward) cur.fwd = v.bps; else cur.rev = v.bps;
        cur.drops += v.drops_ps;
        per.set(sh.of.link, cur);
      });
      for (const [k, v] of per) {
        const e = this.linkEls[k];
        if (!e) continue;
        const w = (bps, sh) => {
          if (bps < 1000) return 0;
          const cap = (sh.rate_mbit || 10000) * 1e6;
          return (1.2 + 6 * Math.min(1, bps / cap)).toFixed(2);
        };
        e.fwd.setAttribute("stroke-width", w(v.fwd, e.link.forward));
        e.rev.setAttribute("stroke-width", w(v.rev, e.link.reverse));
        const parts = [];
        if (v.fwd >= 1000 || v.rev >= 1000) parts.push(`→ ${bits(v.fwd)}  ← ${bits(v.rev)}`);
        if (v.drops >= 0.5) parts.push(`${num(v.drops)} drops/s`);
        e.liveText.textContent = parts.join(" · ");
      }
    }
    this.linkEls.forEach((e, k) => {
      if (!e) return;
      const isCut = cut.has(k);
      e.g.classList.toggle("cut", isCut);
      e.cut.setAttribute("visibility", isCut ? "visible" : "hidden");
      if (isCut) { e.fwd.setAttribute("stroke-width", 0); e.rev.setAttribute("stroke-width", 0); }
    });
    this.nodeEls.forEach((e, j) => {
      if (!e) return;
      const st = nodeState.get(j) || "";
      for (const c of ["active", "paused", "killed", "cut"]) e.g.classList.toggle(c, st === c);
      e.x.setAttribute("visibility", st === "killed" ? "visible" : "hidden");
    });
    this.fitLabels();
  }
}
