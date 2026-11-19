// Line charts on canvas: real units on both axes, one series per stack (hue and line pattern), redrawn at most once
// per animation frame however often data arrives.
const DASH = { pinc: [], iroh: [6, 4], libp2p: [2, 3], all: [] };

function niceStep(range, ticks) {
  const raw = range / Math.max(1, ticks);
  const p = 10 ** Math.floor(Math.log10(raw || 1));
  for (const m of [1, 2, 2.5, 5, 10]) if (raw <= m * p) return m * p;
  return 10 * p;
}

function cssVar(name) {
  return getComputedStyle(document.documentElement).getPropertyValue(name).trim() || "gray";
}

export class LineChart {
  constructor(canvas, { yUnit = "", yFmt = (v) => String(v), xFmt = (v) => String(v), xUnit = "s", windowSpan = null, markers = false } = {}) {
    this.c = canvas;
    this.o = { yUnit, yFmt, xFmt, xUnit, windowSpan, markers };
    this.series = [];
    this.bands = [];
    this.pending = false;
    this.ro = new ResizeObserver(() => this.redraw());
    this.ro.observe(canvas);
  }

  set(series, bands = []) {
    this.series = series;
    this.bands = bands;
    this.redraw();
  }

  redraw() {
    if (this.pending) return;
    this.pending = true;
    requestAnimationFrame(() => { this.pending = false; this.draw(); });
  }

  destroy() { this.ro.disconnect(); }

  draw() {
    const c = this.c;
    const dpr = window.devicePixelRatio || 1;
    const w = c.clientWidth, hgt = c.clientHeight;
    if (!w || !hgt) return;
    if (c.width !== Math.round(w * dpr) || c.height !== Math.round(hgt * dpr)) {
      c.width = Math.round(w * dpr);
      c.height = Math.round(hgt * dpr);
    }
    const g = c.getContext("2d");
    g.setTransform(dpr, 0, 0, dpr, 0, 0);
    g.clearRect(0, 0, w, hgt);
    const ink = cssVar("--ink-2"), muted = cssVar("--muted"), rule = cssVar("--rule"), mono = cssVar("--font-mono");
    const pts = this.series.flatMap((s) => s.points);
    const L = 46, R = 8, T = 8, B = 20;
    g.font = `10px ${mono}`;
    if (!pts.length) {
      g.fillStyle = muted;
      g.fillText("no data yet", L, T + 14);
      return;
    }
    let x1 = Math.max(...pts.map((p) => p[0]));
    let x0 = this.o.windowSpan ? x1 - this.o.windowSpan : Math.min(...pts.map((p) => p[0]));
    if (x1 - x0 < 1e-9) { x0 -= 1; x1 += 1; }
    const visible = pts.filter((p) => p[0] >= x0);
    let y1 = Math.max(...visible.map((p) => p[1]), 0);
    const y0 = 0;
    if (y1 <= 0) y1 = 1;
    const ys = niceStep(y1 - y0, 4);
    y1 = Math.ceil(y1 / ys) * ys;
    const X = (x) => L + ((x - x0) / (x1 - x0)) * (w - L - R);
    const Y = (y) => T + (1 - (y - y0) / (y1 - y0)) * (hgt - T - B);
    // Bands: who ran when (a faint stack-coloured strip along the bottom).
    for (const b of this.bands) {
      if (b.to < x0) continue;
      g.fillStyle = cssVar(`--s-${b.stack}`);
      g.globalAlpha = 0.5;
      g.fillRect(X(Math.max(b.from, x0)), hgt - B + 2, Math.max(1, X(b.to) - X(Math.max(b.from, x0))), 3);
      g.globalAlpha = 1;
    }
    g.strokeStyle = rule;
    g.lineWidth = 1;
    g.fillStyle = muted;
    g.textAlign = "right";
    g.textBaseline = "middle";
    for (let y = y0; y <= y1 + ys / 2; y += ys) {
      const py = Math.round(Y(y)) + 0.5;
      g.beginPath(); g.moveTo(L, py); g.lineTo(w - R, py); g.stroke();
      g.fillText(this.o.yFmt(y), L - 6, py);
    }
    g.textAlign = "left";
    g.textBaseline = "top";
    g.fillText(this.o.yUnit, 2, 0);
    const xs = niceStep(x1 - x0, Math.max(2, Math.floor((w - L) / 80)));
    g.textAlign = "center";
    for (let x = Math.ceil(x0 / xs) * xs; x <= x1 + 1e-9; x += xs) {
      g.fillText(`${this.o.xFmt(x)}${this.o.xUnit}`, X(x), hgt - B + 7);
    }
    for (const s of this.series) {
      const p = s.points.filter((q) => q[0] >= x0);
      if (!p.length) continue;
      g.strokeStyle = cssVar(s.color || `--s-${s.stack}`) || ink;
      g.fillStyle = g.strokeStyle;
      g.setLineDash(DASH[s.stack] || []);
      g.lineWidth = 1.6;
      g.beginPath();
      p.forEach((q, i) => (i ? g.lineTo(X(q[0]), Y(q[1])) : g.moveTo(X(q[0]), Y(q[1]))));
      g.stroke();
      g.setLineDash([]);
      if (this.o.markers) {
        for (const q of p) {
          g.beginPath();
          if (s.stack === "iroh") g.rect(X(q[0]) - 2.5, Y(q[1]) - 2.5, 5, 5);
          else if (s.stack === "libp2p") { g.moveTo(X(q[0]), Y(q[1]) - 3.5); g.lineTo(X(q[0]) + 3.5, Y(q[1]) + 2.5); g.lineTo(X(q[0]) - 3.5, Y(q[1]) + 2.5); g.closePath(); }
          else g.arc(X(q[0]), Y(q[1]), 2.8, 0, Math.PI * 2);
          g.fill();
        }
      }
    }
  }
}
