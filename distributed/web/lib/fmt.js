// Numbers as an instrument shows them: real units, no needless digits.
export function num(v, digits) {
  if (v === null || v === undefined || !Number.isFinite(v)) return "—";
  const a = Math.abs(v);
  if (digits !== undefined) return v.toFixed(digits);
  if (Number.isInteger(v) && a < 1e9) return v.toLocaleString("en-US");
  if (a >= 1000) return Math.round(v).toLocaleString("en-US");
  if (a >= 100) return v.toFixed(0);
  if (a >= 10) return v.toFixed(1);
  if (a >= 0.01) return v.toFixed(2);
  return v.toPrecision(2);
}

export function bits(bps) {
  if (bps === null || bps === undefined || !Number.isFinite(bps)) return "—";
  const units = [["Gbit/s", 1e9], ["Mbit/s", 1e6], ["kbit/s", 1e3]];
  for (const [u, f] of units) if (Math.abs(bps) >= f) return `${num(bps / f)} ${u}`;
  return `${num(bps)} bit/s`;
}

export function bytes(b) {
  if (b === null || b === undefined || !Number.isFinite(b)) return "—";
  const units = [["GiB", 2 ** 30], ["MiB", 2 ** 20], ["KiB", 2 ** 10]];
  for (const [u, f] of units) if (Math.abs(b) >= f) return `${num(b / f)} ${u}`;
  return `${num(b)} B`;
}

export function rate(mbit) {
  if (mbit === undefined || mbit === null) return "no limit";
  return mbit >= 1000 ? `${num(mbit / 1000)} Gbit/s` : `${num(mbit)} Mbit/s`;
}

export function shape(sh) {
  if (!sh) return "";
  const parts = [`${num(sh.delay_ms ?? 0)} ms`];
  if (sh.jitter_ms) parts.push(`±${num(sh.jitter_ms)} ms`);
  if (sh.loss_pct) parts.push(`${num(sh.loss_pct)}% loss`);
  parts.push(rate(sh.rate_mbit));
  return parts.join(" · ");
}

export function clock(ms) {
  const s = Math.max(0, Math.floor(ms / 1000));
  const m = Math.floor(s / 60);
  return `${String(m).padStart(2, "0")}:${String(s % 60).padStart(2, "0")}`;
}

export function when(unixSecs) {
  if (!unixSecs) return "—";
  const d = new Date(unixSecs * 1000);
  return d.toISOString().replace("T", " ").slice(0, 16) + " UTC";
}

export const STACKS = ["vinc", "iroh", "libp2p"];
