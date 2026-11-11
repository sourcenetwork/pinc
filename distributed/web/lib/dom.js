// Tiny element builders. h("div", {class: "x", onclick: f}, child, "text") and s(...) for SVG.
const SVG = "http://www.w3.org/2000/svg";

function build(el, attrs, children) {
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v === undefined || v === null || v === false) continue;
    if (k.startsWith("on") && typeof v === "function") el.addEventListener(k.slice(2), v);
    else if (k === "style" && typeof v === "object") Object.assign(el.style, v);
    else if (k === "dataset") Object.assign(el.dataset, v);
    else if (k === "value" && "value" in el) el.value = v;
    else if (k === "checked" || k === "selected" || k === "disabled") el[k] = !!v;
    else el.setAttribute(k, v === true ? "" : v);
  }
  for (const c of children.flat(Infinity)) {
    if (c === undefined || c === null || c === false) continue;
    el.append(c instanceof Node ? c : document.createTextNode(String(c)));
  }
  return el;
}

export const h = (tag, attrs, ...children) => build(document.createElement(tag), attrs, children);
export const s = (tag, attrs, ...children) => build(document.createElementNS(SVG, tag), attrs, children);
export const clear = (el) => { while (el.firstChild) el.firstChild.remove(); return el; };

export async function api(path, opts = {}) {
  const init = { method: opts.method || "GET", headers: {} };
  if (opts.body !== undefined) {
    init.body = JSON.stringify(opts.body);
    init.headers["content-type"] = "application/json";
  }
  if (init.method !== "GET") init.headers["x-vd"] = "1";
  const r = await fetch(path, init);
  const text = await r.text();
  let data = null;
  try { data = text ? JSON.parse(text) : null; } catch (_) { data = text; }
  if (!r.ok) {
    const err = new Error((data && data.error) || `the server answered ${r.status}`);
    err.data = data;
    throw err;
  }
  return data;
}

let toastTimer = 0;
export function toast(msg, bad = false) {
  document.querySelector(".toast")?.remove();
  const t = h("div", { class: bad ? "toast bad" : "toast", role: bad ? "alert" : "status" }, msg);
  document.body.append(t);
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.remove(), bad ? 8000 : 3500);
}

// A numeric input bound to obj[key]; empty means absent when `optional`.
export function numField(label, obj, key, { unit = "", step = "any", min, max, optional = false, placeholder, onchange } = {}) {
  const input = h("input", {
    type: "number", step, min, max, placeholder,
    value: obj[key] ?? "",
    oninput: (e) => {
      const raw = e.target.value.trim();
      if (raw === "" && optional) delete obj[key];
      else if (raw !== "" && Number.isFinite(Number(raw))) obj[key] = Number(raw);
      onchange?.();
    },
  });
  return h("label", { class: "field" }, h("span", {}, label, unit ? h("span", { class: "unit" }, unit) : null), input);
}

export function textField(label, obj, key, { onchange, placeholder } = {}) {
  const input = h("input", { type: "text", value: obj[key] ?? "", placeholder, spellcheck: "false", oninput: (e) => { obj[key] = e.target.value; onchange?.(); } });
  return h("label", { class: "field" }, h("span", {}, label), input);
}

export function selectField(label, value, options, onpick) {
  const sel = h("select", { onchange: (e) => onpick(e.target.value) },
    options.map(([v, text]) => h("option", { value: v, selected: v === value }, text)));
  return h("label", { class: "field" }, h("span", {}, label), sel);
}
