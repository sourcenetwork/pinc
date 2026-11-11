// Host: what this machine has, what the harness has running or left behind, and the clean-up.
import { h, clear, api, toast } from "../lib/dom.js";

let st = null;

export function mount(el) {
  st = { body: h("div", { class: "pane-body" }) };
  el.append(h("div", { class: "view host" }, h("section", { class: "pane" },
    h("div", { class: "pane-head" }, h("h2", {}, "Host"), h("button", { class: "btn", type: "button", onclick: load }, "Refresh")),
    st.body)));
  load();
}

export function unmount() { st = null; }

async function load() {
  if (!st) return;
  let d;
  try {
    d = await api("/api/host");
  } catch (e) {
    clear(st.body).append(h("div", { class: "empty" }, `The host cannot be read: ${e.message}`));
    return;
  }
  const left = d.containers.length + d.host_netem.length;
  const dockerOk = d.docker && d.docker.Ok;
  const cleanBtn = h("button", { class: "btn danger", type: "button", disabled: d.running, title: d.running ? "a run is going; its teardown removes what it created" : "", onclick: () => clean(cleanBtn) }, "Clean up");
  const out = h("div", {});
  clear(st.body).append(
    h("div", { class: "cols" },
      h("div", {}, h("h3", {}, "Machine"), h("dl", {},
        h("dt", {}, "CPU"), h("dd", {}, d.host.cpu),
        h("dt", {}, "CPUs"), h("dd", {}, String(d.host.cpus)),
        h("dt", {}, "memory"), h("dd", {}, `${d.host.mem_gib} GiB`),
        h("dt", {}, "kernel"), h("dd", {}, d.host.kernel),
        h("dt", {}, "Docker"), h("dd", { class: dockerOk ? "" : "status-bad" }, dockerOk ? d.docker.Ok : `not reachable: ${d.docker.Err}`),
        h("dt", {}, "node image"), h("dd", {}, d.image.present ? `${d.image.name} (${d.image.present.split(" ")[1] ? `${Math.round(Number(d.image.present.split(" ")[1]) / 1048576)} MiB` : "present"})` : `${d.image.name}, pulled on the first run`))),
      h("div", {}, h("h3", {}, "Harness"), h("dl", {},
        h("dt", {}, "run"), h("dd", {}, d.running ? `going: ${d.scenario}` : "none"),
        h("dt", {}, "containers"), h("dd", { class: d.containers.length && !d.running ? "status-bad" : "" }, d.containers.length ? `${d.containers.length} (${[...new Set(d.containers.map((c) => c.run))].join(", ")})` : "none"),
        h("dt", {}, "ifb module"), h("dd", {}, d.ifb_loaded ? "loaded (shapes what nodes send)" : "not loaded"),
        h("dt", {}, "shaping on the host"), h("dd", { class: d.host_netem.length ? "status-bad" : "status-good" }, d.host_netem.length ? d.host_netem.join("; ") : "none: every shaper lives in a router's namespace")))),
    h("div", { class: "row" }, cleanBtn,
      h("span", { class: "sub" }, d.running ? "A run is going; stop it in Live and its teardown removes everything." : left ? "Something is left from an earlier run: clean it up before the next one." : "Nothing is left from earlier runs.")),
    out,
  );
  st.out = out;
}

async function clean(btn) {
  btn.dataset.busy = "true";
  btn.disabled = true;
  try {
    const c = await api("/api/clean", { method: "POST" });
    const lines = [
      c.removed.length ? `Removed ${c.removed.length} container(s): ${c.removed.join(", ")}` : "No container to remove.",
      c.unloaded_ifb ? "Unloaded the ifb module a run had loaded." : null,
      c.left.length ? `Still there: ${c.left.join(", ")}` : "Checked: nothing is left.",
    ].filter(Boolean);
    toast(lines[lines.length - 1], c.left.length > 0);
    await load();
    st?.out?.append(h("pre", { class: "out" }, lines.join("\n")));
  } catch (e) {
    toast(`Clean-up failed: ${e.message}`, true);
    btn.disabled = false;
  } finally {
    btn.dataset.busy = "false";
  }
}
