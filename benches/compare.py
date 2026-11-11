#!/usr/bin/env python3
"""Run the comparison matrix of VINC, iroh and rust-libp2p on this machine and write the results.

Run it on the benchmark host with nothing else running (`VINC_JOB_EXCLUSIVE=1 vinc-job just compare`). It builds the
three `compare_*` benches, then for every library, scenario and network profile starts a fresh server process and a
fresh client process on loopback, repeats each run, and writes under `benches/results/<date>-<host>/`:

  raw.jsonl   every result line exactly as the client printed it, with the library, profile and repetition
  results.md  the table: the median over the repetitions and the range [min..max] of every number
  run.json    the host, the versions, the parameters and the commands that shaped the network

Shaped networks use `tc netem` on the loopback device (sudo). The qdisc is removed after every run, also on an error
or an interrupt. A scenario that did not run, timed out or failed is written as such; nothing is estimated.
"""
import argparse
import datetime
import json
import os
import platform
import re
import signal
import statistics
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# (name shown, bench binary, variant argument)
LIBS = [
    ("vinc", "compare_vinc", None),
    ("iroh", "compare_iroh", None),
    ("libp2p-quic", "compare_libp2p", "quic"),
    ("libp2p-tcp", "compare_libp2p", "tcp"),
]

# network profile -> (netem arguments for lo or None, description)
PROFILES = {
    "loopback": (None, "loopback, no shaping"),
    "rtt50-loss1": (
        "delay 25ms loss 1%",
        "50 ms RTT, 1% loss per packet in each direction (25 ms each way on lo)",
    ),
    "rtt200-loss5-reorder": (
        "delay 100ms 30ms distribution normal loss 5%",
        "200 ms RTT, 5% loss per packet in each direction, 30 ms jitter (which reorders packets)",
    ),
}

GIB = 1 << 30
MIB = 1 << 20

# scenario id -> {profile: (client arguments, repetitions, timeout seconds, server extra arguments)}
SCENARIOS = {
    "setup": {
        "loopback": (["setup", "200"], 3, 600, []),
        "rtt50-loss1": (["setup", "20"], 3, 600, []),
        "rtt200-loss5-reorder": (["setup", "10"], 3, 900, []),
    },
    "resume": {
        "loopback": (["resume", "200"], 3, 600, []),
        "rtt50-loss1": (["resume", "20"], 3, 600, []),
        "rtt200-loss5-reorder": (["resume", "10"], 3, 900, []),
    },
    "throughput_1s": {
        "loopback": (["throughput", str(GIB), "1"], 5, 900, []),
        "rtt50-loss1": (["throughput", str(32 * MIB), "1"], 3, 900, []),
        "rtt200-loss5-reorder": (["throughput", str(8 * MIB), "1"], 3, 900, []),
    },
    "throughput_16s": {
        "loopback": (["throughput", str(GIB), "16"], 5, 900, []),
        "rtt50-loss1": (["throughput", str(32 * MIB), "16"], 3, 900, []),
        "rtt200-loss5-reorder": (["throughput", str(8 * MIB), "16"], 3, 900, []),
    },
    "latency_64b": {
        "loopback": (["latency", "64", "100000"], 3, 900, []),
        "rtt50-loss1": (["latency", "64", "1000"], 3, 900, []),
        "rtt200-loss5-reorder": (["latency", "64", "300"], 3, 900, []),
    },
    "latency_1024b": {
        "loopback": (["latency", "1024", "100000"], 3, 900, []),
        "rtt50-loss1": (["latency", "1024", "1000"], 3, 900, []),
        "rtt200-loss5-reorder": (["latency", "1024", "300"], 3, 900, []),
    },
    "many": {"loopback": (["many", "1000", "65536"], 3, 900, [])},
    "allocs_latency_64b": {"loopback": (["allocs", "20000", str(64 * MIB)], 3, 900, ["--count-allocs"])},
}

# scenario id -> the result line's scenario name, and the metrics to show: (key, label, unit)
SHOW = {
    "setup": ("setup", [("p50_us", "p50", "us"), ("p99_us", "p99", "us"), ("failed", "failed", "")]),
    "resume": ("resume", [("p50_us", "p50", "us"), ("p99_us", "p99", "us"), ("failed", "failed", "")]),
    "throughput_1s": (
        "throughput_1s",
        [("mib_s", "MiB/s", ""), ("cpu_ns_per_byte", "CPU ns/byte (both ends)", ""), ("streams_ok", "streams ok", "")],
    ),
    "throughput_16s": (
        "throughput_16s",
        [("mib_s", "MiB/s", ""), ("cpu_ns_per_byte", "CPU ns/byte (both ends)", ""), ("streams_ok", "streams ok", "")],
    ),
    "latency_64b": (
        "latency_64b",
        [("p50_us", "p50", "us"), ("p99_us", "p99", "us"), ("p999_us", "p99.9", "us"), ("round_trips", "round trips", "")],
    ),
    "latency_1024b": (
        "latency_1024b",
        [("p50_us", "p50", "us"), ("p99_us", "p99", "us"), ("p999_us", "p99.9", "us"), ("round_trips", "round trips", "")],
    ),
    "many": (
        "many",
        [
            ("connected_and_moved", "connected", ""),
            ("failed", "failed", ""),
            ("all_done_s", "all done (s)", ""),
            ("first_byte_p50_ms", "first byte p50 (ms)", ""),
            ("first_byte_p99_ms", "first byte p99 (ms)", ""),
            ("server_kib_per_conn", "server KiB/conn", ""),
            ("client_kib_per_conn", "client KiB/conn", ""),
            ("server_cpu_s", "server CPU s", ""),
            ("client_cpu_s", "client CPU s", ""),
        ],
    ),
    "allocs_latency_64b": (
        "latency_64b",
        [
            ("client_allocs_per_rt", "client allocs/round trip", ""),
            ("server_allocs_per_rt", "server allocs/round trip", ""),
        ],
    ),
}
ALLOC_BULK = [
    ("client_allocs_per_msg", "client allocs/64 KiB msg", ""),
    ("server_allocs_per_msg", "server allocs/64 KiB msg", ""),
    ("client_alloc_bytes_per_msg", "client alloc bytes/msg", ""),
    ("server_alloc_bytes_per_msg", "server alloc bytes/msg", ""),
]


def sh(cmd, **kw):
    return subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True, text=True, **kw)


def netem_clear():
    sh("sudo -n tc qdisc del dev lo root 2>/dev/null")


def netem_set(args):
    netem_clear()
    r = sh(f"sudo -n tc qdisc add dev lo root netem {args}")
    return r.returncode == 0, r.stderr.strip()


def build(cargo, target_dir):
    """Build the benches once and return {bench name: executable}. The benches are a workspace of their own."""
    cmd = [cargo, "bench", "--manifest-path", os.path.join(ROOT, "benches", "Cargo.toml"), "--no-run", "--message-format=json"]
    if target_dir:
        cmd += ["--target-dir", target_dir]
    for b in ("compare_vinc", "compare_iroh", "compare_libp2p"):
        cmd += ["--bench", b]
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit("the benches did not build:\n" + p.stderr[-4000:])
    exes = {}
    for line in p.stdout.splitlines():
        try:
            m = json.loads(line)
        except ValueError:
            continue
        if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"].startswith("compare_"):
            exes[m["target"]["name"]] = m["executable"]
    return exes


def start_server(exe, variant, extra):
    cmd = [exe, "server"] + extra + ([f"--variant={variant}"] if variant else [])
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    deadline = time.time() + 60
    while time.time() < deadline:
        line = p.stdout.readline()
        if line.startswith("ADDR "):
            return p, line.split(None, 1)[1].strip()
        if not line and p.poll() is not None:
            break
    stop(p)
    return None, None


def stop(p):
    if p and p.poll() is None:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    if p:
        p.wait()


def run_once(exe, variant, args, timeout, server_extra):
    """One fresh server and client: (list of result dicts, status text)."""
    srv, addr = start_server(exe, variant, server_extra)
    if srv is None:
        return [], "the server did not start"
    try:
        cmd = [exe, "client", addr] + args + ([f"--variant={variant}"] if variant else [])
        try:
            c = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return [], f"timed out after {timeout} s"
        out = []
        for line in c.stdout.splitlines():
            try:
                out.append(json.loads(line))
            except ValueError:
                pass
        if c.returncode != 0 and not out:
            return [], "the client failed: " + c.stderr.strip()[-300:]
        return out, "ok"
    finally:
        stop(srv)


def scaled(args, k):
    """Scale the main count or size of a scenario for a smoke run."""
    if k == 1.0:
        return args
    a = list(args)
    i = 1 + {"setup": 0, "resume": 0, "throughput": 0, "latency": 1, "many": 0, "allocs": 0}[a[0]]
    a[i] = str(max(1, int(int(a[i]) * k)))
    if a[0] == "allocs":
        a[2] = str(max(1 << 16, int(int(a[2]) * k)))
    return a


def cargo_lock_version(name):
    text = open(os.path.join(ROOT, "Cargo.lock")).read()
    m = re.search(r'name = "%s"\nversion = "([^"]+)"' % re.escape(name), text)
    return m.group(1) if m else "unknown"


def host_info():
    cpu = next((l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name")), "unknown")
    mem = next((l.split()[1] for l in open("/proc/meminfo") if l.startswith("MemTotal")), "0")
    return {
        "host": platform.node(),
        "cpu": cpu,
        "cores": os.cpu_count(),
        "mem_gib": round(int(mem) / 1048576, 1),
        "kernel": platform.release(),
        "rustc": sh("rustc -V").stdout.strip(),
        "git": sh(f"git -C {ROOT} rev-parse --short HEAD").stdout.strip(),
        "versions": {n: cargo_lock_version(n) for n in ("iroh", "noq", "libp2p", "libp2p-quic", "libp2p-stream", "quinn", "tokio", "nuclei")},
        "loadavg_at_start": open("/proc/loadavg").read().strip(),
    }


def fmt(v):
    if v is None:
        return "-"
    if v == int(v) and abs(v) < 1e6:
        return f"{int(v):,}"
    if abs(v) >= 1000:
        return f"{v:,.0f}"
    if abs(v) >= 100:
        return f"{v:.0f}"
    if abs(v) >= 10:
        return f"{v:.1f}"
    return f"{v:.2f}"


def cell(vals):
    vals = [v for v in vals if v is not None]
    if not vals:
        return "not measured"
    if len(vals) == 1:
        return fmt(vals[0])
    return f"{fmt(statistics.median(vals))} [{fmt(min(vals))}..{fmt(max(vals))}]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    ap.add_argument("--libs", default=",".join(n for n, _, _ in LIBS))
    ap.add_argument("--profiles", default=",".join(PROFILES))
    ap.add_argument("--scenarios", default=",".join(SCENARIOS))
    ap.add_argument("--reps", type=int, default=None, help="override the repetitions (a smoke run uses 1)")
    ap.add_argument("--scale", type=float, default=1.0, help="multiply every count and size (a smoke run uses 0.01)")
    ap.add_argument("--cargo", default="cargo")
    ap.add_argument("--target-dir", default=None, help="cargo's build directory for the benches workspace")
    ap.add_argument("--max-timeout", type=int, default=None, help="cap every run's timeout in seconds (keeps a window short)")
    a = ap.parse_args()
    libs = [l for l in LIBS if l[0] in a.libs.split(",")]
    profiles = a.profiles.split(",")
    scen = a.scenarios.split(",")

    # A SIGTERM ends the run the way SIGINT does, so the `finally` below always removes the qdisc.
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    info = host_info()
    date = datetime.date.today().isoformat()
    out = a.out or os.path.join(ROOT, "benches", "results", f"{date}-{info['host']}")
    os.makedirs(out, exist_ok=True)
    exes = build(a.cargo, a.target_dir)
    have_tc = sh("sudo -n tc -V").returncode == 0
    info["tc"] = sh("sudo -n tc -V").stdout.strip() if have_tc else "not available"
    info["profiles"] = {k: {"netem": v[0], "what": v[1]} for k, v in PROFILES.items() if k in profiles}
    info["tc_commands"] = {k: [f"sudo tc qdisc add dev lo root netem {v[0]}", "sudo tc qdisc del dev lo root"] for k, v in PROFILES.items() if v[0]}
    run = int(time.time())
    # Appended to, so a run split over several invocations (one per profile, say) fills one directory.
    raw = open(os.path.join(out, "raw.jsonl"), "a")
    status_log = open(os.path.join(out, "status.jsonl"), "a")
    try:
        for prof in profiles:
            netem = PROFILES[prof][0]
            if netem:
                if not have_tc:
                    for s in scen:
                        for name, _, _ in libs:
                            note(status_log, s, prof, name, run, "not measured: tc (iproute-tc) or sudo is not available on this host")
                    continue
                ok, err = netem_set(netem)
                if not ok:
                    sys.exit(f"tc netem failed: {err}")
            for s in scen:
                if prof not in SCENARIOS[s]:
                    continue
                args, reps, timeout, extra = SCENARIOS[s][prof]
                if a.max_timeout:
                    timeout = min(timeout, a.max_timeout)
                args = scaled(args, a.scale)
                reps = a.reps or reps
                for name, bench, variant in libs:
                    status = "ok"
                    for r in range(reps):
                        la = open("/proc/loadavg").read().split()[0]
                        got, st = run_once(exes[bench], variant, args, timeout, extra)
                        if st != "ok":
                            status = st
                            print(f"{prof} {s} {name} rep {r}: {st}", flush=True)
                            break
                        for g in got:
                            g.update(profile=prof, rep=r, load1=la, args=args, sid=s, run=run, name=name)
                            raw.write(json.dumps(g) + "\n")
                            raw.flush()
                        print(f"{prof} {s} {name} rep {r}: ok", flush=True)
                    if status != "ok":
                        note(status_log, s, prof, name, run, f"not measured: {status}")
            if netem:
                netem_clear()
    finally:
        netem_clear()
        raw.close()
        status_log.close()
    json.dump(info, open(os.path.join(out, f"run-{run}.json"), "w"), indent=2)
    write_md(out, info, libs, profiles, scen, collect(out), a)
    print("wrote", out)


def note(log, sid, prof, name, run, text):
    log.write(json.dumps({"sid": sid, "profile": prof, "name": name, "run": run, "status": text}) + "\n")
    log.flush()


def collect(out):
    """Read the raw lines and the failure notes of this directory: (scenario, profile, lib) -> the newest run's lines, or
    a status string when the newest word on it is a failure."""
    by_args = {(tuple(v[0]), p): s for s, d in SCENARIOS.items() for p, v in d.items()}
    best = {}  # key -> (run, lines or status)
    for fname, is_note in (("raw.jsonl", False), ("status.jsonl", True)):
        path = os.path.join(out, fname)
        if not os.path.exists(path):
            continue
        for line in open(path):
            try:
                g = json.loads(line)
            except ValueError:
                continue
            sid = g.get("sid") or by_args.get((tuple(g.get("args", [])), g.get("profile")))
            key = (sid, g.get("profile"), g.get("name") or g.get("lib"))
            run = g.get("run", 0)
            cur = best.get(key)
            if cur is None or run > cur[0]:
                cur = best[key] = (run, [] if not is_note else g["status"])
            if run == cur[0] and not is_note and isinstance(cur[1], list):
                cur[1].append(g)
    return {k: v[1] for k, v in best.items()}


def write_md(out, info, libs, profiles, scen, results, a):
    md = [f"# VINC against iroh and rust-libp2p\n"]
    md.append(f"Date {datetime.date.today().isoformat()}, host `{info['host']}`: {info['cpu']}, {info['cores']} cores, {info['mem_gib']} GiB, kernel {info['kernel']}, {info['rustc']}, commit {info['git']}.")
    md.append("Versions: " + ", ".join(f"{k} {v}" for k, v in info["versions"].items()) + ".")
    md.append("Every cell is the median over the repetitions with the range [min..max]; a single value is one run. The client and the server are two processes on loopback.")
    if a.scale != 1.0 or a.reps:
        md.append(f"\n**This is a reduced run (scale {a.scale}, reps {a.reps}); do not quote it.**")
    for prof in profiles:
        md.append(f"\n## Network: {PROFILES[prof][1]}\n")
        if PROFILES[prof][0]:
            md.append(f"`sudo tc qdisc add dev lo root netem {PROFILES[prof][0]}`, removed with `sudo tc qdisc del dev lo root` after the run.\n")
        for s in scen:
            if prof not in SCENARIOS[s]:
                continue
            key, cols = SHOW[s]
            args, reps, _, _ = SCENARIOS[s][prof]
            md.append(f"### {s} ({' '.join(args)}; {reps} runs)\n")
            rows = []
            extra_cols = ALLOC_BULK if s == "allocs_latency_64b" else []
            head = ["library"] + [c[1] for c in cols] + [c[1] for c in extra_cols] + ["note"]
            md.append("| " + " | ".join(head) + " |")
            md.append("|" + "---|" * len(head))
            for name, _, _ in libs:
                res = results.get((s, prof, name))
                if res is None:
                    continue
                if isinstance(res, str):
                    md.append(f"| {name} | " + " | ".join(["-"] * (len(head) - 2)) + f" | {res.replace(chr(10), ' ')} |")
                    continue
                main_lines = [g for g in res if g["scenario"] == key]
                bulk = [g for g in res if g["scenario"] == "allocs_bulk"]
                notes = sorted({(g.get("note") or g.get("status") or g.get("last_error") or "") for g in main_lines + bulk} - {"", "ok"})
                cells = [cell([g.get(k) for g in main_lines]) for k, _, _ in cols]
                cells += [cell([g.get(k) for g in bulk]) for k, _, _ in extra_cols]
                md.append(f"| {name} | " + " | ".join(cells) + " | " + "; ".join(n for n in notes if n) + " |")
            md.append("")
    open(os.path.join(out, "results.md"), "w").write("\n".join(md) + "\n")


if __name__ == "__main__":
    main()
