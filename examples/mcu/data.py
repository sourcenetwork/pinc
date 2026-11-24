#!/usr/bin/env python3
"""The board's session as JSON data sets, in the shape of the PINC paper's `data/*.json`.

Usage: examples/mcu/data.py <session-dir>

It reads the result files of a session (`<clock>-opt-<level>.txt`) and writes one data set per optimisation level
beside them (`mcu-opt-3.json`, `mcu-opt-s.json`, `mcu-opt-z.json`). The columns (`stacks`) are the board's clocks.
Each cell is the median, the smallest and the largest value and how many there were; times are milliseconds, but for
the primitives, which are nanoseconds. A re-run on the same files writes the same bytes.
"""
import json, os, re, sys

src = out = sys.argv[1]
CLOCKS = ["64mhz", "320mhz", "600mhz"]
def r6(x):
    v = float(f"{x:.6g}")
    return int(v) if v == int(v) else v
kv = lambda line: dict(re.findall(r'(\w+)=("[^"]*"|\S+)', line))

def cell_us(d):
    return {"median": r6(int(d["median_us"]) / 1000), "min": r6(int(d["min_us"]) / 1000),
            "max": r6(int(d["max_us"]) / 1000), "n": int(d["n"])}

def one(v):
    return {"median": r6(v), "min": r6(v), "max": r6(v), "n": 1}

for level in ("3", "s", "z"):
    tests, meta, clocks = {}, {}, []
    def put(test, pair, metric, clock, cell):
        tests.setdefault(test, {}).setdefault(pair, {}).setdefault(metric, {})[clock] = cell
    for clock in CLOCKS:
        path = os.path.join(src, f"{clock}-opt-{level}.txt")
        if not os.path.exists(path):
            continue
        clocks.append(clock)
        lines = open(path).read().splitlines()
        cond, provider, sessions = {}, "software", []
        for l in lines:
            if l.startswith("conditions "):
                cond.update({k: v.strip('"') for k, v in kv(l).items()})
            elif l.startswith("summary handshake "):
                d = kv(l)
                what = l.split()[4]
                kind = "resumed" if d["resumed"] == "true" else "full"
                role = "accept" if d["board"] == "acceptor" else "dial"
                pair = "laptop>board" if role == "accept" else "board>laptop"
                put(f"handshake_{kind}_{role}", pair, f"{what}_ms", clock, cell_us(d))
            elif l.startswith("summary round_trip "):
                put("round_trip_32b", "board>laptop", "board_ms", clock, cell_us(kv(l)))
            elif l.startswith("summary stack "):
                put("memory", "board", "stack_peak_bytes", clock, one(int(kv(l)["board_peak_bytes"])))
            elif l.startswith("laptop round_trip ") and " n=200 " in l:
                put("round_trip_32b", "laptop>board", "laptop_ms", clock, cell_us(kv(l)))
            elif l.startswith("board crypto name="):
                d = kv(l)
                put("primitive_" + d["name"], "board", "software_ns", clock, one(int(d["software_ns"])))
                if "chip_ns" in d:
                    put("primitive_" + d["name"], "board", "chip_ns", clock, one(int(d["chip_ns"])))
            elif l.startswith("board crypto provider="):
                provider = kv(l)["provider"]
            elif l.startswith("board session "):
                sessions.append(int(kv(l)["cpu_us"]) / 1000)
            elif l.startswith("laptop echo "):
                put("echo_256kib", "laptop>board", "kib_per_s", clock, one(float(kv(l)["kib_per_s"])))
        if sessions:
            # The first session of a file carries the 200 round trips and the 256 KiB; it is the costliest.
            put("echo_256kib", "laptop>board", "board_session_cpu_ms", clock, one(max(sessions)))
        image = kv(next(l for l in lines if l.startswith("board image ")))
        built = kv(next(l for l in lines if l.startswith("board built ")))
        put("memory", "board", "flash_bytes", clock, one(int(image["flash"])))
        put("memory", "board", "statics_bytes", clock, one(int(image["statics"])))
        put("memory", "board", "endpoint_bytes", clock, one(int(built["endpoint"])))
        put("memory", "board", "slot_bytes", clock, one(int(built["slot"])))
        put("memory", "board", "session_memory_bytes", clock, one(int(built["memory"])))
        meta = {
            "board": "NUCLEO-H7S3L8 (STM32H7S3L8, Cortex-M7)",
            "link": f"serial line, {image['baud']} baud, one datagram a frame",
            "peer": {"cpu": cond.get("cpu"), "os": cond.get("laptop")},
            "commit": cond.get("commit"), "commit_source": "the result files' conditions lines",
            "rustc": cond.get("rustc"), "opt_level": level, "crypto": provider, "probe": cond.get("probe"),
            "date": cond.get("date", "")[:10], "repetitions": 10, "status": "ok",
        }
    name = f"mcu-opt-{level}"
    data = {"name": name, "source": os.path.basename(os.path.normpath(src)), "kind": "board", "meta": meta,
            "stacks": clocks, "tests": tests}
    json.dump(data, open(os.path.join(out, name + ".json"), "w"), indent=2)
    print(name, len(tests), "tests", clocks)
