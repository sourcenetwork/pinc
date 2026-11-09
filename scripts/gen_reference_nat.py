#!/usr/bin/env python3
"""Generates tests/data/reference_nat.txt: operation sequences run through the reference harness's NAT class.

Run isolated, from a directory outside the source tree:
`python3 -I /path/to/scripts/gen_reference_nat.py REFERENCE_DIR OUT`. Each case applies datagram operations
(outbound from a private host, inbound from a public server, rebind) and records what the NAT answered. The Rust test
(`tests/sim_nat_ref.rs`) replays them through the simulator.
"""
import hashlib
import importlib.util
import os
import random
import struct
import sys

spec = importlib.util.spec_from_file_location("refnet", os.path.join(os.path.abspath(sys.argv[1]), "net.py"))
net = importlib.util.module_from_spec(spec)
spec.loader.exec_module(net)

NS = 1_000_000_000
EXT = 2_000_000
PRIV = 3_000_001
SERVERS = (1_000_001, 1_000_002, 1_000_003)
out = []


def emit(*f):
    out.append(" ".join(str(x) for x in f))


for mapping in ("eim", "edm"):
    for filtering in ("eif", "adf", "apdf"):
        for seed in (1, 2, 3):
            name = "%s_%s_%d" % (mapping, filtering, seed)
            nat = net.Nat(0, EXT, mapping, filtering, 20 * NS, net._seed(seed, "nat", 0), False, 50 * NS)
            emit("natcase", name, seed, mapping, filtering)
            r = random.Random(seed * 1000 + 7)
            t = 0
            seen = []
            for _ in range(130):
                t += int(r.uniform(0.3, 7) * NS) + 1_000_000
                kind = r.random()
                if kind < 0.62 or not seen:
                    src = 4000 + r.randrange(6)
                    srv = r.randrange(3)
                    sport = 443 + r.randrange(2)
                    ext = nat.outbound(t, "udp", (PRIV, src), (SERVERS[srv], sport))
                    seen.append(ext[1])
                    emit("natop", name, "out", t, src, srv, sport, ext[1])
                elif kind < 0.9:
                    port = r.choice(seen) if r.random() < 0.9 else 20000 + r.randrange(100)
                    srv = r.randrange(3)
                    sport = 443 + r.randrange(2)
                    res = nat.inbound(t, "udp", (SERVERS[srv], sport), port, True)
                    emit("natop", name, "in", t, port, srv, sport, 0 if res is None else 1, 0 if res is None else res[1])
                else:
                    nat.rebind(t)
                    emit("natop", name, "rebind", t)
            emit("natend", name, nat.mapping_count(), nat.punched)

# many mappings: the port counter walks past 65000 and wraps back into 20000..21000 with no collision check
for seed in (1, 2):
    nat = net.Nat(0, EXT, "edm", "eif", 10**6 * NS, net._seed(seed, "nat", 0), False, 10**6 * NS)
    ports = []
    wraps = 0
    for k in range(9000):
        p = nat.outbound(k * 1_000_000, "udp", (PRIV, 4000), (SERVERS[0], 1000 + k))[1]
        if ports and p < ports[-1]:
            wraps += 1
        ports.append(p)
    h = hashlib.blake2b(b"".join(struct.pack("<I", p) for p in ports), digest_size=16).hexdigest()
    emit("natwrap", seed, len(ports), wraps, h, ",".join(map(str, ports[:5])))

open(sys.argv[2], "w").write("\n".join(out) + "\n")
