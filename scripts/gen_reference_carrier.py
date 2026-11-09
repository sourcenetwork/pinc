#!/usr/bin/env python3
"""Generates tests/data/reference_carrier.txt: scenarios run through the reference harness's own network, NAT,
middlebox and TCP code, with the timeline each end saw.

Run isolated, from a directory outside the source tree:
`python3 -I /path/to/scripts/gen_reference_carrier.py REFERENCE_DIR OUT` where REFERENCE_DIR is the directory of
the reference harness package. The harness runs with a stub in place of the protocol: the stub records every
interface event and every record, and the script drives connects, writes and closes itself.

Output lines: `scn` (the scenario), `site`, `nat`, `box`, `cut`, `op`, then the observed `ev`, `rec` and `wire`
lines. The Rust test (`tests/sim_carrier_ref.rs`) rebuilds each scenario and compares every line.
"""
import importlib
import os
import sys

ref = os.path.abspath(sys.argv[1])
sys.path.insert(0, os.path.dirname(ref))
pkg = os.path.basename(ref)
simmod = importlib.import_module(pkg + ".sim")
netmod = importlib.import_module(pkg + ".net")
api = importlib.import_module(pkg + ".protocol_api")

NS = 1_000_000_000
MS = 1_000_000
out = []


def emit(*f):
    out.append(" ".join(str(x) for x in f))


class Rq:
    def __init__(self, op, iface=None, dst=None, arg=None):
        self.op, self.iface, self.dst, self.arg = op, iface, dst, arg


class Core:
    def __init__(self, log, idx):
        self.log, self.idx = log, idx

    def handle_iface_event(self, now, ifc, ev):
        a = ev.arg
        if ev.kind == "stream_pending":
            self.log.append(("ev", self.idx, now, "pending", a[0], a[1][1], a[1][2]))
        elif ev.kind == "stream_opened":
            self.log.append(("ev", self.idx, now, "opened", a[0], a[1][1], a[1][2]))
        elif ev.kind in ("stream_failed", "stream_closed"):
            self.log.append(("ev", self.idx, now, ev.kind.split("_")[1], a, 0, 0))

    def handle_input(self, now, ifc, src, parts, n, ecn):
        data = b"".join(parts)
        self.log.append(("rec", self.idx, now, src[1], n, sum(data) % 1000003))


def payload(i, n):
    return bytes((i + j) % 256 for j in range(n))


def run(sc):
    seed = sc["seed"]
    sites = []
    for s in sc["sites"]:
        d = dict(sid=s["sid"], region=s["region"], up_bps=s["up_bps"], up_delay_ns=s["up_delay"],
                 down_bps=s["down_bps"], down_delay_ns=s["down_delay"], queue_bytes=s["queue"], loss=s["loss"],
                 burst_ns=s["burst"], nats=[])
        if s.get("nat"):
            n = s["nat"]
            d["nats"] = [dict(nid=s["sid"], ext_ip=n["ext"], mapping=n["mapping"], filtering=n["filtering"],
                              timeout_ns=n["timeout"], tcp_timeout_ns=n["tcp_timeout"], no_punch=False)]
        if s.get("box"):
            b = s["box"]
            mb = {"udp_block": b["udp_block"], "tcp_ports": b["ports"], "tls_only": b["tls_only"],
                  "fw_reject": b["reject"]}
            if b["portal"]:
                mb["portal_ns"] = b["portal"]
            d["middlebox"] = mb
        sites.append(d)
    nodes = []
    for i, s in enumerate(sc["sites"]):
        host = s["host"]
        if s.get("nat"):
            ifaces = [dict(name="t", kind="tcp", addr=("tcp4", host, 50000), mtu=1 << 20),
                      dict(name="w", kind="ws", addr=("tcp4", host, 50001), mtu=1 << 20)]
            if s.get("client_port"):
                ifaces.append(dict(name="c", kind="tcp", addr=("tcp4", host, s["client_port"]), mtu=1 << 20))
        else:
            ifaces = [dict(name="t", kind="tcp", addr=("tcp4", host, 443), mtu=1 << 20, public=True),
                      dict(name="w", kind="ws", addr=("tcp4", host, 8443), mtu=1 << 20, public=True)]
            if s.get("client_port"):
                ifaces.append(dict(name="c", kind="tcp", addr=("tcp4", host, s["client_port"]), mtu=1 << 20,
                                   public=True))
        nodes.append(dict(device="desktop", site=s["sid"], ifaces=ifaces))
    rd = sc["region_delay"]
    scenario = dict(sites=sites, nodes=nodes, region_delay_ns=[[0, rd], [rd, 0]],
                    partitions=[(a, b, tuple(x), tuple(y), m) for (a, b, x, y, m) in sc["cuts"]], bootstrap=())
    sim = simmod.Sim(scenario, "", seed)
    sim.rec.finish = lambda until: None
    log = []
    for rt in sim.nodes:
        rt.alive = True
        rt.incarnation = 1
        rt.core = Core(log, rt.idx)
        rt.pump = lambda now: None
        rt.build_ifaces()
        mb = rt.site.mb
        if mb is not None and mb.portal_ns:
            rt.portal_until = mb.portal_ns
    ops = sc["ops"]

    def do(t, op):
        rt = sim.nodes[op["node"]]
        if op["kind"] == "connect":
            name = {"tcp": "t", "ws": "w"}[op["carrier"]]
            if op.get("simul"):
                name = "c"
            sim.iface_request(t, rt, Rq("open_stream", name, op["dst"], "simultaneous" if op.get("simul") else None))
        elif op["kind"] == "write":
            end = rt.tcp.get(op["handle"])
            if end is not None and not end.closed and end.state == "open":
                sim._tcp_write(t, end, (payload(op["i"], op["len"]),))
            else:
                log.append(("werr", op["node"], t, op["handle"], 0, 0))
        elif op["kind"] == "close":
            end = rt.tcp.get(op["handle"])
            sim.iface_request(t, rt, Rq("close_stream", end.iface.name if end else "t", op["handle"]))

    for k, op in enumerate(ops):
        op["i"] = k
        sim.push(op["t"], "env", lambda tt, op=op: do(tt, op))
    sim.run(sc["until"])
    return sim, log


def describe(sc):
    emit("scn", sc["name"], "seed=%d" % sc["seed"], "until=%d" % sc["until"], "region_delay=%d" % sc["region_delay"])
    for s in sc["sites"]:
        emit("site", *["%s=%d" % (k, s[k]) for k in ("sid", "region", "up_bps", "up_delay", "down_bps", "down_delay",
                                                       "queue", "burst", "host")],
             "loss=%r" % s["loss"], "client_port=%d" % s.get("client_port", 0))
        if s.get("nat"):
            n = s["nat"]
            emit("nat", s["sid"], n["ext"], n["mapping"], n["filtering"], n["timeout"], n["tcp_timeout"])
        if s.get("box"):
            b = s["box"]
            emit("box", s["sid"], int(b["udp_block"]), ",".join(map(str, b["ports"])) if b["ports"] else "-",
                 int(b["tls_only"]), int(b["reject"]), b["portal"])
    for a, b, x, y, m in sc["cuts"]:
        emit("cut", a, b, ",".join(map(str, x)), ",".join(map(str, y)), m)
    for op in sc["ops"]:
        emit("op", op["t"], op["node"], op["kind"], op.get("carrier", "-"), op.get("dst", ("-", 0, 0))[1],
             op.get("dst", ("-", 0, 0))[2], op.get("handle", 0), op.get("len", 0), int(bool(op.get("simul"))))


def site(sid, host, bps=20_000_000, delay=10 * MS, q=1 << 20, loss=0.0, burst=20 * MS, region=0, **kw):
    s = dict(sid=sid, region=region, up_bps=bps, up_delay=delay // 2, down_bps=bps, down_delay=delay // 2, queue=q,
             loss=loss, burst=burst, host=host)
    s.update(kw)
    return s


SERVER_HOST = 1_000_001
CLIENT_HOST = 3_000_001
NAT_EXT = 2_000_000


def base(name, seed, ops, until, client=None, server=None, cuts=(), rd=0):
    c = dict(site(0, CLIENT_HOST))
    c.update(client or {})
    s = dict(site(1, SERVER_HOST, bps=1_000_000_000, delay=2 * MS, region=1))
    s.update(server or {})
    return dict(name=name, seed=seed, sites=[c, s], ops=ops, until=until, cuts=list(cuts), region_delay=rd)


def conn(t, carrier, node=0, port=None):
    port = port or {"tcp": 443, "ws": 8443}[carrier]
    return dict(t=t, node=node, kind="connect", carrier=carrier, dst=("tcp4", SERVER_HOST, port))


def wr(t, handle, n, node=0):
    return dict(t=t, node=node, kind="write", handle=handle, len=n)


def cl(t, handle, node=0):
    return dict(t=t, node=node, kind="close", handle=handle)


scenarios = []
for seed in (1, 2, 3, 4, 5):
    ops = [conn(0, "tcp"), conn(0, "ws")]
    ops += [wr(2 * NS + k * 10 * MS, 1 + (k % 2), 300 + 97 * k) for k in range(120)]
    ops += [wr(2 * NS + k * 30 * MS, 1 + (k % 2), 1000 + 61 * k, node=1) for k in range(60)]
    scenarios.append(base("bulk_lossy_%d" % seed, seed, ops, 120 * NS,
                          client=dict(loss=0.04, burst=25 * MS, bps=8_000_000, delay=60 * MS, q=64 << 10),
                          server=dict(loss=0.01, burst=10 * MS)))
for seed in (11, 12):
    ops = [conn(0, "tcp")] + [wr(NS + k * 2 * MS, 1, 1448 * 3 + k) for k in range(400)]
    scenarios.append(base("bulk_heavy_%d" % seed, seed, ops, 200 * NS,
                          client=dict(loss=0.02, burst=30 * MS, bps=50_000_000, delay=40 * MS, q=256 << 10)))
for seed in (21, 22, 23):
    ops = [conn(0, "tcp"), wr(NS, 1, 200), wr(NS + 5 * MS, 1, 5000), cl(5 * NS, 1, node=0), wr(6 * NS, 1, 10)]
    scenarios.append(base("close_%d" % seed, seed, ops, 20 * NS))
    ops = [conn(0, "ws"), wr(2 * NS, 1, 700, node=1), cl(3 * NS, 1, node=1), wr(4 * NS, 1, 10)]
    scenarios.append(base("close_server_%d" % seed, seed, ops, 20 * NS, rd=15 * MS))
ops = [conn(0, "tcp"), conn(NS, "tcp", port=80)]
scenarios.append(base("outage_fail", 31, ops, 400 * NS, server=dict(), cuts=[(5 * MS, 1000 * NS, [0], [1], "both")]))
ops = [conn(0, "tcp"), wr(NS, 1, 100)]
scenarios.append(base("outage_after_open", 32, ops, 600 * NS, cuts=[(500 * MS, 1000 * NS, [0], [1], "both")]))
ops = [conn(0, "tcp"), wr(NS, 1, 3000), wr(3 * NS, 1, 50000), wr(10 * NS, 1, 3000), wr(11 * NS, 1, 50, node=1)]
scenarios.append(base("oneway_cut", 33, ops, 400 * NS, cuts=[(2 * NS, 40 * NS, [1], [0], "oneway")]))
ops = [conn(0, "tcp"), wr(NS, 1, 3000), wr(3 * NS, 1, 50000, node=1)]
scenarios.append(base("heal", 34, ops, 120 * NS, cuts=[(2 * NS, 20 * NS, [0], [1], "both")]))
# NAT: mappings, the idle black hole and its failure timeline
for mapping, filtering, seed in (("eim", "apdf", 41), ("edm", "apdf", 42), ("eim", "eif", 43), ("eim", "adf", 44)):
    nat = dict(ext=NAT_EXT, mapping=mapping, filtering=filtering, timeout=30 * NS, tcp_timeout=60 * NS)
    ops = [conn(0, "tcp"), conn(0, "ws"), wr(NS, 1, 500), wr(NS, 2, 500, node=1), wr(2 * NS, 2, 40),
           wr(100 * NS, 1, 700, node=1), wr(150 * NS, 1, 90), wr(500 * NS, 2, 100)]
    scenarios.append(base("nat_%s_%s" % (mapping, filtering), seed, ops, 900 * NS, client=dict(nat=nat, bps=10_000_000)))
nat = dict(ext=NAT_EXT, mapping="eim", filtering="apdf", timeout=30 * NS, tcp_timeout=60 * NS)
ops = [conn(0, "tcp"), wr(NS, 1, 500), wr(50 * NS, 1, 100), wr(70 * NS, 1, 100, node=1), wr(140 * NS, 1, 100)]
scenarios.append(base("nat_refresh", 45, ops, 900 * NS, client=dict(nat=nat)))
# middleboxes
box = lambda **k: dict(dict(udp_block=True, ports=[443, 8443], tls_only=False, reject=False, portal=0), **k)
for name, b, seed in (("box_drop", box(), 51), ("box_reject", box(reject=True), 52), ("box_tls", box(tls_only=True), 53),
                      ("box_tls_reject", box(tls_only=True, reject=True), 54),
                      ("box_portal", box(portal=20 * NS), 55)):
    ops = [conn(0, "tcp"), conn(0, "ws"), conn(NS, "tcp", port=80), conn(5 * NS, "tcp"), conn(25 * NS, "tcp"),
           conn(25 * NS, "ws"), wr(30 * NS, 3, 100), wr(30 * NS, 4, 100)]
    scenarios.append(base(name, seed, ops, 400 * NS, client=dict(box=b)))
ops = [conn(0, "tcp", node=1, port=443), conn(3 * NS, "tcp")]
scenarios.append(base("box_inbound", 56, [dict(t=0, node=1, kind="connect", carrier="tcp", dst=("tcp4", CLIENT_HOST, 443)),
                                          conn(3 * NS, "tcp")], 200 * NS, client=dict(box=box(), client_port=0)))
# the lost third ACK: the client's uplink is down for the third handshake packet only
scenarios.append(base("third_ack", 57, [conn(0, "tcp"), conn(0, "ws"), wr(NS, 1, 100), wr(NS, 2, 100),
                                        wr(2 * NS, 1, 100, node=1)], 60 * NS,
                      cuts=[(10 * MS, 22 * MS, [0], [1], "both")]))
# simultaneous open between two public hosts
sim_ops = [dict(t=0, node=0, kind="connect", carrier="tcp", simul=True, dst=("tcp4", SERVER_HOST, 7000)),
           dict(t=0, node=1, kind="connect", carrier="tcp", simul=True, dst=("tcp4", CLIENT_HOST, 7000)),
           wr(2 * NS, 1, 100), wr(2 * NS, 1, 100, node=1)]
scenarios.append(base("simultaneous", 58, sim_ops, 20 * NS, client=dict(client_port=7000, host=CLIENT_HOST),
                      server=dict(client_port=7000)))

# hole punching: both hosts are behind NATs and open toward each other's external address at once; the first
# external port of each NAT is found by replaying its allocation with a fresh NAT of the same seed
for filtering, seed in (("apdf", 61), ("adf", 62), ("eif", 63)):
    nats = []
    ports = []
    for sid, host, ext in ((0, CLIENT_HOST, NAT_EXT), (1, CLIENT_HOST + 5, NAT_EXT + 1)):
        nats.append(dict(ext=ext, mapping="eim", filtering=filtering, timeout=30 * NS, tcp_timeout=60 * NS))
        probe = netmod.Nat(sid, ext, "eim", filtering, 30 * NS, netmod._seed(seed, "nat", sid), False, 60 * NS)
        ports.append(probe.outbound(0, "tcp", (host, 7000), (0, 0))[1])
    ops = [dict(t=0, node=0, kind="connect", carrier="tcp", simul=True, dst=("tcp4", NAT_EXT + 1, ports[1])),
           dict(t=3 * MS, node=1, kind="connect", carrier="tcp", simul=True, dst=("tcp4", NAT_EXT, ports[0])),
           wr(2 * NS, 1, 100), wr(2 * NS, 1, 100, node=1)]
    sc = base("punch_%s" % filtering, seed, ops, 100 * NS,
              client=dict(nat=nats[0], client_port=7000),
              server=dict(nat=nats[1], client_port=7000, host=CLIENT_HOST + 5))
    scenarios.append(sc)

for sc in scenarios:
    sim, log = run(sc)
    describe(sc)
    for entry in log:
        emit(*entry)
    for rt in sim.nodes:
        emit("wire", rt.idx, sim.rec.node_tx_bytes.get(rt.idx, 0))
    emit("carriers", sim.rec.carriers)
    emit("end", sc["name"])

open(sys.argv[2], "w").write("\n".join(out) + "\n")
