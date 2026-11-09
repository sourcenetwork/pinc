#!/usr/bin/env python3
"""Generates tests/data/reference_rng.txt: test vectors of CPython's `random` module and of the seed derivation.

Run isolated, from a directory outside the source tree: `python3 -I /path/to/scripts/gen_reference_rng.py OUT`.
Every line is `kind field...`, fields separated by single spaces; strings are hex-encoded, floats are the hex of
their IEEE bits, big values are decimal. The Rust test (`tests/sim_reference_rng.rs`) recomputes every line.
"""
import hashlib
import math
import random
import struct
import sys

out = []


def emit(*fields):
    out.append(" ".join(str(f) for f in fields))


def fbits(x):
    return struct.pack("<d", x).hex()


def digest(values):
    h = hashlib.blake2b(digest_size=16)
    for v in values:
        h.update(struct.pack("<d", v) if isinstance(v, float) else struct.pack("<Q", v))
    return h.hexdigest()


def seed_of(*parts):
    return int.from_bytes(hashlib.blake2b(repr(parts).encode(), digest_size=8).digest(), "little")


def spec_of(parts):
    toks = []
    for p in parts:
        if isinstance(p, bool):
            toks.append("b:%d" % p)
        elif isinstance(p, int):
            toks.append("i:%d" % p)
        elif isinstance(p, float):
            toks.append("f:" + fbits(p))
        elif isinstance(p, str):
            toks.append("s:" + p.encode().hex())
        elif isinstance(p, bytes):
            toks.append("y:" + p.hex())
        elif p is None:
            toks.append("n:")
        else:
            raise TypeError(p)
    return toks


emit("python", sys.version.split()[0])

SEEDS = [0, 1, 2, 42, 90211, 2**31, 2**32 - 1, 2**32, 2**32 + 1, 2**53 + 7, 2**63 + 12345, 2**64 - 1,
         2**64, 2**100 + 3, seed_of(90211, "node", 3), seed_of(7, "ge-up", 0), 90211 * 7919 + 17]

# --- seed derivation and repr -------------------------------------------------------------------
DERIVE = [
    (90211, "ge-up", 3), (0, "nat", 0), (1, "ge-down", 1), (2**63 + 5, "node", 250), (2**64 - 1, "adversary"),
    (7,), (), (5, "a'b"), (5, 'a"b'), (5, "a'b\"c"), (5, "tab\there\nline\\slash"), (5, "café"), (5, "\x01\x7f"),
    (5, " "), (5, "​"), (5, "中文"), (5, "\U0001f600"),
    (5, b"/col/0", 12, 3), (5, b"/col/1", 0, 2), (5, b"a'b\"c\x00\xff"), (-3, 0), (10**30, 1),
    (True, None, False), (1.0,), (0.1,), (1.5, 2.25), (-0.0,), (1e16,), (1e15,), (123456789012345678.0,),
    (1e-4,), (1e-5,), (0.0001234,), (1e22,), (5e-324,), (1.7976931348623157e308,), (0.3,), (100.0,), (2.5e-7,),
    (float("inf"),), (float("-inf"),), (float("nan"),), (12345.678,), (1e300,), (9007199254740993.0,),
]
for parts in DERIVE:
    r = repr(parts)
    emit("derive", seed_of(*parts), r.encode().hex(), *spec_of(parts))

# the 32-byte item digest of the set-reconciliation workload
for parts in [(90211, b"/col/0", 12, 3), (1, b"/col/1", 4000, 2)]:
    emit("digest32", hashlib.blake2b(repr(parts).encode(), digest_size=32).hexdigest(), *spec_of(parts))

# --- the generator -------------------------------------------------------------------------------
for si, s in enumerate(SEEDS):
    heavy = si % 3 == 0 or s in (0, 42, 90211)
    r = random.Random(s)
    vals = [r.random() for _ in range(10000)]
    emit("random", s, 10000, digest(vals), ",".join(fbits(v) for v in vals[:8]))

    if not heavy:
        continue
    r = random.Random(s)
    for k in (1, 7, 8, 31, 32, 33, 53, 64, 100, 127, 128):
        emit("bits", s, k, ",".join(str(r.getrandbits(k)) for _ in range(12)))

    r = random.Random(s)
    for n in (1, 2, 3, 5, 7, 8, 9, 100, 255, 256, 257, 1000, 65535, 65536, 10**6, 2**31 - 1, 2**32, 2**32 + 1,
              2**40 + 3, 2**53, 2**62 + 1, 2**63 + 9, 2**64 - 1):
        emit("below", s, n, ",".join(str(r.randrange(n)) for _ in range(12)))

    r = random.Random(s)
    for a, b in ((0, 1), (1, 6), (-5, 5), (10, 10), (-100, 1000), (0, 2**33)):
        emit("randint", s, a, b, ",".join(str(r.randint(a, b)) for _ in range(12)))
    for a, b in ((0, 10), (5, 7), (-8, -2)):
        emit("range", s, a, b, ",".join(str(r.randrange(a, b)) for _ in range(12)))

    r = random.Random(s)
    for n in (1, 2, 3, 7, 100, 12345):
        seq = list(range(n))
        emit("choice", s, n, ",".join(str(r.choice(seq)) for _ in range(12)))

    r = random.Random(s)
    for n in (0, 1, 2, 3, 10, 100, 1000):
        x = list(range(n))
        r.shuffle(x)
        emit("shuffle", s, n, ",".join(map(str, x)) if n <= 100 else digest(x))

    r = random.Random(s)
    for n, k in ((10, 3), (10, 10), (30, 6), (100, 5), (100, 20), (1000, 20), (1000, 100), (50, 0), (21, 5),
                 (22, 5), (200, 6), (5000, 30), (200, 150), (70, 7)):
        emit("sample", s, n, k, ",".join(map(str, r.sample(range(n), k))))

    r = random.Random(s)
    for a, b in ((0.0, 1.0), (10.0, 35.0), (0.5, 4.0), (60, 200), (-3.5, 2.25)):
        v = [r.uniform(a, b) for _ in range(1000)]
        emit("uniform", s, fbits(float(a)), fbits(float(b)), 1000, digest(v), ",".join(fbits(x) for x in v[:4]))

    r = random.Random(s)
    for lam in (1.0, 1.0 / 30.0, 1.0 / 0.005, 2.0, 1e-9, 1.0 / 3000.0):
        v = [r.expovariate(lam) for _ in range(10000)]
        emit("expo", s, fbits(lam), 10000, digest(v), ",".join(fbits(x) for x in v[:4]))

    r = random.Random(s)
    emit("bytes8", s, bytes(r.getrandbits(8) for _ in range(100)).hex())
    r = random.Random(s)
    for n in (1, 3, 4, 5, 8, 17, 32):
        emit("bytesn", s, n, r.getrandbits(8 * n).to_bytes(n, "little").hex())

    r = random.Random(s)
    acc = []
    for i in range(5000):
        op = i % 8
        if op == 0:
            acc.append(r.random())
        elif op == 1:
            acc.append(r.getrandbits(8))
        elif op == 2:
            acc.append(r.randrange(1000))
        elif op == 3:
            acc.append(r.randrange(3))
        elif op == 4:
            acc.append(r.expovariate(0.5))
        elif op == 5:
            acc.append(r.uniform(10, 20))
        elif op == 6:
            acc.append(r.randint(5, 50))
        else:
            acc.append(r.choice(range(97)))
    emit("mixed", s, digest(acc))

# --- the logarithm --------------------------------------------------------------------------------
r = random.Random(2024)
emit("log", "unit", 200000, digest([math.log(1.0 - r.random()) for _ in range(200000)]))
for k in range(-300, 301, 25):
    scale = float("1e%d" % k)
    r = random.Random(k + 1000)
    emit("log", "scaled", k, 20000, digest([math.log(r.random() * scale + 5e-324) for _ in range(20000)]))
r = random.Random(77)
emit("log", "near1", 100000, digest([math.log(1.0 + (r.random() - 0.5) * 1e-6) for _ in range(100000)]))

open(sys.argv[1], "w").write("\n".join(out) + "\n")
