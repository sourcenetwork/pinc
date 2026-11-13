#!/usr/bin/env python3
"""Coverage of the Rust items docs/PROOFS.md names as modelled, from an lcov file (see scripts/trace-cov.sh).

Reads the "Rust item" column of the tables of docs/PROOFS.md, resolves each `Type::function` (or bare `function`) to
the `fn` definitions under crates/*/src whose file or `impl` block mentions the type, and prints, per file, the line
coverage of the whole file and of the modelled functions, with the uncovered lines (and uncovered branches, when the
lcov file has branch data, i.e. it came from a nightly `--branch` run) as file:line.
"""
import re, sys, glob, collections

lcov_path = sys.argv[1] if len(sys.argv) > 1 else "target/cov.lcov"

# lcov: per file, line -> hits, and (line, block, branch) -> taken
lines, branches, fnhit = collections.defaultdict(dict), collections.defaultdict(dict), {}
cur = None
for raw in open(lcov_path):
    raw = raw.strip()
    if raw.startswith("SF:"):
        cur = raw[3:]
    elif raw.startswith("DA:"):
        n, h = raw[3:].split(",")[:2]
        lines[cur][int(n)] = max(lines[cur].get(int(n), 0), int(h))
    elif raw.startswith("BRDA:"):
        n, blk, br, taken = raw[5:].split(",")
        key = (int(n), blk, br)
        t = 0 if taken == "-" else int(taken)
        branches[cur][key] = max(branches[cur].get(key, 0), t)

def rel(p):
    i = p.find("crates/")
    return p[i:] if i >= 0 else p

lines = {rel(k): v for k, v in lines.items()}
branches = {rel(k): v for k, v in branches.items()}

# the Rust-item cells of the proof tables
tokens = set()
for row in open("docs/PROOFS.md"):
    cells = row.split("|")
    if len(cells) < 8 or not row.startswith("| "):
        continue
    for t in re.findall(r"`([^`]+)`", cells[2]):
        t = re.sub(r"\(.*", "", t).strip()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*", t):
            tokens.add(t)

src = {}
for p in glob.glob("crates/*/src/**/*.rs", recursive=True):
    if p.startswith("crates/vinc-sim/"):
        continue
    src[p] = open(p).read().split("\n")

def extent(text, start):
    """Lines (1-based, inclusive) of the function whose `fn` is on line index start."""
    depth, seen, i = 0, False, start
    while i < len(text):
        code = re.sub(r'//.*|"(\\.|[^"\\])*"|\'.\'', "", text[i])
        for ch in code:
            if ch == "{":
                depth += 1
                seen = True
            elif ch == "}":
                depth -= 1
        if seen and depth <= 0:
            return start + 1, i + 1
        if not seen and code.rstrip().endswith(";"):
            return start + 1, start + 1
        i += 1
    return start + 1, len(text)

funcs = {}  # (file, name) -> (lo, hi)
for tok in sorted(tokens):
    parts = tok.split("::")
    name, owner = parts[-1], (parts[-2] if len(parts) > 1 else None)
    found = []
    for p, text in src.items():
        stem = p.rsplit("/", 1)[-1][:-3]
        body = "\n".join(text)
        if owner and not (stem == owner.lower() or stem == owner or re.search(r"\b(struct|enum|trait|mod|impl)\b[^\n{]*\b%s\b" % re.escape(owner), body)):
            continue
        for i, l in enumerate(text):
            if re.search(r"\bfn\s+%s\b" % re.escape(name), l):
                found.append((p, i))
    if not owner and len(found) > 3:
        continue  # a bare common name: too ambiguous to attribute
    for p, i in found:
        funcs[(p, name + "@" + str(i + 1))] = extent(src[p], i)

by_file = collections.defaultdict(list)
for (p, n), (lo, hi) in funcs.items():
    by_file[p].append((lo, hi, n.split("@")[0]))

def pct(a, b):
    return "n/a" if b == 0 else "%.1f%%" % (100.0 * a / b)

for p in sorted(by_file):
    ln = lines.get(p, {})
    tot = len(ln)
    hit = sum(1 for h in ln.values() if h > 0)
    print("%s: file lines %s (%d/%d)" % (p, pct(hit, tot), hit, tot))
    mod_total = mod_hit = 0
    unc, ubr = [], []
    for lo, hi, n in sorted(by_file[p]):
        fl = {k: v for k, v in ln.items() if lo <= k <= hi}
        mod_total += len(fl)
        mod_hit += sum(1 for v in fl.values() if v > 0)
        miss = sorted(k for k, v in fl.items() if v == 0)
        if miss:
            unc.append("%s: %s" % (n, ", ".join("%s:%d" % (p, k) for k in miss)))
        for (k, blk, br), t in sorted(branches.get(p, {}).items()):
            if lo <= k <= hi and t == 0:
                ubr.append("%s:%d (block %s branch %s)" % (p, k, blk, br))
    print("  modelled functions: %s (%d/%d lines)" % (pct(mod_hit, mod_total), mod_hit, mod_total))
    for u in unc:
        print("  uncovered lines in " + u)
    if branches:
        print("  uncovered branches: " + ("; ".join(ubr) if ubr else "none"))
