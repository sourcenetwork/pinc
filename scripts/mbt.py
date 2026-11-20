#!/usr/bin/env python3
"""Model-based test cases from a TLC state graph.

Usage: scripts/mbt.py <graph.dot> <config.cfg> <tlc.log> <cases.ndjson>

<graph.dot> is the state graph TLC writes with `-dump dot,actionlabels,constrained <file>`. TLC (from the 2026 jar
on; the older one labels an edge with the action's name only) labels an edge with the action that took it and the
values of the bounded `\\E` variables of the next-state relation that the action was split on,
`CallTake(1,2,<<0,2,3>>)`, and a node with the state, its variables as TLA+ values. A spec written for this
(proofs/tla/MbtOrphan.tla is the first) makes one action per call of the code, with the call's arguments and its
result as parameters, so the graph has one node per state of the code and one edge per call from it, labelled with
what the call returns. <tlc.log> is the output of that TLC run: the graph must have every successor TLC generated
(states generated = initial states + edges) and every distinct state it found (distinct states = states inside the
constraint), so a graph cut short fails here.

The script reads every node and edge, computes paths from the initial state that take every edge at least once (it
visits every state on the way), and writes them as test cases:
  line 1:   {"constants": {...}, "init": {...}, "states": n, "leaves": l, "edges": m, "cases": c, "steps": s}
  then one line per case: {"case": i, "steps": [{"call": "CallHold", "args": [...], "state": {...}}, ...]}
`constants` are the CONSTANTS of <config.cfg> given a value (not one substituted with `<-`), `init` the initial state
and `state` the state after the call, every TLA+ value as JSON: an integer, a boolean, a string, a sequence or a set as
an array, a record as an object. A leaf is a state past the config's CONSTRAINT: the graph has the edges into it, none
out of it.

The cover: states are taken in breadth-first order from the initial state; while one has an edge not taken yet, a
case goes to it along the breadth-first tree and then follows edges not taken yet (a call that leaves the state as it
is first, then one into a state with edges still to take, then any) until it reaches a state with none left.
"""

import json
import re
import sys
from collections import deque


class Tla:
    """A reader of the TLA+ values TLC prints."""

    def __init__(self, s):
        self.s, self.i = s, 0

    def ws(self):
        while self.i < len(self.s) and self.s[self.i] in " \t\r\n":
            self.i += 1

    def eat(self, tok):
        self.ws()
        if self.s.startswith(tok, self.i):
            self.i += len(tok)
            return True
        return False

    def items(self, close):
        out = []
        if self.eat(close):
            return out
        while True:
            out.append(self.value())
            if self.eat(close):
                return out
            if not self.eat(","):
                raise ValueError(f"expected , or {close} at {self.i} in {self.s!r}")

    def value(self):
        self.ws()
        s, i = self.s, self.i
        if s.startswith("<<", i):
            self.i += 2
            return self.items(">>")
        if s.startswith("{", i):
            self.i += 1
            return self.items("}")
        if s.startswith("[", i):
            self.i += 1
            rec = {}
            if self.eat("]"):
                return rec
            while True:
                self.ws()
                m = re.compile(r"[A-Za-z_][A-Za-z0-9_]*").match(s, self.i)
                if not m or not self.eat_after(m.end(), "|->"):
                    raise ValueError(f"expected a record field at {self.i} in {s!r}")
                rec[m.group(0)] = self.value()
                if self.eat("]"):
                    return rec
                if not self.eat(","):
                    raise ValueError(f"expected , or ] at {self.i} in {s!r}")
        if s.startswith('"', i):
            m = re.compile(r'"((?:[^"\\]|\\.)*)"').match(s, i)
            self.i = m.end()
            return re.sub(r"\\(.)", lambda c: {"n": "\n", "t": "\t"}.get(c.group(1), c.group(1)), m.group(1))
        for word, val in (("TRUE", True), ("FALSE", False)):
            if s.startswith(word, i):
                self.i += len(word)
                return val
        m = re.compile(r"-?\d+").match(s, i)
        if m:
            self.i = m.end()
            return int(m.group(0))
        raise ValueError(f"cannot read a TLA+ value at {i} in {s!r}")

    def eat_after(self, pos, tok):
        self.i = pos
        return self.eat(tok)

    def done(self):
        self.ws()
        return self.i == len(self.s)


def tla(s):
    p = Tla(s)
    v = p.value()
    if not p.done():
        raise ValueError(f"trailing text in {s!r}")
    return v


def state(label):
    """The variables of a node label: `x = v` for one variable, `/\\ x = v` lines for several."""
    parts = [p for p in re.split(r"(?:^|\n)/\\ ", label) if p.strip()]
    out = {}
    for p in parts:
        name, _, val = p.partition(" = ")
        out[name.strip()] = tla(val)
    return out


def call(label):
    """The action of an edge label and its arguments: `Name(a,b)` or `Name`."""
    name, paren, rest = label.partition("(")
    if not paren:
        return name, []
    p = Tla(rest)
    args = p.items(")")
    if not p.done():
        raise ValueError(f"trailing text in {label!r}")
    return name, args


# A quoted label may span lines: TLC adds the action's source location to the label of an edge into a state past
# the constraint, after a raw newline.
QUOTED = r'"((?:[^"\\]|\\.)*)"'
NODE = re.compile(r"^(-?\d+) \[label=" + QUOTED + r"([^\n]*)", re.M)
EDGE = re.compile(r"^(-?\d+) -> (-?\d+) \[label=" + QUOTED, re.M)


def unescape(s):
    return re.sub(r"\\(.)", lambda c: "\n" if c.group(1) == "n" else c.group(1), s)


def read_graph(path):
    nodes, inits, leaves, edges = {}, [], set(), set()
    with open(path, encoding="utf-8") as f:
        text = f.read()
    for m in EDGE.finditer(text):
        edges.add((m.group(1), m.group(3).split("\n")[0], m.group(2)))
    for m in NODE.finditer(text):
        fp, attrs = m.group(1), m.group(3)
        if fp not in nodes:
            nodes[fp] = state(unescape(m.group(2)))
        if "fillcolor" in attrs:
            leaves.add(fp)
        elif "style = filled" in attrs:
            inits.append(fp)
    missing = {e[0] for e in edges} | {e[2] for e in edges}
    missing -= nodes.keys()
    if missing or not inits:
        raise SystemExit(f"mbt: {path}: {len(missing)} states without a label, {len(inits)} initial states")
    return nodes, inits, leaves, sorted(edges)


KEYWORDS = (r"(?:SPECIFICATION|INIT|NEXT|INVARIANTS?|PROPERTY|PROPERTIES|CONSTRAINTS?|ACTION_CONSTRAINTS?|VIEW|"
            r"SYMMETRY|ALIAS|POSTCONDITION|CHECK_DEADLOCK)")


def constants(path):
    """The `name = value` assignments of the CONSTANTS section of a TLC config, values as TLA+. A substitution
    `name <- Op` is left out: its value is an operator of the module (a config file cannot spell a tuple)."""
    with open(path, encoding="utf-8") as f:
        text = re.sub(r"\\\*[^\n]*", "", f.read())
    out = {}
    ident = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
    for body in re.findall(r"\bCONSTANTS?\b(.*?)(?=\b" + KEYWORDS + r"\b|\Z)", text, re.S):
        p = Tla(body)
        while not p.done():
            m = ident.match(p.s, p.i)
            if m and p.eat_after(m.end(), "<-"):
                p.ws()
                op = ident.match(p.s, p.i)
                if not op:
                    raise SystemExit(f"mbt: {path}: cannot read the operator substituted for {m.group(0)}")
                p.i = op.end()
                continue
            if not m or not p.eat_after(m.end(), "="):
                raise SystemExit(f"mbt: {path}: cannot read the constant at {p.s[p.i:p.i + 20]!r}")
            out[m.group(0)] = p.value()
    return out


def cover(init, edges):
    """Paths from the initial state that take every edge, as lists of edge indices."""
    out = {}
    for k, (u, _, _) in enumerate(edges):
        out.setdefault(u, []).append(k)
    # the breadth-first tree: the edge that first reaches each state
    parent, order, q = {init: None}, [init], deque([init])
    while q:
        u = q.popleft()
        for k in out.get(u, []):
            v = edges[k][2]
            if v not in parent:
                parent[v] = k
                order.append(v)
                q.append(v)
    todo = {u: list(ks) for u, ks in out.items()}
    taken = [False] * len(edges)

    def left(u):
        ks = todo.get(u, [])
        while ks and taken[ks[-1]]:
            ks.pop()
        return ks

    def pick(u):
        ks = [k for k in left(u) if not taken[k]]
        if not ks:
            return None
        loops = [k for k in ks if edges[k][2] == u]
        if loops:
            return loops[0]
        onward = [k for k in ks if left(edges[k][2])]
        return (onward or ks)[0]

    cases = []
    for u in order:
        while left(u):
            path, v = [], u
            while parent[v] is not None:
                path.append(parent[v])
                v = edges[parent[v]][0]
            path.reverse()
            for k in path:
                taken[k] = True
            cur = u
            while (k := pick(cur)) is not None:
                taken[k] = True
                path.append(k)
                cur = edges[k][2]
            cases.append(path)
    if not all(taken):
        raise SystemExit("mbt: an edge no case takes: a state the initial state does not reach")
    return cases


def tlc_counts(path):
    """States generated and distinct states found, from the last summary line of a TLC run."""
    with open(path, encoding="utf-8", errors="replace") as f:
        found = re.findall(r"([\d,]+) states generated, ([\d,]+) distinct states found, 0 states left on queue",
                           f.read())
    if not found:
        raise SystemExit(f"mbt: {path}: no finished TLC run")
    return tuple(int(x.replace(",", "")) for x in found[-1])


def main(argv):
    if len(argv) != 5:
        raise SystemExit(__doc__)
    nodes, inits, leaves, edges = read_graph(argv[1])
    consts = constants(argv[2])
    generated, distinct = tlc_counts(argv[3])
    if (generated, distinct) != (len(inits) + len(edges), len(nodes) - len(leaves)):
        raise SystemExit(f"mbt: {argv[1]} has {len(edges)} edges and {len(nodes) - len(leaves)} states inside the "
                         f"bound; TLC generated {generated} states and found {distinct}")
    if len(inits) != 1:
        raise SystemExit(f"mbt: {len(inits)} initial states; the cases assume one")
    labelled = [(u, call(lab), v) for u, lab, v in edges]
    cases = cover(inits[0], edges)
    steps = sum(len(p) for p in cases)
    with open(argv[4], "w", encoding="utf-8") as f:
        head = {"constants": consts, "init": nodes[inits[0]], "states": len(nodes), "leaves": len(leaves),
                "edges": len(edges), "cases": len(cases), "steps": steps}
        f.write(json.dumps(head, separators=(",", ":")) + "\n")
        for i, path in enumerate(cases):
            st = []
            for k in path:
                _, (name, args), v = labelled[k]
                st.append({"call": name, "args": args, "state": nodes[v]})
            f.write(json.dumps({"case": i, "steps": st}, separators=(",", ":")) + "\n")
    print(f"mbt: {len(nodes)} states ({len(leaves)} past the bound), {len(edges)} edges, "
          f"{len(cases)} cases, {steps} steps")


if __name__ == "__main__":
    main(sys.argv)
