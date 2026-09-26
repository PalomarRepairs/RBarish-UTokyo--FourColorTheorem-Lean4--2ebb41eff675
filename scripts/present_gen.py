#!/usr/bin/env python3
"""Generate the presentation data `FourColor/Present/P5/` ... `FourColor/Present/P11/`.

Coq proves `exclude5` ... `exclude11` (`presentN.v`, the lemmas `excluded_arity N`) with
scripts in the tactic language of `present.v`. The Lean port checks them as data: a case tree
`PTree`, checked by the kernel with `checkTree` (`FourColor.Present.Tree`), split into chunk
declarations of bounded kernel cost. For each presentation N this generator

1. parses `presentN.v` into a case tree (the labels of `Pcase [L]` are resolved lexically into
   de Bruijn indices);
2. walks the tree natively (`scripts/present_gen_native.lean`, run with `lake env lean --run`
   through `scripts/lean.sh`) with the faithful functions of the library: the goal
   `Check p in p0` of every node, the pruning masks of the Reducible and Hubcap leaves
   (`FourColor.PruneGen`), a deterministic cost for every check, and, for the heavy Hubcap
   constraints, the literal data of their recursive checks (see below);
3. splits the tree into chunks (below) and writes the Lean files of `FourColor/Present/P<N>/`:
   chunk files `C<kk>.lean` and the final file `Exclude.lean`, which proves
   `FourColor.excludeN : ExcludedArity N`, and `Rules.lean` (the rules of the drule fork, as
   named parts) when some split needs them.

The output is deterministic (the costs are allocation and comparison counts, not times), so
running the generator twice gives identical files. Nobody edits the generated files by hand:
re-splitting goes through the options below.

## Costs

The cost of a check has two deterministic parts, counted by the native walk: `hb`, the number
of heartbeats (small allocations of the Lean runtime) of its evaluation with the faithful
functions and the pruned quiz tree, and `cmp`, the number of comparison steps of the hubcap
checks (`cmpPart` in `sortDrules` and the subset tests of `checkUnfit`, which allocate
nothing). The estimated kernel time is `HB_MS * hb + CMP_MS * cmp` plus a constant per node or
declaration (`C_*` below). The constants were fitted on kernel times measured with Lean
v4.35.0-rc2: the fast checks' benchmark of 62 single Hubcap leaves (within 15%
up to 3 s per declaration) and the builds of present6 and present11. Kernel time is superlinear
in the size of a declaration (present11 in declarations of at most 0.25, 0.4, 1.5 and 5 s:
16.6, 18.1, 19.7 and 24.7 s of kernel time, and 0.1, 0.1, 0.3 and 1.2 GB of memory), hence
the small default budget.

## Chunks

A chunk is a subtree whose descendants that are chunks of their own are `ext` leaves; it is
proved by one theorem `c<k> : PGoal.OK <goal>` (`PGoal.ok_of_checkTree`, one `decide +kernel`),
given the theorems of its `ext` children. Chunks are made bottom-up: a `Pcase` node whose
subtree costs more than the budget cuts its costliest children into chunks of their own until
it fits (children first); so every chunk costs at most the budget, except single leaves.

A Hubcap leaf that costs more than the budget is a chunk proved by `PGoal.ok_of_hubcap` from
its constraints (`hubcapFitFast_cons1_of`, `hubcapFitFast_cons2_of`), each checked by its own
`decide +kernel`, except a final run of cheap constraints, checked together. A constraint that
costs more than the budget is split target rule by target rule: it is entered with
`check2Dbound2Fast_of_rec_lit` (`checkDbound2Fast_of_rec_lit`) with its literal data (the
rules are the definitions `rule<i>` of `Rules.lean`), and the work for one target rule at a
time (a "head", `check2Dbound2HeadFast`) is checked by its own `decide +kernel`
(`check2Dbound2RecFast_cons_of`, `checkDbound2RecFast_cons_of`; the swap of the two parts of a
dual check is `check2Dbound2RecFast_succ_nil_cons`), until the rest of the check fits in the
budget and is checked at once. All the pieces of a leaf use the leaf's mask. Each
`decide +kernel` is its own declaration in the kernel (an auxiliary lemma).

The chunks are numbered in post-order (children first) and grouped into files in that order,
at most `--file-budget` of estimated kernel time per file; a file imports the files of the
children of its chunks, so the files of disjoint subtrees build in parallel.

## Usage

    scripts/present_gen.py [N ...] [options]

N: the presentations to generate (default: 5 to 11). Options:

* `--budget MS`: the estimated kernel time per declaration (default 400). A head of a
  constraint (the work for one target rule) is not split further, so a few declarations exceed
  it (up to about 1.1 s in present8); the generator lists them.
* `--override N:IDX:MS`: the budget for the subtree of node IDX of presentation N (preorder
  index, as in the chunk docstrings); repeatable. This is how a chunk that is too slow or too
  big in a checker is re-split: give its root node a smaller budget.
* `--file-budget MS`: the estimated kernel time per file (default 60000).
* `--out DIR`: the directory of the `P<N>` directories (default `FourColor/Present`).
* `--cache DIR`: the cache of the native walks (default `.lake/present_gen`); `--refresh`
  recomputes them.
* `--dry-run`: print the plan without writing files. `--summary FILE`: write the estimated
  cost of every declaration (JSON).

Build the files of a presentation in the order of their imports (`C00`, `C01`, ...,
`Exclude`), for instance with `lake build FourColor.Present.P7.Exclude`.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

sys.setrecursionlimit(100000)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NATIVE = os.path.join('scripts', 'present_gen_native.lean')
COQ = os.path.join('.deps', 'fourcolor', 'theories', 'proof')

# --- the cost model (estimated kernel milliseconds) ---
HB_MS = 0.028        # per heartbeat of a check
CMP_MS = 0.0093      # per comparison step of a hubcap check
C_PCASE = 0.3        # a Pcase node (goodSplit, splitPart)
C_SIMILAR = 0.3      # a Similar leaf
C_RED = 1.5          # a Reducible leaf, besides its units (pruning, the search's setup)
C_HUB = 3.0          # a Hubcap leaf, besides its units (size, cover)
C_EXT = 0.2          # an ext leaf (goal comparison)
C_DECL = 2.0         # a declaration (its statement, the pruned quiz tree)
# the native walk records the chains of the constraints above this many units
EXPAND_UNITS = 25000

LOCS = {'s': '.spoke', 'h': '.hat', 'f1': '.fan1', 'f2': '.fan2', 'f3': '.fan3'}

HEADER = '''/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
'''
MARK = 'Generated by `scripts/present_gen.py`'


# ---------------------------------------------------------------------------------------------
# Parsing the Coq scripts
# ---------------------------------------------------------------------------------------------

def strip_comments(src):
    """Remove the (nested) Coq comments."""
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith('(*', i):
            depth += 1
            i += 2
        elif src.startswith('*)', i) and depth > 0:
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(src[i])
            i += 1
    return ''.join(out)


def tactics(src):
    """The hub size and the tactic sentences of the proof of `excludeN`."""
    src = strip_comments(src)
    m = re.search(r'Lemma\s+exclude(\d+)\s*:\s*excluded_arity\s+(\d+)\s*\.\s*Proof\.(.*)Qed\.',
                  src, re.S)
    if not m:
        raise ValueError('no presentation lemma')
    if m.group(1) != m.group(2):
        raise ValueError('lemma name and arity differ')
    body = m.group(3)
    # sentences end with '.' followed by white space or the end (hubcaps end with "$.")
    sents = [' '.join(s.split()) for s in re.split(r'\.(?=\s|$)', body) if s.strip()]
    return int(m.group(2)), sents


class Node:
    """A node of a case tree: kind 'P' (Pcase), 'R' (Reducible), 'H' (Hubcap), 'S' (Similar)."""

    def __init__(self, kind, args, t=None, e=None):
        self.kind, self.args, self.t, self.e = kind, args, t, e
        self.idx = None       # preorder index
        self.chunk = None     # chunk number if the node is a chunk root
        self.split = False    # a Hubcap leaf proved constraint by constraint
        self.budget = None


PC_RE = re.compile(r'^Pcase\s*(\w*)\s*:\s*(s|h|f1|f2|f3)\[(\d+)\]\s*(<=|>)\s*(\d+)$')
SIM_RE = re.compile(r'^Similar to\s*(\*?)\s*(\w+)\[(\d+)\]$')
HC_RE = re.compile(r'\$\[(\d+)(?:,(\d+))?\]<=(\(-\d+\)|-?\d+)')


def parse_hubcap(s):
    """The constraints `(j1, j2 or None, b)` of a `Hubcap` sentence (indices from 0)."""
    body = s[len('Hubcap'):].strip()
    if not body.endswith('$'):
        raise ValueError('bad hubcap ' + s)
    cons = []
    for m in HC_RE.finditer(body.replace(' ', '')):
        j1 = int(m.group(1))
        j2 = int(m.group(2)) if m.group(2) else None
        b = int(m.group(3).strip('()'))
        cons.append((j1 - 1, None if j2 is None else j2 - 1, b))
    if body.replace(' ', '').count('$[') != len(cons):
        raise ValueError('hubcap parse mismatch: ' + s)
    return cons


def parse_script(sents):
    """The case tree of a presentation script. Labels are resolved lexically: `L` is in scope in
    the second subtree of its `Pcase`; a later `Pcase` with the same name shadows it. Similar
    leaves get the de Bruijn index of their label (0: the most recent one in scope)."""
    if sents[0] != 'Presentation red':
        raise ValueError('expected Presentation, got ' + sents[0])
    pos = [1]

    def goal(ctx):
        s = sents[pos[0]]
        pos[0] += 1
        m = PC_RE.match(s)
        if m:
            lbl, loc, j, op, k = m.group(1), m.group(2), int(m.group(3)), m.group(4), int(m.group(5))
            t = goal(ctx)
            e = goal([lbl] + ctx if lbl else ctx)
            return Node('P', (loc, j - 1, k, op == '<=', bool(lbl), lbl), t, e)
        if s == 'Reducible':
            return Node('R', ())
        if s.startswith('Hubcap'):
            return Node('H', tuple(parse_hubcap(s)))
        m = SIM_RE.match(s)
        if m:
            mir, lbl, j = m.group(1) == '*', m.group(2), int(m.group(3))
            if lbl not in ctx:
                raise ValueError(f'label {lbl} not in scope at {s!r}: {ctx}')
            return Node('S', (ctx.index(lbl), j, mir, lbl))
        raise ValueError('unknown tactic ' + repr(s))

    root = goal([])
    if pos[0] != len(sents):
        raise ValueError(f'trailing tactics: {sents[pos[0]:pos[0] + 3]}')
    return root


def parse_presentation(path):
    """The case tree and hub size of `presentN.v`."""
    hub, sents = tactics(open(path).read())
    return parse_script(sents), hub


def preorder(root):
    stack = [root]
    while stack:
        x = stack.pop()
        yield x
        if x.kind == 'P':
            stack.append(x.e)
            stack.append(x.t)


def postorder(root):
    """The nodes in post-order (children before parents, first subtree first)."""
    out, stack = [], [(root, False)]
    while stack:
        x, done = stack.pop()
        if done or x.kind != 'P':
            out.append(x)
        else:
            stack.append((x, True))
            stack.append((x.e, False))
            stack.append((x.t, False))
    return out


def count_kinds(root):
    cnt = {'P': 0, 'R': 0, 'H': 0, 'S': 0}
    for nd in preorder(root):
        cnt[nd.kind] += 1
    return cnt


def tree_text(hub, root):
    """The case tree in the text format of `present_gen_native.lean` (one node per line, in
    preorder): `P loc j k lo named`, `R`, `H m (1 j b | 2 j1 j2 b)*`, `S lbl j mir`."""
    out = []
    for nd in preorder(root):
        if nd.kind == 'P':
            loc, j0, k, lo, named, _ = nd.args
            out.append(f'P {loc} {j0} {k} {int(lo)} {int(named)}')
        elif nd.kind == 'R':
            out.append('R')
        elif nd.kind == 'H':
            toks = [f'H {len(nd.args)}']
            for (a, b2, b) in nd.args:
                toks.append(f'1 {a} {b}' if b2 is None else f'2 {a} {b2} {b}')
            out.append(' '.join(toks))
        else:
            lbl, j, mir, _ = nd.args
            out.append(f'S {lbl} {j} {int(mir)}')
    return f'{hub}\n' + '\n'.join(out) + '\n'


# ---------------------------------------------------------------------------------------------
# The native walk
# ---------------------------------------------------------------------------------------------

def file_hash(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        h.update(f.read())
    return h.hexdigest()


def native_table(n, hub, root, args):
    """The rows of the native walk of presentation `n` (cached)."""
    text = tree_text(hub, root)
    key = hashlib.sha256()
    key.update(text.encode())
    key.update(file_hash(os.path.join(ROOT, NATIVE)).encode())
    key.update(str(EXPAND_UNITS).encode())
    # the data the walk depends on: the checks, the quiz tree, the forks
    for mod in ['Fast/PruneGen', 'Fast/Prune', 'Hubcap', 'QuizData/Tree', 'QuizData/Forks',
                'Present/Tree']:
        olean = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean', 'FourColor', mod + '.olean')
        key.update(file_hash(olean).encode() if os.path.exists(olean) else b'-')
    key = key.hexdigest()[:16]
    cache = os.path.join(ROOT, args.cache)
    os.makedirs(cache, exist_ok=True)
    out = os.path.join(cache, f'present{n}-{key}.jsonl')
    if args.refresh or not os.path.exists(out):
        tree = os.path.join(cache, f'present{n}.tree')
        with open(tree, 'w') as f:
            f.write(text)
        tmp = out + '.tmp'
        print(f'present{n}: native walk ...', file=sys.stderr)
        r = subprocess.run([os.path.join(ROOT, 'scripts', 'lean.sh'), '--run', NATIVE, tree, tmp,
                            str(EXPAND_UNITS), str(10 ** 15)], cwd=ROOT, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True)
        sys.stderr.write(r.stdout)
        if r.returncode != 0:
            raise SystemExit(f'present{n}: the native walk failed (rc={r.returncode})')
        os.replace(tmp, out)
        # drop the walks of older versions
        for fn in sorted(os.listdir(cache)):
            if fn.startswith(f'present{n}-') and fn.endswith('.jsonl') and \
                    os.path.join(cache, fn) != out:
                os.remove(os.path.join(cache, fn))
    return [json.loads(line) for line in open(out)]


class Pres:
    """A presentation: its tree, nodes, rules, and the plan of its chunks."""

    def __init__(self, n):
        self.n = n
        self.root = None
        self.nodes = []
        self.rules = []
        self.chunks = []
        self.files = []
        self.over = []    # (node, constraint, estimated ms) of the pieces over the budget


def load(n, args):
    P = Pres(n)
    root, hub = parse_presentation(os.path.join(ROOT, COQ, f'present{n}.v'))
    if hub != n:
        raise SystemExit(f'present{n}.v proves exclude{hub}')
    P.root = root
    P.nodes = list(preorder(root))
    for i, nd in enumerate(P.nodes):
        nd.idx = i
    rows = native_table(n, hub, root, args)
    hdr = rows[0]
    assert hdr['t'] == 'rules' and hdr['n'] == n
    P.rules = hdr['rules']
    node_rows = [r for r in rows[1:] if r['t'] == 'node']
    if len(node_rows) != len(P.nodes):
        raise SystemExit(f'present{n}: {len(node_rows)} native rows for {len(P.nodes)} nodes')
    for nd, r in zip(P.nodes, node_rows):
        if r['idx'] != nd.idx or r['kind'] != nd.kind:
            raise SystemExit(f'present{n}: native row {r["idx"]} does not match node {nd.idx}')
        if not r['ok']:
            raise SystemExit(f'present{n}: the check of node {nd.idx} ({nd.kind}) fails natively')
        nd.p0, nd.p = r['p0'], r['p']
        nd.hb, nd.cmp = r['hb'], r.get('cmp', 0)
        nd.mask = r.get('mask')
        nd.cons = [tuple(c) for c in r.get('cons', [])]
        nd.cons_data = {}
    for r in rows[1:]:
        if r['t'] == 'cons':
            P.nodes[r['idx']].cons_data[r['ci']] = r
    # contexts: the else-subtree of a named Pcase has the first subgoal's p0 in scope
    P.root.ctx = []
    for nd in P.nodes:
        if nd.kind == 'P':
            nd.t.ctx = nd.ctx
            nd.e.ctx = ([nd.t.p0] + nd.ctx) if nd.args[4] else nd.ctx
    # costs
    for nd in P.nodes:
        if nd.kind == 'P':
            nd.cost = C_PCASE
        elif nd.kind == 'S':
            nd.cost = C_SIMILAR
        elif nd.kind == 'R':
            nd.cost = C_RED + HB_MS * nd.hb
        else:
            nd.cost = C_HUB + units(nd.hb, nd.cmp)
    return P


# ---------------------------------------------------------------------------------------------
# Planning: chunks, split leaves, files
# ---------------------------------------------------------------------------------------------

def units(hb, cmp):
    """The estimated kernel time (ms) of a check of `hb` heartbeats and `cmp` comparison
    steps."""
    return HB_MS * hb + CMP_MS * cmp


def step_cost(st):
    return 0.0 if st['t'] == 'W' else units(st['hb'], st['cmp'])


def plan_chain(chain, budget):
    """The pieces of a recursive check: `('head', est)` for a head checked by its own
    declaration, `('swap',)`, and a final `('rest', est)` checked at once."""
    steps = chain['steps']
    suffix = [0.0] * (len(steps) + 1)
    for j in range(len(steps) - 1, -1, -1):
        suffix[j] = suffix[j + 1] + step_cost(steps[j])
    acts = []
    for j, st in enumerate(steps):
        if suffix[j] + C_DECL <= budget:
            acts.append(('rest', suffix[j] + C_DECL))
            return acts
        if st['t'] == 'W':
            acts.append(('swap',))
        else:
            acts.append(('head', step_cost(st) + C_DECL))
    acts.append(('rest', C_DECL))
    return acts


def plan_leaf(P, nd, budget):
    """The plan of a split Hubcap leaf: for each constraint, `('decide', est)` or
    `('chain', est_entry, acts)`; the constraints from `nd.tail` on are checked at once."""
    plans = []
    costs = [C_DECL + units(hb, cmp) for (hb, cmp) in nd.cons]
    for ci, c in enumerate(costs):
        data = nd.cons_data.get(ci)
        if c <= budget or data is None or not isinstance(data['data'], dict):
            if c > budget:
                P.over.append((nd.idx, ci, c))
            plans.append(('decide', c))
            continue
        chain = data['data']['chain']
        acts = plan_chain(chain, budget)
        heads = sum(step_cost(st) for st in chain['steps'])
        entry = max(C_DECL, c - heads)
        for a in acts:
            if a[0] != 'swap' and a[1] > budget:
                P.over.append((nd.idx, ci, a[1]))
        plans.append(('chain', entry, acts))
    # the longest cheap suffix is checked at once
    tail, acc = len(plans), 0.0
    while tail > 0 and plans[tail - 1][0] == 'decide' and acc + costs[tail - 1] <= budget:
        acc += costs[tail - 1]
        tail -= 1
    nd.tail = tail
    nd.tail_cost = acc
    nd.plans = plans


def assign_budgets(P, args):
    over = {}
    for o in args.override:
        m = re.match(r'^(\d+):(\d+):(\d+(?:\.\d+)?)$', o)
        if not m:
            raise SystemExit(f'bad --override {o!r} (N:IDX:MS)')
        if int(m.group(1)) == P.n:
            if int(m.group(2)) >= len(P.nodes):
                raise SystemExit(f'--override {o}: no node {m.group(2)} in present{P.n}')
            over[int(m.group(2))] = float(m.group(3))
    P.root.budget = over.get(0, args.budget)
    for nd in P.nodes:
        if nd.kind == 'P':
            for ch in (nd.t, nd.e):
                ch.budget = over.get(ch.idx, nd.budget)


def plan_chunks(P, args):
    """Mark the chunk roots (bottom-up packing) and the split Hubcap leaves."""
    assign_budgets(P, args)
    kept = {}   # node -> the cost that stays in its parent's chunk
    for nd in postorder(P.root):
        B = nd.budget
        if nd.kind == 'H' and nd.cost + C_DECL > B:
            nd.split = True
            nd.chunk = True
            plan_leaf(P, nd, B)
            kept[nd.idx] = C_EXT
            continue
        if nd.kind != 'P':
            kept[nd.idx] = nd.cost
            continue
        ct, ce = kept[nd.t.idx], kept[nd.e.idx]
        total = nd.cost + ct + ce
        # cut the costliest children first (the first subtree first on ties)
        for c, _, ch in sorted([(ct, 0, nd.t), (ce, 1, nd.e)], key=lambda x: (-x[0], x[1])):
            if total + C_DECL <= B:
                break
            if ch.chunk:
                continue
            ch.chunk = True
            total -= c - C_EXT
        kept[nd.idx] = total
    P.root.chunk = True
    # number the chunks in post-order
    P.chunks = [nd for nd in postorder(P.root) if nd.chunk]
    for k, nd in enumerate(P.chunks):
        nd.chunk = k
    # the cost of each chunk's own declaration
    for nd in P.chunks:
        if nd.split:
            nd.est = chunk_split_est(nd)
        else:
            nd.est = C_DECL + own_cost(nd)


def own_cost(root):
    tot = 0.0
    stack = [root]
    while stack:
        x = stack.pop()
        if x is not root and x.chunk is not None:
            tot += C_EXT
            continue
        tot += x.cost
        if x.kind == 'P':
            stack.append(x.t)
            stack.append(x.e)
    return tot


def chunk_split_est(nd):
    """The estimated kernel time of a split Hubcap leaf (all its pieces) and its largest
    piece."""
    tot, mx = 2 * C_DECL, C_DECL
    for ci, pl in enumerate(nd.plans):
        if ci >= nd.tail:
            break
        if pl[0] == 'decide':
            tot += pl[1]
            mx = max(mx, pl[1])
        else:
            tot += pl[1]
            for a in pl[2]:
                if a[0] != 'swap':
                    tot += a[1]
                    mx = max(mx, a[1])
    if nd.tail < len(nd.plans):
        tot += nd.tail_cost + C_DECL
        mx = max(mx, nd.tail_cost + C_DECL)
    nd.max_piece = mx
    return tot


def pack(chunks, budget):
    """Cut a sequence of chunks into consecutive groups of estimated cost at most `budget`."""
    groups, cur, acc = [], [], 0.0
    for nd in chunks:
        if cur and acc + nd.est > budget:
            groups.append(cur)
            cur, acc = [], 0.0
        cur.append(nd)
        acc += nd.est
    if cur:
        groups.append(cur)
    return groups


def plan_files(P, args):
    """Group the chunks into files. The maximal subtrees whose chunks cost at most the file
    budget are "file roots"; consecutive file roots are packed into files (these files do not
    import each other, so they build in parallel), and the chunks above the file roots (the
    skeleton of the presentation, with the root chunk) come last, in `Exclude.lean` (and in
    files before it if they cost more than the file budget)."""
    FB = args.file_budget
    sub = {}
    for nd in postorder(P.root):
        c = nd.est if nd.chunk is not None else 0.0
        if nd.kind == 'P':
            c += sub[nd.t.idx] + sub[nd.e.idx]
        sub[nd.idx] = c
    roots, stack = [], [P.root]
    while stack:
        nd = stack.pop()
        if sub[nd.idx] <= FB or nd.kind != 'P':
            if sub[nd.idx] > 0:
                roots.append(nd)
            continue
        stack.append(nd.e)
        stack.append(nd.t)
    groups = []
    if roots and roots[0] is not P.root:
        # the chunks of the file roots, packed in order
        runs, cur, acc = [], [], 0.0
        for r in roots:
            if cur and acc + sub[r.idx] > FB:
                runs.append(cur)
                cur, acc = [], 0.0
            cur.append(r)
            acc += sub[r.idx]
        runs.append(cur)
        inside = set()
        for run in runs:
            g = []
            for r in run:
                for nd in postorder(r):
                    if nd.chunk is not None:
                        g.append(nd)
                        inside.add(nd.idx)
            groups.append(g)
        skeleton = [nd for nd in P.chunks if nd.idx not in inside]
        groups += pack(skeleton, FB)
    else:
        groups = pack(P.chunks, FB)
    P.files = []
    for i, g in enumerate(groups):
        name = 'Exclude' if i == len(groups) - 1 else f'C{i:02d}'
        P.files.append({'name': name, 'chunks': g})
        for nd in g:
            nd.file = i
    assert P.root.file == len(groups) - 1


# ---------------------------------------------------------------------------------------------
# Lean text
# ---------------------------------------------------------------------------------------------

def lean_bool(b):
    return 'true' if b else 'false'


def lean_int(b):
    return f'({b})' if b < 0 else str(b)


def hubcap_src(cons):
    s = '.nil'
    for (j1, j2, b) in reversed(cons):
        s = (f'(.cons1 {j1} {lean_int(b)} {s})' if j2 is None
             else f'(.cons2 {j1} {j2} {lean_int(b)} {s})')
    return s


def goal_src(nd, part=None):
    ctx = ('[' + (',\n      '.join(nd.ctx)) + ']') if nd.ctx else '[]'
    return f'⟨{nd.p0},\n     {part or nd.p},\n     {ctx}⟩'


def tree_src(root, exts):
    """The PTree term of the chunk rooted at `root` (its sub-chunks are `ext` leaves, collected
    in `exts` in preorder)."""
    lines = []

    def go(nd, ind):
        pad = ' ' * ind
        if nd is not root and nd.chunk is not None:
            exts.append(nd)
            lines.append(f'{pad}(.ext {len(exts) - 1})')
            return
        if nd.kind == 'P':
            loc, j0, k, lo, named, _ = nd.args
            lines.append(f'{pad}(.pcase {LOCS[loc]} {j0} {k} {lean_bool(lo)} {lean_bool(named)}')
            go(nd.t, ind + 2)
            go(nd.e, ind + 2)
            lines[-1] += ')'
        elif nd.kind == 'R':
            lines.append(f'{pad}(.reducible {nd.mask})')
        elif nd.kind == 'H':
            lines.append(f'{pad}(.hubcap {hubcap_src(nd.args)}')
            lines.append(f'{pad}  {nd.mask})')
        else:
            lbl, j, mir, _ = nd.args
            lines.append(f'{pad}(.similar {lbl} {j} {lean_bool(mir)})')

    # iterative wrapper would be overkill: the trees are at most ~50 deep
    go(root, 2)
    return '\n'.join(lines)


def fmt_ms(ms):
    return f'{ms / 1000:.2f} s' if ms >= 1000 else f'{ms:.0f} ms'


class Emitter:
    def __init__(self, P):
        self.P = P
        self.n = P.n
        self.rf = f'QuizData.theDruleFork{P.n}'
        self.uses_rules = False
        self.decls = []    # (name, est ms, kind) for the summary

    def rules_list(self, idxs):
        self.uses_rules = True
        return '[' + ', '.join(f'rule{i}' for i in idxs) + ']'

    def redp(self, k):
        return f'(redpartFast (qztPruneFast theQuizTree mask{k}))'

    def chain_src(self, acts, dual):
        cons_of = 'check2Dbound2RecFast_cons_of' if dual else 'checkDbound2RecFast_cons_of'
        out = []
        for a in acts:
            if a[0] == 'head':
                out.append(f'  {cons_of} (by decide +kernel) <|')
            elif a[0] == 'swap':
                out.append('  (check2Dbound2RecFast_succ_nil_cons _ _ _ _ _ _ _ _ _ _ _ _ _).trans <|')
            else:
                out.append('  (by decide +kernel)')
        return '\n'.join(out)

    def constraint_theorem(self, nd, ci, pl):
        """The theorem `c<k>_<ci>` of a constraint split along its chain."""
        n, k = self.n, nd.chunk
        j1, j2, b = nd.args[ci]
        data = nd.cons_data[ci]['data']
        st = data['st']
        redp = self.redp(k)
        rs, rt = f'{self.rf}.sourceDrules', f'{self.rf}.targetDrules'
        acts = pl[2]
        npieces = sum(1 for a in acts if a[0] != 'swap')
        est = pl[1] + sum(a[1] for a in acts if a[0] != 'swap')
        lines = []
        if j2 is not None:
            desc = f'`$[{j1 + 1},{j2 + 1}] <= {b}`'
            stmt = (f'check2Dbound2Fast {n} {redp}\n    {rs} {rt}\n'
                    f'    (hubcapRotFast {n} {j1} part{k}) (hubSubnFast {n} {j2} {j1}) {lean_int(b)} = true')
            entry = ('  check2Dbound2Fast_of_rec_lit ' + str(n) + ' _ _ _ _ _ _ (by decide +kernel)'
                     ' (by decide +kernel)\n    (by decide +kernel) (by decide +kernel)'
                     ' (by decide +kernel) (by decide +kernel)\n    (by decide +kernel)'
                     ' (by decide +kernel) (by decide +kernel) <|')
            show = (f'  show check2Dbound2RecFast {n} {redp} {st["m"]}\n'
                    f'      {st["P1"]}\n      {st["P2"]}\n'
                    f'      {self.rules_list(st["rt1"])}\n      {self.rules_list(st["rs1"])} []\n'
                    f'      {self.rules_list(st["rt2"])}\n      {self.rules_list(st["rs2"])} []\n'
                    f'      {st["i"]} {st["nt"]} = true from')
        else:
            desc = f'`$[{j1 + 1}] <= {b}`'
            stmt = (f'checkDbound2Fast {redp}\n    {rs} {rt}\n'
                    f'    (hubcapRotFast {n} {j1} part{k}) {lean_int(b)} = true')
            entry = ('  checkDbound2Fast_of_rec_lit _ _ _ _ _ (by decide +kernel) (by decide +kernel)'
                     '\n    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|')
            show = (f'  show checkDbound2RecFast {redp} {st["m"]}\n'
                    f'      {st["P"]}\n'
                    f'      {self.rules_list(st["rt"])}\n      {self.rules_list(st["rs"])} []\n'
                    f'      {st["nt"]} = true from')
        name = f'c{k}_{ci}'
        self.decls.append((name, est, 'constraint', max(a[1] for a in acts if a[0] != 'swap')))
        lines.append(f'/-- Constraint {ci} of the Hubcap leaf of chunk `c{k}`, {desc}, checked '
                     f'target rule by\ntarget rule: {npieces} pieces, estimated kernel time '
                     f'{fmt_ms(est)}. -/')
        lines.append(f'theorem {name} :\n    {stmt} :=')
        lines.append(entry)
        lines.append(show)
        lines.append(self.chain_src(acts, j2 is not None))
        return '\n'.join(lines) + '\n'

    def split_chunk(self, nd):
        n, k = self.n, nd.chunk
        out = []
        out.append(f'/-- The pruning mask of the Hubcap leaf of chunk `c{k}` (node {nd.idx}). -/')
        out.append(f'def mask{k} : QztMask :=\n  {nd.mask}\n')
        out.append(f'/-- The part of the Hubcap leaf of chunk `c{k}` (node {nd.idx}). -/')
        out.append(f'def part{k} : Part :=\n  {nd.p}\n')
        for ci, pl in enumerate(nd.plans):
            if ci < nd.tail and pl[0] == 'chain':
                out.append(self.constraint_theorem(nd, ci, pl))
        # the leaf
        fit = []
        for ci, pl in enumerate(nd.plans):
            if ci >= nd.tail:
                break
            j2 = nd.args[ci][1]
            lemma = 'hubcapFitFast_cons1_of' if j2 is None else 'hubcapFitFast_cons2_of'
            arg = f'c{k}_{ci}' if pl[0] == 'chain' else '(by decide +kernel)'
            fit.append(f'  {lemma} {arg} <|')
        fit.append('  hubcapFitFast_nil' if nd.tail == len(nd.plans) else '  (by decide +kernel)')
        est = nd.est
        self.decls.append((f'c{k}', est, 'hubcap', nd.max_piece))
        out.append(f'/-- Chunk `c{k}`: the Hubcap leaf at node {nd.idx}, checked constraint by '
                   f'constraint\n(estimated kernel time {fmt_ms(est)}, at most '
                   f'{fmt_ms(nd.max_piece)} per declaration). -/')
        out.append(f'theorem c{k} : PGoal.OK\n    {goal_src(nd, f"part{k}")} :=')
        out.append(f'  PGoal.ok_of_hubcap {self.rf} mask{k} {hubcap_src(nd.args)}\n'
                   f'    (by decide +kernel) (by decide +kernel) <|')
        out.append('\n'.join(fit))
        return '\n'.join(out) + '\n'

    def tree_chunk(self, nd):
        k = nd.chunk
        exts = []
        body = tree_src(nd, exts)
        gs = '.nil'
        for ch in reversed(exts):
            gs = f'(.cons c{ch.chunk} {gs})'
        what = 'the root of the presentation' if nd is self.P.root else f'the subtree at node {nd.idx}'
        self.decls.append((f'c{k}', nd.est, 'tree', nd.est))
        out = [f'/-- The case tree of chunk `c{k}` ({what}). -/',
               f'def t{k} : PTree :=\n{body}\n',
               f'/-- Chunk `c{k}`: {what} (estimated kernel time {fmt_ms(nd.est)}). -/',
               f'theorem c{k} : PGoal.OK\n    {goal_src(nd)} :=',
               f'  PGoal.ok_of_checkTree {self.rf} {gs} t{k} (by decide +kernel)']
        return '\n'.join(out) + '\n'

    def file_text(self, fi, cmdline):
        P, n = self.P, self.n
        f = P.files[fi]
        imports = set()
        for nd in f['chunks']:
            if nd.split:
                continue
            stack = [nd.t, nd.e] if nd.kind == 'P' else []
            while stack:
                x = stack.pop()
                if x.chunk is not None:
                    if x.file != fi:
                        imports.add(x.file)
                    continue
                if x.kind == 'P':
                    stack.append(x.t)
                    stack.append(x.e)
        body = []
        for nd in f['chunks']:
            body.append(self.split_chunk(nd) if nd.split else self.tree_chunk(nd))
        uses_rules = any(nd.split and any(pl[0] == 'chain' for ci, pl in enumerate(nd.plans)
                                          if ci < nd.tail) for nd in f['chunks'])
        lines = [HEADER.rstrip('\n')]
        mods = ['FourColor.Present.Tree']
        if uses_rules:
            mods.append(f'FourColor.Present.P{n}.Rules')
        mods += [f'FourColor.Present.P{n}.{P.files[i]["name"]}' for i in sorted(imports)]
        lines += [f'import {m}' for m in mods]
        est = sum(nd.est for nd in f['chunks'])
        last = fi == len(P.files) - 1
        ks = [nd.chunk for nd in f['chunks']]
        if len(ks) == 1:
            which = f'chunk `c{ks[0]}`'
        elif ks == list(range(ks[0], ks[-1] + 1)):
            which = f'chunks `c{ks[0]}` to `c{ks[-1]}`'
        else:
            which = 'chunks ' + ', '.join(f'`c{k}`' for k in ks)
        doc = [
            '',
            '/-!',
            f'# The presentation for hub size {n} (Coq `present{n}.v`), {which}',
            '',
            f'{MARK} from `present{n}.v`; do not edit (re-split with the',
            f'generator\'s options instead): `{cmdline}`.',
            '',
            f'{len(f["chunks"])} chunk{"s" if len(f["chunks"]) > 1 else ""} of the case tree of `present{n}.v` (see `FourColor.Present.Tree`),',
            f'children first; estimated kernel time {fmt_ms(est)}.',
        ]
        if last:
            doc.append(f'The last chunk is the root goal `Check pcons_ {n} in pcons_ {n}`, and '
                       f'`FourColor.exclude{n}`')
            doc.append('follows from it.')
        doc.append('-/')
        lines += doc
        lines.append('')
        lines.append(f'namespace FourColor.Present{n}')
        lines.append('')
        lines += body
        lines.append(f'end FourColor.Present{n}')
        if last:
            lines += ['', 'namespace FourColor', '',
                      f'/-- Coq `exclude{n}`: the presentation for hub size {n} (`present{n}.v`). -/',
                      f'theorem exclude{n} : ExcludedArity {n} :=',
                      f'  excludedArity_of_ok Present{n}.c{P.root.chunk}', '',
                      'end FourColor']
        return '\n'.join(lines) + '\n', uses_rules

    def rules_text(self, cmdline):
        n = self.n
        lines = [HEADER.rstrip('\n'), 'import FourColor.Present.Tree', '', '/-!',
                 f'# The rules of the drule fork for hub size {n}, as named parts', '',
                 f'{MARK}; do not edit: `{cmdline}`.', '',
                 f'`rule<i>` is a rule of `QuizData.theDruleFork{n}` (source or target); the split '
                 'Hubcap',
                 f'constraints of `FourColor/Present/P{n}/` state the rule lists of their recursive '
                 'checks',
                 'with these names.', '-/', '', f'namespace FourColor.Present{n}', '']
        for i, r in enumerate(self.P.rules):
            lines.append(f'/-- Rule {i} of the drule fork for hub size {n}. -/')
            lines.append(f'def rule{i} : Part := {r}')
            lines.append('')
        lines.append(f'end FourColor.Present{n}')
        return '\n'.join(lines) + '\n'


# ---------------------------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------------------------

def write_presentation(P, args, cmdline):
    E = Emitter(P)
    outdir = os.path.join(ROOT, args.out, f'P{P.n}')
    texts = {}
    need_rules = False
    for fi, f in enumerate(P.files):
        text, ur = E.file_text(fi, cmdline)
        texts[f['name'] + '.lean'] = text
        need_rules = need_rules or ur
    if need_rules:
        texts['Rules.lean'] = E.rules_text(cmdline)
    for t in texts.values():
        for bad in ('sorry', 'native_decide', 'admit'):
            if bad in t:
                raise SystemExit(f'present{P.n}: generated text contains {bad}')
    E.ndecide = sum(t.count('by decide +kernel') for t in texts.values())
    E.nfiles = len(texts)
    if args.dry_run:
        return E
    os.makedirs(outdir, exist_ok=True)
    # remove the files of a previous generation
    for fn in sorted(os.listdir(outdir)):
        path = os.path.join(outdir, fn)
        if fn.endswith('.lean') and fn not in texts:
            with open(path) as fh:
                head = fh.read(2000)
            if MARK in head or fn == 'Exclude.lean':
                os.remove(path)
    for fn, t in texts.items():
        with open(os.path.join(outdir, fn), 'w') as fh:
            fh.write(t)
    return E


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('pres', nargs='*', type=int)
    ap.add_argument('--budget', type=float, default=400.0)
    ap.add_argument('--override', action='append', default=[])
    ap.add_argument('--file-budget', type=float, default=60000.0)
    ap.add_argument('--out', default=os.path.join('FourColor', 'Present'))
    ap.add_argument('--cache', default=os.path.join('.lake', 'present_gen'))
    ap.add_argument('--refresh', action='store_true')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--summary')
    args = ap.parse_args()
    pres = args.pres or list(range(5, 12))
    summary = {}
    for n in pres:
        if not 5 <= n <= 11:
            raise SystemExit(f'no presentation {n}')
        P = load(n, args)
        plan_chunks(P, args)
        plan_files(P, args)
        # the command line that regenerates this presentation with the same options
        opts = []
        if args.budget != 400.0:
            opts.append(f'--budget {args.budget:g}')
        for o in args.override:
            if o.split(':')[0] == str(n):
                opts.append(f'--override {o}')
        if args.file_budget != 60000.0:
            opts.append(f'--file-budget {args.file_budget:g}')
        cmdline = ' '.join(['scripts/present_gen.py', str(n)] + opts)
        E = write_presentation(P, args, cmdline)
        cnt = count_kinds(P.root)
        split = [nd for nd in P.chunks if nd.split]
        tot = sum(nd.est for nd in P.chunks)
        mx = max(d[3] for d in E.decls)
        print(f'present{n}: {len(P.nodes)} nodes (Pcase {cnt["P"]}, Reducible {cnt["R"]}, '
              f'Hubcap {cnt["H"]}, Similar {cnt["S"]}); {len(P.chunks)} chunk{"s" * (len(P.chunks) > 1)} '
              f'({len(split)} split Hubcap leaves), {E.ndecide} kernel checks, {E.nfiles} files; '
              f'estimated kernel time {fmt_ms(tot)}, at most {fmt_ms(mx)} per declaration')
        if P.over:
            nodes = sorted({o[0] for o in P.over})
            print(f'  {len(P.over)} declarations over the budget (a constraint or a head of a '
                  f'constraint that cannot be split further; at most '
                  f'{fmt_ms(max(o[2] for o in P.over))}), in the Hubcap leaves at nodes '
                  + ', '.join(map(str, nodes)))
        summary[n] = {'decls': E.decls, 'ndecide': E.ndecide, 'est_ms': tot, 'files': [
            {'name': f['name'], 'chunks': [f'c{nd.chunk}' for nd in f['chunks']],
             'est': sum(nd.est for nd in f['chunks'])} for f in P.files]}
    if args.summary:
        with open(args.summary, 'w') as fh:
            json.dump(summary, fh, indent=1)


if __name__ == '__main__':
    main()
