#!/usr/bin/env python3
"""Delta-swap (Benes) networks for the packed graded layout of FourColor/Engine/Layout.lean.

Reference implementation of the layout (must agree with the Lean definitions `gsize`, `goff`,
`blockRank`, `xcode`, `gpos`, `cpos`, `b3idx`) and generator of the two networks per ring size:

  tau  : bit cpos(t) of applyNet(tau, x)  = bit cpos(tau12 t)       of x   (TauSpec)
  cnv  : bit cpos(t) of applyNet(cnv, x)  = bit b3idx(t[:r-1])      of x   (CnvSpec)

A layer (m, d) maps x to x ^ t ^ (t << d), t = ((x >> d) ^ x) & m (`deltaSwap`).

Usage:  engine_nets.py R OUTDIR      writes OUTDIR/tau_R.txt and OUTDIR/cnv_R.txt, one layer
                                     per line as "(0x<hex>, <d>)" (read by `#engine_load_net`).
        engine_nets.py --selftest R  checks the layout (bijection) and the networks.

This script is a development tool (a reference implementation, to cross-check the layout and
the networks); the networks of the proof are routed by the Lean meta-program `#engine_nets` of
FourColor/Engine/Gen.lean.
"""
import sys
import os
from math import comb
from itertools import product


def gsize(r, k):
    return (1 - r % 2) if k == 0 else comb(r, 2 * k) * 2 ** (2 * k - 1)


def goffs(r):
    offs, o = [], 0
    for k in range(r // 2 + 2):
        offs.append(o)
        o += gsize(r, k)
    return offs


def gtotal(r):
    return goffs(r)[r // 2 + 1]


def blockrank(t, m):
    br = 0
    n = len(t)
    for i, c in enumerate(t):
        if c != 1:
            br += comb(n - 1 - i, m)
            m -= 1
    return br


def xcode(t):
    x = 0
    for c in reversed(t):
        if c == 1:
            continue
        x = 2 * x + (1 if c == 3 else 0)
    return x


def gpos(r, t):
    m = sum(1 for c in t if c != 1)
    return (xcode(t) // 2) * comb(r, m) + blockrank(t, m)


def cpos(r, t, offs):
    m = sum(1 for c in t if c != 1)
    return offs[m // 2] + gpos(r, t)


def b3idx(t):
    x = 0
    for c in reversed(t):
        x = 3 * x + (c - 1)
    return x


def valid_traces(r):
    """All valid traces of size r (colors 1..3, xor-sum 0), via their prefixes."""
    for pre in product((1, 2, 3), repeat=r - 1):
        s = 0
        for c in pre:
            s ^= c
        if s != 0:
            yield pre + (s,)


TAU12 = {1: 2, 2: 1, 3: 3}


# ---------------------------------------------------------------- Benes routing

def route(src, n):
    """Benes routing: src[j] = input position whose bit must arrive at output j
    (a permutation of range(2^n)).  Returns the layer masks for the distances
    N/2, ..., 1, ..., N/2 (masks mark the lower index i of each swapped pair (i, i+d)).
    Iterative looping algorithm."""
    N = 1 << n
    if n == 0:
        return []
    if n == 1:
        return [1 if src[0] == 1 else 0]
    h = N // 2
    inv = [0] * N
    for j, s in enumerate(src):
        inv[s] = j
    sub = [-1] * N
    for start in range(N):
        if sub[start] != -1:
            continue
        i = start
        s = 0
        while sub[i] == -1:
            sub[i] = s
            ip = i ^ h
            sub[ip] = 1 - s
            j = inv[ip]
            jp = j ^ h
            i = src[jp]
            if sub[i] != -1:
                break
    first = 0
    for i in range(h):
        if sub[i] == 1:
            first |= 1 << i
    pos_after = [0] * N
    for i in range(N):
        pos_after[i] = (i % h) + (h if sub[i] == 1 else 0)
    last = 0
    for j in range(h):
        if sub[src[j]] == 1:
            last |= 1 << j
    sub_src = [[0] * h, [0] * h]
    for q in range(h):
        for s in (0, 1):
            j = q if sub[src[q]] == s else q + h
            sub_src[s][q] = pos_after[src[j]] - (h if s == 1 else 0)
    ml = route(sub_src[0], n - 1)
    mu = route(sub_src[1], n - 1)
    mids = [a | (b << h) for a, b in zip(ml, mu)]
    return [first] + mids + [last]


def layer_dists(n):
    N = 1 << n
    ds = [N >> (i + 1) for i in range(n)]
    return ds + ds[-2::-1]


def apply_layers(x, layers):
    for m, d in layers:
        t = ((x >> d) ^ x) & m
        x = x ^ t ^ (t << d)
    return x


def benes(src, n):
    masks = route(src, n)
    ds = layer_dists(n)
    assert len(masks) == len(ds)
    # drop empty layers (they are identities)
    return [(m, d) for m, d in zip(masks, ds) if m != 0]


def complete_perm(pairs, n):
    """pairs: dict out->in (partial injective); complete to a permutation of range(2^n),
    mapping free outputs to free inputs in increasing order."""
    N = 1 << n
    src = [-1] * N
    used = [False] * N
    for j, i in pairs.items():
        src[j] = i
        used[i] = True
    free_in = [i for i in range(N) if not used[i]]
    k = 0
    for j in range(N):
        if src[j] == -1:
            src[j] = free_in[k]
            k += 1
    return src


def nets(r):
    offs = goffs(r)
    total = offs[r // 2 + 1]
    tau_pairs = {}
    cnv_pairs = {}
    for t in valid_traces(r):
        j = cpos(r, t, offs)
        tau_pairs[j] = cpos(r, tuple(TAU12[c] for c in t), offs)
        cnv_pairs[j] = b3idx(t[:r - 1])
    assert len(tau_pairs) == total and sorted(tau_pairs) == list(range(total))
    n_tau = max(1, (total - 1).bit_length())
    tau = benes(complete_perm(tau_pairs, n_tau), n_tau)
    n_cnv = max(1, (3 ** (r - 1) - 1).bit_length(), (total - 1).bit_length())
    cnv = benes(complete_perm(cnv_pairs, n_cnv), n_cnv)
    return tau, cnv, total, tau_pairs, cnv_pairs


def rev_net(r):
    """Network of the ring reversal t -> t[::-1] (Birkhoff check): bit cpos(t) of the output
    is bit cpos(reverse t) of the input."""
    offs = goffs(r)
    total = offs[r // 2 + 1]
    pairs = {}
    for t in valid_traces(r):
        pairs[cpos(r, t, offs)] = cpos(r, tuple(reversed(t)), offs)
    n = max(1, (total - 1).bit_length())
    return benes(complete_perm(pairs, n), n)


def write_layers(path, layers):
    with open(path, 'w') as f:
        for m, d in layers:
            f.write(f'(0x{m:x}, {d})\n')


def selftest(r):
    import random
    tau, cnv, total, tau_pairs, cnv_pairs = nets(r)
    for _ in range(3):
        x = random.getrandbits(total)
        y = apply_layers(x, tau)
        for j in random.sample(range(total), min(total, 3000)):
            assert (y >> j) & 1 == (x >> tau_pairs[j]) & 1
        x = random.getrandbits(3 ** (r - 1))
        y = apply_layers(x, cnv)
        for j in random.sample(range(total), min(total, 3000)):
            assert (y >> j) & 1 == (x >> cnv_pairs[j]) & 1
    print(f'r={r}: total {total}, tau {len(tau)} layers, cnv {len(cnv)} layers: ok',
          file=sys.stderr)


def main():
    if sys.argv[1] == '--selftest':
        selftest(int(sys.argv[2]))
        return
    if sys.argv[1] == '--rev':
        r = int(sys.argv[2])
        write_layers(os.path.join(sys.argv[3], f'rev_{r}.txt'), rev_net(r))
        return
    r = int(sys.argv[1])
    out = sys.argv[2]
    os.makedirs(out, exist_ok=True)
    tau, cnv, total, _, _ = nets(r)
    write_layers(os.path.join(out, f'tau_{r}.txt'), tau)
    write_layers(os.path.join(out, f'cnv_{r}.txt'), cnv)
    size = sum(m.bit_length() for m, _ in tau) // 8 + sum(m.bit_length() for m, _ in cnv) // 8
    print(f'r={r}: total {total} bits, tau {len(tau)} layers, cnv {len(cnv)} layers, '
          f'{size} bytes of masks', file=sys.stderr)


if __name__ == '__main__':
    main()
