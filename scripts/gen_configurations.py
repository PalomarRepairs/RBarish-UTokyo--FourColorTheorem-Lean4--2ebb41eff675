#!/usr/bin/env python3
"""Generate FourColor/Configurations.lean from fourcolor's `configurations.v`.

Mechanical translation of the Coq file `theories/proof/configurations.v` of
math-comp/fourcolor (the construction programs of the 633 reducible
configurations `cf001` .. `cf633`, written in the concrete syntax of
`cfmap.v`'s module `ConfigSyntax`, and the list `the_configs`), together with
the dummy configuration `cf000` of `cfreducible.v` (`Definition cf000 :=
Config 0 H.`, the default value of `nth` on configuration lists).

Coq syntax (cfmap.v, Module ConfigSyntax):

    Definition cf001 := Config* 13
      H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y.

  * `Config*` sets `cfsym := true`, `Config` sets `cfsym := false`;
  * the items form a `cprog`: a numeral `n` is the step `CpR n` (coercion
    `CpR : nat >-> cpstep`), and `H`, `Y`, `U` are `CpH`, `CpY`, `CpU`;
  * the notation is `parse_config sym [::] cp`, which moves the leading
    `CpR i` steps into the contract list `cfcontract_ref` (in order); the rest
    of the items is `cfprog`;
  * `the_configs := @seqn config 633 cf001 ... cf633` lists all of them.

Lean output (target: `FourColor.Config` of `FourColor/CfMap/Prog.lean`):

  * `--form literal` (default): each configuration is the explicit structure
    literal denoted by the notation, i.e. the value of `parse_config`:

        def cf001 : Config :=
          { cfsym := true, cfcontractRef := [13],
            cfprog := [.H, .R 3, .H, .R 5, .H, .R 5, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y] }

    (long programs are wrapped at 100 columns). This is the form used for
    FourColor/Configurations.lean.

  * `--form macro`: the `Config*`/`Config` notation of
    `FourColor.ConfigSyntax` applied to the Coq items verbatim (the stored
    value is then `parseConfig sym [] [...]`, not in normal form).

  In both cases the Coq source text of each configuration is quoted in its
  docstring, `theConfigs : List Config` lists the configurations in the order
  of `the_configs`, closed-term extraction of the code generator is disabled
  (it would triple the size of the .olean), and the file ends with two
  kernel-checked sanity theorems (`length_theConfigs`,
  `configProg_theConfigs`).

  * `--check-out FILE` additionally writes a validation file (to be compiled
    with `lake env lean FILE` after building the .olean of the generated
    module) which checks
      - by `rfl`, that `cf000` and every `cfNNN` are equal to the
        `Config*`/`Config` notation of `FourColor.ConfigSyntax` applied to the
        Coq items (an independent check of the contract splitting done here);
      - by `rfl`, that `theConfigs` is `[cf001, ..., cf633]`;
      - by `decide +kernel`, that every program starts with an `H`;
      - with `--ring-csv`, by `decide +kernel`, that `cprsize cf.cfprog` of
        every configuration is the ring size listed in the CSV (columns `idx`
        = configuration number, `ring`).

Usage:
    python3 scripts/gen_configurations.py [--coq-dir DIR] [--out FILE]
        [--form literal|macro] [--check-out FILE] [--ring-csv CSV]

The output is deterministic, so rerunning the script (e.g. to produce only the
validation file) rewrites FILE with identical contents.  Validation run
(RINGS.csv: the ring size of every configuration, columns idx and ring):
    python3 scripts/gen_configurations.py \
        --check-out scratch/configurations_check.lean \
        --ring-csv RINGS.csv
    lake env lean scratch/configurations_check.lean

Defaults: --coq-dir .deps/fourcolor/theories/proof (a clone of math-comp/fourcolor),
          --out FourColor/Configurations.lean (both relative to the project root,
          i.e. the parent directory of this script's directory).
"""
import argparse
import csv
import os
import re
import sys

EXPECTED_COUNT = 633
LINE_WIDTH = 100

# ConfigSyntax identifiers (cfmap.v defines H, Y, U; the Lean syntax also
# accepts K, A and R', which never occur in the configuration data).
STEP_IDENTS = ('H', 'Y', 'U', 'K', 'A', "R'")


# --------------------------------------------------------------------------
# Parsing the Coq sources

def strip_coq_comments(src):
    """Remove (possibly nested) Coq comments, keeping line structure."""
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith('(*', i):
            depth += 1
            i += 2
        elif depth > 0 and src.startswith('*)', i):
            depth -= 1
            i += 2
        else:
            if depth == 0 or src[i] == '\n':
                out.append(src[i])
            i += 1
    if depth != 0:
        raise ValueError('unterminated Coq comment')
    return ''.join(out)


DEF_RE = re.compile(r'Definition\s+(cf\d+)\s*:=\s*(Config\*?)\s+([^.]*)\.')


class Cfg:
    """One `Definition cfNNN := Config[*] items.` of the Coq source."""

    def __init__(self, name, sym, items, raw_lines):
        self.name = name          # 'cf001'
        self.sym = sym            # True for Config*
        self.items = items        # list of tokens (str): '13', 'H', ...
        self.raw_lines = raw_lines  # Coq text of the notation, original layout
        # parse_config: leading numerals are the contract annotation
        k = 0
        while k < len(items) and items[k].isdigit():
            k += 1
        self.contract = [int(t) for t in items[:k]]
        self.prog = items[k:]     # tokens, first one is not a numeral

    @property
    def keyword(self):
        return 'Config*' if self.sym else 'Config'


def parse_items(name, body):
    toks = body.split()
    for t in toks:
        if not (t.isdigit() or t in STEP_IDENTS):
            raise ValueError(f'{name}: unknown configuration item {t!r}')
    if not toks:
        raise ValueError(f'{name}: empty configuration')
    return toks


def raw_layout(kw, body):
    """The Coq text `Config* 13\n  H 3 ...` with its original line breaks
    (trailing blanks removed, continuation lines re-indented by 2)."""
    lines = [ln.strip() for ln in body.split('\n')]
    lines = [ln for ln in lines if ln]
    first = f'{kw} {lines[0]}'
    return [first] + ['  ' + ln for ln in lines[1:]]


def parse_configurations(path):
    src = strip_coq_comments(open(path).read())
    cfgs = []
    for m in DEF_RE.finditer(src):
        name, kw, body = m.group(1), m.group(2), m.group(3)
        items = parse_items(name, body)
        cfgs.append(Cfg(name, kw == 'Config*', items, raw_layout(kw, body)))
    ndefs = len(re.findall(r'\bDefinition\b', src))
    if ndefs != len(cfgs) + 1:   # + the_configs
        raise ValueError(f'{path}: {ndefs} Definitions but {len(cfgs)} configurations parsed')
    m = re.search(r'Definition\s+the_configs\s*:=\s*@seqn\s+config\s+(\d+)\s+([^.]*)\.', src)
    if not m:
        raise ValueError('the_configs not found')
    count = int(m.group(1))
    order = m.group(2).split()
    if len(order) != count:
        raise ValueError(f'the_configs: seqn {count} but {len(order)} names')
    names = [c.name for c in cfgs]
    if len(set(names)) != len(names):
        raise ValueError('duplicate configuration names')
    if sorted(order) != sorted(names):
        raise ValueError('the_configs does not list exactly the defined configurations')
    return cfgs, order


def parse_cf000(path):
    src = strip_coq_comments(open(path).read())
    m = re.search(r'Definition\s+(cf000)\s*:=\s*(Config\*?)\s+([^.]*)\.', src)
    if not m:
        raise ValueError(f'{path}: cf000 not found')
    name, kw, body = m.group(1), m.group(2), m.group(3)
    return Cfg(name, kw == 'Config*', parse_items(name, body), raw_layout(kw, body))


# --------------------------------------------------------------------------
# Emitting Lean

def lean_step(tok):
    if tok.isdigit():
        return f'.R {int(tok)}'
    return f'.{tok}'


def wrap_items(items, first_prefix, cont_indent, last_suffix, width=LINE_WIDTH):
    """Lay out `first_prefix item, item, ... item last_suffix` over several lines,
    continuation lines being indented by `cont_indent` spaces."""
    lines, cur = [], first_prefix
    for i, it in enumerate(items):
        piece = it + (', ' if i + 1 < len(items) else last_suffix)
        cand = cur + piece
        if len(cand.rstrip()) > width and cur.strip() and cur != first_prefix:
            lines.append(cur.rstrip())
            cur = ' ' * cont_indent + piece
        else:
            cur = cand
    lines.append(cur.rstrip())
    return lines


def emit_literal(c):
    """`def cfNNN : Config := { ... }` lines (explicit structure literal)."""
    sym = 'true' if c.sym else 'false'
    contract = '[' + ', '.join(str(n) for n in c.contract) + ']'
    steps = ', '.join(lean_step(t) for t in c.prog)
    one_line = f'  {{ cfsym := {sym}, cfcontractRef := {contract}, cfprog := [{steps}] }}'
    if len(one_line) <= LINE_WIDTH:
        return [f'def {c.name} : Config :=', one_line]
    head = f'  {{ cfsym := {sym}, cfcontractRef := {contract},'
    prefix = '    cfprog := ['
    body = wrap_items([lean_step(t) for t in c.prog], prefix, len(prefix), '] }')
    return [f'def {c.name} : Config :=', head] + body


def emit_macro(c):
    """`def cfNNN : Config := Config* ...` lines (ConfigSyntax notation)."""
    lines = [f'def {c.name} : FourColor.Config := {c.raw_lines[0]}']
    lines += c.raw_lines[1:]
    return lines


def docstring(c, what):
    lines = [f'/-- {what}:', '```']
    lines += c.raw_lines
    lines += ['```', '-/']
    return lines


HEADER = '''\
/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfMap.Prog

/-!
# The 633 reducible configurations  (port of `configurations.v`)

**This file is generated**: it is a mechanical translation of the Coq file
`theories/proof/configurations.v` of math-comp/fourcolor, produced by
`scripts/gen_configurations.py`. Do not edit it by hand; rerun the script instead:

```
python3 scripts/gen_configurations.py --coq-dir <fourcolor>/theories/proof \\
  --out FourColor/Configurations.lean
```

The Coq file gives the construction programs of the 633 reducible configurations of the proof,
in the concrete syntax of `cfmap.v` (module `ConfigSyntax`, see `FourColor/CfMap/Prog.lean`).

* `cfNNN` (math-comp `cfXXX`, `NNN` = `001` ... `633`): the data for configuration number `NNN`.
* `theConfigs` (math-comp `the_configs`): the list of all the `cfNNN`, in order; configuration
  number `n` has index `n - 1` in `theConfigs`, as list indices start at 0.
* `cf000` (math-comp `cf000`, defined in `cfreducible.v` as `Config 0 H`): a dummy
  configuration, the default value in `theConfigs.getD i cf000` (math-comp `nth cf000`).

## Representation

The Coq definition `Definition cfNNN := Config* c1 .. ck s1 .. sm.` (resp. `Config`), where the
`ci` are numerals and `s1` is `H`, is the value of math-comp's `parse_config`; it is translated
into the explicit structure literal it denotes:

* `cfsym := true` for `Config*`, `cfsym := false` for `Config`;
* `cfcontractRef := [c1, ..., ck]`: the leading numerals form the contract annotation;
* `cfprog := [s1', ..., sm']`: the remaining items form the construction program, where a numeral
  `n` stands for the rotation step `.R n` (math-comp coercion `CpR : nat >-> cpstep`) and the
  identifiers `H`, `Y` for the steps `.H`, `.Y` (`U`, `K`, `A` do not occur).

The Coq text of each configuration is quoted verbatim in its docstring. The explicit form does
not depend on the notation nor on `ConfigSyntax.parseConfig`, and `cfNNN` unfolds directly to
constructor applications. With `--check-out FILE`, the script also writes a validation file
checking by `rfl` that each `cfNNN` is equal to the `Config*`/`Config` notation of
`FourColor.ConfigSyntax` applied to the Coq items, and (with `--ring-csv`) by `decide +kernel`
that the ring sizes `cprsize cf.cfprog` are the expected ones; both checks pass for this file.

Only the program-level part of `cfmap.v` is needed, so this file imports
`FourColor.CfMap.Prog` rather than the whole `FourColor.CfMap`. The definitions are computable
(so that they can be `#eval`uated), but closed-term extraction is disabled for this file
(`compiler.extract_closed`): it would compile every sub-term of the data into a separate
auxiliary constant and triple the size of the `.olean`. This only affects the compiled code.

The file ends with two sanity checks, not present in the Coq development and proved by kernel
evaluation: `theConfigs` has length 633, and the program of every configuration satisfies
`configProg` (math-comp `config_prog`: only `R`, `Y` and `H` steps, ending with a `Y`).
-/

namespace FourColor

-- Code generation only: do not cache every closed sub-term of the data (see the header).
set_option compiler.extract_closed false
'''

HEADER_MACRO_OPEN = '''
open ConfigSyntax
'''

FOOTER = '''
/-- Sanity check (not in the Coq development): `theConfigs` lists 633 configurations
(math-comp `the_configs` is defined with `@seqn config 633`). -/
theorem length_theConfigs : theConfigs.length = 633 := by decide +kernel

/-- Sanity check (not in the Coq development): the construction program of every configuration
satisfies `configProg` (math-comp `config_prog`), which `cfquiz.v` and `cfcontract.v` otherwise
check explicitly. -/
theorem configProg_theConfigs : theConfigs.all (fun cf => configProg cf.cfprog) = true := by
  decide +kernel

end FourColor
'''


def emit_file(cfgs, order, cf000, form):
    out = HEADER.splitlines()
    if form == 'macro':
        out += HEADER_MACRO_OPEN.splitlines()
    out.append('')
    emit = emit_literal if form == 'literal' else emit_macro
    # cf000 first (it is defined in cfreducible.v, which comes after this file)
    out.append('/-! ### The dummy configuration `cf000` (from `cfreducible.v`) -/')
    out.append('')
    out += docstring(cf000, 'math-comp `cf000` (`cfreducible.v`), the default value of '
                            '`nth` on configuration lists')
    out += emit(cf000)
    out.append('')
    out.append('/-! ### The 633 reducible configurations -/')
    out.append('')
    for c in cfgs:
        out += docstring(c, f'math-comp `{c.name}`')
        out += emit(c)
        out.append('')
    out.append('/-- math-comp `the_configs`: the list of the 633 reducible configurations; '
               'configuration')
    out.append('number `n` (`cfNNN`) has index `n - 1`. -/')
    # inside `open ConfigSyntax` the identifier `Config` is a keyword
    cfg_type = 'Config' if form == 'literal' else 'FourColor.Config'
    out.append(f'def theConfigs : List {cfg_type} :=')
    out += wrap_items(order, '  [', 3, ']')
    out += FOOTER.splitlines()
    return '\n'.join(out) + '\n'


def emit_check(cfgs, order, cf000, ring_sizes, module):
    out = [f'import {module}', '',
           '/-! Validation of `FourColor/Configurations.lean` (generated by',
           '`scripts/gen_configurations.py --check-out`). -/', '',
           'namespace FourColor', '', 'open ConfigSyntax', '']
    out.append('/-! Each `cfNNN` equals the `Config*`/`Config` notation applied to the Coq items. -/')
    out.append('')
    for c in [cf000] + cfgs:
        items = ' '.join(c.items)
        out.append(f'example : {c.name} = ({c.keyword} {items}) := rfl')
    out.append('')
    out.append('/-! `theConfigs` lists `cf001` ... `cf633` in order, and every program starts with')
    out.append('an `H` (assumed by `cfquiz.v` and `cfcontract.v`, which check it explicitly). -/')
    out.append('')
    out.append('set_option maxRecDepth 10000 in  -- elaborator-side `rfl` on a 633-element list')
    out.append('example : theConfigs =')
    out += wrap_items(order, '    [', 5, '] := rfl')
    out.append('')
    out.append('example : theConfigs.all (fun cf => cf.cfprog.head? == some .H) = true := by')
    out.append('  decide +kernel')
    out.append('')
    if ring_sizes is not None:
        idx = {name: i for i, name in enumerate(order)}
        sizes = [ring_sizes[idx[n] + 1] for n in order]
        out.append('/-! The ring size `cprsize` of every configuration, against the CSV. -/')
        out.append('')
        out.append('example : theConfigs.map (fun cf => cprsize cf.cfprog) =')
        out += wrap_items([str(s) for s in sizes], '    [', 5, '] := by')
        out.append('  decide +kernel')
        out.append('')
    out.append('end FourColor')
    return '\n'.join(out) + '\n'


def read_ring_csv(path):
    sizes = {}
    with open(path) as f:
        for row in csv.DictReader(f):
            sizes[int(row['idx'])] = int(row['ring'])
    return sizes


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(here)
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--coq-dir', default=os.path.join(root, '.deps', 'fourcolor', 'theories', 'proof'),
                    help='directory containing configurations.v and cfreducible.v')
    ap.add_argument('--out', default=os.path.join(root, 'FourColor', 'Configurations.lean'))
    ap.add_argument('--form', choices=('literal', 'macro'), default='literal')
    ap.add_argument('--check-out', default=None,
                    help='also write a validation Lean file to this path')
    ap.add_argument('--ring-csv', default=None,
                    help='CSV with columns idx,ring (1-based configuration number, ring size)')
    ap.add_argument('--module', default='FourColor.Configurations',
                    help='module imported by the validation file')
    a = ap.parse_args()

    cfgs, order = parse_configurations(os.path.join(a.coq_dir, 'configurations.v'))
    cf000 = parse_cf000(os.path.join(a.coq_dir, 'cfreducible.v'))
    if len(cfgs) != EXPECTED_COUNT or len(order) != EXPECTED_COUNT:
        raise ValueError(f'expected {EXPECTED_COUNT} configurations, got {len(cfgs)}')
    expected_names = ['cf%03d' % i for i in range(1, EXPECTED_COUNT + 1)]
    if [c.name for c in cfgs] != expected_names or order != expected_names:
        raise ValueError('configurations are not cf001 .. cf633 in order')
    for c in cfgs + [cf000]:
        if not c.prog:
            raise ValueError(f'{c.name}: no program after the contract')

    txt = emit_file(cfgs, order, cf000, a.form)
    with open(a.out, 'w') as f:
        f.write(txt)
    print(f'{len(cfgs)} configurations (+ cf000) written to {a.out} ({a.form} form)',
          file=sys.stderr)
    if a.check_out:
        ring = read_ring_csv(a.ring_csv) if a.ring_csv else None
        if ring is not None and sorted(ring) != list(range(1, EXPECTED_COUNT + 1)):
            raise ValueError(f'{a.ring_csv}: expected rows idx = 1 .. {EXPECTED_COUNT}')
        with open(a.check_out, 'w') as f:
            f.write(emit_check(cfgs, order, cf000, ring, a.module))
        print(f'validation file written to {a.check_out}', file=sys.stderr)


if __name__ == '__main__':
    main()
