#!/usr/bin/env python3
"""Check that `Challenge.lean` and `FourColor/RealPlane.lean` define the same declarations.

The Palomar comparator requires every declaration used in the statement of `four_color` to be
identical in the Challenge environment (`Challenge.lean`) and in the Solution environment (which
imports `FourColor.RealPlane`). Both files therefore contain the same block of definitions,
delimited by the two marker lines

    -- BEGIN SYNCED DEFINITIONS
    -- END SYNCED DEFINITIONS

Textual checks (always run):

  1. each file has exactly one BEGIN and one END marker line, in this order;
  2. the two blocks (markers included) are character-for-character identical, and contain no
     `sorry`/`axiom`/... ;
  3. before the BEGIN marker both files contain only comments and `import` commands, and the two
     import lists are identical, so both blocks are elaborated in the same context;
  4. `Challenge.lean` imports only Lean core / Mathlib modules, respects the Palomar size limits
     (hard: 1000 lines and 100 KiB; preferred: 300 lines and 32 KiB), and after the block it only
     contains `namespace`/`end` commands and theorem statements proved by `sorry`, among which
     `four_color`.

Kernel check (`--lean`): compiles both files into a temporary directory (RealPlane with the
`leanOptions` of `lakefile.toml`, Challenge with default options, as `lake env lean Challenge.lean`
does) and compares the kernel declarations (universe parameters, types, values, binder
annotations, inductive data) of all the constants that the two modules define:
  * every constant of `FourColor.RealPlane` must appear in `Challenge`, and `Challenge` may only
    add the theorems stated after the block;
  * the constants must be identical; the only tolerated difference is in binder *names*, which
    the comparator ignores (it compares with `Expr.eqv`, i.e. up to alpha-equivalence): some
    auto-generated constants (`Point.noConfusionType`, `Point.mk.inj`, `Point.ctorIdx`, ...) use
    hygienic binder names that contain the module name;
  * the constants of the dependency closure of the statements, computed as the comparator does
    (`runForUsedConsts` of leanprover/comparator), must be strictly identical.
Needs `lake` on the PATH (e.g. `export PATH=$HOME/.elan/bin:$PATH`); takes ~20 seconds.

Usage (from anywhere):  python3 scripts/check_challenge_sync.py [--lean]
Exit status 0 iff all checks pass.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHALLENGE = ROOT / "Challenge.lean"
REALPLANE = ROOT / "FourColor" / "RealPlane.lean"
BEGIN = "-- BEGIN SYNCED DEFINITIONS"
END = "-- END SYNCED DEFINITIONS"

HARD_MAX_LINES, HARD_MAX_BYTES = 1000, 100 * 1024
SOFT_MAX_LINES, SOFT_MAX_BYTES = 300, 32 * 1024
ALLOWED_IMPORT_ROOTS = ("Mathlib", "Init", "Std", "Lean")
FORBIDDEN_IN_BLOCK = ("sorry", "admit", "axiom", "import", "native_decide", "implemented_by",
                      "extern", "unsafe", "opaque", "partial")

errors: list[str] = []
warnings: list[str] = []


def error(msg: str) -> None:
    errors.append(msg)


def strip_comments(text: str) -> str:
    """Remove Lean comments (`-- ...` and nested `/- ... -/`, including doc comments), keeping
    newlines so that line structure is preserved."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(text[i])
            i += 1
    if depth > 0:
        error("unterminated block comment")
    return "".join(out)


def split_file(path: Path) -> tuple[str, str, str] | None:
    """Split a file into (text before BEGIN, block from BEGIN to END inclusive, text after)."""
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    begins = [i for i, l in enumerate(lines) if l.rstrip("\n") == BEGIN]
    ends = [i for i, l in enumerate(lines) if l.rstrip("\n") == END]
    if len(begins) != 1 or len(ends) != 1 or begins[0] > ends[0]:
        error(f"{path.relative_to(ROOT)}: expected exactly one line '{BEGIN}' followed by exactly "
              f"one line '{END}' (found {len(begins)} and {len(ends)})")
        return None
    b, e = begins[0], ends[0]
    return "".join(lines[:b]), "".join(lines[b:e + 1]), "".join(lines[e + 1:])


def imports_of_prefix(path: Path, prefix: str) -> list[str]:
    """The modules imported before the block; anything else but comments is an error."""
    mods: list[str] = []
    for line in strip_comments(prefix).splitlines():
        s = line.strip()
        if not s:
            continue
        m = re.fullmatch(r"import\s+([\w.'«»]+(?:\s+[\w.'«»]+)*)", s)
        if m is None:
            error(f"{path.relative_to(ROOT)}: only comments and `import` commands may precede "
                  f"the synced block, found: {s!r}")
            continue
        mods.extend(m.group(1).split())
    return mods


def check_challenge_suffix(suffix: str) -> list[str]:
    """After the block, Challenge.lean may only contain `namespace`/`end` commands and theorem
    statements proved by `sorry`. Returns the names of the theorems."""
    theorems: list[str] = []
    chunks: list[list[str]] = []
    for line in strip_comments(suffix).splitlines():
        if not line.strip():
            continue
        if line[0].isspace():
            if not chunks:
                error(f"Challenge.lean: unexpected indented line after the block: {line!r}")
            else:
                chunks[-1].append(line.strip())
        else:
            chunks.append([line.strip()])
    for chunk in chunks:
        cmd = " ".join(chunk)
        if re.fullmatch(r"(namespace|end)\s+[\w.]+", cmd):
            continue
        m = re.fullmatch(r"theorem\s+([\w.']+)\s.*:=\s*sorry", cmd, flags=re.S)
        if m is None:
            error(f"Challenge.lean: after the synced block only `namespace`, `end` and "
                  f"`theorem ... := sorry` are allowed, found: {cmd[:120]!r}")
            continue
        theorems.append(m.group(1))
    if "four_color" not in theorems:
        error("Challenge.lean: the statement `theorem four_color ... := sorry` is missing")
    return theorems


def textual_check() -> list[str]:
    parts = {p: split_file(p) for p in (CHALLENGE, REALPLANE)}
    if any(v is None for v in parts.values()):
        return []
    (c_pre, c_block, c_suf), (r_pre, r_block, _) = parts[CHALLENGE], parts[REALPLANE]

    # 2. identical blocks
    if c_block != r_block:
        c_lines, r_lines = c_block.splitlines(), r_block.splitlines()
        for k, (a, b) in enumerate(zip(c_lines, r_lines)):
            if a != b:
                error("synced blocks differ; first difference at block line "
                      f"{k + 1}:\n  Challenge.lean:          {a!r}\n"
                      f"  FourColor/RealPlane.lean: {b!r}")
                break
        else:
            error(f"synced blocks differ in length ({len(c_lines)} vs {len(r_lines)} lines)")
    code = strip_comments(c_block)
    for word in FORBIDDEN_IN_BLOCK:
        if re.search(rf"(?<![\w.]){word}(?![\w'])", code):
            error(f"synced block contains the forbidden word `{word}`")

    # 3. identical imports, nothing else before the block
    c_imps, r_imps = imports_of_prefix(CHALLENGE, c_pre), imports_of_prefix(REALPLANE, r_pre)
    if c_imps != r_imps:
        error(f"import lists differ: Challenge.lean {c_imps} vs FourColor/RealPlane.lean {r_imps}")

    # 4. Challenge-specific rules
    for mod in c_imps:
        if mod.split(".")[0] not in ALLOWED_IMPORT_ROOTS:
            error(f"Challenge.lean imports `{mod}`, which is not a Lean core or Mathlib module")
    raw = CHALLENGE.read_bytes()
    n_lines, n_bytes = raw.count(b"\n") + (0 if raw.endswith(b"\n") else 1), len(raw)
    if n_lines > HARD_MAX_LINES or n_bytes > HARD_MAX_BYTES:
        error(f"Challenge.lean has {n_lines} lines / {n_bytes} bytes; the hard limit is "
              f"{HARD_MAX_LINES} lines / {HARD_MAX_BYTES} bytes")
    elif n_lines > SOFT_MAX_LINES or n_bytes > SOFT_MAX_BYTES:
        warnings.append(f"Challenge.lean has {n_lines} lines / {n_bytes} bytes; preferably at most "
                        f"{SOFT_MAX_LINES} lines / {SOFT_MAX_BYTES} bytes")
    theorems = check_challenge_suffix(c_suf)
    print(f"textual check: block of {len(c_block.splitlines())} lines, imports {c_imps}, "
          f"Challenge.lean {n_lines} lines / {n_bytes} bytes, statements {theorems}")
    return theorems


# ---------------------------------------------------------------------------------------------
# Kernel-level comparison

DUMP_TEMPLATE = r"""import MODULE
open Lean

partial def serExpr : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar id => s!"(fvar {id.name})"
  | .mvar id => s!"(mvar {id.name})"
  | .sort u => s!"(sort {u})"
  | .const n us => s!"(const {n} {us})"
  | .app f a => s!"(app {serExpr f} {serExpr a})"
  | .lam n t b bi => s!"(lam {n} {repr bi} {serExpr t} {serExpr b})"
  | .forallE n t b bi => s!"(pi {n} {repr bi} {serExpr t} {serExpr b})"
  | .letE n t v b nd => s!"(let {n} {nd} {serExpr t} {serExpr v} {serExpr b})"
  | .lit (.natVal k) => s!"(nat {k})"
  | .lit (.strVal s) => s!"(str {s.quote})"
  | .mdata m e => s!"(mdata {m} {serExpr e})"
  | .proj s i e => s!"(proj {s} {i} {serExpr e})"

def serHints : ReducibilityHints → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => s!"regular {h}"

def serSafety : DefinitionSafety → String
  | .unsafe => "unsafe"
  | .safe => "safe"
  | .partial => "partial"

def serConst : ConstantInfo → String
  | .axiomInfo v => s!"axiom {v.levelParams} {serExpr v.type} unsafe={v.isUnsafe}"
  | .defnInfo v => s!"def {v.levelParams} {serExpr v.type} := {serExpr v.value} " ++
      s!"hints={serHints v.hints} safety={serSafety v.safety} all={v.all}"
  | .thmInfo v => s!"theorem {v.levelParams} {serExpr v.type} := {serExpr v.value} all={v.all}"
  | .opaqueInfo v => s!"opaque {v.levelParams} {serExpr v.type} := {serExpr v.value} " ++
      s!"unsafe={v.isUnsafe} all={v.all}"
  | .quotInfo v => s!"quot {v.levelParams} {serExpr v.type}"
  | .inductInfo v => s!"inductive {v.levelParams} {serExpr v.type} params={v.numParams} " ++
      s!"indices={v.numIndices} all={v.all} ctors={v.ctors} nested={v.numNested} " ++
      s!"rec={v.isRec} unsafe={v.isUnsafe} reflexive={v.isReflexive}"
  | .ctorInfo v => s!"ctor {v.levelParams} {serExpr v.type} induct={v.induct} cidx={v.cidx} " ++
      s!"params={v.numParams} fields={v.numFields} unsafe={v.isUnsafe}"
  | .recInfo v => s!"rec {v.levelParams} {serExpr v.type} all={v.all} params={v.numParams} " ++
      s!"indices={v.numIndices} motives={v.numMotives} minors={v.numMinors} k={v.k} " ++
      s!"unsafe={v.isUnsafe} rules={v.rules.map fun r => s!"{r.ctor}/{r.nfields}/{serExpr r.rhs}"}"

/-- The constants that the comparator compares for the theorem statements `targets`
(mirrors `Comparator.compareAt` and `runForUsedConsts` of leanprover/comparator). -/
partial def closure (env : Environment) (targets : List Name) : Std.HashSet Name := Id.run do
  let mut work : Array Name := #[]
  for t in targets do
    if let some ci := env.find? t then work := work ++ ci.type.getUsedConstants
  let mut seen : Std.HashSet Name := {}
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut used := ci.type.getUsedConstants.push n
    if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
    match ci with
    | .inductInfo v => used := used ++ v.ctors.toArray ++ v.all.toArray
    | .ctorInfo v => used := used.push v.induct
    | .recInfo v =>
      for r in v.rules do used := (used.push r.ctor) ++ r.rhs.getUsedConstants
    | _ => pure ()
    for u in used do
      if !seen.contains u then work := work.push u
  return seen

#eval show CoreM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `MODULE | throwError "module MODULE is not loaded"
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      out := out.push s!"@@CONST@@\t{n}\t{serConst ci}"
  for n in closure env [TARGETS] do
    let owner := match env.getModuleIdxFor? n with
      | some i => toString env.header.moduleNames[i.toNat]!
      | none => "-"
    out := out.push s!"@@CLOSURE@@\t{n}\t{owner}"
  for l in out.qsort (· < ·) do
    IO.println l
"""


def run(cmd: list[str], env: dict[str, str], cwd: Path) -> str:
    proc = subprocess.run(cmd, env=env, cwd=cwd, capture_output=True, text=True, timeout=1500)
    if proc.returncode != 0:
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(cmd)}\n"
                           f"{proc.stdout[-4000:]}\n{proc.stderr[-4000:]}")
    return proc.stdout


def dump_constants(module: str, env: dict[str, str], tmp: Path,
                   targets: list[str]) -> tuple[dict[str, str], dict[str, str]]:
    """The constants defined by `module` (name -> serialization), and the comparator's
    dependency closure of the statements of `targets` (name -> defining module)."""
    dump_file = tmp / f"Dump_{module.replace('.', '_')}.lean"
    text = DUMP_TEMPLATE.replace("MODULE", module)
    text = text.replace("[TARGETS]", "[" + ", ".join(f"`{t}" for t in targets) + "]")
    dump_file.write_text(text, encoding="utf-8")
    out = run([env["LEAN"], dump_file.name], env, tmp)
    consts: dict[str, str] = {}
    closure: dict[str, str] = {}
    for line in out.splitlines():
        if line.startswith("@@CONST@@\t"):
            _, name, descr = line.split("\t", 2)
            consts[name] = descr
        elif line.startswith("@@CLOSURE@@\t"):
            _, name, owner = line.split("\t", 2)
            closure[name] = owner
    if not consts:
        raise RuntimeError(f"no constants found for module {module}:\n{out[-2000:]}")
    return consts, closure


def without_binder_names(descr: str) -> str:
    """Erase binder names, which `Expr.eqv` (used by the comparator) ignores."""
    return re.sub(r"\((lam|pi|let) \S+ ", r"(\1 _ ", descr)


def lean_check(theorems: list[str]) -> None:
    lake_env = json.loads(subprocess.run(
        ["lake", "env", sys.executable, "-c", "import json, os; print(json.dumps(dict(os.environ)))"],
        cwd=ROOT, capture_output=True, text=True, check=True, timeout=600).stdout)
    with tempfile.TemporaryDirectory(prefix="challenge_sync_") as tmp_name:
        tmp = Path(tmp_name)
        env = dict(lake_env)
        # the freshly compiled modules must shadow any stale `.olean` of the project
        env["LEAN_PATH"] = f"{tmp}:{lake_env['LEAN_PATH']}"
        (tmp / "FourColor").mkdir()
        run([env["LEAN"], "-DautoImplicit=false", "-Dpp.unicode.fun=true",
             "-o", str(tmp / "FourColor" / "RealPlane.olean"), "FourColor/RealPlane.lean"], env, ROOT)
        run([env["LEAN"], "-o", str(tmp / "Challenge.olean"), "Challenge.lean"], env, ROOT)
        targets = [f"FourColor.RealPlane.{t}" for t in theorems]
        r_consts, _ = dump_constants("FourColor.RealPlane", env, tmp, [])
        c_consts, closure = dump_constants("Challenge", env, tmp, targets)
    only_binder_names: list[str] = []
    for name, descr in sorted(r_consts.items()):
        if name not in c_consts:
            error(f"kernel check: `{name}` (FourColor.RealPlane) is missing from Challenge")
        elif c_consts[name] != descr:
            if without_binder_names(c_consts[name]) == without_binder_names(descr):
                only_binder_names.append(name)
            else:
                error(f"kernel check: `{name}` differs between FourColor.RealPlane and Challenge")
    extra = sorted(set(c_consts) - set(r_consts))
    for name in extra:
        if name not in targets:
            error(f"kernel check: Challenge defines `{name}`, which FourColor.RealPlane does not")
    local = sorted(n for n, owner in closure.items() if owner == "Challenge")
    for name in local:
        if name not in r_consts:
            error(f"kernel check: `{name}`, in the closure of the statement, is not defined "
                  f"by FourColor.RealPlane")
        elif name in only_binder_names:
            error(f"kernel check: `{name}`, in the closure of the statement, differs in binder "
                  f"names between FourColor.RealPlane and Challenge")
    print(f"kernel check: {len(r_consts)} constants of FourColor.RealPlane compared, "
          f"Challenge adds {extra}")
    print(f"kernel check: the comparator's closure of {targets} has {len(closure)} constants, "
          f"{len(local)} of them defined in Challenge:\n  " + " ".join(local))
    outside = [n for n in only_binder_names if n not in closure]
    if outside:
        print(f"note: {len(outside)} auto-generated constants outside the closure differ only in "
              f"(hygienic) binder names, which the comparator ignores: " + " ".join(outside))


def main() -> int:
    theorems = textual_check()
    if "--lean" in sys.argv[1:] and not errors:
        try:
            lean_check(theorems)
        except (RuntimeError, subprocess.SubprocessError, KeyError, OSError) as exc:
            error(f"kernel check could not run: {exc}")
    for w in warnings:
        print(f"WARNING: {w}")
    for e in errors:
        print(f"ERROR: {e}")
    print("OK: Challenge.lean and FourColor/RealPlane.lean are in sync" if not errors
          else f"FAILED with {len(errors)} error(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
