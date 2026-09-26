#!/usr/bin/env bash
# Rehearse Palomar's judging pipeline on this repository, locally.
#
#   scripts/palomar_dryrun.sh [options]
#     -o DIR           keep the exports, logs and the phase table in DIR
#                      (default: .lake/palomar-dryrun)
#     --jobs N         run con-ron with --jobs=N inside the comparator (default: con-ron's own
#                      worker count, as on Palomar; use 1 on a machine with little memory)
#     --skip-build     do not run `lake build Solution` (it must be built already)
#     --skip-comparator  stop after the exports (the kernels are the slow part)
#     --no-sandbox     run `lake comparator --inadvisably-no-sandbox` (needed where bubblewrap
#                      is not installed; Palomar runs the comparator in its bubblewrap sandbox)
#
# The phases follow PalomarSubmission's scripts/verify_submission.py (`prepare`, `execute`):
#   1. repository checks: comparator.json, formalization.yaml, the single root licence file,
#      Challenge.lean's limits and imports, no committed build products, no submodules or LFS,
#      Lake packages pinned to full commit SHAs, the checkout size, check_challenge_sync.py;
#   2. Challenge.lean compiled on its own (`lean -o`, without the lakefile's options) and
#      `lake build Challenge`;
#   3. `lake build Solution` (the candidate build: here it is incremental unless the build
#      directory was cleaned, so its time is not Palomar's);
#   4. `leanexport Challenge` and `leanexport Solution` with Palomar's export targets
#      (Quot, Quot.mk, Quot.lift, Quot.ind, the theorem names, the permitted axioms, and the
#      kernel's primitive constants read from the toolchain's Lake/CLI/Check.lean);
#   5. `lake comparator --config <comparator.json + external_kernels nanoda, con-ron>
#      --challenge-from-export … --solution-from-export …`, which compares the statements and
#      runs con-ron, nanoda and Lean's leanchecker on the solution export;
#   6. the licence check with Licensee 10.0.0 if the `licensee` gem is installed.
# Every phase is timed (wall, CPU, peak memory) into DIR/phases.tsv; the comparator's log is
# time-stamped so that each kernel's time can be read from it (DIR/comparator.log).
set -uo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/.." && pwd)
MEMTIME="$HERE/engine_memtime.py"
OUT=$ROOT/.lake/palomar-dryrun JOBS= SKIP_BUILD=0 SKIP_CMP=0 NOSANDBOX=0
while [ $# -gt 0 ]; do
  case "$1" in
    -o) OUT=$2; shift 2 ;;
    --jobs) JOBS=$2; shift 2 ;;
    --skip-build) SKIP_BUILD=1; shift ;;
    --skip-comparator) SKIP_CMP=1; shift ;;
    --no-sandbox) NOSANDBOX=1; shift ;;
    -h|--help) sed -n '2,31p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "palomar_dryrun: unknown option $1" >&2; exit 2 ;;
  esac
done
cd "$ROOT" || exit 2
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
PHASES=$OUT/phases.tsv
printf 'phase\trc\twall_s\tcpu_s\tmaxrss_MB\tnote\n' > "$PHASES"
START=$(date +%s)
FAILED=0

PREFIX=$(lake env lean --print-prefix) || exit 2
BIN=$PREFIX/bin
for tool in lake lean leanexport leanchecker nanoda_bin con-ron; do
  [ -x "$BIN/$tool" ] || { echo "palomar_dryrun: $BIN/$tool is missing" >&2; exit 2; }
done

# phase NAME NOTE CMD...: run CMD with its output in $OUT/NAME.log, timed; record and print.
phase() {
  local name=$1 note=$2; shift 2
  local line rc wall cpu rss
  line=$(python3 "$MEMTIME" --label "$name" -- bash -c 'log=$1; shift; exec "$@" > "$log" 2>&1' \
    _ "$OUT/$name.log" "$@" | grep '^MEMTIME')
  rc=$(sed -n 's/.* rc=\([^ ]*\).*/\1/p' <<<"$line")
  wall=$(sed -n 's/.* wall=\([0-9.]*\)s.*/\1/p' <<<"$line")
  cpu=$(sed -n 's/.* cpu=\([0-9.]*\)s.*/\1/p' <<<"$line")
  rss=$(sed -n 's/.* maxrss=\([0-9.]*\)MB.*/\1/p' <<<"$line")
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$rc" "$wall" "$cpu" "$rss" "$note" >> "$PHASES"
  local verdict=ok
  [ "$rc" = 0 ] || { verdict="FAILED (rc=$rc)"; FAILED=1; }
  printf '%-22s %-16s %10.1f s wall %10.1f s cpu %8.0f MB   %s\n' "$name" "$verdict" "$wall" \
    "$cpu" "$rss" "$note"
  [ "$rc" = 0 ] || tail -n 20 "$OUT/$name.log" | sed 's/^/    | /'
  return "$rc"
}

# ---------------------------------------------------------------- 1. repository checks
cat > "$OUT/repo_checks.py" <<'PY'
import json, os, re, subprocess, sys
from pathlib import Path
root = Path(sys.argv[1]); ok = True
def check(cond, msg):
    global ok
    print(("ok    " if cond else "FAIL  ") + msg); ok = ok and cond
cfg = json.loads((root / "comparator.json").read_text())
check(set(cfg) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"},
      f"comparator.json has exactly the four keys: {sorted(cfg)}")
check(cfg.get("challenge_module") == "Challenge" and cfg.get("solution_module") == "Solution"
      and cfg.get("theorem_names") == ["FourColor.RealPlane.four_color"]
      and sorted(cfg.get("permitted_axioms", [])) == ["Classical.choice", "Quot.sound", "propext"],
      "comparator.json values")
check((root / "formalization.yaml").is_file(), "formalization.yaml exists")
lic = [p.name for p in root.iterdir()
       if re.fullmatch(r"(?i)(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?", p.name)]
check(lic == ["LICENSE"], f"exactly one root licence file: {lic}")
ch = (root / "Challenge.lean").read_text()
check(len(ch.splitlines()) <= 300 and len(ch.encode()) <= 32 * 1024,
      f"Challenge.lean within 300 lines / 32 KiB ({len(ch.splitlines())} lines, {len(ch.encode())} bytes)")
check(not re.search(r"^\s*private\b", ch, re.M), "Challenge.lean has no private declaration")
imps = re.findall(r"^import\s+(\S+)", ch, re.M)
check(all(i.split(".")[0] in ("Mathlib", "Init", "Std", "Lean") for i in imps),
      f"Challenge.lean imports only Lean/Mathlib: {imps}")
top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=root, capture_output=True,
                     text=True).stdout.strip()
git = bool(top) and os.path.realpath(top) == os.path.realpath(root)
if git:
    files = subprocess.run(["git", "ls-files"], cwd=root, capture_output=True, text=True).stdout.split()
else:  # a downloaded copy: every file but the build and the results
    skip = {".lake", ".git", "final-run-results"}
    files = []
    for d, dirs, fs in os.walk(root):
        dirs[:] = [x for x in dirs if not (d == str(root) and x in skip)]
        files += [os.path.relpath(os.path.join(d, f), root) for f in fs
                  if not f.startswith("final-run-")]
bad = [f for f in files if re.search(r"\.(olean|ilean|o|a|so|dylib|dll|obj|ir|bc|trace)$", f)
       or f.endswith((".olean.private", ".olean.server"))]
check(not bad, f"no committed build products ({len(bad)} found)")
check(not (root / ".gitmodules").exists(), "no submodules")
ga = root / ".gitattributes"
check(not (ga.exists() and "filter=lfs" in ga.read_text()), "no Git LFS files")
size = sum((root / f).stat().st_size for f in files if (root / f).is_file())
pack = subprocess.run(["git", "count-objects", "-v"], cwd=root, capture_output=True,
                      text=True).stdout if git else ""
packkb = sum(int(l.split()[1]) for l in pack.splitlines() if l.startswith(("size:", "size-pack:")))
check(size + packkb * 1024 <= 500 * 1024 * 1024,
      f"checkout {size / 2**20:.1f} MiB of tracked files + {packkb / 1024:.1f} MiB of .git objects (cap 500 MiB)")
man = json.loads((root / "lake-manifest.json").read_text())
for p in man["packages"]:
    check(bool(re.fullmatch(r"[0-9a-f]{40}", p.get("rev", ""))) and
          p.get("url", "").startswith("https://github.com/"),
          f"package {p['name']} pinned to {p.get('rev', '')[:12]} on {p.get('url')}")
mathlib = [p for p in man["packages"] if p["name"] == "mathlib"]
check(bool(mathlib) and mathlib[0].get("inputRev") == "v4.35.0-rc2", "Mathlib at tag v4.35.0-rc2")
tc = (root / "lean-toolchain").read_text().strip()
check(tc == "leanprover/lean4:v4.35.0-rc2", f"lean-toolchain {tc}")
sys.exit(0 if ok else 1)
PY
phase repo-checks "see repo-checks.log" python3 "$OUT/repo_checks.py" "$ROOT"
cat "$OUT/repo-checks.log"
phase challenge-sync "check_challenge_sync.py --lean" python3 scripts/check_challenge_sync.py --lean

# ---------------------------------------------------------------- 2. the challenge
mkdir -p "$OUT/challenge-bare"
phase challenge-bare "lean -o, no lakefile options" \
  lake env lean -o "$OUT/challenge-bare/Challenge.olean" Challenge.lean
phase challenge-build "lake build Challenge" lake build Challenge

# ---------------------------------------------------------------- 3. the solution build
if [ "$SKIP_BUILD" = 0 ]; then
  phase solution-build "lake build Solution (incremental here)" lake build Solution \
    || { echo "palomar_dryrun: the Solution build failed" >&2; exit 1; }
fi

# ---------------------------------------------------------------- 4. the exports
# Palomar's targets: comparator_export_targets in verify_submission.py, with the primitive
# constants read from the toolchain's Lake/CLI/Check.lean (primitive_targets).
PRIMS=()
while IFS= read -r name; do PRIMS+=("$name"); done < <(python3 - "$PREFIX/src/lean/lake/Lake/CLI/Check.lean" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
m = re.search(r"^def primitiveTargets[^\n]*\n(?P<body>.*?)^def ", text, re.M | re.S)
body = re.sub(r"/-.*?-/", "", m.group("body"), flags=re.S)
body = "\n".join(l.split("--", 1)[0] for l in body.splitlines())
for name in re.findall(r"``([A-Za-z0-9_.]+)", body):
    print(name)
PY
)
[ "${#PRIMS[@]}" -gt 10 ] || { echo "palomar_dryrun: could not read primitiveTargets" >&2; exit 2; }
TARGETS=(Quot Quot.mk Quot.lift Quot.ind FourColor.RealPlane.four_color propext Quot.sound
  Classical.choice "${PRIMS[@]}")
printf '%s\n' "${TARGETS[@]}" > "$OUT/export-targets.txt"
export BIN
TARGETS_STR="${TARGETS[*]}"
phase challenge-export "leanexport Challenge" bash -c \
  'TARGETS=($1); lake env "$BIN/leanexport" Challenge -- "${TARGETS[@]}" > "$2.tmp" && mv "$2.tmp" "$2"' \
  _ "$TARGETS_STR" "$OUT/challenge.export"
phase solution-export "leanexport Solution" bash -c \
  'TARGETS=($1); lake env "$BIN/leanexport" Solution -- "${TARGETS[@]}" > "$2.tmp" && mv "$2.tmp" "$2"' \
  _ "$TARGETS_STR" "$OUT/solution.export"
ls -l "$OUT/challenge.export" "$OUT/solution.export" | awk '{printf "  %s: %.1f MB\n", $9, $5 / 1048576}'

# ---------------------------------------------------------------- 5. the comparator
if [ "$SKIP_CMP" = 0 ] && [ "$FAILED" = 0 ]; then
  CONRON=("$BIN/con-ron")
  [ -n "$JOBS" ] && CONRON+=("--jobs=$JOBS")
  python3 - "$ROOT/comparator.json" "$OUT/comparator-dryrun.json" "$BIN/nanoda_bin" "${CONRON[@]}" <<'PY'
import json, sys
cfg = json.load(open(sys.argv[1]))
cfg["external_kernels"] = {"nanoda": [sys.argv[3]], "con-ron": sys.argv[4:]}
json.dump(cfg, open(sys.argv[2], "w"), indent=2)
PY
  SANDBOX=()
  [ "$NOSANDBOX" = 1 ] && SANDBOX=(--inadvisably-no-sandbox)
  # Time-stamp the comparator's output so that each kernel's time can be read from the log.
  phase comparator "con-ron, nanoda, leanchecker; see comparator.log" bash -c \
    'lake comparator "$@" 2>&1 | python3 -u -c "
import sys, time
t0 = time.time()
for line in sys.stdin:
    sys.stdout.write(\"[%9.1f s] %s\" % (time.time() - t0, line)); sys.stdout.flush()
"; exit ${PIPESTATUS[0]}' _ ${SANDBOX[@]+"${SANDBOX[@]}"} --config "$OUT/comparator-dryrun.json" \
    --challenge-from-export "$OUT/challenge.export" --solution-from-export "$OUT/solution.export"
  grep -E "kernel|okay|rror" "$OUT/comparator.log" | sed 's/^/  /'
fi

# ---------------------------------------------------------------- 6. the licence
# Palomar's detector (PalomarSubmission scripts/detect_license.rb, Licensee 10.0.0 at a 98%
# confidence threshold, on the single root licence file).
if ruby -e 'gem "licensee", "10.0.0"; require "licensee"' 2>/dev/null; then
  cat > "$OUT/detect_license.rb" <<'RB'
# frozen_string_literal: true
require "json"
gem "licensee", "10.0.0"
require "licensee"
Licensee.confidence_threshold = 98
project = Licensee.project(ARGV.fetch(0), detect_packages: false, detect_readme: false,
                           filesystem: true)
matched_files = project.matched_files.select { |matched_file| matched_file.directory == "." }
licenses = matched_files.map(&:license).compact.uniq
puts JSON.generate(
  licenses: licenses.map { |license| { spdx_id: license.spdx_id } },
  matched_files: matched_files.map { |f| { matched_license: f.matched_license, confidence: f.confidence } }
)
RB
  phase licensee "Licensee 10.0.0 on LICENSE" ruby "$OUT/detect_license.rb" "$ROOT/LICENSE"
  python3 - "$OUT/licensee.log" "$ROOT/formalization.yaml" <<'PY2'
import json, re, sys
r = json.loads(open(sys.argv[1]).read().strip().splitlines()[-1])
ids = [l.get("spdx_id") for l in r.get("licenses", [])]
declared = re.search(r'^\s*license:\s*"?([^"\n]+)"?', open(sys.argv[2]).read(), re.M).group(1).strip()
print(f"  licensee: {ids} {r.get('matched_files')}; formalization.yaml project.license: {declared}")
print("  licence check:", "ok" if ids == [declared] else "MISMATCH")
PY2
else
  echo "Licensee 10.0.0 is not installed (gem install licensee -v 10.0.0); licence check skipped"
fi

END=$(date +%s)
echo "total wall time: $((END - START)) s; phases in $PHASES"
exit $FAILED
