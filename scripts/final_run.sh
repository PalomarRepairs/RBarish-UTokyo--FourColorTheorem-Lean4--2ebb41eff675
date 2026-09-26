#!/usr/bin/env bash
# The final run of the Four Color Theorem port, in one command: build the 633 reducibility
# certificates and the final theorem, check its axioms, and rehearse Palomar's judging pipeline.
# It uploads nothing.
#
#   bash scripts/final_run.sh [options]
#
# Run it from the repository's folder: a git clone or an unzipped download. A
# download made by `git archive` carries its commit in the file .source-commit.
#
# Stages (each is timed; a stage that finished is skipped when the script is run again, so an
# interrupted run can simply be restarted):
#   environment   checks the tools and records the machine, the commit and the Lean version;
#   mathlib       downloads Mathlib's prebuilt files (`lake exe cache get`);
#   library       `lake build`: the whole library except the 633 certificates;
#   certificates  the 633 generated certificates FourColor/Reducibility/CfNNN.lean, J at a time,
#                 recording each one's time and memory (scripts/build_reducibility.sh build),
#                 then FourColor.Reducibility, which collates them;
#   final         `lake build FourColor.FourColorThm Solution`, `#print axioms` of the final
#                 theorem, and a scan for sorry / admit / native_decide;
#   palomar       Palomar's pipeline (scripts/palomar_dryrun.sh): repository checks, the
#                 exports, `lake comparator` with Lean's leanchecker, nanoda and con-ron, and the
#                 licence check;
#   summary       writes final-run-summary-<commit>.txt (one text file with every result)
#                 and final-run-results-<commit>.tar.gz (all the logs).
#
# Options:
#   -j N              certificates built at a time (default: from the CPU count and the memory,
#                     about 1.6 GB each)
#   --conron-jobs N   con-ron's worker count in the palomar stage (default: from the memory,
#                     about 2 GB each, at most 16 as on Palomar)
#   --no-palomar      skip the palomar stage (it takes the longest: Lean's checker is
#                     single-threaded)
#   --only STAGE      run only this stage (then the summary)
#   --redo            run the stages again even if they finished before
#   --plan            print the machine, the settings and the stages, and stop
#   -o DIR            results directory (default: final-run-results)
#
# Requirements: Linux (or WSL) or macOS; bash, git, curl, python3, and elan, the Lean toolchain
# manager, which installs the pinned Lean version by itself:
#   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# About 25 GB of free disk, and 16 GB of memory or more (32 GB is comfortable for the palomar
# stage). Expect roughly 1–2 hours for the builds on an 8-core machine, and 2–4 hours more for
# the palomar stage.
set -uo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/.." && pwd)
cd "$ROOT" || exit 2
export PATH="$HOME/.elan/bin:$PATH"

RES=final-run-results J= CJ= PALOMAR=1 ONLY= REDO=0 PLAN=0
while [ $# -gt 0 ]; do
  case "$1" in
    -j) J=$2; shift 2 ;;
    --conron-jobs) CJ=$2; shift 2 ;;
    --no-palomar) PALOMAR=0; shift ;;
    --only) ONLY=$2; shift 2 ;;
    --redo) REDO=1; shift ;;
    --plan) PLAN=1; shift ;;
    -o) RES=$2; shift 2 ;;
    -h|--help) sed -n '2,41p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "final_run: unknown option $1 (see --help)" >&2; exit 2 ;;
  esac
done
case "$ONLY" in
  ""|environment|mathlib|library|certificates|final|palomar|summary) ;;
  *) echo "final_run: unknown stage $ONLY" >&2; exit 2 ;;
esac

mkdir -p "$RES" || exit 2
RES=$(cd "$RES" && pwd)
exec > >(tee -a "$RES/final_run.log") 2>&1

# ------------------------------------------------------------------ machine and settings
OS=$(uname -s)
CORES=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)
if [ "$OS" = Darwin ]; then
  RAM_GB=$(( $(sysctl -n hw.memsize) / 1073741824 ))
  CPU_MODEL=$(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown)
else
  RAM_GB=$(awk '/^MemTotal:/ { printf "%d", $2 / 1048576 }' /proc/meminfo 2>/dev/null || echo 8)
  CPU_MODEL=$(awk -F': ' '/^model name/ { print $2; exit }' /proc/cpuinfo 2>/dev/null || echo unknown)
fi
DISK_GB=$(df -Pk . | awk 'NR == 2 { printf "%d", $4 / 1048576 }')
if [ -z "$J" ]; then
  J=$(( (RAM_GB - 3) * 10 / 16 ))
  [ "$J" -gt "$CORES" ] && J=$CORES
  [ "$J" -lt 1 ] && J=1
fi
if [ -z "$CJ" ]; then
  CJ=$(( (RAM_GB - 6) / 2 ))
  [ "$CJ" -gt "$CORES" ] && CJ=$CORES
  [ "$CJ" -gt 16 ] && CJ=16
  [ "$CJ" -lt 1 ] && CJ=1
fi
# The commit: from git in a clone, from .source-commit ("<sha> <branch>") in a downloaded copy.
TOP=$(git rev-parse --show-toplevel 2>/dev/null) && TOP=$(cd "$TOP" && pwd -P)
if [ -n "$TOP" ] && [ "$TOP" = "$(pwd -P)" ]; then
  GIT=1
  SHA=$(git rev-parse HEAD 2>/dev/null || echo unknown)
  BRANCH=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)
else
  GIT=0
  SHA=$(awk 'NR == 1 { print $1 }' .source-commit 2>/dev/null)
  BRANCH="$(awk 'NR == 1 { print $2 }' .source-commit 2>/dev/null) (downloaded copy, no git)"
  [ -n "$SHA" ] || SHA=unknown
fi
SHORT=${SHA:0:12}

echo "final_run: $(date)"
echo "  commit $SHA (branch $BRANCH)"
echo "  $OS, $CPU_MODEL, $CORES cores, $RAM_GB GB of memory, $DISK_GB GB of free disk"
echo "  certificates at a time: $J; con-ron workers: $CJ; palomar stage: $([ "$PALOMAR" = 1 ] && echo yes || echo no)"
echo "  results in $RES"
if [ "$PLAN" = 1 ]; then
  echo "stages: environment mathlib library certificates final $([ "$PALOMAR" = 1 ] && echo palomar) summary"
  for s in environment mathlib library certificates final palomar; do
    [ -f "$RES/.done.$s" ] && echo "  $s: done earlier"
  done
  exit 0
fi
[ "$DISK_GB" -lt 20 ] && echo "final_run: warning: only $DISK_GB GB of free disk (about 25 GB are needed)"
[ "$RAM_GB" -lt 12 ] && echo "final_run: warning: only $RAM_GB GB of memory; the certificates of ring size 14 take about 1.5 GB each, plus 3 GB shared"

# `version_at_least V MIN`: whether the dotted version V is at least MIN.
version_at_least() {
  [ -n "$1" ] && [ "$(printf '%s\n%s\n' "$2" "$1" | sort -t. -k1,1n -k2,2n -k3,3n | head -n 1)" = "$2" ]
}

# `timed LABEL LOG CMD…`: run CMD with its output in LOG; print and return its MEMTIME line.
timed() {
  local label=$1 log=$2; shift 2
  python3 "$ROOT/scripts/engine_memtime.py" --label "$label" -- bash -c \
    'log=$1; shift; exec "$@" > "$log" 2>&1' _ "$log" "$@" | tee -a "$RES/memtime.txt"
  return "${PIPESTATUS[0]}"
}

# ------------------------------------------------------------------ stages
st_environment() {
  local ok=1 t
  for t in git python3 bash; do
    command -v "$t" > /dev/null || { echo "missing: $t"; ok=0; }
  done
  if ! command -v lake > /dev/null; then
    echo "missing: lake. Install elan, the Lean toolchain manager, then run this script again:"
    echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    ok=0
  fi
  [ "$ok" = 1 ] || return 1
  # Lake fetches its packages with `git fetch --filter=…`, which Git 2.27 and older refuse in a
  # new repository ("--filter can only be used when extensions.partialClone is set"): Lake then
  # fails at once with "failed to fetch the package revision".
  if ! version_at_least "$(git --version | awk '{ print $3 }')" 2.28; then
    echo "Git $(git --version | awk '{ print $3 }') is too old: Lake needs Git 2.28 or newer to fetch Mathlib."
    echo "On Ubuntu, install a recent Git from the Git maintainers' PPA, then run this script again:"
    echo "  sudo add-apt-repository -y ppa:git-core/ppa && sudo apt update && sudo apt install -y git"
    echo "On other systems, update Git with the system's package manager."
    return 1
  fi
  [ -f lean-toolchain ] && [ -f Solution.lean ] && [ -f scripts/build_reducibility.sh ] || {
    echo "run this script from the repository's folder"; return 1; }
  if [ "$GIT" = 1 ] && [ -n "$(git status --porcelain --untracked-files=no 2>/dev/null)" ]; then
    echo "warning: the working tree has uncommitted changes (the results name commit $SHORT)"
  fi
  echo "installing or checking the toolchain $(cat lean-toolchain) (the first time, elan downloads it)"
  lake --version || return 1
  local prefix
  prefix=$(lean --print-prefix 2>/dev/null || lake env lean --print-prefix) || return 1
  {
    echo "date: $(date)"
    echo "commit: $SHA"
    echo "branch: $BRANCH"
    if [ "$GIT" = 1 ]; then
      echo "dirty: $(git status --porcelain --untracked-files=no | wc -l | tr -d ' ') changed tracked files"
    fi
    echo "os: $(uname -a)"
    echo "git: $(git --version | awk '{ print $3 }')"
    echo "cpu: $CPU_MODEL"
    echo "cores: $CORES"
    echo "memory_gb: $RAM_GB"
    echo "free_disk_gb: $DISK_GB"
    echo "jobs_certificates: $J"
    echo "jobs_conron: $CJ"
    echo "lean: $(lean --version 2>/dev/null || lake env lean --version)"
    echo "lake: $(lake --version)"
    echo "toolchain_prefix: $prefix"
    for t in leanexport leanchecker nanoda_bin con-ron; do
      if [ -x "$prefix/bin/$t" ]; then echo "tool_$t: yes"; else echo "tool_$t: MISSING"; fi
    done
    echo "bwrap: $(command -v bwrap || echo none)"
    echo "python: $(python3 --version 2>&1)"
  } | tee "$RES/environment.txt"
}

st_mathlib() {
  # `lake exe cache get` fetches the packages of lake-manifest.json and Mathlib's prebuilt
  # .olean files (without them, `lake build` would compile Mathlib: many hours).
  timed mathlib "$RES/mathlib.log" lake exe cache get
  local rc=$?
  tail -n 3 "$RES/mathlib.log"
  return $rc
}

st_library() {
  timed library "$RES/library.log" lake build
  local rc=$?
  tail -n 3 "$RES/library.log"
  return $rc
}

st_certificates() {
  local remaining n rc
  remaining=$(python3 - "$RES/timings.tsv" <<'PY'
import sys
done = set()
try:
    for line in open(sys.argv[1]):
        f = line.rstrip("\n").split("\t")
        if len(f) >= 3 and f[0].startswith("cf") and f[2] == "0":
            done.add(int(f[0][2:]))
except FileNotFoundError:
    pass
print(" ".join(str(i) for i in range(1, 634) if i not in done))
PY
)
  n=$(echo "$remaining" | wc -w | tr -d ' ')
  if [ "$n" -gt 0 ]; then
    echo "building $n certificates, $J at a time (per-module logs in $RES/logs)"
    bash scripts/build_reducibility.sh build -j "$J" --log "$RES/timings.tsv" --no-collate \
      --only "$remaining"
    rc=$?
    if [ "$rc" != 0 ]; then
      echo "some certificates failed:"
      awk -F'\t' 'NR > 1 && $3 != "0"' "$RES/timings.tsv" | tail -n 20
      return "$rc"
    fi
  fi
  timed collation "$RES/collation.log" lake build FourColor.Reducibility
}

st_final() {
  timed final "$RES/final.log" lake build FourColor.FourColorThm Solution || {
    tail -n 30 "$RES/final.log"; return 1; }
  cat > "$RES/Axioms.lean" <<'EOF'
import Solution
#print axioms FourColor.RealPlane.four_color
#print axioms FourColor.four_color_hypermap
#print axioms FourColor.theReducibility
EOF
  lake env lean "$RES/Axioms.lean" > "$RES/axioms.txt" 2>&1
  cat "$RES/axioms.txt"
  grep -rnw -E "sorry|admit|native_decide" --include='*.lean' FourColor FourColor.lean Solution.lean \
    > "$RES/scan.txt" 2>/dev/null
  echo "scan for sorry/admit/native_decide: $(wc -l < "$RES/scan.txt" | tr -d ' ') lines (expected 0)"
  local warn
  warn=$(cat "$RES"/library.log "$RES"/final.log "$RES"/collation.log "$RES"/logs/*.log 2>/dev/null \
    | grep -c "declaration uses 'sorry'")
  echo "\"declaration uses 'sorry'\" warnings in the build logs: $warn (expected 0)"
  grep -q "'FourColor.RealPlane.four_color' depends on axioms: \[propext, Classical.choice, Quot.sound\]" \
    "$RES/axioms.txt" || { echo "UNEXPECTED AXIOMS for FourColor.RealPlane.four_color"; return 1; }
  [ "$warn" = 0 ] && [ ! -s "$RES/scan.txt" ]
}

st_palomar() {
  local prefix t flags=()
  prefix=$(lake env lean --print-prefix) || return 1
  for t in leanexport leanchecker nanoda_bin con-ron; do
    if [ ! -x "$prefix/bin/$t" ]; then
      echo "this Lean toolchain has no $t, so Palomar's pipeline cannot be rehearsed on this"
      echo "machine (Palomar runs on Linux x86_64, whose toolchain ships all four checkers)."
      echo "skipping the palomar stage; the other results are complete"
      return 0
    fi
  done
  # Palomar runs the comparator in a bubblewrap sandbox (Linux only). Lake's comparator needs
  # bwrap 0.5 or newer (--clearenv) and unprivileged user namespaces; without them, run it
  # unsandboxed, which changes nothing in the verdicts or the times.
  if command -v bwrap > /dev/null \
    && version_at_least "$(bwrap --version 2>/dev/null | awk '{ print $2 }')" 0.5 \
    && bwrap --ro-bind / / --dev /dev --proc /proc --clearenv --unshare-all --die-with-parent \
         --new-session true > /dev/null 2>&1; then
    echo "running the comparator in the bubblewrap sandbox, as Palomar does"
  else
    echo "bubblewrap is missing, older than 0.5 or not permitted here: running the comparator unsandboxed"
    flags+=(--no-sandbox)
  fi
  bash scripts/palomar_dryrun.sh -o "$RES/palomar" --skip-build --jobs "$CJ" ${flags[@]+"${flags[@]}"}
}

st_summary() {
  python3 - "$RES" "$ROOT/final-run-summary-$SHORT.txt" <<'PY'
import os, re, sys
res, out = sys.argv[1], sys.argv[2]
L = []
def read(name):
    try:
        return open(os.path.join(res, name)).read()
    except OSError:
        return ""
def hms(s):
    s = int(float(s)); return f"{s // 3600}:{s % 3600 // 60:02d}:{s % 60:02d}"
L.append("FOUR COLOR THEOREM IN LEAN 4: FINAL RUN SUMMARY")
L.append("=" * 72)
L.append(read("environment.txt").rstrip())
L.append("")
L.append("STAGES (name, exit code, wall time)")
for line in read("stages.tsv").splitlines():
    f = line.split("\t")
    if len(f) == 3 and f[2].isdigit():
        L.append(f"  {f[0]:<14} rc={f[1]:<4} {hms(f[2])}")
L.append("")
L.append("TIMED COMMANDS (wall, CPU, peak memory of the command and its descendants)")
L.extend("  " + l for l in read("memtime.txt").splitlines())
rows = []
for line in read("timings.tsv").splitlines()[1:]:
    f = line.split("\t")
    if len(f) == 8:
        rows.append(f)
if rows:
    ok = [r for r in rows if r[2] == "0"]
    bad = [r for r in rows if r[2] != "0"]
    L.append("")
    L.append(f"CERTIFICATES: {len(set(r[0] for r in ok))} of 633 built; {len(bad)} failed rows")
    L.append("  ring  count   wall_s    cpu_s  max_wall_s (cf)   max_rss_MB (cf)   max_anon_MB (cf)  olean_MB")
    rings = sorted(set(int(r[1]) for r in ok))
    for g in rings:
        rr = [r for r in ok if int(r[1]) == g]
        mw = max(rr, key=lambda r: float(r[3])); mr = max(rr, key=lambda r: float(r[5]))
        ma = max(rr, key=lambda r: float(r[6]))
        L.append(f"  {g:>4} {len(rr):>6} {sum(float(r[3]) for r in rr):>8.0f} "
                 f"{sum(float(r[4]) for r in rr):>8.0f}  {float(mw[3]):>7.1f} ({mw[0]})  "
                 f"{float(mr[5]):>7.0f} ({mr[0]})  {float(ma[6]):>7.0f} ({ma[0]})  "
                 f"{sum(int(r[7]) for r in rr) / 1e6:>7.1f}")
    L.append(f"  total {len(ok):>5} {sum(float(r[3]) for r in ok):>8.0f} "
             f"{sum(float(r[4]) for r in ok):>8.0f}")
    L.append("  slowest: " + ", ".join(f"{r[0]} {float(r[3]):.0f}s" for r in
                                       sorted(ok, key=lambda r: -float(r[3]))[:10]))
    if bad:
        L.append("  FAILED: " + ", ".join(f"{r[0]} rc={r[2]}" for r in bad))
ax = read("axioms.txt")
if ax:
    L.append("")
    L.append("AXIOMS")
    L.extend("  " + l for l in ax.splitlines())
    scan = read("scan.txt")
    L.append(f"  scan for sorry/admit/native_decide: {len(scan.splitlines())} lines")
    L.extend("    " + l for l in scan.splitlines()[:20])
ph = read("palomar/phases.tsv")
if ph:
    L.append("")
    L.append("PALOMAR REHEARSAL (scripts/palomar_dryrun.sh; phase, rc, wall_s, cpu_s, maxrss_MB, note)")
    L.extend("  " + l.replace("\t", "  ") for l in ph.splitlines())
    for name in ("challenge.export", "solution.export"):
        p = os.path.join(res, "palomar", name)
        if os.path.exists(p):
            L.append(f"  {name}: {os.path.getsize(p) / 2**20:.1f} MB")
    cmp_log = read("palomar/comparator.log")
    if cmp_log:
        L.append("  comparator (time-stamped):")
        L.extend("    " + l for l in cmp_log.splitlines()
                 if re.search(r"kernel|okay|rror|reject|mismatch|axiom", l))
    for name in ("repo-checks.log", "licensee.log"):
        t = read(os.path.join("palomar", name))
        if t:
            L.append(f"  {name}:")
            L.extend("    " + l for l in t.splitlines()[-30:])
if rows:
    L.append("")
    L.append("APPENDIX: timings.tsv (cf, ring, rc, wall_s, cpu_s, maxrss_MB, anon_MB, olean_bytes)")
    L.extend(read("timings.tsv").splitlines())
open(out, "w").write("\n".join(L) + "\n")
print(f"summary: {out}")
PY
  tar -czf "$ROOT/final-run-results-$SHORT.tar.gz" --exclude='*.export' --exclude='*.olean' \
    --exclude='*.ilean' -C "$(dirname "$RES")" "$(basename "$RES")" \
    && echo "all logs: $ROOT/final-run-results-$SHORT.tar.gz"
}

# `stage NAME`: run st_NAME unless it finished before (or another stage was asked for).
stage() {
  local name=$1 start end rc
  if [ -n "$ONLY" ] && [ "$ONLY" != "$name" ]; then return 0; fi
  if [ -f "$RES/.done.$name" ] && [ "$REDO" = 0 ]; then
    echo "== $name: finished in an earlier run (--redo to run it again)"; return 0
  fi
  echo "== $name: started $(date)"
  start=$(date +%s)
  "st_$name"; rc=$?
  end=$(date +%s)
  printf '%s\t%s\t%s\n' "$name" "$rc" "$((end - start))" >> "$RES/stages.tsv"
  if [ "$rc" = 0 ]; then
    touch "$RES/.done.$name"
    echo "== $name: ok ($((end - start)) s)"
  else
    echo "== $name: FAILED (exit $rc after $((end - start)) s); logs in $RES"
    st_summary
    echo "Results so far: final-run-summary-$SHORT.txt; all the logs: $RES."
    exit "$rc"
  fi
}

stage environment
stage mathlib
stage library
stage certificates
stage final
[ "$PALOMAR" = 1 ] && stage palomar
st_summary
echo "final_run: finished $(date). Results: final-run-summary-$SHORT.txt; all the logs:"
echo "final-run-results-$SHORT.tar.gz."
