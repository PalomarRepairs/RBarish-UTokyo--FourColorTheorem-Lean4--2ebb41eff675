#!/usr/bin/env bash
# Replay declarations with Palomar's three kernels: Lean's leanchecker, nanoda and con-ron.
#
#   scripts/palomar_check.sh [options] MODULE DECL...
#     -C DIR       run in the Lake project DIR (default: the current directory)
#     -o DIR       keep the export and the checkers' logs in DIR (default: a temporary
#                  directory, removed at the end)
#     -t SECONDS   time limit for each checker (default: none)
#     --csv FILE   append one row per step to FILE (created with a header if missing)
#     --jobs N     con-ron's worker count (default: con-ron's own, one per hardware thread up
#                  to 16, as on Palomar; use 1 on a small machine for memory-heavy exports)
#
# Palomar exports the submitted theorems with leanexport and replays the export with con-ron,
# nanoda and leanchecker; a rejection by any of them fails the submission. This script does the
# same for DECL... from MODULE (which must be built): it exports them, with everything they
# depend on and Palomar's fixed list of extra targets, then runs `leanchecker --silent
# --from-export`, `nanoda_bin` with Palomar's configuration, and `con-ron` with its default
# flags. It prints one line per step with its verdict, wall time and peak memory, and exits
# nonzero if any checker fails.
#
# The tools come from the toolchain's bin directory: $PALOMAR_TOOLCHAIN/bin if that variable is
# set, otherwise the directory that `lake env lean --print-prefix` reports. Lean v4.35.0-rc2 and
# later ship all four (leanexport, leanchecker, nanoda_bin, con-ron).
set -uo pipefail

usage() { sed -n '2,10p' "$0" | sed 's/^# \{0,1\}//' >&2; exit 2; }

DIR=. OUT= LIMIT= CSV= JOBS=
while [ $# -gt 0 ]; do
  case "$1" in
    -C) DIR=$2; shift 2 ;;
    -o) OUT=$2; shift 2 ;;
    -t) LIMIT=$2; shift 2 ;;
    --csv) CSV=$2; shift 2 ;;
    --jobs) JOBS=$2; shift 2 ;;
    -h|--help) usage ;;
    -*) echo "unknown option $1" >&2; usage ;;
    *) break ;;
  esac
done
[ $# -ge 2 ] || usage
MODULE=$1; shift
DECLS=("$@")

HERE=$(cd "$(dirname "$0")" && pwd)
MEMTIME="$HERE/engine_memtime.py"
[ -n "$CSV" ] && CSV=$(python3 -c 'import os, sys; print(os.path.abspath(sys.argv[1]))' "$CSV")
cd "$DIR" || exit 2

if [ -n "${PALOMAR_TOOLCHAIN:-}" ]; then
  BIN="$PALOMAR_TOOLCHAIN/bin"
else
  BIN="$(lake env lean --print-prefix)/bin" || exit 2
fi
for tool in leanexport leanchecker nanoda_bin con-ron; do
  [ -x "$BIN/$tool" ] || { echo "palomar_check: $BIN/$tool not found (Lean v4.35.0-rc2 or later ships it)" >&2; exit 2; }
done

if [ -z "$OUT" ]; then
  OUT=$(mktemp -d); trap 'rm -rf "$OUT"' EXIT
else
  mkdir -p "$OUT"
fi
OUT=$(cd "$OUT" && pwd)
EXPORT="$OUT/export.ndjson"

# Palomar's fixed export targets besides the theorem names (its pipeline at v4.35.0-rc2).
TARGETS=(Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor
  Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String
  String.mk Char optParam autoParam semiOutParam outParam)

cat > "$OUT/nanoda.json" <<EOF
{"use_stdin":false,"export_file_path":"$EXPORT","permitted_axioms":["propext","Quot.sound","Classical.choice"],"unpermitted_axiom_hard_error":false,"num_threads":4,"nat_extension":true,"string_extension":true}
EOF

if [ -n "$CSV" ] && [ ! -s "$CSV" ]; then
  echo "module,decls,step,rc,wall_s,cpu_s,maxrss_mb,export_mb" > "$CSV"
fi

FAILED=0
# run LABEL LOG CMD...: time CMD with its output in LOG, print a summary line, record it.
run() {
  local label=$1 log=$2; shift 2
  local tl=() line rc wall cpu rss
  [ -n "$LIMIT" ] && tl=(--timeout "$LIMIT")
  line=$(python3 "$MEMTIME" ${tl[@]+"${tl[@]}"} --label "$label" -- bash -c 'log=$1; shift; exec "$@" > "$log" 2>&1' _ "$log" "$@" | grep '^MEMTIME')
  rc=$(sed -n 's/.* rc=\([^ ]*\).*/\1/p' <<<"$line")
  wall=$(sed -n 's/.* wall=\([0-9.]*\)s.*/\1/p' <<<"$line")
  cpu=$(sed -n 's/.* cpu=\([0-9.]*\)s.*/\1/p' <<<"$line")
  rss=$(sed -n 's/.* maxrss=\([0-9.]*\)MB.*/\1/p' <<<"$line")
  local verdict=ok
  if [ "$rc" != 0 ]; then
    verdict="FAILED (rc=$rc)"; FAILED=1
  fi
  local emb
  emb=$(awk -v b="$(wc -c < "$EXPORT" 2>/dev/null | tr -d ' ')" 'BEGIN { printf "%.1f", (b + 0) / 1048576 }')
  printf '%-12s %-16s %9.2f s %9.0f MB   %s\n' "$label" "$verdict" "$wall" "$rss" \
    "$( [ "$rc" = 0 ] || tail -c 300 "$log" | tr '\n' ' ' )"
  if [ -n "$CSV" ]; then
    local IFS=';'
    echo "$MODULE,${DECLS[*]},$label,$rc,$wall,$cpu,$rss,$emb" >> "$CSV"
  fi
}

run leanexport "$OUT/leanexport.err" bash -c 'out=$1; shift; lake env "$@" > "$out.tmp" && mv "$out.tmp" "$out"' \
  _ "$EXPORT" "$BIN/leanexport" "$MODULE" -- "${TARGETS[@]}" "${DECLS[@]}"
if [ ! -s "$EXPORT" ]; then
  echo "palomar_check: the export failed; see $OUT/leanexport.err" >&2
  exit 1
fi
run leanchecker "$OUT/leanchecker.log" "$BIN/leanchecker" --silent --from-export "$EXPORT"
run nanoda "$OUT/nanoda.log" "$BIN/nanoda_bin" "$OUT/nanoda.json"
CONRON_FLAGS=()
[ -n "$JOBS" ] && CONRON_FLAGS=(--jobs="$JOBS")
run con-ron "$OUT/con-ron.log" "$BIN/con-ron" ${CONRON_FLAGS[@]+"${CONRON_FLAGS[@]}"} "$EXPORT"
exit $FAILED
