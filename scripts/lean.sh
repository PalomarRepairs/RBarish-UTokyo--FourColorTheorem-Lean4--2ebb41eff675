#!/usr/bin/env bash
# Run `lake env lean <args>` under a global limit on concurrent Lean processes
# (default 3 slots) and wait while free memory is low (Linux; used by build_reducibility.sh --direct
# and present_gen.py).
#   scripts/lean.sh FourColor/X.lean
#   scripts/lean.sh -o .lake/build/lib/lean/FourColor/X.olean -i .lake/build/lib/lean/FourColor/X.ilean FourColor/X.lean
SLOTS=${LEAN_SLOTS:-3}
MINFREE_MB=${LEAN_MINFREE_MB:-1800}
LOCKDIR=/tmp/fourcolor-lean-slots
mkdir -p "$LOCKDIR"
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")/.." || exit 1
while true; do
  avail=$(free -m | awk '/^Mem:/ {print $7}')
  if [ "${avail:-0}" -ge "$MINFREE_MB" ]; then
    for i in $(seq 1 "$SLOTS"); do
      exec {fd}>"$LOCKDIR/slot$i"
      if flock -n "$fd"; then
        lake env lean "$@"; rc=$?
        flock -u "$fd"; exec {fd}>&-
        exit $rc
      fi
      exec {fd}>&-
    done
  fi
  sleep 3
done
