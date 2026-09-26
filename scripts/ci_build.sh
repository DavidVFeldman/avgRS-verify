#!/usr/bin/env bash
# Build one Lake target group, and leave behind enough to diagnose a failure.
#
#   scripts/ci_build.sh <label> <lake target> [<lake target> ...]
#
# Writes build-<label>.log, reports wall time and peak resident memory, and on
# failure prints the tail of the log, the lines Lean or Lake marked as errors,
# any OOM-killer message, and the state of memory and disk.  Exits with lake's
# status.

set -uo pipefail

label="$1"; shift
log="build-${label}.log"
mem="mem-${label}.txt"
: > "$mem"

echo "--- ${label}: lake build $*"
start=$(date +%s)

# Memory, sampled every 5 s into mem-<label>.txt and reported to stdout every
# 30 s.  The heartbeat goes to the step log rather than only to the file because
# when the runner host itself dies the artifact upload does not run, and the
# step log is then the only surviving evidence of how much memory was in use.
( t=0
  while sleep 5; do
    ps -eo rss= | awk '{s+=$1} END {print s}' >> "$mem"
    t=$(( t + 5 ))
    if [ $(( t % 30 )) -eq 0 ]; then
      state=$(free -m | awk '/^Mem:/ {printf "used %s MiB, available %s MiB", $3, $7}
                             /^Swap:/ {printf ", swap %s of %s MiB", $3, $2}')
      big=$(ps -eo rss=,comm= --sort=-rss 2> /dev/null | head -1 \
            | awk '{printf "%s at %d MiB", $2, $1 / 1024}')
      echo "--- mem ${label} t=${t}s: ${state}; largest process ${big}"
    fi
  done ) &
sampler=$!

if command -v /usr/bin/time > /dev/null 2>&1; then
  /usr/bin/time -v lake build "$@" 2>&1 | tee "$log"
else
  lake build "$@" 2>&1 | tee "$log"
fi
status=${PIPESTATUS[0]}

kill "$sampler" 2> /dev/null || true
wall=$(( $(date +%s) - start ))

echo "--- ${label}: exit ${status}, ${wall} s wall"
grep -E "Maximum resident set size" "$log" || true
peak=$(sort -n "$mem" 2> /dev/null | tail -1)
total=$(free -m | awk '/^Mem:/ {print $2}')
if [ -n "${peak:-}" ]; then
  echo "--- ${label}: peak resident memory, all processes: $(( peak / 1024 )) MiB of ${total} MiB"
fi

if [ "$status" -ne 0 ]; then
  echo "=== last 200 lines of ${log}"
  tail -200 "$log"
  echo "=== lines Lean or Lake marked as failures"
  grep -nE "^✖|^error|error:|deep recursion|stack overflow|maximum recursion" "$log" | head -40 \
    || echo "none — the build died without printing a diagnostic, which points at the kernel, not at Lean"
  echo "=== OOM killer"
  { sudo dmesg 2> /dev/null || dmesg 2> /dev/null || true; } \
    | grep -iE "out of memory|oom-kill|killed process" | tail -20 || echo "no OOM messages"
  echo "=== memory, disk, build tree"
  free -m
  swapon --show || true
  df -h / /mnt 2> /dev/null || df -h /
  du -sh .lake 2> /dev/null || true
  echo "=== exit code note"
  case "$status" in
    143) echo "143 = SIGTERM: the runner host went away. Read the memory heartbeat above" \
              "before treating it as transient — a host reclaimed after memory exhaustion" \
              "reports a shutdown signal, not 137." ;;
    137) echo "137 = killed by SIGKILL: the OOM killer, or the runner ran out of disk" ;;
    139) echo "139 = segmentation fault: stack, most likely" ;;
    134) echo "134 = abort" ;;
    *)   echo "${status}: an ordinary failure, so the diagnostic above should name the file" ;;
  esac
fi

exit "$status"
