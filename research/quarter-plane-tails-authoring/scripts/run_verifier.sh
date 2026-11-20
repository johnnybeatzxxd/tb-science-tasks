#!/bin/bash
# usage: run_verifier.sh SUBMISSION_DIR LOGDIR   -> prints reward
set -euo pipefail
SUB=$(realpath "$1"); LOG=$(realpath -m "$2"); mkdir -p "$LOG"
T=/home/user/tb-science-tasks/tasks/mathematical-sciences/operations-research/quarter-plane-tails
docker run --rm --network none --cpus 4 -m 8g \
  -v "$T/tests":/tests:ro -v "$SUB":/root/qtails -v "$LOG":/logs/verifier \
  qpt-verifier bash /tests/test.sh > "$LOG/stdout.txt" 2>&1 || true
echo "reward=$(cat "$LOG/reward.txt" 2>/dev/null || echo missing)"
