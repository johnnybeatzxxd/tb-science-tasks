#!/bin/bash
# Install the formal proof (Fan lemma, labelling, extraction, Goal) into the project and build it.
set -euo pipefail
cp /solution/Zigzag/FanLabels.lean /app/Zigzag/FanLabels.lean
cp /solution/Zigzag/FanTucker.lean /app/Zigzag/FanTucker.lean
cp /solution/Zigzag/FanStep.lean /app/Zigzag/FanStep.lean
cp /solution/Zigzag/Lab.lean /app/Zigzag/Lab.lean
cp /solution/Zigzag/Extract.lean /app/Zigzag/Extract.lean
cp /solution/Zigzag/Main.lean /app/Zigzag/Main.lean
cp /solution/Zigzag/Goal.lean /app/Zigzag/Goal.lean
cd /app
lake build Zigzag
