#!/bin/bash
set -euo pipefail
mkdir -p /logs/verifier
echo 0 > /logs/verifier/reward.txt
chmod 700 /logs/verifier
chmod -R go-rwx /tests
cd /root
status=0
pytest --ctrf /logs/verifier/ctrf.json -p no:cacheprovider /tests/test_outputs.py -rA || status=$?
if [ "$status" -eq 0 ]; then
    echo 1 > /logs/verifier/reward.txt
else
    echo 0 > /logs/verifier/reward.txt
fi
