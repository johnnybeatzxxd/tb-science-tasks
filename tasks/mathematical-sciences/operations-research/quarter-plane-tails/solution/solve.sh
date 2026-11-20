#!/bin/bash
# Reference solution: install the kernel-method solver as /root/qtails/tails.py and
# check it against the public examples.
set -euo pipefail
mkdir -p /root/qtails
cp /solution/qtails.py /root/qtails/tails.py
python3 /root/qtails/tails.py /root/examples.json /tmp/examples_out.json
python3 - <<'PY'
import json
from fractions import Fraction
got = json.load(open('/tmp/examples_out.json'))
ref = json.load(open('/root/examples_output.json'))
for wid, r in ref.items():
    for key, v in r.items():
        g = got[wid][key]
        assert Fraction(g['kappa']) == Fraction(v['kappa']), (wid, key)
        assert abs(Fraction(g['rho']) / Fraction(v['rho']) - 1) < Fraction(1, 10**12), (wid, key)
print('reference solver reproduces the', len(ref), 'public examples')
PY
