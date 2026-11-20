"""Verifier for quarter-plane-tails.

Runs the submitted program /root/qtails/tails.py once on the held-out walks and compares
every (rho, kappa) pair with the reference values in expected.json.
Reward 1 iff every check passes.
"""
import json
import os
import shutil
import subprocess
import time
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
PROGRAM = Path("/root/qtails/tails.py")
HELDOUT = HERE / "heldout_walks.json"
EXPECTED = HERE / "expected.json"
WORK = Path("/tmp/qtails_verify")
TIME_LIMIT = 1800          # seconds of wall clock for the whole held-out file
RHO_RTOL = Fraction(1, 10 ** 9)
KEYS = ("x_boundary", "y_boundary", "x_marginal", "y_marginal")

_RUN = {}


def run_program():
    if "result" in _RUN:
        return _RUN["result"]
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    inp = WORK / "input.json"
    out = WORK / "output.json"
    shutil.copy(HELDOUT, inp)
    t0 = time.time()
    try:
        proc = subprocess.run(["python3", str(PROGRAM), str(inp), str(out)],
                              cwd=str(PROGRAM.parent), capture_output=True, text=True,
                              timeout=TIME_LIMIT, env=dict(os.environ, PYTHONHASHSEED="0"))
        status = ("ok", proc.returncode, proc.stdout[-4000:], proc.stderr[-4000:])
    except subprocess.TimeoutExpired:
        status = ("timeout", None, "", "")
    elapsed = time.time() - t0
    data = None
    if status[0] == "ok" and out.exists():
        try:
            data = json.loads(out.read_text())
        except Exception as exc:  # malformed output
            status = ("malformed", status[1], status[2], repr(exc))
    _RUN["result"] = (status, elapsed, data)
    return _RUN["result"]


def parse_rho(s):
    if not isinstance(s, str):
        raise ValueError("rho must be a string")
    digits = [c for c in s.lstrip("+-0.").split("e")[0].split("E")[0] if c.isdigit()]
    if len(digits) < 15:
        raise ValueError("rho needs at least 15 significant digits: %r" % s)
    return Fraction(s)


def parse_kappa(s):
    if not isinstance(s, str):
        raise ValueError("kappa must be a string")
    return Fraction(s.strip())


def test_program_present():
    assert PROGRAM.is_file(), "missing /root/qtails/tails.py"


def test_program_runs_in_time():
    status, elapsed, data = run_program()
    print("status", status[0], "returncode", status[1], "elapsed %.1f s" % elapsed)
    if status[3]:
        print("stderr tail:", status[3])
    assert status[0] == "ok", status[0]
    assert status[1] == 0, "non-zero exit status %r" % status[1]
    assert isinstance(data, dict), "output is not a JSON object"


EXP = json.loads(EXPECTED.read_text())


@pytest.mark.parametrize("wid", sorted(EXP))
def test_walk(wid):
    status, elapsed, data = run_program()
    assert isinstance(data, dict), "no usable output"
    assert wid in data, "walk %s missing from output" % wid
    got = data[wid]
    assert isinstance(got, dict)
    bad = []
    for key in KEYS:
        ref = EXP[wid][key]
        try:
            rho = parse_rho(got[key]["rho"])
            kap = parse_kappa(got[key]["kappa"])
        except Exception as exc:
            bad.append("%s: malformed entry (%s)" % (key, exc))
            continue
        rref = Fraction(ref["rho"])
        kref = Fraction(ref["kappa"])
        if kap != kref:
            bad.append("%s: kappa wrong" % key)
        if abs(rho - rref) > RHO_RTOL * rref:
            bad.append("%s: rho outside tolerance" % key)
    assert not bad, "; ".join(bad)
