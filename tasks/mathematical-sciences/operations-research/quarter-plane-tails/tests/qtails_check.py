"""Checking logic for quarter-plane-tails, shared by test_outputs.py and the provenance controls.

Pure functions only: strict JSON parsing of the program output and comparison with the
reference values. No file access to agent-controlled paths happens here.
"""
import json
from fractions import Fraction

KEYS = ("x_boundary", "y_boundary", "x_marginal", "y_marginal")
# rho is an algebraic number of degree <= 6; double-precision implementations of the exact
# characterisation reach about 1e-14 relative error, so 1e-9 leaves a margin of 10^4-10^5.
RHO_RTOL = Fraction(1, 10 ** 9)
# 15 significant digits are needed so that a reported value can carry relative accuracy 1e-9
# with a margin; double precision gives 15-17.
MIN_SIG_DIGITS = 15
MAX_OUTPUT_BYTES = 1_000_000


class StrictJSONError(ValueError):
    pass


def _no_dupes(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise StrictJSONError("duplicate key %r" % k)
        out[k] = v
    return out


def _bad_constant(name):
    raise StrictJSONError("non-finite constant %s" % name)


def parse_strict(raw: bytes):
    if len(raw) > MAX_OUTPUT_BYTES:
        raise StrictJSONError("output larger than %d bytes" % MAX_OUTPUT_BYTES)
    text = raw.decode("utf-8")
    return json.loads(text, object_pairs_hook=_no_dupes, parse_constant=_bad_constant)


def sig_digits(s: str) -> int:
    mant = s.strip().lstrip("+-").split("e")[0].split("E")[0]
    digits = mant.replace(".", "").lstrip("0")
    return len(digits)


def parse_rho(v):
    if not isinstance(v, str) or isinstance(v, bool):
        raise ValueError("rho is not a string")
    if sig_digits(v) < MIN_SIG_DIGITS:
        raise ValueError("rho has fewer than %d significant digits" % MIN_SIG_DIGITS)
    f = Fraction(v.strip())
    if not (0 < f < 1):
        raise ValueError("rho outside (0, 1)")
    return f


def parse_kappa(v):
    if not isinstance(v, str) or isinstance(v, bool):
        raise ValueError("kappa is not a string")
    return Fraction(v.strip())


def check_structure(data, ids):
    """returns a list of structural problems of the whole output object."""
    probs = []
    if not isinstance(data, dict):
        return ["output is not a JSON object"]
    extra = sorted(set(data) - set(ids))
    if extra:
        probs.append("output contains ids that are not in the input: %s" % extra[:5])
    return probs


def judge_walk(data, wid, ref):
    """per-walk verdict: (ok, problems, record) where record holds the intermediates."""
    probs, rec = [], {}
    if not isinstance(data, dict) or wid not in data:
        return False, ["walk %s missing from the output" % wid], {"present": False}
    got = data[wid]
    if not isinstance(got, dict) or set(got) != set(KEYS):
        return False, ["walk %s: value must be an object with exactly the keys %s" % (wid, list(KEYS))], {"present": True}
    rec["present"] = True
    for key in KEYS:
        ent = got[key]
        r = {"rho": None, "kappa": None, "rho_rel_error": None, "rho_ok": False, "kappa_ok": False}
        if not isinstance(ent, dict) or set(ent) != {"rho", "kappa"}:
            probs.append("%s.%s: must be an object with exactly the keys rho and kappa" % (wid, key))
            rec[key] = r
            continue
        r["rho"], r["kappa"] = ent["rho"], ent["kappa"]
        try:
            rho = parse_rho(ent["rho"])
        except Exception as exc:
            probs.append("%s.%s.rho: malformed (%s)" % (wid, key, exc))
            rho = None
        try:
            kap = parse_kappa(ent["kappa"])
        except Exception as exc:
            probs.append("%s.%s.kappa: malformed (%s)" % (wid, key, exc))
            kap = None
        rref, kref = Fraction(ref[key]["rho"]), Fraction(ref[key]["kappa"])
        if rho is not None:
            err = abs(rho - rref) / rref
            r["rho_rel_error"] = "%.3e" % float(err)
            r["rho_ok"] = err <= RHO_RTOL
            if not r["rho_ok"]:
                probs.append("%s.%s.rho: relative error above 1e-9" % (wid, key))
        if kap is not None:
            r["kappa_ok"] = kap == kref
            if not r["kappa_ok"]:
                probs.append("%s.%s.kappa: not the exact value" % (wid, key))
        rec[key] = r
    return not probs, probs, rec
