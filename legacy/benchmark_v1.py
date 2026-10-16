#!/usr/bin/env python3
# ============================================================================
#  Diagnostics and performance benchmark -- AIR-DEEP-FRI Battery Passport
#
#  Uses the prover / verifier of verify_battery_passport.py (same folder),
#  so that exactly the same code is diagnosed and timed.
#
#  Part A -- Diagnostics
#    A1  all 2^8 = 256 binary traces: accepted / rejected, violated
#        constraint(s) and reason for every rejected trace
#    A2  non-binary traces (random and targeted)
#    A3  independence of the parity and mandatory layers
#    A4  cheating prover on every invalid trace (remainders dropped)
#    A5  tampered proofs of the article trace
#  Part B -- Performance (mean +/- std over R runs)
#    B1  article instance N = 8, blowup = 8
#    B2  blowup in {4, 8, 16, 32} for N = 8
#    B3  N in {8, 16, 32} for blowup = 8 (generalised layout: mandatory
#        criteria at g^0, g^1, g^(N-1), optional criteria at g^2..g^(N-2))
#
#  Usage
#    python3 benchmark.py                 diagnostics + performance (10 runs)
#    python3 benchmark.py --diag          diagnostics only
#    python3 benchmark.py --perf          performance only
#    python3 benchmark.py --runs 20       number of timed runs
#    python3 benchmark.py --list          list the 256 traces one by one
#  Exit code: 0 if every diagnostic matches the compliance rule, 1 otherwise
# ============================================================================

import copy
import platform
import random
import statistics
import sys
import time
from collections import Counter
from itertools import product

import verify_battery_passport as bp

p = bp.p
FAILS = []


def section(title):
    print("\n" + "=" * 78 + "\n  " + title + "\n" + "=" * 78)


def result(label, cond):
    print(("  [ok]   " if cond else "  [FAIL] ") + label)
    if not cond:
        FAILS.append(label)


def fmt(J):
    return "".join(str(j) for j in J)


# ============================================================================
#  Part A -- Diagnostics
# ============================================================================
def a1_all_binary_traces(prm, listing):
    section("A1  All 256 binary traces: verdict and diagnostic")
    rows, by_cause, mismatches = [], Counter(), 0
    for J in product((0, 1), repeat=8):
        J = list(J)
        compliant = bp.is_compliant(J, prm)
        try:
            proof, _ = bp.prove(J, prm)
            ok, reason, _ = bp.verify(proof, prm)
            verdict = "ACCEPTED" if ok else "REJECTED"
            cause = "-" if ok else reason
        except bp.AIRViolation as e:
            verdict = "REJECTED"
            cause = "; ".join(f"C{k}: {bp.diagnose(J, prm, k)}" for k in e.args[0])
            by_cause[" + ".join(f"C{k}" for k in e.args[0])] += 1
        expected = "ACCEPTED" if compliant else "REJECTED"
        mismatches += verdict != expected
        rows.append((J, verdict, cause, expected))

    acc = [r for r in rows if r[1] == "ACCEPTED"]
    print(f"\n  {len(acc)} accepted, {256 - len(acc)} rejected\n")
    print("  Accepted traces (J0..J7)  |  # optional criteria satisfied")
    for J, _, _, _ in acc:
        print(f"    {fmt(J)}   |  {sum(J[2:7])}")
    print("\n  Rejected traces grouped by violated constraint(s)")
    print("    C3 = parity of the optional criteria is odd")
    print("    C4 = at least one mandatory criterion (J0, J1, J7) equals 0")
    for cause, n in sorted(by_cause.items()):
        print(f"    {cause:<8} : {n:3d} traces")
    if listing:
        print("\n  Trace     Verdict    Reason")
        for J, v, c, _ in rows:
            print(f"  {fmt(J)}  {v:<9}  {c}")
    else:
        print("\n  (use --list to print the diagnostic of every trace)")
    result("verdict = compliance rule for all 256 traces", mismatches == 0)
    result("exactly 16 accepted traces (2^4 even-weight optional parts)", len(acc) == 16)
    result("every accepted proof verifies, every rejected trace is stopped by the AIR",
           all((v == "ACCEPTED") == bp.is_compliant(J, prm) for J, v, _, _ in rows))


def a2_non_binary(prm, rng):
    section("A2  Non-binary traces")
    n, rejected_c1 = 300, 0
    for _ in range(n):
        J = [rng.randrange(p) for _ in range(8)]
        A = bp.arithmetize(J, prm)
        rejected_c1 += 1 in A["violated"]
    result(f"{n} random traces in F_p^8 are all rejected by C1 ({rejected_c1}/{n})", rejected_c1 == n)
    x = 2 * bp.inv(3) % p
    J = [1, 1, 2, x, 0, 0, 0, 1]
    P = [p - 1, 1] + [0] * 6
    for i in range(2, 7):
        P[i] = P[i - 1] * (1 - 2 * J[i]) % p
    P[7] = 1
    f, fP = bp.intt(J, prm.g), bp.intt(P, prm.g)
    C = bp.constraint_polys(f, fP, prm)
    viol = [k + 1 for k in range(4) if bp.pdivmod(C[k], prm.Z[k])[1]]
    print("  Targeted attack: J2 = 2, J3 = 2/3, so (1 - 2 J2)(1 - 2 J3) = (-3)(-1/3) = 1;")
    print(f"  the accumulator reaches P6 = 1 and only these constraints fail: {['C%d' % k for k in viol]}")
    result("the targeted non-binary attack is caught by C1 alone", viol == [1])


def a3_layers(prm):
    section("A3  Independence of the two layers")
    par_ok = mand_ok = True
    for J in product((0, 1), repeat=8):
        A = bp.arithmetize(list(J), prm)
        v = set(A["violated"])
        par_ok &= (3 not in v) == (sum(J[2:7]) % 2 == 0)
        mand_ok &= (4 not in v) == (J[0] == J[1] == J[7] == 1)
    result("parity layer {C1,C2,C3} accepts exactly the even-parity traces, whatever J0, J1, J7", par_ok)
    result("mandatory layer {C4} accepts exactly the traces with J0 = J1 = J7 = 1", mand_ok)


def a4_cheating(prm):
    section("A4  Cheating prover on every invalid trace (division remainders dropped)")
    stage = Counter()
    n = 0
    for J in product((0, 1), repeat=8):
        J = list(J)
        if bp.is_compliant(J, prm):
            continue
        proof, _ = bp.prove(J, prm, cheat=True)
        ok, reason, _ = bp.verify(proof, prm)
        n += 1
        stage["ACCEPTED (soundness failure)" if ok else reason] += 1
    for reason, k in stage.items():
        print(f"    {k:3d} / {n}  {reason}")
    result(f"all {n} cheating proofs are rejected by the verifier",
           "ACCEPTED (soundness failure)" not in stage)


def a5_tampering(prm):
    section("A5  Tampered proofs of the article trace")
    proof, _ = bp.prove(prm.default_trace(), prm)
    ok, _, _ = bp.verify(proof, prm)
    result("untampered proof is accepted", ok)

    def flip(b):
        return bytes([b[0] ^ 1]) + b[1:]
    cases = [
        ("Q(z) + 1", lambda q: q.update(Qz=(q["Qz"] + 1) % p)),
        ("f(z) + 1", lambda q: q.update(fz=(q["fz"] + 1) % p)),
        ("f_P(gz) + 1", lambda q: q.update(fPgz=(q["fPgz"] + 1) % p)),
        ("root(f) modified", lambda q: q.update(root_f=flip(q["root_f"]))),
        ("root(DEEP) modified", lambda q: q.update(root_DEEP=flip(q["root_DEEP"]))),
        ("beta_1 + 1", lambda q: q.update(beta=(q["beta"] + 1) % p)),
        ("DEEP value of query 1 + 1", lambda q: q["queries"][0].update(value=(q["queries"][0]["value"] + 1) % p)),
        ("Merkle sibling of query 7 modified", lambda q: q["queries"][6]["path"].__setitem__(3, flip(q["queries"][6]["path"][3]))),
        ("index of query 2 changed", lambda q: q["queries"][1].update(iota=(q["queries"][1]["iota"] + 1) % prm.size_L)),
        ("last query removed", lambda q: q["queries"].pop()),
    ]
    all_rej = True
    for name, mutate in cases:
        t = copy.deepcopy(proof)
        mutate(t)
        ok, reason, _ = bp.verify(t, prm)
        all_rej &= not ok
        print(f"    {name:<36} -> {'ACCEPTED' if ok else 'REJECTED'}: {reason}")
    result("every tampered proof is rejected", all_rej)


# ============================================================================
#  Part B -- Performance
# ============================================================================
def timed(fn, runs):
    out = []
    for _ in range(runs):
        t0 = time.perf_counter()
        fn()
        out.append((time.perf_counter() - t0) * 1000)
    return statistics.mean(out), (statistics.stdev(out) if runs > 1 else 0.0)


def bench(prm, runs):
    J = prm.default_trace()
    proof, _ = bp.prove(J, prm)
    assert bp.verify(proof, prm)[0]
    tp, sp = timed(lambda: bp.prove(J, prm), runs)
    tv, sv = timed(lambda: bp.verify(proof, prm), runs)
    return tp, sp, tv, sv, len(bp.serialize(proof))


def perf(runs):
    section(f"B  Performance ({runs} runs per configuration, times in ms, mean +/- std)")
    print(f"  Python {platform.python_version()} on {platform.platform()}")
    print(f"  Processor: {platform.processor() or platform.machine()}")
    print("  Pure-Python reference implementation, exact F_p arithmetic, no external library.")

    print("\n  B1  Article instance (N = 8, blowup = 8, lambda* = 21)")
    prm = bp.Params(8, 8)
    tp, sp, tv, sv, size = bench(prm, runs)
    print(f"    proving {tp:8.3f} +/- {sp:.3f}   verification {tv:7.3f} +/- {sv:.3f}"
          f"   ratio {tp / tv:5.1f}   proof {size} B")

    print("\n  B2  Blowup (N = 8)")
    print("    blowup  |L|  lambda*  proving (ms)        verification (ms)   proof (B)")
    for b in (4, 8, 16, 32):
        prm = bp.Params(8, b)
        tp, sp, tv, sv, size = bench(prm, runs)
        print(f"    {b:6d} {prm.size_L:4d} {prm.lam:8d}  {tp:8.3f} +/- {sp:6.3f}  {tv:7.3f} +/- {sv:6.3f}  {size:9d}")

    print("\n  B3  Trace length N (blowup = 8; generalised layout, see header)")
    print("    N    |L|  deg Q  lambda*  proving (ms)        verification (ms)   proof (B)")
    for N in (8, 16, 32):
        prm = bp.Params(N, 8)
        tp, sp, tv, sv, size = bench(prm, runs)
        print(f"    {N:3d} {prm.size_L:5d} {prm.deg_Q:6d} {prm.lam:8d}  {tp:8.3f} +/- {sp:6.3f}  "
              f"{tv:7.3f} +/- {sv:6.3f}  {size:9d}")


# ============================================================================
def main():
    args = sys.argv[1:]
    runs = 10
    if "--runs" in args:
        runs = int(args[args.index("--runs") + 1])
    do_diag = "--perf" not in args
    do_perf = "--diag" not in args
    prm = bp.Params(8, 8)
    rng = random.Random(2026)
    print("AIR-DEEP-FRI Battery Passport -- diagnostics and benchmark")
    if do_diag:
        a1_all_binary_traces(prm, "--list" in args)
        a2_non_binary(prm, rng)
        a3_layers(prm)
        a4_cheating(prm)
        a5_tampering(prm)
        section("DIAGNOSTIC SUMMARY")
        print("  all diagnostics consistent with the compliance rule" if not FAILS
              else "  FAILED: " + "; ".join(FAILS))
    if do_perf:
        perf(runs)
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
