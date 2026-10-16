#!/usr/bin/env python3
# ============================================================================
#  Diagnostics and performance benchmark -- transparent AIR-DEEP-FRI STARK
#  Battery Passport compliance over the Goldilocks field
#
#  Uses the prover / verifier of verify_battery_passport.py (same folder),
#  so that exactly the same code is diagnosed and timed.
#
#  Part A -- Diagnostics
#    A1  all 2^8 = 256 binary traces: accepted / rejected, violated
#        constraint(s) and reason for every rejected trace
#    A2  non-binary traces (random and targeted)
#    A3  independence of the parity and mandatory layers
#    A4  cheating provers on every invalid trace: division remainders
#        dropped; false out-of-domain value Q(z) := Q*(z)
#    A5  tampered proofs of the article trace
#    A6  forged proofs without any witness: the attack accepted by the
#        first version of the verifier (legacy/, no FRI layer and no
#        opening of f, f_P, Q) is replayed against the corrected verifier
#    A7  degree cost of a threshold rule "at least k of 5" (comparison)
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
    section("A4  Cheating provers on every invalid trace")
    invalid = [list(J) for J in product((0, 1), repeat=8) if not bp.is_compliant(list(J), prm)]
    for mode, text in (("drop_remainder", "division remainders dropped (Q a polynomial, wrong at z)"),
                       ("fake_ood", "Q(z) replaced by Q*(z) (OOD check passed, F not a polynomial)")):
        stage = Counter()
        for J in invalid:
            proof, _ = bp.prove(J, prm, cheat=mode)
            ok, reason, _ = bp.verify(proof, prm)
            stage["ACCEPTED (soundness failure)" if ok else reason.split(" (query")[0]] += 1
        print(f"\n  {mode}: {text}")
        for reason, k in stage.most_common():
            print(f"    {k:3d} / {len(invalid)}  {reason}")
        result(f"all {len(invalid)} '{mode}' proofs are rejected",
               "ACCEPTED (soundness failure)" not in stage)
    proof, _ = bp.prove(prm.default_trace(), prm, cheat="fake_ood")
    ok, reason, _ = bp.verify(proof, prm)
    print(f"\n  fake_ood on the compliant article trace with Q(z) unchanged -> "
          f"{'ACCEPTED' if ok else 'REJECTED'} (expected: accepted, Q*(z) = Q(z) already)")
    result("fake_ood mode is harmless on a compliant trace (control)", ok)


def a5_tampering(prm):
    section("A5  Tampered proofs of the article trace")
    proof, _ = bp.prove(prm.default_trace(), prm)
    ok, _, _ = bp.verify(proof, prm)
    result("untampered proof is accepted", ok)

    def flip(b):
        return bytes([b[0] ^ 1]) + b[1:]

    def add1(lst, i):
        lst[i] = (lst[i] + 1) % p

    cases = [
        ("Q(z) + 1", lambda q: add1(q["ood"], 4)),
        ("f(z) + 1", lambda q: add1(q["ood"], 0)),
        ("f_P(gz) + 1", lambda q: add1(q["ood"], 3)),
        ("root(T) modified", lambda q: q.update(root_T=flip(q["root_T"]))),
        ("root(C) modified", lambda q: q.update(root_C=flip(q["root_C"]))),
        ("root(F_1) modified", lambda q: q["layer_roots"].__setitem__(0, flip(q["layer_roots"][0]))),
        ("final constant + 1", lambda q: q.update(final=(q["final"] + 1) % p)),
        ("f(x) of query 1 + 1", lambda q: add1(q["queries"][0]["T"]["values"], 0)),
        ("Q(-x) of query 3 + 1", lambda q: add1(q["queries"][2]["C"]["values"], 1)),
        ("F_2 value of query 5 + 1", lambda q: add1(q["queries"][4]["layers"][1]["values"], 0)),
        ("Merkle sibling of query 7 (T) modified",
         lambda q: q["queries"][6]["T"]["path"].__setitem__(3, flip(q["queries"][6]["T"]["path"][3]))),
        ("position of query 2 changed", lambda q: q["queries"][1].update(j=(q["queries"][1]["j"] + 1) % 32)),
        ("last query removed", lambda q: q["queries"].pop()),
    ]
    all_rej = True
    for name, mutate in cases:
        t = copy.deepcopy(proof)
        mutate(t)
        ok, reason, _ = bp.verify(t, prm)
        all_rej &= not ok
        print(f"    {name:<40} -> {'ACCEPTED' if ok else 'REJECTED'}: {reason}")
    result("every tampered proof is rejected", all_rej)


def a6_forgery(prm, rng, trials=200):
    section("A6  Forged proofs without any witness")
    # (a) the attack against the first version of the verifier
    import importlib.util
    import os
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "legacy",
                        "verify_battery_passport_v1.py")
    if os.path.exists(path):
        spec = importlib.util.spec_from_file_location("bp_v1", path)
        v1 = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(v1)
        prm1 = v1.Params()
        acc1 = 0
        for _ in range(trials):
            root_f, root_fP = rng.getrandbits(256).to_bytes(32, "little"), rng.getrandbits(256).to_bytes(32, "little")
            t = root_f + root_fP
            alphas = []
            for _ in range(4):
                a = v1.H(t) % p
                alphas.append(a)
                t += v1.le64(a)
            c = 0
            while True:
                z = v1.H(t + v1.le64(c)) % p
                if z not in prm1.L_set:
                    break
                c += 1
            ev = [rng.randrange(p) for _ in range(4)]
            Cz = v1.constraint_values(*ev)
            Qz = sum(a * cz * v1.inv(v1.peval(zk, z)) for a, cz, zk in zip(alphas, Cz, prm1.Z)) % p
            DEEP_L = [rng.randrange(p) for _ in range(prm1.size_L)]
            layers = v1.merkle_layers(DEEP_L)
            tr5 = t + v1.le64(z) + b"".join(v1.le64(v) for v in ev) + v1.le64(Qz) + layers[-1][0]
            beta = v1.H(tr5) % p
            tr6 = tr5 + v1.le64(beta)
            queries = []
            for r in range(1, prm1.lam + 1):
                c = 0
                while True:
                    iota = v1.H(tr6 + v1.le64(r) + v1.le64(c)) % prm1.size_L
                    if iota not in prm1.G_idx:
                        break
                    c += 1
                queries.append({"iota": iota, "value": DEEP_L[iota], "path": v1.merkle_path(layers, iota)})
            forged = {"root_f": root_f, "root_fP": root_fP, "fz": ev[0], "fPz": ev[1], "fgz": ev[2],
                      "fPgz": ev[3], "Qz": Qz, "root_DEEP": layers[-1][0], "beta": beta, "queries": queries}
            acc1 += v1.verify(forged, prm1)[0]
        print(f"  (a) first verifier (legacy/): {acc1}/{trials} forged proofs ACCEPTED")
        print("      -> no committed FRI layer and no opening of f, f_P, Q: the DEEP values are")
        print("         never tied to the trace, and Q(z) can be chosen equal to Q*(z).")
        result("the legacy verifier is shown to accept forged proofs (motivates the correction)",
               acc1 == trials)
    else:
        print("  (a) legacy/verify_battery_passport_v1.py not found: skipped")

    # (b) the same forgery strategy against the corrected verifier
    n = prm.size_L
    variants = {
        "random values on L": lambda: [[rng.randrange(p) for _ in range(n)] for _ in range(3)],
        "random low-degree f, f_P (deg 7), Q (deg 8)": lambda: [
            bp.ntt([rng.randrange(p) for _ in range(d + 1)], prm.h, n) for d in (7, 7, 8)],
    }
    for name, gen in variants.items():
        stage = Counter()
        for _ in range(trials):
            proof, _ = bp.prove(None, prm, cheat="forge", forged=gen())
            ok, reason, _ = bp.verify(proof, prm)
            stage["ACCEPTED (soundness failure)" if ok else reason.split(" (query")[0]] += 1
        print(f"\n  (b) corrected verifier, forgery with {name}, OOD check passed by construction")
        for reason, k in stage.most_common():
            print(f"    {k:3d} / {trials}  {reason}")
        result(f"all {trials} forged proofs ({name}) are rejected",
               "ACCEPTED (soundness failure)" not in stage)


def a7_threshold_rule(prm):
    section("A7  Cost of a threshold rule 'at least k of 5 optional criteria' (comparison)")
    # additive counter S_1 = 0, S_i = S_(i-1) + J_i (i = 2..6); S_0, S_7 free (set to 0)
    print("  Parity:    transition deg 2, final condition f_P - 1 at g^6 (linear) -> deg Q = 8")
    ok_all = True
    for k in (1, 2, 3, 4, 5):
        J = [1, 1] + [1] * k + [0] * (5 - k) + [1]          # exactly k optional criteria
        S = [0] * 8
        for i in range(2, 7):
            S[i] = S[i - 1] + J[i]
        fS = bp.intt(S, prm.g)
        B = [1]
        for s in range(k, 6):
            B = bp.pmul(B, bp.psub(fS, [s]))
        q, r = bp.pdivmod(B, bp.vanishing([prm.G[6]]))
        f = bp.intt(J, prm.g)
        T = bp.psub(bp.psub(bp.pshift(fS, prm.g), fS), bp.pshift(f, prm.g))
        qt, rt = bp.pdivmod(T, bp.vanishing([prm.G[i] for i in range(1, 6)]))
        d_F = 1
        while d_F <= bp.deg(q):
            d_F *= 2
        print(f"  k = {k}: boundary prod_(s={k}..5)(f_S - s) has degree {bp.deg(B)}, quotient degree "
              f"{bp.deg(q)} (expected {7 * (6 - k) - 1}); transition quotient degree {bp.deg(qt)}; "
              f"|L| at rate 1/8 >= {8 * d_F}")
        ok_all &= (not r and not rt and bp.deg(q) == 7 * (6 - k) - 1)
    result("threshold boundary constraint is exact and has quotient degree 7(6-k) - 1 (27 for k = 2)", ok_all)


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

    print("\n  B1  Article instance (N = 8, blowup = 8, lambda* = 20)")
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
    print("Transparent AIR-DEEP-FRI Battery Passport -- diagnostics and benchmark")
    if do_diag:
        a1_all_binary_traces(prm, "--list" in args)
        a2_non_binary(prm, rng)
        a3_layers(prm)
        a4_cheating(prm)
        a5_tampering(prm)
        a6_forgery(prm, rng)
        a7_threshold_rule(prm)
        section("DIAGNOSTIC SUMMARY")
        print("  all diagnostics consistent with the compliance rule" if not FAILS
              else "  FAILED: " + "; ".join(FAILS))
    if do_perf:
        perf(runs)
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
