#!/usr/bin/env python3
# ============================================================================
#  Reference prover / verifier -- AIR-DEEP-FRI Battery Passport
#  Four-constraint AIR over the Goldilocks field
#
#  Article: "ZK-STARK over the Goldilocks Field for Battery Passport
#            Compliance: Tight Soundness Bounds and Full Numerical
#            Verification"
#
#  Construction (article instance: N = 8, blowup = 8, |L| = 64)
#    Trace          J in {0,1}^N over G = <g>, g of order N
#    Evaluation dom L = <h>, |L| = N * blowup, G = {h^(blowup*k)}
#    Criteria       mandatory: J_0, J_1, J_(N-1); optional: J_2 .. J_(N-2)
#    Accumulator    P_1 = 1, P_i = P_{i-1}(1 - 2 J_i) for i = 2..N-2,
#                   P_0 = 1 - 2 J_1 (padding), P_(N-1) = 1 (free, convention)
#    Constraints    C1 = f^2 - f                          on G
#                   C2 = f_P(gx) - f_P(x)(1 - 2 f(gx))    on {g^0 .. g^(N-3)}
#                   C3 = f_P - 1                          on {g^1, g^(N-2)}
#                   C4 = f - 1                            on {g^0, g^1, g^(N-1)}
#    Batched        Q = sum_k alpha_k C_k / Z_k,          deg Q <= N
#
#  Encoding convention
#    field element : 8 bytes little-endian (LE64)
#    Merkle leaf   : SHA256(LE64(v)); node = SHA256(left || right)
#    H(t)          : SHA256(t)[0:8] read as LE64 (mod p for field
#                    challenges, mod |L| for query indices)
#
#  Transcript (Table "Complete protocol transcript" of the article)
#    tr1 = root(f) || root(f_P)
#    alpha_1 = H(tr1), alpha_k = H(tr1 || alpha_1 || ... || alpha_{k-1})
#    tr2 = tr1 || alpha_1 || ... || alpha_4
#    z   = H(tr2 || c) mod p, smallest c >= 0 with z not in L
#    tr3 = tr2 || z || f(z) || f_P(z) || f(gz) || f_P(gz)
#    tr4 = tr3 || Q(z);  tr5 = tr4 || root(DEEP)
#    beta_1 = H(tr5) mod p;  tr6 = tr5 || beta_1
#    iota_r = H(tr6 || r || c) mod |L|, smallest c >= 0 with h^iota_r not in G
#
#  Scope of the verifier (as in the article): it recomputes every
#  Fiat-Shamir challenge, checks the out-of-domain identity
#  Q*(z) = Q(z) and the Merkle authentication of the lambda queried
#  DEEP values. It does not open f, f_P at the query points.
#
#  Usage
#    python3 verify_battery_passport.py                    article trace
#    python3 verify_battery_passport.py 1 1 1 0 1 0 0 1    any trace
#    python3 verify_battery_passport.py ... --json out.json
#  The run stops in the module where a violation is detected.
#  Exit code: 0 = trace accepted, 2 = trace rejected, 1 = internal error
#
#  Requirements: Python 3.8+, standard library only.
# ============================================================================

import hashlib
import json
import math
import struct
import sys

p = 2**64 - 2**32 + 1
ARTICLE_TRACE = [1, 1, 1, 0, 1, 0, 0, 1]
CRITERIA_8 = ["raw material origin certification", "legal entity identity (LEI)",
              "carbon footprint (PCF)", "responsible sourcing (RMC)",
              "recycled content", "performance / durability (SoH)",
              "audited labour conditions", "end-of-life declaration"]


# ----------------------------------------------------------------------------
#  Field and polynomials (coefficients low -> high degree)
# ----------------------------------------------------------------------------
def inv(a):
    a %= p
    if a == 0:
        raise ZeroDivisionError("inverse of 0 in F_p")
    return pow(a, p - 2, p)


def trim(a):
    a = [x % p for x in a]
    while a and a[-1] == 0:
        a.pop()
    return a


def deg(a):
    return len(trim(a)) - 1


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pscale(a, c):
    return trim([x * c for x in a])


def psub(a, b):
    return padd(a, pscale(b, p - 1))


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
    return trim(r)


def pdivmod(a, b):
    a, b = trim(a), trim(b)
    if len(a) < len(b):
        return [], a
    q = [0] * (len(a) - len(b) + 1)
    ib = inv(b[-1])
    while len(a) >= len(b) and a:
        c = a[-1] * ib % p
        d = len(a) - len(b)
        q[d] = c
        for i, y in enumerate(b):
            a[i + d] = (a[i + d] - c * y) % p
        a = trim(a)
    return trim(q), a


def peval(a, x):
    r = 0
    for c in reversed(a):
        r = (r * x + c) % p
    return r


def pshift(a, s):
    return trim([c * pow(s, i, p) for i, c in enumerate(a)])


def vanishing(points):
    r = [1]
    for x in points:
        r = pmul(r, [(-x) % p, 1])
    return r


def intt(values, w):
    n = len(values)
    iw, inn = inv(w), inv(n)
    return trim([inn * sum(values[k] * pow(iw, i * k, p) for k in range(n)) % p for i in range(n)])


def ntt(coeffs, w, n):
    c = list(coeffs) + [0] * (n - len(coeffs))
    return [sum(c[i] * pow(w, i * k, p) for i in range(n)) % p for k in range(n)]


# ----------------------------------------------------------------------------
#  Hashing, Fiat-Shamir, Merkle
# ----------------------------------------------------------------------------
def le64(x):
    return struct.pack("<Q", int(x) % 2**64)


def sha256(b):
    return hashlib.sha256(b).digest()


def H(t):
    return int.from_bytes(sha256(t)[:8], "little")


def merkle_layers(values):
    layer = [sha256(le64(v)) for v in values]
    layers = [layer]
    while len(layer) > 1:
        if len(layer) % 2:
            layer = layer + [layer[-1]]
        layer = [sha256(layer[i] + layer[i + 1]) for i in range(0, len(layer), 2)]
        layers.append(layer)
    return layers


def merkle_path(layers, idx):
    path = []
    for layer in layers[:-1]:
        if len(layer) % 2:
            layer = layer + [layer[-1]]
        path.append(layer[idx ^ 1])
        idx //= 2
    return path


def merkle_verify(root, idx, value, path):
    """Returns (valid, number of SHA-256 evaluations)."""
    node, n = sha256(le64(value)), 1
    for sib in path:
        node = sha256(node + sib) if idx % 2 == 0 else sha256(sib + node)
        n += 1
        idx //= 2
    return node == root, n


# ----------------------------------------------------------------------------
#  Parameters
# ----------------------------------------------------------------------------
class Params:
    """Domains, vanishing polynomials and soundness parameters for (N, blowup)."""

    def __init__(self, N=8, blowup=8, lam=None):
        assert N >= 8 and N & (N - 1) == 0, "N must be a power of two >= 8"
        self.N, self.blowup, self.size_L = N, blowup, N * blowup
        sL = self.size_L
        assert (p - 1) % sL == 0
        # article generator h = 2^(192/|L|) when possible (h = 8 for |L| = 64)
        self.h = pow(2, 192 // sL, p) if 192 % sL == 0 else pow(7, (p - 1) // sL, p)
        assert pow(self.h, sL, p) == 1 and pow(self.h, sL // 2, p) != 1, "h must have order |L|"
        self.g = pow(self.h, blowup, p)
        self.G = [pow(self.g, k, p) for k in range(N)]
        self.L = [pow(self.h, i, p) for i in range(sL)]
        self.L_set = set(self.L)
        self.G_idx = set(range(0, sL, blowup))
        self.mandatory = [0, 1, N - 1]
        self.optional = list(range(2, N - 1))
        self.domains = [list(range(N)), list(range(N - 2)), [1, N - 2], [0, 1, N - 1]]
        self.Z = [vanishing([self.G[k] for k in d]) for d in self.domains]
        self.deg_Q = N                                # deg Q2 = 2(N-1) - (N-2)
        self.deg_DEEP = N - 1
        self.eps_deep = self.deg_Q / (p - sL)
        self.eps_fri = self.deg_DEEP / (sL - N)
        self.kappa = -math.log2(self.eps_deep)
        self.bits_per_query = math.log2(1 / self.eps_fri)
        self.lam_star = math.ceil(self.kappa / self.bits_per_query)
        self.lam = lam if lam is not None else self.lam_star
        self.depth = int(math.log2(sL))

    def default_trace(self):
        if self.N == 8:
            return list(ARTICLE_TRACE)
        J = [0] * self.N
        for i in self.mandatory + self.optional[:2]:
            J[i] = 1
        return J

    def eps_total(self, lam):
        return self.eps_deep + (1 - self.eps_deep) * self.eps_fri**lam

    def proof_size(self, lam=None):
        lam = self.lam if lam is None else lam
        return 144 + lam * (8 + self.depth * 32)


# ----------------------------------------------------------------------------
#  AIR
# ----------------------------------------------------------------------------
def is_compliant(J, prm):
    return (all(j in (0, 1) for j in J) and all(J[i] == 1 for i in prm.mandatory)
            and sum(J[i] for i in prm.optional) % 2 == 0)


def accumulator(J, prm):
    N = prm.N
    P = [0] * N
    P[1] = 1
    for i in range(2, N - 1):
        P[i] = P[i - 1] * (1 - 2 * J[i]) % p
    P[0] = (1 - 2 * J[1]) % p
    P[N - 1] = 1
    return P


def constraint_polys(f, fP, prm):
    fg, fPg = pshift(f, prm.g), pshift(fP, prm.g)
    return [psub(pmul(f, f), f),
            psub(fPg, pmul(fP, padd([1], pscale(fg, p - 2)))),
            psub(fP, [1]),
            psub(f, [1])]


def constraint_values(fz, fPz, fgz, fPgz):
    return [(fz * fz - fz) % p, (fPgz - fPz * (1 - 2 * fgz)) % p, (fPz - 1) % p, (fz - 1) % p]


def arithmetize(J, prm):
    """Interpolation and AIR check.  Returns a dict with f, f_P, P, C_k,
    quotients Q_k, remainders R_k and the list of violated constraints."""
    Jm = [x % p for x in J]
    P = accumulator(Jm, prm)
    f, fP = intt(Jm, prm.g), intt(P, prm.g)
    C = constraint_polys(f, fP, prm)
    Q, R = zip(*[pdivmod(C[k], prm.Z[k]) for k in range(4)])
    violated = [k + 1 for k in range(4) if R[k]]
    return {"J": Jm, "P": P, "f": f, "fP": fP, "C": list(C), "Q": list(Q), "R": list(R),
            "violated": violated}


def diagnose(J, prm, k):
    """Human-readable reason why constraint C_k is violated by the trace J."""
    N = prm.N
    names = CRITERIA_8 if N == 8 else [f"criterion {i}" for i in range(N)]
    if k == 1:
        bad = [i for i in range(N) if J[i] % p not in (0, 1)]
        return "non-binary trace value(s) at " + ", ".join(f"g^{i} (J_{i} = {J[i]})" for i in bad)
    if k == 4:
        bad = [i for i in prm.mandatory if J[i] % p != 1]
        return "mandatory criterion not satisfied: " + "; ".join(
            f"J(g^{i}) = {J[i]} ({names[i]})" for i in bad)
    if k == 3:
        s = sum(J[i] for i in prm.optional)
        if all(J[i] in (0, 1) for i in prm.optional):
            return (f"parity condition fails: {s} optional criteria satisfied (odd), "
                    f"so CI_opt = -1 != 1")
        return "CI_opt != 1 (non-binary optional values)"
    return "transition constraint not satisfied by the accumulator"


# ----------------------------------------------------------------------------
#  Prover
# ----------------------------------------------------------------------------
class AIRViolation(Exception):
    pass


def prove(J, prm, cheat=False):
    """Honest prover.  Raises AIRViolation if the trace violates the AIR.
    With cheat=True the remainders of the divisions are silently dropped,
    producing a (false) proof for a non-compliant trace."""
    A = arithmetize(J, prm)
    if A["violated"] and not cheat:
        raise AIRViolation(A["violated"])
    f, fP = A["f"], A["fP"]
    f_L = [peval(f, x) for x in prm.L]
    fP_L = [peval(fP, x) for x in prm.L]
    root_f, root_fP = merkle_layers(f_L)[-1][0], merkle_layers(fP_L)[-1][0]
    n_fs = 0
    t = root_f + root_fP
    alphas = []
    for _ in range(4):
        a = H(t) % p
        n_fs += 1
        alphas.append(a)
        t += le64(a)
    tr2, c = t, 0
    while True:
        z = H(tr2 + le64(c)) % p
        n_fs += 1
        if z not in prm.L_set:
            break
        c += 1
    gz = prm.g * z % p
    ev = [peval(f, z), peval(fP, z), peval(f, gz), peval(fP, gz)]
    Q = []
    for a, q in zip(alphas, A["Q"]):
        Q = padd(Q, pscale(q, a))
    Qz = peval(Q, z)
    tr4 = tr2 + le64(z) + b"".join(le64(v) for v in ev) + le64(Qz)
    DEEP, rem = pdivmod(psub(Q, [Qz]), [(-z) % p, 1])
    DEEP_L = [peval(DEEP, x) for x in prm.L]
    layers = merkle_layers(DEEP_L)
    root_D = layers[-1][0]
    tr5 = tr4 + root_D
    beta = H(tr5) % p
    n_fs += 1
    tr6 = tr5 + le64(beta)
    queries, rejections = [], 0
    for r in range(1, prm.lam + 1):
        c = 0
        while True:
            iota = H(tr6 + le64(r) + le64(c)) % prm.size_L
            n_fs += 1
            if iota not in prm.G_idx:
                break
            c += 1
            rejections += 1
        queries.append({"iota": iota, "value": DEEP_L[iota], "path": merkle_path(layers, iota)})
    proof = {"root_f": root_f, "root_fP": root_fP, "fz": ev[0], "fPz": ev[1], "fgz": ev[2],
             "fPgz": ev[3], "Qz": Qz, "root_DEEP": root_D, "beta": beta, "queries": queries}
    aux = {"A": A, "alphas": alphas, "z": z, "Q": Q,
           "DEEP": DEEP, "DEEP_rem": rem, "DEEP_L": DEEP_L, "rejections": rejections,
           "prover_fs_hashes": n_fs}
    return proof, aux


def serialize(proof):
    return (proof["root_f"] + proof["root_fP"]
            + b"".join(le64(proof[k]) for k in ("fz", "fPz", "fgz", "fPgz", "Qz"))
            + proof["root_DEEP"] + le64(proof["beta"])
            + b"".join(le64(q["value"]) + b"".join(q["path"]) for q in proof["queries"]))


# ----------------------------------------------------------------------------
#  Verifier (works on the proof only)
# ----------------------------------------------------------------------------
def verify(proof, prm):
    """Returns (accepted, reason, stats)."""
    st = {"fs_hashes": 0, "merkle_hashes": 0, "inversions": 0}
    t = proof["root_f"] + proof["root_fP"]
    alphas = []
    for _ in range(4):
        a = H(t) % p
        st["fs_hashes"] += 1
        alphas.append(a)
        t += le64(a)
    tr2, c = t, 0
    while True:
        z = H(tr2 + le64(c)) % p
        st["fs_hashes"] += 1
        if z not in prm.L_set:
            break
        c += 1
    Cz = constraint_values(proof["fz"], proof["fPz"], proof["fgz"], proof["fPgz"])
    Qstar = 0
    for a, cz, zk in zip(alphas, Cz, prm.Z):
        Qstar = (Qstar + a * cz * inv(peval(zk, z))) % p
        st["inversions"] += 1
    st.update(z=z, z_counter=c, alphas=alphas, Qstar=Qstar)
    if Qstar != proof["Qz"]:
        return False, "Round 3: out-of-domain check Q*(z) != Q(z)", st
    tr5 = (tr2 + le64(z) + b"".join(le64(proof[k]) for k in ("fz", "fPz", "fgz", "fPgz"))
           + le64(proof["Qz"]) + proof["root_DEEP"])
    beta = H(tr5) % p
    st["fs_hashes"] += 1
    if beta != proof["beta"]:
        return False, "Round 5: folding challenge beta_1 does not match the transcript", st
    tr6 = tr5 + le64(beta)
    if len(proof["queries"]) != prm.lam:
        return False, f"Round 6: {len(proof['queries'])} queries instead of {prm.lam}", st
    for r, q in enumerate(proof["queries"], 1):
        c = 0
        while True:
            iota = H(tr6 + le64(r) + le64(c)) % prm.size_L
            st["fs_hashes"] += 1
            if iota not in prm.G_idx:
                break
            c += 1
        if q["iota"] != iota:
            return False, f"Round 6: query {r} index {q['iota']} != transcript index {iota}", st
        ok, n = merkle_verify(proof["root_DEEP"], iota, q["value"], q["path"])
        st["merkle_hashes"] += n
        if not ok:
            return False, f"Round 6: Merkle path of query {r} (index {iota}) is invalid", st
    return True, "all checks passed", st


# ============================================================================
#  Command-line verifier for one trace
# ============================================================================
CHECKS = {"n": 0, "failed": []}


def check(label, cond):
    CHECKS["n"] += 1
    print(("  [ok]   " if cond else "  [FAIL] ") + label)
    if not cond:
        CHECKS["failed"].append(label)
    return cond


def section(title):
    print("\n" + "=" * 74 + "\n  " + title + "\n" + "=" * 74)


def info(label, value):
    print(f"         {label:<30} {value}")


def hx(x):
    return f"0x{x:016x}"


def finish(J, accepted, reason, result, json_out):
    section("VERDICT")
    print(f"  Trace J = {J}")
    if accepted:
        print("  VERDICT : ACCEPTED  -- the trace is compliant; the proof verifies")
    else:
        print(f"  VERDICT : REJECTED  -- {reason}")
    print(f"  Internal consistency checks of this verifier: "
          f"{CHECKS['n'] - len(CHECKS['failed'])}/{CHECKS['n']} passed")
    for e in CHECKS["failed"]:
        print("  FAILED: " + e)
    result["verdict"] = "accepted" if accepted else "rejected"
    result["reason"] = reason
    if json_out:
        with open(json_out, "w") as fh:
            json.dump(result, fh, indent=1)
        print(f"  values written to {json_out}")
    sys.exit(1 if CHECKS["failed"] else (0 if accepted else 2))


def main():
    args = sys.argv[1:]
    json_out = None
    if "--json" in args:
        i = args.index("--json")
        json_out = args[i + 1]
        del args[i:i + 2]
    prm = Params()
    try:
        J = [int(a) for a in args] if args else prm.default_trace()
    except ValueError:
        sys.exit("usage: verify_battery_passport.py [J0 ... J7] [--json file]")
    if len(J) != prm.N:
        sys.exit("usage: verify_battery_passport.py [J0 ... J7] [--json file]")
    result = {"J": J}
    print("AIR-DEEP-FRI Battery Passport -- reference prover/verifier (4-constraint AIR)")
    print(f"Trace J = {J}")
    print("Exit code: 0 = trace accepted, 2 = trace rejected, 1 = internal error")

    # ---------------------------------------------------------------- 1
    section("MODULE 1  Goldilocks field and generators")
    g, h = prm.g, prm.h
    check("p = t^2 - t + 1 with t = 2^32", p == (2**32)**2 - 2**32 + 1)
    check("p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537", p - 1 == 2**32 * 3 * 5 * 17 * 257 * 65537)
    check("ord_p(2) = 192  (2^192 = 1, 2^96 = -1, 2^64 = 4294967295)",
          pow(2, 192, p) == 1 and pow(2, 96, p) == p - 1 and pow(2, 64, p) == 4294967295)
    check("h = 8 has order exactly 64", h == 8 and pow(h, 64, p) == 1 and pow(h, 32, p) != 1)
    check("g = h^8 = 2^24 has order exactly 8", g == 2**24 and pow(g, 8, p) == 1 and pow(g, 4, p) != 1)
    check("g^4 = -1 and g^(-4i) = (-1)^i",
          pow(g, 4, p) == p - 1 and all(pow(inv(pow(g, 4, p)), i, p) == (1, p - 1)[i % 2] for i in range(8)))

    # ---------------------------------------------------------------- 2
    section("MODULE 2  Domains G and L")
    check("g^0 .. g^7 pairwise distinct", len(set(prm.G)) == 8)
    check("G = {h^(8k)} subset of L, |L| = 64", all(prm.G[k] == prm.L[8 * k] for k in range(8))
          and len(prm.L_set) == 64)
    check("prod_k (x - g^k) = x^8 - 1", prm.Z[0] == [p - 1, 0, 0, 0, 0, 0, 0, 0, 1])
    check("x in G  =>  g x in G", all(g * x % p in set(prm.G) for x in prm.G))

    # ---------------------------------------------------------------- 3
    section("MODULE 3  NTT/INTT interpolation of f and f_P")
    A = arithmetize(J, prm)
    f, fP, P = A["f"], A["fP"], A["P"]
    check("NTT(INTT(J)) = J", ntt(f, g, 8) == A["J"])
    check("f(g^k) = J_k and f_P(g^k) = P_k for all k",
          all(peval(f, prm.G[k]) == A["J"][k] and peval(fP, prm.G[k]) == P[k] for k in range(8)))
    info("P (signed)", [x if x < p // 2 else x - p for x in P])
    info("deg f, deg f_P", (deg(f), deg(fP)))
    if J == ARTICLE_TRACE:
        check("f coefficients = Table tab:coeffs-pi", f == [
            6917529026030469121, 18446708747605639201, 16140901060737761281, 35321808945120,
            16140901060737761281, 18446709022479351777, 16140901060737761281, 35046935232544])
        check("f_P coefficients = Table tab:coeffs_fP", fP == [
            13835058052060938241, 4611756386102018048, 18446673700670406657, 4611615923487375296,
            4611686017353646080, 4611756386093629440, 70368744177664, 4611615373731561536])
    result.update(P=P, f=f, fP=fP)

    # ---------------------------------------------------------------- 4
    section("MODULE 4  AIR constraints and quotient polynomials")
    for k in range(4):
        dom = "{" + ", ".join(f"g^{e}" for e in prm.domains[k]) + "}"
        label = f"C{k+1} vanishes on {dom}  (deg C = {deg(A['C'][k])}, deg Z = {deg(prm.Z[k])})"
        if A["R"][k]:
            print(f"  [VIOL] {label}\n         -> VIOLATED: {diagnose(J, prm, k + 1)}")
        else:
            print(f"  [ok]   {label}, deg Q{k+1} = {deg(A['Q'][k])}")
    if A["violated"]:
        reasons = "; ".join(f"C{k}: {diagnose(J, prm, k)}" for k in A["violated"])
        print("\n  The trace violates the AIR: no valid proof exists. Stopping here.")
        finish(J, False, "the trace is NOT compliant -- " + reasons, result, json_out)
    for k in range(4):
        check(f"deg Q{k+1} = {deg(A['Q'][k])} <= bound", deg(A["Q"][k]) <= [6, 8, 5, 4][k])

    # ---------------------------------------------------------------- 5
    section("MODULE 5  Soundness bounds")
    check("eps_FRI = 7/56 = 1/8", prm.eps_fri == 1 / 8)
    check("kappa* = -log2(8/(p-64)) ~ 61.00", abs(prm.kappa - 61) < 1e-3)
    check("lambda* = ceil(kappa*/3) = 21", prm.lam_star == 21)
    regime = []
    for lam in (1, 5, 10, 15, 20, 21, 22, 25, 30):
        e = prm.eps_total(lam)
        share = (1 - prm.eps_deep) * prm.eps_fri**lam / e
        regime.append({"lambda": lam, "bits": -math.log2(e), "fri_share": share})
        info(f"lambda = {lam:2d}", f"2^-{-math.log2(e):.2f}   FRI {100*share:5.1f}%   DEEP {100*(1-share):5.1f}%")
    check("eps_total(21) <= 2^-60 < eps_total(20)", prm.eps_total(21) <= 2**-60 < prm.eps_total(20))
    blow = []
    for b in (4, 8, 16, 32):
        q = Params(8, b)
        blow.append({"blowup": b, "L": q.size_L, "bits": q.bits_per_query,
                     "lambda": q.lam_star, "proof_size": q.proof_size()})
        info(f"blowup {b:2d}", f"|L| = {q.size_L:3d}  bits/query = {q.bits_per_query:.3f}  "
             f"lambda* = {q.lam_star}  proof = {q.proof_size()} B")
    result["soundness"] = {"kappa": prm.kappa, "lambda_star": prm.lam_star,
                           "regime": regime, "blowup": blow}

    # ---------------------------------------------------------------- 6-7
    proof, aux = prove(J, prm)
    section("MODULE 6  Prover, Rounds 0-3 (commitments, challenges, OOD evaluations)")
    info("root(f)", "0x" + proof["root_f"].hex())
    info("root(f_P)", "0x" + proof["root_fP"].hex())
    for k, a in enumerate(aux["alphas"], 1):
        info(f"alpha_{k}", hx(a))
    info("z", hx(aux["z"]))
    check("z not in L", aux["z"] not in prm.L_set)
    for key, name in (("fz", "f(z)"), ("fPz", "f_P(z)"), ("fgz", "f(gz)"), ("fPgz", "f_P(gz)"), ("Qz", "Q(z)")):
        info(name, hx(proof[key]))
    check("deg Q <= 8", deg(aux["Q"]) <= 8)

    section("MODULE 7  Prover, Rounds 4-6 (DEEP, FRI folding, queries)")
    check("(x - z) divides Q(x) - Q(z) and deg DEEP <= 7", aux["DEEP_rem"] == [] and deg(aux["DEEP"]) <= 7)
    Q, z, Qz, L = aux["Q"], aux["z"], proof["Qz"], prm.L
    check("DEEP(h^i) = (Q(h^i) - Q(z))/(h^i - z) at all 64 points of L (incl. G)",
          all(aux["DEEP_L"][i] == (peval(Q, L[i]) - Qz) * inv(L[i] - z) % p for i in range(64)))
    De, Do = aux["DEEP"][0::2], aux["DEEP"][1::2]
    D1 = padd(De, pscale(Do, proof["beta"]))
    i2, DL = inv(2), aux["DEEP_L"]
    check("FRI folding: DEEP^(1) has degree <= 3 and matches the folding formula on L^2",
          deg(D1) <= 3 and all(peval(D1, L[i] * L[i] % p) ==
                               ((DL[i] + DL[i + 32]) * i2 + proof["beta"] * (DL[i] - DL[i + 32]) * inv(2 * L[i])) % p
                               for i in range(32)))
    info("root(DEEP)", "0x" + proof["root_DEEP"].hex())
    info("beta_1", hx(proof["beta"]))
    info(f"iota_1 .. iota_{prm.lam}", [q["iota"] for q in proof["queries"]])
    info("rejections (draws in G)", aux["rejections"])
    q1 = proof["queries"][0]
    info(f"DEEP(h^{q1['iota']})", hx(q1["value"]))
    idx = q1["iota"]
    for lvl, s in enumerate(q1["path"]):
        info(f"  level {lvl}  index {idx:2d}  {'left ' if idx % 2 == 0 else 'right'}", "0x" + s.hex())
        idx //= 2
    blob = serialize(proof)
    check(f"serialized proof size = 200 lambda + 144 = {prm.proof_size()} bytes", len(blob) == prm.proof_size())

    # ---------------------------------------------------------------- 8
    section("MODULE 8  Verifier (works on the proof only)")
    ok, reason, st = verify(proof, prm)
    check("verifier recomputes alpha_1..alpha_4 and z", st["alphas"] == aux["alphas"] and st["z"] == z)
    info("Q*(z) recomputed", hx(st["Qstar"]))
    info("Fiat-Shamir hashes", st["fs_hashes"])
    info("Merkle hashes (leaf + 6 nodes)", st["merkle_hashes"])
    info("total SHA-256", st["fs_hashes"] + st["merkle_hashes"])
    info("field inversions", st["inversions"])
    check("verifier decision: " + reason, ok)

    result.update(
        root_f=proof["root_f"].hex(), root_fP=proof["root_fP"].hex(), alphas=aux["alphas"],
        z=z, z_counter=st["z_counter"], fz=proof["fz"], fPz=proof["fPz"], fgz=proof["fgz"],
        fPgz=proof["fPgz"], Qz=Qz,
        terms=[a * cz % p * inv(peval(zk, z)) % p for a, cz, zk in
               zip(aux["alphas"], constraint_values(proof["fz"], proof["fPz"], proof["fgz"], proof["fPgz"]), prm.Z)],
        degQ=deg(Q), degDEEP=deg(aux["DEEP"]), root_DEEP=proof["root_DEEP"].hex(), beta=proof["beta"],
        queries=[{"iota": q["iota"], "value": q["value"], "path": [s.hex() for s in q["path"]]}
                 for q in proof["queries"]],
        rejections=aux["rejections"], fs_hashes=st["fs_hashes"], merkle_hashes=st["merkle_hashes"],
        proof_size=len(blob))
    finish(J, ok, reason, result, json_out)


if __name__ == "__main__":
    main()
