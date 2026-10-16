#!/usr/bin/env python3
# ============================================================================
#  Reference prover / verifier -- transparent AIR-DEEP-FRI STARK
#  Battery Passport compliance over the Goldilocks field
#
#  Article: "A Transparent STARK over the Goldilocks Field for Battery
#            Passport Compliance: Exact AIR, Closed-Form Soundness Bounds
#            and Full Numerical Verification"
#
#  AIR (article instance: N = 8, blowup = 8, |L| = 64)
#    Trace          J in {0,1}^N over G = <g>, g of order N
#    Evaluation dom L = <h>, |L| = N * blowup, G = {h^(blowup*k)} subset of L
#    Criteria       mandatory: J_0, J_1, J_(N-1); optional: J_2 .. J_(N-2)
#    Accumulator    P_1 = 1, P_i = P_{i-1}(1 - 2 J_i) for i = 2..N-2,
#                   P_0 = 1 - 2 J_1 (padding), P_(N-1) = 1 (free, convention)
#    Constraints    C1 = f^2 - f                          on G
#                   C2 = f_P(gx) - f_P(x)(1 - 2 f(gx))    on {g^0 .. g^(N-3)}
#                   C3 = f_P - 1                          on {g^1, g^(N-2)}
#                   C4 = f - 1                            on {g^0, g^1, g^(N-1)}
#    Batched        Q = sum_k alpha_k C_k / Z_k,          deg Q <= N
#
#  Protocol (DEEP-ALI + full FRI, no zero-knowledge)
#    Round 1  commit T: leaf j = (f(x_j), f(-x_j), f_P(x_j), f_P(-x_j))
#    Round 2  alpha_1..alpha_4; commit C: leaf j = (Q(x_j), Q(-x_j))
#    Round 3  z outside L; send f(z), f_P(z), f(gz), f_P(gz), Q(z);
#             the verifier checks Q*(z) = Q(z)
#    Round 4  gamma_1..gamma_5 and the DEEP composition
#               F = g1 (f - f(z))/(x - z)     + g2 (f_P - f_P(z))/(x - z)
#                 + g3 (f - f(gz))/(x - gz)   + g4 (f_P - f_P(gz))/(x - gz)
#                 + g5 (Q - Q(z))/(x - z),          deg F <= N - 1
#    Round 5  FRI commit phase: beta_0, root(F_1), beta_1, ..., beta_(m-1),
#             m = log2 N folds  F_(i+1)(x^2) = (F_i(x) + F_i(-x))/2
#                                           + beta_i (F_i(x) - F_i(-x))/(2x),
#             final layer constant c sent in clear
#    Round 6  lambda query positions j_r in [0, |L|/2); for each query the
#             verifier opens T and C at x_j and -x_j, recomputes F(x_j),
#             F(-x_j), and checks every folding step up to c.
#    Here x_j = h^j, and -x_j = h^(j + |L|/2).  Since F is evaluated
#    without any division by a vanishing polynomial, queries in G are
#    legitimate and no rejection sampling is needed.
#
#  Encoding convention
#    field element : 8 bytes little-endian (LE64)
#    Merkle leaf   : SHA256(LE64(v_1) || ... || LE64(v_k)); node = SHA256(l || r)
#    Fiat-Shamir   : H(t) = SHA256(t)[0:8] read as LE64; every challenge is
#                    appended to the transcript once drawn
#                    alpha_k, gamma_k, beta_i = H(tr) mod p
#                    z = H(tr || c) mod p, smallest c >= 0 with z not in L
#                    j_r = H(tr || r) mod |L|/2
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
from collections import Counter
from fractions import Fraction

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


def batch_inv(vals):
    """Montgomery batch inversion: n inverses for the cost of one."""
    pref, acc = [], 1
    for v in vals:
        pref.append(acc)
        acc = acc * v % p
    inv_acc = inv(acc)
    out = [0] * len(vals)
    for i in range(len(vals) - 1, -1, -1):
        out[i] = inv_acc * pref[i] % p
        inv_acc = inv_acc * vals[i] % p
    return out


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


def div_linear(a, z):
    """(a(x) - a(z)) / (x - z) by synthetic division."""
    a = trim(a)
    n = len(a)
    if n <= 1:
        return []
    q = [0] * (n - 1)
    acc = 0
    for i in range(n - 1, 0, -1):
        acc = (acc * z + a[i]) % p
        q[i - 1] = acc
    return trim(q)


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


def fold_coeffs(c, beta):
    """Coefficients of F_(i+1) from F_i: F_e + beta F_o."""
    return padd(c[0::2], pscale(c[1::2], beta))


def intt(values, w):
    n = len(values)
    iw, inn = inv(w), inv(n)
    return trim([inn * sum(values[k] * pow(iw, i * k, p) for k in range(n)) % p for i in range(n)])


def _ntt_pow2(a, w):
    """Iterative radix-2 NTT of a list of length 2^m (evaluations at w^i)."""
    n = len(a)
    a = list(a)
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j |= bit
        if i < j:
            a[i], a[j] = a[j], a[i]
    length = 2
    while length <= n:
        wl = pow(w, n // length, p)
        half = length // 2
        for start in range(0, n, length):
            wk = 1
            for k in range(start, start + half):
                u, v = a[k], a[k + half] * wk % p
                a[k], a[k + half] = (u + v) % p, (u - v) % p
                wk = wk * wl % p
        length <<= 1
    return a


def ntt(coeffs, w, n):
    """Evaluations of the polynomial `coeffs` at w^0 .. w^(n-1), w of order n."""
    c = trim(coeffs)
    assert len(c) <= n
    return _ntt_pow2(c + [0] * (n - len(c)), w)


# ----------------------------------------------------------------------------
#  Hashing, transcript, Merkle trees
# ----------------------------------------------------------------------------
def le64(x):
    return struct.pack("<Q", int(x) % 2**64)


def sha256(b):
    return hashlib.sha256(b).digest()


class Transcript:
    """Fiat-Shamir transcript; H(t) = SHA256(t)[0:8] read as LE64."""

    def __init__(self):
        self.state = b""
        self.n_hash = 0

    def absorb(self, data):
        self.state += data

    def _h(self, extra=b""):
        self.n_hash += 1
        return int.from_bytes(sha256(self.state + extra)[:8], "little")

    def field(self):
        c = self._h() % p
        self.absorb(le64(c))
        return c

    def field_outside(self, forbidden):
        c = 0
        while True:
            z = self._h(le64(c)) % p
            if z not in forbidden:
                self.absorb(le64(z))
                return z, c
            c += 1

    def index(self, r, n):
        return self._h(le64(r)) % n


class MerkleTree:
    """Leaf i = SHA256(LE64(v_1) || ... || LE64(v_k)), node = SHA256(l || r)."""

    def __init__(self, leaves_values):
        self.values = leaves_values
        layer = [sha256(b"".join(le64(v) for v in vals)) for vals in leaves_values]
        self.layers = [layer]
        while len(layer) > 1:
            layer = [sha256(layer[i] + layer[i + 1]) for i in range(0, len(layer), 2)]
            self.layers.append(layer)
        self.root = self.layers[-1][0]

    def open(self, idx):
        path, i = [], idx
        for layer in self.layers[:-1]:
            path.append(layer[i ^ 1])
            i //= 2
        return {"values": list(self.values[idx]), "path": path}


def merkle_check(root, idx, opening):
    """Returns (valid, number of SHA-256 evaluations)."""
    node, n = sha256(b"".join(le64(v) for v in opening["values"])), 1
    for sib in opening["path"]:
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
        assert blowup >= 2 and blowup & (blowup - 1) == 0
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
        self.mandatory = [0, 1, N - 1]
        self.optional = list(range(2, N - 1))
        self.domains = [list(range(N)), list(range(N - 2)), [1, N - 2], [0, 1, N - 1]]
        self.Z = [vanishing([self.G[k] for k in d]) for d in self.domains]
        self.deg_Q = N                                # deg Q2 = 2(N-1) - (N-2)
        self.d_F = N                                  # deg F <= N - 1
        self.rounds = int(math.log2(N))               # FRI folds, final layer constant
        self.rho = 1 / blowup
        # DEEP-ALI out-of-domain error: E = Z_G Q - sum_k alpha_k C_k Z_G / Z_k has
        # degree <= deg Q + N, and z is uniform over F_p minus L (|F_p \ L| = p - |L|)
        self.eps_ood = (self.deg_Q + N) / (p - sL)
        self.kappa = -math.log2(self.eps_ood)
        self.bits_per_query = math.log2(blowup)
        self.lam_star = math.ceil(self.kappa / self.bits_per_query)
        self.lam = lam if lam is not None else self.lam_star
        self.depth = int(math.log2(sL)) - 1           # depth of the trees on L (pair leaves)

    def point(self, layer, t):
        """t-th point of L_layer = <h^(2^layer)>."""
        return pow(self.h, (1 << layer) * t, p)

    def default_trace(self):
        if self.N == 8:
            return list(ARTICLE_TRACE)
        J = [0] * self.N
        for i in self.mandatory + self.optional[:2]:
            J[i] = 1
        return J

    def eps_total(self, lam=None):
        lam = self.lam if lam is None else lam
        return self.eps_ood + (1 - self.eps_ood) * self.rho**lam

    def proof_size(self, lam=None):
        """Bytes: roots of T, C and the m - 1 committed FRI layers, 5 OOD values,
        final constant, and per query the openings of T, C and every layer."""
        lam = self.lam if lam is None else lam
        m, d = self.rounds, self.depth
        header = 32 * (2 + m - 1) + 8 * 5 + 8
        per_query = (32 + 32 * d) + (16 + 32 * d) + sum(16 + 32 * (d - i) for i in range(1, m))
        return header + lam * per_query


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


def deep_composition(evals, ood, gammas, z, gz, xs):
    """F(x) for every x in xs from the evaluations (f, f_P, Q) at x."""
    fz, fPz, fgz, fPgz, Qz = ood
    inv_z = batch_inv([(x - z) % p for x in xs])
    inv_gz = batch_inv([(x - gz) % p for x in xs])
    g1, g2, g3, g4, g5 = gammas
    out = []
    for t, (fx, Px, Qx) in enumerate(evals):
        out.append((g1 * (fx - fz) * inv_z[t] + g2 * (Px - fPz) * inv_z[t]
                    + g3 * (fx - fgz) * inv_gz[t] + g4 * (Px - fPgz) * inv_gz[t]
                    + g5 * (Qx - Qz) * inv_z[t]) % p)
    return out


def fri_fold(cur, beta, prm, layer):
    """Values of F_(layer+1) on L_(layer+1) from those of F_layer on L_layer."""
    half = len(cur) // 2
    i2 = inv(2)
    inv2x = batch_inv([2 * prm.point(layer, t) % p for t in range(half)])
    return [((cur[t] + cur[t + half]) * i2 + beta * (cur[t] - cur[t + half]) * inv2x[t]) % p
            for t in range(half)]


def prove(J, prm, cheat=None, forged=None):
    """Prover.
    cheat = None              honest prover; raises AIRViolation on a non-compliant trace
          | 'drop_remainder'  non-compliant trace, division remainders silently dropped
          | 'fake_ood'        honest commitments, Q(z) replaced by the value Q*(z)
                              the verifier expects (F is then not a polynomial)
          | 'forge'           no witness at all: `forged` = (f_L, fP_L, Q_L) arbitrary
                              values on L, OOD values arbitrary with Q(z) = Q*(z)
    In the cheating modes F is computed from evaluations, the FRI layers are the
    true folds of these evaluations, and the final constant is the most frequent
    value of the last layer (best choice for the cheater)."""
    n, half = prm.size_L, prm.size_L // 2
    if cheat == "forge":
        A = None
        f_L, fP_L, Q_L = forged
        f = fP = Q = None
    else:
        A = arithmetize(J, prm)
        if A["violated"] and cheat is None:
            raise AIRViolation(A["violated"])
        f, fP = A["f"], A["fP"]
        f_L, fP_L = ntt(f, prm.h, n), ntt(fP, prm.h, n)
    tr = Transcript()
    # ---- Round 1: trace commitment
    T = MerkleTree([(f_L[j], f_L[j + half], fP_L[j], fP_L[j + half]) for j in range(half)])
    tr.absorb(T.root)
    # ---- Round 2: batching coefficients, quotient, commitment to Q
    alphas = [tr.field() for _ in range(4)]
    if cheat != "forge":
        Q = []
        for a, q in zip(alphas, A["Q"]):
            Q = padd(Q, pscale(q, a))
        Q_L = ntt(Q, prm.h, n)
    Cm = MerkleTree([(Q_L[j], Q_L[j + half]) for j in range(half)])
    tr.absorb(Cm.root)
    # ---- Round 3: out-of-domain point and evaluations
    z, zc = tr.field_outside(prm.L_set)
    gz = prm.g * z % p
    if cheat == "forge":
        rnd = Transcript()
        rnd.absorb(b"forger" + T.root + Cm.root)
        ood = [rnd.field() for _ in range(4)] + [0]
    else:
        ood = [peval(f, z), peval(fP, z), peval(f, gz), peval(fP, gz), peval(Q, z)]
    if cheat in ("fake_ood", "forge"):
        Cz = constraint_values(*ood[:4])
        ood[4] = sum(a * c * inv(peval(zk, z)) for a, c, zk in zip(alphas, Cz, prm.Z)) % p
    for v in ood:
        tr.absorb(le64(v))
    # ---- Round 4: DEEP-ALI composition
    gammas = [tr.field() for _ in range(5)]
    F_coeffs = None
    if cheat is None:
        F_coeffs = []
        for gm, pol, pt in zip(gammas, (f, fP, f, fP, Q), (z, z, gz, gz, z)):
            F_coeffs = padd(F_coeffs, pscale(div_linear(pol, pt), gm))
        assert deg(F_coeffs) < prm.d_F
        F_L = ntt(F_coeffs, prm.h, n)
    else:
        F_L = deep_composition(list(zip(f_L, fP_L, Q_L)), ood, gammas, z, gz, prm.L)
    # ---- Round 5: FRI commit phase
    layers, betas, cur, cur_coeffs, layer_coeffs = [], [], F_L, F_coeffs, []
    for i in range(prm.rounds):
        beta = tr.field()
        betas.append(beta)
        cur = fri_fold(cur, beta, prm, i)
        if cur_coeffs is not None:
            cur_coeffs = fold_coeffs(cur_coeffs, beta)
            layer_coeffs.append(cur_coeffs)
        if i + 1 < prm.rounds:
            hn = len(cur) // 2
            tree = MerkleTree([(cur[t], cur[t + hn]) for t in range(hn)])
            layers.append(tree)
            tr.absorb(tree.root)
    final = Counter(cur).most_common(1)[0][0]
    tr.absorb(le64(final))
    # ---- Round 6: queries
    positions = [tr.index(r, half) for r in range(1, prm.lam + 1)]
    queries = []
    for j in positions:
        q = {"j": j, "T": T.open(j), "C": Cm.open(j), "layers": []}
        t = j
        for tree in layers:
            hn = len(tree.values)
            t = t % (2 * hn)
            q["layers"].append(tree.open(t % hn))
        queries.append(q)
    proof = {"root_T": T.root, "root_C": Cm.root, "ood": ood,
             "layer_roots": [t.root for t in layers], "final": final, "queries": queries}
    aux = {"A": A, "Q": Q, "F": F_coeffs, "F_L": F_L, "f_L": f_L, "fP_L": fP_L, "Q_L": Q_L,
           "alphas": alphas, "z": z, "z_counter": zc, "gammas": gammas, "betas": betas,
           "layers": layers, "layer_coeffs": layer_coeffs, "last_layer": cur,
           "positions": positions, "prover_hashes": tr.n_hash}
    return proof, aux


def serialize(proof):
    out = proof["root_T"] + proof["root_C"] + b"".join(le64(v) for v in proof["ood"])
    out += b"".join(proof["layer_roots"]) + le64(proof["final"])
    for q in proof["queries"]:
        for op in [q["T"], q["C"]] + q["layers"]:
            out += b"".join(le64(v) for v in op["values"]) + b"".join(op["path"])
    return out


# ----------------------------------------------------------------------------
#  Verifier (works on the proof only)
# ----------------------------------------------------------------------------
def verify(proof, prm):
    """Returns (accepted, reason, stats)."""
    st = {"fs_hashes": 0, "merkle_hashes": 0, "inversions": 0}
    n, half = prm.size_L, prm.size_L // 2
    tr = Transcript()
    tr.absorb(proof["root_T"])
    alphas = [tr.field() for _ in range(4)]
    tr.absorb(proof["root_C"])
    z, zc = tr.field_outside(prm.L_set)
    gz = prm.g * z % p
    ood = proof["ood"]
    if len(ood) != 5:
        return False, "Round 3: wrong number of out-of-domain values", st
    for v in ood:
        tr.absorb(le64(v))
    fz, fPz, fgz, fPgz, Qz = ood
    Cz = constraint_values(fz, fPz, fgz, fPgz)
    inv_Z = batch_inv([peval(zk, z) for zk in prm.Z])     # one inversion for the four Z_k(z)
    st["inversions"] += 1
    Qstar = sum(a * cz * iz for a, cz, iz in zip(alphas, Cz, inv_Z)) % p
    st.update(alphas=alphas, z=z, z_counter=zc, Qstar=Qstar)
    if Qstar != Qz:
        st["fs_hashes"] = tr.n_hash
        return False, "Round 3: out-of-domain check Q*(z) != Q(z)", st
    gammas = [tr.field() for _ in range(5)]
    if len(proof["layer_roots"]) != prm.rounds - 1:
        st["fs_hashes"] = tr.n_hash
        return False, "Round 5: wrong number of committed FRI layers", st
    betas = []
    for i in range(prm.rounds):
        betas.append(tr.field())
        if i + 1 < prm.rounds:
            tr.absorb(proof["layer_roots"][i])
    tr.absorb(le64(proof["final"]))
    positions = [tr.index(r, half) for r in range(1, prm.lam + 1)]
    st.update(fs_hashes=tr.n_hash, gammas=gammas, betas=betas, positions=positions)
    if len(proof["queries"]) != prm.lam:
        return False, f"Round 6: {len(proof['queries'])} queries instead of {prm.lam}", st
    # every denominator of Round 6 depends only on z and the positions: one batch inversion
    hns = [(n >> (i + 1)) // 2 for i in range(prm.rounds)]   # leaves of layer i + 1
    dens = []
    for j in positions:
        x0 = prm.point(0, j)
        dens += [(x0 - z) % p, (-x0 - z) % p, (x0 - gz) % p, (-x0 - gz) % p]
        t = j
        for i in range(prm.rounds):
            dens.append(2 * prm.point(i, t) % p)
            t = t % hns[i] if i + 1 < prm.rounds else t
    invs = batch_inv(dens + [2])
    i2 = invs[-1]
    st["inversions"] += 1
    per_q = 4 + prm.rounds
    g1, g2, g3, g4, g5 = gammas
    for r, (q, j) in enumerate(zip(proof["queries"], positions), 1):
        if q["j"] != j:
            return False, f"Round 6: query {r} position {q['j']} != transcript position {j}", st
        for name, root, nv in (("T", proof["root_T"], 4), ("C", proof["root_C"], 2)):
            if len(q[name]["values"]) != nv:
                return False, f"Round 6: malformed {name} opening of query {r}", st
            ok, nh = merkle_check(root, j, q[name])
            st["merkle_hashes"] += nh
            if not ok:
                what = "trace (f, f_P)" if name == "T" else "quotient (Q)"
                return False, f"Round 6: Merkle path of the {what} opening of query {r} is invalid", st
        f0, f1, P0, P1 = q["T"]["values"]
        Q0, Q1 = q["C"]["values"]
        iv = invs[(r - 1) * per_q:r * per_q]
        a = (g1 * (f0 - fz) * iv[0] + g2 * (P0 - fPz) * iv[0] + g3 * (f0 - fgz) * iv[2]
             + g4 * (P0 - fPgz) * iv[2] + g5 * (Q0 - Qz) * iv[0]) % p
        b = (g1 * (f1 - fz) * iv[1] + g2 * (P1 - fPz) * iv[1] + g3 * (f1 - fgz) * iv[3]
             + g4 * (P1 - fPgz) * iv[3] + g5 * (Q1 - Qz) * iv[1]) % p
        t = j                                   # position of x in L_i, 0 <= t < |L_i|/2
        for i in range(prm.rounds):
            val = ((a + b) * i2 + betas[i] * (a - b) * iv[4 + i]) % p
            if i + 1 < prm.rounds:
                hn = hns[i]
                op = q["layers"][i]
                if len(op["values"]) != 2:
                    return False, f"Round 6: malformed FRI layer {i+1} opening of query {r}", st
                ok, nh = merkle_check(proof["layer_roots"][i], t % hn, op)
                st["merkle_hashes"] += nh
                if not ok:
                    return False, f"Round 6: FRI layer {i+1} Merkle path of query {r} is invalid", st
                c0, c1 = op["values"]
                if val != (c0 if t < hn else c1):
                    return False, f"Round 6: FRI folding inconsistency at layer {i+1} (query {r})", st
                a, b = c0, c1
                t = t % hn
            elif val != proof["final"]:
                return False, f"Round 6: last FRI fold differs from the final constant (query {r})", st
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
        J = []
    if len(J) != prm.N:
        sys.exit("usage: verify_battery_passport.py [J0 ... J7] [--json file]")
    result = {"J": J}
    print("Transparent AIR-DEEP-FRI Battery Passport -- reference prover/verifier")
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
    section("MODULE 2  Domains G and L, FRI domains L_i")
    check("g^0 .. g^7 pairwise distinct", len(set(prm.G)) == 8)
    check("G = {h^(8k)} subset of L, |L| = 64", all(prm.G[k] == prm.L[8 * k] for k in range(8))
          and len(prm.L_set) == 64)
    check("prod_k (x - g^k) = x^8 - 1", prm.Z[0] == [p - 1, 0, 0, 0, 0, 0, 0, 0, 1])
    check("x in G  =>  g x in G", all(g * x % p in set(prm.G) for x in prm.G))
    check("g L = L (so z not in L implies gz not in L)", all(g * x % p in prm.L_set for x in prm.L))
    check("-x_j = x_(j+32): h^32 = -1, L closed under negation", pow(h, 32, p) == p - 1)
    check("L_i = {x^(2^i) : x in L} has 64 / 2^i points (i = 0..3)",
          all(len({pow(x, 1 << i, p) for x in prm.L}) == 64 >> i for i in range(4)))

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
    check("eps_OOD = (deg Q + 8)/(p - |L|) = 16/(p - 64)", prm.eps_ood == 16 / (p - 64))
    check("kappa* = -log2(eps_OOD) ~ 60.00", abs(prm.kappa - 60) < 1e-3)
    check("rho = 1/8: 3 bits per query (conjectured FRI soundness)", prm.bits_per_query == 3)
    check("lambda* = ceil(kappa*/3) = 20", prm.lam_star == 20)
    regime = []
    for lam in (1, 5, 10, 15, 19, 20, 21, 25, 30):
        e = prm.eps_total(lam)
        share = (1 - prm.eps_ood) * prm.rho**lam / e
        regime.append({"lambda": lam, "bits": -math.log2(e), "fri_share": share})
        info(f"lambda = {lam:2d}", f"2^-{-math.log2(e):.2f}   FRI {100*share:5.1f}%   OOD {100*(1-share):5.1f}%")
    e_ood = Fraction(prm.deg_Q + prm.N, p - prm.size_L)
    rho = Fraction(1, prm.blowup)
    check("rho^20 <= eps_OOD < rho^19 (exact): lambda* = 20 is the balance point",
          rho**20 <= e_ood < rho**19)
    e20 = e_ood + (1 - e_ood) * rho**20
    check("eps_total(20) <= 2 eps_OOD (exact), i.e. -log2 eps_total(20) = "
          f"{-math.log2(e20):.2f} bits", e20 <= 2 * e_ood)
    blow = []
    for b in (4, 8, 16, 32):
        q = Params(8, b)
        blow.append({"blowup": b, "L": q.size_L, "kappa": q.kappa, "bits": q.bits_per_query,
                     "lambda": q.lam_star, "proof_size": q.proof_size()})
        info(f"blowup {b:2d}", f"|L| = {q.size_L:3d}  kappa* = {q.kappa:.2f}  bits/query = "
             f"{q.bits_per_query:.0f}  lambda* = {q.lam_star}  proof = {q.proof_size()} B")
    result["soundness"] = {"eps_ood": prm.eps_ood, "kappa": prm.kappa, "lambda_star": prm.lam_star,
                           "regime": regime, "blowup": blow}

    # ---------------------------------------------------------------- 6
    proof, aux = prove(J, prm)
    section("MODULE 6  Prover, Rounds 1-3 (commitments, challenges, OOD evaluations)")
    Q, z = aux["Q"], aux["z"]
    info("root(T)  [f, f_P]", "0x" + proof["root_T"].hex())
    for k, a in enumerate(aux["alphas"], 1):
        info(f"alpha_{k}", hx(a))
    check("deg Q <= 8", deg(Q) <= 8)
    info("root(C)  [Q]", "0x" + proof["root_C"].hex())
    info("z  (counter c)", f"{hx(z)}  ({aux['z_counter']})")
    check("z not in L (hence z, gz not in G and Z_k(z) != 0)", z not in prm.L_set)
    for v, name in zip(proof["ood"], ("f(z)", "f_P(z)", "f(gz)", "f_P(gz)", "Q(z)")):
        info(name, hx(v))
    Cz = constraint_values(*proof["ood"][:4])
    terms = [a * c % p * inv(peval(zk, z)) % p for a, c, zk in zip(aux["alphas"], Cz, prm.Z)]
    for k, t in enumerate(terms, 1):
        info(f"alpha_{k} C_{k}(z)/Z_{k}(z)", hx(t))
    check("sum of the four terms = Q(z)", sum(terms) % p == proof["ood"][4])

    # ---------------------------------------------------------------- 7
    section("MODULE 7  Prover, Rounds 4-5 (DEEP composition, FRI commit phase)")
    for k, gm in enumerate(aux["gammas"], 1):
        info(f"gamma_{k}", hx(gm))
    F = aux["F"]
    check("F = sum gamma_i (P_i - P_i(z_i))/(x - z_i) is a polynomial of degree <= 7",
          deg(F) <= 7)
    info("deg F", deg(F))
    xs = prm.L
    direct = deep_composition(list(zip(aux["f_L"], aux["fP_L"], aux["Q_L"])), proof["ood"],
                              aux["gammas"], z, prm.g * z % p, xs)
    check("F(x) recomputed from f(x), f_P(x), Q(x) equals F(x) at all 64 points of L (incl. G)",
          direct == aux["F_L"])
    for i, (beta, co) in enumerate(zip(aux["betas"], aux["layer_coeffs"])):
        info(f"beta_{i}", hx(beta))
        bound = (prm.d_F >> (i + 1)) - 1
        check(f"F_{i+1} = F_{i},e + beta_{i} F_{i},o has degree {deg(co)} <= {bound}", deg(co) <= bound)
        if i + 1 < prm.rounds:
            tree = aux["layers"][i]
            vals = [v for pair in tree.values for v in pair[:1]] + [pair[1] for pair in tree.values]
            check(f"committed layer F_{i+1} = evaluations of F_{i+1} on L_{i+1} ({len(vals)} points)",
                  vals == [peval(co, prm.point(i + 1, t)) for t in range(len(vals))])
            info(f"root(F_{i+1})", "0x" + tree.root.hex())
    check("last layer constant on L_3 (8 points) = final value c",
          set(aux["last_layer"]) == {proof["final"]} and aux["layer_coeffs"][-1] == ([proof["final"]] if proof["final"] else []))
    info("final constant c", hx(proof["final"]))

    # ---------------------------------------------------------------- 8
    section("MODULE 8  Round 6: queries and openings")
    pos = aux["positions"]
    info(f"positions j_1 .. j_{prm.lam}", pos)
    info("distinct positions", f"{len(set(pos))} of {prm.size_L // 2} cosets {{x, -x}}")
    q1 = proof["queries"][0]
    j = q1["j"]
    info(f"query 1: x = h^{j}, -x = h^{j + 32}", "")
    info("  T leaf (f(x),f(-x),fP(x),fP(-x))", [hx(v) for v in q1["T"]["values"]])
    info("  C leaf (Q(x), Q(-x))", [hx(v) for v in q1["C"]["values"]])
    for i, op in enumerate(q1["layers"], 1):
        info(f"  F_{i} leaf", [hx(v) for v in op["values"]])
    blob = serialize(proof)
    check(f"serialized proof size = {prm.proof_size()} bytes (closed form)", len(blob) == prm.proof_size())

    # ---------------------------------------------------------------- 9
    section("MODULE 9  Verifier (works on the proof only)")
    ok, reason, st = verify(proof, prm)
    check("verifier recomputes alpha_1..4, z, gamma_1..5, beta_0..2 and the positions",
          st["alphas"] == aux["alphas"] and st["z"] == z and st.get("gammas") == aux["gammas"]
          and st.get("betas") == aux["betas"] and st.get("positions") == pos)
    info("Q*(z) recomputed", hx(st["Qstar"]))
    info("Fiat-Shamir hashes", st["fs_hashes"])
    info("Merkle hashes", st["merkle_hashes"])
    info("total SHA-256", st["fs_hashes"] + st["merkle_hashes"])
    info("field inversions", st["inversions"])
    check("verifier decision: " + reason, ok)

    result.update(
        root_T=proof["root_T"].hex(), root_C=proof["root_C"].hex(), alphas=aux["alphas"],
        z=z, z_counter=aux["z_counter"], ood=proof["ood"], terms=terms, degQ=deg(Q),
        gammas=aux["gammas"], degF=deg(F), betas=aux["betas"],
        layer_roots=[r.hex() for r in proof["layer_roots"]], final=proof["final"],
        positions=pos, fs_hashes=st["fs_hashes"], merkle_hashes=st["merkle_hashes"],
        inversions=st["inversions"], proof_size=len(blob),
        query1={"j": j, "T": q1["T"]["values"], "C": q1["C"]["values"],
                "layers": [op["values"] for op in q1["layers"]],
                "T_path": [s.hex() for s in q1["T"]["path"]]})
    finish(J, ok, reason, result, json_out)


if __name__ == "__main__":
    main()
